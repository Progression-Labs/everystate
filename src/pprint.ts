// Faithful port of TLC's value pretty-printer (tlc2.pprint.{PrettyPrint,Parse,
// Format,Node}).  TLC prints every value through
//
//     tlc2.value.Values.ppr(s)  ==  tlc2.pprint.PrettyPrint.mypp(s, 80)
//
// which RE-PARSES the one-line string form of the value and re-wraps it so that
// it fits in `width` columns.  The parser is deliberately naive (no escape
// handling in strings, constants are runs of letters/digits only, ...) and the
// port keeps every one of those quirks: whenever the Java code would throw, or
// would not consume the whole input, the input is returned unchanged.
//
// The structure (and most names) follow the Java source one-to-one so the two
// can be diffed by eye.

/* ------------------------------------------------------------------------- */
/* Exceptions                                                                */
/* ------------------------------------------------------------------------- */

class ParseException extends Error {}
class FormatException extends Error {}
/** Stand-in for java.lang.StringIndexOutOfBoundsException. */
class StringIndexOutOfBoundsException extends Error {}

/* ------------------------------------------------------------------------- */
/* java.lang.String / java.lang.Character helpers                            */
/* ------------------------------------------------------------------------- */

/** String.charAt: returns the UTF-16 code unit, throws when out of range. */
function charAt(string: string, index: number): number {
  if (index < 0 || index >= string.length) {
    throw new StringIndexOutOfBoundsException("index " + index + ", length " + string.length);
  }
  return string.charCodeAt(index);
}

/** String.regionMatches(index, other, 0, other.length()) / startsWith(other, index). */
function regionMatches(string: string, index: number, other: string): boolean {
  if (index < 0 || index + other.length > string.length) return false;
  return string.startsWith(other, index);
}

/** Character.isWhitespace(char). */
function isWhitespace(c: number): boolean {
  return (
    (c >= 0x09 && c <= 0x0d) ||
    (c >= 0x1c && c <= 0x20) ||
    c === 0x1680 ||
    (c >= 0x2000 && c <= 0x2006) ||
    (c >= 0x2008 && c <= 0x200a) ||
    c === 0x2028 ||
    c === 0x2029 ||
    c === 0x205f ||
    c === 0x3000
  );
}

const DIGIT_RE = /^\p{Nd}$/u;
const LETTER_OR_DIGIT_RE = /^[\p{L}\p{Nd}]$/u;

/** Character.isDigit(char) -- a single UTF-16 unit, so surrogates never match. */
function isDigit(c: number): boolean {
  if (c < 0x80) return c >= 0x30 && c <= 0x39;
  return DIGIT_RE.test(String.fromCharCode(c));
}

/** Character.isLetterOrDigit(char). */
function isLetterOrDigit(c: number): boolean {
  if (c < 0x80) {
    return (c >= 0x30 && c <= 0x39) || (c >= 0x41 && c <= 0x5a) || (c >= 0x61 && c <= 0x7a);
  }
  return LETTER_OR_DIGIT_RE.test(String.fromCharCode(c));
}

/* ------------------------------------------------------------------------- */
/* Node                                                                      */
/* ------------------------------------------------------------------------- */

const CONSTANT = 1;
const SET = 2;
const SEQUENCE = 3;
const RECORD = 4;
const RECORDPAIR = 5;
const FUNCTION = 6;
const FUNCTIONPAIR = 7;
const SUBSET = 8;

class Node {
  type: number;
  first: number;
  last: number;
  children: Node | null;
  next: Node | null;
  string: string;

  constructor(str: string, s: number, e: number, t: number) {
    this.string = str;
    this.type = t;
    this.first = s;
    this.last = e;
    this.children = null;
    this.next = null;
  }

  /** string.substring(first, last+1), with Java's bounds checking. */
  value(): string {
    const begin = this.first;
    const end = this.last + 1;
    if (begin < 0 || end > this.string.length || begin > end) {
      throw new StringIndexOutOfBoundsException(
        "begin " + begin + ", end " + end + ", length " + this.string.length,
      );
    }
    return this.string.substring(begin, end);
  }

  length(): number {
    return this.last - this.first + 1;
  }
}

/* ------------------------------------------------------------------------- */
/* Parse                                                                     */
/* ------------------------------------------------------------------------- */

const P_setOpen = 0x7b; // '{'
const P_setClose = 0x7d; // '}'
const P_seqOpen = 0x3c; // '<'
const P_seqClose = 0x3e; // '>'
const P_recOpen = 0x5b; // '['
const P_recClose = 0x5d; // ']'
const P_recDiv = "|->";
const P_funOpen = 0x28; // '('
const P_funClose = 0x29; // ')'
const P_funDiv = ":>";
const P_funSep = "@@";
const P_intDiv = "..";
const P_ssDiv = "SUBSET";
const COMMA = 0x2c;
const QUOTE = 0x22;
const MINUS = 0x2d;

/** Converts a run off the end of the string into a ParseException, as each Java method does. */
function rethrow(e: unknown, what: string, index: number, string: string): never {
  if (e instanceof StringIndexOutOfBoundsException) {
    throw new ParseException(
      "TLC Bug: while formating output, the formatter ran off the end of the string while " +
        what + " starting at index " + index + " in the value " + string + "\n" + e.message,
    );
  }
  throw e;
}

function parse(string: string, index: number): Node {
  if (string.length === 0) {
    throw new ParseException(
      "TLC Bug: while formating output, the formatter was called with an empty string for a value",
    );
  }
  if (index < 0 || index > string.length - 1) {
    throw new ParseException(
      "TLC Bug: while formating output, the formatter was called with a string " +
        string + " for a value and an index " + index + " out of bounds",
    );
  }

  index = skipWhitespace(string, index);

  // NB: an uncaught StringIndexOutOfBoundsException cannot escape from here:
  // skipWhitespace either returns a valid index or throws a ParseException.
  if (charAt(string, index) === P_setOpen) {
    return parseSet(string, index);
  }
  if (charAt(string, index) === P_seqOpen) {
    return parseSequence(string, index);
  }
  if (charAt(string, index) === P_recOpen) {
    return parseRecord(string, index);
  }
  if (charAt(string, index) === P_funOpen) {
    return parseFunction(string, index);
  }
  if (regionMatches(string, index, P_ssDiv)) {
    return parseSubset(string, index);
  }
  return parseConstant(string, index);
}

/** Parse a set.  Assume that index points to the '{' character in string. */
function parseSet(string: string, index: number): Node {
  const first = index;
  let last = index;

  try {
    const node = new Node(string, first, 0, SET);

    let firstelement: Node | null = null;
    let lastelement: Node | null = null;

    // skip the '{' character and following whitespace
    last++;
    last = skipWhitespace(string, last);

    // parse comma-separated elements in set up to a '}' character
    while (charAt(string, last) !== P_setClose) {
      const elt = parse(string, last);

      if (lastelement === null) {
        firstelement = elt;
        lastelement = elt;
      } else {
        lastelement.next = elt;
        lastelement = elt;
      }

      // point to character after this element
      last = elt.last + 1;

      // skip the comma between elements, and surrounding whitespace
      last = skipWhitespace(string, last);
      if (charAt(string, last) === COMMA) last++;
      last = skipWhitespace(string, last);
    }
    node.children = firstelement;
    node.last = last;

    return node;
  } catch (e) {
    rethrow(e, "parsing a set", index, string);
  }
}

/** Parse a sequence.  Assume that index points to the '<' character in string. */
function parseSequence(string: string, index: number): Node {
  const first = index;
  let last = index;

  try {
    const node = new Node(string, first, 0, SEQUENCE);

    let firstelement: Node | null = null;
    let lastelement: Node | null = null;

    // skip the '<<' token and following whitespace
    last++;
    last++;
    last = skipWhitespace(string, last);

    // parse comma-separated elements in sequence up to a '>>' token
    while (charAt(string, last) !== P_seqClose) {
      const elt = parse(string, last);

      if (lastelement === null) {
        firstelement = elt;
        lastelement = elt;
      } else {
        lastelement.next = elt;
        lastelement = elt;
      }

      // point to character after this element
      last = elt.last + 1;

      // skip the comma between elements, and surrounding whitespace
      last = skipWhitespace(string, last);
      if (charAt(string, last) === COMMA) last++;
      last = skipWhitespace(string, last);
    }
    // point to the second '>' in the '>>' token (unchecked, as in Java)
    last++;

    node.children = firstelement;
    node.last = last;

    return node;
  } catch (e) {
    rethrow(e, "parsing a sequence", index, string);
  }
}

/** Parse a record.  Assume that index points to the '[' character in string. */
function parseRecord(string: string, index: number): Node {
  const first = index;
  let last = index;

  try {
    const node = new Node(string, first, 0, RECORD);

    let firstelement: Node | null = null;
    let lastelement: Node | null = null;

    // skip the '[' character and following whitespace
    last++;
    last = skipWhitespace(string, last);

    // parse comma-separated pairs in record up to a ']' character
    while (charAt(string, last) !== P_recClose) {
      const elt = parseRecordPair(string, last);

      if (lastelement === null) {
        firstelement = elt;
        lastelement = elt;
      } else {
        lastelement.next = elt;
        lastelement = elt;
      }

      // point to character after this element
      last = elt.last + 1;

      // skip the comma between elements, and surrounding whitespace
      last = skipWhitespace(string, last);
      if (charAt(string, last) === COMMA) last++;
      last = skipWhitespace(string, last);
    }
    node.children = firstelement;
    node.last = last;

    return node;
  } catch (e) {
    rethrow(e, "parsing a record", index, string);
  }
}

/** Assume that index points to the start of a "field|->value" record pair in string. */
function parseRecordPair(string: string, index: number): Node {
  const first = index;
  let last = index;

  try {
    const node = new Node(string, first, 0, RECORDPAIR);

    // get field name
    const field = parse(string, last);

    // point to position just past field name in string
    last = field.last + 1;

    // skip the '|->' token and the surrounding whitespace
    last = skipWhitespace(string, last);
    if (!regionMatches(string, last, P_recDiv)) {
      throw new ParseException(
        "TLC Bug: while formating output, the formatter couldn't find the token " + P_recDiv +
          " while parsing a record field/value pair starting at index " + index +
          " in value " + string,
      );
    }
    last = last + P_recDiv.length;
    last = skipWhitespace(string, last);

    // get field value
    const value = parse(string, last);

    // make field name and value children of the record pair node
    field.next = value;
    node.children = field;
    node.last = value.last;

    return node;
  } catch (e) {
    rethrow(e, "parsing a record pair", index, string);
  }
}

/** Parse a function.  Assume that index points to the '(' character in string. */
function parseFunction(string: string, index: number): Node {
  const first = index;
  let last = index;

  try {
    const node = new Node(string, first, 0, FUNCTION);

    let firstpair: Node | null = null;
    let lastpair: Node | null = null;

    // skip the '(' character and following whitespace
    last++;
    last = skipWhitespace(string, last);

    // parse the pairs in function up to a ')' character
    while (charAt(string, last) !== P_funClose) {
      const pair = parseFunctionPair(string, last);

      if (lastpair === null) {
        firstpair = pair;
        lastpair = pair;
      } else {
        lastpair.next = pair;
        lastpair = pair;
      }

      // point to character after this pair
      last = pair.last + 1;

      // skip the separator between pairs, and surrounding whitespace
      last = skipWhitespace(string, last);
      if (regionMatches(string, last, P_funSep)) {
        last = last + P_funSep.length;
      }
      last = skipWhitespace(string, last);
    }
    node.children = firstpair;
    node.last = last;

    return node;
  } catch (e) {
    rethrow(e, "parsing a function", index, string);
  }
}

/** Parse a SUBSET.  Assume that index points to the start of the substring "SUBSET". */
function parseSubset(string: string, index: number): Node {
  const first = index;
  let last = index;

  try {
    const node = new Node(string, first, 0, SUBSET);

    // skip the 'SUBSET' and following whitespace
    last += 6;
    last = skipWhitespace(string, last);

    const elt = parse(string, last);
    node.children = elt;
    node.last = elt.last;

    return node;
  } catch (e) {
    rethrow(e, "parsing a SUBSET", index, string);
  }
}

/** Assume that index points to the start of a "domain:>range" pair in string. */
function parseFunctionPair(string: string, index: number): Node {
  const first = index;
  let last = index;

  try {
    const node = new Node(string, first, 0, FUNCTIONPAIR);

    // get domain value
    const domain = parse(string, last);

    // point to position just past domain value in string
    last = domain.last + 1;

    // skip the ':>' token and the surrounding whitespace
    last = skipWhitespace(string, last);
    if (!regionMatches(string, last, P_funDiv)) {
      throw new ParseException(
        "TLC Bug: while formating output, the formatter couldn't find token " + P_funDiv +
          " while parsing a function arg/value pair starting at index " + index +
          " in value " + string,
      );
    }
    last = last + P_funDiv.length;
    last = skipWhitespace(string, last);

    // get range value
    const range = parse(string, last);

    // make domain and range values children of the function pair node
    domain.next = range;
    node.children = domain;
    node.last = range.last;

    return node;
  } catch (e) {
    rethrow(e, "parsing a function pair", index, string);
  }
}

/** Parse a constant: strings, booleans, integers, intervals and model values. */
function parseConstant(string: string, index: number): Node {
  try {
    const first = skipWhitespace(string, index);
    let last = first;

    if (charAt(string, first) === QUOTE) {
      // we are parsing a string constant (NB: no notion of escaped quotes)
      do last++;
      while (charAt(string, last) !== QUOTE);
      return new Node(string, first, last, CONSTANT);
    }

    if (isDigit(charAt(string, last))) {
      // we might be parsing a constant interval i..j
      const node = parseInterval(string, index);
      if (node !== null) return node;
    }

    if (charAt(string, last) === MINUS) {
      // we are parsing a negative integer
      last++;
      while (isDigit(charAt(string, last))) {
        last++;
        if (last === string.length) break;
      }
      last--;
      return new Node(string, first, last, CONSTANT);
    }

    if (isLetterOrDigit(charAt(string, last))) {
      // we are parsing an integer, boolean, or model value
      while (isLetterOrDigit(charAt(string, last))) {
        last++;
        if (last === string.length) break;
      }
      last--;
      return new Node(string, first, last, CONSTANT);
    }

    // we have encountered an illegal character in a constant
    throw new ParseException(
      "TLC Bug: while formating output, the formatter discovered an illegal character while" +
        " parsing a constant starting at index " + first + " in the value " + string,
    );
  } catch (e) {
    rethrow(e, "parsing a constant", index, string);
  }
}

/**
 * Parse a constant interval of the form i..j for integers i and j.  Returns
 * null if the parsing fails, rather than throwing as other routines do.
 */
function parseInterval(string: string, index: number): Node | null {
  try {
    const first = index;
    let last = first;

    // parse the first integer i
    if (!isDigit(charAt(string, last))) return null;
    while (last < string.length && isDigit(charAt(string, last))) {
      last++;
    }

    // parse the interval constructor ".."
    if (!regionMatches(string, last, P_intDiv)) return null;
    last++;
    last++;

    // parse the second integer j
    if (!isDigit(charAt(string, last))) return null;
    while (isDigit(charAt(string, last))) {
      last++;
      if (last === string.length) break;
    }
    last--;

    return new Node(string, first, last, CONSTANT);
  } catch (e) {
    // bail if we run off the string during parsing
    if (e instanceof StringIndexOutOfBoundsException) return null;
    throw e;
  }
}

/**
 * Skip whitespace starting at index in string, and return the index of the
 * first non-whitespace character, throwing if we run off the end.
 */
function skipWhitespace(string: string, index: number): number {
  try {
    let i = index;
    while (isWhitespace(charAt(string, i))) {
      i++;
    }
    return i;
  } catch (e) {
    rethrow(e, "skipping whitespace", index, string);
  }
}

/* ------------------------------------------------------------------------- */
/* Format                                                                    */
/* ------------------------------------------------------------------------- */

const setOpen = "{ ";
const setClose = " }";
const setPad = "  ";
const setSep = ",";

const seqOpen = "<< ";
const seqClose = " >>";
const seqPad = "   ";
const seqSep = ",";

const funOpen = "( ";
const funClose = " )";
const funPad = "  ";
const funSep = " @@";
const funDiv = " :>";
const funDivPad = "    ";

const recOpen = "[ ";
const recClose = " ]";
const recPad = "  ";
const recSep = ",";
const recDiv = " |->";
const recDivPad = "    ";

const subsetOpen = "SUBSET ";
const subsetClose = " ";
const subsetPad = " ";
const subsetSep = ",";

function format(value: Node, columnwidth: number, trailerwidth: number, leftpad: string): string {
  // Use the value's original format if it will fit on the line
  if (value.length() <= columnwidth - trailerwidth) return value.value();

  // Break the value over multiple lines since it won't fit on one line
  switch (value.type) {
    case CONSTANT:
      return value.value();
    case SET:
      return formatSimpleValue(value, columnwidth, trailerwidth, leftpad,
        setOpen, setClose, setPad, setSep);
    case SEQUENCE:
      return formatSimpleValue(value, columnwidth, trailerwidth, leftpad,
        seqOpen, seqClose, seqPad, seqSep);
    case FUNCTION:
      return formatPairValue(value, columnwidth, trailerwidth, leftpad,
        funOpen, funClose, funPad, funSep, funDiv, funDivPad);
    case RECORD:
      return formatPairValue(value, columnwidth, trailerwidth, leftpad,
        recOpen, recClose, recPad, recSep, recDiv, recDivPad);
    case SUBSET:
      return formatSimpleValue(value, columnwidth, trailerwidth, leftpad,
        subsetOpen, subsetClose, subsetPad, subsetSep);
    default:
      throw new FormatException(
        "TLC Bug: while formating output, the formatter called with an expression of type " +
          value.type + " while formatting " + value.value() + " and this should never happen",
      );
  }
}

function formatSimpleValue(
  list: Node,
  columnwidth: number,
  trailerwidth: number,
  leftpad: string,
  open: string,
  close: string,
  pad: string,
  sep: string,
): string {
  return (
    open +
    formatValues(
      list.children,
      columnwidth - Math.max(open.length, pad.length),
      trailerwidth + close.length,
      leftpad + pad,
      sep,
    ) +
    close
  );
}

function formatValues(
  values: Node | null,
  columnwidth: number,
  trailerwidth: number,
  leftpad: string,
  sep: string,
): string {
  let pp = "";
  for (let value = values; value !== null; value = value.next) {
    if (value.next !== null) {
      // this is not the last value in the list, so leave room for sep
      pp = pp + format(value, columnwidth, sep.length, leftpad) + sep + "\n" + leftpad;
    } else {
      // this is the last value in the list
      pp = pp + format(value, columnwidth, trailerwidth, leftpad);
    }
  }
  return pp;
}

function formatPairValue(
  list: Node,
  columnwidth: number,
  trailerwidth: number,
  leftpad: string,
  open: string,
  close: string,
  pad: string,
  sep: string,
  div: string,
  divpad: string,
): string {
  return (
    open +
    formatPairs(
      list.children,
      columnwidth - Math.max(open.length, pad.length),
      trailerwidth + close.length,
      leftpad + pad,
      sep,
      div,
      divpad,
    ) +
    close
  );
}

function formatPairs(
  pairs: Node | null,
  columnwidth: number,
  trailerwidth: number,
  leftpad: string,
  sep: string,
  div: string,
  divpad: string,
): string {
  let pp = "";
  for (let pair = pairs; pair !== null; pair = pair.next) {
    // Every pair node is built by parse{Record,Function}Pair with exactly two children.
    const arg = pair.children as Node;
    const val = arg.next as Node;

    // First suppose this pair is not the last pair in the list.  In this
    // case, don't forget to append sep to the end of the value; but don't
    // bother keeping the last trailerwidth characters open at the end of
    // the line, go ahead and use them to format the value.
    if (pair.next !== null) {
      // put argument and value on one line if they will fit
      if (arg.length() + div.length + 1 + val.length() + sep.length <= columnwidth) {
        pp = pp + arg.value() + div + " " + val.value() + sep + "\n" + leftpad;
        continue;
      }

      // put argument on one line if it will fit
      if (arg.length() + div.length <= columnwidth) {
        pp = pp + arg.value() + div +
          "\n" + leftpad + divpad +
          format(val, columnwidth - divpad.length, sep.length, leftpad + divpad) + sep +
          "\n" + leftpad;
        continue;
      }

      // format the argument on multiple lines and then the value
      pp = pp + format(arg, columnwidth, trailerwidth + div.length, leftpad) + div +
        "\n" + leftpad + divpad +
        format(val, columnwidth - divpad.length, sep.length, leftpad + divpad) + sep +
        "\n" + leftpad;
      continue;
    }

    // Now suppose this pair is the last pair in the list.  Remember to leave
    // trailerwidth space at the end of the line, but don't worry about
    // appending sep to the end of the line.

    // put argument and value on one line if they will fit
    if (arg.length() + div.length + 1 + val.length() <= columnwidth - trailerwidth) {
      pp = pp + arg.value() + div + " " + val.value();
      continue;
    }

    // put argument alone on one line if it will fit
    if (arg.length() + div.length <= columnwidth) {
      pp = pp + arg.value() + div +
        "\n" + leftpad + divpad +
        format(val, columnwidth - divpad.length, trailerwidth, leftpad + divpad);
      continue;
    }

    // format the argument on multiple lines and then the value
    pp = pp + format(arg, columnwidth, trailerwidth + div.length, leftpad) + div +
      "\n" + leftpad + divpad +
      format(val, columnwidth - divpad.length, trailerwidth, leftpad + divpad);
    continue;
  }
  return pp;
}

/* ------------------------------------------------------------------------- */
/* PrettyPrint                                                               */
/* ------------------------------------------------------------------------- */

/**
 * `tlc2.value.Values.ppr(value)` / `tlc2.pprint.PrettyPrint.mypp(value, width)`:
 * re-wraps the one-line string form of a TLC value at `width` columns.  Returns
 * `value` unchanged when it cannot be parsed, cannot be formatted, or when the
 * parse does not reach the last character.
 */
export function ppr(value: string, width = 80): string {
  try {
    const tree = parse(value, 0);
    if (tree.last < value.length - 1) {
      return value;
    }
    return format(tree, width, 0, "");
  } catch {
    // Java catches every Exception here (ParseException, FormatException and
    // the StringIndexOutOfBoundsException a bogus Node.value() can raise).
    return value;
  }
}
