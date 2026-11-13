//! Port of TLC's value pretty-printer (tlc2.pprint.{PrettyPrint,Parse,Format,Node}) via pprint.ts.
//! TLC re-parses the one-line string form of a value and re-wraps it at 80 columns. The parser is
//! deliberately naive; whenever the Java code would throw, or would not consume the whole input,
//! the input is returned unchanged. Indices are UTF-16 code units, as in Java.

#[derive(Clone, Copy, PartialEq)]
enum Ty {
    Constant,
    Set,
    Sequence,
    Record,
    RecordPair,
    Function,
    FunctionPair,
    Subset,
}

struct Node {
    ty: Ty,
    first: i64,
    last: i64,
    children: Vec<usize>,
}

enum Ex {
    Oob,
    Parse,
}
type P<T> = Result<T, Ex>;

struct Ctx<'a> {
    s: &'a [u16],
    nodes: Vec<Node>,
}

fn is_whitespace(c: u16) -> bool {
    (0x09..=0x0d).contains(&c)
        || (0x1c..=0x20).contains(&c)
        || c == 0x1680
        || (0x2000..=0x2006).contains(&c)
        || (0x2008..=0x200a).contains(&c)
        || c == 0x2028
        || c == 0x2029
        || c == 0x205f
        || c == 0x3000
}
fn is_digit(c: u16) -> bool {
    if c < 0x80 {
        return (0x30..=0x39).contains(&c);
    }
    char::from_u32(c as u32).map_or(false, is_nd)
}
fn is_nd(ch: char) -> bool {
    // decimal digits outside ASCII: approximated by "numeric and not a letter-like number"
    ch.is_numeric() && !matches!(ch as u32, 0x00B2 | 0x00B3 | 0x00B9 | 0x00BC..=0x00BE | 0x2070..=0x218F | 0x2460..=0x24FF | 0x2776..=0x2793 | 0x3007 | 0x3021..=0x3029 | 0x3038..=0x303A | 0x3192..=0x3195 | 0x3220..=0x3229 | 0x3248..=0x324F | 0x3251..=0x325F | 0x3280..=0x3289 | 0x32B1..=0x32BF)
}
fn is_letter_or_digit(c: u16) -> bool {
    if c < 0x80 {
        return (0x30..=0x39).contains(&c) || (0x41..=0x5a).contains(&c) || (0x61..=0x7a).contains(&c);
    }
    char::from_u32(c as u32).map_or(false, |ch| ch.is_alphabetic() || is_nd(ch))
}

const SS_DIV: &str = "SUBSET";

impl<'a> Ctx<'a> {
    fn char_at(&self, i: i64) -> P<u16> {
        if i < 0 || i as usize >= self.s.len() {
            return Err(Ex::Oob);
        }
        Ok(self.s[i as usize])
    }
    fn region(&self, i: i64, other: &str) -> bool {
        let o: Vec<u16> = other.encode_utf16().collect();
        if i < 0 || i as usize + o.len() > self.s.len() {
            return false;
        }
        self.s[i as usize..i as usize + o.len()] == o[..]
    }
    fn new_node(&mut self, ty: Ty, first: i64, last: i64) -> usize {
        self.nodes.push(Node { ty, first, last, children: vec![] });
        self.nodes.len() - 1
    }
    fn skip_ws(&self, index: i64) -> P<i64> {
        let mut i = index;
        loop {
            match self.char_at(i) {
                Ok(c) if is_whitespace(c) => i += 1,
                Ok(_) => return Ok(i),
                Err(_) => return Err(Ex::Parse),
            }
        }
    }
    fn parse(&mut self, index: i64) -> P<usize> {
        if self.s.is_empty() || index < 0 || index > self.s.len() as i64 - 1 {
            return Err(Ex::Parse);
        }
        let index = self.skip_ws(index)?;
        let c = self.char_at(index)?;
        let r = match c {
            0x7b => self.parse_list(index, Ty::Set),
            0x3c => self.parse_list(index, Ty::Sequence),
            0x5b => self.parse_list(index, Ty::Record),
            0x28 => self.parse_list(index, Ty::Function),
            _ if self.region(index, SS_DIV) => self.parse_subset(index),
            _ => self.parse_constant(index),
        };
        // every Java parse method converts running off the string into a ParseException
        r.map_err(|_| Ex::Parse)
    }
    fn parse_list(&mut self, index: i64, ty: Ty) -> P<usize> {
        let first = index;
        let mut last = index;
        let close: u16 = match ty {
            Ty::Set => 0x7d,
            Ty::Sequence => 0x3e,
            Ty::Record => 0x5d,
            _ => 0x29,
        };
        let mut kids = vec![];
        last += if ty == Ty::Sequence { 2 } else { 1 };
        last = self.skip_ws(last)?;
        while self.char_at(last)? != close {
            let elt = match ty {
                Ty::Record => self.parse_pair(last, Ty::RecordPair)?,
                Ty::Function => self.parse_pair(last, Ty::FunctionPair)?,
                _ => self.parse(last)?,
            };
            kids.push(elt);
            last = self.nodes[elt].last + 1;
            last = self.skip_ws(last)?;
            if ty == Ty::Function {
                if self.region(last, "@@") {
                    last += 2;
                }
            } else if self.char_at(last)? == 0x2c {
                last += 1;
            }
            last = self.skip_ws(last)?;
        }
        if ty == Ty::Sequence {
            last += 1; // the second '>' of '>>' (unchecked, as in Java)
        }
        let n = self.new_node(ty, first, last);
        self.nodes[n].children = kids;
        Ok(n)
    }
    fn parse_pair(&mut self, index: i64, ty: Ty) -> P<usize> {
        let first = index;
        let div = if ty == Ty::RecordPair { "|->" } else { ":>" };
        let field = self.parse(index)?;
        let mut last = self.nodes[field].last + 1;
        last = self.skip_ws(last)?;
        if !self.region(last, div) {
            return Err(Ex::Parse);
        }
        last += div.len() as i64;
        last = self.skip_ws(last)?;
        let value = self.parse(last)?;
        let vl = self.nodes[value].last;
        let n = self.new_node(ty, first, vl);
        self.nodes[n].children = vec![field, value];
        Ok(n)
    }
    fn parse_subset(&mut self, index: i64) -> P<usize> {
        let mut last = index + 6;
        last = self.skip_ws(last)?;
        let elt = self.parse(last)?;
        let el = self.nodes[elt].last;
        let n = self.new_node(Ty::Subset, index, el);
        self.nodes[n].children = vec![elt];
        Ok(n)
    }
    fn parse_constant(&mut self, index: i64) -> P<usize> {
        let first = self.skip_ws(index)?;
        let mut last = first;
        let len = self.s.len() as i64;
        if self.char_at(first)? == 0x22 {
            // a string constant (NB: no notion of escaped quotes)
            loop {
                last += 1;
                if self.char_at(last)? == 0x22 {
                    break;
                }
            }
            return Ok(self.new_node(Ty::Constant, first, last));
        }
        if is_digit(self.char_at(last)?) {
            if let Some(n) = self.parse_interval(index)? {
                return Ok(n);
            }
        }
        if self.char_at(last)? == 0x2d {
            last += 1;
            while is_digit(self.char_at(last)?) {
                last += 1;
                if last == len {
                    break;
                }
            }
            last -= 1;
            return Ok(self.new_node(Ty::Constant, first, last));
        }
        if is_letter_or_digit(self.char_at(last)?) {
            while is_letter_or_digit(self.char_at(last)?) {
                last += 1;
                if last == len {
                    break;
                }
            }
            last -= 1;
            return Ok(self.new_node(Ty::Constant, first, last));
        }
        Err(Ex::Parse)
    }
    /// i..j for integers i and j; None if the parse fails (also when it runs off the string).
    fn parse_interval(&mut self, index: i64) -> P<Option<usize>> {
        let r: P<Option<(i64, i64)>> = (|| {
            let first = index;
            let mut last = first;
            let len = self.s.len() as i64;
            if !is_digit(self.char_at(last)?) {
                return Ok(None);
            }
            while last < len && is_digit(self.char_at(last)?) {
                last += 1;
            }
            if !self.region(last, "..") {
                return Ok(None);
            }
            last += 2;
            if !is_digit(self.char_at(last)?) {
                return Ok(None);
            }
            while is_digit(self.char_at(last)?) {
                last += 1;
                if last == len {
                    break;
                }
            }
            last -= 1;
            Ok(Some((first, last)))
        })();
        match r {
            Ok(Some((f, l))) => Ok(Some(self.new_node(Ty::Constant, f, l))),
            Ok(None) | Err(Ex::Oob) => Ok(None),
            Err(e) => Err(e),
        }
    }

    // ---- Format ----
    fn len(&self, n: usize) -> i64 {
        self.nodes[n].last - self.nodes[n].first + 1
    }
    fn value(&self, n: usize) -> P<String> {
        let (b, e) = (self.nodes[n].first, self.nodes[n].last + 1);
        if b < 0 || e > self.s.len() as i64 || b > e {
            return Err(Ex::Oob);
        }
        Ok(String::from_utf16_lossy(&self.s[b as usize..e as usize]))
    }
    fn format(&self, v: usize, columnwidth: i64, trailerwidth: i64, leftpad: &str) -> P<String> {
        if self.len(v) <= columnwidth - trailerwidth {
            return self.value(v);
        }
        match self.nodes[v].ty {
            Ty::Constant => self.value(v),
            Ty::Set => self.simple(v, columnwidth, trailerwidth, leftpad, "{ ", " }", "  ", ","),
            Ty::Sequence => self.simple(v, columnwidth, trailerwidth, leftpad, "<< ", " >>", "   ", ","),
            Ty::Function => self.pair_value(v, columnwidth, trailerwidth, leftpad, "( ", " )", "  ", " @@", " :>", "    "),
            Ty::Record => self.pair_value(v, columnwidth, trailerwidth, leftpad, "[ ", " ]", "  ", ",", " |->", "    "),
            Ty::Subset => self.simple(v, columnwidth, trailerwidth, leftpad, "SUBSET ", " ", " ", ","),
            _ => Err(Ex::Parse),
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn simple(&self, list: usize, cw: i64, tw: i64, leftpad: &str, open: &str, close: &str, pad: &str, sep: &str) -> P<String> {
        let cw2 = cw - open.len().max(pad.len()) as i64;
        let tw2 = tw + close.len() as i64;
        let lp = format!("{}{}", leftpad, pad);
        let kids = &self.nodes[list].children;
        let mut pp = String::from(open);
        for (i, &v) in kids.iter().enumerate() {
            if i + 1 < kids.len() {
                pp += &self.format(v, cw2, sep.len() as i64, &lp)?;
                pp += sep;
                pp.push('\n');
                pp += &lp;
            } else {
                pp += &self.format(v, cw2, tw2, &lp)?;
            }
        }
        pp += close;
        Ok(pp)
    }
    #[allow(clippy::too_many_arguments)]
    fn pair_value(&self, list: usize, cw: i64, tw: i64, leftpad: &str, open: &str, close: &str, pad: &str, sep: &str, div: &str, divpad: &str) -> P<String> {
        let columnwidth = cw - open.len().max(pad.len()) as i64;
        let trailerwidth = tw + close.len() as i64;
        let leftpad = format!("{}{}", leftpad, pad);
        let lp2 = format!("{}{}", leftpad, divpad);
        let (dl, sl, dpl) = (div.len() as i64, sep.len() as i64, divpad.len() as i64);
        let kids = &self.nodes[list].children;
        let mut pp = String::from(open);
        for (i, &pair) in kids.iter().enumerate() {
            let arg = self.nodes[pair].children[0];
            let val = self.nodes[pair].children[1];
            if i + 1 < kids.len() {
                if self.len(arg) + dl + 1 + self.len(val) + sl <= columnwidth {
                    pp += &format!("{}{} {}{}\n{}", self.value(arg)?, div, self.value(val)?, sep, leftpad);
                    continue;
                }
                if self.len(arg) + dl <= columnwidth {
                    pp += &format!("{}{}\n{}{}{}\n{}", self.value(arg)?, div, lp2, self.format(val, columnwidth - dpl, sl, &lp2)?, sep, leftpad);
                    continue;
                }
                pp += &format!("{}{}\n{}{}{}\n{}", self.format(arg, columnwidth, trailerwidth + dl, &leftpad)?, div, lp2, self.format(val, columnwidth - dpl, sl, &lp2)?, sep, leftpad);
                continue;
            }
            if self.len(arg) + dl + 1 + self.len(val) <= columnwidth - trailerwidth {
                pp += &format!("{}{} {}", self.value(arg)?, div, self.value(val)?);
                continue;
            }
            if self.len(arg) + dl <= columnwidth {
                pp += &format!("{}{}\n{}{}", self.value(arg)?, div, lp2, self.format(val, columnwidth - dpl, trailerwidth, &lp2)?);
                continue;
            }
            pp += &format!("{}{}\n{}{}", self.format(arg, columnwidth, trailerwidth + dl, &leftpad)?, div, lp2, self.format(val, columnwidth - dpl, trailerwidth, &lp2)?);
        }
        pp += close;
        Ok(pp)
    }
}

/// `tlc2.value.Values.ppr(value)`: re-wraps the one-line string form of a TLC value at 80 columns.
pub fn ppr(value: &str) -> String {
    ppr_width(value, 80)
}
pub fn ppr_width(value: &str, width: i64) -> String {
    if value.len() as i64 <= width && !value.starts_with(|c: char| c.is_whitespace()) {
        // fast path: a value that parses completely and fits is returned as is; one that does not parse is
        // returned as is as well
        return value.to_string();
    }
    let s: Vec<u16> = value.encode_utf16().collect();
    let mut c = Ctx { s: &s, nodes: Vec::new() };
    let tree = match c.parse(0) {
        Ok(t) => t,
        Err(_) => return value.to_string(),
    };
    if c.nodes[tree].last < s.len() as i64 - 1 {
        return value.to_string();
    }
    c.format(tree, width, 0, "").unwrap_or_else(|_| value.to_string())
}
