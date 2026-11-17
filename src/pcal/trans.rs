//! The driver of the PlusCal translator (port of pcal.trans and pcal.Validator): options,
//! locating the algorithm and the translation in the module, checksums, and the files written.
use super::ast::{Ast, Printer};
use super::symtab::SymTab;
use super::tokenize::CharReader;
use super::{err, version_to_number, Ctx, PR};
use crate::host::HostRef;

pub const STATUS_OK: i32 = 1;
pub const STATUS_EXIT_WITHOUT_ERROR: i32 = 0;
pub const STATUS_EXIT_WITH_ERRORS: i32 = -1;

const BEGIN_LINE: &str = "\\* BEGIN TRANSLATION";
const END_LINE: &str = "\\* END TRANSLATION";
const CFG_FILE_DELIMITER: &str = "\\* Add statements after this line.";
const HELP: &str = include_str!("help.txt");

type Line = Vec<char>;

// ---- small string helpers on lines of characters ----
fn chars(s: &str) -> Line {
    s.chars().collect()
}
fn index_of(line: &[char], pat: &str, from: usize) -> Option<usize> {
    let p: Line = chars(pat);
    if p.is_empty() {
        return Some(from.min(line.len()));
    }
    if line.len() < p.len() {
        return None;
    }
    (from..=line.len() - p.len()).find(|i| line[*i..*i + p.len()] == p[..])
}
fn starts_with_at(line: &[char], at: usize, pat: &str) -> bool {
    let p: Line = chars(pat);
    at + p.len() <= line.len() && line[at..at + p.len()] == p[..]
}
fn java_trim(s: &[char]) -> String {
    let t: String = s.iter().collect();
    t.trim_matches(|c: char| c <= ' ').to_string()
}

/// `Files.readAllLines`: lines end at "\n", "\r\n" or "\r"; the input must be valid UTF-8.
pub fn read_all_lines(bytes: &[u8]) -> Option<Vec<String>> {
    let text = std::str::from_utf8(bytes).ok()?;
    Some(split_lines(text))
}
pub fn split_lines(text: &str) -> Vec<String> {
    let mut lines = vec![];
    let mut cur = String::new();
    let mut it = text.chars().peekable();
    let mut pending = false;
    while let Some(c) = it.next() {
        pending = true;
        match c {
            '\n' => {
                lines.push(std::mem::take(&mut cur));
                pending = false;
            }
            '\r' => {
                if it.peek() == Some(&'\n') {
                    it.next();
                }
                lines.push(std::mem::take(&mut cur));
                pending = false;
            }
            c => cur.push(c),
        }
    }
    if pending {
        lines.push(cur);
    }
    lines
}

/// Expands tabs and appends a space to every line.
pub fn remove_tabs(input: &[String]) -> Vec<Line> {
    input
        .iter()
        .map(|old| {
            let mut new: Line = Vec::with_capacity(old.len() + 1);
            for c in old.chars() {
                if c == '\t' {
                    let n = 8 - (new.len() % 8);
                    new.extend(std::iter::repeat(' ').take(n));
                } else {
                    new.push(c);
                }
            }
            new.push(' ');
            new
        })
        .collect()
}

fn find_token_pair(vec: &[Line], line_num: usize, tok1: &str, tok2: &str) -> Option<usize> {
    for i in line_num..vec.len() {
        let line = &vec[i];
        if let Some(col) = index_of(line, tok1, 0) {
            let mut next = col + tok1.chars().count();
            while next < line.len() && line[next] == ' ' {
                next += 1;
            }
            if next < line.len() && Some(next) == index_of(line, tok2, 0) {
                return Some(i);
            }
        }
    }
    None
}

// ---- the options statement in the file ----
fn goto_next_non_space<'a>(vec: &'a [Line], loc: &mut (usize, usize)) -> &'a [char] {
    let mut found = false;
    while !found && loc.0 < vec.len() {
        let line = &vec[loc.0];
        while !found && loc.1 < line.len() {
            if line[loc.1] == ' ' {
                loc.1 += 1;
            } else {
                found = true;
            }
        }
        if !found {
            loc.0 += 1;
            loc.1 = 0;
        }
    }
    if loc.0 < vec.len() { &vec[loc.0] } else { &[] }
}
fn next_col(line: &[char], col: usize, delims: &[char]) -> usize {
    (col..line.len()).find(|i| delims.contains(&line[*i])).unwrap_or(line.len())
}
fn find_token(token: &str, vec: &[Line], loc: &mut (usize, usize)) -> bool {
    let n = token.chars().count();
    let mut found = false;
    while !found && loc.0 < vec.len() {
        let line = goto_next_non_space(vec, loc);
        if starts_with_at(line, loc.1, token) {
            let end = loc.1 + n;
            if end >= line.len() || !(line[end].is_alphabetic() || line[end] == '_') {
                found = true;
                loc.1 = end;
            }
        }
        loc.1 = next_col(line, loc.1.min(line.len()), &[' ']);
    }
    found
}
fn next_non_id_char(s: &[char], col: usize) -> usize {
    let mut cur = col;
    while cur < s.len() && (s[cur].is_alphanumeric() || s[cur] == '_') {
        cur += 1;
    }
    cur
}

fn process_options(ctx: &mut Ctx, vec: &[Line], loc: &mut (usize, usize)) -> i32 {
    let line = goto_next_non_space(vec, loc);
    if !starts_with_at(line, loc.1, "options") {
        return STATUS_OK;
    }
    loc.1 += 7;
    let line = goto_next_non_space(vec, loc);
    if !starts_with_at(line, loc.1, "(") {
        loc.0 = vec.len();
        ctx.report_error("`PlusCal options' not followed by '('");
        return STATUS_EXIT_WITH_ERRORS;
    }
    loc.1 += 1;
    let mut line = goto_next_non_space(vec, loc);
    let mut args: Vec<String> = vec![];
    while loc.0 < vec.len() && line[loc.1] != ')' {
        if line[loc.1] == ',' {
            loc.1 += 1;
        } else {
            let end = next_col(line, loc.1, &[' ', ',', ')']);
            args.push(line[loc.1..end].iter().collect());
            loc.1 = end;
        }
        line = goto_next_non_space(vec, loc);
    }
    if loc.0 >= vec.len() {
        ctx.report_error("No closing ')' found in options statement");
        return STATUS_EXIT_WITH_ERRORS;
    }
    loc.1 += 1;
    goto_next_non_space(vec, loc);
    args.push(String::new());
    parse_and_process_arguments(ctx, &args)
}

/// Looks for a `PlusCal options (...)` statement and applies it.
fn find_and_process_options(ctx: &mut Ctx, untab: &[Line]) {
    let mut loc = (0usize, 0usize);
    loop {
        if !find_token("PlusCal", untab, &mut loc) {
            return;
        }
        let line = goto_next_non_space(untab, &mut loc);
        let rest = &line[loc.1.min(line.len())..];
        if starts_with_at(rest, 0, "options") && next_non_id_char(rest, 0) == 7 {
            ctx.options_in_file = true;
            process_options(ctx, untab, &mut loc);
            return;
        }
    }
}

fn command_line_error(ctx: &mut Ctx, msg: &str) -> i32 {
    ctx.report_error(&format!("Command-line error: {}.", msg));
    STATUS_EXIT_WITH_ERRORS
}
fn output_help(ctx: &mut Ctx) -> i32 {
    for l in split_lines(HELP) {
        ctx.out.push(l);
    }
    STATUS_EXIT_WITHOUT_ERROR
}
fn valid_label_root(s: &str) -> bool {
    let mut cs = s.chars();
    matches!(cs.next(), Some(c) if c.is_ascii_alphabetic()) && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
}
fn java_parse_int(s: &str) -> Option<i32> {
    let digits = s.strip_prefix('-').or_else(|| s.strip_prefix('+')).unwrap_or(s);
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    s.strip_prefix('+').unwrap_or(s).parse::<i32>().ok()
}

/// `trans.parseAndProcessArguments`, for the command line and for the options statement.
pub fn parse_and_process_arguments(ctx: &mut Ctx, args: &[String]) -> i32 {
    let in_file = ctx.options_in_file;
    let not_in_file = !in_file;
    let mut first_fairness = in_file;
    let mut explicit_nof = false;
    if args.is_empty() {
        return command_line_error(ctx, "No arguments specified");
    }
    let max_arg = args.len() - 1;
    if not_in_file && args[max_arg].starts_with('-') {
        return output_help(ctx);
    }
    let conflicting = |ctx: &mut Ctx| -> bool {
        let n = [ctx.spec_option, ctx.myspec_option, ctx.spec2_option, ctx.myspec2_option, ctx.write_ast_flag].iter().filter(|b| **b).count();
        if n > 1 {
            command_line_error(ctx, "\nCan have at most one of the options -spec, -myspec, -spec2, -myspec2, writeAST");
            return true;
        }
        false
    };
    let mut next_arg = 0;
    while next_arg < max_arg {
        let option = args[next_arg].as_str();
        let is = |name: &str| option.strip_prefix('-') == Some(name) || (in_file && option == name);
        if not_in_file && option == "-help" {
            return output_help(ctx);
        } else if not_in_file && option == "-writeAST" {
            ctx.write_ast_flag = true;
            if conflicting(ctx) {
                return STATUS_EXIT_WITH_ERRORS;
            }
        } else if is("spec") || is("myspec") || (not_in_file && (option == "-spec2" || option == "-myspec2")) {
            let name = option.trim_start_matches('-');
            match name {
                "spec" => ctx.spec_option = true,
                "myspec" => ctx.myspec_option = true,
                "spec2" => ctx.spec2_option = true,
                _ => ctx.myspec2_option = true,
            }
            if conflicting(ctx) {
                return STATUS_EXIT_WITH_ERRORS;
            }
            next_arg += 1;
            if next_arg == max_arg {
                let which = if name.starts_with("my") { "-myspec" } else { "-spec" };
                return command_line_error(ctx, &format!("Specification name must follow `{}' option", which));
            }
            ctx.spec_file = args[next_arg].clone();
        } else if not_in_file && option == "-debug" {
            ctx.debug = true;
        } else if not_in_file && option == "-unixEOL" {
            ctx.unix_eol = true;
        } else if is("termination") {
            ctx.check_termination = true;
        } else if option == "-noold" {
            ctx.no_old = true;
        } else if option == "-nocfg" {
            ctx.nocfg = true;
        } else if is("noDoneDisjunct") {
            ctx.no_done_disjunct = true;
        } else if is("wf") || is("sf") || is("wfNext") || is("nof") {
            if first_fairness {
                ctx.fairness_option = String::new();
                first_fairness = false;
            }
            if !ctx.fairness_option.is_empty() {
                return command_line_error(ctx, "Can only have one of -wf, -sf, -wfNext, and -nof options");
            }
            ctx.fairness_option = option.trim_start_matches('-').to_string();
            if ctx.fairness_option == "nof" {
                explicit_nof = true;
            }
        } else if is("label") {
            ctx.label_flag = true;
        } else if not_in_file && option == "-reportLabels" {
            ctx.report_labels_flag = true;
            ctx.label_flag = true;
        } else if is("labelRoot") {
            next_arg += 1;
            if next_arg == max_arg {
                return command_line_error(ctx, "Label root must follow `-labelRoot' option");
            }
            if !valid_label_root(&args[next_arg]) {
                return command_line_error(ctx, "Label root must be a valid PlusCal identifier (must start with a letter and contain only letters, numbers, and underscores)");
            }
            ctx.label_root = args[next_arg].clone();
        } else if is("version") {
            next_arg += 1;
            if next_arg == max_arg {
                return command_line_error(ctx, "Version number must follow `-version' option");
            }
            let v = args[next_arg].clone();
            if !ctx.process_version(&v) {
                return command_line_error(ctx, "Bad version number");
            }
        } else if option == "-lineWidth" {
            next_arg += 1;
            let a = if next_arg == max_arg { None } else { java_parse_int(&args[next_arg]) };
            match a {
                Some(a) if a >= 60 => {
                    ctx.wrap_column = a;
                    ctx.ss_wrap_column = a - 33;
                }
                _ => return command_line_error(ctx, "Integer value at least 60 must follow `-lineWidth' option"),
            }
        } else if not_in_file {
            return command_line_error(ctx, &format!("Unknown command-line option: {}", option));
        } else {
            return command_line_error(ctx, &format!("Unknown or illegal option in options statement: {}", option));
        }
        next_arg += 1;
    }
    if next_arg > max_arg {
        return command_line_error(ctx, "No input file specified");
    }
    if ctx.check_termination && ctx.fairness_option.is_empty() && !explicit_nof {
        ctx.fairness_option = "wf".to_string();
    }
    if in_file {
        return STATUS_OK;
    }
    // the input file: a name without extension, or with the extension tla
    let path = args[max_arg].as_str();
    let name_start = path.rfind(|c| c == '/' || (cfg!(windows) && c == '\\')).map(|i| i + 1).unwrap_or(0);
    let name = &path[name_start..];
    match name.rfind('.') {
        None => ctx.tla_input_file = path.to_string(),
        Some(_) => {
            if name.to_lowercase().ends_with(".tla") {
                ctx.tla_input_file = path[..path.rfind('.').unwrap()].to_string();
            } else {
                return command_line_error(ctx, "Input file has extension other than tla");
            }
        }
    }
    STATUS_OK
}

// ---- comments ----
/// Blanks out the comments nested in the algorithm, up to the end of the comment that contains it.
fn uncomment(inp: &mut [Line], beg_line: usize, beg_col: usize) -> PR<()> {
    let mut line = beg_line;
    let mut col = beg_col;
    let mut not_done = true;
    let mut comment_depth = 0;
    let mut new_line: Line = inp[line][..col.min(inp[line].len())].to_vec();
    while not_done && line < inp.len() {
        let old = inp[line].clone();
        let mut in_string = false;
        while not_done && col < old.len() {
            let in_char = old[col];
            let mut out_char = in_char;
            let has_next = col + 1 < old.len();
            if in_char == '(' && !in_string && has_next && old[col + 1] == '*' {
                comment_depth += 1;
                out_char = ' ';
                col += 1;
                new_line.push(out_char);
            } else if in_char == '*' && !in_string && has_next && old[col + 1] == ')' {
                if comment_depth == 0 {
                    new_line.push(in_char);
                    out_char = ')';
                    col += 1;
                    not_done = false;
                } else {
                    comment_depth -= 1;
                    out_char = ' ';
                    col += 1;
                    new_line.push(out_char);
                }
            } else if comment_depth == 0 {
                if in_string {
                    if in_char == '"' {
                        in_string = false;
                    } else if in_char == '\\' && has_next {
                        new_line.push(in_char);
                        out_char = old[col + 1];
                        col += 1;
                    }
                } else if in_char == '\\' && has_next && old[col + 1] == '*' {
                    out_char = ' ';
                    col = old.len();
                } else if in_char == '"' {
                    in_string = true;
                }
            } else {
                out_char = ' ';
            }
            new_line.push(out_char);
            col += 1;
        }
        if in_string {
            return err(format!("Unterminated string in line {}", line + 1));
        }
        inp[line] = std::mem::take(&mut new_line);
        col = 0;
        line += 1;
    }
    Ok(())
}

// ---- checksums ----
fn crc32(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    for &b in data {
        crc ^= b as u32;
        for _ in 0..8 {
            crc = if crc & 1 != 0 { (crc >> 1) ^ 0xEDB8_8320 } else { crc >> 1 };
        }
    }
    !crc
}
pub fn checksum(s: &str) -> String {
    format!("{:x}", crc32(s.as_bytes()))
}
fn checksum_lines(lines: &[String]) -> String {
    checksum(&lines.concat())
}

struct ChecksumMatch {
    /// (start, end) in characters of the hexadecimal digits, when the checksum is given as a string
    pcal: Option<(usize, usize)>,
    tla: Option<(usize, usize)>,
}
fn is_java_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r')
}
/// The regular expression `Validator.CHECKSUM_PATTERN`, matched by hand.
fn match_checksums(line: &[char]) -> Option<ChecksumMatch> {
    let mut from = 0;
    while let Some(start) = index_of(line, BEGIN_LINE, from) {
        from = start + 1;
        let mut i = start + BEGIN_LINE.chars().count();
        let skip_ws = |i: &mut usize| {
            while *i < line.len() && is_java_space(line[*i]) {
                *i += 1;
            }
        };
        let lit = |i: &mut usize, s: &str, ci: bool| -> bool {
            let p: Line = chars(s);
            if *i + p.len() > line.len() {
                return false;
            }
            let ok = (0..p.len()).all(|k| if ci { line[*i + k].to_lowercase().eq(p[k].to_lowercase()) } else { line[*i + k] == p[k] });
            if ok {
                *i += p.len();
            }
            ok
        };
        let value = |i: &mut usize| -> Option<Option<(usize, usize)>> {
            if lit(i, "=", false) {
                skip_ws(i);
                if !lit(i, "\"", false) {
                    return None;
                }
                let s = *i;
                while *i < line.len() && line[*i].is_ascii_hexdigit() {
                    *i += 1;
                }
                let e = *i;
                if !lit(i, "\"", false) {
                    return None;
                }
                Some(Some((s, e)))
            } else if lit(i, "\\in", false) {
                skip_ws(i);
                if !lit(i, "STRING", false) {
                    return None;
                }
                Some(None)
            } else {
                None
            }
        };
        let attempt = (|| -> Option<ChecksumMatch> {
            let ws = i;
            skip_ws(&mut i);
            if i == ws || !lit(&mut i, "(", false) {
                return None;
            }
            skip_ws(&mut i);
            if !(lit(&mut i, "chksum", true) || lit(&mut i, "checksum", true)) {
                return None;
            }
            if !(lit(&mut i, "(pcal)", true) || lit(&mut i, "(pluscal)", true)) {
                return None;
            }
            skip_ws(&mut i);
            let pcal = value(&mut i)?;
            skip_ws(&mut i);
            if !lit(&mut i, "/\\", false) {
                return None;
            }
            skip_ws(&mut i);
            if !(lit(&mut i, "chksum", true) || lit(&mut i, "checksum", true)) {
                return None;
            }
            if !(lit(&mut i, "(tla)", true) || lit(&mut i, "(tla+)", true)) {
                return None;
            }
            skip_ws(&mut i);
            let tla = value(&mut i)?;
            skip_ws(&mut i);
            if !lit(&mut i, ")", false) {
                return None;
            }
            Some(ChecksumMatch { pcal, tla })
        })();
        if attempt.is_some() {
            return attempt;
        }
    }
    None
}
fn replace_range(line: &str, range: (usize, usize), with: &str) -> String {
    let c: Line = chars(line);
    let mut s: String = c[..range.0].iter().collect();
    s += with;
    s.extend(c[range.1..].iter());
    s
}

// ---- translation ----
fn ast_to_string(ctx: &Ctx, ast: &Ast) -> String {
    let mut p = Printer::new(ctx.debug, ctx.input_version_number < version_to_number("1.5"));
    p.print(ast)
}
fn pcal_checksum(ctx: &Ctx, ast: &Ast, fair: bool) -> String {
    if fair { checksum("fair") } else { checksum(&ast_to_string(ctx, ast)) }
}

/// Where the algorithm starts: (line, column after the keyword, whether it is `--fair`).
fn find_algorithm(untab: &[Line]) -> Option<(usize, usize, bool)> {
    for (i, line) in untab.iter().enumerate() {
        if let Some(c) = index_of(line, "--algorithm", 0) {
            return Some((i, c + 11, false));
        }
        if let Some(c) = index_of(line, "--fair", 0) {
            return Some((i, c + 6, true));
        }
    }
    None
}

/// Parsing, renaming and generation (`ParseAlgorithm.getAlgorithm`, `PCalTLAGenerator`).
fn translate_algorithm(ctx: &mut Ctx, reader: CharReader, fair: bool) -> PR<(Ast, Option<Vec<String>>)> {
    let ast = ctx.get_algorithm(reader, fair)?;
    ctx.report_info("Parsing completed.");
    if ctx.write_ast_flag {
        return Ok((ast, None));
    }
    let mut st = SymTab::new(&ast)?;
    st.disambiguate();
    if !st.disambiguate_report.is_empty() {
        ctx.report_warning("symbols were renamed.");
    }
    if !st.error_report.is_empty() {
        return err(st.error_report.clone());
    }
    st.fix(&ast, ctx)?;
    if ctx.tlc_translation() {
        return err("The -spec and -myspec options (translation by running TLC on the PlusCal specification) are not supported by everystate");
    }
    let xast = super::explode::explode(&ast, &st, ctx)?;
    let report = st.disambiguate_report.clone();
    let translation = super::gen::generate(&xast, &st, ctx, &report)?;
    if ctx.has_default_initialization {
        st.check_for_default_init_value()?;
    }
    Ok((ast, Some(translation)))
}

/// The lines of `AST.tla` that the -writeAST option produces.
fn ast_file(ctx: &Ctx, ast: &Ast) -> Vec<String> {
    vec![
        "------ MODULE AST -------".to_string(),
        "EXTENDS TLC".to_string(),
        format!("fairness == \"{}\"", ctx.fairness_option),
        " ".to_string(),
        "ast == ".to_string(),
        ast_to_string(ctx, ast),
        "==========================".to_string(),
    ]
}

pub struct Translated {
    /// The lines of the new module, or None when the translation failed (or only wrote the AST).
    pub output: Option<Vec<String>>,
    /// The lines of AST.tla, with -writeAST.
    pub ast_file: Option<Vec<String>>,
}

/// `trans.performTranslation`
pub fn perform_translation(ctx: &mut Ctx, spec: &[String]) -> Translated {
    let failed = Translated { output: None, ast_file: None };
    let mut untab = remove_tabs(spec);
    find_and_process_options(ctx, &untab);
    let mut output: Vec<String> = spec.to_vec();
    let mut translation_line = find_token_pair(&untab, 0, "BEGIN", "TRANSLATION");
    if let Some(tl) = translation_line {
        let end = match find_token_pair(&untab, tl + 1, "END", "TRANSLATION") {
            Some(e) => e,
            None => {
                ctx.report_error("No line containing `END TRANSLATION");
                return failed;
            }
        };
        if end > tl + 1 {
            output.drain(tl + 1..end);
            untab.drain(tl + 1..end);
        }
    }
    let (alg_line, alg_col, fair) = match find_algorithm(&untab) {
        Some(x) => x,
        None => {
            ctx.report_error("Beginning of algorithm string --algorithm not found.");
            return failed;
        }
    };
    let translation_line = match translation_line.take() {
        Some(tl) => tl,
        None => {
            // find the end of the comment that contains the algorithm and add the two lines after it
            let mut depth = 1;
            let (mut ec_line, mut ec_col) = (alg_line, alg_col);
            let mut not_found = true;
            while not_found && ec_line < untab.len() {
                let line = &untab[ec_line];
                while not_found && ec_col + 1 < line.len() {
                    if line[ec_col] == '(' && line[ec_col + 1] == '*' {
                        depth += 1;
                        ec_col += 2;
                    } else if line[ec_col] == '*' && line[ec_col + 1] == ')' {
                        depth -= 1;
                        ec_col += 2;
                        if depth == 0 {
                            not_found = false;
                        }
                    } else {
                        ec_col += 1;
                    }
                }
                if not_found {
                    ec_line += 1;
                    ec_col = 0;
                }
            }
            if not_found {
                ctx.report_error("Algorithm not in properly terminated comment");
                return failed;
            }
            let end_stuff = java_trim(&untab[ec_line][ec_col.min(untab[ec_line].len())..]);
            if !end_stuff.is_empty() && !end_stuff.starts_with("\\*") {
                ctx.report_error("Text on same line following `*)' that ends the \n   comment containing the algorithm.");
                return failed;
            }
            output.insert(ec_line + 1, format!("{} (chksum(pcal) = \"ffffffff\" /\\ chksum(tla) = \"ffffffff\")", BEGIN_LINE));
            untab.insert(ec_line + 1, chars(BEGIN_LINE));
            output.insert(ec_line + 2, format!("{} ", END_LINE));
            untab.insert(ec_line + 2, chars(END_LINE));
            ec_line + 1
        }
    };
    if let Err(e) = uncomment(&mut untab, alg_line, alg_col) {
        ctx.report(&e);
        return failed;
    }
    let reader = CharReader::new(untab, alg_line, alg_col, output.len(), 0);
    let (ast, translation) = match translate_algorithm(ctx, reader, fair) {
        Ok(x) => x,
        Err(e) => {
            ctx.report(&e);
            return failed;
        }
    };
    let translation = match translation {
        Some(t) => t,
        None => return Translated { output: None, ast_file: Some(ast_file(ctx, &ast)) },
    };
    let begin: Line = chars(&output[translation_line]);
    if let Some(m) = match_checksums(&begin) {
        if let Some(r) = m.tla {
            output[translation_line] = replace_range(&output[translation_line], r, &checksum_lines(&translation));
        }
        if let Some(r) = m.pcal {
            output[translation_line] = replace_range(&output[translation_line], r, &pcal_checksum(ctx, &ast, fair));
        }
    }
    for (i, l) in translation.into_iter().enumerate() {
        output.insert(translation_line + 1 + i, l);
    }
    ctx.report_info("Translation completed.");
    Translated { output: Some(output), ast_file: None }
}

// ---- validation of an existing translation (what SANY does when TLC loads a module) ----
#[derive(Default, Debug, PartialEq)]
pub struct Divergence {
    pub pcal: bool,
    pub tla: bool,
    pub error: bool,
}

/// `Validator.validate`: compares the checksums in the BEGIN TRANSLATION line of a module with the
/// algorithm and the translation in it.  `messages` receives what the translator prints on the way.
pub fn validate(spec: &[String], messages: &mut Vec<String>) -> Divergence {
    let mut res = Divergence::default();
    if !spec.iter().any(|l| l.find("algorithm").map(|i| i > 0).unwrap_or(false)) {
        return res;
    }
    let mut ctx = Ctx::new();
    let mut untab = remove_tabs(spec);
    find_and_process_options(&mut ctx, &untab);
    let alg = find_algorithm(&untab);
    let translation_line = find_token_pair(&untab, 0, "BEGIN", "TRANSLATION");
    let end_line = find_token_pair(&untab, translation_line.map(|t| t + 1).unwrap_or(0), "END", "TRANSLATION");
    let (translation_line, end_line) = match (translation_line, end_line) {
        (Some(t), Some(e)) => (t, e),
        _ => {
            messages.append(&mut ctx.out);
            return res;
        }
    };
    if let Some((alg_line, alg_col, fair)) = alg {
        if let Err(e) = uncomment(&mut untab, alg_line, alg_col) {
            ctx.report(&e);
            messages.append(&mut ctx.out);
            res.error = true;
            return res;
        }
        let begin = untab[translation_line].clone();
        let reader = CharReader::new(untab, alg_line, alg_col, spec.len(), 0);
        let ast = match translate_algorithm(&mut ctx, reader, fair) {
            Ok((ast, _)) => Some(ast),
            Err(e) => {
                ctx.report(&e);
                None
            }
        };
        if let Some(m) = match_checksums(&begin) {
            if let Some((s, e)) = m.pcal {
                let stored: String = begin[s..e].iter().collect();
                let actual = match &ast {
                    _ if fair => Some(checksum("fair")),
                    Some(a) => Some(checksum(&ast_to_string(&ctx, a))),
                    None => None,
                };
                if actual.as_deref() != Some(stored.as_str()) {
                    res.pcal = true;
                }
            }
            if let Some((s, e)) = m.tla {
                let stored: String = begin[s..e].iter().collect();
                if stored != checksum_lines(&spec[translation_line + 1..end_line.max(translation_line + 1)]) {
                    res.tla = true;
                }
            }
        }
    }
    // only the errors are of interest to the caller, not the progress messages
    messages.extend(ctx.out.drain(..).filter(|m| m.starts_with("\nUnrecoverable error")));
    res
}

// ---- entry points ----
/// Translates the text of a module.  `options` are command-line options without the file name.
/// Returns the new text (None on failure) and the messages of the translator.
pub fn translate_text(source: &str, options: &[String]) -> (Option<String>, Vec<String>) {
    let mut ctx = Ctx::new();
    let mut args: Vec<String> = options.to_vec();
    args.push("Spec".to_string());
    if parse_and_process_arguments(&mut ctx, &args) != STATUS_OK {
        return (None, ctx.out);
    }
    let spec = split_lines(source);
    let res = perform_translation(&mut ctx, &spec);
    let text = res.output.map(|lines| {
        let mut s = String::new();
        for l in lines {
            s += &l;
            s.push('\n');
        }
        s
    });
    (text, ctx.out)
}

fn exit_status(status: i32) -> i32 {
    if status < 0 { 255 } else { status }
}
fn join_lines(lines: &[String], eol: &str) -> Vec<u8> {
    let mut s = String::new();
    for l in lines {
        s += l;
        s += eol;
    }
    s.into_bytes()
}

/// `java pcal.trans args`: translates the file in place, writes `File.old` and updates `File.cfg`.
/// Returns the exit status.
pub fn run(args: &[String], host: HostRef) -> i32 {
    let mut ctx = Ctx::new();
    ctx.report_info(&format!("pcal.trans Version {} of {}", super::VERSION, super::MOD_DATE));
    let status = run_inner(&mut ctx, args, &host);
    let mut text = String::new();
    for l in &ctx.out {
        text += l;
        text.push('\n');
    }
    host.print(&text);
    exit_status(status)
}

fn run_inner(ctx: &mut Ctx, args: &[String], host: &HostRef) -> i32 {
    let status = parse_and_process_arguments(ctx, args);
    if status != STATUS_OK {
        return status;
    }
    let eol = if cfg!(windows) && !ctx.unix_eol { "\r\n" } else { "\n" };
    let tla = format!("{}.tla", ctx.tla_input_file);
    if !host.exists(&tla) {
        ctx.report_error(&format!("Input file {} not found", tla));
        return STATUS_EXIT_WITH_ERRORS;
    }
    let bytes = host.read_file(&tla).ok();
    let input = match bytes.as_deref().and_then(read_all_lines) {
        Some(l) => l,
        None => {
            ctx.report_error(&format!("Error reading file {}.", tla));
            return STATUS_EXIT_WITH_ERRORS;
        }
    };
    let res = perform_translation(ctx, &input);
    if let Some(ast) = res.ast_file {
        if host.write_file("AST.tla", &join_lines(&ast, eol)).is_err() {
            ctx.report_error("Could not write file AST.tla");
        } else {
            ctx.report_info("Wrote file AST.tla.");
        }
    }
    let output = match res.output {
        Some(o) => o,
        None => return STATUS_EXIT_WITH_ERRORS,
    };
    if !ctx.no_old {
        let old = format!("{}.old", ctx.tla_input_file);
        if host.write_file(&old, bytes.as_deref().unwrap_or(&[])).is_err() {
            ctx.report_error(&format!("Could not rename input file {} to {}", tla, old));
            return STATUS_EXIT_WITH_ERRORS;
        }
    }
    if host.write_file(&tla, &join_lines(&output, eol)).is_err() {
        ctx.report_error(&format!("Could not write file {}", tla));
        return STATUS_EXIT_WITH_ERRORS;
    }
    ctx.report_info(&format!("New file {} written.", tla));
    if ctx.nocfg {
        return STATUS_EXIT_WITHOUT_ERROR;
    }
    let cfg_name = format!("{}.cfg", ctx.tla_input_file);
    let mut cfg: Vec<String> = if host.exists(&cfg_name) {
        match host.read_file(&cfg_name).ok().as_deref().and_then(read_all_lines) {
            Some(l) => l,
            None => {
                ctx.report_error(&format!("Error reading file {}.", cfg_name));
                return STATUS_EXIT_WITH_ERRORS;
            }
        }
    } else {
        vec![CFG_FILE_DELIMITER.to_string()]
    };
    match cfg.iter().position(|l| l.contains(CFG_FILE_DELIMITER)) {
        Some(j) => {
            cfg.drain(..j);
        }
        None => cfg.insert(0, CFG_FILE_DELIMITER.to_string()),
    }
    if ctx.tlc_translation() || ctx.has_default_initialization {
        cfg.insert(0, "CONSTANT defaultInitValue = defaultInitValue".to_string());
    }
    if ctx.check_termination {
        cfg.insert(0, "PROPERTY Termination".to_string());
    }
    let has_spec = cfg.iter().any(|l| match l.find("SPECIFICATION") {
        Some(i) => l.find("\\*").map(|c| c > i).unwrap_or(true),
        None => false,
    });
    if has_spec {
        ctx.report_info(&format!("File {}.cfg already contains SPECIFICATION statement,\n   so new one not written.", ctx.tla_input_file));
    } else {
        cfg.insert(0, "SPECIFICATION Spec".to_string());
    }
    if host.write_file(&cfg_name, &join_lines(&cfg, eol)).is_err() {
        ctx.report_error(&format!("Could not write file {}", cfg_name));
        return STATUS_EXIT_WITH_ERRORS;
    }
    ctx.report_info(&format!("New file {} written.", cfg_name));
    STATUS_EXIT_WITHOUT_ERROR
}
