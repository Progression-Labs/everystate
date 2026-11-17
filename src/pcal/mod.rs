//! A PlusCal translator: a port of the Java `pcal.trans` of the TLA+ tools (version 1.12), which
//! turns the PlusCal algorithm in a comment of a module into TLA+ between the
//! `\* BEGIN TRANSLATION` and `\* END TRANSLATION` lines.  The port follows the Java classes stage
//! by stage (tokenize, parse, rename, explode into labeled steps, generate TLA+) and keeps their
//! data model, so that the output, including its layout and the checksums, is the same.
pub mod ast;
pub mod expr;
pub mod explode;
pub mod gen;
pub mod parse;
pub mod symbols;
pub mod symtab;
pub mod tokenize;
pub mod trans;

use ast::{Ast, V};
use std::collections::HashSet;

pub const VERSION: &str = "1.12";
pub const MOD_DATE: &str = "01 July 2024";
const VERSION_WEIGHT: i32 = 1903;

/// How a stage fails.
pub enum PErr {
    /// A reported error (the Java `UnrecoverableException`s); the text is what follows
    /// "Unrecoverable error:\n -- ".
    Msg(String),
    /// A Java `RuntimeException` (null origin, index out of range): inside the parser it is
    /// reported as "Unknown error at or before ...".
    Runtime,
    /// `PcalDebug.ReportBug`
    Bug(String),
}
pub type PR<T> = Result<T, PErr>;

pub fn err<T>(msg: impl Into<String>) -> PR<T> {
    Err(PErr::Msg(msg.into()))
}
/// An error positioned at a node (`UnrecoverablePositionedException`).
pub fn err_at<T>(msg: impl Into<String>, n: &ast::Node) -> PR<T> {
    let msg = msg.into();
    if n.line.get() == 0 { Err(PErr::Msg(msg)) } else { Err(PErr::Msg(format!("{}\n    at {}", msg, n.location()))) }
}

/// `PcalParams.VersionToNumber`: "1.5" is 1500; -1 for a malformed version.
pub fn version_to_number(s: &str) -> i32 {
    let mut result: i64 = 0;
    let mut digits_after = 0;
    let mut after = false;
    for c in s.chars() {
        if c.is_ascii_digit() {
            result = 10 * result + (c as i64 - '0' as i64);
            if result > i32::MAX as i64 {
                return -1;
            }
            if after {
                digits_after += 1;
                if digits_after > 3 {
                    return -1;
                }
            }
        } else if c == '.' {
            after = true;
        } else {
            return -1;
        }
    }
    for _ in 0..(3 - digits_after) {
        result *= 10;
    }
    if result > i32::MAX as i64 { -1 } else { result as i32 }
}

/// Everything the Java translator keeps in static fields: the options (`PcalParams`), the
/// messages printed so far, and the state of `ParseAlgorithm`.
pub struct Ctx {
    // ---- PcalParams ----
    pub debug: bool,
    pub write_ast_flag: bool,
    pub spec_option: bool,
    pub myspec_option: bool,
    pub spec2_option: bool,
    pub myspec2_option: bool,
    pub spec_file: String,
    pub label_flag: bool,
    pub report_labels_flag: bool,
    pub label_root: String,
    pub fairness_option: String,
    pub fair_algorithm: bool,
    pub check_termination: bool,
    pub no_old: bool,
    pub nocfg: bool,
    pub no_done_disjunct: bool,
    pub options_in_file: bool,
    pub input_version_number: i32,
    pub wrap_column: i32,
    pub ss_wrap_column: i32,
    pub tla_input_file: String,
    pub unix_eol: bool,
    // ---- ToolIO.out ----
    pub out: Vec<String>,
    // ---- ParseAlgorithm ----
    pub(crate) reader: Option<tokenize::CharReader>,
    pub(crate) tokenizer: tokenize::Tokenizer,
    pub current_procedure: Option<String>,
    pub(crate) plus_labels: V<String>,
    pub(crate) minus_labels: V<String>,
    pub(crate) procedures_called: V<String>,
    pub goto_used: bool,
    pub goto_done_used: bool,
    pub omit_pc: bool,
    pub omit_stuttering_when_done: bool,
    pub has_default_initialization: bool,
    pub has_label: bool,
    pub(crate) all_labels: HashSet<String>,
    pub(crate) next_label_num: i32,
    pub(crate) added_labels: Vec<String>,
    pub(crate) added_labels_locs: Vec<String>,
    pub(crate) procedures: V<Ast>,
    pub p_syntax: bool,
    pub c_syntax: bool,
    pub(crate) in_get_macro: bool,
    pub(crate) lat: Vec<String>,
    pub(crate) cur_tok_col: [i32; 10],
    pub(crate) cur_tok_line: [i32; 10],
    pub(crate) last_tok_col: i32,
    pub(crate) last_tok_line: i32,
    pub(crate) last_tok_string: String,
}

impl Ctx {
    /// `PcalParams.resetParams()`
    pub fn new() -> Self {
        Ctx {
            debug: false,
            write_ast_flag: false,
            spec_option: false,
            myspec_option: false,
            spec2_option: false,
            myspec2_option: false,
            spec_file: String::new(),
            label_flag: false,
            report_labels_flag: false,
            label_root: "Lbl_".to_string(),
            fairness_option: String::new(),
            fair_algorithm: false,
            check_termination: false,
            no_old: false,
            nocfg: false,
            no_done_disjunct: false,
            options_in_file: false,
            input_version_number: VERSION_WEIGHT,
            wrap_column: 78,
            ss_wrap_column: 45,
            tla_input_file: String::new(),
            unix_eol: false,
            out: vec![],
            reader: None,
            tokenizer: tokenize::Tokenizer::new(),
            current_procedure: None,
            plus_labels: V::new(),
            minus_labels: V::new(),
            procedures_called: V::new(),
            goto_used: false,
            goto_done_used: false,
            omit_pc: true,
            omit_stuttering_when_done: true,
            has_default_initialization: false,
            has_label: false,
            all_labels: HashSet::new(),
            next_label_num: 1,
            added_labels: vec![],
            added_labels_locs: vec![],
            procedures: V::new(),
            p_syntax: false,
            c_syntax: false,
            in_get_macro: false,
            lat: vec![],
            cur_tok_col: [0; 10],
            cur_tok_line: [0; 10],
            last_tok_col: 0,
            last_tok_line: 0,
            last_tok_string: String::new(),
        }
    }
    pub fn tlc_translation(&self) -> bool {
        self.spec_option || self.myspec_option || self.spec2_option || self.myspec2_option
    }
    pub fn report_info(&mut self, s: &str) {
        self.out.push(s.to_string());
    }
    pub fn report_warning(&mut self, s: &str) {
        self.out.push(format!("Warning: {}", s));
    }
    pub fn report_error(&mut self, s: &str) {
        self.out.push(format!("\nUnrecoverable error:\n -- {}.\n", s));
    }
    /// Reports a failure the way the Java translator does for the corresponding throwable.
    pub fn report(&mut self, e: &PErr) {
        match e {
            PErr::Msg(m) => self.report_error(m),
            PErr::Runtime => self.out.push("Exception in thread \"main\" java.lang.RuntimeException".to_string()),
            PErr::Bug(m) => self.out.push(format!(
                "\nYou have discovered a bug in pcal.trans.\nSend the following information and the\ninput file to the current maintainer(s).\n\n -- {}.\n",
                m
            )),
        }
    }
    /// `PcalParams.ProcessVersion`
    pub fn process_version(&mut self, ver: &str) -> bool {
        let vnum = version_to_number(ver);
        if vnum < 0 {
            self.report_error(&format!("Illegal version {} specified.", ver));
            return false;
        }
        if vnum > VERSION_WEIGHT {
            self.report_error(&format!("Specified version {} later than current version {}", ver, VERSION));
            return false;
        }
        self.input_version_number = vnum;
        true
    }
}

impl Default for Ctx {
    fn default() -> Self {
        Self::new()
    }
}
