// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS4.1 (finding F-066, audit row `a.format.text_parser_utf8`,
// skeptic reproduction c09): the text parser is TOTAL over UTF-8 — it returns
// `Ok` or a `ParseError` and never panics on a multi-byte character.
//
// Before WS4.1 `Parser::advance(n)` sliced `input[pos..pos + n]` as BYTES
// while `skip_line` (every `;` comment, and — until WS4.2 made them refusals
// — unknown `; #directive`s, node comments and top-level lines) and
// `read_ident` stepped ONE BYTE per
// character, so `; é` alone made the parser panic (`byte index N is not a
// char boundary`, exit 101 from `trust-ir validate --format text`).
//
// This module is compiled into the `module_roundtrip_fuzz` test target so
// that standing gate 8 (`wire-format-goldens`) runs it; the `trust-ir`
// crate's own tests are run by no standing gate. The corpus-and-seed leg
// (`parse_never_panics`) lives in `module_roundtrip_fuzz.rs` itself and uses
// the helpers below.
//
//   * positive      — `; é`, `;é`, `ret %0 ; é` and a 4-byte character in a
//                     comment parse to the SAME module as the ASCII baseline;
//   * negative twin — a bare non-ASCII identifier (`fn @café(`) is a
//                     `ParseError` naming the line and column, never a panic
//                     (the BARE identifier alphabet is ASCII
//                     `[A-Za-z0-9_.$]`; WS4.3's printer spells such a
//                     symbol quoted, `fn @"café"(`);
//   * per-site      — the two further sites of the class the fix found by
//                     reading (`bytes:<len>:<hex>` dialect attrs and the
//                     `true` / `false` / `phantomdata` boundary peek), each
//                     with its ASCII control;
//   * ported ratchet — the proof program's exact specimen, now `Ok`.

use std::panic::{AssertUnwindSafe, catch_unwind};

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::parser::{ParseError, parse_function, parse_module};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Constant, Function, Module};

/// The substring of the fallible cursor's refusal. The correct parser can
/// never produce it (every single-character step goes through `bump`); a
/// scanner reverted to a byte step over a non-ASCII character produces it.
pub const CURSOR_SPLIT: &str = "internal: cursor split";

/// Parse with panics CAPTURED, so a regression is reported as "the parser
/// panicked" with the offending input rather than as a bare unwind.
///
/// The process-global panic hook is deliberately left alone: tests run on
/// parallel threads, and a `take_hook` / `set_hook` swap races.
pub fn parse_caught(text: &str) -> Result<Result<Module, ParseError>, String> {
    catch_unwind(AssertUnwindSafe(|| parse_module(text))).map_err(|payload| {
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "<non-string panic payload>".to_string())
    })
}

fn parse_ok(text: &str) -> Module {
    match parse_caught(text) {
        Ok(Ok(module)) => module,
        Ok(Err(err)) => panic!("expected Ok, got {err}\n--- input ---\n{text}"),
        Err(msg) => panic!("parser PANICKED (F-066): {msg}\n--- input ---\n{text}"),
    }
}

fn parse_err(text: &str) -> ParseError {
    match parse_caught(text) {
        Ok(Ok(module)) => panic!(
            "expected ParseError, got Ok (module {:?}, {} fns)\n--- input ---\n{text}",
            module.name,
            module.functions.len()
        ),
        Ok(Err(err)) => {
            assert!(
                !err.message.contains(CURSOR_SPLIT),
                "a scanner split a UTF-8 scalar: {err}\n--- input ---\n{text}"
            );
            err
        }
        Err(msg) => {
            panic!("parser PANICKED instead of returning Err: {msg}\n--- input ---\n{text}")
        }
    }
}

/// `fn @<name>() -> i32 { bb0: %0 = const i32 7; ret %0 }`.
fn named_module(fn_name: &str) -> Module {
    let mut module = Module::new("utf8");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), fn_name, ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn body_text(fn_name: &str) -> String {
    named_module(fn_name).to_string()
}

/// Append `suffix` to the first line containing `anchor`.
fn append_to_line(text: &str, anchor: &str, suffix: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let idx = lines
        .iter()
        .position(|l| l.contains(anchor))
        .unwrap_or_else(|| panic!("no line containing {anchor:?} in:\n{text}"));
    lines[idx].push_str(suffix);
    lines.join("\n") + "\n"
}

/// Insert `line` before the first line containing `anchor`.
fn insert_before(text: &str, anchor: &str, line: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let idx = lines
        .iter()
        .position(|l| l.contains(anchor))
        .unwrap_or_else(|| panic!("no line containing {anchor:?} in:\n{text}"));
    lines.insert(idx, line.to_string());
    lines.join("\n") + "\n"
}

/// The multi-byte characters under test: 2-, 3- and 4-byte encodings, and a
/// combining mark (a scalar that is not a grapheme of its own).
const MULTIBYTE: [(&str, char); 5] = [
    ("2-byte e-acute", '\u{e9}'),
    ("3-byte arrow", '\u{2192}'),
    ("3-byte em dash", '\u{2014}'),
    ("4-byte double-struck X", '\u{1d54f}'),
    ("combining acute U+0301", '\u{301}'),
];

// ---------------------------------------------------------------------------
// Positive: a multi-byte character in a comment changes nothing.
// ---------------------------------------------------------------------------

#[test]
fn utf8_in_comment_parses_to_the_ascii_baseline() {
    let text = body_text("seven");
    let baseline = parse_ok(&text);
    assert_eq!(baseline.to_string(), text, "Display -> parse -> Display");

    // The ASCII control: the same comment shapes, ASCII only.
    for ascii in [
        format!("; e\n{text}"),
        format!(";e\n{text}"),
        append_to_line(&text, "ret %0", " ; e"),
    ] {
        assert_eq!(parse_ok(&ascii), baseline, "ASCII comment:\n{ascii}");
    }

    for (label, ch) in MULTIBYTE {
        for twin in [
            // `; é` — a header comment.
            format!("; {ch}\n{text}"),
            // `;é` — no space after the `;`.
            format!(";{ch}\n{text}"),
            // `ret %0 ; é` — a trailing node comment (the plain-comment arm).
            append_to_line(&text, "ret %0", &format!(" ; {ch}")),
            // A plain comment between top-level items.
            format!("{text}; zzz {ch}\n"),
        ] {
            assert_eq!(parse_ok(&twin), baseline, "{label}:\n{twin}");
        }
        // Roadmap WS4.2: an unknown `; #directive` and an unknown top-level
        // line are REFUSED by name (they used to be skipped) — and still
        // never panic or split a scalar on the multi-byte payload.
        for (twin, needle) in [
            (
                insert_before(&text, "bb0", &format!("    ; #note: caf{ch}")),
                "unknown directive `#note` — refusing rather than dropping it",
            ),
            (
                format!("{text}zzz {ch}\n"),
                "unknown directive `zzz` — refusing rather than dropping it",
            ),
            (format!("{text}zzz {ch}"), "unknown directive `zzz`"),
            (
                format!("{text}zzz{ch}"),
                &format!("unknown directive `zzz{ch}`"),
            ),
        ] {
            let err = parse_err(&twin);
            assert!(err.message.contains(needle), "{label}: {err}\n{twin}");
        }
    }

    // A 4-byte character in a comment, stated on its own (the spec's
    // positive case), including emoji.
    for four in ['\u{1d54f}', '\u{1f600}'] {
        assert_eq!(four.len_utf8(), 4);
        assert_eq!(parse_ok(&format!("; {four}{four}\n{text}")), baseline);
    }
}

#[test]
fn ported_ratchet_a_format_text_parser_utf8() {
    // Proof-program row `a.format.text_parser_utf8` (specimen
    // parta/attrib/text_utf8_comment.trust_ir) asserted GAP: exit 101 with
    // "panicked at ... parser.rs". PASS: the identical bytes parse. Its
    // right-reason negative twin is
    // `non_ascii_identifier_is_a_located_parse_error`.
    let specimen = "; TrustIr text format v1\n\
                    ; a comment with one multi-byte character: \u{2014}\n\
                    module \"parta-utf8-comment\"\n";
    let parsed = parse_ok(specimen);
    assert_eq!(parsed.name, "parta-utf8-comment");
    assert!(parsed.functions.is_empty());

    // The skeptic's minimum input, `;é` with no newline: a comment then EOF
    // is a missing `module` line — a ParseError, never a panic.
    for (label, ch) in MULTIBYTE {
        let err = parse_err(&format!(";{ch}"));
        assert!(err.message.contains("expected 'module'"), "{label}: {err}");
    }
}

// ---------------------------------------------------------------------------
// Negative twin: a bare non-ASCII identifier is a located ParseError.
// ---------------------------------------------------------------------------

#[test]
fn non_ascii_identifier_is_a_located_parse_error() {
    let text = body_text("cafe");
    let fn_line = text
        .lines()
        .position(|l| l.starts_with("fn @"))
        .expect("fn line")
        + 1;
    // Control: the ASCII spelling parses.
    assert_eq!(parse_ok(&text).functions[0].name, "cafe");

    // Twin, one character changed: `fn @café(`. The identifier alphabet is
    // ASCII `[A-Za-z0-9_.$]`, so the run ends at `é` and the parser expects
    // `(`. The error names the line and the (character-counted) column of
    // the `é`: `fn @caf` is 7 characters wide, so column 8.
    let twin = text.replacen("fn @cafe(", "fn @caf\u{e9}(", 1);
    let err = parse_err(&twin);
    assert_eq!((err.line, err.col), (fn_line, 8), "{err}");
    assert!(
        err.message.contains("expected '('") && err.message.contains('\u{e9}'),
        "the error names what it saw: {err}"
    );
    let shown = err.to_string();
    assert!(
        shown.contains(&format!("parse error at {fn_line}:8")),
        "Display names line:col: {shown}"
    );

    // The single-function entry point takes the same path.
    let fn_text: String = twin
        .lines()
        .skip_while(|l| !l.starts_with("fn @"))
        .collect::<Vec<_>>()
        .join("\n");
    let err = catch_unwind(AssertUnwindSafe(|| parse_function(&fn_text)))
        .expect("parse_function must not panic")
        .expect_err("a non-ASCII symbol is refused by parse_function too");
    assert!(err.message.contains("expected '('"), "{err}");

    // WS4.3: every non-ASCII spelling a producer mints — Clean's `List.map\u{3b1}`,
    // Greek, CJK, a non-alphanumeric `\u{271d}`, a leading `\u{2192}` — now PRINTS
    // QUOTED and round-trips. Before WS4.3 each printed BARE and the whole
    // module was refused by the `#lossy` marker.
    //
    // The F-066 guard is kept, and is the reason the two forms must stay
    // disjoint: the BARE spelling of the very same name is still a LOCATED
    // parse error at the offending character, never a panic and never a
    // silently different name.
    for (name, col, what) in [
        ("List.map\u{3b1}", 13, "expected '('"),
        ("\u{3b1}", 5, "expected identifier"),
        ("\u{65e5}\u{672c}", 5, "expected identifier"),
        ("add\u{271d}", 8, "expected '('"),
        ("\u{2192}seven", 5, "expected identifier"),
    ] {
        let printed = body_text(name);
        let quoted = format!("fn @{name:?}(");
        assert!(
            printed.contains(&quoted),
            "WS4.3 must print the name quoted:\n{printed}"
        );
        assert!(
            !printed.contains("#lossy"),
            "{name:?} is no longer a text loss:\n{printed}"
        );
        assert_eq!(
            parse_ok(&printed).functions[0].name,
            name,
            "{name:?} must round-trip through the quoted spelling"
        );

        // F-066: the BARE spelling is still refused at the located character.
        let bare = printed.replacen(&quoted, &format!("fn @{name}("), 1);
        let err = parse_err(&bare);
        assert_eq!((err.line, err.col), (fn_line, col), "{name:?}: {err}");
        assert!(err.message.contains(what), "{name:?}: {err}");
    }

    // ASCII control: a character outside the alphabet was always refused.
    let err = parse_err(&text.replacen("fn @cafe(", "fn @ca<fe(", 1));
    assert!(err.message.contains("expected '('"), "{err}");
}

#[test]
fn bare_multibyte_character_in_a_token_position_is_a_parse_error() {
    for (label, ch) in MULTIBYTE {
        // Not a comment: a non-ASCII character where `module` must be.
        let err = parse_err(&format!("{ch}\nmodule \"m\"\n"));
        assert!(err.message.contains("expected 'module'"), "{label}: {err}");
        assert_eq!((err.line, err.col), (1, 1), "{label}: {err}");
        // A non-ASCII module NAME outside quotes.
        let err = parse_err(&format!("module caf{ch}\n"));
        assert!(err.message.contains("expected '\"'"), "{label}: {err}");
    }
}

#[test]
fn error_column_after_a_multibyte_comment_counts_characters() {
    // Location bookkeeping walks characters, so a multi-byte comment on the
    // line before does not skew the reported position of a later error.
    let err = parse_err("; caf\u{e9} \u{2014} \u{1f600}\nmodule m\n");
    assert_eq!((err.line, err.col), (2, 8), "{err}");
}

// ---------------------------------------------------------------------------
// Per-site: `bytes:<len>:<hex>` dialect attrs.
// ---------------------------------------------------------------------------

/// `named_module("dialect")` with a `dialect acme.op ... bytes:<len>:<hex>`.
fn dialect_bytes_module(payload: &[u8]) -> Module {
    use trust_ir::dialect::{AttrValue, DialectInst};
    let mut module = named_module("dialect");
    let op = DialectInst::new("acme", "op")
        .with_result_ty(Ty::I32)
        .with_attr("payload", AttrValue::Bytes(payload.to_vec()));
    let node = InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(ValueId::new(1));
    module.functions[0].blocks[0].body.insert(1, node);
    module
}

#[test]
fn dialect_bytes_attr_payload_is_read_digit_by_digit() {
    // Positive: the printer's own `bytes:<len>:<hex>` spelling.
    let text = dialect_bytes_module(&[0xDE, 0xAD]).to_string();
    assert!(text.contains("bytes:2:dead"), "printer spelling:\n{text}");
    assert_eq!(
        parse_ok(&text).to_string(),
        text,
        "Display -> parse -> Display"
    );

    // Twin: the parser used to slice `input[start..start + 2*len]` by BYTE
    // COUNT, so a multi-byte character inside the declared span put the bound
    // on a non-boundary and panicked. Now: a ParseError naming the character.
    for (label, ch) in MULTIBYTE {
        let twin = text.replacen("bytes:2:dead", &format!("bytes:2:de{ch}d"), 1);
        let err = parse_err(&twin);
        assert!(
            err.message.contains("expected hex digit") && err.message.contains(&format!("{ch:?}")),
            "{label}: {err}"
        );
    }

    // Controls: an ASCII non-hex digit is the same error; a sign inside a
    // digit pair is not a digit (the old `u8::from_str_radix` path read `+e`
    // as 0x0e — a second spelling of one byte); a short payload runs into
    // the next token; and a declared length near `u64::MAX` neither
    // overflows `len * 2` nor allocates.
    for (from, what) in [
        ("bytes:2:dexd", "expected hex digit"),
        ("bytes:2:de+e", "expected hex digit"),
        ("bytes:3:dead", "expected hex digit"),
        (
            "bytes:18446744073709551615:dead",
            "hex chars for bytes attr",
        ),
        ("bytes:4611686018427387904:dead", "hex chars for bytes attr"),
    ] {
        let err = parse_err(&text.replacen("bytes:2:dead", from, 1));
        assert!(err.message.contains(what), "{from}: {err}");
    }
}

// ---------------------------------------------------------------------------
// Per-site: the `true` / `false` / `phantomdata` keyword boundary.
// ---------------------------------------------------------------------------

#[test]
fn bool_keyword_boundary_sees_a_multibyte_character() {
    let base = body_text("seven").replacen("const i32 7", "const bool true", 1);
    let parsed = parse_ok(&base);
    assert!(matches!(
        parsed.functions[0].blocks[0].body[0].inst,
        Inst::Const {
            value: Constant::Bool(true),
            ..
        }
    ));
    let parsed = parse_ok(&base.replacen("const bool true", "const bool false", 1));
    assert!(matches!(
        parsed.functions[0].blocks[0].body[0].inst,
        Inst::Const {
            value: Constant::Bool(false),
            ..
        }
    ));

    // Control: `truex` is one token the constant grammar does not know,
    // refused AT THE CONSTANT.
    let ascii = parse_err(&base.replacen("const bool true", "const bool truex", 1));
    assert!(ascii.message.contains("expected number"), "{ascii}");

    // Twin: the boundary peek used a one-byte window (`get(4..5)`), which is
    // `None` inside a multi-byte character and so read as "keyword ends
    // here". `trueα` must be refused exactly like `truex`.
    for to in ["true\u{3b1}", "false\u{e9}", "phantomdata\u{3b1}"] {
        let twin = base.replacen("const bool true", &format!("const bool {to}"), 1);
        let err = parse_err(&twin);
        assert_eq!(
            (err.line, err.col, err.message.as_str()),
            (ascii.line, ascii.col, ascii.message.as_str()),
            "{to}: refused at the constant exactly like the ASCII twin: {err}"
        );
    }
}

// ---------------------------------------------------------------------------
// Review adversaries (WS4.1 review, 2026-10-01): inputs the increment's own
// tests did not write.
// ---------------------------------------------------------------------------

/// Unicode whitespace that is NOT ASCII whitespace. `char::is_whitespace`
/// (and `str::trim`) treat the first four as whitespace; the last two are
/// invisible format characters an editor or a copy-paste can introduce.
const UNICODE_SPACES: [(&str, char); 6] = [
    ("NBSP U+00A0", '\u{a0}'),
    ("NEL U+0085", '\u{85}'),
    ("LINE SEPARATOR U+2028", '\u{2028}'),
    ("IDEOGRAPHIC SPACE U+3000", '\u{3000}'),
    ("BOM U+FEFF", '\u{feff}'),
    ("ZWSP U+200B", '\u{200b}'),
];

/// The token separator is ASCII whitespace ONLY. A Unicode space that
/// replaces any separating ASCII space (outside quoted strings and comments)
/// is a located `ParseError` on that line — never a second spelling of the
/// same module (one spelling per construct), never a panic, never a cursor
/// split. Several parser lookaheads use the Unicode `is_whitespace` /
/// `trim_start` while the consuming scanners use the ASCII test, so a
/// lookahead could in principle route such a space to a branch that
/// accepts it; this pins that none does.
#[test]
fn unicode_whitespace_is_not_a_token_separator() {
    let text = body_text("cafe");
    let baseline = parse_ok(&text);
    let mut refused = 0usize;
    for (label, ws) in UNICODE_SPACES {
        for (i, _) in text.match_indices(' ') {
            let line_start = text[..i].rfind('\n').map_or(0, |j| j + 1);
            let in_quotes = text[line_start..i].matches('"').count() % 2 == 1;
            let in_comment = text[line_start..i].contains(';');
            if in_quotes || in_comment {
                continue;
            }
            let mutated = format!("{}{ws}{}", &text[..i], &text[i + 1..]);
            let err = parse_err(&mutated);
            let line = text[..i].matches('\n').count() + 1;
            assert_eq!(
                err.line, line,
                "{label} replacing the space at byte {i} was refused on the wrong line: {err}\n\
                 --- input ---\n{mutated}"
            );
            refused += 1;
        }
        // Before `module`: a leading BOM / NBSP is not skipped as whitespace.
        let err = parse_err(&format!("{ws}{text}"));
        assert_eq!((err.line, err.col), (1, 1), "{label} leading: {err}");
        // Inside a comment it is content, and the module is unchanged.
        assert_eq!(
            parse_ok(&format!(";{ws}x{ws}\n{text}")),
            baseline,
            "{label} in a comment"
        );
    }
    assert!(
        refused >= 6 * 4,
        "too few separator positions exercised ({refused}) in:\n{text}"
    );
}

/// `\u{..}` escapes inside a quoted string: every malformed shape is a
/// located `ParseError` on the string's line, never a panic — a surrogate,
/// a scalar past U+10FFFF, a hex run that overflows `u32`, an empty escape,
/// a missing `}`, a multi-byte character where a hex digit or `}` must be,
/// and an escape cut off at end of input.
#[test]
fn malformed_unicode_escapes_in_quoted_strings_are_located_errors() {
    for (what, body) in [
        ("surrogate", r"m\u{D800}"),
        ("past U+10FFFF", r"m\u{110000}"),
        ("u32 overflow", r"m\u{FFFFFFFFFFFFFFFF}"),
        ("empty escape", r"m\u{}"),
        ("missing close brace", r"m\u{e9"),
        ("multi-byte char for a hex digit", "m\\u{\u{e9}}"),
        ("multi-byte char for the open brace", "m\\u\u{1f600}"),
    ] {
        let text = format!("; header \u{2014}\nmodule \"{body}\"\n");
        let err = parse_err(&text);
        assert_eq!(err.line, 2, "{what}: {err}");
    }
    // Cut off: a backslash, or a backslash and a multi-byte char, at EOF.
    for tail in ["\\", "\\\u{1f600}", "\\u{1f6"] {
        let err = parse_err(&format!("module \"m{tail}"));
        assert_eq!(err.line, 1, "cut-off escape {tail:?}: {err}");
    }
}

/// The reported column counts CHARACTERS on the SAME line as an earlier
/// multi-byte character (the existing column test puts the multi-byte
/// comment on the line BEFORE the error, where a byte-counting column would
/// have been reset by the newline anyway).
#[test]
fn error_column_counts_characters_after_a_multibyte_symbol_on_the_same_line() {
    let text = body_text("cafe");
    let header = text
        .lines()
        .find(|l| l.starts_with("fn @cafe("))
        .expect("fn header")
        .to_string();
    let quoted = header.replacen("fn @cafe(", "fn @\"caf\u{e9}\u{1f600}\"(", 1);
    // Control: the quoted non-ASCII symbol alone parses.
    let control = text.replacen(&header, &quoted, 1);
    assert_eq!(parse_ok(&control).functions[0].name, "caf\u{e9}\u{1f600}");
    // Twin: a stray `~` right after the parameter list opens, on the same
    // line as (and after) the 2- and 4-byte characters of the symbol.
    let open = "fn @\"caf\u{e9}\u{1f600}\"(".len();
    let broken = format!("{}~{}", &quoted[..open], &quoted[open..]);
    let err = parse_err(&text.replacen(&header, &broken, 1));
    let line = text.lines().position(|l| l == header).expect("line") + 1;
    let col = quoted[..open].chars().count() + 1;
    assert_eq!(
        (err.line, err.col),
        (line, col),
        "{err}\n--- header ---\n{broken}"
    );
}
