//! Parser: a minimal indentation-based Python-like surface syntax → [`Ast`].

use super::*;
use std::collections::BTreeMap;

/// Parse Python-like source into an [`Ast`]. Supports `def`, immutable
/// assignment (`x = …`, `a, b = f(…)`), `assert a == b`, `for i in
/// mul_range(GEN**lo, GEN**hi):`, `return`, calls, and `+`/`*` arithmetic over
/// integer literals and variables. Top level also accepts **global constant**
/// declarations `NAME = <const-expr>` (see [`parse_with_replacements`]).
///
/// A DSL source is a valid Python file: `import snark_lib` / `from snark_lib
/// import *` pulls the stub definitions (`snark_lib.py` at the repo root) that
/// make editors and linters happy, and is skipped here. Importing anything
/// else is an error — the compiler does not include other source files.
pub fn parse(src: &str) -> Result<Ast, String> {
    parse_with_replacements(src, &BTreeMap::new())
}

/// Like [`parse`], but first applies compile-time **placeholder** replacements
/// (identifier-level text substitution — see [`apply_replacements`]). This is
/// how a host injects sizes/flags into a program without editing it: write a
/// placeholder identifier in source and map it to a value at compile time. The
/// idiom is a placeholder feeding a named constant:
///
/// ```text
/// V = V_PLACEHOLDER          # with replacement  "V_PLACEHOLDER" ↦ "128"
/// def main():
///     buf = StackBuf(V)      # V is now the constant 128 everywhere
/// ```
///
/// **Global constants.** Between the (optional) `snark_lib` import and the
/// `def`s, the top level accepts constant declarations `NAME = <int-expr>`,
/// where `<int-expr>` is a compile-time **integer** — decimal literals combined
/// with `+ - * / **` and parentheses (ordinary integer arithmetic, *not* the
/// runtime field's XOR/GHASH), and references to *earlier* constants. So a
/// derived size like `N_TWEAKS = 2 + (W - 1) * V + LOG_LIFETIME` comes out
/// right. Each constant is evaluated and substituted, as a single decimal
/// literal, everywhere its name appears in the functions below — so a constant
/// is usable anywhere a literal is: arithmetic operand, `StackBuf` / `HeapBuf`
/// size, stack index, slice bound, `**` exponent, loop bound, range-check
/// bound, `Const` argument. Constants are resolved before variables, so a
/// constant name is **reserved**: do not reuse it as a parameter or local name.
pub fn parse_with_replacements(src: &str, replacements: &BTreeMap<String, String>) -> Result<Ast, String> {
    let src = apply_replacements(src, replacements);
    // (indent, content) for each significant line.
    let mut lines: Vec<(usize, String)> = Vec::new();
    for raw in src.lines() {
        let no_comment = raw.split('#').next().unwrap();
        if no_comment.trim().is_empty() {
            continue;
        }
        let t = no_comment.trim();
        if let Some(rest) = t.strip_prefix("import ").or_else(|| t.strip_prefix("from ")) {
            let module = rest.split_whitespace().next().unwrap_or("");
            if module != "snark_lib" {
                return Err(format!(
                    "file imports are not supported (only the `snark_lib` stub): `{t}`"
                ));
            }
            continue; // the stub is for Python tooling; the compiler skips it
        }
        let indent = no_comment.len() - no_comment.trim_start().len();
        lines.push((indent, no_comment.trim().to_string()));
    }
    // Peel off the leading top-level constant declarations (before any `def`),
    // each evaluated to a field value and rendered as a single decimal literal.
    // Building a `name → literal` map lets later constants and the functions
    // reference them by plain text substitution — so a constant works even in
    // positions that demand a parse-time literal (`StackBuf`, `**`, `assert log
    // _ < _`).
    let mut consts: BTreeMap<String, String> = BTreeMap::new();
    let mut const_arrays: Vec<(String, Vec<u128>)> = Vec::new();
    let mut start = 0;
    while start < lines.len() {
        let (indent, line) = &lines[start];
        if *indent == 0 && (line.starts_with("def ") || line.starts_with('@')) {
            break;
        }
        if *indent != 0 {
            return Err(format!("unexpected indentation at top level: `{line}`"));
        }
        let (lhs, rhs) = split_assign(line).ok_or_else(|| {
            format!("top level: expected `def`, a global constant `NAME = value`, or the `snark_lib` import, got `{line}`")
        })?;
        let name = lhs.trim().to_string();
        if !is_ident(&name) {
            return Err(format!("global constant name must be a plain identifier: `{}`", lhs.trim()));
        }
        if consts.contains_key(&name) || const_arrays.iter().any(|(n, _)| n == &name) {
            return Err(format!("global constant `{name}` is declared twice"));
        }
        // Resolve earlier scalar constants inside the value first.
        let rhs = apply_replacements(rhs.trim(), &consts);
        let rhs = rhs.trim();
        if let Some(inner) = rhs.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            // A constant array `NAME = [a, b, c]`: each element a compile-time
            // integer / field value. Not textually substituted — carried to
            // lowering, indexed/measured there.
            let mut elems = Vec::new();
            for part in split_top(inner, ',') {
                let p = part.trim();
                if p.is_empty() {
                    continue; // tolerate a trailing comma
                }
                elems.push(eval_const_int(p).map_err(|e| format!("global constant array `{name}`: {e}"))?);
            }
            const_arrays.push((name, elems));
        } else {
            // A scalar constant: evaluate it as a compile-time integer.
            let value = eval_const_int(rhs).map_err(|e| format!("global constant `{name}`: {e}"))?;
            consts.insert(name, value.to_string());
        }
        start += 1;
    }
    // Substitute the constants into every remaining (function) line, then parse.
    let func_lines: Vec<(usize, String)> = lines[start..]
        .iter()
        .map(|(ind, l)| (*ind, apply_replacements(l, &consts)))
        .collect();
    let mut p = Parser { lines: func_lines, i: 0 };
    let mut funcs = Vec::new();
    while p.i < p.lines.len() {
        funcs.push(p.func()?);
    }
    Ok(Ast { funcs, const_arrays })
}

/// Apply identifier-level **placeholder** replacements to source text before
/// parsing: each maximal run of identifier characters (`[A-Za-z0-9_]`) that
/// equals a key of `replacements` is replaced by its value; other text —
/// including substrings of longer identifiers — is untouched. Mirrors leanVM's
/// `CompilationFlags::replacements`. An empty map returns the source unchanged.
pub fn apply_replacements(src: &str, replacements: &BTreeMap<String, String>) -> String {
    if replacements.is_empty() {
        return src.to_string();
    }
    let is_ident_char = |c: char| c.is_alphanumeric() || c == '_';
    let mut out = String::with_capacity(src.len());
    let mut word = String::new(); // current run of identifier characters
    let flush = |out: &mut String, word: &mut String| {
        match replacements.get(word.as_str()) {
            Some(v) => out.push_str(v),
            None => out.push_str(word),
        }
        word.clear();
    };
    for c in src.chars() {
        if is_ident_char(c) {
            word.push(c);
        } else {
            flush(&mut out, &mut word);
            out.push(c);
        }
    }
    flush(&mut out, &mut word);
    out
}

/// A plain identifier: non-empty, starts with a letter or `_`, all
/// `[A-Za-z0-9_]` (no operators, brackets, or commas).
fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    matches!(cs.next(), Some(c) if c.is_alphabetic() || c == '_') && s.chars().all(|c| c.is_alphanumeric() || c == '_')
}

/// Evaluate a compile-time **integer** constant expression: decimal literals
/// combined with `+`, `-`, `*`, `/` (truncating), `**` (power), and
/// parentheses. This is ordinary integer arithmetic — a global constant is a
/// count / size / exponent — deliberately *distinct* from the runtime field's
/// `+` = XOR and `*` = GHASH, so derived sizes like `2 + (W - 1) * V +
/// LOG_LIFETIME` come out right. All references to earlier constants have
/// already been substituted to their decimal values, so the input is pure
/// arithmetic. Overflow, division by zero, and a negative intermediate are
/// errors.
fn eval_const_int(s: &str) -> Result<u128, String> {
    #[derive(Clone, Copy, PartialEq)]
    enum Tok {
        Num(u128),
        Add,
        Sub,
        Mul,
        Div,
        Pow,
        LParen,
        RParen,
    }
    let bytes = s.as_bytes();
    let mut toks = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b' ' | b'\t' => i += 1,
            b'+' => {
                toks.push(Tok::Add);
                i += 1;
            }
            b'-' => {
                toks.push(Tok::Sub);
                i += 1;
            }
            b'/' => {
                toks.push(Tok::Div);
                i += 1;
            }
            b'(' => {
                toks.push(Tok::LParen);
                i += 1;
            }
            b')' => {
                toks.push(Tok::RParen);
                i += 1;
            }
            b'*' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'*' {
                    toks.push(Tok::Pow);
                    i += 2;
                } else {
                    toks.push(Tok::Mul);
                    i += 1;
                }
            }
            c if c.is_ascii_digit() => {
                let start = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                let n = s[start..i]
                    .parse::<u128>()
                    .map_err(|_| format!("integer literal out of range: `{}`", &s[start..i]))?;
                toks.push(Tok::Num(n));
            }
            c => {
                return Err(format!(
                    "unexpected `{}` in integer constant expression `{}`",
                    c as char,
                    s.trim()
                ));
            }
        }
    }
    if toks.is_empty() {
        return Err("empty constant expression".into());
    }
    // Recursive descent: expr → term (('+'|'-') term)*, term → power
    // (('*'|'/') power)*, power → atom ('**' power)?, atom → num | '(' expr ')'.
    fn atom(t: &[Tok], p: &mut usize) -> Result<u128, String> {
        match t.get(*p) {
            Some(Tok::Num(n)) => {
                *p += 1;
                Ok(*n)
            }
            Some(Tok::LParen) => {
                *p += 1;
                let v = expr(t, p)?;
                if t.get(*p) != Some(&Tok::RParen) {
                    return Err("expected `)` in constant expression".into());
                }
                *p += 1;
                Ok(v)
            }
            _ => Err("expected a number or `(` in constant expression".into()),
        }
    }
    fn power(t: &[Tok], p: &mut usize) -> Result<u128, String> {
        let base = atom(t, p)?;
        if t.get(*p) == Some(&Tok::Pow) {
            *p += 1;
            let exp = power(t, p)?; // right-associative
            let exp = u32::try_from(exp).map_err(|_| "`**` exponent too large".to_string())?;
            base.checked_pow(exp).ok_or_else(|| "constant overflow in `**`".to_string())
        } else {
            Ok(base)
        }
    }
    fn term(t: &[Tok], p: &mut usize) -> Result<u128, String> {
        let mut acc = power(t, p)?;
        while let Some(op @ (Tok::Mul | Tok::Div)) = t.get(*p).copied() {
            *p += 1;
            let rhs = power(t, p)?;
            acc = if op == Tok::Mul {
                acc.checked_mul(rhs).ok_or_else(|| "constant overflow in `*`".to_string())?
            } else {
                acc.checked_div(rhs)
                    .ok_or_else(|| "division by zero in constant expression".to_string())?
            };
        }
        Ok(acc)
    }
    fn expr(t: &[Tok], p: &mut usize) -> Result<u128, String> {
        let mut acc = term(t, p)?;
        while let Some(op @ (Tok::Add | Tok::Sub)) = t.get(*p).copied() {
            *p += 1;
            let rhs = term(t, p)?;
            acc = if op == Tok::Add {
                acc.checked_add(rhs).ok_or_else(|| "constant overflow in `+`".to_string())?
            } else {
                acc.checked_sub(rhs).ok_or_else(|| "constant is negative (underflow in `-`)".to_string())?
            };
        }
        Ok(acc)
    }
    let mut pos = 0;
    let value = expr(&toks, &mut pos)?;
    if pos != toks.len() {
        return Err(format!("unexpected trailing tokens in constant expression `{}`", s.trim()));
    }
    Ok(value)
}

/// Evaluate a compile-time constant expression — integer literals, `GEN`,
/// `GEN ** k`, and `+`/`*` combinations of those — to its field element.
/// Used for the `# public_input: <elt>, <elt>` annotation of `.py` test
/// programs (see `tests/py_source.rs`).
pub fn parse_const(s: &str) -> Result<F128, String> {
    fn eval(e: &Expr) -> Result<F128, String> {
        match e {
            Expr::Lit(n) => Ok(F128::new(*n as u64, (*n >> 64) as u64)),
            Expr::Gen => Ok(g_pow(1)),
            Expr::GPow(k) => Ok(g_pow_u128(*k)),
            Expr::Add(a, b) => Ok(eval(a)? + eval(b)?),
            Expr::Mul(a, b) => Ok(eval(a)? * eval(b)?),
            other => Err(format!("not a constant expression: `{other:?}`")),
        }
    }
    eval(&parse_expr(s)?)
}

/// Parse a zkDSL source file (a `.py` file — the DSL is Python-shaped, see
/// [`parse`]) with compile-time **placeholder** replacements (see
/// [`parse_with_replacements`]).
pub fn parse_file_with_replacements(
    path: impl AsRef<std::path::Path>,
    replacements: &BTreeMap<String, String>,
) -> Result<Ast, String> {
    let path = path.as_ref();
    let src = std::fs::read_to_string(path).map_err(|e| format!("cannot read `{}`: {e}", path.display()))?;
    parse_with_replacements(&src, replacements)
}

struct Parser {
    lines: Vec<(usize, String)>,
    i: usize,
}

impl Parser {
    fn func(&mut self) -> Result<Func, String> {
        let (mut indent, mut line) = self.lines[self.i].clone();
        // Optional `@inline` decorator on its own line before `def`.
        let inline = if let Some(dec) = line.strip_prefix('@') {
            if dec.trim() != "inline" {
                return Err(format!("unknown decorator `@{}` (only `@inline`)", dec.trim()));
            }
            self.i += 1;
            (indent, line) = self.lines.get(self.i).cloned().ok_or("`@inline` must precede a `def`")?;
            true
        } else {
            false
        };
        let header = line
            .strip_prefix("def ")
            .ok_or_else(|| format!("expected `def`, got `{line}`"))?;
        let header = header.strip_suffix(':').ok_or("function header needs `:`")?;
        let open = header.find('(').ok_or("function header needs `(`")?;
        let name = header[..open].trim().to_string();
        let params_str = header[open + 1..header.rfind(')').ok_or("missing `)`")?].trim();
        let (mut params, mut const_params) = (Vec::new(), Vec::new());
        if !params_str.is_empty() {
            for part in params_str.split(',') {
                // `x` (runtime) or `x: Const` (compile-time, specialized).
                if let Some((n, ann)) = part.split_once(':') {
                    if ann.trim() != "Const" {
                        return Err(format!(
                            "unsupported parameter annotation `{}` (only `Const`)",
                            ann.trim()
                        ));
                    }
                    params.push(n.trim().to_string());
                    const_params.push(true);
                } else {
                    params.push(part.trim().to_string());
                    const_params.push(false);
                }
            }
        }
        self.i += 1;
        let body = self.block(indent)?;
        let n_ret = body
            .iter()
            .filter_map(|s| if let Stmt::Return(es) = s { Some(es.len()) } else { None })
            .max()
            .unwrap_or(0);
        Ok(Func {
            name,
            params,
            const_params,
            n_ret,
            body,
            inline,
        })
    }

    /// Parse a block: all statements indented strictly more than `parent`.
    fn block(&mut self, parent: usize) -> Result<Vec<Stmt>, String> {
        let mut stmts = Vec::new();
        let block_indent = match self.lines.get(self.i) {
            Some((ind, _)) if *ind > parent => *ind,
            _ => return Err("expected an indented block".into()),
        };
        while let Some((ind, _)) = self.lines.get(self.i) {
            if *ind != block_indent {
                if *ind > parent && *ind > block_indent {
                    return Err("inconsistent indentation".into());
                }
                break;
            }
            stmts.push(self.stmt(block_indent)?);
        }
        Ok(stmts)
    }

    fn stmt(&mut self, indent: usize) -> Result<Stmt, String> {
        let line = self.lines[self.i].1.clone();
        if let Some(rest) = line.strip_prefix("for ") {
            // for VAR in mul_range(START, STOP): the counter walks gᵏ from START
            // to STOP, ×g each iteration (STOP is exclusive). Bounds are field
            // elements (powers of GEN), so the multiplicative walk is explicit.
            let rest = rest.strip_suffix(':').ok_or("`for` needs `:`")?;
            let (var, iter) = rest.split_once(" in ").ok_or("`for` needs `in`")?;
            // `for i in unroll(a, b):` — compile-time replication; the bounds
            // are integer expressions, evaluated at lowering (so a `Const`
            // parameter works as a bound).
            if let Some(inner) = iter.trim().strip_prefix("unroll(").and_then(|s| s.strip_suffix(')')) {
                let parts = split_top(inner, ',');
                if parts.len() != 2 {
                    return Err("unroll needs `a, b` (compile-time integers)".into());
                }
                let (lo, hi) = (parse_expr(&parts[0])?, parse_expr(&parts[1])?);
                self.i += 1;
                let body = self.block(indent)?;
                return Ok(Stmt::Unroll {
                    var: var.trim().to_string(),
                    lo,
                    hi,
                    body,
                });
            }
            let inner = iter
                .trim()
                .strip_prefix("mul_range(")
                .and_then(|s| s.strip_suffix(')'))
                .ok_or("`for` needs `mul_range(start, stop)` or `unroll(a, b)`")?;
            let parts = split_top(inner, ',');
            if parts.len() != 2 {
                return Err("mul_range needs `start, stop`".into());
            }
            let lo = parse_gpow_bound(&parts[0])?;
            // The stop bound: a compile-time power of GEN, or any expression —
            // a runtime g-power element the walk must be able to reach.
            let hi = match parse_gpow_bound(&parts[1]) {
                Ok(hi) => {
                    if lo > hi {
                        return Err(format!("mul_range: start GEN**{lo} must not exceed stop GEN**{hi}"));
                    }
                    ForBound::Const(hi)
                }
                Err(_) => ForBound::Runtime(parse_expr(&parts[1])?),
            };
            self.i += 1;
            let body = self.block(indent)?;
            return Ok(Stmt::For {
                var: var.trim().to_string(),
                lo,
                hi,
                body,
            });
        }
        if let Some(rest) = line.strip_prefix("if ") {
            let rest = rest.to_string();
            return self.if_stmt(&rest, indent);
        }
        if let Some(rest) = line.strip_prefix("match ") {
            let rest = rest.to_string();
            return self.match_stmt(&rest, indent);
        }
        self.i += 1;
        if line == "return" {
            return Ok(Stmt::Return(vec![]));
        }
        if let Some(rest) = line.strip_prefix("return ") {
            return Ok(Stmt::Return(
                split_top(rest, ',')
                    .iter()
                    .map(|e| parse_expr(e))
                    .collect::<Result<_, _>>()?,
            ));
        }
        // `hint_witness(dest, "name")` — the string literal is not an
        // expression; parsed here.
        if let Some(inner) = line.strip_prefix("hint_witness(").and_then(|s| s.strip_suffix(')')) {
            let parts = split_top(inner, ',');
            let [dest, name] = parts.as_slice() else {
                return Err("hint_witness(dest, \"name\") takes two arguments".into());
            };
            let name = name
                .trim()
                .strip_prefix('"')
                .and_then(|s| s.strip_suffix('"'))
                .ok_or("hint_witness's second argument is a string literal: \"name\"")?;
            return Ok(Stmt::HintWitness {
                dest: parse_expr(dest)?,
                name: name.to_string(),
            });
        }
        if let Some(rest) = line.strip_prefix("assert ") {
            if let Some((a, b)) = split_once_top(rest, "==") {
                return Ok(Stmt::AssertEq(parse_expr(&a)?, parse_expr(&b)?));
            }
            if let Some((a, b)) = split_once_top(rest, "!=") {
                return Ok(Stmt::AssertNe(parse_expr(&a)?, parse_expr(&b)?));
            }
            // `assert log X < log Y` (`Y` a compile-time g-power) or
            // `assert log X < k` (`k` an integer exponent) — a range check in
            // the exponent: proves `log_g(X) < k`.
            if let Some((a, b)) = split_once_top(rest, "<") {
                let x =
                    strip_log(&a).ok_or("a `<` assert compares logs: `assert log X < log Y` or `assert log X < k`")?;
                let bound = match strip_log(&b) {
                    Some(y) => gpow_bound(&parse_expr(y)?)?, // log GEN ** k = k
                    // An integer bound folds like any parse-time size (`CAP + 1`).
                    None => match const_int_expr(&parse_expr(&b)?) {
                        Some(k) => u64::try_from(k).map_err(|_| format!("log bound {k} does not fit in u64"))?,
                        None => {
                            return Err(format!(
                                "a log bound must be `log GEN ** k` or a parse-time integer, got `{b}`"
                            ));
                        }
                    },
                };
                return Ok(Stmt::AssertLt(parse_expr(x)?, bound));
            }
            return Err("`assert` needs `==`, `!=`, or `log _ < _`".into());
        }
        // Augmented assignment `x OP= rhs` (Python `*=`, `+=`, `//=`, `%=`,
        // `-=`) desugars to `x = x OP (rhs)`.
        let line = match split_aug(&line) {
            Some((lhs, op, rhs)) => format!("{lhs} = {lhs} {op} ({rhs})"),
            None => line,
        };
        // Assignment or bare call.
        if let Some((lhs, rhs)) = split_assign(&line) {
            // `names = match_range(…)` carries lambdas, which `parse_expr`
            // does not speak — expanded by its own parser.
            if rhs.trim_start().starts_with("match_range(") {
                return parse_match_range(&lhs, &rhs);
            }
            let rhs_expr = parse_expr(&rhs)?;
            // Indexed LHS `arr[idx] = value` is a heap store.
            if lhs.trim_end().ends_with(']') {
                let lhs = lhs.trim();
                let open = lhs.find('[').ok_or("malformed store target")?;
                let arr = parse_expr(&lhs[..open])?;
                let idx = parse_expr(&lhs[open + 1..lhs.len() - 1])?;
                return Ok(Stmt::Store(arr, idx, rhs_expr));
            }
            let targets = split_top(&lhs, ',');
            if targets.len() == 1 {
                return Ok(Stmt::Let(targets[0].trim().to_string(), rhs_expr));
            }
            // Tuple assignment: RHS must be a call.
            if let Expr::Call(f, args) = rhs_expr {
                let names = targets.iter().map(|t| t.trim().to_string()).collect();
                return Ok(Stmt::LetTuple(names, f, args));
            }
            return Err("tuple assignment requires a call on the right".into());
        }
        // Bare call statement.
        if let Expr::Call(f, args) = parse_expr(&line)? {
            return Ok(Stmt::Call(f, args));
        }
        Err(format!("statement has no effect: `{line}`"))
    }

    /// `if a == b:` / `if a != b:` (the current line, its `if `/`elif `
    /// prefix already stripped into `header`), with an optional `elif`/`else`
    /// tail at the same indent — an `elif` is sugar for an `else` holding a
    /// nested `if`.
    fn if_stmt(&mut self, header: &str, indent: usize) -> Result<Stmt, String> {
        let cond = header.strip_suffix(':').ok_or("`if` needs `:`")?;
        let (eq, l, r) = if let Some((l, r)) = split_once_top(cond, "==") {
            (true, l, r)
        } else if let Some((l, r)) = split_once_top(cond, "!=") {
            (false, l, r)
        } else {
            return Err("an `if` condition must be `a == b` or `a != b`".into());
        };
        let (lhs, rhs) = (parse_expr(&l)?, parse_expr(&r)?);
        self.i += 1;
        let then = self.block(indent)?;
        let mut els = Vec::new();
        if let Some((ind, line)) = self.lines.get(self.i).cloned()
            && ind == indent
        {
            if line == "else:" {
                self.i += 1;
                els = self.block(indent)?;
            } else if let Some(rest) = line.strip_prefix("elif ") {
                let rest = rest.to_string();
                els = vec![self.if_stmt(&rest, indent)?];
            }
        }
        Ok(Stmt::If {
            eq,
            lhs,
            rhs,
            then,
            els,
        })
    }

    /// `match log(x):` with `case 0:` … `case n-1:` bodies — the cases must
    /// be consecutive integers from 0 (the trampoline table is dense; there
    /// is no `case _`). Matching is on the *log*: `x = GEN ** j` runs case `j`.
    fn match_stmt(&mut self, header: &str, indent: usize) -> Result<Stmt, String> {
        let inner = header.strip_suffix(':').ok_or("`match` needs `:`")?;
        let x = strip_log(inner).ok_or("`match` matches logs: `match log(x):`")?;
        let x = parse_expr(x)?;
        self.i += 1;
        let case_indent = match self.lines.get(self.i) {
            Some((ind, _)) if *ind > indent => *ind,
            _ => return Err("`match` needs an indented `case` block".into()),
        };
        let mut cases = Vec::new();
        while let Some((ind, line)) = self.lines.get(self.i).cloned() {
            if ind != case_indent {
                break;
            }
            let rest = line
                .strip_prefix("case ")
                .ok_or_else(|| format!("expected `case k:`, got `{line}`"))?;
            let k: usize = rest
                .strip_suffix(':')
                .ok_or("`case` needs `:`")?
                .trim()
                .parse()
                .map_err(|_| format!("a `case` value must be an integer literal, got `{rest}`"))?;
            if k != cases.len() {
                return Err(format!(
                    "match cases must be consecutive from 0: expected `case {}:`, got `case {k}:`",
                    cases.len()
                ));
            }
            self.i += 1;
            cases.push(self.block(case_indent)?);
        }
        if cases.is_empty() {
            return Err("`match` needs at least one case".into());
        }
        Ok(Stmt::Match { x, cases })
    }
}

/// Split on a top-level (paren-depth-0) single `=` that is not `==`.
/// A top-level augmented assignment `lhs OP= rhs` -> `(lhs, "OP", rhs)`, for
/// OP in `+ - * // %`. Returns `None` for a plain `=`, a comparison (`==`,
/// `!=`, `<=`, `>=`), or `**=` (unused). The operator's `=` must sit at depth
/// 0 and be immediately preceded by exactly the operator characters.
fn split_aug(s: &str) -> Option<(String, &'static str, String)> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    for i in 0..b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'=' if depth == 0 => {
                // not `==` and not a comparison tail (`<=`, `>=`, `!=`)
                if b.get(i + 1) == Some(&b'=') || matches!(b.get(i.wrapping_sub(1)), Some(b'=' | b'<' | b'>' | b'!')) {
                    return None;
                }
                let (op, plen): (&str, usize) = match b[i - 1] {
                    b'+' => ("+", 1),
                    b'-' => ("-", 1),
                    b'%' => ("%", 1),
                    b'*' if b[i - 2] != b'*' => ("*", 1),
                    b'/' if b[i - 2] == b'/' => ("//", 2),
                    _ => return None,
                };
                return Some((s[..i - plen].trim().to_string(), op, s[i + 1..].trim().to_string()));
            }
            _ => {}
        }
    }
    None
}

fn split_assign(s: &str) -> Option<(String, String)> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'=' if depth == 0 => {
                let next_eq = i + 1 < b.len() && b[i + 1] == b'=';
                let prev_eq = i > 0 && b[i - 1] == b'=';
                if !next_eq && !prev_eq {
                    return Some((s[..i].to_string(), s[i + 1..].to_string()));
                }
                if next_eq {
                    i += 1; // skip `==`
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Split `s` on every top-level occurrence of `sep` (a single char).
fn split_top(s: &str, sep: char) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ if c == sep && depth == 0 => {
                parts.push(s[start..i].to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(s[start..].to_string());
    parts
}

/// Split `s` at the top-level additive tier: operands and the `+` / `-`
/// operators between them. Left-associative; parenthesised/bracketed sub-terms
/// are left intact.
fn split_add(s: &str) -> (Vec<String>, Vec<u8>) {
    let b = s.as_bytes();
    let (mut segs, mut ops) = (Vec::new(), Vec::new());
    let (mut depth, mut start) = (0i32, 0usize);
    for i in 0..b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'+' | b'-' if depth == 0 => {
                segs.push(s[start..i].to_string());
                ops.push(b[i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    segs.push(s[start..].to_string());
    (segs, ops)
}

/// Split `s` at the top-level multiplicative tier: the operands and the
/// operators between them (`*`, `//` for floor-division, `%` for remainder).
/// A `**` power is left intact (bound tighter). Left-associative.
fn split_mul(s: &str) -> (Vec<String>, Vec<u8>) {
    let b = s.as_bytes();
    let (mut segs, mut ops) = (Vec::new(), Vec::new());
    let (mut depth, mut start, mut i) = (0i32, 0usize, 0usize);
    while i < b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'*' if depth == 0 => {
                let double = (i + 1 < b.len() && b[i + 1] == b'*') || (i > 0 && b[i - 1] == b'*');
                if !double {
                    segs.push(s[start..i].to_string());
                    ops.push(b'*');
                    start = i + 1;
                }
            }
            b'/' if depth == 0 && b.get(i + 1) == Some(&b'/') => {
                segs.push(s[start..i].to_string());
                ops.push(b'/'); // `//` compile-time floor-division
                i += 1; // consume the second `/`
                start = i + 1;
            }
            b'/' if depth == 0 => {
                segs.push(s[start..i].to_string());
                ops.push(b'd'); // `/` runtime field division
                start = i + 1;
            }
            b'%' if depth == 0 => {
                segs.push(s[start..i].to_string());
                ops.push(b'%');
                start = i + 1;
            }
            _ => {}
        }
        i += 1;
    }
    segs.push(s[start..].to_string());
    (segs, ops)
}

/// Split `s` once on a top-level multi-char operator `op`.
fn split_once_top(s: &str, op: &str) -> Option<(String, String)> {
    let b = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i + op.len() <= b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            _ if depth == 0 && &s[i..i + op.len()] == op => {
                return Some((s[..i].to_string(), s[i + op.len()..].to_string()));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Fold a compile-time INTEGER expression (literals combined with the usual
/// operators) to its value; `None` if any leaf is not a literal. Placeholders
/// are substituted before parsing, so `GEN ** (K_SKIP + 1)`-style exponents
/// fold here.
fn const_int_expr(e: &Expr) -> Option<u128> {
    match e {
        Expr::Lit(k) => Some(*k),
        Expr::Add(a, b) => const_int_expr(a)?.checked_add(const_int_expr(b)?),
        Expr::Sub(a, b) => const_int_expr(a)?.checked_sub(const_int_expr(b)?),
        Expr::Mul(a, b) => const_int_expr(a)?.checked_mul(const_int_expr(b)?),
        Expr::Div(a, b) => match const_int_expr(b)? {
            0 => None,
            d => Some(const_int_expr(a)? / d),
        },
        Expr::Mod(a, b) => match const_int_expr(b)? {
            0 => None,
            d => Some(const_int_expr(a)? % d),
        },
        Expr::Pow(a, b) => const_int_expr(a)?.checked_pow(u32::try_from(const_int_expr(b)?).ok()?),
        _ => None,
    }
}

/// A range bound (`mul_range` bounds and `assert log _ < log _` bounds): a
/// compile-time power of the generator — `1` (= `g^0`), `GEN` (= `g^1`), or
/// `GEN ** k` — returning the exponent `k`. Both uses walk/compare exponents,
/// so the bound must name `g^k` explicitly (an element that is not a known
/// power of `g` has no usable exponent).
fn gpow_bound(e: &Expr) -> Result<u64, String> {
    match e {
        // `1` is the multiplicative identity g^0 — the natural loop start.
        Expr::Lit(1) => Ok(0),
        Expr::Gen => Ok(1),
        Expr::GPow(k) => u64::try_from(*k).map_err(|_| format!("bound exponent {k} does not fit in u64")),
        other => Err(format!(
            "a range bound must be a power of GEN (`1`, `GEN`, or `GEN ** k`), got `{other:?}`"
        )),
    }
}

fn parse_gpow_bound(s: &str) -> Result<u64, String> {
    gpow_bound(&parse_expr(s)?)
}

/// Strip a leading `log` token (`log x`, `log(x)`), if present. The token must
/// end at a boundary, so a variable named `logx` is not a log of `x`.
fn strip_log(s: &str) -> Option<&str> {
    let r = s.trim_start().strip_prefix("log")?;
    r.starts_with([' ', '(']).then_some(r)
}

/// Substitute `Var(name)` → `to` through a statement list, stopping at a
/// statement that rebinds `name` (later uses refer to the new binding).
/// Nested blocks recurse independently — their bindings are branch-local,
/// matching the lowering's scoping. Used by `Const`-parameter specialization.
pub(crate) fn subst_stmts(stmts: &[Stmt], name: &str, to: &Expr) -> Vec<Stmt> {
    let mut out = Vec::with_capacity(stmts.len());
    let mut active = true;
    for s in stmts {
        if !active {
            out.push(s.clone());
            continue;
        }
        let (s, rebinds) = subst_stmt(s, name, to);
        out.push(s);
        active = !rebinds;
    }
    out
}

/// One statement of [`subst_stmts`]; the flag says whether it rebinds `name`.
fn subst_stmt(s: &Stmt, name: &str, to: &Expr) -> (Stmt, bool) {
    let e = |x: &Expr| subst_var(x, name, to);
    match s {
        Stmt::Let(n, x) => (Stmt::Let(n.clone(), e(x)), n == name),
        Stmt::LetTuple(ns, f, args) => (
            Stmt::LetTuple(ns.clone(), f.clone(), args.iter().map(e).collect()),
            ns.iter().any(|n| n == name),
        ),
        Stmt::AssertEq(a, b) => (Stmt::AssertEq(e(a), e(b)), false),
        Stmt::AssertNe(a, b) => (Stmt::AssertNe(e(a), e(b)), false),
        Stmt::AssertLt(a, k) => (Stmt::AssertLt(e(a), *k), false),
        Stmt::Call(f, args) => (Stmt::Call(f.clone(), args.iter().map(e).collect()), false),
        Stmt::HintWitness { dest, name: n } => (
            Stmt::HintWitness {
                dest: e(dest),
                name: n.clone(),
            },
            false,
        ),
        Stmt::Store(a, i, v) => (Stmt::Store(e(a), e(i), e(v)), false),
        Stmt::Return(es) => (Stmt::Return(es.iter().map(e).collect()), false),
        Stmt::CallIfNe(a, b, f, args) => (
            Stmt::CallIfNe(e(a), e(b), f.clone(), args.iter().map(e).collect()),
            false,
        ),
        Stmt::For { var, lo, hi, body } => {
            let hi = match hi {
                ForBound::Const(k) => ForBound::Const(*k),
                ForBound::Runtime(b) => ForBound::Runtime(e(b)),
            };
            // The counter shadows `name` inside the body only.
            let body = if var == name {
                body.clone()
            } else {
                subst_stmts(body, name, to)
            };
            (
                Stmt::For {
                    var: var.clone(),
                    lo: *lo,
                    hi,
                    body,
                },
                false,
            )
        }
        Stmt::Unroll { var, lo, hi, body } => {
            let body = if var == name {
                body.clone()
            } else {
                subst_stmts(body, name, to)
            };
            (
                Stmt::Unroll {
                    var: var.clone(),
                    lo: e(lo),
                    hi: e(hi),
                    body,
                },
                false,
            )
        }
        Stmt::If {
            eq,
            lhs,
            rhs,
            then,
            els,
        } => (
            Stmt::If {
                eq: *eq,
                lhs: e(lhs),
                rhs: e(rhs),
                then: subst_stmts(then, name, to),
                els: subst_stmts(els, name, to),
            },
            false,
        ),
        Stmt::Match { x, cases } => (
            Stmt::Match {
                x: e(x),
                cases: cases.iter().map(|c| subst_stmts(c, name, to)).collect(),
            },
            false,
        ),
        Stmt::LetMatchRange { names, x, arms } => (
            Stmt::LetMatchRange {
                names: names.clone(),
                x: e(x),
                arms: arms.iter().map(e).collect(),
            },
            names.iter().any(|n| n == name),
        ),
    }
}

/// `e` with every `Var(name)` replaced by `to` — the `match_range` arm
/// expansion, where the lambda parameter becomes the arm's integer literal.
fn subst_var(e: &Expr, name: &str, to: &Expr) -> Expr {
    let s = |b: &Expr| Box::new(subst_var(b, name, to));
    match e {
        Expr::Var(v) if v == name => to.clone(),
        Expr::Add(a, b) => Expr::Add(s(a), s(b)),
        Expr::Mul(a, b) => Expr::Mul(s(a), s(b)),
        Expr::Sub(a, b) => Expr::Sub(s(a), s(b)),
        Expr::Div(a, b) => Expr::Div(s(a), s(b)),
        Expr::FieldDiv(a, b) => Expr::FieldDiv(s(a), s(b)),
        Expr::Mod(a, b) => Expr::Mod(s(a), s(b)),
        Expr::Index(a, b) => Expr::Index(s(a), s(b)),
        Expr::Slice(a, lo, hi) => Expr::Slice(s(a), s(lo), s(hi)),
        Expr::GenPow(e) => Expr::GenPow(s(e)),
        Expr::Pow(a, b) => Expr::Pow(s(a), s(b)),
        Expr::HeapBufDyn(sz) => Expr::HeapBufDyn(s(sz)),
        Expr::ListLit(es) => Expr::ListLit(es.iter().map(|a| subst_var(a, name, to)).collect()),
        Expr::Call(f, args) => Expr::Call(f.clone(), args.iter().map(|a| subst_var(a, name, to)).collect()),
        other => other.clone(),
    }
}

/// `names = match_range(log(x), range(a, b), lambda i: expr, …)` — leanVM's
/// `match_range`, expanded at parse time: one arm per integer of the
/// contiguous `(range, lambda)` pairs, arm `j` being the lambda body with the
/// parameter substituted by the literal `j`. The union of the ranges must be
/// gapless and start at 0 (this compiler's `match` rule). Everything sits on
/// one line — there is no line continuation.
fn parse_match_range(lhs: &str, rhs: &str) -> Result<Stmt, String> {
    if lhs.trim_end().ends_with(']') {
        return Err("bind `match_range` results to names, not a store target".into());
    }
    let names: Vec<String> = split_top(lhs, ',').iter().map(|t| t.trim().to_string()).collect();
    let inner = rhs
        .trim()
        .strip_prefix("match_range(")
        .and_then(|s| s.strip_suffix(')'))
        .ok_or("malformed `match_range(…)`")?;
    let chunks = split_top(inner, ',');
    let (first, pairs) = chunks.split_first().ok_or("match_range needs arguments")?;
    let x = strip_log(first).ok_or("`match_range` matches logs: `match_range(log(x), …)`")?;
    let x = parse_expr(x)?;
    if pairs.is_empty() || !pairs.len().is_multiple_of(2) {
        return Err("match_range needs `range(a, b), lambda i: …` pairs after the scrutinee".into());
    }
    let mut arms = Vec::new();
    for pair in pairs.chunks(2) {
        let (lo, hi) = match parse_expr(&pair[0])? {
            Expr::Call(f, args) if f == "range" => match args.as_slice() {
                [Expr::Lit(a), Expr::Lit(b)] if a < b => (*a, *b),
                _ => return Err("match_range needs `range(a, b)` with integer literals, a < b".into()),
            },
            other => return Err(format!("expected `range(a, b)`, got `{other:?}`")),
        };
        if lo != arms.len() as u128 {
            return Err(format!(
                "match_range ranges must be contiguous from 0: expected a range starting at {}, got {lo}",
                arms.len()
            ));
        }
        let lam = pair[1]
            .trim()
            .strip_prefix("lambda ")
            .ok_or("expected `lambda i: …` after each range")?;
        let (param, body) = split_once_top(lam, ":").ok_or("`lambda` needs `:`")?;
        let body = parse_expr(&body)?;
        for j in lo..hi {
            arms.push(subst_var(&body, param.trim(), &Expr::Lit(j)));
        }
    }
    Ok(Stmt::LetMatchRange { names, x, arms })
}

/// Parse an expression with `+` (lowest) then `*`, atoms being integer literals,
/// variables, calls `f(args)`, and parenthesised sub-expressions.
fn parse_expr(s: &str) -> Result<Expr, String> {
    let s = s.trim();
    // `+` / `-` at top level (lowest precedence), left-associative. `-` is
    // compile-time integer subtraction (field subtraction is `+` = XOR).
    let (segs, ops) = split_add(s);
    if !ops.is_empty() {
        let mut acc = parse_expr(&segs[0])?;
        for (op, seg) in ops.iter().zip(&segs[1..]) {
            let rhs = Box::new(parse_expr(seg)?);
            let lhs = Box::new(acc);
            acc = if *op == b'+' { Expr::Add(lhs, rhs) } else { Expr::Sub(lhs, rhs) };
        }
        return Ok(acc);
    }
    // `*`, `//`, `%` (bind tighter than `+`), skipping the two-char `**`.
    let (segs, ops) = split_mul(s);
    if segs.len() > 1 {
        let mut acc = parse_expr(&segs[0])?;
        for (op, seg) in ops.iter().zip(&segs[1..]) {
            let rhs = Box::new(parse_expr(seg)?);
            let lhs = Box::new(acc);
            acc = match op {
                b'*' => Expr::Mul(lhs, rhs),
                b'/' => Expr::Div(lhs, rhs),
                b'd' => Expr::FieldDiv(lhs, rhs),
                _ => Expr::Mod(lhs, rhs),
            };
        }
        return Ok(acc);
    }
    // `**` (compile-time power), tightest binding: `base ** k` with `k` a
    // (possibly large) integer literal.
    if let Some((base, exp)) = split_once_top(s, "**") {
        let base = parse_expr(&base)?;
        let exp_e = parse_expr(&exp)?;
        return match base {
            // `GEN ** k`: a compile-time integer exponent (a literal or a
            // constant expression like `K_SKIP + 1`) folds to `g^k`; a runtime
            // expression (e.g. an `unroll` var) becomes `GenPow`, resolved at
            // lowering.
            Expr::Gen => match const_int_expr(&exp_e) {
                Some(k) => Ok(Expr::GPow(k)),
                None => Ok(Expr::GenPow(Box::new(exp_e))),
            },
            // Any other base with a compile-time exponent: square-and-multiply.
            _ => Ok(Expr::Pow(Box::new(base), Box::new(exp_e))),
        };
    }
    // Atom.
    if s.starts_with('(') && s.ends_with(')') {
        return parse_expr(&s[1..s.len() - 1]);
    }
    if s == "GEN" {
        return Ok(Expr::Gen);
    }
    if let Ok(n) = s.parse::<u128>() {
        return Ok(Expr::Lit(n));
    }
    // List literal `[a, b, …]` — an initialized StackBuf (only meaningful as
    // the RHS of an assignment; top-level constant arrays are parsed earlier).
    if s.starts_with('[') && s.ends_with(']') {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return Err("a list literal needs at least one element".into());
        }
        return Ok(Expr::ListLit(
            split_top(inner, ',')
                .iter()
                .map(|e| parse_expr(e))
                .collect::<Result<_, _>>()?,
        ));
    }
    // Index `base[idx]` or slice `base[lo:hi]` (binds tightest, like a call).
    if s.ends_with(']') {
        let open = s.find('[').ok_or_else(|| format!("unbalanced `]` in `{s}`"))?;
        let base = parse_expr(&s[..open])?;
        let inner = &s[open + 1..s.len() - 1];
        if let Some((lo, hi)) = split_once_top(inner, ":") {
            return Ok(Expr::Slice(
                Box::new(base),
                Box::new(parse_expr(&lo)?),
                Box::new(parse_expr(&hi)?),
            ));
        }
        let idx = parse_expr(inner)?;
        return Ok(Expr::Index(Box::new(base), Box::new(idx)));
    }
    if let Some(open) = s.find('(')
        && s.ends_with(')')
    {
        let name = s[..open].trim().to_string();
        let args_str = s[open + 1..s.len() - 1].trim();
        let args = if args_str.is_empty() {
            vec![]
        } else {
            split_top(args_str, ',')
                .iter()
                .map(|a| parse_expr(a))
                .collect::<Result<_, _>>()?
        };
        // `HeapBuf(n)` / `StackBuf(n)` are allocations, not ordinary calls. A size
        // that folds as parse-time integer arithmetic (`MAXQ + 1`, constants
        // already substituted) is a static size like a bare literal.
        if name == "HeapBuf" {
            if let Ok(n) = eval_const_int(args_str) {
                return Ok(Expr::HeapBuf(n as u64));
            }
            return match args.as_slice() {
                // A literal size is baked into the bytecode; any other
                // expression is a runtime size (its low word is the count).
                [Expr::Lit(n)] => Ok(Expr::HeapBuf(*n as u64)),
                [e] => Ok(Expr::HeapBufDyn(Box::new(e.clone()))),
                _ => Err("HeapBuf(size) takes one argument".into()),
            };
        }
        if name == "StackBuf" {
            if let Ok(n) = eval_const_int(args_str) {
                return Ok(Expr::StackBuf(n as u64));
            }
            return Err("StackBuf(n) needs a parse-time integer size".into());
        }
        return Ok(Expr::Call(name, args));
    }
    if s.chars().all(|c| c.is_alphanumeric() || c == '_') && !s.is_empty() {
        return Ok(Expr::Var(s.to_string()));
    }
    Err(format!("cannot parse expression `{s}`"))
}
