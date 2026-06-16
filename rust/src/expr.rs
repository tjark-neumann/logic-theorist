//! Propositional formulas in *Principia Mathematica* primitive form.
//!
//! Only three constructors exist: variables, negation, and disjunction.
//! Implication is sugar — `a -> b` is built as `~a | b` (PM's definition),
//! which is how the "Replacement" rule is realised: every formula already
//! lives in primitive form, so `a -> b` and `~a | b` are the same value.

use std::collections::HashMap;
use std::fmt;

/// A propositional formula.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Expr {
    Var(String),
    Not(Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
}

/// A substitution from variable names to formulas.
pub type Subst = HashMap<String, Expr>;

impl Expr {
    pub fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    pub fn not(e: Expr) -> Expr {
        Expr::Not(Box::new(e))
    }

    pub fn or(a: Expr, b: Expr) -> Expr {
        Expr::Or(Box::new(a), Box::new(b))
    }

    /// Build `a -> b` as the primitive `~a | b`.
    pub fn implies(a: Expr, b: Expr) -> Expr {
        Expr::or(Expr::not(a), b)
    }

    /// If this formula has the shape `a -> b` (i.e. `~a | b`), return `(a, b)`.
    pub fn as_implication(&self) -> Option<(&Expr, &Expr)> {
        if let Expr::Or(left, right) = self {
            if let Expr::Not(inner) = left.as_ref() {
                return Some((inner.as_ref(), right.as_ref()));
            }
        }
        None
    }

    /// Apply a substitution throughout the formula.
    pub fn substitute(&self, subst: &Subst) -> Expr {
        match self {
            Expr::Var(name) => subst.get(name).cloned().unwrap_or_else(|| self.clone()),
            Expr::Not(e) => Expr::not(e.substitute(subst)),
            Expr::Or(a, b) => Expr::or(a.substitute(subst), b.substitute(subst)),
        }
    }

    /// Collect the set of variable names occurring in the formula.
    pub fn variables(&self, out: &mut Vec<String>) {
        match self {
            Expr::Var(name) => {
                if !out.contains(name) {
                    out.push(name.clone());
                }
            }
            Expr::Not(e) => e.variables(out),
            Expr::Or(a, b) => {
                a.variables(out);
                b.variables(out);
            }
        }
    }

    /// Rename every variable with a suffix, to avoid clashes when a theorem
    /// is reused inside a larger proof.
    pub fn rename_apart(&self, suffix: &str) -> Expr {
        let mut vars = Vec::new();
        self.variables(&mut vars);
        let mut subst: Subst = HashMap::new();
        for v in vars {
            subst.insert(v.clone(), Expr::var(&format!("{v}{suffix}")));
        }
        self.substitute(&subst)
    }
}

/// One-way match: find a substitution `s` with `pattern.substitute(&s) == target`.
/// Variables in `pattern` may bind; `target` is treated as fixed structure.
pub fn matches(pattern: &Expr, target: &Expr, subst: &Subst) -> Option<Subst> {
    match pattern {
        Expr::Var(name) => match subst.get(name) {
            Some(bound) => {
                if bound == target {
                    Some(subst.clone())
                } else {
                    None
                }
            }
            None => {
                let mut next = subst.clone();
                next.insert(name.clone(), target.clone());
                Some(next)
            }
        },
        Expr::Not(p) => {
            if let Expr::Not(t) = target {
                matches(p, t, subst)
            } else {
                None
            }
        }
        Expr::Or(pl, pr) => {
            if let Expr::Or(tl, tr) = target {
                let s = matches(pl, tl, subst)?;
                matches(pr, tr, &s)
            } else {
                None
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(name) => write!(f, "{name}"),
            Expr::Not(e) => write!(f, "~{e}"),
            Expr::Or(left, right) => {
                // Re-sugar  ~a | b  back into  a -> b  for readability.
                if let Expr::Not(inner) = left.as_ref() {
                    write!(f, "({inner} -> {right})")
                } else {
                    write!(f, "({left} | {right})")
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Parser
//
// Precedence: ~ tightest, then |, then ->, right-associative.
// Accepts ascii (~ | ->) and unicode (¬ ∨ ⊃ →) interchangeably.
// ---------------------------------------------------------------------------

/// Parse a formula from text. Panics with a message on malformed input
/// (this is a teaching tool, not a production parser).
pub fn parse(text: &str) -> Expr {
    let normalized = text
        .replace('¬', "~")
        .replace('∨', "|")
        .replace('⊃', "->")
        .replace('→', "->");
    let chars: Vec<char> = normalized.chars().collect();
    let mut p = Parser { chars, pos: 0 };
    let e = p.parse_imp();
    p.skip_ws();
    if p.pos != p.chars.len() {
        panic!("unexpected trailing text in formula: {text:?}");
    }
    e
}

struct Parser {
    chars: Vec<char>,
    pos: usize,
}

impl Parser {
    fn skip_ws(&mut self) {
        while self.pos < self.chars.len() && self.chars[self.pos].is_whitespace() {
            self.pos += 1;
        }
    }

    fn eat(&mut self, token: &str) -> bool {
        self.skip_ws();
        let tk: Vec<char> = token.chars().collect();
        if self.pos + tk.len() <= self.chars.len()
            && self.chars[self.pos..self.pos + tk.len()] == tk[..]
        {
            self.pos += tk.len();
            true
        } else {
            false
        }
    }

    fn parse_imp(&mut self) -> Expr {
        let left = self.parse_or();
        if self.eat("->") {
            let right = self.parse_imp(); // right-associative
            Expr::implies(left, right)
        } else {
            left
        }
    }

    fn parse_or(&mut self) -> Expr {
        let mut left = self.parse_unary();
        while self.eat("|") {
            let right = self.parse_unary();
            left = Expr::or(left, right);
        }
        left
    }

    fn parse_unary(&mut self) -> Expr {
        if self.eat("~") {
            Expr::not(self.parse_unary())
        } else {
            self.parse_atom()
        }
    }

    fn parse_atom(&mut self) -> Expr {
        if self.eat("(") {
            let e = self.parse_imp();
            if !self.eat(")") {
                panic!("missing closing parenthesis");
            }
            return e;
        }
        self.skip_ws();
        let start = self.pos;
        while self.pos < self.chars.len()
            && (self.chars[self.pos].is_alphanumeric() || self.chars[self.pos] == '_')
        {
            self.pos += 1;
        }
        if start == self.pos {
            panic!("expected a variable at position {}", self.pos);
        }
        Expr::Var(self.chars[start..self.pos].iter().collect())
    }
}
