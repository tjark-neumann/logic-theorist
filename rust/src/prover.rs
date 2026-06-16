//! The Logic Theorist proper: a backward-search prover using the four
//! heuristic methods of the 1956 program — substitution, detachment, and
//! forward / backward chaining — over the five PM axioms.

use std::cell::Cell;
use std::collections::HashSet;

use crate::expr::{matches, Expr, Subst};

/// A named, established formula (an axiom or a previously proved theorem).
#[derive(Clone)]
pub struct Theorem {
    pub name: String,
    pub statement: Expr,
}

impl Theorem {
    fn new(name: &str, statement: Expr) -> Theorem {
        Theorem {
            name: name.to_string(),
            statement,
        }
    }
}

/// The five PM propositional-calculus axioms given to the original program,
/// written in primitive `~`/`|` form (implication shown in comments).
pub fn axioms() -> Vec<Theorem> {
    let (p, q, r) = (Expr::var("p"), Expr::var("q"), Expr::var("r"));
    vec![
        // *1.2  (p | p) -> p
        Theorem::new(
            "1.2",
            Expr::implies(Expr::or(p.clone(), p.clone()), p.clone()),
        ),
        // *1.3  p -> (p | q)
        Theorem::new(
            "1.3",
            Expr::implies(p.clone(), Expr::or(p.clone(), q.clone())),
        ),
        // *1.4  (p | q) -> (q | p)
        Theorem::new(
            "1.4",
            Expr::implies(
                Expr::or(p.clone(), q.clone()),
                Expr::or(q.clone(), p.clone()),
            ),
        ),
        // *1.5  (p | (q | r)) -> (q | (p | r))
        Theorem::new(
            "1.5",
            Expr::implies(
                Expr::or(p.clone(), Expr::or(q.clone(), r.clone())),
                Expr::or(q.clone(), Expr::or(p.clone(), r.clone())),
            ),
        ),
        // *1.6  (p -> q) -> ((r | p) -> (r | q))
        Theorem::new(
            "1.6",
            Expr::implies(
                Expr::implies(p.clone(), q.clone()),
                Expr::implies(
                    Expr::or(r.clone(), p.clone()),
                    Expr::or(r.clone(), q.clone()),
                ),
            ),
        ),
    ]
}

/// A node in a proof tree: a conclusion, the method that produced it, the
/// axiom/theorem invoked, and any sub-proofs.
#[derive(Clone)]
pub struct Proof {
    pub conclusion: Expr,
    pub method: String,
    pub reference: String,
    pub premises: Vec<Proof>,
}

impl Proof {
    fn leaf(conclusion: Expr, method: &str, reference: &str) -> Proof {
        Proof {
            conclusion,
            method: method.to_string(),
            reference: reference.to_string(),
            premises: Vec::new(),
        }
    }

    fn node(conclusion: Expr, method: &str, reference: &str, premise: Proof) -> Proof {
        Proof {
            conclusion,
            method: method.to_string(),
            reference: reference.to_string(),
            premises: vec![premise],
        }
    }

    /// Total number of nodes in the proof tree.
    pub fn step_count(&self) -> usize {
        1 + self.premises.iter().map(Proof::step_count).sum::<usize>()
    }

    /// Render the proof tree as an indented string.
    pub fn render(&self) -> String {
        let mut lines = Vec::new();
        self.render_into(&mut lines, 0);
        lines.join("\n")
    }

    fn render_into(&self, lines: &mut Vec<String>, depth: usize) {
        let indent = "  ".repeat(depth);
        let tag = if self.reference.is_empty() {
            format!("[{}]", self.method)
        } else {
            format!("[{} via {}]", self.method, self.reference)
        };
        lines.push(format!("{indent}{}    {tag}", self.conclusion));
        for p in &self.premises {
            p.render_into(lines, depth + 1);
        }
    }
}

/// The prover. Holds a growing knowledge base of theorems.
pub struct LogicTheorist {
    pub theorems: Vec<Theorem>,
    pub max_depth: usize,
    gensym: Cell<u64>,
}

impl Default for LogicTheorist {
    fn default() -> Self {
        LogicTheorist {
            theorems: axioms(),
            max_depth: 6,
            gensym: Cell::new(0),
        }
    }
}

impl LogicTheorist {
    pub fn new(max_depth: usize) -> Self {
        LogicTheorist {
            theorems: axioms(),
            max_depth,
            gensym: Cell::new(0),
        }
    }

    /// Attempt to prove `goal`, using iterative deepening so the first proof
    /// found is among the shortest.
    pub fn prove(&self, goal: &Expr) -> Option<Proof> {
        for depth in 1..=self.max_depth {
            self.gensym.set(0);
            let seen = HashSet::new();
            if let Some(proof) = self.search(goal, depth as i32, &seen) {
                return Some(proof);
            }
        }
        None
    }

    /// Prove a theorem and, on success, add it to the knowledge base so later
    /// proofs can reuse it — mirroring the original program's accumulation.
    pub fn learn(&mut self, name: &str, goal: &Expr) -> Option<Proof> {
        let proof = self.prove(goal);
        if proof.is_some() {
            self.theorems.push(Theorem::new(name, goal.clone()));
        }
        proof
    }

    fn fresh(&self) -> String {
        let n = self.gensym.get() + 1;
        self.gensym.set(n);
        format!("#{n}")
    }

    fn search(&self, goal: &Expr, depth: i32, seen: &HashSet<Expr>) -> Option<Proof> {
        if seen.contains(goal) {
            return None;
        }
        let mut seen = seen.clone();
        seen.insert(goal.clone());

        // 1) Substitution method (base case).
        if let Some(p) = self.substitution_method(goal) {
            return Some(p);
        }
        if depth <= 0 {
            return None;
        }
        // 2) Detachment method.
        if let Some(p) = self.detachment_method(goal, depth, &seen) {
            return Some(p);
        }
        // 3) Chaining, when the goal is an implication.
        if let Some((a, c)) = goal.as_implication() {
            let (a, c) = (a.clone(), c.clone());
            if let Some(p) = self.forward_chaining(&a, &c, depth, &seen) {
                return Some(p);
            }
            if let Some(p) = self.backward_chaining(&a, &c, depth, &seen) {
                return Some(p);
            }
        }
        None
    }

    fn substitution_method(&self, goal: &Expr) -> Option<Proof> {
        for thm in &self.theorems {
            if matches(&thm.statement, goal, &Subst::new()).is_some() {
                return Some(Proof::leaf(goal.clone(), "substitution", &thm.name));
            }
        }
        None
    }

    fn detachment_method(&self, goal: &Expr, depth: i32, seen: &HashSet<Expr>) -> Option<Proof> {
        // Find a theorem  A -> B  whose consequent B matches the goal; then it
        // suffices to prove the (substituted) antecedent A.
        for thm in &self.theorems {
            let stmt = thm.statement.rename_apart(&self.fresh());
            if let Some((ante, cons)) = stmt.as_implication() {
                if let Some(s) = matches(cons, goal, &Subst::new()) {
                    let subgoal = ante.substitute(&s);
                    if &subgoal == goal {
                        continue;
                    }
                    if let Some(sub) = self.search(&subgoal, depth - 1, seen) {
                        return Some(Proof::node(goal.clone(), "detachment", &thm.name, sub));
                    }
                }
            }
        }
        None
    }

    fn forward_chaining(
        &self,
        a: &Expr,
        c: &Expr,
        depth: i32,
        seen: &HashSet<Expr>,
    ) -> Option<Proof> {
        // Goal  a -> c.  Find theorem  a -> b,  then prove  b -> c.
        let goal = Expr::implies(a.clone(), c.clone());
        for thm in &self.theorems {
            let stmt = thm.statement.rename_apart(&self.fresh());
            if let Some((ante, cons)) = stmt.as_implication() {
                if let Some(s) = matches(ante, a, &Subst::new()) {
                    let b = cons.substitute(&s);
                    let subgoal = Expr::implies(b, c.clone());
                    if subgoal == goal {
                        continue;
                    }
                    if let Some(sub) = self.search(&subgoal, depth - 1, seen) {
                        return Some(Proof::node(goal, "forward-chaining", &thm.name, sub));
                    }
                }
            }
        }
        None
    }

    fn backward_chaining(
        &self,
        a: &Expr,
        c: &Expr,
        depth: i32,
        seen: &HashSet<Expr>,
    ) -> Option<Proof> {
        // Goal  a -> c.  Find theorem  b -> c,  then prove  a -> b.
        let goal = Expr::implies(a.clone(), c.clone());
        for thm in &self.theorems {
            let stmt = thm.statement.rename_apart(&self.fresh());
            if let Some((ante, cons)) = stmt.as_implication() {
                if let Some(s) = matches(cons, c, &Subst::new()) {
                    let b = ante.substitute(&s);
                    let subgoal = Expr::implies(a.clone(), b);
                    if subgoal == goal {
                        continue;
                    }
                    if let Some(sub) = self.search(&subgoal, depth - 1, seen) {
                        return Some(Proof::node(goal, "backward-chaining", &thm.name, sub));
                    }
                }
            }
        }
        None
    }
}
