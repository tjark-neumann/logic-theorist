//! Integration tests. As in the Python suite, every proof emitted by the
//! prover is re-checked independently, so a buggy search cannot pass.

use logic_theorist::{matches, parse, Expr, LogicTheorist, Proof, Subst, Theorem};

/// Independently verify that a proof tree is sound against a set of
/// already-established theorems.
fn check_proof(proof: &Proof, known: &[Theorem]) -> bool {
    for p in &proof.premises {
        if !check_proof(p, known) {
            return false;
        }
    }
    let by_name = |name: &str| known.iter().find(|t| t.name == name).map(|t| &t.statement);
    let goal = &proof.conclusion;

    match proof.method.as_str() {
        "substitution" => match by_name(&proof.reference) {
            Some(stmt) => matches(stmt, goal, &Subst::new()).is_some(),
            None => false,
        },
        "detachment" => {
            // theorem  A -> goal,  premise proves A.
            if proof.premises.len() != 1 {
                return false;
            }
            let a = &proof.premises[0].conclusion;
            match by_name(&proof.reference) {
                Some(stmt) => {
                    let target = Expr::implies(a.clone(), goal.clone());
                    matches(stmt, &target, &Subst::new()).is_some()
                }
                None => false,
            }
        }
        "forward-chaining" => {
            // goal x -> z ; theorem x -> b ; premise b -> z.
            let (x, z) = match goal.as_implication() {
                Some(v) => v,
                None => return false,
            };
            let leg = &proof.premises[0].conclusion;
            let (b, z2) = match leg.as_implication() {
                Some(v) => v,
                None => return false,
            };
            if z2 != z {
                return false;
            }
            match by_name(&proof.reference) {
                Some(stmt) => {
                    matches(stmt, &Expr::implies(x.clone(), b.clone()), &Subst::new()).is_some()
                }
                None => false,
            }
        }
        "backward-chaining" => {
            // goal x -> z ; theorem b -> z ; premise x -> b.
            let (x, z) = match goal.as_implication() {
                Some(v) => v,
                None => return false,
            };
            let leg = &proof.premises[0].conclusion;
            let (x2, b) = match leg.as_implication() {
                Some(v) => v,
                None => return false,
            };
            if x2 != x {
                return false;
            }
            match by_name(&proof.reference) {
                Some(stmt) => {
                    matches(stmt, &Expr::implies(b.clone(), z.clone()), &Subst::new()).is_some()
                }
                None => false,
            }
        }
        _ => false,
    }
}

fn prove_and_check(lt: &LogicTheorist, text: &str) -> Proof {
    let known = lt.theorems.clone();
    let goal = parse(text);
    let proof = lt.prove(&goal).unwrap_or_else(|| panic!("failed to prove {text}"));
    assert_eq!(proof.conclusion, goal);
    assert!(check_proof(&proof, &known), "proof of {text} did not verify");
    proof
}

#[test]
fn parser_roundtrips() {
    for text in ["p -> p", "(p | q) -> (q | p)", "~p | p", "p -> (q | r)"] {
        let e = parse(text);
        assert_eq!(parse(&e.to_string()), e);
    }
}

#[test]
fn implication_is_sugar() {
    assert_eq!(parse("p -> q"), parse("~p | q"));
}

#[test]
fn unicode_accepted() {
    assert_eq!(parse("p ⊃ q"), parse("p -> q"));
    assert_eq!(parse("¬p ∨ p"), parse("~p | p"));
}

#[test]
fn match_yields_instance() {
    let pat = parse("p -> (p | q)");
    let tgt = parse("(a | b) -> ((a | b) | c)");
    let s = matches(&pat, &tgt, &Subst::new()).expect("should match");
    assert_eq!(pat.substitute(&s), tgt);
    assert!(matches(&parse("p -> p"), &parse("p -> q"), &Subst::new()).is_none());
}

#[test]
fn proves_axiom_instances() {
    let lt = LogicTheorist::new(7);
    prove_and_check(&lt, "(p | q) -> (q | p)");
    prove_and_check(&lt, "(a | a) -> a");
}

#[test]
fn proves_classic_theorems() {
    let lt = LogicTheorist::new(7);
    prove_and_check(&lt, "(q -> r) -> ((p -> q) -> (p -> r))"); // *2.05
    prove_and_check(&lt, "p -> p"); // *2.08
    prove_and_check(&lt, "p -> (q | p)");
}

#[test]
fn learning_enables_excluded_middle() {
    let mut lt = LogicTheorist::new(7);
    lt.learn("2.08", &parse("p -> p"));
    prove_and_check(&lt, "~p | p"); // *2.1
    lt.learn("2.1", &parse("~p | p"));
    prove_and_check(&lt, "p | ~p"); // *2.11
}

#[test]
fn non_theorem_is_not_proved() {
    let lt = LogicTheorist::new(5);
    assert!(lt.prove(&parse("p -> q")).is_none());
}
