//! Demonstration binary: work through a sequence of *Principia Mathematica*
//! Chapter 2 theorems, accumulating results, the way the original LT did.
//!
//! Run with:  cargo run

use logic_theorist::{parse, LogicTheorist};

fn main() {
    let program: &[(&str, &str, &str)] = &[
        ("2.05", "(q -> r) -> ((p -> q) -> (p -> r))", "syllogism (one form)"),
        ("2.06", "(p -> q) -> ((q -> r) -> (p -> r))", "syllogism (other form)"),
        ("2.08", "p -> p", "self-implication"),
        ("2.07", "p -> (p | p)", "self-addition"),
        ("Add'", "p -> (q | p)", "addition, commuted"),
        ("2.1", "~p | p", "excluded middle (disjunctive)"),
        ("2.11", "p | ~p", "law of excluded middle"),
    ];

    let mut lt = LogicTheorist::new(7);

    println!("{}", "=".repeat(72));
    println!("  THE LOGIC THEORIST");
    println!("  after Newell, Shaw & Simon (1956)  —  Rust edition");
    println!("{}", "=".repeat(72));
    println!("\nAxioms given (Principia Mathematica propositional calculus):");
    for ax in &lt.theorems {
        println!("    *{:<4}  {}", ax.name, ax.statement);
    }
    println!("\nRules: substitution, replacement (-> as ~ |), detachment (modus ponens).");
    println!("Methods: substitution, detachment, forward/backward chaining.\n");

    for (name, text, gloss) in program {
        let goal = parse(text);
        println!("{}", "-".repeat(72));
        println!("Goal *{name}:  {goal}    ({gloss})");
        match lt.learn(name, &goal) {
            Some(proof) => {
                println!("    PROVED in {} step(s). Proof tree:\n", proof.step_count());
                for line in proof.render().lines() {
                    println!("    {line}");
                }
                println!(
                    "\n    *{name} added to the knowledge base ({} theorems known).",
                    lt.theorems.len()
                );
            }
            None => println!("    ...no proof found within the depth limit."),
        }
    }

    println!("{}", "-".repeat(72));
    let names: Vec<String> = lt.theorems.iter().map(|t| format!("*{}", t.name)).collect();
    println!("\nKnowledge base now contains: {}", names.join(", "));
}
