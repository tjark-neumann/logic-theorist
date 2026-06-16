//! Logic Theorist — a faithful re-creation of the 1956 program by
//! Newell, Shaw & Simon, often called the first artificial-intelligence
//! program. It proves theorems of propositional logic from the five axioms
//! of *Principia Mathematica* using substitution, detachment (modus ponens),
//! and chaining.
//!
//! ```
//! use logic_theorist::{LogicTheorist, parse};
//!
//! let lt = LogicTheorist::new(6);
//! let proof = lt.prove(&parse("p -> (q | p)")).expect("provable");
//! println!("{}", proof.render());
//! ```

pub mod expr;
pub mod prover;

pub use expr::{matches, parse, Expr, Subst};
pub use prover::{axioms, LogicTheorist, Proof, Theorem};
