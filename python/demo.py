"""
Demonstration: watch the Logic Theorist work through a sequence of theorems
from *Principia Mathematica* Chapter 2, accumulating results as it goes — the
way the original program did in 1956.

Run with:  python demo.py
"""

from logic_theorist import LogicTheorist, parse


# A small "curriculum" of theorems. Each is proved using only the five axioms
# plus whatever has already been proved, then added to the knowledge base.
PROGRAM = [
    ("2.05", "(q -> r) -> ((p -> q) -> (p -> r))", "syllogism (one form)"),
    ("2.06", "(p -> q) -> ((q -> r) -> (p -> r))", "syllogism (other form)"),
    ("2.08", "p -> p",                              "self-implication"),
    ("2.07", "p -> (p | p)",                        "self-addition"),
    ("Add'", "p -> (q | p)",                        "addition, commuted"),
    ("2.1",  "~p | p",                              "excluded middle (disjunctive)"),
    ("2.11", "p | ~p",                              "law of excluded middle"),
]


def main() -> None:
    lt = LogicTheorist(max_depth=7)

    print("=" * 72)
    print("  THE LOGIC THEORIST")
    print("  after Newell, Shaw & Simon (1956)")
    print("=" * 72)
    print("\nAxioms given (Principia Mathematica propositional calculus):")
    for ax in lt.theorems:
        print(f"    *{ax.name:4}  {ax.statement}")
    print("\nRules: substitution, replacement (-> as ~ |), detachment (modus ponens).")
    print("Methods: substitution, detachment, forward/backward chaining.\n")

    for name, text, gloss in PROGRAM:
        goal = parse(text)
        print("-" * 72)
        print(f"Goal *{name}:  {goal}    ({gloss})")
        proof = lt.learn(name, goal)
        if proof is None:
            print("    ...no proof found within the depth limit.")
            continue
        print(f"    PROVED in {proof.step_count()} step(s). Proof tree:\n")
        for line in proof.render().splitlines():
            print("    " + line)
        print(f"\n    *{name} added to the knowledge base "
              f"({len(lt.theorems)} theorems known).")

    print("-" * 72)
    print("\nKnowledge base now contains:",
          ", ".join(f"*{t.name}" for t in lt.theorems))
    print("\nTry your own:  LogicTheorist().prove(parse('p -> (q | p)'))")


if __name__ == "__main__":
    main()
