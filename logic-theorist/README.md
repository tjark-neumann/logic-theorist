# Logic Theorist

A faithful, working re-creation of the **Logic Theorist** — the 1956 program by
Allen Newell, Cliff Shaw, and Herbert Simon that is widely regarded as the first
artificial-intelligence program ever written.

The original ran on the RAND Corporation's JOHNNIAC and proved theorems of
propositional logic taken from Chapter 2 of Whitehead & Russell's *Principia
Mathematica*. It was demonstrated at the 1956 Dartmouth workshop, the meeting
that gave the field its name. Famously, it found a proof of theorem **2.85**
shorter and more elegant than the one in *Principia* — and the editor of the
*Journal of Symbolic Logic* reportedly declined to publish a paper co-authored
by a machine.

This repo reproduces the program's actual machinery — its axioms, rules of
inference, and search "methods" — in two languages:

- **`python/`** — the readable reference implementation (standard library only)
- **`rust/`** — a port with the same architecture (standard library only)

Both find genuine, verifiable proofs. They are small enough to read in one
sitting and are meant for fun and study, not performance.

## What it actually does

The Logic Theorist works **backward** from a formula you want to prove,
reducing it to subgoals until everything bottoms out in an axiom.

### Primitives and the five axioms

*Principia* takes negation (`~`) and disjunction (`|`) as primitive and *defines*
implication:

```
a -> b   ==   ~a | b
```

This implementation does the same: implication is sugar, so `a -> b` and `~a | b`
are literally the same internal value. That is how *Principia*'s **Replacement**
rule is realised here — there is nothing to convert at run time.

The five propositional-calculus axioms the program was given:

| #     | Axiom                               |
|-------|-------------------------------------|
| *1.2  | `(p \| p) -> p`                     |
| *1.3  | `p -> (p \| q)`                     |
| *1.4  | `(p \| q) -> (q \| p)`              |
| *1.5  | `(p \| (q \| r)) -> (q \| (p \| r))`|
| *1.6  | `(p -> q) -> ((r \| p) -> (r \| q))`|

### Rules of inference

- **Substitution** — uniformly replace a variable by any formula.
- **Replacement** — swap a connective for its definition (handled by keeping
  everything in `~`/`|` primitive form).
- **Detachment** — from `A` and `A -> B`, infer `B` (modus ponens).

### The four search methods

These are exactly the heuristics the 1956 program used:

1. **Substitution method** — is the goal a substitution instance of a known
   axiom or theorem? (the base case)
2. **Detachment method** — find a theorem `A -> goal`, then set up `A` as a new
   subgoal.
3. **Forward chaining** — to prove `a -> c`, find a theorem `a -> b`, then prove
   `b -> c`.
4. **Backward chaining** — to prove `a -> c`, find a theorem `b -> c`, then prove
   `a -> b`.

Chaining is justified by the syllogism principle (*Principia* \*2.06), which is
itself among the theorems the program can prove.

As in the original, **proved theorems are added to the knowledge base** and
reused in later proofs, so the system "learns" as it works through a chapter.

## Running it

### Python

```bash
cd python
python demo.py                       # watch it work through PM Chapter 2
python -m unittest test_logic_theorist -v
```

```python
from logic_theorist import LogicTheorist, parse

lt = LogicTheorist()
proof = lt.prove(parse("p -> (q | p)"))
print(proof.render())
```

### Rust

```bash
cd rust
cargo run            # the demo
cargo test           # tests, including independent proof verification
```

```rust
use logic_theorist::{LogicTheorist, parse};

let lt = LogicTheorist::new(6);
let proof = lt.prove(&parse("p -> (q | p)")).unwrap();
println!("{}", proof.render());
```

## Sample output

Proving \*2.06 (one direction of the syllogism). The program first recognises
that \*2.05 is a substitution instance of axiom \*1.6, then detaches via \*1.5:

```
((p -> q) -> ((q -> r) -> (p -> r)))    [detachment via 1.5]
  ((q -> r) -> ((p -> q) -> (p -> r)))    [substitution via 1.6]
```

Deriving the law of excluded middle, `p | ~p` (\*2.11), once `p -> p` is known —
it is just `~p | p` commuted via axiom \*1.4:

```
(p | ~p)    [backward-chaining via 1.4]
  (p -> p)    [substitution via 2.08]
```

(One pleasant accident this reproduces: \*2.05 falls straight out of axiom \*1.6
by substituting `r := ~p`. The matcher discovers that on its own.)

## Notes on faithfulness

This is an homage in the **spirit** of the original, not a bit-for-bit emulation
of the IPL-II code:

- The search uses iterative-deepening DFS with a depth limit, so the first proof
  found is among the shortest. The original used a similarity heuristic to order
  and prune attempts; here pruning is deliberately light to keep the code clear.
- Every proof is **sound by construction** (substitution produces instances,
  detachment is modus ponens, chaining is the syllogism). The test suites
  *independently re-verify* each proof tree, so a buggy search can never report a
  false theorem.
- Like the original, it is *incomplete*: a depth limit means some true theorems
  will not be found, and it can fail on harder targets in PM Chapter 2.

## Further reading

- A. Newell & H. A. Simon, *The Logic Theory Machine* (IRE Transactions on
  Information Theory, 1956).
- A. Newell, J. C. Shaw & H. A. Simon, *Empirical Explorations of the Logic
  Theory Machine* (1957).
- Pamela McCorduck, *Machines Who Think* (for the history and anecdotes).

## License

MIT — see [LICENSE](LICENSE).
