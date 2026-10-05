# Sierpiński's closed-partition theorem

A nonempty compact connected Hausdorff space cannot be partitioned into countably many pairwise disjoint closed pieces unless one piece is the whole space. Empty pieces are allowed, and finite partitions are included.

`Solution.lean` proves the result for natural-number indices and for any countable index type. It also proves that a continuous function choosing pointwise among countably many everywhere-distinct continuous functions agrees globally with one fixed function. The codomain of those functions need only be Hausdorff.

The proof follows Lemma 5.9 and Theorem 5.10 in [Chapter V of the Washington University topology notes](https://www.math.wustl.edu/~freiwald/topology/Ch5.pdf#page=19), printed pages 231 through 233. It uses a local, credited Boundary Bumping proof, separation in a compact connected subtype, and Mathlib's Cantor intersection theorem. The shrinking helper is private because its assumptions occur only inside the contradiction argument.

The exact pins are Lean `4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. `Challenge.lean` imports Mathlib alone and gives the three selected statement contracts with deliberate theorem holes. Solution has no admissions or new axioms.

For an ordinary dependency installation and strict verification, run:

```text
python3 scripts/verify.py --lake-build
```

The verifier compiles Solution afresh, compiles an isolated random-name copy of Challenge with dependency paths alone, compares complete raw declaration types and universe parameters, and audits transitive axioms. The CI workflow runs this command. Independent AI review approved the full mathematical scope and exact local proof, type, universe, axiom, and JSON metadata checks without corrections. See `REVIEW.md` and `VERIFICATION.md` for the checked scope and remaining limits.

`PROVENANCE.md` records source attribution, reuse, and the scope of the Mathlib search. `formalization.yaml` contains v0.4 metadata. The private review archive contains exact source files and full diagnostic receipts; it excludes cached dependency binaries. Publication uses only the separately audited 16-file public whitelist. No registry submission or public repository change is made by this desktop task.
