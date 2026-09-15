# Formal Verification 鈥?Problem 129

## Status

**Formal verification: Conditional F1**

**Full-paper formalization: PARTIAL**

**Build/kernel check: PASS**

**Lean/source snapshot commit:** `319844f011f58dc2a3a1de0dfb6f33b80af5a53a`

## Environment

- Lean: `4.33.1`
- Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- mathlib: `v4.33.1`
- exact mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`

## Principal theorem

```lean
Nikliborc129.negative_answer_129 (pub : PublishedTheory)
```

## Development source path

```text
PaperFormalization/Scottish 129/Main.lean
```

## Kernel axiom audit

```text
propext
Classical.choice
Quot.sound
```

No user-defined Lean axiom occurs in the principal theorem.

## Explicit mathematical interface

The theorem is conditional on `PublishedTheory`, a structure containing 27 external theorem interfaces covering:

- calculus/Laplacian bridges;
- smooth cutoff existence;
- homogeneous-ball Newtonian potential facts;
- whole-space obstacle theory;
- Serfaty--Serra stability;
- weak/distributional Laplacian bridges;
- Newtonian representation, uniqueness, and regularity;
- geometric/topological facts about balls and diffeomorphic spheres;
- the classical quadratic interior-potential theorem for ellipsoids.

These interfaces are assumptions of the formal theorem and are not themselves proved in this Lean development.

## Formalization provenance

Lean code generation: GPT-5.6 Sol, AI-assisted and human-operated.

Build/kernel execution: Chuyang Chen.

## Human mathematical verification

**NONE**

No independent human mathematical review has been performed.

## Statement-correspondence audit

**NONE**

Therefore this is a **conditional F1** record, not F2.

## Important limitation

Successful Lean verification establishes correctness of the formalized statement relative to its assumptions. It does not by itself establish that the formalized statement is exactly equivalent to the historical problem as originally formulated.

## Reproducibility note

The `Main.lean` file in this public directory is a source snapshot.

The recorded PASS result was obtained in the original `PaperFormalization` Lake project layout using the source path shown above.

