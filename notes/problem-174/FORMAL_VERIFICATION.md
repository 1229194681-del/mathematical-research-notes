# Formal Verification 鈥?Problem 174

## Status

**Formal verification: F1 for a related real-scalar counterexample**

**Build/kernel check: PASS**

**Lean/source snapshot commit:** `319844f011f58dc2a3a1de0dfb6f33b80af5a53a`

## Environment

- Lean: `4.33.1`
- Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- mathlib: `v4.33.1`
- exact mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`

## Principal theorems

```lean
ScottishBook174.scottish_book_174_negative
ScottishBook174.resolvent_everywhere_but_no_neumann_radius
```

## Development source path

```text
PaperFormalization/Scottish 174/Main.lean
```

## Kernel axiom audit

```text
propext
Classical.choice
Quot.sound
```

No user-defined mathematical axiom occurs in these principal theorems.

## Scope

The Lean development formalizes a distinct real-scalar product-space counterexample.

The flat-function construction presented in the accompanying mathematical note is **not** the construction formalized in this Lean file.

Accordingly, the Lean result must not be presented as kernel verification of every step of the paper's flat-function proof.

## Formalization provenance

Lean code generation and revision: GPT-5.6 Sol, AI-assisted and human-operated.

Build/kernel execution: Chuyang Chen.

## Human mathematical verification

**NONE**

No independent human mathematical review has been performed.

## Statement-correspondence audit

**NONE**

Therefore this record is F1 for the stated formal construction, not F2.

## Important limitation

Successful Lean verification establishes correctness of the formalized statement relative to its assumptions. It does not by itself establish that the formalized statement is exactly equivalent to the historical problem as originally formulated.

## Reproducibility note

The recorded PASS result was obtained in the original development layout at:

`PaperFormalization/Scottish 174/Main.lean`

A deprecation warning concerning `ContinuousLinearMap.mul_apply` was emitted; it did not invalidate compilation or kernel checking.

