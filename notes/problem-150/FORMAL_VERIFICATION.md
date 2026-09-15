# Formal Verification — Problem 150

## Status

**Formal verification: Conditional F1**

**Build/kernel check: PASS**

## Environment

- Lean: `4.33.1`
- Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
- mathlib: `v4.33.1`
- exact mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`

## Principal theorems

```lean
Nikliborc150.counterexample
Nikliborc150.printed_problem_150_is_false
```

## Development source path

```text
PaperFormalization/Scottish 150/Main.lean
```

## Kernel axiom audit

```text
propext
Classical.choice
Quot.sound
Nikliborc150.classical_balayage_on_sphere
```

## Explicit external mathematical axiom

`Nikliborc150.classical_balayage_on_sphere`

The formal proof is therefore conditional on this explicit classical balayage input.

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

