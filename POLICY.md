# Publication and Verification Policy

This repository separates three independent questions:

1. whether a mathematical note has undergone human mathematical review;
2. whether a formal Lean statement has passed kernel checking;
3. whether that formal statement has been audited as an exact rendering of the historical problem.

## Mathematical review

Current public notes are classified as:

**E1 — AI cross-checked; NOT HUMAN VERIFIED.**

No independent human mathematical review has been performed.

## Formal verification

`F1` means that an explicit formal statement has been accepted by the Lean kernel in the recorded environment.

`Conditional F1` means that the formal theorem is kernel-checked relative to explicit mathematical assumptions or interfaces that are not themselves formalized in the development.

`F2` would additionally require a human audit of the correspondence between the historical/natural-language problem and the Lean statement.

None of the present records claims F2.

## Important limitation

Successful Lean verification establishes correctness of the formalized statement relative to its assumptions. It does not by itself establish that the formalized statement is exactly equivalent to the historical problem as originally formulated.

## Corrections and withdrawal

If a mathematical error is identified, the affected record will be marked explicitly as withdrawn or superseded rather than silently removed.

Readers are encouraged to report errors, relevant prior literature, or statement-correspondence issues.


