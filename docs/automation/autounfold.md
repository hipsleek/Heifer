# The `autounfold` tactics

## Usage

Given a proof obligation that we want to automate, we want to automatically unfold some definitions before apply other automation tactics.

## Problem

- How to avoid looping in the case of Landin's knot?
- How to deal with recursive definition?
- Can we use fold/unfold lemmas instead? However, that would require us to automatically derive these lemmas, which is non-trivial.
- How to not unfold meta-symbol (that is defined in the meta-logic, but not in the current session, for example `is_int`)?
- How to choose which symbol to unfold, and whether to unfold them? Sometimes, symbols are given "summarization", and their usage is **rewrite** away using lemmas. Unfolding those symbols may cause this sumarization mechanism to fail. The prime examples of this pattern are the `shift/reset` proofs, in which we use non-trivial summarization lemmas to **rewrite** away usages of symbol (that corresponds to a definition containing `shift`).
- When to call `autounfold` in an automated proof?

## Strategy

- In major proof assistants/functional programming languages (Rocq, Lean, Haskell), terms are reduced only to **weak head normal form** (WHNF). We can try to apply this as a heuristic for our system: terms are `autounfold` to WHNF.
- Additionally, unfolding over recursive definition is restricted (how, exactly?).

## Interaction with other tactics

We note that `autounfold` should not be called arbitrarily, especially on large or recursive definitions. That would lead to an explosion of goal, resulting in a slow proof time. Also, `autounfold` may clash with `autorewrite`, as some relevant lemma may not be appliable on the unfolded term.

## Implementation

- How to not unfold meta-symbol: try apply `unfold`, if that fails, then the symbol cannot be unfolded, we ignore the error.

## Reference

- Rocq `autounfold`: https://rocq-prover.org/doc/V8.19.0/refman/proofs/automatic-tactics/auto.html#coq:tacn.autounfold
- Weak head normal form: https://stackoverflow.com/questions/6872898/what-is-weak-head-normal-form
