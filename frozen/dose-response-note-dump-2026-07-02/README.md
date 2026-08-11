# Dose-Response — Lean 4 formalization

Kernel-checked formalization of [`dose-response.md`](dose-response.md)
(*Dose-Response Audits for Faithful Acceleration*), in the style of the `lean-deference`
corpus it extends. Its companion notes, `faithful-acceleration.md` and
`faithful-acceleration-scope.md`, are in the deference note dump of 2026-06-27; citations "[LI x.y.z]" are to the arXiv v5 of the Logical Induction paper.

## Discipline

Identical to the source corpus: the genuine arithmetic/asymptotic cores are **proved
outright**; Logical-Induction facts enter **only as named hypotheses** (the `hbias`/`hbdd`
discipline). Target is model (D) only — no probability, coins as fixed sequences. Every
module ends with a `#print axioms` audit; every declaration must rest on exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms).

The standing caveat of that discipline (see `AUDIT.md`): the kernel certifies the proofs,
not that the named hypotheses render the LI theorems faithfully. The trust surface is the
definitions and the statements; read them adversarially.

## Modules

| # | Module | Note | Status |
|---|--------|------|--------|
| — | `FaithfulAccelCore` | vendored corpus chain (`dsWeight`, `round_profit_ge` → `soft_total_trust`) | ✅ |
| 1 | `DestinationAudit` | Lemma 4.4, T3(i)/(ii), the exactness iff, Cor T3.5 (note §7) | ✅ |
| 2 | `ThinnedForcing` | T1 per-sparse-schedule (note §5): `thinnedWeight = S·c·dsWeight`, support lemmas, `Summable` conclusion, Cor T1.1, gated classwise form at full strength (`t − ε − o(1)`) | ✅ |
| 3 | `IndependentAtom` | Lemma A (note §6.1, the flagship): mirror traders constructed, value identities proved, day-indexed criterion preservation with realizability guard; atom marginal in the note's limit form `Pₙ(u) → q_∞` | ✅ |
| 4 | `Steering` | T2 (note §6.2–6.3): dose-graded destinations (a), the composed compliant-and-graded arm, audit fires (d), non-attribution (e) via the jump-target identity + day-recursion induction; (b)/(c) carried as citations | ✅ |

Two of the note's displays are as they are because the kernel pinned them: the sign
convention of the §6.1 mirror-value identities (the opposite signs, consistent under
`D ↦ −D`, do not survive the accounting), and the atom marginal in limit form (the exact
`Pₙ(u) = qₙ` needs a price normalization LI markets don't promise).

Not formalized, by declared scope (see `AUDIT.md` §3.7 for the assembled list): the
model-(R)/pseudorandomness leg (note Prop 4.1, Lemma 4.2), prescribed prefixes (Lemma 4.3),
Cor T1.2, T2(b)'s quote-stream clause, T2(c), and the note's §8 open problems —
unrestricted sparsification (shared with `faithful-acceleration.md` §5), Lemma A beyond
finitely many jumps, content randomization.

## Build

```
lake exe cache get   # once
lake build
```

Toolchain `leanprover/lean4:v4.27.0`, mathlib `v4.27.0` (matching the source corpus).
