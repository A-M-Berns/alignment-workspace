# Countermodels A–K

**Status:** `ci-only`.  Every fixture is exact in `tests/test_countermodels.py`; those with
a Lean twin name it.  Worlds are the advisor's interventions under one principal policy
unless said otherwise; `R` is the declared reason view; `V` the committed payload.

## A. Legitimate epistemic influence — authorship HOLDS

Interventions `{silent, proof}`.  `R` records the proof; `V` moves from `0` to `1`.
Reason mediation holds (`V = F ∘ R` with `F(∅) = 0`, `F(proof) = 1`), the principal
binds, so the session is authored although the verdict changed radically.
`TestA`; Lean `Witness.legitimate_influence`.

## B. Direct write — FAILS

`{honest, covert}`; `R` is the argument in both; the covert write moves `V` from `1` to
`0`.  Same reasons, different payload: not mediated; no factor map.  `TestB`.

## C. Coercion — FAILS

`{argue, argue+threat}`; the threat is not an admitted reason, so `R` is blind to the
pair; `V` differs.  `Blind R` holds and `Blind V` fails, so mediation fails.  `TestC`.

## D. Over-rich `R` — vacuous

`R = id`.  The covert-write payload of **B** is now mediated (every fiber is a
singleton).  `Blind R {(honest, covert)}` fails, and so the derived `Blind V` is not
available: the certificate holds and guarantees nothing.  `TestD`; Lean
`Witness.overRich`, `reasonMediated_of_injOn`, `not_blind_of_injOn`.

## E. Under-rich `R` — false manipulation

`R` constant (the proof is not recorded).  The honest proof of **A** now reads as
manipulation: mediation fails.  Recording the proof restores it.  `TestE`; Lean
`Witness.underRich`, `reasonMediated_const_iff`.

## F. Exclusive bind without mediation — FAILS

**B** with the principal signing: bind holds, mediation fails, not authored.  `TestF`;
Lean `Witness.bind_not_mediated`.

## G. Mediation without exclusive bind — FAILS

`{honest, write}`; `V = F ∘ R` exactly; in `write` the advisor emits the answer.
Mediation holds, bind fails, not authored.  `TestG`; Lean `Witness.mediated_not_bind`.

## H. Selection leakage

`q = (σ, other)`; `R` reads `other` only; the principal never sees `σ`.  Advisor policy
`other = σ`: mediation holds, `R` is blind to the selection coordinate, and the payload
depends on `σ`.  Under the sealed policy `other = a` it does not.  A second fixture
reproduces the Value pathology: under the leaking policy the selected candidate is
punished and no selection is an argmax.  `TestH`; Lean `Witness.leak`.

## I. Partial evaluation

Worlds `{0 (mass ¾, certified), 1 (mass ¼, void)}`; `Ṽ` defined on world `0` only, both
candidates worth `½`; strategy follows `b`.  Over the `3×3` grid of completions on the
void world: the activated securities are identical; `R_U = 0` for all; `R_V̄` ranges over
`[0, ¼]` with both ends attained; `R_U = p · R_auth` for every completion.  `TestI`; Lean
`activated_completion_congr`, `regret_constant_completion`,
`regretU_eq_mass_mul_regretAuth`.

## J. Unrelated Integrity failure

Occurrence `1` vanishes (exposure shrinks); occurrence `0`'s account propagates.  No
global step; a local trace exists.  `TestJ`; Lean `Witness.no_evolution`,
`Witness.localLegit`, `Witness.unrelated_integrity_failure`.

## K. Selective certification failure

`C = 0` exactly on anti-advisor worlds for `η ∈ {½, ¼, ⅛}`; `R_U = 0`; the anti-selection
completion attains `R_V̄ = η`; every completion on the grid is at most that.  `TestK`;
Lean `availability_transfer_completion`, `Sharp.transfer_sharp`.

## Sweeps

`R_U = p · R_auth` over `3` worlds, every activation pattern, `{0, ½, 1}³` per candidate,
three mixtures; the perturbation bound `2δ·mass`; the defect `χ` on a three-intervention
session (`χ(honest) = ⅖`, `χ(proof) = 0`).  `TestIdentities`.
