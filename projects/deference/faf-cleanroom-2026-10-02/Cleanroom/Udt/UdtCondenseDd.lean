import Cleanroom.Udt.UdtCondenseDd.Access
import Cleanroom.Udt.UdtCondenseDd.Approx
import Cleanroom.Udt.UdtCondenseDd.Witness
import Cleanroom.Udt.UdtCondenseDd.Bridge
import Cleanroom.Udt.UdtCondenseDd.Latent
import Cleanroom.Udt.UdtCondenseDd.Markov
import Cleanroom.Udt.UdtCondenseDd.WitnessLatent
import Cleanroom.Udt.UdtCondenseDd.Correspond
import Cleanroom.Udt.UdtCondenseDd.Minimal
import Cleanroom.Udt.UdtCondenseDd.Squeeze
import Cleanroom.Udt.UdtCondenseDd.Submod
import Cleanroom.Udt.UdtCondenseDd.Entropy
import Cleanroom.Udt.UdtCondenseDd.WitnessEntropy

/-!
# `Cleanroom.Udt.UdtCondenseDd`: Gap 1 — approximate factoring, condensation variables and decision-determination

Root module of work package `udt-condense-dd` (faf-cleanroom run, 2026-09-30). Report, findings,
ledger and open list in `run/wp/udt-condense-dd/`.

* `Access` — the predictor-access model; Gap 1's three readings; extensional ↔ factoring (T1);
  perfect accuracy on full support ⟹ factoring (T2(a)).
* `Approx` — the approximate factoring lemma (T3), utility-level approximate DD in both regimes with
  the note's constant derived (T4; `tv` enters once, the single-step Lipschitz hypothesis verbatim),
  on-support invariance (T5), the converse's neighbours (T12(a)).
* `Witness` — layer-A witnesses: the off-support counterexample and its encoding check (T2(b),(c)),
  T3 attained and strict, the prediction-dependent-law witness with the bound below the range
  bound (T4(b)), the constant predictor over two same-policy mechanisms (T12(a)).
* `Bridge` — `FinDist` → `Measure`; `IsSubvariable` = `AEFunctionOf`; DD = `CondIndepFun`
  = `I[E : D_{I,B} | Π̈] = 0` (T7).
* `Latent` — the three-variable RVM and the policy latent model over FAF; perfect condensation ⟹
  `Π̈ ⊑ E` (T9(a)); the mandate's independent-environment witness is impossible.
* `Markov` — DD is the ordered-Markov clause of Theorem 4.9(B); under DD perfect condensation is the
  function clause, i.e. `Π̈ ⊑ E` (T9(b)).
* `WitnessLatent` — `Three`, the decision-determined refutation of "Π̈ is a perfect condensation
  variable" (T9(a)); `Xor`, the non-degenerate positive instance (decision-determined, `Π̈ ⊑ E`,
  `E` not injective, two non-constant policies: the same encoding does perfectly condense when
  `Π̈ ⊑ E`; repair round 2); `NoSubPerfect`, the satisfiability check on `udt-comm-trust`'s `NoSub`
  (N−: `E` is the identity there).
* `Correspond` — the "correspondence theorem for agency" refuted; FAF Theorem 4.15 as the surviving
  neighbour (T8).
* `Minimal` — the minimality premise; refinement; Gap 1 under minimality is definitional (T6).
* `Squeeze` — the "representation theorem" as `S` next to its `C` form; policy-compatibility refuted
  on transparent Newcomb; the one-condition "characterization" (T10).
* `Submod` — approximate submodularity and the exact interaction identity (T11, FAF API request).
* `Entropy` — the entropy-level approximate DD (T11(c)), proved in repair round 1: the
  `D_{I,B}`-averaged gap `|E[U | D_{I,B}] − E[U | Π̈]|` is at most `√(I[E : D_{I,B} | Π̈] / 2)`, by
  Pinsker on the finite simplex, the chain rule for `Π̈ ⊑ D_{I,B}` and the bridge to PFR's
  conditional mutual information. Nothing is open after repair round 1 (`Open.lean` retired; the
  note's T4(b) constant, listed there until this round, is `approxDD_varying`).
* `WitnessEntropy` — `XorSkew`, the N+ witness of `approxDD_entropy` (repair round 2): `Xor` with
  a skewed prior, `U ⊑ E`, not decision-determined, `I[E : D_{I,B} | Π̈] > 0`, and a positive
  left-hand side (`E[U | d] = 1/3` against `E[U | [[d]]] = 1/2` on one atom).
-/
