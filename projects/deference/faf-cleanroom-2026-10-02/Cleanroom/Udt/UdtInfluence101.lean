import Cleanroom.Udt.UdtInfluence101.Defs
import Cleanroom.Udt.UdtInfluence101.Atoms
import Cleanroom.Udt.UdtInfluence101.Calculus
import Cleanroom.Udt.UdtInfluence101.Theorem1
import Cleanroom.Udt.UdtInfluence101.Tiling
import Cleanroom.Udt.UdtInfluence101.Conservation
import Cleanroom.Udt.UdtInfluence101.Profile
import Cleanroom.Udt.UdtInfluence101.ProfileLemmas
import Cleanroom.Udt.UdtInfluence101.ProfileA5
import Cleanroom.Udt.UdtInfluence101.Witnesses
import Cleanroom.Udt.UdtInfluence101.Deferral
import Cleanroom.Udt.UdtInfluence101.Two
import Cleanroom.Udt.UdtInfluence101.Tie
import Cleanroom.Udt.UdtInfluence101.Omega
import Cleanroom.Udt.UdtInfluence101.Bridge
import Cleanroom.Udt.UdtInfluence101.Priv
import Cleanroom.Udt.UdtInfluence101.OmegaA5
import Cleanroom.Udt.UdtInfluence101.HomeScore

/-!
# `Cleanroom.Udt.UdtInfluence101`: Diffractor's UDT1.01 — influence lemmas, tiling, the profile model

Root module of the `udt-influence-101` work package (faf-cleanroom run, 2026-10-02). Sources:
Diffractor's UDT1.01 Posts 2, 4, 6, 7, 8 (`research/udt-representation-theorem/references/udt101/`)
and Abram's notes on the PDFs. Dependency: `Cleanroom.Udt.UdtPolicyCalc`.

* `Defs`: `Alg`, `PlaySpace` (signed polynomial ε-law), atoms, conditionals (junk `0`), the three
  influences as `deriv … 0`, `SmoothLaw`/`A1`, `avg` (`Ā_{h,n}`), `A3`/`A4`/`A5`/`CEI`, positivity
  predicates, `Along`.
* `Atoms`: the filtration, measurability, `avg` lemmas (clipping identity `avg_avg`), the regrouping
  identity and the tower property.
* `Calculus`: T1 Assumption 2 as a theorem, `A1_of_smoothLaw`; T2 Lemma 1 as a product rule
  (`lemma1_split`); T3 `fS`, Post 8 Lemma 1 (`IE_ofDist_affine`), Lemma 2 (`fS_affine`).
* `Theorem1`: T4 Post 8 Theorem 1 (`theorem1`, `theorem1_sum`).
* `Tiling`: T5 `IsUDT101`, Theorem 2 as weak dominance (`theorem2_tiling`), non-uniqueness
  (`exists_two_isUDT101`), the tie class (`tie_iff`).
* `Conservation`: T6 the decomposition behind the failure of CEI (`IEo_decomp`, `CEI_iff`,
  `A4_at_of_shift_eq`).
* `Profile`, `ProfileLemmas`, `ProfileA5`: T7 the profile-predictor model; `smoothLaw` (A1), `A3`,
  `A4` derived; `A5` for constant algorithms and for precommitments along `h` under `OneEps`;
  OPEN `A5_ofDist_general`.
* `Witnesses`: T7 instance (I), Counterfactual Mugging With Homework; Theorem 1 and 2 instantiated.
* `Deferral`: T13 the value of deferral (`defer_ge_now`, `defer_ge_commit`), the chicken failure
  witness and the coin strict-gain witness.
* `Two` (repair round 1): horizon-`2` marginalization lemmas; **inert nodes** (nobody reads the
  node's profile, kernels ignore the action) have zero influences and zero score.
* `Tie` (repair round 1): the tie instance — both constants are UDT1.01 at the inert node `hT`
  (`two_udt101_hT`), the score is non-constant at the root (`score_root`): the N+ witness for the
  refutation of the uniqueness glosses.
* `Omega` (repair round 1): instance (II) — CEI fails (`not_CEI`: `1/8 ≠ 0`) in a model with `A1`,
  `A3`, `A4`, `AllPosObs`, `ReachPos`; `OmegaA5` (repair round 2) proves `A5` there too (`A5_asp`,
  OPEN in round 1), so the failure sits inside Theorem 1's full hypothesis package.
* `Bridge` (repair round 1): T8 — a DD-like environment implies A3 (`profile_env_implies_A3`); A3
  does not imply a behaviour-determined law (`law_not_determined` on `sqSpace`, which satisfies
  A3); A2 without DD (`a2_without_dd`).
* `Priv` (repair round 2): Post 8's literal Assumption 5 as a predicate (`PlaySpace.A5Lit`) and the
  private-signal model, where it holds while the precommitment form `A5` fails (`Priv.not_A5`) and
  **Post 8's Theorem 1 fails under its stated assumptions** (`Priv.theorem1_fails`,
  `Priv.post8_theorem1_counterexample`: left side `0`, right side `1/2`).
* `HomeScore` (repair round 2): in the homework instance the pure actions' time-`0` influences at
  `hT` are `±1/8` (`IE_true`, `IE_false`), so `f^0_{hT}` is not constant there
  (`score_hT_nonconst`) — the in-library N+ companion of the `hH` tie.

Not built (see the report): T9–T12, T12b (docstring only), T14–T16.
-/
