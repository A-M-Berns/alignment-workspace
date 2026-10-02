import Cleanroom.Bli.UdtBliLearning.Defs

/-!
# `udt-bli-learning` · Calibration: calibrated versus uncalibrated under the external criterion
"ex-ante value under the true law" (T5)

**Scope: single coin, additive stakes, finite horizon `K`; the criterion is external — the value
of a policy under the prior whose coin probability is the *true* `q'`** (`valueUnder p q' π :=
(scPrior (withQ p q')).exAnteValue π`, with `withQ` changing only `q`). The frozen prior `scPrior
p` is *calibrated* when `q' = q` (the source's "calibrated" means "objectively correct
probabilities", journal 2023-09-27 ll. 95–97; the reference-class notion of bli-paper-2-012 is not
formalized).

* **Calibrated (`q' = q`).** `priorOptimal_beats` (Kind **T**: prior-optimality *is* "weakly
  beats every policy", in particular every updateful one — the first reading of "correct UDT
  behavior is a strict superset of correct updateful behavior"); the strict instance
  `updateful_strictly_beaten` (Kind **C**): for `gain > 0` the updateful rule refuses at every
  `Ask_j` (`homeEU_diff`, `isUpdatefulChoice_refuse`, re-proved on `scPrior`), so every updateful
  policy loses at least `gain · γ_j` against `payAll`; **its hypothesis package is inhabited**:
  `refuseAll` is an updateful policy of `scPrior p` (`isUpdatefulPolicy_refuseAll`, N+; at `Rec_k`
  and `Other` the home value is action-blind, `homeEU_actionBlind`), and
  `updateful_strictly_beaten_refuseAll` fires the headline on it (gap `≥ gain · ∑ γ`); and the
  tie-aware form `le_priorOptimal_iff`: *every* policy's value is at most the optimum's, with
  equality iff it is itself prior-optimal (stated for every policy, since the statement would not
  use an updateful hypothesis; read at the updateful `refuseAll`).
* **Uncalibrated (`q' ≠ q`).** `venn_coin_true` (`q' = 1`): `valueUnder 1 payAll = −c ∑γ + r₀ true <
  r₀ true = valueUnder 1 refuseAll`; `venn_coin_false` (`q' = 0`): `valueUnder 0 refuseAll = r₀ false
  < V ∑γ + r₀ false = valueUnder 0 payAll`. With the calibrated case this is **the full Venn
  diagram** (`venn_diagram`): the prior-optimal `payAll` is more correct than the updateful
  `refuseAll` under `q' = q` and `q' = 0`, less correct under `q' = 1`.

`q' ∈ {0, 1}` makes some tables null, but the policy law is the same product-uniform law for every
`q'`, so `NDPOLICY` holds and every `exAnteValue` compared is that of a positive-mass policy
(`structure_facts (withQ p q')`). The one new positivity hypothesis is `0 < w j` (the round `j`
has positive mass) for the home-branch computation at `Ask_j`.

Sources: bli-paper-2-009 (`udt-tiling-working-notes-2025-06-30` b.278–285: "Assuming
calibration, correct UDT behavior is a strict superset of correct updateful behavior. If we drop
the calibration assumption, it seems like we get the full Venn diagram"; examples include
"iterated mugging with a single coin"); bli-soto-b-051 (journal 2023-09-27 ll. 7–65, 95–97);
mandate T5.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

variable {K : ℕ} (p : Params K)

/-! ## The true law: the same model with another coin probability -/

/-- **The parameters with the coin probability replaced by `q'`** (everything else unchanged): the
*true law* when `q'` is the objective probability of the coin.
Source: bli-paper-2-009 ("calibrated" = objectively correct probabilities); mandate T5
Kind: D
Fidelity: exact -/
def withQ (q' : ℚ) (h0 : 0 ≤ q') (h1 : q' ≤ 1) : Params K :=
  { p with q := q', hq0 := h0, hq1 := h1 }

/-- **The external criterion**: the ex-ante value of `π` under the prior with the true coin
probability `q'`.
Source: bli-paper-2-009; mandate T5 ("the *true* law; external criterion")
Kind: D
Fidelity: exact -/
def valueUnder (q' : ℚ) (h0 : 0 ≤ q') (h1 : q' ≤ 1) (π : Policy (iterTables K) Bool) : ℚ :=
  (scPrior (withQ p q' h0 h1)).exAnteValue π

/-- `valueUnder` in closed form: `(V(1−q') − cq') · roundSum γ π + q' r₀ true + (1−q') r₀ false`.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem valueUnder_eq (q' : ℚ) (h0 : 0 ≤ q') (h1 : q' ≤ 1) (π : Policy (iterTables K) Bool) :
    valueUnder p q' h0 h1 π =
      (p.V * (1 - q') - p.c * q') * roundSum p.γ π + (q' * p.r₀ true + (1 - q') * p.r₀ false) := by
  unfold valueUnder
  rw [exAnteValue_eq]
  rfl

/-- At `q' = q` the external criterion is the frozen prior's own value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma valueUnder_self (π : Policy (iterTables K) Bool) :
    valueUnder p p.q p.hq0 p.hq1 π = (scPrior p).exAnteValue π := by
  rw [valueUnder_eq, exAnteValue_eq]; rfl

/-- `tailSum γ 0 = ∑ γ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tailSum_zero : tailSum p.γ 0 = ∑ k, p.γ k := by
  unfold tailSum; simp

/-! ## The updateful rule on the model: the home-branch value at `Ask_j` -/

/-- The table that obtains is `st (some (b, j))` iff the base outcome is `(b, j)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseState_eq_st_iff (ω₀ : Base K) (b : Bool) (j : Fin K) :
    baseState ω₀ = st K (some (b, j)) ↔ (ω₀.1 = b ∧ ω₀.2 = j) := by
  constructor
  · intro h
    have := Option.some_injective _ (st_injective K h)
    rw [this]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have : ω₀ = (b, j) := Prod.ext h1 h2
    rw [this]; rfl

/-- A sum over the base collapses at the single outcome `(b, j)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_base_single (g : Base K → ℚ) (b : Bool) (j : Fin K) :
    (∑ ω₀ : Base K, if ω₀.1 = b ∧ ω₀.2 = j then g ω₀ else 0) = g (b, j) := by
  rw [Fintype.sum_prod_type]
  cases b <;> simp [Finset.sum_ite_eq']

/-- **The branch value of a point at a single base outcome, in closed form**: for
`baseMass (b, j) > 0`, `condEU (st (b, j)) Ask_j a = payoff(b) · (γ_j ([a] − ½) + ∑_k γ_k/2) + r₀ b`
— inside the branch `(b, j)` the other rounds' points are still uniform, so the action moves only
its own round's term. `b = true` is the home branch of `Ask_j` (`homeEU_askT_eq`); `b = false` is
the cross branch `Rec_j` (the non-squeeze witness of `EpsCorr.lean`).
Source: bli-soto-a-011 (the updateful picture); mandate T5 ("re-prove on `scPrior`"), T9 (N−)
Kind: P
Fidelity: exact
Hyps: (a) `0 < baseMass (b, j)`; does not use faith -/
theorem condEU_base_askT_eq (b : Bool) (j : Fin K) (a : Bool) (hpos : 0 < baseMass p (b, j)) :
    (scPrior p).condEU (st K (some (b, j))) (askT K j) a =
      payoff p.c p.V b * (p.γ j * (ind a - 1 / 2) + ∑ k, p.γ k * (1 / 2)) + p.r₀ b := by
  unfold FiniteBLIPrior.condEU scPrior
  have hev : ∀ ω : (scData p).Ω₀ × Policy (iterTables K) Bool,
      ((scData p).toPrior.state ω = st K (some (b, j)) ∧
        (scData p).toPrior.pp ω (askT K j) = a) ↔
      ((ω.1.1 = b ∧ ω.1.2 = j) ∧ ω.2 (askT K j) = a) := by
    intro ω
    change (baseState ω.1 = st K (some (b, j)) ∧ ω.2 (askT K j) = a) ↔ _
    rw [baseState_eq_st_iff]
  refine ((condExp_congr _ _ hev).trans
    (IndepCalc.condExp_base_point (scData p) (fun ω₀ : Base K => ω₀.1 = b ∧ ω₀.2 = j)
      (askT K j) a)).trans ?_
  rw [SingleCoin.massOf_point]
  change (∑ ω₀ : Base K, if ω₀.1 = b ∧ ω₀.2 = j then baseMass p ω₀ * ∑ π,
      (if π (askT K j) = a then (scData p).ν π * (scData p).U₀ ω₀ π else 0) else 0) /
    (massOf (baseMass p) (fun ω₀ : Base K => ω₀.1 = b ∧ ω₀.2 = j) * (1 / 2)) = _
  simp only [inner_sum, roundMoment_eq]
  rw [sum_base_single]
  have hm : massOf (baseMass p) (fun ω₀ : Base K => ω₀.1 = b ∧ ω₀.2 = j) =
      baseMass p (b, j) := by
    unfold massOf
    exact sum_base_single (baseMass p) b j
  rw [hm, mul_div_mul_left _ _ (ne_of_gt hpos),
    mul_div_cancel_left₀ _ (by norm_num : (1 / 2 : ℚ) ≠ 0)]

/-- **The home-branch value at `Ask_j` in closed form**: for `q · w_j > 0`,
`homeEU Ask_j a = −c · (γ_j ([a] − ½) + ∑_k γ_k/2) + r₀ true`.
Source: bli-soto-a-011 (the updateful picture); mandate T5 ("re-prove on `scPrior`")
Kind: C (`condEU_base_askT_eq`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < w_j`; does not use faith -/
theorem homeEU_askT_eq (j : Fin K) (a : Bool) (hq : 0 < p.q) (hw : 0 < p.w j) :
    (scPrior p).homeEU (askT K j) a =
      -p.c * (p.γ j * (ind a - 1 / 2) + ∑ k, p.γ k * (1 / 2)) + p.r₀ true := by
  have h := condEU_base_askT_eq p true j a
    (by unfold baseMass; simp only [↓reduceIte]; exact mul_pos hq hw)
  unfold FiniteBLIPrior.homeEU
  rw [h]
  simp [payoff]

/-- **The updateful verdict at every round**: `homeEU Ask_j pay − homeEU Ask_j refuse = −c · γ_j`.
Source: bli-soto-a-011; bli-paper-2-009 (the updateful rule refuses); mandate T5
Kind: C (`homeEU_askT_eq`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < w_j`; does not use faith -/
theorem homeEU_diff (j : Fin K) (hq : 0 < p.q) (hw : 0 < p.w j) :
    (scPrior p).homeEU (askT K j) true - (scPrior p).homeEU (askT K j) false = -p.c * p.γ j := by
  rw [homeEU_askT_eq p j true hq hw, homeEU_askT_eq p j false hq hw]
  simp only [ind_true, ind_false]
  ring

/-- **The updateful choice at `Ask_j` is uniquely `refuse`** (`c > 0`, `γ_j > 0`, `q · w_j > 0`).
Source: bli-paper-2-009; mandate T5
Kind: C (`homeEU_diff`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < w_j`, `0 < c`, `0 < γ_j`; does not use faith -/
theorem isUpdatefulChoice_refuse (j : Fin K) (hq : 0 < p.q) (hw : 0 < p.w j) (hc : 0 < p.c)
    (hγ : 0 < p.γ j) :
    (scPrior p).IsUpdatefulChoice (askT K j) false ∧
      ¬ (scPrior p).IsUpdatefulChoice (askT K j) true := by
  have hd := homeEU_diff p j hq hw
  have hneg : -p.c * p.γ j < 0 := by nlinarith
  refine ⟨fun b => ?_, fun h => ?_⟩
  · cases b
    · exact le_rfl
    · linarith
  · have := h false; linarith

/-! ## The updateful policy exists on the model (the witness for `IsUpdatefulPolicy`) -/

/-- **At a table that no round reads (`Rec_k`, `Other`) the home-branch value is action-blind**:
the policy law is a product and the utility reads only the `Ask` points, so the action at `Q`
moves nothing inside `Q`'s own branch.
Source: none: infrastructure (audit r1 B1, probe `T5UpdatefulWitness`)
Kind: L
Fidelity: n/a -/
lemma homeEU_actionBlind (Q : ↥(iterTables K)) (hQ : ∀ j, askT K j ≠ Q) (a a' : Bool) :
    (scPrior p).homeEU Q a = (scPrior p).homeEU Q a' := by
  unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU scPrior
  have hev : ∀ b : Bool, ∀ ω : (scData p).Ω₀ × Policy (iterTables K) Bool,
      ((scData p).toPrior.state ω = Q ∧ (scData p).toPrior.pp ω Q = b) ↔
      (baseState ω.1 = Q ∧ ω.2 Q = b) := fun _ _ => Iff.rfl
  have h1 := (condExp_congr _ _ (hev a)).trans
    (IndepCalc.condExp_base_point (scData p) (fun ω₀ : Base K => baseState ω₀ = Q) Q a)
  have h2 := (condExp_congr _ _ (hev a')).trans
    (IndepCalc.condExp_base_point (scData p) (fun ω₀ : Base K => baseState ω₀ = Q) Q a')
  refine h1.trans (Eq.trans ?_ h2.symm)
  simp only [inner_sum, SingleCoin.massOf_point, hQ, if_false]

/-- **`refuseAll` is an updateful policy on `scPrior p`** (`0 < q`, `0 < c`, `γ > 0`, `w > 0` at
every round): at every `Ask_j` the updateful choice is `refuse` (`isUpdatefulChoice_refuse`), and
at `Rec_k` and `Other` every action is an updateful choice because the home value is action-blind
(`homeEU_actionBlind`). This inhabits the hypothesis package `IsUpdatefulPolicy πu` of
`updateful_strictly_beaten` — a universally quantified theorem is not its own witness. Why a
*constant* policy is an N+ here (audit r2 fidelity N6): on this model every updateful policy
agrees with `refuseAll` at every `Ask_j` (the updateful choice there is *uniquely* `refuse`) and
may differ only at `Rec_k`/`Other`, which no round reads; so `refuseAll` is the canonical
updateful policy, not a degenerate pick, and every updateful policy shares its `valueUnder`. The
`Rec_k`/`Other` conjuncts are ties — genuine where the cell is positive (`homeEU_actionBlind` is an
equality), junk `0 = 0` where it is null (at `q = 1`), harmless either way (audit r2 adversarial
N7).
Source: bli-paper-2-009 b.278 ("correct updateful behavior" on the single coin); mandate T5
(N+); audit r1 B1
Kind: N+
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `∀ j, 0 < w j` (the witness needs positive mass at every
round; the headline needs it at one); does not use faith -/
theorem isUpdatefulPolicy_refuseAll (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hw : ∀ j, 0 < p.w j) : (scPrior p).IsUpdatefulPolicy refuseAll := by
  intro T
  obtain ⟨s, rfl⟩ := st_surjective K T
  rcases s with _ | ⟨b, j⟩
  · intro b'
    exact le_of_eq (homeEU_actionBlind p (st K none) (fun j => askT_ne_otherT j) b' _)
  · cases b
    · intro b'
      exact le_of_eq
        (homeEU_actionBlind p (st K (some (false, j))) (fun k => askT_ne_recT k j) b' _)
    · exact (isUpdatefulChoice_refuse p j hq (hw j) hc (hγ j)).1

/-! ## Calibrated: prior-optimal beats updateful -/

/-- **Prior-optimality is "weakly beats every policy"**, in particular every updateful one — the
first reading of "correct UDT behavior is a superset of correct updateful behavior" under
calibration, which is the definition of prior-optimality (hence Kind `T`; the content is in the
strict instance below).
Source: bli-paper-2-009 b.278 ("Assuming calibration, correct UDT behavior is a strict superset
of correct updateful behavior"); mandate T5 (a)
Kind: T
Fidelity: exact (the external criterion at `q' = q` is the frozen prior's value)
Hyps: (a) none beyond `IsPriorOptimal π*`; does not use faith -/
theorem priorOptimal_beats (πs : Policy (iterTables K) Bool) (h : (scPrior p).IsPriorOptimal πs)
    (π : Policy (iterTables K) Bool) :
    valueUnder p p.q p.hq0 p.hq1 π ≤ valueUnder p p.q p.hq0 p.hq1 πs := by
  rw [valueUnder_self, valueUnder_self]; exact h π

/-- A policy refusing at `Ask_j` has `roundSum + γ_j ≤ ∑ γ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_add_le_of_refuse (hγ : ∀ k, 0 ≤ p.γ k) (j : Fin K) (π : Policy (iterTables K) Bool)
    (h : π (askT K j) = false) : roundSum p.γ π + p.γ j ≤ ∑ k, p.γ k := by
  have e : ∑ k, p.γ k - roundSum p.γ π = ∑ k, p.γ k * (1 - ind (π (askT K k))) := by
    unfold roundSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _; ring
  have hle : p.γ j * (1 - ind (π (askT K j))) ≤ ∑ k, p.γ k * (1 - ind (π (askT K k))) :=
    Finset.single_le_sum (f := fun k => p.γ k * (1 - ind (π (askT K k))))
      (fun k _ => mul_nonneg (hγ k) (by linarith [ind_le_one (π (askT K k))])) (Finset.mem_univ j)
  rw [h, ind_false] at hle
  linarith

/-- **The strict instance under calibration**: for `gain > 0`, every updateful policy (updateful
choice at every table) refuses at `Ask_j` and loses at least `gain · γ_j > 0` against the
prior-optimal `payAll`, under the frozen (= true) law.
Source: bli-paper-2-009 b.278 ("strict superset"); bli-paper-2-009 b.283 ("iterated mugging with
a single coin" as the example); mandate T5 (a) ("strict when `gain > 0`")
Kind: C (`isUpdatefulChoice_refuse`, `roundSum_add_le_of_refuse`, `exAnteValue_eq`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < w_j`, `0 < c`, `0 < γ`, `0 < gain`; does not use faith -/
theorem updateful_strictly_beaten (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hg : 0 < gain p) (j : Fin K) (hw : 0 < p.w j) (πu : Policy (iterTables K) Bool)
    (hu : (scPrior p).IsUpdatefulPolicy πu) :
    πu (askT K j) = false ∧
      gain p * p.γ j ≤ valueUnder p p.q p.hq0 p.hq1 payAll - valueUnder p p.q p.hq0 p.hq1 πu ∧
      valueUnder p p.q p.hq0 p.hq1 πu < valueUnder p p.q p.hq0 p.hq1 payAll := by
  have href : πu (askT K j) = false := by
    obtain ⟨_, h2⟩ := isUpdatefulChoice_refuse p j hq hw hc (hγ j)
    cases h : πu (askT K j)
    · rfl
    · exact absurd (h ▸ hu (askT K j)) h2
  have hr := roundSum_add_le_of_refuse p (fun k => (hγ k).le) j πu href
  rw [valueUnder_self, valueUnder_self, exAnteValue_eq, exAnteValue_eq, roundSum_payAll]
  refine ⟨href, ?_, ?_⟩ <;> nlinarith [hγ j]

/-- **N+ for `updateful_strictly_beaten`**: its full hypothesis package is inhabited by
`refuseAll` (`isUpdatefulPolicy_refuseAll`), and the conclusion then fires: the updateful
`refuseAll` is strictly beaten by `payAll` under the calibrated law, by at least `gain · ∑ γ > 0`
(every round, not only one).
Source: bli-paper-2-009 b.278, b.283; mandate T5 (N+); audit r1 B1
Kind: N+
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`, `∀ j, 0 < w j`, `0 < K`; does not use faith -/
theorem updateful_strictly_beaten_refuseAll (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hg : 0 < gain p) (hw : ∀ j, 0 < p.w j) (hK : 0 < K) :
    (scPrior p).IsUpdatefulPolicy refuseAll ∧
      gain p * ∑ k, p.γ k ≤ valueUnder p p.q p.hq0 p.hq1 payAll - valueUnder p p.q p.hq0 p.hq1 refuseAll ∧
      valueUnder p p.q p.hq0 p.hq1 refuseAll < valueUnder p p.q p.hq0 p.hq1 payAll := by
  have hs : 0 < ∑ k, p.γ k := by rw [← tailSum_zero]; exact tailSum_pos p hγ 0 hK
  refine ⟨isUpdatefulPolicy_refuseAll p hq hc hγ hw, ?_, ?_⟩ <;>
    rw [valueUnder_self, valueUnder_self, exAnteValue_eq, exAnteValue_eq, roundSum_payAll,
      roundSum_refuseAll] <;> nlinarith

/-- **Tie-aware "superset", for every policy**: any policy's value under the calibrated law is at
most the prior-optimal value, with equality iff that policy is itself prior-optimal (the maximizer
sets, not the policies, are compared; ties are allowed, `udt-bli-tiling` F5). Stated for every
`π`: the statement carries no `IsUpdatefulPolicy` hypothesis, which it would not use (audit r2
fidelity N2 — the old name `updateful_le_priorOptimal_iff` promised one); read at an updateful
`π` (`isUpdatefulPolicy_refuseAll`) it is the tie-aware form of b.278's superset claim.
Source: bli-paper-2-009 b.278, read tie-aware; mandate T5 (a) ("read tie-aware (maximizer sets)")
Kind: L
Fidelity: exact (general: every policy)
Hyps: (a) `IsPriorOptimal π*`; does not use faith -/
theorem le_priorOptimal_iff (πs : Policy (iterTables K) Bool)
    (h : (scPrior p).IsPriorOptimal πs) (πu : Policy (iterTables K) Bool) :
    valueUnder p p.q p.hq0 p.hq1 πu ≤ valueUnder p p.q p.hq0 p.hq1 πs ∧
      (valueUnder p p.q p.hq0 p.hq1 πu = valueUnder p p.q p.hq0 p.hq1 πs ↔
        (scPrior p).IsPriorOptimal πu) := by
  refine ⟨priorOptimal_beats p πs h πu, ?_⟩
  rw [valueUnder_self, valueUnder_self]
  constructor
  · intro he π'; rw [he]; exact h π'
  · intro hu; exact le_antisymm (h πu) (hu πs)

/-! ## Uncalibrated: the full Venn diagram -/

/-- **Under the true law "coin true" (`q' = 1`) the updateful `refuseAll` beats the prior-optimal
`payAll`**: `valueUnder 1 payAll = −c ∑γ + r₀ true < r₀ true = valueUnder 1 refuseAll`.
Source: bli-paper-2-009 b.279–280 ("drop calibration … the full Venn diagram"; "UDT risks caring
about a totally non-real branch of possibility, and sacrificing utility in the real branch");
mandate T5 (b)
Kind: P
Fidelity: exact
Hyps: (a) `0 < c`, `0 < γ`, `0 < K`; does not use faith -/
theorem venn_coin_true (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (hK : 0 < K) :
    valueUnder p 1 zero_le_one le_rfl payAll = -p.c * ∑ k, p.γ k + p.r₀ true ∧
    valueUnder p 1 zero_le_one le_rfl refuseAll = p.r₀ true ∧
    valueUnder p 1 zero_le_one le_rfl payAll < valueUnder p 1 zero_le_one le_rfl refuseAll := by
  have hs : 0 < ∑ k, p.γ k := by rw [← tailSum_zero]; exact tailSum_pos p hγ 0 hK
  rw [valueUnder_eq, valueUnder_eq, roundSum_payAll, roundSum_refuseAll]
  refine ⟨by ring, by ring, ?_⟩
  nlinarith

/-- **Under the true law "coin false" (`q' = 0`) the prior-optimal `payAll` beats the updateful
`refuseAll`**: `valueUnder 0 refuseAll = r₀ false < V ∑γ + r₀ false = valueUnder 0 payAll`.
Source: bli-paper-2-009 b.279–280; mandate T5 (b)
Kind: P
Fidelity: exact
Hyps: (a) `0 < V`, `0 < γ`, `0 < K`; does not use faith -/
theorem venn_coin_false (hV : 0 < p.V) (hγ : ∀ k, 0 < p.γ k) (hK : 0 < K) :
    valueUnder p 0 le_rfl zero_le_one payAll = p.V * ∑ k, p.γ k + p.r₀ false ∧
    valueUnder p 0 le_rfl zero_le_one refuseAll = p.r₀ false ∧
    valueUnder p 0 le_rfl zero_le_one refuseAll < valueUnder p 0 le_rfl zero_le_one payAll := by
  have hs : 0 < ∑ k, p.γ k := by rw [← tailSum_zero]; exact tailSum_pos p hγ 0 hK
  rw [valueUnder_eq, valueUnder_eq, roundSum_payAll, roundSum_refuseAll]
  refine ⟨by ring, by ring, ?_⟩
  nlinarith

/-- **The full Venn diagram** (`gain > 0`): the prior-optimal `payAll` is strictly more correct
than `refuseAll` under the calibrated law `q' = q` and under `q' = 0`, strictly less correct under
`q' = 1` — "one or the other can be more correct" once calibration is dropped, and both are
positive-mass policies under every law (`NDPOLICY` for every `q'`). `refuseAll` is *the* updateful
policy of the model by `isUpdatefulPolicy_refuseAll` (which needs `0 < q` and `∀ j, 0 < w j`, not
hypotheses of this theorem, whose inequalities hold regardless).
Source: bli-paper-2-009 b.278–280; bli-soto-b-051 (journal 2023-09-27 ll. 95–97: "calibrated"
means "objectively correct"); mandate T5 (b)
Kind: C (`venn_coin_true`, `venn_coin_false`, `structure_facts`)
Fidelity: exact (the first reading of "calibrated"; the reference-class notion not formalized)
Hyps: (a) `0 < c`, `0 < V`, `0 < γ`, `0 < gain`, `0 < K`; does not use faith -/
theorem venn_diagram (hc : 0 < p.c) (hV : 0 < p.V) (hγ : ∀ k, 0 < p.γ k)
    (hg : 0 < gain p) (hK : 0 < K) :
    valueUnder p p.q p.hq0 p.hq1 refuseAll < valueUnder p p.q p.hq0 p.hq1 payAll ∧
    valueUnder p 0 le_rfl zero_le_one refuseAll < valueUnder p 0 le_rfl zero_le_one payAll ∧
    valueUnder p 1 zero_le_one le_rfl payAll < valueUnder p 1 zero_le_one le_rfl refuseAll ∧
    (∀ q' (h0 : 0 ≤ q') (h1 : q' ≤ 1), (scPrior (withQ p q' h0 h1)).NDPOLICY) := by
  refine ⟨?_, (venn_coin_false p hV hγ hK).2.2, (venn_coin_true p hc hγ hK).2.2,
    fun q' h0 h1 => (structure_facts (withQ p q' h0 h1)).1⟩
  have hs : 0 < ∑ k, p.γ k := by rw [← tailSum_zero]; exact tailSum_pos p hγ 0 hK
  rw [valueUnder_eq, valueUnder_eq, roundSum_payAll, roundSum_refuseAll]
  have : gain p = p.V * (1 - p.q) - p.c * p.q := rfl
  nlinarith

end Cleanroom.Bli.UdtBliLearning
