import Cleanroom.Udt.UdtInfluence101.Atoms
import Mathlib.Data.Finset.Lattice.Fold

/-!
# `Cleanroom.Udt.UdtInfluence101.Deferral`: the value of deferral (Post 4)

Target T13 of [[udt-influence-101-mandate]]. Over a finite prior and two partitions `G ≤ H`
(`H` refines `G`):

* **the classical inequality** `𝔼[max_a 𝔼[U_a | H] | G] ≥ max_a 𝔼[U_a | G]` on the support
  (Jensen for `max` plus the tower property, `defer_ge_now`);
* **the decision form**: if committing now to `a` is worth no more than `a`'s expected utility under
  the undisturbed prior — Post 4's "most critical and dubious assumption" — then the best commitment
  is worth at most the value of deferring (`defer_ge_commit`);
* **the failure witness**: a chicken-like game where the opponent yields iff it sees a commitment to
  `dare`: committing now is worth `1`, deferring `0` (`chicken_commit_beats_defer`);
* **a strict-gain witness**: with a coin the deferring agent sees, deferring strictly beats every
  commitment (`coin_defer_strict`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc

namespace Deferral

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The cell of `ω` in the partition induced by the map `H`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def cell {J : Type} [DecidableEq J] (H : Ω → J) (ω : Ω) : Finset Ω := event (fun ω' => H ω' = H ω)

/-- **Conditional expectation given a partition** (junk `0` on null cells): `𝔼_μ[f | H](ω)`.
Source: `references/udt101/04-essential-miscellanea.md` ll. 27–44 ("what future me thinks"); mandate T13
Kind: D
Fidelity: exact (finite form, junk `0` disclosed)
Hyps: n/a -/
def condExpPart {J : Type} [DecidableEq J] (μ : FinDist Ω) (f : Ω → ℝ) (H : Ω → J) (ω : Ω) : ℝ :=
  condExpJunk μ.w f (cell H ω) 0

/-- `H` refines `G`: the cells of `H` are contained in the cells of `G`.
Source: mandate T13 ("two partitions `G ≤ H`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Refines {I J : Type} (G : Ω → I) (H : Ω → J) : Prop := ∀ ω ω', H ω = H ω' → G ω = G ω'

/-- Supporting lemma `mem_cell`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_cell {J : Type} [DecidableEq J] {H : Ω → J} {ω ω' : Ω} :
    ω' ∈ cell H ω ↔ H ω' = H ω := by simp [cell]

/-- Supporting lemma `cell_eq_of_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cell_eq_of_mem {J : Type} [DecidableEq J] {H : Ω → J} {ω ω' : Ω} (h : ω' ∈ cell H ω) :
    cell H ω' = cell H ω := by
  ext ω''
  simp only [mem_cell] at h ⊢
  rw [h]

/-- **The tower property for partitions**: `𝔼[𝔼[f | H] | G] = 𝔼[f | G]` at a world of positive mass,
when `H` refines `G`.
Source: `references/udt101/04-essential-miscellanea.md` l. 37 ("the laws of iterated expectations")
Kind: P
Fidelity: exact (finite form; Post 4 has it "in the limit" for logical inductors)
Hyps: none -/
theorem condExpPart_condExpPart {I J : Type} [DecidableEq I] [DecidableEq J] (μ : FinDist Ω)
    (f : Ω → ℝ) {G : Ω → I} {H : Ω → J} (hGH : Refines G H) (ω : Ω) :
    condExpPart μ (fun ω' => condExpPart μ f H ω') G ω = condExpPart μ f G ω := by
  unfold condExpPart
  simp only [condExpJunk_eq_div]
  congr 1
  -- regroup the inner sums over `H`-cells inside the `G`-cell
  have hinner : ∀ ω' ∈ cell G ω, μ.w ω' * ((∑ ω'' ∈ cell H ω', μ.w ω'' * f ω'') / mass μ.w (cell H ω')) =
      ∑ ω'' ∈ cell G ω, if H ω'' = H ω' then μ.w ω' * (μ.w ω'' * f ω'' / mass μ.w (cell H ω'')) else 0 := by
    intro ω' hω'
    have hset : (cell G ω).filter (fun ω'' => H ω'' = H ω') = cell H ω' := by
      ext ω''
      simp only [Finset.mem_filter, mem_cell]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨(hGH _ _ h).trans (mem_cell.1 hω'), h⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hset, div_eq_mul_inv, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω'' hω'' => ?_
    rw [cell_eq_of_mem hω'', div_eq_mul_inv]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω'' hω'' => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hset : (cell G ω).filter (fun ω' => H ω'' = H ω') = cell H ω'' := by
    ext ω'
    simp only [Finset.mem_filter, mem_cell]
    constructor
    · exact fun h => h.2.symm
    · intro h
      exact ⟨(hGH _ _ h).trans (mem_cell.1 hω''), h.symm⟩
  rw [hset, ← Finset.sum_mul]
  have hm : (∑ ω' ∈ cell H ω'', μ.w ω') = mass μ.w (cell H ω'') := rfl
  rw [hm]
  by_cases h0 : mass μ.w (cell H ω'') = 0
  · have : μ.w ω'' = 0 := weight_eq_zero_of_mass_eq_zero μ.nonneg h0 (mem_cell.2 rfl)
    rw [this]; ring
  · field_simp

/-- Supporting lemma `condExpPart_mono` (monotone in the integrand, on positive-mass worlds).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpPart_mono {I : Type} [DecidableEq I] (μ : FinDist Ω) {f g : Ω → ℝ} (G : Ω → I) (ω : Ω)
    (hfg : ∀ ω' ∈ cell G ω, 0 < μ.w ω' → f ω' ≤ g ω') :
    condExpPart μ f G ω ≤ condExpPart μ g G ω := by
  unfold condExpPart
  simp only [condExpJunk_eq_div]
  refine div_le_div_of_nonneg_right ?_ (mass_nonneg μ.nonneg _)
  refine Finset.sum_le_sum fun ω' hω' => ?_
  rcases (μ.nonneg ω').lt_or_eq with h0 | h0
  · exact mul_le_mul_of_nonneg_left (hfg ω' hω' h0) h0.le
  · rw [← h0, zero_mul, zero_mul]

variable {Act : Type} [Fintype Act] [Nonempty Act]

/-- **The value of deferral (classical inequality)**: at any world, with `H` refining `G`,
`𝔼[max_a 𝔼[U_a | H] | G] ≥ max_a 𝔼[U_a | G]` — the expectation of the finer-information maximum
dominates the coarser-information maximum (Jensen for `max`, then the tower property).
Source: `references/udt101/04-essential-miscellanea.md` ll. 29–37 (udt-rep-2-022); mandate T13(i)
Kind: P
Fidelity: exact (finite form of Post 4's "what I think(max_{A'} what future me thinks of A') ≥ max_A what I think of A")
Hyps: (a) none (`H` refines `G`) -/
theorem defer_ge_now {I J : Type} [DecidableEq I] [DecidableEq J] (μ : FinDist Ω) (U : Act → Ω → ℝ)
    {G : Ω → I} {H : Ω → J} (hGH : Refines G H) (ω : Ω) :
    (univ : Finset Act).sup' univ_nonempty (fun a => condExpPart μ (U a) G ω) ≤
      condExpPart μ (fun ω' => (univ : Finset Act).sup' univ_nonempty (fun a => condExpPart μ (U a) H ω')) G ω := by
  refine Finset.sup'_le _ _ fun a _ => ?_
  rw [← condExpPart_condExpPart μ (U a) hGH ω]
  exact condExpPart_mono μ G ω fun ω' _ _ => Finset.le_sup' (fun a => condExpPart μ (U a) H ω') (Finset.mem_univ a)

/-- **The value of deciding now** under commitment to `a`: the expected utility of `a` under the law
`ℙ_a` that commitment induces (which may differ from the undisturbed prior).
Source: `references/udt101/04-essential-miscellanea.md` l. 41 ("expected utility of me deciding now to play action A"); mandate T13(ii)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Dnow (ℙa : Act → FinDist Ω) (U : Act → Ω → ℝ) (a : Act) : ℝ := (ℙa a).exp (U a)

/-- **The value of deferring**: the expected (under the prior) finer-information maximum.
Source: `references/udt101/04-essential-miscellanea.md` l. 41 ("expected score of me deferring so future-me makes the decision later")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Ddefer {J : Type} [DecidableEq J] (μ : FinDist Ω) (U : Act → Ω → ℝ) (H : Ω → J) : ℝ :=
  μ.exp (fun ω => (univ : Finset Act).sup' univ_nonempty (fun a => condExpPart μ (U a) H ω))

/-- Supporting lemma `exp_condExpPart` (the law of total expectation: `𝔼[𝔼[f | H]] = 𝔼[f]`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem exp_condExpPart {J : Type} [DecidableEq J] (μ : FinDist Ω) (f : Ω → ℝ) (H : Ω → J) :
    μ.exp (fun ω => condExpPart μ f H ω) = μ.exp f := by
  rcases isEmpty_or_nonempty Ω with hE | ⟨⟨ω₀⟩⟩
  · simp [FinDist.exp]
  · have key := condExpPart_condExpPart μ f (G := fun _ : Ω => ()) (H := H) (fun _ _ _ => rfl) ω₀
    have hcell : cell (fun _ : Ω => ()) ω₀ = univ := by ext; simp [cell]
    have hmass : mass μ.w univ = 1 := μ.sum_one
    unfold condExpPart at key
    rw [hcell, condExpJunk_of_pos (by rw [hmass]; exact one_pos),
      condExpJunk_of_pos (by rw [hmass]; exact one_pos), hmass, div_one, div_one] at key
    exact key

/-- Supporting lemma `exp_mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem exp_mono (μ : FinDist Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : μ.exp f ≤ μ.exp g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

/-- **Deferring is worth at least the best commitment, under Post 4's assumption**: if committing
now to any action `a` is worth no more than `a`'s expected utility under the undisturbed prior
("the most critical and dubious assumption": the commitment itself changes nothing the agent
cares about), then `max_a Dnow(a) ≤ Ddefer`.
Source: `references/udt101/04-essential-miscellanea.md` ll. 39–42 (udt-rep-2-022); mandate T13(ii)
Kind: P
Fidelity: exact
Hyps: (b)/(c) the commitment assumption `∀ a, Dnow a ≤ 𝔼_ℙ[U_a]`, a modelling assumption about
commitment power taken as the source states it -/
theorem defer_ge_commit {J : Type} [DecidableEq J] (μ : FinDist Ω) (ℙa : Act → FinDist Ω)
    (U : Act → Ω → ℝ) (H : Ω → J) (hyp : ∀ a, Dnow ℙa U a ≤ μ.exp (U a)) :
    (univ : Finset Act).sup' univ_nonempty (Dnow ℙa U) ≤ Ddefer μ U H := by
  refine Finset.sup'_le _ _ fun a _ => (hyp a).trans ?_
  rw [← exp_condExpPart μ (U a) H]
  exact exp_mono μ fun ω => Finset.le_sup' (fun a => condExpPart μ (U a) H ω) (Finset.mem_univ a)

/-! ### Witnesses -/

/-- Supporting lemma `sup'_bool`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sup'_bool (f : Bool → ℝ) :
    (univ : Finset Bool).sup' univ_nonempty f = max (f true) (f false) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun b _ => by cases b <;> simp
  · exact max_le (Finset.le_sup' f (Finset.mem_univ true)) (Finset.le_sup' f (Finset.mem_univ false))

/-- The prior of the chicken game: a fair coin (irrelevant, seen by the deferring agent) and an
opponent who dares (`yields = false`) unless it sees a commitment.
Source: mandate T13(iii)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chickenPrior : FinDist (Bool × Bool) where
  w ω := if ω.2 then 0 else 1 / 2
  nonneg ω := by split_ifs <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type]

/-- The law under commitment to `dare`: the opponent yields.
Source: mandate T13(iii)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chickenDare : FinDist (Bool × Bool) where
  w ω := if ω.2 then 1 / 2 else 0
  nonneg ω := by split_ifs <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type]

/-- The commitment laws: `dare = true` makes the opponent yield; `yield = false` changes nothing.
Source: mandate T13(iii)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chickenLaw (a : Bool) : FinDist (Bool × Bool) := if a then chickenDare else chickenPrior

/-- The chicken payoffs: `(dare, yield) = 1`, `(dare, dare) = −10`, `(yield, ·) = 0`.
Source: mandate T13(iii)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chickenU (a : Bool) (ω : Bool × Bool) : ℝ := if a then (if ω.2 then 1 else -10) else 0

/-- Supporting lemma `condExpPart_fst_chicken` (the finer-information conditional values).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpPart_chicken (a : Bool) (ω : Bool × Bool) :
    condExpPart chickenPrior (chickenU a) Prod.fst ω = if a then -10 else 0 := by
  unfold condExpPart cell
  rw [condExpJunk_eq_div]
  have hcell : (event fun ω' : Bool × Bool => ω'.1 = ω.1) = {(ω.1, true), (ω.1, false)} := by
    ext ω'
    simp only [mem_event, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    cases ω'.2 <;> simp
  rw [hcell]
  cases a <;> norm_num [mass, chickenPrior, chickenU]

/-- **Committing now can beat deferring** (the failure of Post 4's assumption): in the chicken game,
`Dnow(dare) = 1` while `Ddefer = 0`; the assumption fails for `dare` (`1 > 𝔼_ℙ[U_dare] = −10`).
The deferring agent's partition is the coin, so the `max` is exercised.
Source: `references/udt101/04-essential-miscellanea.md` l. 43 ("a kinda dumb opponent who can see commitments you make now"); mandate T13(iii)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem chicken_commit_beats_defer :
    Ddefer chickenPrior chickenU Prod.fst < (univ : Finset Bool).sup' univ_nonempty (Dnow chickenLaw chickenU) ∧
      ¬ (Dnow chickenLaw chickenU true ≤ chickenPrior.exp (chickenU true)) := by
  have hD : Ddefer chickenPrior chickenU Prod.fst = 0 := by
    unfold Ddefer
    simp only [sup'_bool, condExpPart_chicken]
    norm_num [FinDist.exp, Fintype.sum_prod_type, chickenPrior]
  have hnow : Dnow chickenLaw chickenU true = 1 := by
    norm_num [Dnow, chickenLaw, chickenDare, chickenU, FinDist.exp, Fintype.sum_prod_type]
  have hnow' : Dnow chickenLaw chickenU false = 0 := by
    norm_num [Dnow, chickenLaw, chickenU, FinDist.exp]
  have hexp : chickenPrior.exp (chickenU true) = -10 := by
    norm_num [FinDist.exp, Fintype.sum_prod_type, chickenPrior, chickenU]
  refine ⟨?_, ?_⟩
  · rw [hD, sup'_bool, hnow, hnow']; norm_num
  · rw [hnow, hexp]; norm_num

/-- The coin game: the deferring agent sees a fair coin and must match it; commitment changes
nothing.
Source: mandate T13(iv)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def coinU (a : Bool) (ω : Bool) : ℝ := if a = ω then 1 else 0

/-- The fair coin as a finite distribution.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def fairCoin : FinDist Bool := FinDist.halfHalf true false

/-- Supporting lemma `fairCoin_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem fairCoin_w (b : Bool) : fairCoin.w b = 1 / 2 := by
  cases b <;> norm_num [fairCoin, FinDist.halfHalf, FinDist.bern_w]

/-- **Deferring can strictly beat every commitment while Post 4's assumption holds**: matching a
coin the deferring agent sees is worth `1` deferred and `1/2` committed, and commitment changes
nothing (`ℙ_a = ℙ`), so the assumption holds with equality.
Source: mandate T13(iv)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem coin_defer_strict :
    (∀ a, Dnow (fun _ => fairCoin) coinU a ≤ fairCoin.exp (coinU a)) ∧
      (univ : Finset Bool).sup' univ_nonempty (Dnow (fun _ => fairCoin) coinU) <
        Ddefer fairCoin coinU id := by
  have hcell : ∀ ω : Bool, cell (id : Bool → Bool) ω = {ω} := fun ω => by ext; simp [cell]
  have hc : ∀ a ω, condExpPart fairCoin (coinU a) id ω = coinU a ω := by
    intro a ω
    unfold condExpPart
    rw [hcell, condExpJunk_of_pos (by simp [mass])]
    simp only [Finset.sum_singleton, mass, fairCoin_w]
    ring
  refine ⟨fun a => le_rfl, ?_⟩
  have hnow : ∀ a, Dnow (fun _ => fairCoin) coinU a = 1 / 2 := by
    intro a; cases a <;> norm_num [Dnow, FinDist.exp, coinU]
  have hD : Ddefer fairCoin coinU id = 1 := by
    unfold Ddefer
    simp only [sup'_bool, hc]
    norm_num [FinDist.exp, coinU]
  rw [hD, sup'_bool, hnow, hnow]
  norm_num

end Deferral

end

end Cleanroom.Udt.UdtInfluence101
