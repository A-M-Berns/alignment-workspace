import Cleanroom.Decision.DpCausalConsist.Witness3

/-!
# `dp-causal-consist`: the (S1) tree (T3(A)), the pairwise-independence refutation, the proviso's N−

* **The (S1) tree** `s1TreeS1` (`κ ℓ m = γ_ℓ`, no direct effect) pushes to `s1P`, under which the
  act is *jointly* independent of `(ℓ, k)` (`s1P_jointIndep`), so `thm3_iii` gives the collapse
  for **every** structure for `s1P` (`s1_collapse_all`, T3(A)) — the wiki's "16 of 16" without
  an enumeration. `P(k | m) = 21/200` for both acts (`s1P_k_given`).
* **The noisy-XOR tree** `xorTree` (`ℓ ∼ Bern(1/2)`, `k ∼ Bern(4/5)` if `ℓ ≠ m`, `Bern(1/5)` if
  `ℓ = m`) refutes the wiki's *pairwise* reading of (iii): it records, `m ⊥ ℓ` and `m ⊥ k`
  each hold, but `m` is not independent of `(ℓ, k)`; the complete DAG `ℓ → k, ℓ → m, k → m`
  is compatible, and its truncated law differs from the act-conditional on the positive-mass event
  `{ℓ = 0, k = 1}` (`1/4` vs `2/5`). Finding §6.2: the hypothesis (iii) needs is joint.
* **The proviso of (iv) is needed** (`tcdt_not_tedt_of_null_argmax`): at the deterministic label
  `C(d) = δ_1` on the direct-effect tree with payoff `u = 1[m = 0]`, every hypothesis of `thm3_iv`
  but the proviso holds, `T_EDT` holds (the only positive act is the only act played) and `T_CDT`
  fails: the null act's CPD-filled value `1` tops the played act's `0`. Grade N−: a deterministic
  label (the R1 vacuity regime), which is exactly the regime the proviso is about.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

/-! ## The (S1) tree and joint independence -/

/-- `κ ℓ m = γ_ℓ` at `γ = (1/20, 3/5)`. Source: mandate T2 witness. Kind: D -/
def s1RateQ (ℓ _ : Bool) : ℚ := if ℓ then 3/5 else 1/20

/-- `0 ≤ s1RateQ`. Source: none: infrastructure. Kind: L -/
theorem s1RateQ_nonneg (ℓ m : Bool) : 0 ≤ s1RateQ ℓ m := by cases ℓ <;> norm_num [s1RateQ]

/-- `s1RateQ ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem s1RateQ_le_one (ℓ m : Bool) : s1RateQ ℓ m ≤ 1 := by cases ℓ <;> norm_num [s1RateQ]

/-- **The (S1) recorded tree** at `ρ = 1/10`, `γ = (1/20, 3/5)`.
Source: [[decision-problems-v2]] §7.3 (S1); mandate T2 witness (`s1Tree`)
Kind: D -/
def s1TreeS1 (u : W3 → ℚ) : Tree W3 Unit (fun _ => Bool) ℚ :=
  s1Fam (1/10) (by norm_num) (by norm_num) s1RateQ s1RateQ_nonneg s1RateQ_le_one u

/-- Its calibrated state at label `1/2`. Source: mandate T2 witness. Kind: D -/
def s1StateS1 (u : W3 → ℚ) : State W3 ℚ :=
  s1State (1/10) (by norm_num) (by norm_num) s1RateQ s1RateQ_nonneg s1RateQ_le_one u procHalf

/-- The mass table of the (S1) law. Source: mandate T2 witness. Kind: D -/
noncomputable def s1Mass (ℓ m k : Bool) : ℝ :=
  (if ℓ then 1/10 else 9/10) * (1/2) * (if k then (if ℓ then 3/5 else 1/20) else 1 - (if ℓ then 3/5 else 1/20))

/-- **The (S1) law** on `W3`. Source: mandate T2 witness, T3(A). Kind: D -/
noncomputable def s1P : Distr W3 :=
  distr3 s1Mass (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num [s1Mass])
    (by norm_num [s1Mass])

/-- The bridge for the (S1) tree. Source: mandate §3.3. Kind: L -/
theorem s1TreeS1_toDistr (u : W3 → ℚ) : State.toDistr (State.castℝ (s1StateS1 u)) = s1P := by
  apply Distr.ext
  funext x
  rw [eq_pt3 x]
  simp only [State.toDistr_mass, State.castℝ, FinDistr.castℝ, s1StateS1, s1State_w,
    s1Fam_nu_singleton, s1P, distr3_mass, s1Mass, procHalf, FinDistr.bool, s1RateQ]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> norm_num

/-- `∀ u ≠ 1, x u = y u` on `Fin 3` is agreement at `0` and `2`. Source: none: infrastructure. Kind: L -/
theorem forall_ne_one_iff (x y : W3) : (∀ u : Fin 3, u ≠ 1 → x u = y u) ↔ x 0 = y 0 ∧ x 2 = y 2 := by
  constructor
  · intro h; exact ⟨h 0 (by decide), h 2 (by decide)⟩
  · rintro ⟨h0, h2⟩ u hu
    fin_cases u
    · exact h0
    · exact absurd rfl hu
    · exact h2

/-- **Joint independence of the act on the (S1) law**: `m ⊥ (ℓ, k)`.
Source: [[learning-cdt-renderings]] Theorem 3(iii) ("post-query chance does not read the act, as
under (S1)"); mandate T3(A) ("joint independence of `m` from `(ℓ,k)` holds there: prove it from
the tree")
Kind: N+ -/
theorem s1P_jointIndep : ActJointlyIndep s1P 1 := by
  intro b y
  rw [eq_pt3 y]
  simp only [prob_eq_sum_ite, sum_pt3, Finset.mem_inter, mem_actEvCoord, mem_fiberOff,
    forall_ne_one_iff, pt3_zero, pt3_one, pt3_two]
  cases b <;> cases y 0 <;> cases y 1 <;> cases y 2 <;> norm_num [s1P, s1Mass]

/-- `P(m = b) > 0` under `s1P`. Source: none: infrastructure. Kind: L -/
theorem s1P_m_pos (b : Bool) : 0 < s1P.prob {x | x 1 = b} := by
  rw [prob3_eq]; cases b <;> norm_num [s1P, s1Mass]

/-- **T3(A): the collapse holds for every structure for the (S1) law** — the wiki's "16 of 16
Markov-compatible DAGs", as a theorem over all of them rather than an enumeration.
Source: [[learning-cdt-renderings]] "Checks" ("25 DAGs on `(ℓ, m, k)`, 16 Markov-compatible, and
the identity holds for all 16 — reversed structures included (clause iii)"); mandate T3(A)
Kind: C
Hyps: (a) `Γ.IsFor s1P` -/
theorem s1_collapse_all (Γ : CausalStructure (fun _ : Fin 3 => Bool)) (hΓ : Γ.IsFor s1P) (b : Bool) :
    Γ.truncate 1 b = condDistr s1P {x | x 1 = b} (s1P_m_pos b) :=
  thm3_iii s1P_jointIndep Γ hΓ b (s1P_m_pos b)

/-- `P(k = 1 | m = b) = 21/200` for both acts under `s1P`.
Source: [[learning-cdt-renderings]] "Checks" ("`P(k | m) = 0.105` for both acts"); mandate T2
witness
Kind: N+ -/
theorem s1P_k_given (b : Bool) : s1P.condProb {x | x 2 = true} {x | x 1 = b} = 21/200 := by
  unfold Distr.condProb
  have : ({x : W3 | x 2 = true} ∩ {x | x 1 = b}) = {x | x 2 = true ∧ x 1 = b} := by ext x; simp
  rw [this, prob3_eq, prob3_eq]
  cases b <;> norm_num [s1P, s1Mass]

/-- The structure is not vacuous: `sColl`'s DAG with the (S1) rates is a structure for `s1P`.
Source: mandate T3(A)
Kind: N+ -/
noncomputable def rS1 : Rate3 where
  r v ℓ _ _ := match v with
    | 0 => 1/10
    | 1 => 1/2
    | 2 => if ℓ then 3/5 else 1/20
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num

/-- `gColl` with the (S1) rates is a structure for `s1P` (so `s1_collapse_all` is inhabited).
Source: mandate T3(A)
Kind: N+ -/
theorem sS1_isFor :
    (⟨gColl, isAcyclic_of_rank _ _ gColl_rank, cpdOfRate gColl rS1⟩ :
      CausalStructure (fun _ : Fin 3 => Bool)).IsFor s1P := by
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gColl_parents.1, gColl_parents.2.1, gColl_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [s1P, s1Mass, rS1]

/-! ## The noisy-XOR tree: the pairwise reading of (iii) refuted -/

/-- `κ ℓ m = 4/5` if `ℓ ≠ m`, `1/5` if `ℓ = m`. Source: finding §6.2. Kind: D -/
def xorRateQ (ℓ m : Bool) : ℚ := if ℓ = m then 1/5 else 4/5

/-- `0 ≤ xorRateQ`. Source: none: infrastructure. Kind: L -/
theorem xorRateQ_nonneg (ℓ m : Bool) : 0 ≤ xorRateQ ℓ m := by
  cases ℓ <;> cases m <;> norm_num [xorRateQ]

/-- `xorRateQ ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem xorRateQ_le_one (ℓ m : Bool) : xorRateQ ℓ m ≤ 1 := by
  cases ℓ <;> cases m <;> norm_num [xorRateQ]

/-- **The noisy-XOR tree**: `ℓ ∼ Bern(1/2)`, query `d`, `k ∼ Bern(xorRateQ ℓ m)`. It records for
every procedure (a member of `s1Fam`).
Source: finding §6.2 (mandate §6.2: "exhibit a tree where it fails")
Kind: D -/
def xorTree (u : W3 → ℚ) : Tree W3 Unit (fun _ => Bool) ℚ :=
  s1Fam (1/2) (by norm_num) (by norm_num) xorRateQ xorRateQ_nonneg xorRateQ_le_one u

/-- Its calibrated state at label `1/2`. Source: finding §6.2. Kind: D -/
def xorState (u : W3 → ℚ) : State W3 ℚ :=
  s1State (1/2) (by norm_num) (by norm_num) xorRateQ xorRateQ_nonneg xorRateQ_le_one u procHalf

/-- The mass table of the XOR law. Source: finding §6.2. Kind: D -/
noncomputable def xorMass (ℓ m k : Bool) : ℝ :=
  (1/2) * (1/2) * (if k then (if ℓ = m then 1/5 else 4/5) else 1 - (if ℓ = m then 1/5 else 4/5))

/-- **The XOR law** on `W3`. Source: finding §6.2. Kind: D -/
noncomputable def xorP : Distr W3 :=
  distr3 xorMass (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num [xorMass])
    (by norm_num [xorMass])

/-- The bridge for the XOR tree. Source: mandate §3.3. Kind: L -/
theorem xorTree_toDistr (u : W3 → ℚ) : State.toDistr (State.castℝ (xorState u)) = xorP := by
  apply Distr.ext
  funext x
  rw [eq_pt3 x]
  simp only [State.toDistr_mass, State.castℝ, FinDistr.castℝ, xorState, s1State_w,
    s1Fam_nu_singleton, xorP, distr3_mass, xorMass, procHalf, FinDistr.bool, xorRateQ]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> norm_num

/-- **Pairwise independence holds on the XOR law**: `m ⊥ ℓ` and `m ⊥ k` (each cell).
Source: finding §6.2 (the wiki's hypothesis "`m ⊥ ⟨V₀⟩` … moreover `m ⊥ ⟨V₁⟩`")
Kind: N+ -/
theorem xorP_pairwise :
    (∀ b c : Bool, xorP.prob {x | x 1 = b ∧ x 0 = c} = xorP.prob {x | x 1 = b} * xorP.prob {x | x 0 = c}) ∧
    (∀ b c : Bool, xorP.prob {x | x 1 = b ∧ x 2 = c} = xorP.prob {x | x 1 = b} * xorP.prob {x | x 2 = c}) := by
  constructor <;> intro b c <;> simp only [prob3_eq] <;>
    cases b <;> cases c <;> norm_num [xorP, xorMass]

/-- **Joint independence fails on the XOR law**: `P(m = 1 ∧ ℓ = 0 ∧ k = 1) = 1/5 ≠ 1/8 = P(m = 1) P(ℓ = 0 ∧ k = 1)`.
Source: finding §6.2
Kind: N+ -/
theorem xorP_not_joint :
    xorP.prob {x | x 1 = true ∧ x 0 = false ∧ x 2 = true}
      ≠ xorP.prob {x | x 1 = true} * xorP.prob {x | x 0 = false ∧ x 2 = true} := by
  simp only [prob3_eq]; norm_num [xorP, xorMass]

/-- `P(m = 1) > 0` under `xorP`. Source: none: infrastructure. Kind: L -/
theorem xorP_m1_pos : 0 < xorP.prob {x | x 1 = true} := by
  rw [prob3_eq]; norm_num [xorP, xorMass]

/-- The rate table of the complete DAG `ℓ → k`, `ℓ → m`, `k → m` under the XOR law:
`ℓ ∼ Bern(1/2)`, `k | ℓ ∼ Bern(1/2)`, `m | ℓ, k ∼ Bern(4/5)` if `ℓ ≠ k`, `Bern(1/5)` if `ℓ = k`.
Source: finding §6.2
Kind: D -/
noncomputable def rXor : Rate3 where
  r v ℓ _ k := match v with
    | 0 => 1/2
    | 1 => if ℓ = k then 1/5 else 4/5
    | 2 => 1/2
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num

/-- Parents in `gLKM`. Source: none: infrastructure. Kind: L -/
theorem gLKM_parents : gLKM.parents 0 = ∅ ∧ gLKM.parents 1 = {0, 2} ∧ gLKM.parents 2 = {0} := by
  decide

/-- The complete structure `ℓ → k, ℓ → m, k → m` for the XOR law. Source: finding §6.2. Kind: D -/
noncomputable def sXor : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gLKM, isAcyclic_of_rank _ _ gLKM_rank, cpdOfRate gLKM rXor⟩

/-- `sXor` is a structure for `xorP`. Source: finding §6.2. Kind: N+ -/
theorem sXor_isFor : sXor.IsFor xorP := by
  unfold sXor
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gLKM_parents.1, gLKM_parents.2.1, gLKM_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [xorP, xorMass, rXor]

/-- `ℓ ∈ nondesc(m)` in `gLKM`. Source: none: infrastructure. Kind: L -/
theorem gLKM_ell_nondesc : (0 : Fin 3) ∈ nondesc gLKM 1 :=
  mem_nondesc_of_rank gLKM rankLKM gLKM_rank (by decide) (by decide)

/-- **The pairwise reading of (iii) is refuted**: on the XOR law (pairwise independence,
`xorP_pairwise`), the compatible structure `sXor` has `P^{do(m := 1)}(ℓ = 0 ∧ k = 1) = 1/4` (Pearl's
invariance: both coordinates are non-descendants) while `P(ℓ = 0 ∧ k = 1 | m = 1) = 2/5`, so the
identity fails. The hypothesis Theorem 3(iii) needs is joint independence (`thm3_iii`).
Source: [[learning-cdt-renderings]] Theorem 3(iii) (refuted as printed); finding §6.2
Kind: N+ -/
theorem xor_pairwise_refutes_iii :
    sXor.truncate 1 true ≠ condDistr xorP {x | x 1 = true} xorP_m1_pos := by
  intro h
  have hfix : InFixedAlgebra gLKM 1 (Finset.univ.filter fun x : W3 => x 0 = false ∧ x 2 = true) := by
    intro x y hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hxy 0 gLKM_ell_nondesc, hxy 2 gLKM_k_nondesc]
  have hset : ({x : W3 | x 0 = false ∧ x 2 = true})
      = ↑(Finset.univ.filter fun x : W3 => x 0 = false ∧ x 2 = true) := by ext x; simp
  have h1 : (sXor.truncate 1 true).prob {x | x 0 = false ∧ x 2 = true} = 1/4 := by
    rw [hset, CausalStructure.truncate,
      truncate_prob_eq_of_inFixedAlgebra sXor.acyclic sXor.φ sXor_isFor 1 true _ hfix, ← hset,
      prob3_eq]
    norm_num [xorP, xorMass]
  have h2 : (condDistr xorP {x | x 1 = true} xorP_m1_pos).prob {x | x 0 = false ∧ x 2 = true} = 2/5 := by
    rw [condDistr_prob]
    unfold Distr.condProb
    have : ({x : W3 | x 0 = false ∧ x 2 = true} ∩ {x | x 1 = true})
        = {x | x 0 = false ∧ x 2 = true ∧ x 1 = true} := by ext x; simp [and_assoc]
    rw [this, prob3_eq, prob3_eq]
    norm_num [xorP, xorMass]
  rw [h] at h1
  rw [h1] at h2
  norm_num at h2

/-! ## The proviso of Theorem 3(iv) is needed -/

/-- The deterministic label `C(d) = δ_1`. Source: none: infrastructure. Kind: D -/
def procOne : Proc Unit (fun _ => Bool) ℚ := fun _ => FinDistr.pure true

/-- The payoff `1[m = 0]`: abstaining pays one. Source: mandate T2(iv) (the N− companion). Kind: D -/
def uAbstain : W3 → ℚ := fun x => if x 1 then 0 else 1

/-- The calibrated state of the direct-effect tree at the deterministic label.
Source: mandate T2(iv)
Kind: D -/
def oneState : State W3 ℚ :=
  s1State (1/10) (by norm_num) (by norm_num) dRateQ dRateQ_nonneg dRateQ_le_one uAbstain procOne

/-- The mass table at the deterministic label: `m = 1` always. Source: mandate T2(iv). Kind: D -/
noncomputable def oneMass (ℓ m k : Bool) : ℝ :=
  if m then (if ℓ then 1/10 else 9/10) * (if k then dRate ℓ true else 1 - dRate ℓ true) else 0

/-- The law at the deterministic label. Source: mandate T2(iv). Kind: D -/
noncomputable def oneP : Distr W3 :=
  distr3 oneMass (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num [oneMass, dRate])
    (by norm_num [oneMass, dRate])

/-- The bridge at the deterministic label. Source: mandate §3.3. Kind: L -/
theorem oneState_toDistr : State.toDistr (State.castℝ oneState) = oneP := by
  apply Distr.ext
  funext x
  rw [eq_pt3 x]
  simp only [State.toDistr_mass, State.castℝ, FinDistr.castℝ, oneState, s1State_w,
    s1Fam_nu_singleton, oneP, distr3_mass, oneMass, dRate, procOne, FinDistr.pure_w, dRateQ]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> norm_num

/-- The temporal rate table at the deterministic label: `m ∼ Bern(1)`. Source: mandate T2(iv). Kind: D -/
noncomputable def rOne : Rate3 where
  r v ℓ m _ := match v with
    | 0 => 1/10
    | 1 => 1
    | 2 => dRate ℓ m
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [dRate]
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [dRate]

/-- The collider structure at the deterministic label. Source: mandate T2(iv). Kind: D -/
noncomputable def sOne : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gColl, isAcyclic_of_rank _ _ gColl_rank, cpdOfRate gColl rOne⟩

/-- `sOne` is a structure for `oneP`. Source: mandate T2(iv). Kind: N− -/
theorem sOne_isFor : sOne.IsFor oneP := by
  unfold sOne
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gColl_parents.1, gColl_parents.2.1, gColl_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [oneP, oneMass, dRate, rOne]

/-- The supposed value of an act under `cfG` with a payoff constant on the act event is that
constant.
Source: none: infrastructure
Kind: L -/
theorem cfG_V_act_const (Γ : CausalStructure (fun _ : Fin 3 => Bool)) (u : W3 → ℝ) (b : Bool)
    (v : ℝ) (hu : ∀ x, x 1 = b → u x = v) :
    (cfG Γ 1 u b).V (actEvCoord 1 b) = v := by
  rw [cfG, expState_V]
  have hnum : ∑ x ∈ actEvCoord 1 b, (Γ.truncate 1 b).mass x * u x
      = v * ∑ x ∈ actEvCoord 1 b, (Γ.truncate 1 b).mass x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hu x ((mem_actEvCoord 1 b x).mp hx)]; ring
  have hden : ∑ x ∈ actEvCoord 1 b, (Γ.truncate 1 b).mass x = 1 := by
    rw [sum_mass_eq_prob, coe_actEvCoord]
    exact truncate_prob_act Γ.acyclic Γ.φ 1 b
  rw [hnum, hden]; simp

/-- **The proviso of Theorem 3(iv) is needed** (N−, deterministic label): at `C(d) = δ_1` on the
direct-effect tree with payoff `1[m = 0]`, recording, the strict clauses, Markov compatibility
of `sOne` and the pre-query parent cells all hold, `T_EDT` holds, but the causal argmax over
`A_d` is `{0}` — the null act, filled by the CPD, tops the list — so it misses `A_d^+ = {1}` and
`T_CDT` fails.
Source: [[learning-cdt-renderings]] Theorem 3(iv) ("whenever the causal argmax meets the
positive-probability acts"); mandate T2(iv) (`tcdt_not_tedt_of_null_argmax`)
Kind: N− -/
theorem tcdt_not_tedt_of_null_argmax :
    RecordsFor s1Obs s1ActEv procOne (directTree uAbstain) () ∧
    StrictClausesAt (fun _ => oneState) s1Obs procOne (directTree uAbstain) () ∧
    sOne.IsFor (State.toDistr (State.castℝ oneState)) ∧
    (∀ c, PreQuery s1Obs procOne (directTree uAbstain) () (parentCell sOne 1 c)) ∧
    (argmaxAll (fun a => (cfG sOne 1 (fun x => (uAbstain x : ℝ)) a).V (s1ActEv () a))
      ∩ APlus (fun _ => oneState) s1ActEv () = ∅) ∧
    TEdtAt (fun _ => oneState) s1ActEv procOne () ∧
    ¬ TCdtAt (fun _ => oneState) s1ActEv procOne ()
        (fun a => cfG sOne 1 (fun x => (uAbstain x : ℝ)) a) := by
  have hpr : ∀ b, oneState.pr (actEvCoord 1 b) = if b then 1 else 0 := by
    intro b
    rw [oneState, s1State_pr_act]
    cases b <;> simp [procOne]
  have hAPlus : APlus (fun _ => oneState) s1ActEv () = {true} := by
    ext b
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      s1ActEv_eq, hpr]
    cases b <;> simp
  have hvT : (cfG sOne 1 (fun x => (uAbstain x : ℝ)) true).V (s1ActEv () true) = 0 := by
    rw [s1ActEv_eq]
    exact cfG_V_act_const sOne _ true 0 fun x hx => by simp [uAbstain, hx]
  have hvF : (cfG sOne 1 (fun x => (uAbstain x : ℝ)) false).V (s1ActEv () false) = 1 := by
    rw [s1ActEv_eq]
    exact cfG_V_act_const sOne _ false 1 fun x hx => by simp [uAbstain, hx]
  have hargmax : argmaxAll (fun a => (cfG sOne 1 (fun x => (uAbstain x : ℝ)) a).V (s1ActEv () a))
      = {false} := by
    ext b
    rw [mem_argmaxAll, Finset.mem_singleton]
    cases b
    · refine ⟨fun _ => rfl, fun _ c => ?_⟩
      cases c
      · exact le_rfl
      · rw [hvT, hvF]; norm_num
    · refine ⟨fun h => ?_, fun h => absurd h (by decide)⟩
      have := h false
      rw [hvT, hvF] at this
      norm_num at this
  refine ⟨s1Fam_recordsFor _ _ _ _ _ _ uAbstain procOne, s1State_strict _ _ _ _ _ _ uAbstain procOne,
    by rw [oneState_toDistr]; exact sOne_isFor, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [parentCell_eq_univ_of_parents_empty sOne 1 gColl_parents.2.1 c]
    exact preQuery_univ s1Obs procOne (directTree uAbstain) ()
  · rw [hargmax, hAPlus]; decide
  · intro _ a ha
    have hb : a = true := by
      cases a
      · simp [procOne] at ha
      · rfl
    subst hb
    rw [mem_argmaxPlus, hAPlus]
    exact ⟨Finset.mem_singleton_self _, fun b hb => by rw [Finset.mem_singleton.mp hb]⟩
  · intro h
    have hne : (APlus (fun _ => oneState) s1ActEv ()).Nonempty := by
      rw [hAPlus]; exact Finset.singleton_nonempty _
    have := h hne true (by simp [procOne])
    rw [hargmax] at this
    exact absurd this (by decide)

/-! ## The refutation of (iii) as printed, in one statement (repair round 1, audit r1 N7) -/

/-- **Theorem 3(iii) as printed is refuted, in one statement**: the noisy-XOR tree records at `d`
for the label `1/2`; its calibrated state pushes to `xorP`; both pairwise independences `m ⊥ ℓ`,
`m ⊥ k` hold; joint independence fails; the complete structure `sXor` is compatible with `xorP`;
and its truncated law at `do(m := 1)` is not the act-conditional.
Source: [[learning-cdt-renderings]] Theorem 3(iii) ("if moreover `m ⊥ ⟨V₁⟩` under `P_{s_d}` … the
identity holds for every compatible `G`"), refuted as printed; finding §6.2
Kind: N+
Fidelity: exact (every hypothesis of the printed clause, in its own setting, plus the failure) -/
theorem xor_refutes_iii_package (u : W3 → ℚ) :
    RecordsFor s1Obs s1ActEv procHalf (xorTree u) () ∧
    State.toDistr (State.castℝ (xorState u)) = xorP ∧
    (∀ b c : Bool, xorP.prob {x | x 1 = b ∧ x 0 = c}
      = xorP.prob {x | x 1 = b} * xorP.prob {x | x 0 = c}) ∧
    (∀ b c : Bool, xorP.prob {x | x 1 = b ∧ x 2 = c}
      = xorP.prob {x | x 1 = b} * xorP.prob {x | x 2 = c}) ∧
    xorP.prob {x | x 1 = true ∧ x 0 = false ∧ x 2 = true}
      ≠ xorP.prob {x | x 1 = true} * xorP.prob {x | x 0 = false ∧ x 2 = true} ∧
    sXor.IsFor xorP ∧
    sXor.truncate 1 true ≠ condDistr xorP {x | x 1 = true} xorP_m1_pos :=
  ⟨s1Fam_recordsFor _ _ _ _ _ _ u procHalf, xorTree_toDistr u, xorP_pairwise.1, xorP_pairwise.2,
    xorP_not_joint, sXor_isFor, xor_pairwise_refutes_iii⟩

end Cleanroom.Decision.DpCausalConsist
