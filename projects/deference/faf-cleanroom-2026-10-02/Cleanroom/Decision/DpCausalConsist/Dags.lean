import Cleanroom.Decision.DpCausalConsist.Dag3
import Cleanroom.Decision.DpCausalConsist.Collapse

/-!
# `dp-causal-consist`: Theorem 3's boundary in DAG counts (T3(B)) and the null-act fill (T4(a))

**The direct-effect law** `directP` is the calibrated state of the direct-effect tree
`s1DirectTree` (`Witness3.lean` proves the bridge) at `ρ = 1/10`, `q = 1/2`, `γ = (1/20, 3/5)`,
`τ = 1/5`: `ℓ ∼ Bern(1/10)`, `m ∼ Bern(1/2)` independent of `ℓ`, `k ∼ Bern(γ_ℓ + τ·m)`. The
conditionals are `P(k | m = 1) = 61/200`, `P(k | m = 0) = 21/200`, the marginal `P(k) = 41/200`.

**The seven Markov-compatible DAGs** on `(ℓ, m, k)` (the wiki's count is a script output; the
theorems are per structure): `ℓ ⊥ m` and `k` depends on both, so a compatible DAG has `k`
adjacent to both and either no `ℓ–m` edge with `k` a collider (`gColl`) or all three edges (the
six complete DAGs). By the position of `m`:
* temporal (`pa(m) ⊆ {ℓ}`): `gColl` (`ℓ → k ← m`), `gLMK` (`ℓ → m → k`, `ℓ → k`);
* `m` a root with reversed `ℓ`-edges: `gMLK` (`m → ℓ → k`, `m → k`), `gMKL` (`m → k → ℓ`, `m → ℓ`);
* `k ∈ pa(m)`: `gLKM`, `gKLM`, `gKML`.

For each of the first four an explicit CPD is exhibited (`IsFor`, eight `norm_num` identities)
and the identity `do(m := b) = P(· | m = b)` is proved from `thm3_i` (its right side is
`φ_m(·)(b) = 1/2 = P(m = b)`). For the last three the identity **fails for every compatible
CPD**: `k` is a non-descendant of `m`, so Pearl's invariance pins `P^{do m}(k) = P(k) = 41/200`
against the conditionals `61/200`, `21/200` — no CPD needs to be written, but one is
(`gKML`) so that "every compatible structure" is not vacuous.

**T4(a), the null-act fill** (`nullAct_truncate_ne`): a law with `P(m = 1) = 0` and the DAG
`m → k`; two CPDs factorize it and give different truncated laws at the null act `do(m := 1)`
on the positive-mass event `{k = 1}`. (The mandate's sketch put the null cell at `pa(m)`; with
`P(ℓ = 1) = 0` the truncated laws coincide, since `φ_ℓ(1) = 0` is pinned — the freedom that
reaches the truncated law is at a null *act*, as Corollary 3.1(a) says.)
-/

namespace Cleanroom.Decision.DpCausalConsist

open FactoredSpaces Finset

/-! ## The direct-effect law -/

/-- `P(k = 1 | ℓ, m) = γ_ℓ + τ·m` at `γ = (1/20, 3/5)`, `τ = 1/5`.
Source: mandate T3(B) (`s1DirectTree ρ γ₀ γ₁ τ`, `k ∼ Bern(γ_ℓ + τ·m)`)
Kind: D -/
noncomputable def dRate (ℓ m : Bool) : ℝ := (if ℓ then 3/5 else 1/20) + (if m then 1/5 else 0)

/-- The mass table of the direct-effect law. Source: mandate T3(B). Kind: D -/
noncomputable def dMass (ℓ m k : Bool) : ℝ :=
  (if ℓ then 1/10 else 9/10) * (1/2) * (if k then dRate ℓ m else 1 - dRate ℓ m)

/-- **The direct-effect law** on `W3`.
Source: [[learning-cdt-renderings]] "Checks" ("With a direct effect `m → k` added (still
recorded)"); mandate T3(B)
Kind: D -/
noncomputable def directP : Distr W3 :=
  distr3 dMass (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num [dMass, dRate])
    (by norm_num [dMass, dRate])

/-- `P(m = 1) = 1/2`. Source: mandate T3(B). Kind: N+ -/
theorem directP_m : directP.prob {x | x 1 = true} = 1/2 := by
  rw [prob3_eq]; norm_num [directP, dMass, dRate]

/-- `P(m = 0) = 1/2`. Source: mandate T3(B). Kind: N+ -/
theorem directP_m' : directP.prob {x | x 1 = false} = 1/2 := by
  rw [prob3_eq]; norm_num [directP, dMass, dRate]

/-- `P(k = 1) = 41/200`. Source: mandate T3(B) (`0.205`). Kind: N+ -/
theorem directP_k : directP.prob {x | x 2 = true} = 41/200 := by
  rw [prob3_eq]; norm_num [directP, dMass, dRate]

/-- `P(k = 1 | m = 1) = 61/200`. Source: mandate T3(B) (`0.305`). Kind: N+ -/
theorem directP_k_given_m1 : directP.condProb {x | x 2 = true} {x | x 1 = true} = 61/200 := by
  unfold Distr.condProb
  have : ({x : W3 | x 2 = true} ∩ {x | x 1 = true}) = {x | x 2 = true ∧ x 1 = true} := by
    ext x; simp
  rw [this, directP_m, prob3_eq]; norm_num [directP, dMass, dRate]

/-- `P(k = 1 | m = 0) = 21/200`. Source: mandate T3(B) (`0.105`). Kind: N+ -/
theorem directP_k_given_m0 : directP.condProb {x | x 2 = true} {x | x 1 = false} = 21/200 := by
  unfold Distr.condProb
  have : ({x : W3 | x 2 = true} ∩ {x | x 1 = false}) = {x | x 2 = true ∧ x 1 = false} := by
    ext x; simp
  rw [this, directP_m', prob3_eq]; norm_num [directP, dMass, dRate]

/-- `P(m = b) > 0` for both acts. Source: none: infrastructure. Kind: L -/
theorem directP_m_pos (b : Bool) : 0 < directP.prob {x | x 1 = b} := by
  cases b
  · rw [directP_m']; norm_num
  · rw [directP_m]; norm_num

/-- The conditional `P(k = 1 | m = b)` as a function of `b`. Source: none: infrastructure. Kind: L -/
theorem directP_k_given (b : Bool) :
    directP.condProb {x | x 2 = true} {x | x 1 = b} = if b then 61/200 else 21/200 := by
  cases b
  · exact directP_k_given_m0
  · exact directP_k_given_m1

/-! ## The rate tables -/

/-- The temporal rate table: `ℓ ∼ Bern(1/10)`, `m ∼ Bern(1/2)`, `k ∼ Bern(dRate ℓ m)` — the
tree's own mechanism, read on the parents of each of `gColl`, `gLMK`, `gMLK`.
Source: mandate T3(B)
Kind: D -/
noncomputable def rTemporal : Rate3 where
  r v ℓ m _ := match v with
    | 0 => 1/10
    | 1 => 1/2
    | 2 => dRate ℓ m
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [dRate]
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [dRate]

/-- `P(ℓ = 1 | m, k)` under `directP`, the factor of `ℓ` in the orderings ending in `ℓ`.
Source: none: infrastructure (computed from `directP`)
Kind: D -/
noncomputable def lRate (m k : Bool) : ℝ :=
  match m, k with
  | true, true => 16/61
  | true, false => 4/139
  | false, true => 4/7
  | false, false => 8/179

/-- The rate table for `gMKL` (`m → k → ℓ`, `m → ℓ`): `m ∼ Bern(1/2)`, `k | m ∼ Bern(P(k|m))`,
`ℓ | m, k ∼ Bern(lRate m k)`.
Source: mandate T3(B)
Kind: D -/
noncomputable def rMKL : Rate3 where
  r v _ m k := match v with
    | 0 => lRate m k
    | 1 => 1/2
    | 2 => if m then 61/200 else 21/200
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [lRate]
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [lRate]

/-- The rate table for `gKML` (`k → m → ℓ`, `k → ℓ`): `k ∼ Bern(41/200)`,
`m | k ∼ Bern(P(m | k))`, `ℓ | m, k ∼ Bern(lRate m k)`.
Source: mandate T3(B)
Kind: D -/
noncomputable def rKML : Rate3 where
  r v _ m k := match v with
    | 0 => lRate m k
    | 1 => if k then 61/82 else 139/318
    | 2 => 41/200
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [lRate]
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> norm_num [lRate]

/-! ## The seven DAGs -/

/-- `ℓ → k ← m` (the collider). Source: mandate T3(B). Kind: D -/
def gColl : Digraph (Fin 3) := dag3 fun a b => decide ((a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2))

/-- `ℓ → m`, `ℓ → k`, `m → k`. Source: mandate T3(B). Kind: D -/
def gLMK : Digraph (Fin 3) :=
  dag3 fun a b => decide ((a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2))

/-- `m → ℓ`, `m → k`, `ℓ → k`. Source: mandate T3(B). Kind: D -/
def gMLK : Digraph (Fin 3) :=
  dag3 fun a b => decide ((a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 0 ∧ b = 2))

/-- `m → k`, `m → ℓ`, `k → ℓ`. Source: mandate T3(B). Kind: D -/
def gMKL : Digraph (Fin 3) :=
  dag3 fun a b => decide ((a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 0))

/-- `ℓ → k`, `ℓ → m`, `k → m`. Source: mandate T3(B). Kind: D -/
def gLKM : Digraph (Fin 3) :=
  dag3 fun a b => decide ((a = 0 ∧ b = 2) ∨ (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 1))

/-- `k → ℓ`, `k → m`, `ℓ → m`. Source: mandate T3(B). Kind: D -/
def gKLM : Digraph (Fin 3) :=
  dag3 fun a b => decide ((a = 2 ∧ b = 0) ∨ (a = 2 ∧ b = 1) ∨ (a = 0 ∧ b = 1))

/-- `k → m`, `k → ℓ`, `m → ℓ`. Source: mandate T3(B). Kind: D -/
def gKML : Digraph (Fin 3) :=
  dag3 fun a b => decide ((a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 0))

instance : DecidableRel gColl.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)
instance : DecidableRel gLMK.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)
instance : DecidableRel gMLK.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)
instance : DecidableRel gMKL.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)
instance : DecidableRel gLKM.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)
instance : DecidableRel gKLM.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)
instance : DecidableRel gKML.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)

/-- The rank `ℓ < m < k`. Source: none: infrastructure. Kind: D -/
def rankLMK : Fin 3 → ℕ := fun v => v.val

/-- The rank `m < ℓ < k`. Source: none: infrastructure. Kind: D -/
def rankMLK : Fin 3 → ℕ := ![1, 0, 2]

/-- The rank `m < k < ℓ`. Source: none: infrastructure. Kind: D -/
def rankMKL : Fin 3 → ℕ := ![2, 0, 1]

/-- The rank `ℓ < k < m`. Source: none: infrastructure. Kind: D -/
def rankLKM : Fin 3 → ℕ := ![0, 2, 1]

/-- The rank `k < ℓ < m`. Source: none: infrastructure. Kind: D -/
def rankKLM : Fin 3 → ℕ := ![1, 2, 0]

/-- The rank `k < m < ℓ`. Source: none: infrastructure. Kind: D -/
def rankKML : Fin 3 → ℕ := ![2, 1, 0]

/-- Edges of `gColl` increase `rankLMK`. Source: none: infrastructure. Kind: L -/
theorem gColl_rank : ∀ u v, gColl.Adj u v → rankLMK u < rankLMK v := by decide

/-- Edges of `gLMK` increase `rankLMK`. Source: none: infrastructure. Kind: L -/
theorem gLMK_rank : ∀ u v, gLMK.Adj u v → rankLMK u < rankLMK v := by decide

/-- Edges of `gMLK` increase `rankMLK`. Source: none: infrastructure. Kind: L -/
theorem gMLK_rank : ∀ u v, gMLK.Adj u v → rankMLK u < rankMLK v := by decide

/-- Edges of `gMKL` increase `rankMKL`. Source: none: infrastructure. Kind: L -/
theorem gMKL_rank : ∀ u v, gMKL.Adj u v → rankMKL u < rankMKL v := by decide

/-- Edges of `gLKM` increase `rankLKM`. Source: none: infrastructure. Kind: L -/
theorem gLKM_rank : ∀ u v, gLKM.Adj u v → rankLKM u < rankLKM v := by decide

/-- Edges of `gKLM` increase `rankKLM`. Source: none: infrastructure. Kind: L -/
theorem gKLM_rank : ∀ u v, gKLM.Adj u v → rankKLM u < rankKLM v := by decide

/-- Edges of `gKML` increase `rankKML`. Source: none: infrastructure. Kind: L -/
theorem gKML_rank : ∀ u v, gKML.Adj u v → rankKML u < rankKML v := by decide

/-- Parents in `gColl`. Source: none: infrastructure. Kind: L -/
theorem gColl_parents : gColl.parents 0 = ∅ ∧ gColl.parents 1 = ∅ ∧ gColl.parents 2 = {0, 1} := by
  decide

/-- Parents in `gLMK`. Source: none: infrastructure. Kind: L -/
theorem gLMK_parents : gLMK.parents 0 = ∅ ∧ gLMK.parents 1 = {0} ∧ gLMK.parents 2 = {0, 1} := by
  decide

/-- Parents in `gMLK`. Source: none: infrastructure. Kind: L -/
theorem gMLK_parents : gMLK.parents 0 = {1} ∧ gMLK.parents 1 = ∅ ∧ gMLK.parents 2 = {0, 1} := by
  decide

/-- Parents in `gMKL`. Source: none: infrastructure. Kind: L -/
theorem gMKL_parents : gMKL.parents 0 = {1, 2} ∧ gMKL.parents 1 = ∅ ∧ gMKL.parents 2 = {1} := by
  decide

/-- Parents in `gKML`. Source: none: infrastructure. Kind: L -/
theorem gKML_parents : gKML.parents 0 = {1, 2} ∧ gKML.parents 1 = {2} ∧ gKML.parents 2 = ∅ := by
  decide

/-- The four structures on which the identity holds, with their CPDs.
Source: mandate T3(B)
Kind: D -/
noncomputable def sColl : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gColl, isAcyclic_of_rank _ _ gColl_rank, cpdOfRate gColl rTemporal⟩

/-- `gLMK` with the temporal CPD. Source: mandate T3(B). Kind: D -/
noncomputable def sLMK : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gLMK, isAcyclic_of_rank _ _ gLMK_rank, cpdOfRate gLMK rTemporal⟩

/-- `gMLK` with the temporal CPD (`P(ℓ | m) = P(ℓ)` since `ℓ ⊥ m`). Source: mandate T3(B). Kind: D -/
noncomputable def sMLK : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gMLK, isAcyclic_of_rank _ _ gMLK_rank, cpdOfRate gMLK rTemporal⟩

/-- `gMKL` with its CPD. Source: mandate T3(B). Kind: D -/
noncomputable def sMKL : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gMKL, isAcyclic_of_rank _ _ gMKL_rank, cpdOfRate gMKL rMKL⟩

/-- `gKML` with its CPD (a compatible structure with `k ∈ pa(m)`). Source: mandate T3(B). Kind: D -/
noncomputable def sKML : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gKML, isAcyclic_of_rank _ _ gKML_rank, cpdOfRate gKML rKML⟩

/-! ## Compatibility -/

/-- `sColl` is a structure for `directP`. Source: mandate T3(B). Kind: N+ -/
theorem sColl_isFor : sColl.IsFor directP := by
  unfold sColl
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gColl_parents.1, gColl_parents.2.1, gColl_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [directP, dMass, dRate, rTemporal]

/-- `sLMK` is a structure for `directP`. Source: mandate T3(B). Kind: N+ -/
theorem sLMK_isFor : sLMK.IsFor directP := by
  unfold sLMK
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gLMK_parents.1, gLMK_parents.2.1, gLMK_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [directP, dMass, dRate, rTemporal]

/-- `sMLK` is a structure for `directP`. Source: mandate T3(B). Kind: N+ -/
theorem sMLK_isFor : sMLK.IsFor directP := by
  unfold sMLK
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gMLK_parents.1, gMLK_parents.2.1, gMLK_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [directP, dMass, dRate, rTemporal]

/-- `sMKL` is a structure for `directP`. Source: mandate T3(B). Kind: N+ -/
theorem sMKL_isFor : sMKL.IsFor directP := by
  unfold sMKL
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gMKL_parents.1, gMKL_parents.2.1, gMKL_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [directP, dMass, dRate, rMKL, lRate]

/-- `sKML` is a structure for `directP` (so the failing class is inhabited). Source: mandate T3(B). Kind: N+ -/
theorem sKML_isFor : sKML.IsFor directP := by
  unfold sKML
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gKML_parents.1, gKML_parents.2.1, gKML_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [directP, dMass, dRate, rKML, lRate]

/-! ## The identity on the four -/

/-- The act's factor is `1/2` under the temporal table, whatever the parent configuration.
Source: none: infrastructure
Kind: L -/
theorem rTemporal_act (G : Digraph (Fin 3)) [DecidableRel G.Adj]
    (c : ParentVals G (fun _ : Fin 3 => Bool) 1) (b : Bool) :
    (cpdOfRate G rTemporal 1 c).mass b = 1/2 := by
  simp only [cpdOfRate, bern_mass, rTemporal]
  cases b <;> norm_num

/-- The act's factor is `1/2` under `rMKL`. Source: none: infrastructure. Kind: L -/
theorem rMKL_act (c : ParentVals gMKL (fun _ : Fin 3 => Bool) 1) (b : Bool) :
    (cpdOfRate gMKL rMKL 1 c).mass b = 1/2 := by
  simp only [cpdOfRate, bern_mass, rMKL]
  cases b <;> norm_num

/-- **The identity on `gColl`**: `do(m := b) = P(· | m = b)` for both acts.
Source: [[learning-cdt-renderings]] "Checks" ("the identity holds for the two temporal ones");
mandate T3(B)
Kind: N+ -/
theorem sColl_collapse (b : Bool) :
    sColl.truncate 1 b = condDistr directP {x | x 1 = b} (directP_m_pos b) := by
  rw [CausalStructure.truncate, thm3_i sColl.acyclic sColl.φ sColl_isFor 1 b (directP_m_pos b)]
  intro x _ _
  show (cpdOfRate gColl rTemporal 1 _).mass b = _
  rw [rTemporal_act]
  cases b
  · rw [directP_m']
  · rw [directP_m]

/-- **The identity on `gLMK`**. Source: [[learning-cdt-renderings]] "Checks"; mandate T3(B). Kind: N+ -/
theorem sLMK_collapse (b : Bool) :
    sLMK.truncate 1 b = condDistr directP {x | x 1 = b} (directP_m_pos b) := by
  rw [CausalStructure.truncate, thm3_i sLMK.acyclic sLMK.φ sLMK_isFor 1 b (directP_m_pos b)]
  intro x _ _
  show (cpdOfRate gLMK rTemporal 1 _).mass b = _
  rw [rTemporal_act]
  cases b
  · rw [directP_m']
  · rw [directP_m]

/-- **The identity on `gMLK`** (`m` a root, reversed `m → ℓ`).
Source: [[learning-cdt-renderings]] "Checks" ("the two reversed ones in which `m` is a root");
mandate T3(B)
Kind: N+ -/
theorem sMLK_collapse (b : Bool) :
    sMLK.truncate 1 b = condDistr directP {x | x 1 = b} (directP_m_pos b) := by
  rw [CausalStructure.truncate, thm3_i sMLK.acyclic sMLK.φ sMLK_isFor 1 b (directP_m_pos b)]
  intro x _ _
  show (cpdOfRate gMLK rTemporal 1 _).mass b = _
  rw [rTemporal_act]
  cases b
  · rw [directP_m']
  · rw [directP_m]

/-- **The identity on `gMKL`** (`m` a root). Source: [[learning-cdt-renderings]] "Checks"; mandate T3(B). Kind: N+ -/
theorem sMKL_collapse (b : Bool) :
    sMKL.truncate 1 b = condDistr directP {x | x 1 = b} (directP_m_pos b) := by
  rw [CausalStructure.truncate, thm3_i sMKL.acyclic sMKL.φ sMKL_isFor 1 b (directP_m_pos b)]
  intro x _ _
  show (cpdOfRate gMKL rMKL 1 _).mass b = _
  rw [rMKL_act]
  cases b
  · rw [directP_m']
  · rw [directP_m]

/-! ## The failure on the three with `k ∈ pa(m)` -/

/-- `{x | x 2 = true}` is in the fixed algebra of any DAG in which `k` is a non-descendant of `m`.
Source: none: infrastructure
Kind: L -/
theorem k_inFixedAlgebra (G : Digraph (Fin 3)) (hk : (2 : Fin 3) ∈ nondesc G 1) :
    InFixedAlgebra G 1 (Finset.univ.filter fun x : W3 => x 2 = true) := by
  intro x y hxy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hxy 2 hk]

/-- **Pearl's invariance pins the interventional `k`-rate to the marginal when `k ∈ nondesc(m)`**:
for every structure `Γ` for `directP` with `k` a non-descendant of `m`,
`P^{do(m := b)}(k = 1) = P(k = 1) = 41/200` for both acts.
Source: [[learning-cdt-renderings]] "Checks" ("`P(k | do m) = 0.205`"); mandate T3(B)
Kind: C
Hyps: (a) `Γ.IsFor directP`; (a) `2 ∈ nondesc Γ.G 1` -/
theorem truncate_k_of_nondesc (Γ : CausalStructure (fun _ : Fin 3 => Bool)) (hΓ : Γ.IsFor directP)
    (hk : (2 : Fin 3) ∈ nondesc Γ.G 1) (b : Bool) :
    (Γ.truncate 1 b).prob {x | x 2 = true} = 41/200 := by
  have hset : ({x : W3 | x 2 = true}) = ↑(Finset.univ.filter fun x : W3 => x 2 = true) := by
    ext x; simp
  rw [hset, CausalStructure.truncate,
    truncate_prob_eq_of_inFixedAlgebra Γ.acyclic Γ.φ hΓ 1 b _ (k_inFixedAlgebra Γ.G hk), ← hset,
    directP_k]

/-- **The identity fails for every compatible structure with `k ∈ nondesc(m)`**: the truncated
law gives `k` probability `41/200` while the conditional gives `61/200` (`m = 1`) or `21/200`
(`m = 0`).
Source: [[learning-cdt-renderings]] "Checks" ("fails for the three in which `k` is a parent of
`m` — `P(k | do m) = 0.205` against `P(k | m=1) = 0.305`, `P(k | m=0) = 0.105`"); mandate T3(B)
Kind: C
Hyps: (a) `Γ.IsFor directP`; (a) `2 ∈ nondesc Γ.G 1` -/
theorem truncate_ne_cond_of_nondesc (Γ : CausalStructure (fun _ : Fin 3 => Bool))
    (hΓ : Γ.IsFor directP) (hk : (2 : Fin 3) ∈ nondesc Γ.G 1) (b : Bool) :
    Γ.truncate 1 b ≠ condDistr directP {x | x 1 = b} (directP_m_pos b) := by
  intro h
  have h1 := truncate_k_of_nondesc Γ hΓ hk b
  rw [h, condDistr_prob, directP_k_given] at h1
  cases b <;> norm_num at h1

/-- `k ∈ nondesc(m)` in `gLKM`. Source: none: infrastructure. Kind: L -/
theorem gLKM_k_nondesc : (2 : Fin 3) ∈ nondesc gLKM 1 :=
  mem_nondesc_of_rank gLKM rankLKM gLKM_rank (by decide) (by decide)

/-- `k ∈ nondesc(m)` in `gKLM`. Source: none: infrastructure. Kind: L -/
theorem gKLM_k_nondesc : (2 : Fin 3) ∈ nondesc gKLM 1 :=
  mem_nondesc_of_rank gKLM rankKLM gKLM_rank (by decide) (by decide)

/-- `k ∈ nondesc(m)` in `gKML`. Source: none: infrastructure. Kind: L -/
theorem gKML_k_nondesc : (2 : Fin 3) ∈ nondesc gKML 1 :=
  mem_nondesc_of_rank gKML rankKML gKML_rank (by decide) (by decide)

/-- **The failure on `gLKM`, `gKLM`, `gKML`**, for every CPD compatible with `directP` on them.
Source: [[learning-cdt-renderings]] "Checks"; mandate T3(B)
Kind: C
Hyps: (a) `Γ.G` one of the three; (a) `Γ.IsFor directP` -/
theorem failing_three (Γ : CausalStructure (fun _ : Fin 3 => Bool)) (hΓ : Γ.IsFor directP)
    (hG : Γ.G = gLKM ∨ Γ.G = gKLM ∨ Γ.G = gKML) (b : Bool) :
    Γ.truncate 1 b ≠ condDistr directP {x | x 1 = b} (directP_m_pos b) := by
  apply truncate_ne_cond_of_nondesc Γ hΓ _ b
  rcases hG with h | h | h <;> rw [h]
  · exact gLKM_k_nondesc
  · exact gKLM_k_nondesc
  · exact gKML_k_nondesc

/-- **The failure on `sKML` in particular** (the class is not vacuous).
Source: mandate T3(B)
Kind: N+ -/
theorem sKML_not_collapse (b : Bool) :
    sKML.truncate 1 b ≠ condDistr directP {x | x 1 = b} (directP_m_pos b) :=
  failing_three sKML sKML_isFor (Or.inr (Or.inr rfl)) b

/-- **T1's non-vacuity**: on `gColl`, the non-descendants of `m` are `{ℓ}`, and the `k`-marginal
*does* move under `do m` (`61/200` vs `21/200`), so Pearl's invariance is not an artifact of
the algebra being everything.
Source: mandate T1 ("Witness N+: the collider-shaped DAG … where `nondesc = {ℓ}` and the
`k`-marginal does move under `do m`")
Kind: N+ -/
theorem sColl_k_moves :
    (sColl.truncate 1 true).prob {x | x 2 = true} ≠ (sColl.truncate 1 false).prob {x | x 2 = true} ∧
    (2 : Fin 3) ∉ nondesc gColl 1 := by
  refine ⟨?_, ?_⟩
  · rw [sColl_collapse, sColl_collapse, condDistr_prob, condDistr_prob, directP_k_given,
      directP_k_given]
    norm_num
  · rw [mem_nondesc]
    push Not
    intro _
    exact Relation.TransGen.single (by decide)

/-! ## T4(a): the null-act fill -/

/-- A law with the act null: `ℓ ∼ Bern(1/2)`, `m = 0`, `k ∼ Bern(1/3)`.
Source: [[learning-cdt-renderings]] Corollary 3.1(a) ("at null acts, where the truncated
factorization needs probability-zero cells and the parameter prior fills them"); mandate T4(a)
Kind: D -/
noncomputable def nullActP : Distr W3 :=
  distr3 (fun _ m k => if m then 0 else (1/2) * (if k then 1/3 else 2/3))
    (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num) (by norm_num)

/-- `m → k` alone. Source: mandate T4(a). Kind: D -/
def gMK : Digraph (Fin 3) := dag3 fun a b => decide (a = 1 ∧ b = 2)

instance : DecidableRel gMK.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)

/-- Parents in `gMK`. Source: none: infrastructure. Kind: L -/
theorem gMK_parents : gMK.parents 0 = ∅ ∧ gMK.parents 1 = ∅ ∧ gMK.parents 2 = {1} := by decide

/-- Edges of `gMK` increase the rank. Source: none: infrastructure. Kind: L -/
theorem gMK_rank : ∀ u v, gMK.Adj u v → rankLMK u < rankLMK v := by decide

/-- A CPD for `nullActP` on `gMK` whose factor at the null cell `m = 1` fills `k` with rate `t`.
Source: mandate T4(a)
Kind: D -/
noncomputable def rNull (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Rate3 where
  r v _ m _ := match v with
    | 0 => 1/2
    | 1 => 0
    | 2 => if m then t else 1/3
  nonneg v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> simp <;> linarith
  le_one v a b c := by fin_cases v <;> cases a <;> cases b <;> cases c <;> simp <;> linarith

/-- The structure `gMK` with fill `t`. Source: mandate T4(a). Kind: D -/
noncomputable def sNull (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gMK, isAcyclic_of_rank _ _ gMK_rank, cpdOfRate gMK (rNull t h0 h1)⟩

/-- Every fill `t` gives a structure for `nullActP`: the CPD at the null act is free.
Source: [[learning-cdt-renderings]] Corollary 3.1(a); FAF `FactorizesOverDAG` docstring ("the
CPD at a parent configuration of probability zero is not determined by `P`")
Kind: N+ -/
theorem sNull_isFor (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : (sNull t h0 h1).IsFor nullActP := by
  unfold sNull
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gMK_parents.1, gMK_parents.2.1, gMK_parents.2.2,
    Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [nullActP, rNull]

/-- The truncated law at the null act `do(m := 1)` gives `k` probability `t`: the fill.
Source: mandate T4(a)
Kind: N+ -/
theorem sNull_truncate_k (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((sNull t h0 h1).truncate 1 true).prob {x | x 2 = true} = t := by
  rw [prob3_eq]
  unfold sNull
  simp only [truncate_cpdOfRate_mass, cpdFactor_cpdOfRate, gMK_parents.1, gMK_parents.2.2,
    Finset.notMem_empty, Finset.mem_singleton]
  norm_num [rNull]
  ring

/-- **Corollary 3.1(a), the null-act fill**: two CPDs both factorizing `nullActP` over `m → k`
whose truncated laws at the null act differ on the positive-mass event `{k = 1}` (`1/4` vs `3/4`).
`thm3_i` does not apply (`P(m = 1) = 0`); the supposition at a null act is whatever the
parameter prior says.
Source: [[learning-cdt-renderings]] Corollary 3.1(a); mandate T2(i) (`thm3_i_null_cell`), T4(a)
Kind: N+ -/
theorem nullAct_truncate_ne :
    (sNull (1/4) (by norm_num) (by norm_num)).IsFor nullActP ∧
    (sNull (3/4) (by norm_num) (by norm_num)).IsFor nullActP ∧
    nullActP.prob {x | x 1 = true} = 0 ∧
    (sNull (1/4) (by norm_num) (by norm_num)).truncate 1 true
      ≠ (sNull (3/4) (by norm_num) (by norm_num)).truncate 1 true := by
  refine ⟨sNull_isFor _ _ _, sNull_isFor _ _ _, ?_, ?_⟩
  · rw [prob3_eq]; norm_num [nullActP]
  · intro h
    have h1 := sNull_truncate_k (1/4) (by norm_num) (by norm_num)
    rw [h, sNull_truncate_k] at h1
    norm_num at h1

end Cleanroom.Decision.DpCausalConsist
