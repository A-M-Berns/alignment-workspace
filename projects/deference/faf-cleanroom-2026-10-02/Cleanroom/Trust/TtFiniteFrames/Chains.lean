import Cleanroom.Trust.TtFiniteFrames.Partition
import Mathlib.Data.Fin.VecNotation

/-!
# Chain-transitivity of finite-frame Total Trust is false

Package `tt-finite-frames`, Targets T2 and T4 (load-bearing 1), plus T3's non-vacuity witness.

* **T4 (headline)**: three agents with one prior each — `H = πH`, `A = (πA, cA)`, `B = (πB, cB)` —
  on `Fin 3`: `πH` totally trusts `A`'s partition expert `ofPartition πA cA`, `πA` totally trusts
  `B`'s `ofPartition πB cB`, and `πH` does **not** totally trust `B`'s expert, failing at the
  exhibited `(X, s) = (𝟙_{1}, 1/2)` with product-form mass exactly `−1/8`. Both links carry the
  honest `∀ X ∀ s` quantifier (through T3, i.e. cellwise conditional agreement); the failure is one
  exhibited pair. The honest one-line summary is "**chain**-transitivity of finite-frame Total
  Trust in partition experts is false" ([[route-transitivity]] §8's correction of emphasis), not
  "trust is not transitive" unqualified.
* **T2 (the lab's chain, as recorded)**: trust-lab-063's `Fin 3` chain, in which the middle agent's
  *frame* is built from `H`'s prior while its *deferral* uses its own — finding F-T2 in the
  package findings; T4 is the repair.
* **`Sharper.recovery`** (T3's N+): distinct priors that agree cellwise, so prior identity is
  sufficient, not necessary, for cross-prior trust.

All numbers are exact rationals checked by `norm_num` over `Fin.sum_univ_three`; nothing is
`decide`d on reals.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Computation helpers -/

/-- The mass of a fibre as a `univ`-sum with an indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_ofMap_eq {ι : Type} [DecidableEq ι] (π : W → ℝ) (c : W → ι) (v : W) :
    mass π (Corr.ofMap c v) = ∑ u, if c u = c v then π u else 0 := by
  rw [mass, Corr.ofMap, sum_filter]

/-- The partition expert's estimate as a ratio of `univ`-sums with indicators (for `norm_num`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_E_eq' {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (f : W → ι) (w : W) (X : W → ℝ) :
    E ((Frame.ofPartition π hpos f).P w) X =
      (∑ v, if f v = f w then π v * X v else 0) / (∑ v, if f v = f w then π v else 0) := by
  rw [Frame.ofPartition_E_eq, mass_ofMap_eq, Corr.ofMap, sum_filter]

/-! ## T4: one prior per agent (the headline) -/

namespace T4

/-- `H`'s prior `(1/4, 1/4, 1/2)`.
Source: mandate T4 (witness found via T3)
Kind: D
Fidelity: exact -/
def πH : Fin 3 → ℝ := ![1 / 4, 1 / 4, 1 / 2]

/-- `A`'s prior, uniform `(1/3, 1/3, 1/3)`.
Source: mandate T4
Kind: D
Fidelity: exact -/
def πA : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-- `B`'s prior `(1/2, 1/4, 1/4)`.
Source: mandate T4
Kind: D
Fidelity: exact -/
def πB : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- `A`'s partition: cells `{0, 1}`, `{2}`.
Source: mandate T4
Kind: D
Fidelity: exact -/
def cA : Fin 3 → Fin 2 := ![0, 0, 1]

/-- `B`'s partition: cells `{0}`, `{1, 2}`.
Source: mandate T4
Kind: D
Fidelity: exact -/
def cB : Fin 3 → Fin 2 := ![0, 1, 1]

/-- `πH` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hposH : ∀ w, 0 < πH w := by intro w; fin_cases w <;> norm_num [πH]

/-- `πA` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hposA : ∀ w, 0 < πA w := by intro w; fin_cases w <;> norm_num [πA]

/-- `πB` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hposB : ∀ w, 0 < πB w := by intro w; fin_cases w <;> norm_num [πB]

/-- `A`'s expert: `πA` conditioned on `A`'s partition.
Source: mandate T4
Kind: D
Fidelity: exact -/
def FA : Frame (Fin 3) := Frame.ofPartition πA hposA cA

/-- `B`'s expert: `πB` conditioned on `B`'s partition.
Source: mandate T4
Kind: D
Fidelity: exact -/
def FB : Frame (Fin 3) := Frame.ofPartition πB hposB cB

/-- Cellwise agreement of `πH` and `πA` on `cA`: `πH(· | {0,1}) = (1/2, 1/2) = πA(· | {0,1})`
(product form, all three worlds by `norm_num`).
Source: mandate T4 (via trust-lab-064)
Kind: L
Fidelity: n/a -/
theorem agree1 : ∀ v, πA v * mass πH (Corr.ofMap cA v) = πH v * mass πA (Corr.ofMap cA v) := by
  intro v
  fin_cases v <;> simp [mass_ofMap_eq, Fin.sum_univ_three, πH, πA, cA] <;> norm_num

/-- **Link 1**: `πH` totally trusts `A`'s expert — `πH(· | {0,1}) = (1/2, 1/2) = πA(· | {0,1})`,
so T3 applies; the honest `∀ X ∀ s` quantifier. The priors are distinct, so as a `(prior, frame)`
pair this is not the self-instance T1; at the frame level it is one, necessarily by T3 — `FA` is
`πH`'s own partition expert on `cA` (`FA_P_eq_own`).
Source: mandate T4 (via trust-lab-064)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem link1 : TotalTrust πH FA := (totalTrust_ofPartition_cross_iff hposH hposA cA).2 agree1

/-- Cellwise agreement of `πA` and `πB` on `cB`: `πA(· | {1,2}) = (1/2, 1/2) = πB(· | {1,2})`.
Source: mandate T4 (via trust-lab-064)
Kind: L
Fidelity: n/a -/
theorem agree2 : ∀ v, πB v * mass πA (Corr.ofMap cB v) = πA v * mass πB (Corr.ofMap cB v) := by
  intro v
  fin_cases v <;> simp [mass_ofMap_eq, Fin.sum_univ_three, πA, πB, cB] <;> norm_num

/-- **Link 2**: `πA` totally trusts `B`'s expert — `πA(· | {1,2}) = (1/2, 1/2) = πB(· | {1,2})`;
the priors are distinct, so as a `(prior, frame)` pair this is not the self-instance T1; at the
frame level it is one, necessarily by T3 — `FB` is `πA`'s own partition expert on `cB`
(`FB_P_eq_own`).
Source: mandate T4 (via trust-lab-064)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem link2 : TotalTrust πA FB := (totalTrust_ofPartition_cross_iff hposA hposB cB).2 agree2

/-- `B`'s expert's estimate of `𝟙_{1}` at each world: `0, 1/2, 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem FB_E_ind1 : E (FB.P 0) (ind {1}) = 0 ∧ E (FB.P 1) (ind {1}) = 1 / 2 ∧
    E (FB.P 2) (ind {1}) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [FB, Frame.ofPartition_E_eq']; simp [Fin.sum_univ_three, πB, cB, ind] <;> norm_num)

/-- **The exact gap on the long edge**: at `(X, s) = (𝟙_{1}, 1/2)` the product-form mass of
"`πH` totally trusts `B`'s expert" is exactly `−1/8`.
Source: mandate T4 (re-verified)
Kind: N+
Fidelity: exact -/
theorem long_edge_gap :
    ∑ w, πH w * (ind {1} w - 1 / 2) * (if (1 / 2 : ℝ) ≤ E (FB.P w) (ind {1}) then 1 else 0) =
      -1 / 8 := by
  obtain ⟨h0, h1, h2⟩ := FB_E_ind1
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp [πH, ind]
  norm_num

/-- **The long edge fails**: `πH` does not totally trust `B`'s expert (exhibited `(X, s)`).
Source: mandate T4
Kind: N+
Fidelity: exact -/
theorem long_edge_fails : ¬ TotalTrust πH FB := by
  intro h
  have := h (ind {1}) (1 / 2)
  rw [long_edge_gap] at this
  norm_num at this

/-- **T4 (load-bearing 1). Chain-transitivity of finite-frame Total Trust in partition experts
is false, one prior per agent.** `H` totally trusts `A`'s expert and `A` totally trusts `B`'s
expert — both for all `X` and all `s` — yet `H` does not totally trust `B`'s expert. The
statement is about a *chain* `H → A → B` of partition experts on a three-world frame; it does not
say "trust is not transitive" in any wider sense ([[route-transitivity]] §8).
Source: trust-lab-063 (chain), repaired to one prior per agent per the mandate; witness checked by
the mandate writer and re-verified here
Kind: P / N+ (both links through T3 at grade (a); the failure exhibited)
Fidelity: variant: single prior per agent (the source's chain gives the middle agent two priors)
Hyps: (a) none -/
theorem totalTrust_not_transitive : TotalTrust πH FA ∧ TotalTrust πA FB ∧ ¬ TotalTrust πH FB :=
  ⟨link1, link2, long_edge_fails⟩

/-- The long edge also fails through the characterization: at world `1`,
`πB 1 · πH({1,2}) = 3/16 ≠ 1/8 = πH 1 · πB({1,2})`.
Source: mandate T4 (via trust-lab-064)
Kind: L
Fidelity: n/a -/
theorem long_edge_fails_via_iff : ¬ TotalTrust πH FB := by
  rw [FB, totalTrust_ofPartition_cross_iff hposH hposB cB]
  intro h
  have := h 1
  simp [mass_ofMap_eq, Fin.sum_univ_three, πH, πB, cB] at this

/-- Non-degeneracy: the three priors are pairwise distinct, and both partitions are non-trivial
(`cA` separates `1` from `2`, `cB` separates `0` from `1`, neither is discrete).
Source: mandate T4
Kind: N+
Fidelity: exact -/
theorem nondegenerate : πH ≠ πA ∧ πA ≠ πB ∧ πH ≠ πB ∧
    (cA 0 = cA 1 ∧ cA 1 ≠ cA 2) ∧ (cB 0 ≠ cB 1 ∧ cB 1 = cB 2) := by
  refine ⟨?_, ?_, ?_, ⟨rfl, by decide⟩, ⟨by decide, rfl⟩⟩
  · intro h; have := congrFun h 0; norm_num [πH, πA] at this
  · intro h; have := congrFun h 0; norm_num [πA, πB] at this
  · intro h; have := congrFun h 0; norm_num [πH, πB] at this

/-- **The links are frame identities** (audit r1 fidelity N3). T3's (⇐) direction is
`Frame.ofPartition_P_eq_of_agree`: link 1 holds because `A`'s expert *is* `πH`'s own partition
expert on `cA`, and link 2 because `B`'s expert *is* `πA`'s own partition expert on `cB` —
cross-prior Total Trust in a partition expert is frame-identity with the deferrer's own expert.
So T4's repair of F-T2 lies in the bookkeeping (one prior per agent; the identities hold between
*distinct* priors, as in `Sharper.recovery`), not in the trust relation: no partition-expert
chain can have a link that is not a self-instance at the frame level.
Source: none: audit r1 fidelity N3
Kind: L
Fidelity: n/a -/
theorem FA_P_eq_own : FA.P = (Frame.ofPartition πH hposH cA).P :=
  (Frame.ofPartition_P_eq_of_agree hposH hposA cA agree1).symm

/-- Link 2 as a frame identity: `B`'s expert is `πA`'s own partition expert on `cB`.
Source: none: audit r1 fidelity N3
Kind: L
Fidelity: n/a -/
theorem FB_P_eq_own : FB.P = (Frame.ofPartition πA hposA cB).P :=
  (Frame.ofPartition_P_eq_of_agree hposA hposB cB agree2).symm

end T4

/-! ## T2: the lab's chain, as recorded -/

namespace T2

/-- The lab's human prior `(1/2, 1/4, 1/4)`.
Source: trust-lab-063 `πH`
Kind: D
Fidelity: exact -/
def πH : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The lab's advisor prior `(1/4, 1/2, 1/4)`.
Source: trust-lab-063 `πA`
Kind: D
Fidelity: exact -/
def πA : Fin 3 → ℝ := ![1 / 4, 1 / 2, 1 / 4]

/-- The lab's partition `F_A`: cells `{0}`, `{1, 2}`.
Source: trust-lab-063 `cA`
Kind: D
Fidelity: exact -/
def cA : Fin 3 → Fin 2 := ![0, 1, 1]

/-- The lab's partition `F_B`: cells `{0, 1}`, `{2}`.
Source: trust-lab-063 `cB`
Kind: D
Fidelity: exact -/
def cB : Fin 3 → Fin 2 := ![0, 0, 1]

/-- `πH` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hposH : ∀ w, 0 < πH w := by intro w; fin_cases w <;> norm_num [πH]

/-- `πA` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hposA : ∀ w, 0 < πA w := by intro w; fin_cases w <;> norm_num [πA]

/-- The lab's expert `A`: `πH` conditioned on `F_A` — built from **`H`'s** prior (finding F-T2).
Source: trust-lab-063 `PA = condExpert πH cA`
Kind: D
Fidelity: exact -/
def FA : Frame (Fin 3) := Frame.ofPartition πH hposH cA

/-- The lab's expert `B`: `πA` conditioned on `F_B`.
Source: trust-lab-063 `PB = condExpert πA cB`
Kind: D
Fidelity: exact -/
def FB : Frame (Fin 3) := Frame.ofPartition πA hposA cB

/-- The lab's recovery expert: the same partition `F_B` conditioned by `πH`.
Source: trust-lab-063 `PB' = condExpert πH cB`
Kind: D
Fidelity: exact -/
def FB' : Frame (Fin 3) := Frame.ofPartition πH hposH cB

/-- Link 1 of the lab's chain: `πH` totally trusts `FA` — the self-instance T1, since `FA` is
`πH`'s own partition expert.
Source: trust-lab-063 `link1`
Kind: L (instance of T1)
Fidelity: exact -/
theorem link1 : TotalTrust πH FA := totalTrust_ofPartition hposH cA

/-- Link 2 of the lab's chain: `πA` totally trusts `FB` — again the self-instance T1.
Source: trust-lab-063 `link2`
Kind: L (instance of T1)
Fidelity: exact -/
theorem link2 : TotalTrust πA FB := totalTrust_ofPartition hposA cB

/-- `FB`'s estimate of `𝟙_{1}` at each world: `2/3, 2/3, 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem FB_E_ind1 : E (FB.P 0) (ind {1}) = 2 / 3 ∧ E (FB.P 1) (ind {1}) = 2 / 3 ∧
    E (FB.P 2) (ind {1}) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [FB, Frame.ofPartition_E_eq']; simp [Fin.sum_univ_three, πA, cB, ind] <;> norm_num)

/-- The lab's exact gap: at `(X₀, s) = (𝟙_{1}, 1/2)` the product-form mass is `−1/8`.
Source: trust-lab-063 `long_edge_gap`
Kind: N+
Fidelity: exact -/
theorem long_edge_gap :
    ∑ w, πH w * (ind {1} w - 1 / 2) * (if (1 / 2 : ℝ) ≤ E (FB.P w) (ind {1}) then 1 else 0) =
      -1 / 8 := by
  obtain ⟨h0, h1, h2⟩ := FB_E_ind1
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp [πH, ind]
  norm_num

/-- The lab's long edge fails.
Source: trust-lab-063 `long_edge_fails`
Kind: N+
Fidelity: exact -/
theorem long_edge_fails : ¬ TotalTrust πH FB := by
  intro h
  have := h (ind {1}) (1 / 2)
  rw [long_edge_gap] at this
  norm_num at this

/-- **T2, the lab's chain as recorded**: both links hold with the `∀ X ∀ s` quantifier (each is
T1), the long edge fails at `(𝟙_{1}, 1/2)`. Recorded variant of T4: here the middle agent's frame
is `H`'s conditional expert on `F_A` while its deferral uses `πA` (finding F-T2).
Source: trust-lab-063 `TT_not_transitive`
Kind: N+
Fidelity: exact (of the source; see F-T2 for what it does and does not show)
Hyps: (a) none -/
theorem lab_chain : TotalTrust πH FA ∧ TotalTrust πA FB ∧ ¬ TotalTrust πH FB :=
  ⟨link1, link2, long_edge_fails⟩

/-- The lab's recovery: conditioning the same partition `F_B` by `πH` restores trust (T1).
Source: trust-lab-063 `recovery`
Kind: L (instance of T1)
Fidelity: exact -/
theorem recovery : TotalTrust πH FB' := totalTrust_ofPartition hposH cB

/-- Non-degeneracy block: the priors differ; `FB` is genuinely `πA`-conditional (its rows differ
from the `πH`-conditional `FB'`); both partitions are non-trivial.
Source: trust-lab-063 (non-degeneracy checks)
Kind: N+
Fidelity: exact -/
theorem nondegenerate : πA ≠ πH ∧ FB.P ≠ FB'.P ∧
    (cA 0 ≠ cA 1 ∧ cA 1 = cA 2) ∧ (cB 0 = cB 1 ∧ cB 1 ≠ cB 2) := by
  refine ⟨?_, ?_, ⟨by decide, rfl⟩, ⟨rfl, by decide⟩⟩
  · intro h; have := congrFun h 0; norm_num [πH, πA] at this
  · intro h
    have := congrFun (congrFun h 0) 0
    rw [FB, FB', Frame.ofPartition_P_apply, Frame.ofPartition_P_apply] at this
    simp [mass_ofMap_eq, Fin.sum_univ_three, πH, πA, cB] at this
    norm_num at this

end T2

/-! ## T3's witness: prior identity is sufficient, not necessary -/

namespace Sharper

/-- `H`'s prior `(1/6, 1/6, 2/3)`.
Source: trust-lab-064 `sharper_recovery` (`πH₂`)
Kind: D
Fidelity: exact -/
def πH : Fin 3 → ℝ := ![1 / 6, 1 / 6, 2 / 3]

/-- `A`'s prior, uniform.
Source: trust-lab-064 `sharper_recovery` (`πA₂`)
Kind: D
Fidelity: exact -/
def πA : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-- The partition with cells `{0, 1}`, `{2}`.
Source: trust-lab-064 `sharper_recovery`
Kind: D
Fidelity: exact -/
def c : Fin 3 → Fin 2 := ![0, 0, 1]

/-- `πH` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hposH : ∀ w, 0 < πH w := by intro w; fin_cases w <;> norm_num [πH]

/-- `πA` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hposA : ∀ w, 0 < πA w := by intro w; fin_cases w <;> norm_num [πA]

/-- **Sharper recovery (T3's N+ witness).** Distinct priors whose conditionals agree on every
cell: `πH` totally trusts `πA`'s partition expert although `πH ≠ πA`. So prior identity is
sufficient but not necessary for cross-prior trust; the exact condition is T3's.
Source: trust-lab-064 `sharper_recovery`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem recovery : TotalTrust πH (Frame.ofPartition πA hposA c) ∧ πH ≠ πA := by
  constructor
  · refine (totalTrust_ofPartition_cross_iff hposH hposA c).2 ?_
    intro v
    fin_cases v <;> simp [mass_ofMap_eq, Fin.sum_univ_three, πH, πA, c] <;> norm_num
  · intro h; have := congrFun h 0; norm_num [πH, πA] at this

end Sharper

end

end Cleanroom.Trust.TtFiniteFrames
