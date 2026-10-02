import Cleanroom.Deference.DefSelfTrust.Pseudorandom
import Cleanroom.Trust.LegitFiniteDefect.Defs
import LogicalInduction.Properties.AffinePersistence

/-!
# `legit-li-register` · Gate: the legitimacy gate lives inside `ccee` (Target 6)

trust-lab-2-034 / root-deference-059: "`cee` restricted by an e.c. legitimacy weight is FAF's
`ccee`" — the legitimacy-modified Tower of [[li-deference]] §0.3 holds for free whenever
legitimacy is a *generable* weight, and the proposal has content only when it is not.

**(i) Imported, not restated** (one ledger row each, Status `imported`): `def-self-trust`'s
`legitimacyGated_tower_of_generable`, `legitimacyGated_condTower`, `gatedSelfTrust_productForm`,
`modifiedTower_decomposition`, `correctionFunction_idle` (`Legitimacy.lean`), and
`corr-li-shutdown`'s `legitWeight_pgenerable`, `legitWeight_eventually_one/zero`
(`Legitimacy.lean`: a day-indexed e.c. legitimacy sentence family's price ramp is generable and
tracks its decided value — 2-034's honest positive fragment (ii-c)). Those modules are over
`paperDP T` and are **not imported here** (memory; and nothing is re-proved).

**(ii-b) The dichotomy's hard half** (OPEN, `gatedUpdate_fails_at_truthStar_open`): a
non-generable gate exists — `def-self-trust`'s `truthStar_not_pgenerable` (imported here): the
truth stream of `li-pseudorandom`'s pseudorandom atom family is not a generable weight at FAF's
LIA over its own process. The theorem the corrigibility thesis needs is that the *gated update
identity fails there*. Its honest shape at the LI register: with the gate `w_n := 𝟙[x_n]` (the
atom family's own truth, `truthR`), the gated net update from the day-`n` price to the
limiting belief, `w_n · (P_∞(φ_n) − P_n(φ_n))`, is **not** asymptotically `0` — because
`P_n(φ_n) ≈ p ∈ (0,1)` (pseudorandom frequency learning) while `P_∞(φ_n) = x_n` (decided), so
on the days `x_n = 1` (a positive fraction) the gated update is `≈ 1 − p`. At a *generable* gate
the corresponding identity is FAF's `ccee` (the imported rows). `def-self-trust`'s F13 names the
obstacle for the deferred-day family (pseudorandomness is diagonal); stated OPEN with this
diagnosis in `legit-li-register-open.txt`, not attempted. No squeeze: nothing here assumes the
tower fails.

**(ii-a) Sound but not safe** (finite, N−, `SoundNotSafe`): a two-world frame over
`legit-finite-defect`'s `defect` in which a self-reported gate that passes everywhere endorses
the gated report (the finite calibration identity on the gated class is a zero) while the gated
report *is* the corrupt value on every world; on the world gates it is not endorsed. The content
is the example.

**(iii)** "legitimate gating = generable ∧ computed outside the gated channel" is the scout's
reading — INTERPRETATION, ATTRIBUTION-UNVETTED, findings.
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Li.LiPseudorandom Cleanroom.Deference.DefSelfTrust
open Filter Topology

/-- **OPEN — the gated update identity fails at a non-generable gate** (Target 6 (ii-b)): over FAF's
LIA on `li-pseudorandom`'s atom process with the pseudorandom truth stream `truthStar a g p`,
`p ∈ (0,1)`, the net update from the day-`n` price of the day-`n` atom to its limiting belief,
gated by the atom's own truth, is not asymptotically zero. The gate is not generable
(`truthStar_not_pgenerable`); at a generable gate the analogous identity is FAF's `ccee`.
Route: `lic_learning_pseudorandom_frequency_of_historicalVerifiers` gives `P_n(φ_n) ≈ p` along
the family; the atom is decided at day `g n`, so `limitingBelief P (φ_n) = truthR x n`; the gated
difference is `truthR x n · (1 − P_n(φ_n)) ≈ truthR x n · (1 − p)`, frequently `≥ (1 − p)/2`.
Source: trust-lab-2-034 (ii-b); root-deference-059; `def-self-trust` 4c(ii) (unattempted there, F13); mandate Target 6 (ii-b)
Kind: OPEN
Fidelity: variant: the gated update to the *limiting* belief (the deferred-day family is `def-self-trust`'s F13 obstacle)
Hyps: n/a -/
theorem gatedUpdate_fails_at_truthStar_open (a g : ℕ → ℕ) (ha : Function.Injective a)
    (hg : ∀ j, j < g j) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ ((fun n => truthR (truthStar a g p) n *
        (limitingBelief (liaHistory (atomDP a (truthStar a g p) g)) (atomFamily a n) -
          liaHistory (atomDP a (truthStar a g p) g) n (atomFamily a n))) ≈ₙ (fun _ => 0)) := by
  sorry

/-! ## (ii-a) Sound but not safe: a two-world frame -/

namespace SoundNotSafe

open Cleanroom.Trust.LegitFiniteDefect Cleanroom.Found.LitDdbFrames

noncomputable section

/-- The principal: two equiprobable worlds, `0` clean and `1` corrupt.
Source: trust-lab-2-034 (ii-a); mandate Target 6 (ii-a)
Kind: D
Fidelity: n/a -/
def π2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The target: `1` on the clean world, `0` on the corrupt one.
Source: trust-lab-2-034 (ii-a)
Kind: D
Fidelity: n/a -/
def θ2 : Fin 2 → ℝ := ![1, 0]

/-- The gated process's report: the **corrupt value** on every world (`1 − θ`).
Source: trust-lab-2-034 (ii-a) ("the gated target still equals the corrupt value")
Kind: D
Fidelity: n/a -/
def Rcorrupt : Fin 2 → ℝ := ![0, 1]

/-- The self-reported gate: computed by the gated process, it passes everywhere.
Source: trust-lab-2-034 (ii-a) ("a self-reported gate … passes")
Kind: D
Fidelity: n/a -/
def selfGate : Fin 2 → ℝ := fun _ => 1

/-- **Sound**: on the gated class — the self-reported gate alone — the report is endorsed (the
finite calibration identity is an exact zero: `E(θ) = E(R) = ½`).
Source: trust-lab-2-034 (ii-a) ("the gated tower identity holds")
Kind: N−
Fidelity: variant: the finite calibration identity on the gated class, for the tower identity
Hyps: (a) none -/
theorem selfGate_endorsed : Endorses π2 θ2 Rcorrupt {selfGate} := by
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  simp only [defect, E, π2, θ2, Rcorrupt, selfGate, Fin.sum_univ_two]
  norm_num

/-- **Not safe**: the endorsed report is the corrupt value on the corrupt world (and wrong on the
clean one too).
Source: trust-lab-2-034 (ii-a)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem report_is_corrupt_value : Rcorrupt 1 = 1 ∧ θ2 1 = 0 ∧ Rcorrupt 0 = 0 ∧ θ2 0 = 1 := by
  simp [Rcorrupt, θ2]

/-- On the world gates (every non-negative weight), the corrupt report is **not** endorsed: the
point mass on the corrupt world has defect `−½`.
Source: trust-lab-2-034 (ii-a) (the contrast)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem not_endorsed_on_worldGates : ¬ Endorses π2 θ2 Rcorrupt worldGates := by
  intro h
  have := h (ind {1}) (ind_mem_worldGates _)
  simp only [defect, E, π2, θ2, Rcorrupt, ind, Fin.sum_univ_two] at this
  norm_num at this

end

end SoundNotSafe

end Cleanroom.Trust.LegitLiRegister
