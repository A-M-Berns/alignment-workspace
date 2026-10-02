import Cleanroom.Deference.DefFrozenSibling.OnG
import Cleanroom.Trust.LegitLiRegister.Idle
import Cleanroom.Trust.LegitLiRegister.PiOne
import Cleanroom.Trust.LegitLiRegister.Predication
import Cleanroom.Li.LiProjection.Subst

/-!
# `legit-li-register` · Witness: the one-way N+ / N− instances (heavy: imports the LIA compiler
through `def-frozen-sibling`'s `OnG.lean`)

Every witness that mentions `onGSystem` or FAF's LIA lives here and nowhere else (memory) — with
one exception: the Target 9 (iii) bridge's LIA witness (`truthProcess_bridge_alternating_lia`)
lives in `Schedule.lean`, whose imports already carry the compiler through `PaperInstances`.

* **Target 2, N+ (one-way)**: at `onGSystem` (shared process `base0`: alternating contract atoms
  decided at stage `n`; `A`, `Hplus` FAF's LIA; siblings perturbed to the decided value; horizon
  `succDeferral`, injective; every day timely at `ε ≡ 0`), the polarity pattern is even/odd, so
  both `H`-side certificates of `defect_agreeAlong_zero_onG_ofPattern` are discharged
  (`hpat₁_onG`, `hpat₀_onG`: one `MachineSentenceCodes.ifZero` on the parity rulers), and
  **the defect tends to `0`** (`defect_onG_tendsto_zero`). The witness inhabits the headline's
  full hypothesis package; as the dependency's F4 says, it lives in the regime where the pattern
  is e.c. — the only regime in which idleness is proved here, and believed the only one (findings
  F1: the grade-(a) statement is OPEN both ways).
* **Target 5 (i), N+**: the ledger-threshold monitors on the even days of `onGSystem`'s advised
  reasoner — "the settled value published under item `1` on day `n` exceeded `½`" — a real
  decided family, learned (`monitor_learned`).
* **Target 5 (ii), N−**: an atom no stage of `paperDP 𝗜𝚺₁` mentions, at FAF's LIA over it: both
  polarities are consistent with every stage (`li-projection`'s `exists_consistent_holds_atom`),
  so the price is pinned in `(0,1)` forever (`globalLegit_pinned_fresh`). Degenerate: nothing
  constrains the atom (the N+ — a genuinely independent Π₁ sentence of `𝗜𝚺₁` — was not attempted).
* **Target 8, satisfiable branch**: the decided literals of `base0` as the received feedback
  `ψ` (`decidedFeedback`): the received process is `onGSystem.processH` stage-wise, so every stage
  is satisfiable. `predicated_learns_feedback` (the predicated history prices what it received
  at `≈ 1`) is **N−**: the learned sentence is a conjunct of the conditioning prefix, and FAF's
  `conditionalQuote` returns `1` on its own conjuncts by its `else` clause (audit round 1: the
  constant-`½` market gives the same conclusion with no inductor property). The **N+** is section
  G: the prefix with a *nominal verdict atom* received on day `1` (`verdictFeedback`; stages stay
  satisfiable because the atom is fresh for `processH`, `verdict_hworld`), at which the predicated
  market learns the even-day monitors — a theorem family of the shared process that is **not** in
  the prefix (`predicated_learns_monitor`) — and no e.c. trader exploits it (`verdict_no_book`):
  the "all three horns, alive" configuration, inhabited.
* **Target 2, grade-(a) engine**: `horizon_price_agree_anticipation` instantiated at `onGSystem`
  (`horizon_price_agree_anticipation_onG`), section F.
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefFrozenSibling
  Cleanroom.Deference.DefTrackingPin Cleanroom.Li.LiProjection
open Filter Topology

/-! ## A. The successor horizon -/

/-- `succDeferral` is injective (the `hinj` of every witness).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem succDeferral_injective : Function.Injective succDeferral.f :=
  fun _ _ h => Nat.succ_injective h

/-- An image day of the successor horizon is any day `≥ 1`.
Source: none: infrastructure (FAF `deferralImageFlag_eq_one_iff`)
Kind: L
Fidelity: n/a -/
theorem deferralImageFlag_succ_iff (m : ℕ) : deferralImageFlag succDeferral m = 1 ↔ 1 ≤ m := by
  rw [deferralImageFlag_eq_one_iff]
  constructor
  · rintro ⟨k, hk, -⟩
    omega
  · intro h
    exact ⟨m - 1, by omega, by show m - 1 + 1 = m; omega⟩

/-- The preimage of `k + 1` under the successor horizon is `k`.
Source: none: infrastructure (FAF `deferralPreimage_at`)
Kind: L
Fidelity: n/a -/
theorem deferralPreimage_succ (k : ℕ) : deferralPreimage succDeferral (k + 1) = k :=
  deferralPreimage_at succDeferral succDeferral_injective k

/-- At `onGSystem` with the trivial ruler the horizon gate is zero exactly on days `≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem horizonGate_onG (m : ℕ) : horizonGate onGSystem (fun _ => 0) m = 0 ↔ 1 ≤ m := by
  rw [horizonGate_eq_zero_iff]
  show deferralImageFlag succDeferral m = 1 ∧ (0 : ℕ) = 0 ↔ 1 ≤ m
  rw [deferralImageFlag_succ_iff]
  simp

/-! ## B. Target 2: the certificates at `onGSystem` -/

/-- The positive-polarity family at `onGSystem` is the odd-day family `contract5 (m − 1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem horizonFamilyPos_onG (m : ℕ) :
    horizonFamilyPos onGSystem (fun _ => 0) m =
      if m % 2 = 1 then contract5 (m - 1) else ⊤ := by
  unfold horizonFamilyPos
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [if_neg, if_neg (by norm_num)]
    rintro ⟨h, -⟩
    rw [horizonGate_onG] at h
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hpre : deferralPreimage onGSystem.F (k + 1) = k := deferralPreimage_succ k
    have hg : horizonGate onGSystem (fun _ => 0) (k + 1) = 0 := (horizonGate_onG _).2 (by omega)
    rw [hpre, onG_truthAt]
    unfold Y0
    by_cases hk : k % 2 = 0
    · rw [if_pos ⟨hg, by rw [if_pos hk]⟩, if_pos (by omega), Nat.add_sub_cancel]
      rfl
    · rw [if_neg (fun h => by rw [if_neg hk] at h; exact absurd h.2 (by norm_num)),
        if_neg (by omega)]

/-- The negative-polarity family at `onGSystem` is the even-day (`≥ 2`) family `contract5 (m − 1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem horizonFamilyNeg_onG (m : ℕ) :
    horizonFamilyNeg onGSystem (fun _ => 0) m =
      if 1 ≤ m ∧ m % 2 = 0 then contract5 (m - 1) else ∼(⊤ : Sentence) := by
  unfold horizonFamilyNeg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [if_neg, if_neg (by omega)]
    rintro ⟨h, -⟩
    rw [horizonGate_onG] at h
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hpre : deferralPreimage onGSystem.F (k + 1) = k := deferralPreimage_succ k
    have hg : horizonGate onGSystem (fun _ => 0) (k + 1) = 0 := (horizonGate_onG _).2 (by omega)
    rw [hpre, onG_truthAt]
    unfold Y0
    by_cases hk : k % 2 = 0
    · rw [if_neg (fun h => by rw [if_pos hk] at h; exact absurd h.2 (by norm_num)),
        if_neg (by omega)]
    · rw [if_pos ⟨hg, by rw [if_neg hk]⟩, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
      rfl

/-- **The positive certificate at `onGSystem`**: the odd-day family is e.c. (`ifZero` on the parity
ruler `flip_ruler`, the contract reindexed by `m ↦ m − 1`).
Source: mandate Target 2 (witness); `def-frozen-sibling` `hpat₁_onG` (the pattern)
Kind: L
Fidelity: n/a -/
theorem hpat₁_onG : MachineSentenceCodes (horizonFamilyPos onGSystem (fun _ => 0)) :=
  (MachineSentenceCodes.ifZero (contract5_codes.comp (UnaryRuler.id.sub (UnaryRuler.const 1)))
    (MachineSentenceCodes.const ⊤) flip_ruler).of_eq (fun m => by
      rw [horizonFamilyPos_onG]
      by_cases h : m % 2 = 0
      · have h1 : m % 2 ≠ 1 := by omega
        simp [h1]
      · have h1 : m % 2 = 1 := by omega
        simp [h1])

/-- **The negative certificate at `onGSystem`**: the even-day family is e.c. (`ifZero` on the ruler
`m ↦ (m mod 2) + (1 − m)`, zero exactly on even days `≥ 1`).
Source: mandate Target 2 (witness); `def-frozen-sibling` `hpat₀_onG` (the pattern)
Kind: L
Fidelity: n/a -/
theorem hpat₀_onG : MachineSentenceCodes (horizonFamilyNeg onGSystem (fun _ => 0)) :=
  (MachineSentenceCodes.ifZero (contract5_codes.comp (UnaryRuler.id.sub (UnaryRuler.const 1)))
    (MachineSentenceCodes.const (∼(⊤ : Sentence)))
    (evenZero_ruler.add ((UnaryRuler.const 1).sub UnaryRuler.id))).of_eq (fun m => by
      rw [horizonFamilyNeg_onG]
      by_cases h : m % 2 = 0
      · by_cases h1 : 1 ≤ m
        · have hz : (if m % 2 = 0 then 0 else 1) + (1 - m) = 0 := by rw [if_pos h]; omega
          rw [if_pos hz, if_pos ⟨h1, h⟩]
        · have hz : (if m % 2 = 0 then 0 else 1) + (1 - m) ≠ 0 := by rw [if_pos h]; omega
          rw [if_neg hz, if_neg (fun hh => h1 hh.1)]
      · have hz : (if m % 2 = 0 then 0 else 1) + (1 - m) ≠ 0 := by rw [if_neg h]; omega
        rw [if_neg hz, if_neg (fun hh => h hh.2)])

/-- **Idleness at the inhabitant, `AgreeAlong` form**: the headline's full hypothesis package at
`onGSystem`, `ε ≡ 0`, `t ≡ 0`.
Source: mandate Target 2 (witness, N+)
Kind: N+
Fidelity: n/a
Hyps: (a) none (every certificate discharged) -/
theorem defect_onG_agreeAlong : AgreeAlong (fun _ => 0) (defect onGSystem) (fun _ => 0) :=
  defect_agreeAlong_zero_onG_ofPattern onGSystem (fun _ => 0) hε_onG hG_onG
    succDeferral_injective hpat₁_onG hpat₀_onG

/-- **The defect vanishes at the inhabitant** (Target 2's N+, one-way): `d_n → 0` at `onGSystem`.
Source: mandate Target 2 (`defect_onG_tendsto_zero`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem defect_onG_tendsto_zero : Tendsto (defect onGSystem) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (defect_onG_agreeAlong (r / 2) (half_pos hr))
  refine ⟨N, fun n hn => ?_⟩
  have hd : 0 ≤ defect onGSystem n := abs_nonneg _
  have h := hN n hn rfl
  rw [sub_zero, abs_of_nonneg hd] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hd]
  exact lt_of_le_of_lt h (half_lt_self hr)

/-! ## C. Target 5 (i): the ledger-threshold monitors at `onGSystem` -/

/-- **The monitor family**: on even days, "the settled value published under item `1` on day `n`
exceeds `½`" (`⌜α_{1,n} > ½⌝`); the filler `⊤` on odd days.
Source: mandate Target 5 (i) (witness); scout-fresh-eyes Q5 (i)
Kind: D
Fidelity: n/a -/
def monitor (n : ℕ) : Sentence := if n % 2 = 0 then (ledgerLuv 1 n).gt (1 / 2) else ⊤

/-- The monitor family is e.c.
Source: none: infrastructure (`def-tracking-pin` `ledgerLuv_gt_sentenceCodes`)
Kind: L
Fidelity: n/a -/
theorem monitor_codes : MachineSentenceCodes monitor :=
  (MachineSentenceCodes.ifZero (ledgerLuv_gt_sentenceCodes 1 (1 / 2))
    (MachineSentenceCodes.const ⊤) evenZero_ruler).of_eq (fun n => by
      unfold monitor
      by_cases h : n % 2 = 0 <;> simp [h])

/-- Every monitor is a theorem of the advised reasoner's process (on even days the settled value
is `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem monitor_thm (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory onGSystem.processH) :
    v.Holds (monitor n) := by
  unfold monitor
  by_cases h : n % 2 = 0
  · rw [if_pos h, ledgerLuv_gt_holds_iff _ _ _ 1 n (1 / 2) v hv]
    show (1 / 2 : ℚ) < frozenTable a0 Y0 1 n
    norm_num [frozenTable, Y0, h]
  · rw [if_neg h]
    exact PCWorld.holds_top v

/-- **Bounded legitimacy learned at the inhabitant** (Target 5 (i), N+): the advised reasoner's
price of the monitor tends to `1`.
Source: mandate Target 5 (i); scout-fresh-eyes Q5 (i)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem monitor_learned : (fun n => onGSystem.Hplus n (monitor n)) ≈ₙ (fun _ => 1) :=
  haveI := onGSystem.Hplus_inductor
  boundedLegit_learned onGSystem.Hplus onGSystem.processH monitor monitor_codes monitor_thm
    onGSystem.hworldH

/-! ## D. Target 5 (ii): an atom nothing mentions, at FAF's LIA over `paperDP 𝗜𝚺₁` -/

/-- A fresh atom code of family `17` (the schedule family of this package), payload `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def freshU : ℕ := freshAtomCode 17 0

/-- No stage of `paperDP 𝗜𝚺₁` mentions the fresh atom (tag `cleanroomBaseTag + 17 > 8`).
Source: none: infrastructure (`bli-found` `paperDP_tagFree`)
Kind: L
Fidelity: n/a -/
theorem atomFree_paperDP : AtomFreeProcess freshU (paperDP 𝗜𝚺₁) := by
  intro k φ hφ hmem
  have h := paperDP_tagFree 𝗜𝚺₁ (t := cleanroomBaseTag + 17)
    (by simp [cleanroomBaseTag]) k φ hφ
  exact h _ hmem (by simp [freshU, freshAtomCode_unpair])

/-- **Global legitimacy pinned at an unconstrained atom** (Target 5 (ii), N−): at FAF's LIA over
`paperDP 𝗜𝚺₁`, the price of the fresh atom is eventually in `[ε, ε']` with `0 < ε`, `ε' < 1`.
Degenerate: both polarities are consistent because nothing mentions the atom.
Source: mandate Target 5 (ii) (N−)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem globalLegit_pinned_fresh :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ε' : ℝ, ε' < 1 ∧ ∀ᶠ n in atTop,
      ε ≤ liaHistory (paperDP 𝗜𝚺₁) n (Formula.atom freshU) ∧
        liaHistory (paperDP 𝗜𝚺₁) n (Formula.atom freshU) ≤ ε' :=
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁)
  globalLegit_pinned (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) (Formula.atom freshU)
    (exists_consistent_holds_atom atomFree_paperDP (paperDP_hworld 𝗜𝚺₁))
    (exists_consistent_not_holds_atom atomFree_paperDP (paperDP_hworld 𝗜𝚺₁))

/-! ## E. Target 8: the satisfiable branch on a real family -/

/-- **The received feedback**: the decided literal of `base0` on each day (the contract on even
days, its negation on odd days).
Source: mandate Target 8 (witness: "the ledger literals as `ψ`"; here the decided contract literals)
Kind: D
Fidelity: n/a -/
def decidedFeedback (n : ℕ) : Sentence := if n % 2 = 0 then contract5 n else ∼contract5 n

/-- The received feedback is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem decidedFeedback_codes : MachineSentenceCodes decidedFeedback :=
  (MachineSentenceCodes.ifZero contract5_codes contract5_codes.neg evenZero_ruler).of_eq
    (fun n => by
      unfold decidedFeedback
      by_cases h : n % 2 = 0 <;> simp [h])

/-- Each received sentence is in the shared process's stage of its day.
Source: none: infrastructure (`def-frozen-sibling` `contract0_mem_of_even`, `contract0_neg_mem_of_odd`)
Kind: L
Fidelity: n/a -/
theorem decidedFeedback_mem (n : ℕ) : decidedFeedback n ∈ base0.D n := by
  unfold decidedFeedback
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos h]
    exact contract0_mem_of_even n h
  · rw [if_neg (by omega)]
    exact contract0_neg_mem_of_odd n h

/-- Every stage of the received process is satisfiable (it is the advised reasoner's process
stage-wise).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem received_hworld :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((receivedProcess onGSystem.processH decidedFeedback).D n) := by
  intro n
  obtain ⟨v, hv⟩ := onGSystem.hworldH n
  refine ⟨v, fun φ hφ => ?_⟩
  rw [receivedProcess, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with h | h
  · exact hv φ h
  · change φ ∈ ((List.range (n + 1)).map decidedFeedback).toFinset at h
    rw [List.mem_toFinset, List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    rw [List.mem_range] at hk
    exact hv _ (onGSystem.base_subset_processH n
      (base0.mono_le (by omega) (decidedFeedback_mem k)))

/-- **The predicated history prices what it received at `≈ 1`** (Target 8, satisfiable branch —
**N−**): at `onGSystem`'s advised reasoner conditioned on the decided literals, the price of each
received sentence tends to `1`. Degenerate (audit round 1): the learned sentence `ψ n` is a
conjunct of the conditioning prefix `C n`, so `conditionalQuote (P n) (ψ n) (C n)` is `1` by
FAF's `else` clause whenever `P n (ψ n ⋏ C n) ≥ P n (C n)` and otherwise the ratio of two prices
of propositionally equivalent sentences — the conclusion holds at the constant-`½` market with no
inductor property. Kept as the record of what conditioning on a sentence *means*; the alive
branch's N+ is `predicated_learns_monitor` below.
Source: mandate Target 8 (witness); audit round 1 B1/B2 (regraded)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem predicated_learns_feedback :
    (fun n => predicatedHistory onGSystem.Hplus decidedFeedback n (decidedFeedback n)) ≈ₙ
      (fun _ => 1) :=
  haveI := onGSystem.Hplus_inductor
  predication_learns_theorems onGSystem.Hplus onGSystem.processH decidedFeedback
    decidedFeedback_codes received_hworld decidedFeedback decidedFeedback_codes
    (fun n v hv => hv.holds_of_mem_stage ⟨n, by
      rw [receivedProcess, DeductiveProcess.union_stage]
      exact Finset.mem_union_left _ (onGSystem.base_subset_processH n (decidedFeedback_mem n))⟩)

/-! ## F. Target 2: the grade-(a) engine at the inhabitant -/

/-- **The anticipation engine at the inhabitant** (Target 2, grade (a), N+): at `onGSystem` the
advised reasoner's horizon price of the contract agrees with its own horizon expectation of the
settled-value item `α_{1,n}`, along the trivial ruler (every day timely at `ε ≡ 0`). Both sides
are day-`n + 1` quantities of FAF's LIA; neither is pinned to the truth by this row. What the
instance does *not* separate (audit round 2 N5): at `onGSystem` both sides reach the truth under
the discharged certificates, so it does not exhibit the engine's distinctive content — agreement
*without* a certificate; the honest N+ for that would be a system whose pattern is not e.c.
(`horizon_idleness_fails_exists_open`'s construction), which is not built.
Source: mandate Target 2 (the engine); audit round 1 N5; audit round 2 (adversarial) N5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem horizon_price_agree_anticipation_onG :
    AgreeAlong (fun _ => 0) (fun n => onGSystem.Hplus (onGSystem.F.f n) (onGSystem.contract n))
      (fun n => (ledgerLuv 1 n).expect onGSystem.Hplus (onGSystem.F.f n)) :=
  horizon_price_agree_anticipation onGSystem (fun _ => 0) hε_onG (UnaryRuler.const 0) hG_onG
    succDeferral_injective

/-! ## G. Target 8: the alive branch with a nominal verdict in the prefix, learning a family that
is not in the prefix (audit round 1) -/

/-- **The verdict atom**: a fresh atom of family `17`, payload `1` — "day-`0` feedback was
corrupt", received on day `1`, logically unlinked to every contract literal. This is *nominal*
retro-detection: the theory does not connect the verdict to `ψ_0` (the linked case is
`retroFamily`, which kills the market); the predicated market will hold both `ψ_0` and the verdict
at `≈ 1`.
Source: scout-legitimacy Q8 (horn 2); audit round 1 (adversarial) B2 ("a fresh atom appended as the verdict")
Kind: D
Fidelity: variant: the verdict is an atom the theory does not link to the feedback it is about
Hyps: n/a -/
def verdictU : ℕ := freshAtomCode 17 1

/-- **The received feedback with a verdict**: the decided literal of `base0` on every day except
day `1`, on which the verdict atom is received (`(n − 1) + (1 − n) = 0` iff `n = 1`).
Source: mandate Target 8 (witness); audit round 1 (adversarial) B2
Kind: D
Fidelity: n/a -/
def verdictFeedback (n : ℕ) : Sentence :=
  if (n - 1) + (1 - n) = 0 then Formula.atom verdictU else decidedFeedback n

/-- The verdict family is e.c. (one `ifZero` on the ruler `(n − 1) + (1 − n)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem verdictFeedback_codes : MachineSentenceCodes verdictFeedback :=
  (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (Formula.atom verdictU))
    decidedFeedback_codes
    ((UnaryRuler.id.sub (UnaryRuler.const 1)).add ((UnaryRuler.const 1).sub UnaryRuler.id))).of_eq
    (fun n => by
      unfold verdictFeedback
      rfl)

/-- Off day `1` the verdict family is the decided feedback.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem verdictFeedback_of_ne (n : ℕ) (h : n ≠ 1) : verdictFeedback n = decidedFeedback n := by
  unfold verdictFeedback
  rw [if_neg]
  omega

/-- On day `1` the verdict family is the verdict atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem verdictFeedback_one : verdictFeedback 1 = Formula.atom verdictU := by
  simp [verdictFeedback]

/-- **The advised reasoner's process never mentions the verdict atom**: `base0` is tag-free of
family `17` (`base0_tagFree`) and every ledger literal is of family `ledgerFamily`.
Source: none: infrastructure (`def-frozen-sibling` `base0_tagFree`; `li-quote-lane` `ledgerSchedule_families`)
Kind: L
Fidelity: n/a -/
theorem processH_onG_atomFree : AtomFreeProcess verdictU onGSystem.processH := by
  intro k φ hφ
  have htag : TagFreeSentence (cleanroomBaseTag + 17) φ := by
    change φ ∈ (extendBy base0 (ledgerSchedule _ _)).D k at hφ
    rw [extendBy_D, Finset.mem_union] at hφ
    rcases hφ with h | h
    · exact base0_tagFree (by simp [cleanroomBaseTag])
        (by simp [cleanroomBaseTag, contractFamily]) k φ h
    · rw [Finset.mem_image] at h
      obtain ⟨⟨f, p, b⟩, hx, rfl⟩ := h
      have hf : f = ledgerFamily := ledgerSchedule_families _ _ f ⟨k, (f, p, b), hx, rfl⟩
      subst hf
      cases b
      · simp only [literalOf_false]
        exact (freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, ledgerFamily])).neg
      · simp only [literalOf_true]
        exact freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, ledgerFamily])
  exact fun hmem => htag _ hmem (by simp [verdictU, freshAtomCode_unpair])

/-- **Every stage of the received process with the verdict is satisfiable**: a world of
`processH` with the verdict atom forced true is still a world of `processH` (the atom is fresh,
`li-projection`'s `consistentWith_setAtom_iff`) and holds every received sentence.
Source: none: infrastructure; audit round 1 (adversarial) B2
Kind: L
Fidelity: n/a -/
theorem verdict_hworld :
    ∀ n, ∃ v : PCWorld,
      v.ConsistentWith ((receivedProcess onGSystem.processH verdictFeedback).D n) := by
  intro n
  obtain ⟨v, hv⟩ := onGSystem.hworldH n
  have hv' : (setAtom v verdictU true).ConsistentWith (onGSystem.processH.D n) :=
    (consistentWith_setAtom_iff processH_onG_atomFree v true n).mp hv
  refine ⟨setAtom v verdictU true, fun φ hφ => ?_⟩
  rw [receivedProcess, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with h | h
  · exact hv' φ h
  · change φ ∈ ((List.range (n + 1)).map verdictFeedback).toFinset at h
    rw [List.mem_toFinset, List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    rw [List.mem_range] at hk
    by_cases h1 : k = 1
    · subst h1
      rw [verdictFeedback_one]
      exact setAtom_holds_atom_true v verdictU
    · rw [verdictFeedback_of_ne k h1]
      exact hv' _ (onGSystem.base_subset_processH n
        (base0.mono_le (by omega) (decidedFeedback_mem k)))

/-- **The predicated market with a nominal verdict learns the monitors** (Target 8, **N+** for
the alive branch): at `onGSystem`'s advised reasoner conditioned on the decided literals with the
verdict atom received on day `1`, the price of the even-day monitor `⌜α_{1,n} > ½⌝` — a theorem
of the shared process that is **not** in the conditioning prefix — tends to `1`. Which branch of
`conditionalQuote` fires on a given day is not controlled: in the ratio branch
(`P n (monitor n ⋏ C n) / P n (C n)` at FAF's LIA) the content is provability induction at the
conditioned inductor; in the junk branch (`P n (monitor n ⋏ C n) ≥ P n (C n)`, which coherence
does not exclude, the two sentences being theory-equivalent) the value is `1` by definition. The
N+ stands on the configuration: FAF's LIA, a verdict in the prefix, satisfiable stages, a learned
family outside the prefix, and a conclusion that fails at an incoherent market (`P n (φ ⋏ C) = 0`
with `P n C = 1` quotes `0`). The odd-day half of `monitor` is the filler `⊤`; the even days carry
the content.
Source: mandate Target 8 (N+); audit round 1 B1 ("the real N+ the branch theorem is about"); audit round 2 N2/N3
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem predicated_learns_monitor :
    (fun n => predicatedHistory onGSystem.Hplus verdictFeedback n (monitor n)) ≈ₙ
      (fun _ => 1) :=
  haveI := onGSystem.Hplus_inductor
  predication_learns_theorems onGSystem.Hplus onGSystem.processH verdictFeedback
    verdictFeedback_codes verdict_hworld monitor monitor_codes
    (fun n v hv => monitor_thm n v (consistentWithTheory_of_received hv))

/-- **No book at the verdict configuration** (Target 8): with the nominal verdict in the prefix
and every stage satisfiable, no e.c. trader exploits the predicated market over the received
process — horns 1–3 hold together at an inhabited configuration (under the asymptotic reading of
horn 3).
Source: scout-legitimacy Q8 (the pre-approved consistency outcome); audit round 1 (adversarial) B2
Kind: L (instance of `predication_no_book`)
Fidelity: as `predication_no_book`
Hyps: (a) none -/
theorem verdict_no_book :
    ∀ Tr : Trader, EfficientlyComputable Tr →
      ¬ Tr.Exploits (predicatedHistory onGSystem.Hplus verdictFeedback)
        (receivedProcess onGSystem.processH verdictFeedback) :=
  haveI := onGSystem.Hplus_inductor
  predication_no_book onGSystem.Hplus onGSystem.processH verdictFeedback verdictFeedback_codes

end Cleanroom.Trust.LegitLiRegister
