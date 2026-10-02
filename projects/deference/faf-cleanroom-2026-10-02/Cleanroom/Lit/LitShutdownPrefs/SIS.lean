import Cleanroom.Lit.LitShutdownPrefs.Weak

/-!
# The shutdown-influencing state and the First Theorem (Targets 2–3)

Thornley 2023 §5–6 and Appendix A. The state `SIS R` carries the three button probabilities
`0 ≤ f < g < h ≤ 1` and two base lotteries `P₀ U₀ : Lottery R` over the rest of the trajectory;
the predicted pressed/unpressed lotteries are the *labelled* push-forwards
`P a = P₀.map (a, ·)`, `U a = U₀.map (a, ·)` (the clause "these actions have no effect on the
probabilities of each future trajectory conditional on reaching each state", l. 96, is this
relabelling, so Lemma 1's "differ only with respect to the timestep-1 action" is literal), and
an action *is* its Backward-Induction mixture `act a = prob a • P a + (1 − prob a) • U a`.

* `lemma1_P`, `lemma1_U`, `lemma1_mix` — Lemma 1 (A1): all `P a` mutually indifferent, all `U a`
  mutually indifferent, and `c P a + (1−c) U a ~ c P b + (1−c) U b`; from IABM + IBIL through the
  pointwise lift `Weak.indiff_map_of_pointwise`.
* `lemma2_*` — Lemma 2 (A2): whichever of the four relations holds between some `U a`/`P a` pair
  holds between every pair (Transitivity, PI/IP/II).
* `first_theorem_averse`, `first_theorem_seeking` — the First Theorem (A3, A4) under
  `Weak.Transitive ∧ IABM ∧ IBILsub ∧ StrictMonotone`, as the composition Lemma 2 + StrictMonotone +
  Lemma 1 + IP-transitivity; the Better-Chances corollaries follow since Better Chances implies
  StrictMonotone.

`Fidelity: variant: OSI and Backward Induction are definitional (menu-free relation; action =
predicted lottery)` on every headline, per the mandate. The conclusion is a preference
statement (`lt (act Prevent) (act Leave) ∧ lt (act Prevent) (act Cause)`); "deterministically
chooses" is Thornley's behavioural reading of `lt` (l. 592: "By our assumption linking
preferences and choice-dispositions").
-/

namespace Cleanroom.Lit.LitShutdownPrefs

/-- The three actions available in a shutdown-influencing state.
Source: Thornley 2023 §5 ll. 84–92
Kind: D
Fidelity: exact -/
inductive Act
  | Leave
  | Prevent
  | Cause
  deriving DecidableEq

/-- A shutdown-influencing state: button probabilities `0 ≤ f < g < h ≤ 1` for Prevent/Leave/Cause
and base lotteries `P₀` (rest of trajectory after a press) and `U₀` (after no press) over `R`.
Source: Thornley 2023 §5 ll. 82–106; [[lit-shutdown-prefs-mandate]] Target 2
Kind: D
Fidelity: variant: the paper's `U`/`P` lotteries are predicted future *choices*; that they differ
across actions only by the timestep-1 label (the "no effect conditional on reaching each state"
clause, l. 96, and App. A A1's "exactly like … except") is built into the carrier as the shared
`P₀`, `U₀` relabelled by `a`. The label `a` is kept so that IABM and Lemma 1 are not vacuous
(audit round 1, fidelity non-blocking 4) -/
structure SIS (R : Type) where
  /-- pressing probability under Prevent -/
  f : ℝ
  /-- pressing probability under Leave -/
  g : ℝ
  /-- pressing probability under Cause -/
  h : ℝ
  f_nonneg : 0 ≤ f
  f_lt_g : f < g
  g_lt_h : g < h
  h_le_one : h ≤ 1
  /-- the predicted pressed lottery, before labelling by the timestep-1 action -/
  P₀ : Lottery R
  /-- the predicted unpressed lottery, before labelling by the timestep-1 action -/
  U₀ : Lottery R

namespace SIS

open Lottery Weak

variable {R : Type} (S : SIS R)

/-- The predicted pressed lottery after action `a`: `P₀` relabelled by `a`.
Source: Thornley 2023 §5 ll. 100–104 (`PPrevent`, `PLeave`, `PCause`)
Kind: D
Fidelity: exact -/
noncomputable def P (a : Act) : Lottery (Act × R) := S.P₀.map (fun r => (a, r))

/-- The predicted unpressed lottery after action `a`: `U₀` relabelled by `a`.
Source: Thornley 2023 §5 ll. 100–104 (`UPrevent`, `ULeave`, `UCause`)
Kind: D
Fidelity: exact -/
noncomputable def U (a : Act) : Lottery (Act × R) := S.U₀.map (fun r => (a, r))

/-- The pressing probability of each action.
Source: Thornley 2023 §5
Kind: D -/
def prob : Act → ℝ
  | .Leave => S.g
  | .Prevent => S.f
  | .Cause => S.h

/-- Each pressing probability lies in `[0, 1]`.
Source: none: infrastructure
Kind: L -/
theorem prob_mem (a : Act) : S.prob a ∈ Set.Icc (0 : ℝ) 1 := by
  have := S.f_nonneg; have := S.f_lt_g; have := S.g_lt_h; have := S.h_le_one
  cases a <;> simp only [prob] <;> constructor <;> linarith

/-- `1 − f ∈ [0, 1]`.
Source: none: infrastructure
Kind: L -/
theorem one_sub_prob_mem (a : Act) : 1 - S.prob a ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := S.prob_mem a; constructor <;> linarith

/-- **Backward Induction, definitional**: the lottery given by action `a` is
`prob a • P a + (1 − prob a) • U a`.
Source: Thornley 2023 §6 ll. 125–131 (`fPPrevent+(1−f)UPrevent`, …)
Kind: D
Fidelity: variant: Backward Induction is definitional (action = predicted lottery) -/
noncomputable def act (a : Act) : Lottery (Act × R) :=
  mix (S.prob a) (S.prob_mem a) (S.P a) (S.U a)

/-- **Shutdown-averse**: the agent (strictly) prefers Prevent to each of Leave and Cause.
"Deterministically chooses Prevent" is Thornley's behavioural reading of this preference.
Source: Thornley 2023 §5 l. 88, App. A l. 592
Kind: D
Fidelity: exact (as a preference statement) -/
def ShutdownAverse (le : Lottery (Act × R) → Lottery (Act × R) → Prop) : Prop :=
  lt le (S.act .Prevent) (S.act .Leave) ∧ lt le (S.act .Prevent) (S.act .Cause)

/-- **Shutdown-seeking**: the agent (strictly) prefers Cause to each of Leave and Prevent.
Source: Thornley 2023 §5 l. 92, App. A l. 612
Kind: D
Fidelity: exact (as a preference statement) -/
def ShutdownSeeking (le : Lottery (Act × R) → Lottery (Act × R) → Prop) : Prop :=
  lt le (S.act .Cause) (S.act .Leave) ∧ lt le (S.act .Cause) (S.act .Prevent)

section Lemmas

variable {le : Lottery (Act × R) → Lottery (Act × R) → Prop}

/-- Relabelling `P a` by `a'` gives `P a'`.
Source: Thornley 2023 App. A A1 ("`PPrevent` is exactly like `PLeave` … except …")
Kind: L -/
theorem P_map (a a' : Act) : (S.P a).map (fun x : Act × R => (a', x.2)) = S.P a' := by
  ext1
  simp only [P, map_p]
  rw [← Finsupp.mapDomain_comp]
  rfl

/-- Relabelling `U a` by `a'` gives `U a'`.
Source: Thornley 2023 App. A A1
Kind: L -/
theorem U_map (a a' : Act) : (S.U a).map (fun x : Act × R => (a', x.2)) = S.U a' := by
  ext1
  simp only [U, map_p]
  rw [← Finsupp.mapDomain_comp]
  rfl

/-- **Lemma 1 (pressed half)**: all predicted pressed lotteries are mutually indifferent.
Source: Thornley 2023 App. A A1 (Lemma 1)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem lemma1_P (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a a' : Act) :
    indiff le (S.P a) (S.P a') := by
  rw [← S.P_map a a']
  exact indiff_map_of_pointwise hT hI _ _ (S.P a) rfl (fun t _ => hA t.1 a' t.2)

/-- **Lemma 1 (unpressed half)**: all predicted unpressed lotteries are mutually indifferent.
Source: Thornley 2023 App. A A1 (Lemma 1)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem lemma1_U (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a a' : Act) :
    indiff le (S.U a) (S.U a') := by
  rw [← S.U_map a a']
  exact indiff_map_of_pointwise hT hI _ _ (S.U a) rfl (fun t _ => hA t.1 a' t.2)

/-- **Lemma 1 (stored fact)**: `c P a + (1−c) U a ~ c P b + (1−c) U b` for any `c ∈ [0,1]`
(the paper states it for `c = f`, `a = Leave`, `b = Prevent`).
Source: Thornley 2023 App. A A1 ("one more fact to store up")
Kind: L
Fidelity: stronger (any `c`, any `a b`) -/
theorem lemma1_mix (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a b : Act) (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    indiff le (mix c hc (S.P a) (S.U a)) (mix c hc (S.P b) (S.U b)) := by
  have hc' : 1 - c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have h1 : indiff le (mix c hc (S.P a) (S.U a)) (mix c hc (S.P b) (S.U a)) :=
    hI _ _ (S.U a) c hc (S.lemma1_P hT hI hA a b)
  have h2 : indiff le (mix c hc (S.P b) (S.U a)) (mix c hc (S.P b) (S.U b)) := by
    rw [mix_comm c hc hc' (S.P b) (S.U a), mix_comm c hc hc' (S.P b) (S.U b)]
    exact hI _ _ _ (1 - c) hc' (S.lemma1_U hT hI hA a b)
  exact ii_trans hT h1 h2

/-- **Lemma 2, weak-preference transfer**: `U a ≽ P a → U b ≽ P b`.
Source: Thornley 2023 App. A A2 (Lemma 2)
Kind: L -/
theorem lemma2_le_UP (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a b : Act)
    (h : le (S.U a) (S.P a)) : le (S.U b) (S.P b) :=
  hT _ _ _ (S.lemma1_U hT hI hA b a).1 (hT _ _ _ h (S.lemma1_P hT hI hA a b).1)

/-- **Lemma 2, weak-preference transfer**: `P a ≽ U a → P b ≽ U b`.
Source: Thornley 2023 App. A A2 (Lemma 2)
Kind: L -/
theorem lemma2_le_PU (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a b : Act)
    (h : le (S.P a) (S.U a)) : le (S.P b) (S.U b) :=
  hT _ _ _ (S.lemma1_P hT hI hA b a).1 (hT _ _ _ h (S.lemma1_U hT hI hA a b).1)

/-- **Lemma 2 (preference)**: if `U a ≻ P a` for some `a` then `U b ≻ P b` for every `b`.
Source: Thornley 2023 App. A A2 (Lemma 2)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem lemma2_lt_UP (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a b : Act)
    (h : lt le (S.U a) (S.P a)) : lt le (S.U b) (S.P b) :=
  ⟨S.lemma2_le_UP hT hI hA a b h.1, fun h' => h.2 (S.lemma2_le_PU hT hI hA b a h')⟩

/-- **Lemma 2 (dispreference)**: if `P a ≻ U a` for some `a` then `P b ≻ U b` for every `b`.
Source: Thornley 2023 App. A A2 (Lemma 2)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem lemma2_lt_PU (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a b : Act)
    (h : lt le (S.P a) (S.U a)) : lt le (S.P b) (S.U b) :=
  ⟨S.lemma2_le_PU hT hI hA a b h.1, fun h' => h.2 (S.lemma2_le_UP hT hI hA b a h')⟩

/-- **Lemma 2 (indifference)**: if `U a ~ P a` for some `a` then `U b ~ P b` for every `b`.
Source: Thornley 2023 App. A A2 (Lemma 2)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem lemma2_indiff (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a b : Act)
    (h : indiff le (S.U a) (S.P a)) : indiff le (S.U b) (S.P b) :=
  ⟨S.lemma2_le_UP hT hI hA a b h.1, S.lemma2_le_PU hT hI hA a b h.2⟩

/-- **Lemma 2 (gap)**: if there is a preferential gap between `U a` and `P a` for some `a` then
there is one between `U b` and `P b` for every `b`.
Source: Thornley 2023 App. A A2 (Lemma 2, "by contraposition")
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem lemma2_gap (hT : Weak.Transitive le) (hI : IBILsub le) (hA : IABM le) (a b : Act)
    (h : gap le (S.U a) (S.P a)) : gap le (S.U b) (S.P b) :=
  ⟨fun h' => h.1 (S.lemma2_le_UP hT hI hA b a h'), fun h' => h.2 (S.lemma2_le_PU hT hI hA b a h')⟩

end Lemmas

section FirstTheorem

variable {le : Lottery (Act × R) → Lottery (Act × R) → Prop}

/-- The action lottery written with the unpressed lottery first: `act a = (1 − prob a) U a + prob a P a`.
Source: none: infrastructure
Kind: L -/
theorem act_eq_mix_U_P (a : Act) :
    S.act a = mix (1 - S.prob a) (S.one_sub_prob_mem a) (S.U a) (S.P a) :=
  mix_comm _ _ _ _ _

/-- **First Theorem, clause 1 (shutdown-averse)**: under Transitivity, IABM, IBIL and Strict
Monotonicity, if the agent prefers some predicted unpressed lottery `U a` to its corresponding
pressed lottery `P a`, it prefers Prevent to each of Leave and Cause. Composition: Lemma 2 ⇒
`U Leave ≻ P Leave`; Strict Monotonicity (`1−f > 1−g`) ⇒ `f P Leave + (1−f) U Leave ≻ act Leave`;
Lemma 1 ⇒ `act Prevent ~ f P Leave + (1−f) U Leave`; IP-transitivity. Likewise against Cause.
Source: Thornley 2023 §6 l. 175 (First Theorem, clause 1), App. A A3 ll. 583–596; corr-refs-049,
corr-core-028
Kind: C
Fidelity: variant: OSI and Backward Induction are definitional (menu-free relation; action =
predicted lottery); stated under StrictMonotone, weaker than the paper's Better Chances
Hyps: (a) all: Weak.Transitive, IABM, IBILsub, StrictMonotone are the paper's antecedents (StrictMonotone
is implied by Better Chances, `Weak.strictMonotone_of_betterChances`) -/
theorem first_theorem_averse (hT : Weak.Transitive le) (hA : IABM le) (hI : IBILsub le)
    (hM : StrictMonotone le) (h : ∃ a, lt le (S.U a) (S.P a)) : S.ShutdownAverse le := by
  obtain ⟨a, ha⟩ := h
  have hf := S.f_nonneg; have hfg := S.f_lt_g; have hgh := S.g_lt_h; have hh := S.h_le_one
  have hf' : 1 - S.f ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hfI : S.f ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- Lemma 1: act Prevent ~ f P b + (1−f) U b for any b
  have hPrev : ∀ b, indiff le (S.act .Prevent) (mix S.f hfI (S.P b) (S.U b)) := fun b =>
    S.lemma1_mix hT hI hA .Prevent b S.f hfI
  constructor
  · -- against Leave
    have hL : lt le (S.U .Leave) (S.P .Leave) := S.lemma2_lt_UP hT hI hA a .Leave ha
    have hg' : 1 - S.g ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hstep : lt le (mix (1 - S.f) hf' (S.U .Leave) (S.P .Leave))
        (mix (1 - S.g) hg' (S.U .Leave) (S.P .Leave)) :=
      hM _ _ _ _ hf' hg' (by linarith) hL
    rw [← mix_comm S.f hfI hf' (S.P .Leave) (S.U .Leave)] at hstep
    rw [S.act_eq_mix_U_P .Leave]
    exact ip_trans hT (hPrev .Leave) hstep
  · -- against Cause
    have hC : lt le (S.U .Cause) (S.P .Cause) := S.lemma2_lt_UP hT hI hA a .Cause ha
    have hh' : 1 - S.h ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hstep : lt le (mix (1 - S.f) hf' (S.U .Cause) (S.P .Cause))
        (mix (1 - S.h) hh' (S.U .Cause) (S.P .Cause)) :=
      hM _ _ _ _ hf' hh' (by linarith) hC
    rw [← mix_comm S.f hfI hf' (S.P .Cause) (S.U .Cause)] at hstep
    rw [S.act_eq_mix_U_P .Cause]
    exact ip_trans hT (hPrev .Cause) hstep

/-- **First Theorem, clause 2 (shutdown-seeking)**: under the same four conditions, if the agent
prefers some predicted pressed lottery `P a` to its corresponding unpressed lottery `U a`, it
prefers Cause to each of Leave and Prevent.
Source: Thornley 2023 §6 l. 175 (First Theorem, clause 2), App. A A4 ll. 600–616; corr-refs-049
Kind: C
Fidelity: variant: OSI and Backward Induction are definitional (menu-free relation; action =
predicted lottery); stated under StrictMonotone
Hyps: (a) all -/
theorem first_theorem_seeking (hT : Weak.Transitive le) (hA : IABM le) (hI : IBILsub le)
    (hM : StrictMonotone le) (h : ∃ a, lt le (S.P a) (S.U a)) : S.ShutdownSeeking le := by
  obtain ⟨a, ha⟩ := h
  have hf := S.f_nonneg; have hfg := S.f_lt_g; have hgh := S.g_lt_h; have hh := S.h_le_one
  have hhI : S.h ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hCause : ∀ b, indiff le (S.act .Cause) (mix S.h hhI (S.P b) (S.U b)) := fun b =>
    S.lemma1_mix hT hI hA .Cause b S.h hhI
  constructor
  · have hL : lt le (S.P .Leave) (S.U .Leave) := S.lemma2_lt_PU hT hI hA a .Leave ha
    have hgI : S.g ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hstep : lt le (mix S.h hhI (S.P .Leave) (S.U .Leave))
        (mix S.g hgI (S.P .Leave) (S.U .Leave)) :=
      hM _ _ _ _ hhI hgI hgh hL
    exact ip_trans hT (hCause .Leave) hstep
  · have hP : lt le (S.P .Prevent) (S.U .Prevent) := S.lemma2_lt_PU hT hI hA a .Prevent ha
    have hfI : S.f ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hstep : lt le (mix S.h hhI (S.P .Prevent) (S.U .Prevent))
        (mix S.f hfI (S.P .Prevent) (S.U .Prevent)) :=
      hM _ _ _ _ hhI hfI (by linarith) hP
    exact ip_trans hT (hCause .Prevent) hstep

/-- **First Theorem under Better Chances** (the paper's own hypothesis), clause 1.
Source: Thornley 2023 §6 l. 175
Kind: C
Fidelity: variant: OSI and Backward Induction are definitional
Hyps: (a) all -/
theorem first_theorem_averse_bc (hT : Weak.Transitive le) (hA : IABM le) (hI : IBILsub le)
    (hB : BetterChances le) (h : ∃ a, lt le (S.U a) (S.P a)) : S.ShutdownAverse le :=
  S.first_theorem_averse hT hA hI (strictMonotone_of_betterChances hB) h

/-- **First Theorem under Better Chances** (the paper's own hypothesis), clause 2.
Source: Thornley 2023 §6 l. 175
Kind: C
Fidelity: variant: OSI and Backward Induction are definitional
Hyps: (a) all -/
theorem first_theorem_seeking_bc (hT : Weak.Transitive le) (hA : IABM le) (hI : IBILsub le)
    (hB : BetterChances le) (h : ∃ a, lt le (S.P a) (S.U a)) : S.ShutdownSeeking le :=
  S.first_theorem_seeking hT hA hI (strictMonotone_of_betterChances hB) h

end FirstTheorem

end SIS

end Cleanroom.Lit.LitShutdownPrefs
