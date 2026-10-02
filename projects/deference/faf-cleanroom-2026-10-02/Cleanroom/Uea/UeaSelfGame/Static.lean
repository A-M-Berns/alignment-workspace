import Cleanroom.Uea.UeaSelfGame.Repaired

/-!
# Theorem B: the fixed-instance margin theorem, with converse

Under the static belief `μ = (1-δ) δ_{π*} + δ Po`, an action `a' ≠ π*(s)` is supported only by `Po`, so
its conditional is the pure `Po`-conditional `pva/pa` (`cond_mu_ne`). With a positive `Po`-margin `m` and
`δ < m/U*`, every such conditional is `≤ U* − m < (1-δ) U* ≤ cond(π*(s))` (self-evidence), so `π*(s)` is
the strict argmax everywhere and the unique realized policy is `π*` (Theorem B). Conversely, a margin-zero
pair `(s, a')` ties or beats `π*(s)` for every `δ > 0`.

The margin is encoded as a `Prop` (`HasMargin m`) rather than a real-valued minimum over a possibly empty
index set (no `sInf`-of-empty junk); the index set carries `0 < pa s a'`, so unavailable actions never
enter with a `0/0`.

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, static belief; not
rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-- **`Po`-margin at least `m`**: for every `s` and every `a' ≠ π*(s)` with `Po(π'(s) = a') > 0`, the
`Po`-conditional value `E_{Po}[U | π'(s) = a'] = pva/pa` is at most `U* − m`. Vacuous (every `m`) when no
such pair exists — the note's `m := +∞`.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §4 ("`P_o`-margin")
Kind: D
Fidelity: exact (as a lower bound on the note's minimum; `+∞` is "every `m`")
Hyps: n/a -/
def HasMargin (m : ℝ) : Prop :=
  ∀ s a', a' ≠ G.piStar s → 0 < G.pa s a' → G.pva s a' / G.pa s a' ≤ G.Ustar - m
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_mu_ne {s : S} {a' : A} (h : a' ≠ G.piStar s) : condDen G.mu s a' = G.δ * G.pa s a' := by
  unfold mu; rw [G.condDen_muSelf, if_neg (Ne.symm h)]; ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_mu_ne {s : S} {a' : A} (h : a' ≠ G.piStar s) : G.condNum G.mu s a' = G.δ * G.pva s a' := by
  unfold mu; rw [G.condNum_muSelf, if_neg (Ne.symm h)]; ring

/-- **A deviation's conditional is a pure `Po`-conditional**: for available `a' ≠ π*(s)`,
`E_μ[U | π'(s) = a'] = E_{Po}[U | π'(s) = a'] = pva/pa` (the self-mass plays `π*(s)`, not `a'`).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §4 (Theorem B proof); §2 ("the value of `b` is computed by `P_o` alone")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_mu_ne {s : S} {a' : A} (h : a' ≠ G.piStar s) (hav : avail G.mu s a') :
    G.cond G.mu s a' = G.pva s a' / G.pa s a' := by
  unfold cond
  rw [G.condNum_mu_ne h, G.condDen_mu_ne h]
  have hd : G.δ * G.pa s a' ≠ 0 := by
    have : 0 < condDen G.mu s a' := hav
    rw [G.condDen_mu_ne h] at this
    exact ne_of_gt this
  have hδ : G.δ ≠ 0 := fun h0 => hd (by rw [h0, zero_mul])
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem avail_mu_ne_iff {s : S} {a' : A} (h : a' ≠ G.piStar s) :
    avail G.mu s a' ↔ 0 < G.δ ∧ 0 < G.pa s a' := by
  unfold avail
  rw [G.condDen_mu_ne h]
  constructor
  · intro hpos
    have h1 := G.δ_nonneg; have h2 := G.pa_nonneg s a'
    constructor
    · rcases h1.eq_or_lt with h1 | h1
      · rw [← h1, zero_mul] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h1
    · rcases h2.eq_or_lt with h2 | h2
      · rw [← h2, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h2
  · rintro ⟨h1, h2⟩; positivity

/-- Every conditional of a nonnegative belief is at most `U*` (`U ≤ U*` pointwise).
Source: [[updateless-self-game]] §4 (converse)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_le_Ustar {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') {s : S} {a : A} (h : avail μ s a) :
    G.cond μ s a ≤ G.Ustar := by
  unfold cond
  have hd : 0 < condDen μ s a := h
  rw [div_le_iff₀ hd]
  unfold condNum condDen
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun π' _ => ?_
  split_ifs
  · have := G.U_le_Ustar π'; have := hμ π'; nlinarith
  · simp

/-- **Theorem B (fixed-instance margin theorem)**: with `Po`-margin at least `m`, `0 < U*` and
`δ < m/U*` (which forces `m > 0`), under the static belief `π*(s)` is the strict Herrmann argmax at every situation: it is an
argmax, and every available `a' ≠ π*(s)` has a strictly smaller conditional. Hence the argmax is strict
everywhere (`theoremB_strictArgmax`) and the unique realized policy is `π*` (`theoremB_realizes`).
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, static belief; not
rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §4 (Theorem B); [[uea-inventory]] 025
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremB {m : ℝ} (hm : G.HasMargin m) (hU : 0 < G.Ustar)
    (hδ : G.δ < m / G.Ustar) (s : S) :
    G.IsArgmaxH G.mu s (G.piStar s) ∧
      ∀ a', avail G.mu s a' → a' ≠ G.piStar s → G.cond G.mu s a' < G.cond G.mu s (G.piStar s) := by
  have hlt : ∀ a', avail G.mu s a' → a' ≠ G.piStar s →
      G.cond G.mu s a' < G.cond G.mu s (G.piStar s) := by
    intro a' hav hne
    obtain ⟨hδpos, hpa⟩ := (G.avail_mu_ne_iff hne).1 hav
    rw [G.cond_mu_ne hne hav]
    have h1 := hm s a' hne hpa
    have h2 : G.Ustar - m < G.thr := by
      unfold thr
      rw [lt_div_iff₀ hU] at hδ
      nlinarith
    have h3 := (G.self_evidence s).2
    linarith
  refine ⟨⟨G.avail_muSelf_self G.piStar s, fun b hb => ?_⟩, hlt⟩
  by_cases hbe : b = G.piStar s
  · rw [hbe]
  · exact (hlt b hb hbe).le

/-- Theorem B, conclusion form: the argmax is strict at every situation.
Source: [[updateless-self-game]] §4 (Theorem B, "strict argmax at every situation")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremB_strictArgmax {m : ℝ} (hm : G.HasMargin m) (hU : 0 < G.Ustar)
    (hδ : G.δ < m / G.Ustar) : G.StrictArgmax G.mu := by
  intro s
  obtain ⟨hmax, hlt⟩ := G.theoremB hm hU hδ s
  refine ⟨G.piStar s, hmax, fun b hb => ?_⟩
  by_contra hne
  have h1 := hlt b hb.1 hne
  have h2 := hb.2 (G.piStar s) hmax.1
  linarith

/-- Theorem B, conclusion form: the unique realized policy is `π*`.
Source: [[updateless-self-game]] §4 (Theorem B, "the realized policy is exactly `π*`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremB_realizes {m : ℝ} (hm : G.HasMargin m) (hU : 0 < G.Ustar)
    (hδ : G.δ < m / G.Ustar) (π : S → A) (hπ : G.Realizes G.mu π) : π = G.piStar := by
  funext s
  obtain ⟨hmax, hlt⟩ := G.theoremB hm hU hδ s
  by_contra hne
  have h1 := hlt (π s) (hπ s).1 hne
  have h2 := (hπ s).2 (G.piStar s) hmax.1
  linarith

/-- `π*` itself is realized under the margin hypothesis (so "the unique realized policy is `π*`" is not
vacuous).
Source: [[updateless-self-game]] §4
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem theoremB_realizes_piStar {m : ℝ} (hm : G.HasMargin m) (hU : 0 < G.Ustar)
    (hδ : G.δ < m / G.Ustar) : G.Realizes G.mu G.piStar :=
  fun s => (G.theoremB hm hU hδ s).1

/-- **Converse of Theorem B**: if the margin is `0` at some `(s, a')` — all `Po`-mass playing `a' ≠ π*(s)`
sits on optimal policies, `pva/pa = U*` with `pa > 0` — then for every `δ > 0`, `a'` is available and its
conditional equals `U* ≥ cond(π*(s))`: `a'` ties or beats `π*(s)`, so `π*(s)` is not the strict argmax.
Scope: finite updateless self-game — static belief; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §4 ("Converse")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremB_converse {s : S} {a' : A} (hne : a' ≠ G.piStar s) (hpa : 0 < G.pa s a')
    (hzero : G.pva s a' / G.pa s a' = G.Ustar) (hδ : 0 < G.δ) :
    avail G.mu s a' ∧ G.cond G.mu s a' = G.Ustar ∧ G.cond G.mu s (G.piStar s) ≤ G.cond G.mu s a' ∧
      G.IsArgmaxH G.mu s a' := by
  have hav : avail G.mu s a' := (G.avail_mu_ne_iff hne).2 ⟨hδ, hpa⟩
  have hc : G.cond G.mu s a' = G.Ustar := by rw [G.cond_mu_ne hne hav, hzero]
  have hle : ∀ b, avail G.mu s b → G.cond G.mu s b ≤ G.cond G.mu s a' := by
    intro b hb; rw [hc]; exact G.cond_le_Ustar G.mu_nonneg hb
  exact ⟨hav, hc, hle _ (G.avail_muSelf_self G.piStar s), hav, hle⟩

end Game

end Cleanroom.Uea.UeaSelfGame
