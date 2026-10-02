import Cleanroom.Uea.UeaSelfGame.Herrmann

/-!
# The two floored notions at pure policies, and the inclusion conjecture at `|S| = 1`

Repair round 2 of the `uea-self-game` package (faf-cleanroom run, 2026-10-01); round-2 adversarial audit
N3 and N4.

* **N3, the bridge.** `IsPureFPfloored π` takes the maximum over *available* actions (Herrmann, the note's
  default and the pure script's `floored_fixed_points(…, convention='herrmann')`), while `IsFlooredFPext σ`
  takes `maxF` over *all* actions (the extension, `floored_allowed`). At a pure policy the extension
  notion is the stronger one: `IsFlooredFPext.isPureFPfloored` proves
  `IsFlooredFPext (pureMix π) → IsPureFPfloored π` (the extension maximum dominates the Herrmann one, and
  `Fext (δ_π) s (π s) = cond (μ_π) s (π s)`, so each extension branch lands in a Herrmann branch the pure
  definition accepts). The converse fails: on the `|S| = 1` instance of `Herrmann.lean` (`U(a) = 9/10`,
  `U(b) = 1`, `Po = δ_a`), `a` is a pure floored fixed point iff `1/10 ≤ δ`
  (`OneSituation.isPureFPfloored_iff`) but `δ_a` is never a floored extension fixed point
  (`OneSituation.not_isFlooredFPext_pure`: `Fext (δ_a) b = U(b) = 1 > thr`, so the argmax branch forces
  `supp ⊆ {b}`). Consequence for the ledger: `theoremD_pure` (hypothesis `IsPureFPfloored`) covers the
  extension-pure case through the bridge, and `floored_mixed_bound_open` at a pure `σ` is implied by
  `theoremD_pure`.
* **N4, the inclusion conjecture at `|S| = 1`.** `inclusion_open` is trivially true on one situation: the
  chosen maximizer `π*` is itself a pure extension fixed point of every game on `Fin 1`
  (`exists_isFPext_pureMix_fin1`), with no hypothesis at all — `Fext (δ_{π*}) s (π* s) = U*` because on one
  situation the fibre `π'(s) = π*(s)` is `{π*}`, while every `Fext (δ_π) s b ≤ U*` (`Fext_pureMix_le_Ustar`,
  general). So the conjecture's content is `|S| ≥ 2`.

Scope: finite updateless self-game — floored agent in both conventions; the continuous extension; not
rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30; repair round 2, 2026-10-01).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pureMix_self_pos (π : S → A) (s : S) : 0 < pureMix π s (π s) := by simp [pureMix]

/-- At the pure policy `π` the extended conditional of the own action is its pure conditional.
Source: none: infrastructure (`Fext_pureMix` at `a := π s`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Fext_pureMix_self (π : S → A) (s : S) :
    G.Fext (pureMix π) s (π s) = G.cond (G.muSelf π) s (π s) :=
  G.Fext_pureMix π (G.avail_muSelf_self π s)

/-- **Bridge between the two floored notions**: a floored *extension* fixed point at a pure policy is a
pure floored fixed point in the Herrmann sense. (The extension maximum `maxF` dominates the maximum over
available actions; the own action's `Fext` is its pure conditional; so the reset, argmax and equality
branches of `floored_allowed` under the extension each imply the corresponding Herrmann branch.) The
converse fails: `OneSituation.isPureFPfloored_iff` with `OneSituation.not_isFlooredFPext_pure`.
Scope: finite updateless self-game — floored agent; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: round-2 adversarial audit N3; [[updateless-self-game]] §1 ("Floored agent"), §7
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem IsFlooredFPext.isPureFPfloored [Nonempty A] {G : Game S A} {π : S → A}
    (h : G.IsFlooredFPext (pureMix π)) : G.IsPureFPfloored π := by
  intro s
  obtain ⟨_, hs⟩ := h
  obtain ⟨hlt, hgt, heq⟩ := hs s
  have hpos := pureMix_self_pos π s
  have hself := G.Fext_pureMix_self π s
  have hav := G.avail_muSelf_self π s
  -- an available action's `Fext` is its conditional and is below `maxF`
  have hle : ∀ b, avail (G.muSelf π) s b → G.cond (G.muSelf π) s b ≤ G.maxF (pureMix π) s := by
    intro b hb
    have := G.Fext_le_maxF (pureMix π) s b
    rwa [G.Fext_pureMix π hb] at this
  -- if the own action attains `maxF`, it is a Herrmann argmax
  have hargmax : G.Fext (pureMix π) s (π s) = G.maxF (pureMix π) s →
      G.IsArgmaxH (G.muSelf π) s (π s) := by
    intro h1
    refine ⟨hav, fun b hb => ?_⟩
    rw [← hself, h1]; exact hle b hb
  refine ⟨?_, ?_, ?_⟩
  · -- reset branch: every available conditional is below the threshold
    intro hall
    have hc : G.cond (G.muSelf π) s (π s) < G.thr := hall _ hav
    rcases lt_trichotomy (G.resid (pureMix π) s) 0 with hr | hr | hr
    · exact hlt hr _ hpos
    · rcases heq hr _ hpos with h1 | h1
      · exfalso
        unfold resid at hr
        rw [hself] at h1
        linarith
      · exact h1
    · exfalso
      have h1 := hgt hr _ hpos
      unfold resid at hr
      rw [hself] at h1
      linarith
  · -- argmax branch: some available conditional exceeds the threshold
    rintro ⟨a, ha, hthr⟩
    have hr : 0 < G.resid (pureMix π) s := by
      unfold resid
      have := hle a ha
      linarith
    exact hargmax (hgt hr _ hpos)
  · -- equality branch
    intro _ _
    rcases lt_trichotomy (G.resid (pureMix π) s) 0 with hr | hr | hr
    · exact Or.inr (hlt hr _ hpos)
    · rcases heq hr _ hpos with h1 | h1
      · exact Or.inl (hargmax h1)
      · exact Or.inr h1
    · exact Or.inl (hargmax (hgt hr _ hpos))

/-- `pva ≤ pa · U*`: the fibre's `Po`-mass weighted by utility is at most its mass times the optimum.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_le_pa_mul_Ustar (s : S) (a : A) : G.pva s a ≤ G.pa s a * G.Ustar := by
  unfold pva pa condNum condDen
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun π' _ => ?_
  split_ifs
  · exact mul_le_mul_of_nonneg_left (G.U_le_Ustar π') (G.Po_nonneg π')
  · simp

/-- At a pure policy every extended conditional is at most `U*` (a convex combination of utilities).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Fext_pureMix_le_Ustar (π : S → A) (s : S) (b : A) : G.Fext (pureMix π) s b ≤ G.Ustar := by
  unfold Fext
  split_ifs with hden
  · rw [G.Ucoord_pureMix]; exact G.U_le_Ustar _
  · have hpos : 0 < G.denMix (pureMix π) s b :=
      lt_of_le_of_ne (G.denMix_nonneg (isMixed_pureMix π) s b) (Ne.symm hden)
    rw [div_le_iff₀ hpos]
    unfold denMix
    have h1 := G.one_sub_δ_pos
    have hσ : 0 ≤ pureMix π s b := (isMixed_pureMix π).nonneg s b
    have hU : G.Ucoord (pureMix π) s b ≤ G.Ustar := by rw [G.Ucoord_pureMix]; exact G.U_le_Ustar _
    have hpva := G.pva_le_pa_mul_Ustar s b
    have hδ := G.δ_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hU (mul_nonneg h1.le hσ), mul_le_mul_of_nonneg_left hpva hδ]

end Game

/-! ### The inclusion conjecture at `|S| = 1` -/

namespace Game

variable {A : Type*} [Fintype A] [DecidableEq A] (G : Game (Fin 1) A)

/-- On one situation the fibre `π'(0) = a` is the single policy `![a]`, so `pa 0 a = Po ![a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_fin1 (a : A) : G.pa 0 a = G.Po ![a] := by
  unfold pa condDen
  rw [sum_fin1_arrow]
  simp

/-- On one situation `pva 0 a = Po ![a] · U ![a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_fin1 (a : A) : G.pva 0 a = G.Po ![a] * G.U ![a] := by
  unfold pva condNum
  rw [sum_fin1_arrow]
  simp

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem fin1_eq_vec (π : Fin 1 → A) : π = ![π 0] := by
  funext i; fin_cases i; rfl

/-- On one situation the extended conditional of `π*` at its own action is exactly `U*`.
Source: round-2 adversarial audit N4
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Fext_pureMix_piStar_fin1 : G.Fext (pureMix G.piStar) 0 (G.piStar 0) = G.Ustar := by
  have hav := G.avail_muSelf_self G.piStar 0
  have hpos : 0 < G.denMix (pureMix G.piStar) 0 (G.piStar 0) :=
    (G.availMix_pureMix_iff G.piStar 0 (G.piStar 0)).2 hav
  rw [G.Fext_eq_of_availMix hpos, div_eq_iff (ne_of_gt hpos)]
  unfold denMix
  rw [G.Ucoord_pureMix, Function.update_eq_self, G.pva_fin1, G.pa_fin1, ← fin1_eq_vec G.piStar]
  have hσ : pureMix G.piStar 0 (G.piStar 0) = 1 := by simp [pureMix]
  rw [hσ]
  unfold Ustar
  ring

/-- **The inclusion conjecture holds trivially at `|S| = 1`**: every game on one situation has a pure
extension fixed point, namely `π*` itself (no hypothesis: in particular no Herrmann fixed point is
needed). So `inclusion_open`'s content is `|S| ≥ 2`.
Scope: finite updateless self-game — continuous extension; not rOSI, not the sequential model of
`uea-cole-shadow`.
Source: round-2 adversarial audit N4 (i); [[uea-2-inventory]] 2-014, 2-015 (the conjecture)
Kind: P
Fidelity: stronger: unconditional at `|S| = 1` (the conjecture's hypothesis is not needed there)
Hyps: (a) -/
theorem exists_isFPext_pureMix_fin1 : ∃ π : Fin 1 → A, G.IsFPext (pureMix π) := by
  refine ⟨G.piStar, isMixed_pureMix _, fun s a ha b => ?_⟩
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  have ha' : a = G.piStar 0 := by
    unfold pureMix at ha; by_contra hne; simp [hne] at ha
  subst ha'
  rw [G.Fext_pureMix_piStar_fin1]
  exact G.Fext_pureMix_le_Ustar _ _ _

end Game

/-! ### The converse of the bridge fails: the `|S| = 1` instance -/

namespace OneSituation

variable {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Fext_pure_b : (game h0 h1).Fext (pureMix polA) 0 1 = 1 := by
  rw [(game h0 h1).Fext_eq_Ucoord_of_pa_eq_zero _ (pa_b h0 h1), Ucoord_pure_b]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Fext_pure_a : (game h0 h1).Fext (pureMix polA) 0 0 = 9 / 10 := by
  have hav : avail ((game h0 h1).muSelf polA) 0 0 := (game h0 h1).avail_muSelf_self polA 0
  rw [(game h0 h1).Fext_pureMix polA hav, cond_a]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem maxF_pure : (game h0 h1).maxF (pureMix polA) 0 = 1 := by
  apply le_antisymm
  · unfold Game.maxF
    rw [Finset.sup'_le_iff]
    simp only [Finset.mem_univ, true_implies, Fin.forall_fin_two]
    exact ⟨by rw [Fext_pure_a h0 h1]; norm_num, by rw [Fext_pure_b h0 h1]⟩
  · rw [← Fext_pure_b h0 h1]; exact (game h0 h1).Fext_le_maxF _ _ _

/-- **`a` is a pure floored fixed point (Herrmann) iff `1/10 ≤ δ`**: the only available action is `a` with
conditional `9/10`; below `δ = 1/10` the reset branch demands `π* = b`, which `a` is not.
Source: round-2 adversarial audit N3 ("`OneSituation` at any `δ > 1/10` has `IsPureFPfloored a`")
Kind: P
Fidelity: exact (the audit's "`δ > 1/10`" sharpened to an iff with `1/10 ≤ δ`)
Hyps: (a) -/
theorem isPureFPfloored_iff : (game h0 h1).IsPureFPfloored polA ↔ 1 / 10 ≤ δ := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have h0' := (h 0).1
    have : polA 0 = (game h0 h1).piStar 0 := by
      apply h0'
      simp only [Fin.forall_fin_two]
      exact ⟨fun _ => by rw [cond_a h0 h1, thr_eq h0 h1]; linarith,
        fun ha => absurd ha (not_avail_b h0 h1)⟩
    have h2 : (game h0 h1).piStar 0 = 1 := rfl
    rw [h2] at this
    simp [polA] at this
  · intro h s
    have hs : s = 0 := Subsingleton.elim _ _
    subst hs
    refine ⟨fun hall => ?_, fun _ => isPureFP h0 h1 0, fun _ _ => Or.inl (isPureFP h0 h1 0)⟩
    exfalso
    have := hall 0 ((game h0 h1).avail_muSelf_self polA 0)
    rw [cond_a h0 h1, thr_eq h0 h1] at this
    linarith

/-- **`δ_a` is never a floored extension fixed point**: `maxF = Fext b = U(b) = 1 > 1 − δ = thr`, so the
argmax branch forces every supported action to attain `1`, while `a` is supported with `Fext a = 9/10`.
With `isPureFPfloored_iff` this is the failure of the converse to `IsFlooredFPext.isPureFPfloored`.
Source: round-2 adversarial audit N3 ("`¬ IsFlooredFPext (pureMix a)`")
Kind: P
Fidelity: exact (for every `δ ∈ (0,1)`, not only `δ > 1/10`)
Hyps: (a) -/
theorem not_isFlooredFPext_pure : ¬ (game h0 h1).IsFlooredFPext (pureMix polA) := by
  rintro ⟨_, h⟩
  obtain ⟨_, hgt, _⟩ := h 0
  have hr : 0 < (game h0 h1).resid (pureMix polA) 0 := by
    unfold Game.resid; rw [maxF_pure, thr_eq]; linarith
  have hpos : 0 < pureMix polA 0 0 := by simp [pureMix]
  have := hgt hr 0 hpos
  rw [Fext_pure_a h0 h1, maxF_pure h0 h1] at this
  norm_num at this

end OneSituation

end Cleanroom.Uea.UeaSelfGame
