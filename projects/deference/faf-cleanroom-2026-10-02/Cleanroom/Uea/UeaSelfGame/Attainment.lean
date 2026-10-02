import Cleanroom.Uea.UeaSelfGame.Repaired

/-!
# Theorem C's constant is never attained by a pure fixed point (`δ > 0`)

If a pure fixed point `π` with the trust bound at `s₀` had `U(π) = U* − δ/(1−δ)` exactly, then (from the
`p`-dependent form) `p = 1` and `V_o = 1`: all of `Po` sits on policies that play `π(s₀)` at `s₀` and have
utility `1`, so `U* = 1` and `U(π) < 1`. Any such `ρ` differs from `π` at some `s`; there `ρ(s)` is
available with conditional `1` (every policy in its fibre is a `Po`-supported optimal one) while `π(s)`'s
conditional is `< 1` (its fibre contains `π` with positive weight) — contradicting the fixed point at `s`.
So Theorem C's inequality is strict: the constant `δ/(1−δ)` is an upper bound on the gap that is never
attained by a pure fixed point. That it is the *supremum* **on `δ ≤ 1/2`** (the corrected §5.5 conjecture,
approached by the `T3(n, θ, g)` family) is `T3Family.sup_limit` (proved in the continuation of repair
round 2; until then the OPEN `sup_limit_open`), not this module. For `δ > 1/2` the strictness is empty:
the bound is negative there
(`Regimes.theoremC_strict_trivial_of_half_lt`) and the maximal gap `1` is attained
(`Regimes.GapOne.gap_one_attained`) — the two-regime statement is `Regimes.lean` (repair round 2). Mandate
target 6's `extension` item.

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-- Equality in Theorem C forces `p = 1` and `pva = 1` at `s₀` (so `V_o = 1`), when `δ > 0`.
Source: [[uea-self-game-mandate]] target 6 ("equality forces `V_a = 1` on the support and `∑ p_a = 1`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem eq_forces_pa_pva (hδ : 0 < G.δ) (π : S → A) (s₀ : S)
    (hc : G.thr ≤ G.cond (G.muSelf π) s₀ (π s₀)) (heq : G.U π = G.Ustar - G.δ / (1 - G.δ)) :
    G.pa s₀ (π s₀) = 1 ∧ G.pva s₀ (π s₀) = 1 := by
  have h1 := G.one_sub_δ_pos
  have hcl := G.theoremC_cleared π s₀ hc
  have hr1 : G.δ / (1 - G.δ) * (1 - G.δ) = G.δ := div_mul_cancel₀ _ (ne_of_gt h1)
  have hUπ : (1 - G.δ) * G.U π = (1 - G.δ) * G.Ustar - G.δ := by rw [heq]; linarith [hr1]
  have hpa1 := G.pa_le_one s₀ (π s₀); have hpva := G.pva_le_pa s₀ (π s₀)
  have hU1 := G.Ustar_le_one; have hU0 := G.Ustar_nonneg
  have hpa0 := G.pa_nonneg s₀ (π s₀)
  -- from the cleared inequality: `(1-δ) U* (1-δ+δp) ≤ (1-δ) U* − δ + δ pva ≤ (1-δ)U* − δ + δ pa`
  have key : G.δ * (1 - G.pa s₀ (π s₀)) * (1 - G.Ustar * (1 - G.δ)) ≤ 0 := by
    nlinarith
  have hpos : 0 < 1 - G.Ustar * (1 - G.δ) := by nlinarith
  have hp : 1 ≤ G.pa s₀ (π s₀) := by
    by_contra hlt; push Not at hlt
    have : 0 < G.δ * (1 - G.pa s₀ (π s₀)) * (1 - G.Ustar * (1 - G.δ)) :=
      mul_pos (mul_pos hδ (by linarith)) hpos
    linarith
  have hpa : G.pa s₀ (π s₀) = 1 := le_antisymm hpa1 hp
  refine ⟨hpa, le_antisymm (by linarith) ?_⟩
  rw [hpa] at hcl
  nlinarith

/-- **Non-attainment**: for `δ > 0`, every pure fixed point with the trust bound at some situation satisfies
the *strict* inequality `U(π) > U* − δ/(1−δ)`. Theorem C's constant is an upper bound on the gap that is
never attained; that it is the supremum on `δ ≤ 1/2` is `T3Family.sup_limit` (proved, repair round 2
continuation; formerly the OPEN `sup_limit_open`), not this theorem — together they make `δ/(1−δ)` the
exact, unattained supremum of the gap there. Content
region: for `δ > 1/2` the bound is negative and the strict inequality holds for every policy
(`Regimes.theoremC_strict_trivial_of_half_lt`), and the gap `1` is attained (`Regimes.GapOne`); the
theorem says something only for `δ ≤ 1/2`.
Scope: finite updateless self-game — self-consistent belief; not rOSI, not the sequential model of
`uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 6 (`extension`: "prove non-attainment if you can"); [[updateless-self-game]] §5.5
Kind: P
Fidelity: stronger: strict form of `theoremC`
Hyps: (a) -/
theorem theoremC_strict (hδ : 0 < G.δ) (π : S → A) (hfp : G.IsPureFP π) (s₀ : S)
    (htb : G.TB (G.muSelf π) s₀) : G.Ustar - G.δ / (1 - G.δ) < G.U π := by
  have hle := G.theoremC π hfp s₀ htb
  refine lt_of_le_of_ne hle fun heq => ?_
  have heq' : G.U π = G.Ustar - G.δ / (1 - G.δ) := heq.symm
  obtain ⟨a, ha, hthr⟩ := htb
  have hc : G.thr ≤ G.cond (G.muSelf π) s₀ (π s₀) := le_trans hthr ((hfp s₀).2 a ha)
  obtain ⟨hpa, hpva⟩ := G.eq_forces_pa_pva hδ π s₀ hc heq'
  have h1 := G.one_sub_δ_pos
  -- every `Po`-supported policy plays `π s₀` at `s₀` and has utility `1`
  have hfib : ∀ ρ, 0 < G.Po ρ → ρ s₀ = π s₀ := by
    intro ρ hρ
    by_contra hne
    have : G.pa s₀ (π s₀) ≤ 1 - G.Po ρ := by
      unfold pa condDen
      have hsplit := Finset.add_sum_erase Finset.univ (fun π' => if π' s₀ = π s₀ then G.Po π' else 0)
        (Finset.mem_univ ρ)
      rw [if_neg hne, zero_add] at hsplit
      rw [← hsplit]
      have := Finset.sum_le_sum (s := Finset.univ.erase ρ)
        (f := fun π' => if π' s₀ = π s₀ then G.Po π' else 0) (g := fun π' => G.Po π')
        (fun π' _ => by split_ifs <;> simp [G.Po_nonneg])
      have hPo := Finset.add_sum_erase Finset.univ G.Po (Finset.mem_univ ρ)
      rw [G.Po_sum] at hPo
      linarith
    linarith
  have hopt : ∀ ρ, 0 < G.Po ρ → G.U ρ = 1 := by
    intro ρ hρ
    by_contra hne
    have hlt : G.U ρ < 1 := lt_of_le_of_ne (G.U_le_one ρ) hne
    have : G.pva s₀ (π s₀) < G.pa s₀ (π s₀) := by
      unfold pva pa condNum condDen
      refine Finset.sum_lt_sum (fun π' _ => ?_) ⟨ρ, Finset.mem_univ _, ?_⟩
      · split_ifs
        · have := G.U_le_one π'; have := G.Po_nonneg π'; nlinarith
        · exact le_rfl
      · rw [if_pos (hfib ρ hρ), if_pos (hfib ρ hρ)]
        nlinarith
    linarith
  -- `U* = 1`, so `U π < 1`
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ, 0 < G.Po ρ := by
    by_contra hall; push Not at hall
    have : ∑ ρ, G.Po ρ = 0 := Finset.sum_eq_zero fun ρ _ => le_antisymm (hall ρ) (G.Po_nonneg ρ)
    rw [G.Po_sum] at this; exact one_ne_zero this
  have hUstar : G.Ustar = 1 := le_antisymm G.Ustar_le_one (by rw [← hopt ρ₀ hρ₀]; exact G.U_le_Ustar ρ₀)
  have hUπ : G.U π < 1 := by
    rw [heq', hUstar]; have : 0 < G.δ / (1 - G.δ) := div_pos hδ h1; linarith
  -- `ρ₀ ≠ π`, so they differ at some `s`
  have hne : ρ₀ ≠ π := fun h => by
    have := hopt ρ₀ hρ₀
    rw [h] at this
    linarith
  obtain ⟨s, hs⟩ : ∃ s, ρ₀ s ≠ π s := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  -- at `s`, action `ρ₀ s` is available with conditional `1`
  have hav : avail (G.muSelf π) s (ρ₀ s) := by
    unfold avail
    rw [G.condDen_muSelf, if_neg (Ne.symm hs)]
    have : 0 < G.pa s (ρ₀ s) := by
      unfold pa condDen
      refine lt_of_lt_of_le hρ₀ ?_
      have := Finset.single_le_sum (f := fun π' => if π' s = ρ₀ s then G.Po π' else 0)
        (fun π' _ => by split_ifs <;> simp [G.Po_nonneg]) (Finset.mem_univ ρ₀)
      simpa using this
    have := G.δ_nonneg
    nlinarith
  have hcond_ρ : G.cond (G.muSelf π) s (ρ₀ s) = 1 := by
    have hnum : G.condNum (G.muSelf π) s (ρ₀ s) = condDen (G.muSelf π) s (ρ₀ s) := by
      rw [G.condNum_muSelf, G.condDen_muSelf, if_neg (Ne.symm hs), if_neg (Ne.symm hs)]
      unfold pva pa condNum condDen
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun π' _ => ?_
      split_ifs with h
      · rcases (G.Po_nonneg π').eq_or_lt with h0 | h0
        · rw [← h0]; ring
        · rw [hopt π' h0, mul_one]
      · rfl
    unfold cond; rw [hnum]; exact div_self (ne_of_gt hav)
  have hcond_π : G.cond (G.muSelf π) s (π s) < 1 := by
    have hd := G.avail_muSelf_self π s
    unfold cond; rw [div_lt_one hd, G.condNum_muSelf, G.condDen_muSelf, if_pos rfl, if_pos rfl, mul_one]
    have := G.pva_le_pa s (π s); have := G.δ_nonneg
    nlinarith
  have := (hfp s).2 (ρ₀ s) hav
  linarith

end Game

end Cleanroom.Uea.UeaSelfGame
