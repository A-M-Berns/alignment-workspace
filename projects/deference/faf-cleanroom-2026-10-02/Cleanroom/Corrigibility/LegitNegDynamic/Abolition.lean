import Cleanroom.Corrigibility.LegitNegStatic.Proposals
import Cleanroom.Corrigibility.LegitNegPricing.Basic
import Cleanroom.Corrigibility.LegitNegPricing.Lexical

/-!
# E4: anticipated abolition of legitimacy — cdot manipulates iff `ρ > v/m`

Package `legit-neg-dynamic`, target 10. Sources: `clusters/E/NEGATIVES.md` E4; `clusters/E/VERIFY.md`
"E4 — narrowed" (V-E4: the margin `v` assumes a manipulated score `m = 1`; in general `v/m`);
`clusters/E/fixtures/e2_abolition.py`, `verify_e.py` V-E4; pinned by
[[corr-legit-neg-inventory]] item 057.

`abolitionToy v m ρ retro`: states `AB = 0` (abolition, prior `ρ`), `KP = 1`; actions `HON = 0`
(legitimate, scores `v`) and `MAN = 1` (a manipulation scoring `m`); `leg (AB, MAN) = retro`
(retroactive abolition: the post-abolition evaluation carries no legitimacy check),
`leg (KP, MAN) = false`. Under retroactive abolition cdot manipulates iff `ρ m > v` (`m = 1` gives
the source's `v`, the worst-case margin); conditioning at every `ρ > 0` iff `m > v` (and is `none`
at `ρ = 0`, exclusion convention); the graded proposals iff `ρ > (v − g)/(m − g)`; the strict
lexicographic `P4a` never for `ρ < 1`; under prospective abolition (`retro = false`) none of them.
Register: a genuine steering-toward-illegitimacy failure under the retroactive reading only
(verifier); "humans do away with legitimacy" read prospectively removes it.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

section Abolition

variable (v m ρ : ℚ) (retro : Bool) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)

/-- **The abolition toy** (`e2_abolition.py:21-27`, with V-E4's manipulated score `m`).
Source: [[corr-legit-neg-inventory]] item 057 (E4 model)
Kind: D
Fidelity: exact (`m` generalises the fixture's `1`, per V-E4) -/
def abolitionToy : Problem (Fin 2) (Fin 2) where
  prior := ![ρ, 1 - ρ]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun s a => if a = 0 then true else if s = 0 then retro else false
  u := fun _ a => if a = 0 then v else m

/-- `abolition_PL`: supporting lemma (no headline): `P(L | HON) = 1`, `P(L | MAN) = ρ` (retroactive)
or `0` (prospective).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abolition_PL :
    (abolitionToy v m ρ retro h0 h1).PL 0 = 1 ∧
    (abolitionToy v m ρ retro h0 h1).PL 1 = if retro then ρ else 0 := by
  cases retro <;> simp [abolitionToy, Problem.PL, Problem.mass, Fin.sum_univ_two]

/-- `abolition_P1`: supporting lemma (no headline): `P1 HON = v`, `P1 MAN = ρ m` (retroactive) or
`0` (prospective).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abolition_P1 :
    (abolitionToy v m ρ retro h0 h1).P1 (S1 (abolitionToy v m ρ retro h0 h1).u) 0 = v ∧
    (abolitionToy v m ρ retro h0 h1).P1 (S1 (abolitionToy v m ρ retro h0 h1).u) 1
      = if retro then ρ * m else 0 := by
  cases retro <;> simp [abolitionToy, Problem.P1, S1, Fin.sum_univ_two] <;> ring

/-- **E4 for cdot, retroactive**: MAN is chosen alone iff `v < ρ m`, i.e. (for `0 < m`) iff
`ρ > v / m`; at `m = 1` the threshold is `v` — the worst-case margin, "protection proportional
to the score" for anticipated abolition.
Source: [[corr-legit-neg-inventory]] item 057 (E4, cdot); VERIFY E V-E4; `e2_abolition.py:58-70`
Kind: P
Fidelity: exact (V-E4's `v/m` form)
Hyps: (a) `0 < m` for the ratio form -/
theorem E4_cdot :
    (argmax ((abolitionToy v m ρ true h0 h1).P1 (S1 (abolitionToy v m ρ true h0 h1).u)) = {1}
      ↔ v < ρ * m) ∧
    (0 < m → (argmax ((abolitionToy v m ρ true h0 h1).P1 (S1 (abolitionToy v m ρ true h0 h1).u)) = {1}
      ↔ v / m < ρ)) ∧
    (argmax ((abolitionToy v 1 ρ true h0 h1).P1 (S1 (abolitionToy v 1 ρ true h0 h1).u)) = {1} ↔ v < ρ) := by
  obtain ⟨hp0, hp1⟩ := abolition_P1 v m ρ true h0 h1
  obtain ⟨hq0, hq1⟩ := abolition_P1 v 1 ρ true h0 h1
  simp only [if_true] at hp1 hq1
  refine ⟨?_, fun hm => ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff, hp0, hp1]
  · rw [argmax_fin2_eq_one_iff, hp0, hp1, div_lt_iff₀ hm]
  · rw [argmax_fin2_eq_one_iff, hq0, hq1, mul_one]

/-- **E4 for conditioning, retroactive**: for `0 < ρ`, `P2 MAN = some m` and `P2 HON = some v`, so P2
manipulates alone iff `m > v` — at *every* positive credence, however small; at `ρ = 0`,
`P2 MAN = none`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 057 (E4, conditioning); VERIFY E V-E4; `e2_abolition.py:72-77`
Kind: P
Fidelity: exact; exclusion convention
Hyps: (a) `0 < ρ` -/
theorem E4_cond (hρ : 0 < ρ) :
    (abolitionToy v m ρ true h0 h1).P2 (S1 (abolitionToy v m ρ true h0 h1).u) 1 = some m ∧
    (abolitionToy v m ρ true h0 h1).P2 (S1 (abolitionToy v m ρ true h0 h1).u) 0 = some v ∧
    (argmaxOpt ((abolitionToy v m ρ true h0 h1).P2 (S1 (abolitionToy v m ρ true h0 h1).u)) = {1} ↔ v < m) ∧
    (abolitionToy v m 0 true le_rfl zero_le_one).P2 (S1 (abolitionToy v m 0 true le_rfl zero_le_one).u) 1 = none := by
  obtain ⟨hPL0, hPL1⟩ := abolition_PL v m ρ true h0 h1
  obtain ⟨hp0, hp1⟩ := abolition_P1 v m ρ true h0 h1
  simp only [if_true] at hPL1 hp1
  have hm : (abolitionToy v m ρ true h0 h1).P2 (S1 (abolitionToy v m ρ true h0 h1).u) 1 = some m := by
    rw [Problem.P2_of_ne _ _ _ (by rw [hPL1]; exact hρ.ne'), hPL1, hp1]
    congr 1; field_simp
  have hv : (abolitionToy v m ρ true h0 h1).P2 (S1 (abolitionToy v m ρ true h0 h1).u) 0 = some v := by
    rw [Problem.P2_of_ne _ _ _ (by rw [hPL0]; exact one_ne_zero), hPL0, hp0, div_one]
  refine ⟨hm, hv, ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![v, m])
      (by rw [Fin.forall_fin_two]; exact ⟨by simp [hv], by simp [hm]⟩)]
    rw [argmax_fin2_eq_one_iff]; simp
  · exact Problem.P2_of_eq _ _ _ (by simpa using (abolition_PL v m 0 true le_rfl zero_le_one).2)

/-- **E4 for the graded proposals, retroactive**: with the illegitimate terminal graded `g`
(`W ≡ g`, `λ = 1`), `P3 MAN = ρ m + (1 − ρ) g`, `P3 HON = v`, so P3 manipulates alone iff
`v < ρ m + (1 − ρ) g`, i.e. (for `g < m`) iff `ρ > (v − g)/(m − g)`; and at `m = 1` the threshold
`(v − g)/(1 − g)` is at most `v` (`⟺ 0 ≤ g (1 − v)`, for `g < 1`): grading lowers the bar. `P5`
with the cross-branch assessment `K ≡ g` coincides with P3 for `0 < ρ`.
Source: [[corr-legit-neg-inventory]] item 057 (E4, P3/P4/P5); `e2_abolition.py:79-105`
Kind: P
Fidelity: exact
Hyps: (a) `g < m` for the ratio form; `g < 1` for the comparison; `0 < ρ` for P5 -/
theorem E4_graded (g : ℚ) :
    (abolitionToy v m ρ true h0 h1).P3 (fun _ _ _ => g) 1 (S1 (abolitionToy v m ρ true h0 h1).u) 1
      = ρ * m + (1 - ρ) * g ∧
    (abolitionToy v m ρ true h0 h1).P3 (fun _ _ _ => g) 1 (S1 (abolitionToy v m ρ true h0 h1).u) 0 = v ∧
    (argmax ((abolitionToy v m ρ true h0 h1).P3 (fun _ _ _ => g) 1 (S1 (abolitionToy v m ρ true h0 h1).u)) = {1}
      ↔ v < ρ * m + (1 - ρ) * g) ∧
    (g < m → (argmax ((abolitionToy v m ρ true h0 h1).P3 (fun _ _ _ => g) 1
      (S1 (abolitionToy v m ρ true h0 h1).u)) = {1} ↔ (v - g) / (m - g) < ρ)) ∧
    (g < 1 → ((v - g) / (1 - g) ≤ v ↔ 0 ≤ g * (1 - v))) ∧
    (0 < ρ → (abolitionToy v m ρ true h0 h1).P5 (fun _ _ _ => g) (S1 (abolitionToy v m ρ true h0 h1).u) 1
      = some (ρ * m + (1 - ρ) * g)) := by
  have hp1 : (abolitionToy v m ρ true h0 h1).P3 (fun _ _ _ => g) 1 (S1 (abolitionToy v m ρ true h0 h1).u) 1
      = ρ * m + (1 - ρ) * g := by
    simp [abolitionToy, Problem.P3, S1, Fin.sum_univ_two]
  have hp0 : (abolitionToy v m ρ true h0 h1).P3 (fun _ _ _ => g) 1 (S1 (abolitionToy v m ρ true h0 h1).u) 0
      = v := by
    simp [abolitionToy, Problem.P3, S1, Fin.sum_univ_two]; ring
  refine ⟨hp1, hp0, ?_, fun hg => ?_, fun hg => ?_, fun hρ => ?_⟩
  · rw [argmax_fin2_eq_one_iff, hp0, hp1]
  · rw [argmax_fin2_eq_one_iff, hp0, hp1, div_lt_iff₀ (by linarith)]
    constructor <;> intro hx <;> nlinarith
  · have : (0:ℚ) < 1 - g := by linarith
    rw [div_le_iff₀ this]; constructor <;> intro hx <;> nlinarith
  · obtain ⟨hPL0, hPL1⟩ := abolition_PL v m ρ true h0 h1
    obtain ⟨hq0, hq1⟩ := abolition_P1 v m ρ true h0 h1
    simp only [if_true] at hPL1 hq1
    rw [Problem.P5_of_ne _ _ _ _ (by rw [hPL1]; exact hρ.ne'), hPL1, hq1]
    have hK : (abolitionToy v m ρ true h0 h1).Kbar (fun _ _ _ => g) 1 = g := by
      unfold Problem.Kbar; rw [hPL1]
      simp [abolitionToy, Fin.sum_univ_two]; field_simp
    rw [hK]

/-- **E4, the strict lexicographic rule never manipulates for `ρ < 1`**: `P4a` compares `P(L)`
first, and `P(L | MAN) = ρ < 1 = P(L | HON)`, whatever the second coordinate.
Source: [[corr-legit-neg-inventory]] item 057 (E4, N−, "strict lexicographic P4"); `e2_abolition.py:107-112`
Kind: N−
Fidelity: exact (static's `P4a`, whose second coordinate is `P3 W 1`; irrelevant here)
Hyps: (a) `ρ < 1` -/
theorem E4_lexicographic (hρ : ρ < 1) (Wg : MenuVec (Fin 2) (Fin 2)) :
    argmaxLex ((abolitionToy v m ρ true h0 h1).P4a Wg (S1 (abolitionToy v m ρ true h0 h1).u)) = {0} := by
  obtain ⟨hPL0, hPL1⟩ := abolition_PL v m ρ true h0 h1
  simp only [if_true] at hPL1
  rw [argmaxLex_fin2_eq_zero_iff]
  unfold Problem.P4a
  rw [Prod.Lex.toLex_lt_toLex]
  left; rw [hPL0, hPL1]; exact hρ

/-- **E4 under prospective abolition (N−)**: the `t = 0` manipulation is judged by the criterion in
force when taken, so `P1 MAN = 0 < v` (for `0 < v`) at every `ρ`, and `P2 MAN = none` (exclusion
convention).
Source: [[corr-legit-neg-inventory]] item 057 (E4, N−, prospective); `e2_abolition.py:113-119`
Kind: N−
Fidelity: exact
Hyps: (a) `0 < v` -/
theorem E4_prospective (hv : 0 < v) :
    argmax ((abolitionToy v m ρ false h0 h1).P1 (S1 (abolitionToy v m ρ false h0 h1).u)) = {0} ∧
    (abolitionToy v m ρ false h0 h1).P2 (S1 (abolitionToy v m ρ false h0 h1).u) 1 = none := by
  obtain ⟨hp0, hp1⟩ := abolition_P1 v m ρ false h0 h1
  obtain ⟨_, hPL1⟩ := abolition_PL v m ρ false h0 h1
  simp only [Bool.false_eq_true, if_false] at hp1 hPL1
  constructor
  · rw [argmax_fin2_eq_zero_iff, hp0, hp1]; exact hv
  · exact Problem.P2_of_eq _ _ _ hPL1

/-- **E4, the mistaken anticipation**: truth `ρ = 0`, belief `ρ' = v + 1/100` (`m = 1`,
`v + 1/100 ≤ 1`): cdot at the belief manipulates alone, and the true activated loss is
`P1 HON − P1 MAN = v` at `ρ = 0` — the manipulation happens with certainty in a world where
legitimacy still binds.
Source: [[corr-legit-neg-inventory]] item 057 (E4, mistaken); `e2_abolition.py:121-127`
Kind: N+
Fidelity: exact
Hyps: (a) `0 ≤ v`, `v + 1/100 ≤ 1` -/
theorem E4_mistaken (hv0 : 0 ≤ v) (hv1 : v + 1/100 ≤ 1) :
    argmax ((abolitionToy v 1 (v + 1/100) true (by linarith) hv1).P1
      (S1 (abolitionToy v 1 (v + 1/100) true (by linarith) hv1).u)) = {1} ∧
    (abolitionToy v 1 0 true le_rfl zero_le_one).P1 (S1 (abolitionToy v 1 0 true le_rfl zero_le_one).u) 0
      - (abolitionToy v 1 0 true le_rfl zero_le_one).P1 (S1 (abolitionToy v 1 0 true le_rfl zero_le_one).u) 1
      = v := by
  constructor
  · exact (E4_cdot v 1 (v + 1/100) (by linarith) hv1).2.2.2 (by linarith)
  · obtain ⟨hp0, hp1⟩ := abolition_P1 v 1 0 true le_rfl zero_le_one
    simp only [if_true] at hp1
    rw [hp0, hp1]; ring

/-- **E4, the fixture's threshold arithmetic** (not a witness): `(3/10 − 1/10)/(1 − 1/10) = 2/9`,
`(3/10 − 1/5)/(1 − 1/5) = 1/8`, `(3/10)/(1/2) = 3/5`, `(3/10 − 1/10)/(1/2 − 1/10) = 1/2` — the
formulas `(v − g)/(m − g)` and `v/m` of `E4_graded`/`E4_cdot` evaluated at the fixture's points.
The verdicts on the toy that these numbers threshold are `E4_instances`.
Source: [[corr-legit-neg-inventory]] item 057; `e2_abolition.py:79-95`, `verify_e.py:27-45`
Kind: L
Fidelity: n/a (four rational identities) -/
theorem E4_thresholds :
    ((3/10 : ℚ) - 1/10) / (1 - 1/10) = 2/9 ∧ ((3/10 : ℚ) - 1/5) / (1 - 1/5) = 1/8 ∧
    (3/10 : ℚ) / (1/2) = 3/5 ∧ ((3/10 : ℚ) - 1/10) / (1/2 - 1/10) = 1/2 := by
  norm_num

/-- **E4, the fixture's instances as verdicts on the toy** (`v = 3/10`, every `ρ ∈ [0, 1]`): P3 with
`g = 1/10` manipulates alone iff `ρ > 2/9`; P3 with `g = 1/5` iff `ρ > 1/8`; cdot at `m = 1/2` iff
`ρ > 3/5`; P3 with `g = 1/10` at `m = 1/2` iff `ρ > 1/2`. **Disclosure**: the fixture's "P4 numeric
lexical" instance (`e2_abolition.py:88-95`) is its `graded` at `g = 1/5` — P3 with the line
`g < λ = 1/4 ≤ v` entering only as a side `assert` — and that is what the `1/8` clause states;
static's `P4b` is not used, and no separate numeric-lexical P4 result exists here (the source
itself says numeric P4 "is numerically P3 with `W` the lexical scale").
Source: [[corr-legit-neg-inventory]] item 057; `e2_abolition.py:79-95`, `verify_e.py:27-45`; audit r1 adversarial 2.1
Kind: N+
Fidelity: exact (the `1/8` instance is P3 at `g = 1/5`, as in the fixture; not a P4b computation)
Hyps: (a) `0 ≤ ρ ≤ 1` -/
theorem E4_instances :
    (argmax ((abolitionToy (3/10) 1 ρ true h0 h1).P3 (fun _ _ _ => 1/10) 1
      (S1 (abolitionToy (3/10) 1 ρ true h0 h1).u)) = {1} ↔ 2/9 < ρ) ∧
    (argmax ((abolitionToy (3/10) 1 ρ true h0 h1).P3 (fun _ _ _ => 1/5) 1
      (S1 (abolitionToy (3/10) 1 ρ true h0 h1).u)) = {1} ↔ 1/8 < ρ) ∧
    (argmax ((abolitionToy (3/10) (1/2) ρ true h0 h1).P1
      (S1 (abolitionToy (3/10) (1/2) ρ true h0 h1).u)) = {1} ↔ 3/5 < ρ) ∧
    (argmax ((abolitionToy (3/10) (1/2) ρ true h0 h1).P3 (fun _ _ _ => 1/10) 1
      (S1 (abolitionToy (3/10) (1/2) ρ true h0 h1).u)) = {1} ↔ 1/2 < ρ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(E4_graded (3/10) 1 ρ h0 h1 (1/10)).2.2.2.1 (by norm_num)]; norm_num
  · rw [(E4_graded (3/10) 1 ρ h0 h1 (1/5)).2.2.2.1 (by norm_num)]; norm_num
  · rw [(E4_cdot (3/10) (1/2) ρ h0 h1).2.1 (by norm_num)]; norm_num
  · rw [(E4_graded (3/10) (1/2) ρ h0 h1 (1/10)).2.2.2.1 (by norm_num)]; norm_num

end Abolition

end Cleanroom.Corrigibility.LegitNegDynamic
