import Cleanroom.Corrigibility.CorrOsgChai.Redundant
import Cleanroom.Corrigibility.CorrOsgChai.OffSwitch
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# The File Deletion Game (Garber Example 4.1) and Example A.13 (T7(a)–(d), T9)

Package `corr-osg-chai`. **The File Deletion Game** `fileDeletion`: states `(version, code)`
uniform on `Fin 2 × Fin 2` (versions `1.0, 2.0` = rows `0, 1`; code `L, M` = columns `0, 1`),
H sees the version, A sees the code, `ua = ![![3, −5], ![−1, 5]]`, `uo ≡ 0`.

* `fileDeletion_alwaysWait_le_one`: every always-wait pair pays `≤ 1` (the four H-policies pay
  `1/2, −1/2, 1, 0`).
* `fileDeletion_opp_payoff`: the pair "act on `L`, wait on `M`; H off on `1.0`, on on `2.0`" pays
  `7/4`.
* `fileDeletion_payoff_le`, `fileDeletion_optValue`: `optValue = 7/4`, and
  `fileDeletion_unique`: **every other deterministic pair pays less**; `fileDeletion_unique_stoch`
  (through Lemma A.5, `stoch_opt_dirac_of_unique`): **every optimal stochastic pair is Dirac at
  the OPP**. The proof of uniqueness is the dominance argument, not a 36-cell table:
  a pair's payoff is `¼ (col_L + col_M)` where each column's through-set is `∅`, `all`, or H's
  on-set `W` (`fileDeletion_payoff_cols`); column `M` reaches its best value `5` only through
  `W = {2.0}` with A waiting (`fdCol_M`), and then column `L` is at most `2`, attained only by
  acting (`fdCol_L`); otherwise `M` contributes `≤ 0` and `L ≤ 3`.
* `fileDeletion_not_redundantA`, `fileDeletion_not_redundantH`: the game is redundant neither
  way (contrapositives of Prop. 4.3 through uniqueness) — the N+ side of Prop. 4.3's witness.
  `osgAsPOOSG` re-reads the original off-switch game (`ΩA = Unit`) as a PO-OSG in which A's
  observations *are* redundant, with the always-wait payoff of a `{0,1}`-valued human equal to
  `E_μ[π^H U]` (the bridge to `osgDelta`).
* **Example A.13** (`exA13S1`, `exA13O2`): with `ua = 2 − 3·𝟙[s₁ = s₂]`, Structure 1 (each sees a
  coordinate) has `optValue = 3/4` with exactly two OPPs (`exA13S1_opp_iff`), Structure 2 (H sees
  `𝟙[s₁ ≠ s₂]`, A nothing) has `optValue = 1`; Structure 2 *is* a garbling of Structure 1
  (`exA13_isGarbling`) — hence, by Theorem 4.7 (⇐), **not a coordinated one**
  (`exA13_not_coordinated`) — and no garbling at all runs the other way
  (`exA13_no_reverse_garbling`, the paper's two-line argument). This is the non-vacuity check
  that "coordinated" in Theorem 4.7 is load-bearing.

Sources: `04-chai/garber-2024-…md` l. 125–135 (Ex. 4.1), l. 413–421 and 425–429 (Ex. A.13).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep POOSG
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- Summing against a Dirac kernel evaluates. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_delta_mul {X : Type*} [Fintype X] [DecidableEq X] (x : X) (f : X → ℝ) :
    ∑ y, (Distr.delta x).mass y * f y = f x := by
  simp [Distr.delta_mass]

/-- The uniform mass on `Fin 2 × Fin 2` is `1/4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma uniform_mass_fin2_fin2 (s : Fin 2 × Fin 2) :
    (Distr.uniform : Distr (Fin 2 × Fin 2)).mass s = 4⁻¹ := by
  simp only [Distr.uniform, Fintype.card_prod, Fintype.card_fin]
  norm_num

/-! ## The File Deletion Game -/

/-- The File Deletion payoff table: rows versions `1.0, 2.0`, columns code `L, M`.
Source: Garber et al. 2024 Ex. 4.1, Table 1 (l. 129)
Kind: D
Fidelity: exact -/
def fdUa : Fin 2 → Fin 2 → ℝ := ![![3, -5], ![-1, 5]]

/-- **The File Deletion Game** (Ex. 4.1): uniform prior on `(version, code)`, H observes the
version (first coordinate), A the code (second), `ua` from Table 1, `uo ≡ 0`.
Source: Garber et al. 2024 Ex. 4.1 (l. 125–135)
Kind: D
Fidelity: exact -/
noncomputable def fileDeletion : POOSG (Fin 2 × Fin 2) (Fin 2) (Fin 2) where
  P0 := Distr.uniform
  obs := fun s => Distr.delta s
  ua := fun s => fdUa s.1 s.2
  uo := fun _ => 0

/-- The prior mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma fileDeletion_P0 (s : Fin 2 × Fin 2) : fileDeletion.P0.mass s = 4⁻¹ :=
  uniform_mass_fin2_fin2 s

/-- The observation kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma fileDeletion_obs (s : Fin 2 × Fin 2) : fileDeletion.obs s = Distr.delta s := rfl

/-- Payoff if through. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma fileDeletion_ua (s : Fin 2 × Fin 2) : fileDeletion.ua s = fdUa s.1 s.2 := rfl

/-- Payoff if not. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma fileDeletion_uo (s : Fin 2 × Fin 2) : fileDeletion.uo s = 0 := rfl

/-- The state payoff. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma fileDeletion_u (r c : Fin 2) (aH : HAct) (aA : AAct) :
    fileDeletion.u (r, c) aH aA = if through aH aA then fdUa r c else 0 := rfl

/-- A column's contribution: the payoff collected in code column `c` when A plays `a` there and
H plays `h0` on version `1.0`, `h1` on version `2.0` — the through-set of the column is `∅`
(`off`), both rows (`act`), or H's on-set (`wait`).
Source: Garber et al. 2024 Ex. 4.1 (the through-set reading of Fig. 3)
Kind: D
Fidelity: exact -/
noncomputable def fdCol (c : Fin 2) (a : AAct) (h0 h1 : HAct) : ℝ :=
  fileDeletion.u (0, c) h0 a + fileDeletion.u (1, c) h1 a

/-- **Column decomposition**: a pair's payoff is `¼ (col_L + col_M)`.
Source: Garber et al. 2024 Ex. 4.1 (Fig. 3's caption: sum the circled cells and divide by 4)
Kind: L
Fidelity: exact -/
lemma fileDeletion_payoff_cols (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) :
    fileDeletion.payoff πH πA =
      4⁻¹ * (fdCol 0 (πA 0) (πH 0) (πH 1) + fdCol 1 (πA 1) (πH 0) (πH 1)) := by
  simp only [payoff, fileDeletion_P0, fileDeletion_obs, sum_delta_mul]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  unfold fdCol
  ring

/-- **Column `M` dominance**: its value is at most `5`, equals `5` exactly when A waits and H is
off on `1.0`, on on `2.0`, and is at most `0` otherwise.
Source: Garber et al. 2024 Ex. 4.1 (the dominance step)
Kind: L
Fidelity: exact -/
lemma fdCol_M (a : AAct) (h0 h1 : HAct) :
    fdCol 1 a h0 h1 ≤ 5 ∧ (fdCol 1 a h0 h1 = 5 ↔ (a = .wait ∧ h0 = .off ∧ h1 = .on)) ∧
      (¬ (a = .wait ∧ h0 = .off ∧ h1 = .on) → fdCol 1 a h0 h1 ≤ 0) := by
  cases a <;> cases h0 <;> cases h1 <;> simp [fdCol, fileDeletion_u, through, fdUa] <;> norm_num

/-- **Column `L` dominance**: its value is at most `3`; when H is off on `1.0` and on on `2.0`
it is at most `2`, with equality only if A acts.
Source: Garber et al. 2024 Ex. 4.1 (the dominance step)
Kind: L
Fidelity: exact -/
lemma fdCol_L (a : AAct) (h0 h1 : HAct) :
    fdCol 0 a h0 h1 ≤ 3 ∧
      ((h0 = .off ∧ h1 = .on) → fdCol 0 a h0 h1 ≤ 2 ∧ (fdCol 0 a h0 h1 = 2 → a = .act)) := by
  cases a <;> cases h0 <;> cases h1 <;> simp [fdCol, fileDeletion_u, through, fdUa] <;> norm_num

/-- **T7(a): every always-wait pair pays at most `1`** (the four H-policies pay `1/2, −1/2, 1, 0`).
Source: Garber et al. 2024 Ex. 4.1 (l. 131, "the best response for H … +1")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fileDeletion_alwaysWait_le_one (πH : Fin 2 → HAct) :
    fileDeletion.payoff πH (fun _ => .wait) ≤ 1 := by
  rw [fileDeletion_payoff_cols]
  cases h0 : πH 0 <;> cases h1 : πH 1 <;> simp [fdCol, fileDeletion_u, through, fdUa] <;> norm_num

/-- **T7(b): the pair "act on `L`, wait on `M`; H off on `1.0`, on on `2.0`" pays `7/4`.**
Source: Garber et al. 2024 Ex. 4.1 (l. 133–135)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fileDeletion_opp_payoff :
    fileDeletion.payoff ![.off, .on] ![.act, .wait] = 7 / 4 := by
  rw [fileDeletion_payoff_cols]
  simp [fdCol, fileDeletion_u, through, fdUa]
  norm_num

/-- **T7(c): no pair pays more than `7/4`** — by column dominance: if column `M` is at its best
(`5`, forcing `W = {2.0}` and a wait), column `L` is at most `2`; otherwise `M ≤ 0` and `L ≤ 3`.
Source: Garber et al. 2024 Ex. 4.1 / §4.1 ("the unique OPP")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fileDeletion_payoff_le (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) :
    fileDeletion.payoff πH πA ≤ 7 / 4 := by
  rw [fileDeletion_payoff_cols]
  obtain ⟨hM5, -, hM0⟩ := fdCol_M (πA 1) (πH 0) (πH 1)
  obtain ⟨hL3, hL2⟩ := fdCol_L (πA 0) (πH 0) (πH 1)
  by_cases hc : πA 1 = .wait ∧ πH 0 = .off ∧ πH 1 = .on
  · have := (hL2 hc.2).1
    linarith
  · have := hM0 hc
    linarith

/-- **T7(c): `optValue = 7/4`.**
Source: Garber et al. 2024 Ex. 4.1 / §4.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem fileDeletion_optValue : fileDeletion.optValue = 7 / 4 :=
  fileDeletion.optValue_eq_of fileDeletion_payoff_le fileDeletion_opp_payoff

/-- **T7(d): uniqueness among deterministic pairs** — the paper's OPPs (l. 91). A deterministic
pair pays `7/4` only if it is the pair of (b): A acts on `L` and waits on `M`, H is off on `1.0`
and on on `2.0`. Uniqueness among *stochastic* pairs is `fileDeletion_unique_stoch` below (it
does not follow from `optValue_isGreatest_stoch` alone: audit r1 B1).
Source: Garber et al. 2024 §4.1 (l. 97, "the unique OPP")
Kind: P
Fidelity: exact (deterministic pairs)
Hyps: (a) none -/
theorem fileDeletion_unique (πH : Fin 2 → HAct) (πA : Fin 2 → AAct)
    (h : fileDeletion.payoff πH πA = 7 / 4) :
    πA 0 = .act ∧ πA 1 = .wait ∧ πH 0 = .off ∧ πH 1 = .on := by
  rw [fileDeletion_payoff_cols] at h
  obtain ⟨hM5, -, hM0⟩ := fdCol_M (πA 1) (πH 0) (πH 1)
  obtain ⟨hL3, hL2⟩ := fdCol_L (πA 0) (πH 0) (πH 1)
  by_cases hc : πA 1 = .wait ∧ πH 0 = .off ∧ πH 1 = .on
  · obtain ⟨hle, heq⟩ := hL2 hc.2
    exact ⟨heq (by linarith), hc.1, hc.2.1, hc.2.2⟩
  · have := hM0 hc
    linarith

/-- The OPP, as `IsOPP`. Source: Garber et al. 2024 §4.1. Kind: L. Fidelity: exact -/
theorem fileDeletion_isOPP : fileDeletion.IsOPP ![.off, .on] ![.act, .wait] := by
  rw [IsOPP, fileDeletion_optValue, fileDeletion_opp_payoff]

/-- **T7(d), uniqueness among stochastic pairs** (Cor. A.6's uniqueness clause on the File
Deletion Game): a stochastic pair pays `7/4` only if it is Dirac at the OPP — A acts on `L` and
waits on `M` with probability one, H is off on `1.0` and on on `2.0` with probability one. From
`fileDeletion_unique` through Lemma A.5 (`stoch_opt_dirac_of_unique`). The ledger's LB-2 row and
finding F-8 rest on this declaration (audit r1 B1).
Source: Garber et al. 2024 §4.1 (l. 97, "the unique OPP") with Lemma A.5 / Cor. A.6 (l. 365–367)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem fileDeletion_unique_stoch (σH : Fin 2 → Distr HAct) (σA : Fin 2 → Distr AAct)
    (h : fileDeletion.payoffStoch σH σA = 7 / 4) :
    (∀ r, σH r = Distr.delta ((![HAct.off, .on] : Fin 2 → HAct) r)) ∧
      (∀ c, σA c = Distr.delta ((![AAct.act, .wait] : Fin 2 → AAct) c)) := by
  refine fileDeletion.stoch_opt_dirac_of_unique (πH₀ := ![.off, .on]) (πA₀ := ![.act, .wait]) ?_
    (by rw [h, fileDeletion_optValue])
  intro πH πA hopp
  rw [IsOPP, fileDeletion_optValue] at hopp
  obtain ⟨h0, h1, h2, h3⟩ := fileDeletion_unique πH πA hopp
  refine ⟨funext fun r => ?_, funext fun c => ?_⟩
  · fin_cases r <;> simp [h2, h3]
  · fin_cases c <;> simp [h0, h1]

/-- **T16(d): under the OPP, "A waited" reveals `oA = M`.** The wait-set of the OPP's assistant
policy is exactly `{M}` (code `1`), so on the event `πA oA = wait` H's posterior on `oA` is
`δ_M` — the observation kernel is deterministic, so the posterior is the indicator of this set.
With `fileDeletion_unique` this is the "interference" of finding F-14, and the pair is optimal
(`fileDeletion_isOPP`).
Source: Garber et al. 2024 §4.5 (l. 281, "whenever H is deferred to, H can deduce that A's
observation is M"); position-statement.md §2.7 (finding F-14)
Kind: L
Fidelity: exact (the wait-set; the posterior statement is this set being the singleton `{M}`) -/
theorem fileDeletion_opp_waitSet (oA : Fin 2) :
    (![AAct.act, .wait] : Fin 2 → AAct) oA = .wait ↔ oA = 1 := by
  fin_cases oA <;> simp

/-- **The OPP is not always-wait, so A's observations are not redundant** (contrapositive of
Prop. 4.3 through uniqueness).
Source: Garber et al. 2024 §4.2 (the game is the non-redundant case)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem fileDeletion_not_redundantA : ¬ fileDeletion.RedundantA := by
  intro h
  obtain ⟨πH, hopp⟩ := fileDeletion.exists_opp_alwaysWait_of_redundantA h
  rw [IsOPP, fileDeletion_optValue] at hopp
  have := (fileDeletion_unique πH _ hopp).1
  simp at this

/-- **The OPP waits on `M`, so H's observations are not redundant either.**
Source: Garber et al. 2024 §4.2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem fileDeletion_not_redundantH : ¬ fileDeletion.RedundantH := by
  intro h
  obtain ⟨πH, πA, hopp, hnw⟩ := fileDeletion.exists_opp_neverWait_of_redundantH h
  rw [IsOPP, fileDeletion_optValue] at hopp
  exact hnw 1 (fileDeletion_unique πH πA hopp).2.1

/-- **The trivial game has every pair optimal** (`ua ≡ uo`): uniqueness in the File Deletion Game
is not an artefact of the encoding, and the converse of Prop. 4.3 ("always-wait optimal only if
redundant") is not claimed — this game is not redundant-free-of-OPPs in any direction.
Source: none: non-vacuity check (mandate T7, finding F-9)
Kind: N−
Fidelity: n/a -/
theorem trivialGame_all_opp {S ΩH ΩA : Type} [Fintype S] [Fintype ΩH] [Fintype ΩA]
    [DecidableEq ΩH] [DecidableEq ΩA] (G : POOSG S ΩH ΩA) (h : G.ua = G.uo)
    (πH : ΩH → HAct) (πA : ΩA → AAct) : G.IsOPP πH πA := by
  rw [G.isOPP_iff]
  intro πH' πA'
  have hu : ∀ s aH aA aH' aA', G.u s aH aA = G.u s aH' aA' := by
    intro s aH aA aH' aA'
    simp only [u, h]
    split_ifs <;> rfl
  unfold payoff
  refine le_of_eq (sum_congr rfl fun s _ => congrArg _ (sum_congr rfl fun o _ => ?_))
  rw [hu s _ _ (πH o.1) (πA o.2)]

/-! ## The original off-switch game as a PO-OSG (Prop. 4.3's hypothesis, inhabited) -/

section OSG

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **The off-switch game as a PO-OSG**: H observes the world `ω` (her type), A observes nothing
(`ΩA = Unit`), `ua = U`, `uo = 0`.
Source: Garber et al. 2024 §4.2 ("in the off-switch game … A has redundant observations")
Kind: D
Fidelity: exact -/
noncomputable def osgAsPOOSG (μ : Distr Ω) (U : Ω → ℝ) : POOSG Ω Ω Unit where
  P0 := μ
  obs := fun ω => Distr.delta (ω, ())
  ua := U
  uo := fun _ => 0

/-- In the off-switch game A's observations are redundant (`K ≡ δ_()`).
Source: Garber et al. 2024 §4.2 (l. 173, "its observations are a deterministic function of H's")
Kind: L
Fidelity: exact -/
theorem osgAsPOOSG_redundantA (μ : Distr Ω) (U : Ω → ℝ) : (osgAsPOOSG μ U).RedundantA := by
  refine ⟨fun _ => Distr.delta (), fun s _ oH oA => ?_⟩
  simp only [osgAsPOOSG, obsH, Distr.delta_mass, Prod.mk.injEq, and_true]
  cases oA
  simp

/-- **Prop. 4.3 inhabited on a non-trivial game**: the off-switch game with `U = ![1, −1]` and a
uniform prior has an always-wait OPP.
Source: Garber et al. 2024 Prop. 4.3 (N+ witness)
Kind: N+
Fidelity: n/a -/
theorem osgAsPOOSG_exists_alwaysWait_opp :
    ∃ πH, (osgAsPOOSG (Distr.uniform : Distr (Fin 2)) ![1, -1]).IsOPP πH (fun _ => .wait) :=
  (osgAsPOOSG _ _).exists_opp_alwaysWait_of_redundantA (osgAsPOOSG_redundantA _ _)

/-- **The bridge to `osgDelta`**: an always-wait pair against a deterministic human pays
`E_μ[π^H U]` with `π^H = 𝟙[πH = on]`, i.e. Eq. 1's first term.
Source: Hadfield-Menell et al. 2017 Eq. 1 (`E[π^H(U_a) U_a]`)
Kind: L
Fidelity: exact -/
theorem osgAsPOOSG_payoff_wait (μ : Distr Ω) (U : Ω → ℝ) (πH : Ω → HAct) :
    (osgAsPOOSG μ U).payoff πH (fun _ => .wait) =
      expect μ (fun ω => (if πH ω = .on then 1 else 0) * U ω) := by
  simp only [payoff, osgAsPOOSG, expect, sum_delta_mul, u, through_wait_iff]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs <;> ring

end OSG

/-! ## Example A.13: an uncoordinated garbling that raises the optimum -/

/-- Example A.13's payoff `ua(s) = 2 − 3·𝟙[s₁ = s₂]`.
Source: Garber et al. 2024 Ex. A.13 (l. 413)
Kind: D
Fidelity: exact -/
noncomputable def exA13Ua (s : Fin 2 × Fin 2) : ℝ := 2 - 3 * (if s.1 = s.2 then 1 else 0)

/-- **Example A.13, Structure 1**: each player observes one coordinate of the uniform state.
Source: Garber et al. 2024 Ex. A.13, Structure 1 (l. 415)
Kind: D
Fidelity: exact -/
noncomputable def exA13S1 : POOSG (Fin 2 × Fin 2) (Fin 2) (Fin 2) where
  P0 := Distr.uniform
  obs := fun s => Distr.delta s
  ua := exA13Ua
  uo := fun _ => 0

/-- **Example A.13, Structure 2's kernel**: H observes `𝟙[s₁ ≠ s₂]`, A observes nothing.
Source: Garber et al. 2024 Ex. A.13, Structure 2 (l. 419)
Kind: D
Fidelity: exact -/
noncomputable def exA13O2 (s : Fin 2 × Fin 2) : Distr (Fin 2 × Unit) :=
  Distr.delta (if s.1 = s.2 then 0 else 1, ())

/-- Prior mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma exA13S1_P0 (s : Fin 2 × Fin 2) : exA13S1.P0.mass s = 4⁻¹ := uniform_mass_fin2_fin2 s

/-- Kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma exA13S1_obs (s : Fin 2 × Fin 2) : exA13S1.obs s = Distr.delta s := rfl

/-- Payoff if through. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma exA13S1_ua (s : Fin 2 × Fin 2) : exA13S1.ua s = exA13Ua s := rfl

/-- Payoff if not. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma exA13S1_uo (s : Fin 2 × Fin 2) : exA13S1.uo s = 0 := rfl

/-- State payoff. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exA13S1_u (r c : Fin 2) (aH : HAct) (aA : AAct) :
    exA13S1.u (r, c) aH aA = if through aH aA then exA13Ua (r, c) else 0 := rfl

/-- A column's contribution in Structure 1 (A sees the column `c = s₂`).
Source: Garber et al. 2024 Ex. A.13
Kind: D
Fidelity: exact -/
noncomputable def exA13Col (c : Fin 2) (a : AAct) (h0 h1 : HAct) : ℝ :=
  exA13S1.u (0, c) h0 a + exA13S1.u (1, c) h1 a

/-- Column decomposition in Structure 1. Source: none: infrastructure. Kind: L. Fidelity: exact -/
lemma exA13S1_payoff_cols (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) :
    exA13S1.payoff πH πA =
      4⁻¹ * (exA13Col 0 (πA 0) (πH 0) (πH 1) + exA13Col 1 (πA 1) (πH 0) (πH 1)) := by
  simp only [payoff, exA13S1_P0, exA13S1_obs, sum_delta_mul]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  unfold exA13Col
  ring

/-- Column `0` dominance in Structure 1: at most `2`, equal to `2` iff A waits with H
`(off, on)`, at most `1` otherwise; and under H `(on, off)` it equals `1` iff A acts.
Source: Garber et al. 2024 Ex. A.13. Kind: L. Fidelity: exact -/
lemma exA13Col_0 (a : AAct) (h0 h1 : HAct) :
    exA13Col 0 a h0 h1 ≤ 2 ∧ (exA13Col 0 a h0 h1 = 2 ↔ (a = .wait ∧ h0 = .off ∧ h1 = .on)) ∧
      (¬ (a = .wait ∧ h0 = .off ∧ h1 = .on) → exA13Col 0 a h0 h1 ≤ 1) ∧
      ((h0 = .on ∧ h1 = .off) → (exA13Col 0 a h0 h1 = 1 ↔ a = .act)) := by
  cases a <;> cases h0 <;> cases h1 <;> simp [exA13Col, exA13S1_u, through, exA13Ua] <;> norm_num

/-- Column `1` dominance in Structure 1 (the mirror image).
Source: Garber et al. 2024 Ex. A.13. Kind: L. Fidelity: exact -/
lemma exA13Col_1 (a : AAct) (h0 h1 : HAct) :
    exA13Col 1 a h0 h1 ≤ 2 ∧ (exA13Col 1 a h0 h1 = 2 ↔ (a = .wait ∧ h0 = .on ∧ h1 = .off)) ∧
      (¬ (a = .wait ∧ h0 = .on ∧ h1 = .off) → exA13Col 1 a h0 h1 ≤ 1) ∧
      ((h0 = .off ∧ h1 = .on) → (exA13Col 1 a h0 h1 = 1 ↔ a = .act)) := by
  cases a <;> cases h0 <;> cases h1 <;> simp [exA13Col, exA13S1_u, through, exA13Ua] <;> norm_num

/-- **Structure 1: no pair pays more than `3/4`** (the two columns cannot both be at their best
`2`, which need opposite H-policies).
Source: Garber et al. 2024 Ex. A.13 (l. 417, "expected payoff of 3/4")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exA13S1_payoff_le (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) :
    exA13S1.payoff πH πA ≤ 3 / 4 := by
  rw [exA13S1_payoff_cols]
  obtain ⟨h02, -, h01, -⟩ := exA13Col_0 (πA 0) (πH 0) (πH 1)
  obtain ⟨h12, -, h11, -⟩ := exA13Col_1 (πA 1) (πH 0) (πH 1)
  by_cases hc : πA 0 = .wait ∧ πH 0 = .off ∧ πH 1 = .on
  · have : ¬ (πA 1 = .wait ∧ πH 0 = .on ∧ πH 1 = .off) := fun h => by
      rw [hc.2.1] at h; exact absurd h.2.1 (by simp)
    have := h11 this
    linarith
  · have := h01 hc
    linarith

/-- **Structure 1: the optimal pairs are exactly the two the paper names** (the pair on l. 415 and
its swap), and `optValue = 3/4`.
Source: Garber et al. 2024 Ex. A.13 (l. 415–417)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exA13S1_opp_iff (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) :
    exA13S1.payoff πH πA = 3 / 4 ↔
      (πH 0 = .off ∧ πH 1 = .on ∧ πA 0 = .wait ∧ πA 1 = .act) ∨
        (πH 0 = .on ∧ πH 1 = .off ∧ πA 0 = .act ∧ πA 1 = .wait) := by
  rw [exA13S1_payoff_cols]
  obtain ⟨h02, h02iff, h01, h0act⟩ := exA13Col_0 (πA 0) (πH 0) (πH 1)
  obtain ⟨h12, h12iff, h11, h1act⟩ := exA13Col_1 (πA 1) (πH 0) (πH 1)
  constructor
  · intro h
    by_cases hc : πA 0 = .wait ∧ πH 0 = .off ∧ πH 1 = .on
    · have hn : ¬ (πA 1 = .wait ∧ πH 0 = .on ∧ πH 1 = .off) := fun h' => by
        rw [hc.2.1] at h'; exact absurd h'.2.1 (by simp)
      have h1 : exA13Col 1 (πA 1) (πH 0) (πH 1) = 1 := by
        have := h11 hn; have := h02iff.mpr hc; linarith
      exact Or.inl ⟨hc.2.1, hc.2.2, hc.1, (h1act ⟨hc.2.1, hc.2.2⟩).mp h1⟩
    · have h0le := h01 hc
      have h1 : exA13Col 1 (πA 1) (πH 0) (πH 1) = 2 := by linarith
      obtain ⟨ha, hh0, hh1⟩ := h12iff.mp h1
      have h0 : exA13Col 0 (πA 0) (πH 0) (πH 1) = 1 := by linarith
      exact Or.inr ⟨hh0, hh1, (h0act ⟨hh0, hh1⟩).mp h0, ha⟩
  · rintro (⟨hh0, hh1, ha0, ha1⟩ | ⟨hh0, hh1, ha0, ha1⟩)
    · have := h02iff.mpr ⟨ha0, hh0, hh1⟩
      have := (h1act ⟨hh0, hh1⟩).mpr ha1
      linarith
    · have := h12iff.mpr ⟨ha1, hh0, hh1⟩
      have := (h0act ⟨hh0, hh1⟩).mpr ha0
      linarith

/-- `optValue = 3/4` in Structure 1. Source: Garber et al. 2024 Ex. A.13. Kind: C. Fidelity: exact. Hyps: (a) none -/
theorem exA13S1_optValue : exA13S1.optValue = 3 / 4 :=
  exA13S1.optValue_eq_of exA13S1_payoff_le
    ((exA13S1_opp_iff ![.off, .on] ![.wait, .act]).mpr (Or.inl (by simp)))

/-- **Structure 2: `optValue = 1`** — the best-conceivable-through-set bound `¼ ∑ max(ua, 0) = 1`
is attained by "A waits, H on iff the coordinates differ".
Source: Garber et al. 2024 Ex. A.13 (l. 421–425, "the expected payoff is 1")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exA13S2_optValue : (exA13S1.withObs exA13O2).optValue = 1 := by
  refine (exA13S1.withObs exA13O2).optValue_eq_of (πH := ![.off, .on]) (πA := fun _ => .wait)
    (fun πH πA => ?_) ?_
  · refine ((exA13S1.withObs exA13O2).payoff_le_sum_max πH πA).trans (le_of_eq ?_)
    simp only [withObs, exA13S1_P0, exA13S1_ua, exA13S1_uo]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [exA13Ua]
    norm_num [max_def]
  · simp only [payoff, withObs, exA13S1_P0, exA13O2, sum_delta_mul, u, through_wait_iff,
      exA13S1_ua, exA13S1_uo]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [exA13Ua]
    norm_num

/-- **Structure 2 is a garbling of Structure 1** through `ν(oH, oA) = δ_{(𝟙[oH ≠ oA], ())}`.
Source: Garber et al. 2024 Ex. A.13 (l. 427)
Kind: L
Fidelity: exact -/
theorem exA13_isGarbling :
    ∀ s o', (exA13O2 s).mass o' = ∑ o, (exA13S1.obs s).mass o *
      ((fun o : Fin 2 × Fin 2 => Distr.delta ((if o.1 = o.2 then 0 else 1 : Fin 2), ())) o).mass o' := by
  intro s o'
  rw [exA13S1_obs, sum_delta_mul]
  rfl

/-- **The garbling is not coordinated** — because Theorem 4.7 (⇐) would then give
`optValue₂ ≤ optValue₁`, i.e. `1 ≤ 3/4`. This is the non-vacuity check that "coordinated" in
Theorem 4.7 is load-bearing (the paper's "ν is not coordinated", l. 431, derived here from the
values rather than inspected).
Source: Garber et al. 2024 Ex. A.13 (l. 431); Thm 4.7's scope
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA13_not_coordinated :
    ¬ Coordinated (fun o : Fin 2 × Fin 2 => Distr.delta ((if o.1 = o.2 then 0 else 1 : Fin 2), ())) := by
  intro hc
  have := exA13S1.optValue_withObs_le_of_moreInformative exA13O2 ⟨_, hc, exA13_isGarbling⟩
  rw [exA13S2_optValue, exA13S1_optValue] at this
  norm_num at this

/-- **Structure 1 is not a garbling of Structure 2 at all** (coordinated or not): the states
`(0,0)` and `(1,1)` have the same Structure-2 observation but different Structure-1
observations.
Source: Garber et al. 2024 Ex. A.13 (l. 429, the two-line impossibility)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exA13_no_reverse_garbling :
    ¬ ∃ ξ : ObsGarbling (Fin 2) Unit (Fin 2) (Fin 2), ∀ s o',
      (exA13S1.obs s).mass o' = ∑ o, (exA13O2 s).mass o * (ξ o).mass o' := by
  rintro ⟨ξ, hξ⟩
  have h00 := hξ (0, 0) (0, 0)
  have h11 := hξ (1, 1) (0, 0)
  simp only [exA13S1_obs, exA13O2, sum_delta_mul, Distr.delta_mass] at h00 h11
  simp at h00 h11
  linarith

end Cleanroom.Corrigibility.CorrOsgChai
