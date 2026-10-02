import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Marginal
import Cleanroom.Li.LiProjection.Underdetermination
import Cleanroom.Li.LiProjection.Prescribe
import Cleanroom.Li.LiProjection.Fragments
import Cleanroom.Bli.BliFound.PaperInstances
import Cleanroom.Found.LiQuoteLane.PaperWitness
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `li-projection` · Witnesses: the N+ packages over `liaHistory (paperDP 𝗜𝚺₁)` (T2.1 and friends)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 11 of the layout — the only
file importing `Construction.LIACompiler` (`LIA_is_logical_inductor`) and `Construction.Paper.TheoremDP`.

* **T2.1.** The full hypothesis package of Lemma A inhabited on the real construction: base
  inductor `liaHistory (paperDP 𝗜𝚺₁)` (FAF's LIA over the paper's first-order process), fresh atom
  `projAtomCode 0` (freshness from `bli-found`'s `paperDP_cleanroomFree`), `hworld` from consistency
  of `𝗜𝚺₁` (`paperDP_hworld`), and a **non-constant** weight `jumpWeight` with one jump (`1/3` before
  day `5`, `1/2` after; `η = 1/3`, `N = 5`), so the correction term `Σ_{m<5} (q_m − λ) D_m` of the
  mirror identity is live. Delivered: the package (`paperProjection_package`, proved outright), the
  conclusion `IsLogicalInductor (project …) (paperDP 𝗜𝚺₁)` (`paperProjection`, resting on the OPEN
  certificate through Lemma A), the marginal `→ 1/2` (`paperProjection_atom_tendsto`, outright), and
  the restriction on the concrete arithmetic family `paperPrimeDecompose σ` (`paperProjection_restrict_paperPrime`,
  outright: every atom of a paper-prime decomposition has FAF's tag `5`).
* **The ledger instance** (T2.3's N+): over `li-quote-lane`'s `paperOneWayPair` (reader
  `liaHistory (paperDP 𝗜𝚺₁ ⊕ ledger)`), the projections on `projAtomCode 0` are inductors over the
  same ledger process (`paperLedgerProjection`).
* **T3.1's witness**: `liaHistory (paperDP 𝗜𝚺₁)` patched at two coordinates on two different days
  (`paperPatchTwoDays`), strictly more than FAF's one-point `liaPerturbed`; its prescription is exact
  (`paperPatchTwoDays_exact`).
* **T4.3's witness**: the achievable rational limits over `paperDP 𝗜𝚺₁` (`paperAchievableLimits`).

Grades: N+ throughout (a real market with a proved criterion over a real computable process, with
the jump term exercised) — except that the *conclusion* instances inherit the OPEN certificate.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## T4.2(iii) N+: the buy-both trader on an oscillating pricing over the paper process -/

/-- **N+ for `buyBoth_exploits`** (replacing the N− grade of `buyBoth_exploits_quarterP`, audit r1
fidelity B2): the buy-both trader exploits the pricing `oscGapP` — `atom 0` at `3/8`/`1/8` on
even/odd days, its negation the other way round, a coherence gap of `1/2` on every day — over FAF's
paper process `paperDP 𝗜𝚺₁` (a consistent world at every stage by `paperDP_hworld`). The pricing is
not constant in time (`oscGapP_not_const`) and the process is not empty.
Source: mandate T4.2(iii) ("N+ on an explicit history"); audit r1 (fidelity) B2
Kind: N+
Fidelity: exact -/
theorem buyBoth_exploits_oscGapP_paper :
    (buyBoth (Formula.atom 0)).Exploits oscGapP (paperDP 𝗜𝚺₁) :=
  buyBoth_exploits oscGapP (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) _ (1 / 2) (by norm_num)
    (fun n => by rw [oscGapP_sum]; norm_num)

/-! ## The witness weight: one jump -/

/-- The witness weight: `1/3` on days `< 5`, `1/2` from day `5` on (`η = 1/3`, `N = 5`).
Source: mandate T2.1 ("e.g. `q n := if n < 5 then 1/3 else 1/2`")
Kind: D
Fidelity: n/a -/
def jumpWeight : ℕ → ℚ := fun n => if n < 5 then 1 / 3 else 1 / 2

/-- `jumpWeight_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jumpWeight_mem (n : ℕ) : 1 / 3 ≤ jumpWeight n ∧ jumpWeight n ≤ 1 - 1 / 3 := by
  unfold jumpWeight; split_ifs <;> norm_num

/-- `jumpWeight_jump`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jumpWeight_jump : ∀ n, 5 ≤ n → jumpWeight n = jumpWeight 5 := by
  intro n hn; simp [jumpWeight, not_lt.mpr hn]

/-- `jumpWeight_five`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jumpWeight_five : jumpWeight 5 = 1 / 2 := by simp [jumpWeight]

/-- `jumpWeight_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jumpWeight_zero : jumpWeight 0 = 1 / 3 := by simp [jumpWeight]

/-- The witness weight is efficiently computable (hypothesis (i), discharged).
Source: mandate T1.5/T2.1
Kind: L
Fidelity: exact -/
theorem jumpWeight_machineRatCodes : MachineRatCodes jumpWeight :=
  MachineRatCodes.ofFiniteTable _ 5 (1 / 2) fun n hn => by simp [jumpWeight, not_lt.mpr hn]

/-! ## Freshness of the projection atoms for the paper process -/

/-- `paperDP T` is free of every projection atom (every atom of FAF's paper process carries a tag
`< 9`; `bli-found`'s `paperDP_cleanroomFree`).
Source: mandate T1.2
Kind: L
Fidelity: exact -/
theorem paperDP_atomFree (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] (k : ℕ) :
    AtomFreeProcess (projAtomCode k) (paperDP T) :=
  atomFreeProcess_of_cleanroomFree (paperDP_cleanroomFree T) k

/-- A paper-prime decomposition never mentions a projection atom (its atoms carry FAF's tag `5`).
Source: none: infrastructure (FAF `paperPrimeDecompose_atom_tag`)
Kind: L
Fidelity: n/a -/
theorem atomFreeSentence_paperPrimeDecompose (k : ℕ) (σ : LO.FirstOrder.ArithmeticProposition) :
    AtomFreeSentence (projAtomCode k) (paperPrimeDecompose σ) := by
  intro h
  have := paperPrimeDecompose_atom_tag σ _ h
  simp [projAtomCode, freshAtomCode_unpair, cleanroomBaseTag, paperPrimeTag] at this

/-! ## T2.1 The N+ package -/

/-- **T2.1, the hypothesis package of Lemma A inhabited** on `liaHistory (paperDP 𝗜𝚺₁)`: the base
inductor's criterion (FAF's `LIA_is_logical_inductor`), freshness of `projAtomCode 0`, a consistent
world at every stage, `η = 1/3 > 0`, the range of the weight, its efficiency certificate, the jump
at `N = 5` — and the weight is genuinely non-constant (`jumpWeight 0 ≠ jumpWeight 5`), so the
correction term is exercised. Proved outright.
Source: mandate T2.1; [[anson-2-inventory]] 029 (the N+ package)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperProjection_package :
    IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) ∧
    AtomFreeProcess (projAtomCode 0) (paperDP 𝗜𝚺₁) ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
    (0 : ℚ) < 1 / 3 ∧
    (∀ n, 1 / 3 ≤ jumpWeight n ∧ jumpWeight n ≤ 1 - 1 / 3) ∧
    MachineRatCodes jumpWeight ∧
    (∀ n, 5 ≤ n → jumpWeight n = jumpWeight 5) ∧
    jumpWeight 0 ≠ jumpWeight 5 :=
  ⟨LIA_is_logical_inductor _ (paperDP_computable _), paperDP_atomFree 𝗜𝚺₁ 0, paperDP_hworld 𝗜𝚺₁,
   by norm_num, jumpWeight_mem, jumpWeight_machineRatCodes, jumpWeight_jump,
   by rw [jumpWeight_zero, jumpWeight_five]; norm_num⟩

/-- **T2.1, the conclusion instance**: the projection of FAF's paper LIA on `projAtomCode 0` with
the one-jump weight is a logical inductor over `paperDP 𝗜𝚺₁`. Lemma A at the package above; rests
on the OPEN certificate.
Source: mandate T2.1; [[anson-2-inventory]] 029
Kind: N+
Fidelity: exact
Hyps: (a) none; rests on the OPEN rewriters through Lemma A -/
theorem paperProjection :
    IsLogicalInductor (project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) jumpWeight)
      (paperDP 𝗜𝚺₁) :=
  project_isLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁)
    (hLI := LIA_is_logical_inductor _ (paperDP_computable _)) (projAtomCode 0)
    (paperDP_atomFree 𝗜𝚺₁ 0) jumpWeight (1 / 3) (by norm_num) jumpWeight_mem
    jumpWeight_machineRatCodes 5 jumpWeight_jump

/-- **T2.1, the marginal**: the projected price of the atom tends to `1/2` (proved outright from the
base LIA's criterion).
Source: mandate T2.1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperProjection_atom_tendsto :
    Tendsto (fun n => project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) jumpWeight n (projAtom 0))
      atTop (𝓝 (1 / 2)) := by
  haveI := LIA_is_logical_inductor (paperDP 𝗜𝚺₁) (paperDP_computable _)
  have h := project_atom_tendsto (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (projAtomCode 0) jumpWeight 5 jumpWeight_jump
  rw [jumpWeight_five] at h
  push_cast at h
  exact h

/-- **T2.1, the restriction on a concrete arithmetic family**: on every paper-prime decomposition
`paperPrimeDecompose σ` the projected market *is* the base LIA, on every day.
Source: mandate T2.1 ("`project_restrict` on a concrete arithmetic sentence family")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperProjection_restrict_paperPrime (σ : LO.FirstOrder.ArithmeticProposition) (n : ℕ) :
    project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) jumpWeight n (paperPrimeDecompose σ) =
      liaHistory (paperDP 𝗜𝚺₁) n (paperPrimeDecompose σ) :=
  project_restrict _ _ _ n (atomFreeSentence_paperPrimeDecompose 0 σ)

/-- **Lemma A over any computable process**, with FAF's LIA as the base: the general N+ generator.
Source: mandate T2.1
Kind: C
Fidelity: exact
Hyps: (a) none; rests on the OPEN rewriters through Lemma A -/
theorem liaProjection (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP) (u : ℕ)
    (hu : AtomFreeProcess u DP) (q : ℕ → ℚ) (η : ℚ) (hη : 0 < η)
    (hq : ∀ n, η ≤ q n ∧ q n ≤ 1 - η) (hqec : MachineRatCodes q) (N : ℕ)
    (hjump : ∀ n, N ≤ n → q n = q N) :
    IsLogicalInductor (project (liaHistory DP) u q) DP :=
  project_isLogicalInductor (liaHistory DP) DP (hLI := LIA_is_logical_inductor DP hDP) u hu q η hη
    hq hqec N hjump

/-! ## The ledger instance (T2.3's N+) -/

/-- The reader's base process of `li-quote-lane`'s paper pair is free of the projection atoms.
Source: mandate T2.3
Kind: L
Fidelity: exact -/
theorem paperOneWayPair_atomFree (k : ℕ) : AtomFreeProcess (projAtomCode k) paperOneWayPair.DPH :=
  paperDP_atomFree 𝗜𝚺₁ k

/-- **The ledger instance.** Over `paperOneWayPair` (advisor `liaHistory (paperDP 𝗜𝚺₁)`, reader
`liaHistory (paperDP 𝗜𝚺₁ ⊕ ledger)`), the two projected readers at `c, c'` are inductors over the
same ledger process, agree at every `u`-free sentence, read the same published numbers, and differ
by `|c − c'|` in the limit. Scope: one-way.
Source: mandate T2.1 ("the one-way 'same `A`, same ledger' instance for T2.3"); [[root-deference-inventory]] 044(ii)
Kind: N+
Fidelity: exact
Hyps: (a) none; the inductor conjuncts rest on the OPEN rewriters -/
theorem paperLedgerProjection (c c' : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (hc'0 : 0 < c')
    (hc'1 : c' < 1) :
    IsLogicalInductor (project paperOneWayPair.H (projAtomCode 0) (fun _ => c))
      paperOneWayPair.process ∧
    IsLogicalInductor (project paperOneWayPair.H (projAtomCode 0) (fun _ => c'))
      paperOneWayPair.process ∧
    (∀ n φ, AtomFreeSentence (projAtomCode 0) φ →
      project paperOneWayPair.H (projAtomCode 0) (fun _ => c) n φ =
        project paperOneWayPair.H (projAtomCode 0) (fun _ => c') n φ) ∧
    (∀ j m r n, project paperOneWayPair.H (projAtomCode 0) (fun _ => c) n ((ledgerLuv j m).gt r) =
      paperOneWayPair.H n ((ledgerLuv j m).gt r)) ∧
    (∀ j m n, LUV.expect (project paperOneWayPair.H (projAtomCode 0) (fun _ => c)) n (ledgerLuv j m) =
      LUV.expect paperOneWayPair.H n (ledgerLuv j m)) ∧
    limitingBelief (project paperOneWayPair.H (projAtomCode 0) (fun _ => c)) (projAtom 0) = c ∧
    limitingBelief (project paperOneWayPair.H (projAtomCode 0) (fun _ => c')) (projAtom 0) = c' :=
  underdetermination_ledger paperOneWayPair 0 (paperOneWayPair_atomFree 0) c c' hc0 hc1 hc'0 hc'1

/-! ## T3.1's witness: two coordinates on two days -/

/-- The two-coordinate, two-day patch set `{(0, atom 0), (3, atom 1)}`.
Source: mandate T3.1 (N+: "patched at two coordinates on two different days")
Kind: D
Fidelity: n/a -/
def twoDayS : Finset (ℕ × Sentence) := {(0, Formula.atom 0), (3, Formula.atom 1)}

/-- The prescribed table: `1/3` on day `0`, `2/3` elsewhere.
Source: mandate T3.1
Kind: D
Fidelity: n/a -/
def twoDayT : ℕ → Sentence → ℚ := fun n _ => if n = 0 then 1 / 3 else 2 / 3

/-- **T3.1's witness**: FAF's paper LIA patched at `(0, atom 0) ↦ 1/3` and `(3, atom 1) ↦ 2/3` is a
logical inductor over `paperDP 𝗜𝚺₁` — two coordinates on two different days, strictly more than
FAF's one-point `liaPerturbed` (its own non-vacuity for the corrected `thm:ifp` is
`FreezeOracle.lic_iff_twoPoint`).
Source: mandate T3.1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperPatchTwoDays :
    IsLogicalInductor (patch (liaHistory (paperDP 𝗜𝚺₁)) twoDayS twoDayT) (paperDP 𝗜𝚺₁) :=
  prescribe_finiteSupport (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁)
    (hLI := LIA_is_logical_inductor _ (paperDP_computable _)) twoDayS twoDayT (by
      intro p hp
      simp only [twoDayS, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> norm_num [twoDayT])

/-- The prescription of `paperPatchTwoDays` is exact at both coordinates, and they lie on different
days.
Source: mandate T3.1 (`patch_mem`)
Kind: N+
Fidelity: exact -/
theorem paperPatchTwoDays_exact :
    patch (liaHistory (paperDP 𝗜𝚺₁)) twoDayS twoDayT 0 (Formula.atom 0) = 1 / 3 ∧
    patch (liaHistory (paperDP 𝗜𝚺₁)) twoDayS twoDayT 3 (Formula.atom 1) = 2 / 3 := by
  constructor
  · rw [patch_mem _ _ _ (by simp [twoDayS])]; norm_num [twoDayT]
  · rw [patch_mem _ _ _ (by simp [twoDayS])]; norm_num [twoDayT]

/-! ## T4.3's witness -/

/-- **The achievable rational limits over `paperDP 𝗜𝚺₁`**: every inductor over it has an interior
limit on `projAtom 0`, and every rational `c ∈ (0,1)` is attained by a projection of FAF's LIA.
Source: mandate T4.3 (LIA instance)
Kind: N+
Fidelity: exact
Hyps: (a) none; the (⊇) half rests on the OPEN rewriters -/
theorem paperAchievableLimits :
    (∀ P : History, IsLogicalInductor P (paperDP 𝗜𝚺₁) →
      limitingBelief P (projAtom 0) ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ c : ℚ, 0 < c → c < 1 →
      ∃ P : History, IsLogicalInductor P (paperDP 𝗜𝚺₁) ∧ limitingBelief P (projAtom 0) = c) := by
  haveI := LIA_is_logical_inductor (paperDP 𝗜𝚺₁) (paperDP_computable _)
  exact achievable_limits_fresh_atom_rat (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) (projAtomCode 0)
    (paperDP_atomFree 𝗜𝚺₁ 0) (liaHistory (paperDP 𝗜𝚺₁))

end Cleanroom.Li.LiProjection
