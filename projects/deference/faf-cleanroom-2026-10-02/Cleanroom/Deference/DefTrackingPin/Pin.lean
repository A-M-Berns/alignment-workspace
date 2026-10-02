import Cleanroom.Deference.DefTrackingPin.Defs
import Cleanroom.Found.LiQuoteLane.Readability
import Cleanroom.Found.LiQuoteLane.CrossQuote
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Construction.LUV.Endpoints

/-!
# `def-tracking-pin` · Pin: the pinning lemma, in its three grades (T1, T2, T3)

The corpus's Computable LUV Tracking / Pinning / Vanishing lemma (anson-042): if a contract
settles — the deductive process decides the thresholds of a `[0,1]`-LUV `X_n` to a value `v_n` —
then the reader's day-`n` price of `X_n` is forced to `v_n`. Over FAF the lemma's core is affine
provability induction (`PolySequence.affine_provind_theory_*`, `Properties/AffineCoherence.lean`,
the engine of `thm:expprovind`), and it comes in **three grades** that the corpus does not
separate:

* **T2, eventual** (`pinning_fixed`): a *fixed* LUV settled at `y` has `𝔼^P_n(X) → y`; equivalently
  FAF's `LUV.expectInf` is `y`. Grade (a): a constant target needs no coefficient.
* **T3, convergent-target** (`pinning_ofTendsto`): a settled e.c. *family* whose targets converge
  to any real `L` has `𝔼^P_n(X_n) ≈ₙ v_n`. Grade (a): FAF's one-sided vanishing-error forms
  (`affine_provind_theory_le_const` / `_ge_const`) take an *eventual* world bound, so no coefficient
  and no shift of the family is needed.
* **T1, timely / approximant** (`pinning_ofApprox`): a settled e.c. family with an *arbitrary*
  target `v_n` has `𝔼^P_n(X_n) ≈ₙ v_n` **provided** some `P`-generable rational `ẑ_n` approximates
  `v_n` (`hz : PGenerableRat P ẑ`, FAF's `def:ece`). The target is centred into the affine
  combination as a coefficient (`mesh_{n+1}(X_n) − ⟨feature of ẑ_n⟩`), and a coefficient enters a
  `PolySequence` only if it is machine-metered. **`hz` is the one clause the corpus hides**: the
  "`v_n` is `𝒞`-computable" of anson-042, the "(A4) power" of root-deference-038, the 2b cost story —
  surfacing as a type. It is a modelling substitution (c): FAF has one trader class, so the corpus's
  relativized `𝒞_A`-computability is rendered as generability of the approximant in the plain
  class. On a convergent or constant target `hz` is idle (T3 / T2 discharge it with
  `MachineRatCodes.const`), so the witness on which T1 *as written* is load-bearing must be a
  target with no limit (`Witnesses.lean`, the oscillating table of `li-quote-lane`).

The ledger-LUV instance of T1 is `li-quote-lane`'s `readability_ofApprox` (Lemma 2.1 in approximant
form), whose route this file generalizes to an arbitrary e.c. LUV family: `pinning_ledger` below
re-derives it from `pinning_ofApprox` so that the two are visibly the same theorem.

**Roles.** `P` is the **reader** throughout — the inductor whose day-`n` expectation is forced; in
the deference story this is `A` (the predictor, whose process `D_A` adjoins the settlement), and the
settled value is `H`'s deferred credence. No other `History` appears in this file. **Scope:
one-way.** **Settlement is an FAF fact**: `hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n)` — the
settlement stage `σ(n)` does not appear (`Defs.lean`), and `v` is *not* a hypothesis-bounded real
sequence standing in for settlement (the [[AUDIT]] §3.3 squeeze this package replaces).
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## The engine: convergent-target pinning from a mesh certificate -/

/-- **The engine of T2 and T3.** For a reader `P` over `DP` (every stage satisfiable) and a LUV
family `X` whose diagonal threshold mesh `n ↦ mesh_{n+1}(X_n)` is a `PolySequence`, if every `X_n`
is settled at `v_n` and `v_n → L` (any real), then the reader's day-`n` expectation `𝔼^P_n(X_n)`
tends to `L`. Route: the mesh prices are in `[0,1]` (`expectAffineSeq_boundedPrices`) with unit
magnitude; in every completed-theory world the mesh value is within `1/(n+1)` of `v_n`
(`determinedVia_expectApprox_near`), hence eventually within `ε` of `L`; FAF's one-sided
vanishing-error affine provability induction (`affine_provind_theory_le_const` / `_ge_const`) gives
`price ≲ₙ L` and `≳ₙ L`, and the diagonal price is `𝔼^P_n(X_n)` (`LUV.expectAffine_price`). **No
generability of the target**: the bound is a constant, so nothing is centred. The mesh certificate
is the only input not derived here; T3 supplies it from the e.c. certificate of the family, T2 from
the single LUV's. Reader `P`; one-way.
Source: anson-042 (chat 10 L9411, L16147–16200), the "eventual" grade; anson-030; FAF `thm:expprovind` (`Construction/LUV/Endpoints.lean`) and `thm:affprovind` one-sided vanishing-error forms
Kind: C
Fidelity: exact (the limit form; the corpus's `v_n ∈ ℚ` is relaxed to real targets)
Hyps: (a) none (`hpoly` is a certificate the headlines derive) -/
theorem pin_tendsto_of_polySequence {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (hpoly : AffineCombination.PolySequence (fun n => (X n).expectAffine (n + 1)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    {L : ℝ} (hconv : Tendsto v atTop (𝓝 L)) :
    Tendsto (fun n => (X n).expect P n) atTop (𝓝 L) := by
  have hbounded := expectAffineSeq_boundedPrices X P DP
  have hmag : ∃ C : ℝ, ∀ n, ((X n).expectAffine (n + 1)).magnitude P ≤ C :=
    ⟨1, fun n => (X n).expectAffine_magnitude_le_one P (n + 1)⟩
  have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hvL : Tendsto (fun n => |v n - L|) atTop (𝓝 0) := by
    have := (tendsto_sub_nhds_zero_iff.2 hconv).abs
    rwa [abs_zero] at this
  have hnear : ∀ ε > 0, ∀ᶠ n in atTop, ∀ w : PCWorld, w.ConsistentWithTheory DP →
      |((X n).expectAffine (n + 1)).value P w.payout - L| ≤ ε := by
    intro ε hε
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hvL.eventually (eventually_le_nhds (half_pos hε))] with n hn1 hn2 w hw
    rw [LUV.expectAffine_value]
    have h1 := determinedVia_expectApprox_near (hdet n) (Nat.succ_pos n) w hw
    calc |(X n).expectApprox w.payout (n + 1) - L|
        ≤ |(X n).expectApprox w.payout (n + 1) - v n| + |v n - L| := abs_sub_le _ _ _
      _ ≤ 1 / ((n + 1 : ℕ) : ℝ) + |v n - L| := by gcongr
      _ = 1 / ((n : ℝ) + 1) + |v n - L| := by push_cast; rfl
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := by ring
  have hle := hpoly.affine_provind_theory_le_const P DP hbounded hmag hworld L
    (fun ε hε => by
      filter_upwards [hnear ε hε] with n hn w hw
      linarith [(abs_le.1 (hn w hw)).2])
  have hge := hpoly.affine_provind_theory_ge_const P DP hbounded hmag hworld L
    (fun ε hε => by
      filter_upwards [hnear ε hε] with n hn w hw
      linarith [(abs_le.1 (hn w hw)).1])
  have heq : (fun n => ((X n).expectAffine (n + 1)).price P n) ≈ₙ fun _ => L :=
    asympEq_iff_asympLE_asympGE.2 ⟨hle, hge⟩
  have hconv' : Tendsto (fun n => ((X n).expectAffine (n + 1)).price P n) atTop (𝓝 L) :=
    convergesTo_iff_asympEq_const.2 heq
  exact hconv'.congr fun n => (X n).expectAffine_price P n

/-! ## T3: convergent-target pinning (grade (a), no generability) -/

/-- **T3 (headline), limit form. Convergent-target pinning:** for a reader `P` over `DP` (every
stage satisfiable), an e.c. family `X` of `[0,1]`-LUVs (`hX : LUV.MachineThresholdCodeSeq X`) each
settled at `v_n` (`hdet`), and any real `L` with `v_n → L`: `𝔼^P_n(X_n) → L`. **No generability
hypothesis**: the engine `pin_tendsto_of_polySequence` at the mesh certificate FAF derives from
`hX` (`LUV.expectAffineSeq_polySequence`). This is anson-030's per-sentence limit agreement in
general form (the "trivial predictor" `v_n → L` suffices) and the convergent case of anson-2-022
Theorem 2; it strictly extends `li-quote-lane`'s `readability_ofTendsto` (rational limit, ledger
LUV) to real limits and arbitrary e.c. families. Reader `P`; one-way.
Source: anson-030 ([[trust-between-inductors-summary-v2]] §2.1; chat 11 Claim 3(c)); anson-2-022 Theorem 2, convergent case (chat 01 L1539–1546); anson-043 corollary
Kind: C
Fidelity: exact (real limit; the family's e.c. certificate is FAF's `def:ec` machine reading)
Hyps: (a) none -/
theorem pinning_tendsto {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    {L : ℝ} (hconv : Tendsto v atTop (𝓝 L)) :
    Tendsto (fun n => (X n).expect P n) atTop (𝓝 L) :=
  pin_tendsto_of_polySequence (LUV.expectAffineSeq_polySequence X hX) hworld hdet hconv

/-- **T3 (headline), tracking form:** under the hypotheses of `pinning_tendsto`,
`𝔼^P_n(X_n) ≈ₙ v_n` — the reader's day-`n` price tracks the settled target, with no generability
of the target, because the target converges. Reader `P`; one-way.
Source: anson-030; anson-2-022 Theorem 2 (convergent case); anson-043 corollary
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem pinning_ofTendsto {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    {L : ℝ} (hconv : Tendsto v atTop (𝓝 L)) :
    (fun n => (X n).expect P n) ≈ₙ v := by
  have h := pinning_tendsto (P := P) hX hworld hdet hconv
  unfold AsympEq
  have := h.sub hconv
  rwa [sub_self] at this

/-! ## T3, one-sided forms: an eventual one-sided bound on the target -/

/-- **One-sided engine, `≲ₙ` form:** `pin_tendsto_of_polySequence`'s hypotheses with the
convergence `v_n → L` weakened to the eventual upper bound `∀ ε > 0, ∀ᶠ n, v_n ≤ L + ε` give the
reader's expectations `≲ₙ L` — the same route, one side of FAF's `affine_provind_theory_le_const`.
Used by the diagonal reading of T6 (`Column.lean`), where the padded target has no limit.
Reader `P`; one-way.
Source: none: infrastructure (the `≲ₙ` half of `pin_tendsto_of_polySequence`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem pin_asympLE_of_polySequence {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (hpoly : AffineCombination.PolySequence (fun n => (X n).expectAffine (n + 1)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    {L : ℝ} (hle : ∀ ε > 0, ∀ᶠ n in atTop, v n ≤ L + ε) :
    (fun n => (X n).expect P n) ≲ₙ fun _ => L := by
  have hbounded := expectAffineSeq_boundedPrices X P DP
  have hmag : ∃ C : ℝ, ∀ n, ((X n).expectAffine (n + 1)).magnitude P ≤ C :=
    ⟨1, fun n => (X n).expectAffine_magnitude_le_one P (n + 1)⟩
  have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear : ∀ ε > 0, ∀ᶠ n in atTop, ∀ w : PCWorld, w.ConsistentWithTheory DP →
      ((X n).expectAffine (n + 1)).value P w.payout ≤ L + ε := by
    intro ε hε
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hle (ε / 2) (half_pos hε)] with n hn1 hn2 w hw
    rw [LUV.expectAffine_value]
    have h1 := determinedVia_expectApprox_near (hdet n) (Nat.succ_pos n) w hw
    have h2 : (X n).expectApprox w.payout (n + 1) - v n ≤ 1 / ((n : ℝ) + 1) := by
      have := (abs_le.1 h1).2
      push_cast at this
      linarith
    linarith
  have hle' := hpoly.affine_provind_theory_le_const P DP hbounded hmag hworld L
    (fun ε hε => by
      filter_upwards [hnear ε hε] with n hn w hw
      exact hn w hw)
  intro ε hε
  filter_upwards [hle' ε hε] with n hn
  rwa [(X n).expectAffine_price P n] at hn

/-- **One-sided engine, `≳ₙ` form:** dual of `pin_asympLE_of_polySequence`.
Source: none: infrastructure (the `≳ₙ` half of `pin_tendsto_of_polySequence`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem pin_asympGE_of_polySequence {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (hpoly : AffineCombination.PolySequence (fun n => (X n).expectAffine (n + 1)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    {L : ℝ} (hge : ∀ ε > 0, ∀ᶠ n in atTop, L - ε ≤ v n) :
    (fun n => (X n).expect P n) ≳ₙ fun _ => L := by
  have hbounded := expectAffineSeq_boundedPrices X P DP
  have hmag : ∃ C : ℝ, ∀ n, ((X n).expectAffine (n + 1)).magnitude P ≤ C :=
    ⟨1, fun n => (X n).expectAffine_magnitude_le_one P (n + 1)⟩
  have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear : ∀ ε > 0, ∀ᶠ n in atTop, ∀ w : PCWorld, w.ConsistentWithTheory DP →
      L - ε ≤ ((X n).expectAffine (n + 1)).value P w.payout := by
    intro ε hε
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hge (ε / 2) (half_pos hε)] with n hn1 hn2 w hw
    rw [LUV.expectAffine_value]
    have h1 := determinedVia_expectApprox_near (hdet n) (Nat.succ_pos n) w hw
    have h2 : -(1 / ((n : ℝ) + 1)) ≤ (X n).expectApprox w.payout (n + 1) - v n := by
      have := (abs_le.1 h1).1
      push_cast at this
      linarith
    linarith
  have hge' := hpoly.affine_provind_theory_ge_const P DP hbounded hmag hworld L
    (fun ε hε => by
      filter_upwards [hnear ε hε] with n hn w hw
      exact hn w hw)
  intro ε hε
  filter_upwards [hge' ε hε] with n hn
  rwa [(X n).expectAffine_price P n] at hn

/-- **T3, one-sided `≲ₙ` form (headline):** an e.c. family settled at `v_n` with `v_n ≤ L + ε`
eventually, for every `ε`, has `𝔼^P_n(X_n) ≲ₙ L`; no generability. The convergent case
`pinning_tendsto` is the conjunction of this and `pinning_asympGE`; the diagonal reading of T6
(`deferred_diagonal_subsequence`, `Column.lean`) is where the one-sided forms earn their keep: a
padded target with no limit that is eventually on the right side of `L`. Reader `P`; one-way.
Source: anson-030; anson-2-022 Theorem 2 (the one-sided reading); FAF `thm:affprovind`
Kind: C
Fidelity: exact (one-sided, eventual)
Hyps: (a) none -/
theorem pinning_asympLE {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    {L : ℝ} (hle : ∀ ε > 0, ∀ᶠ n in atTop, v n ≤ L + ε) :
    (fun n => (X n).expect P n) ≲ₙ fun _ => L :=
  pin_asympLE_of_polySequence (LUV.expectAffineSeq_polySequence X hX) hworld hdet hle

/-- **T3, one-sided `≳ₙ` form (headline):** dual of `pinning_asympLE`. Reader `P`; one-way.
Source: anson-030; anson-2-022 Theorem 2 (the one-sided reading); FAF `thm:affprovind`
Kind: C
Fidelity: exact (one-sided, eventual)
Hyps: (a) none -/
theorem pinning_asympGE {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    {L : ℝ} (hge : ∀ ε > 0, ∀ᶠ n in atTop, L - ε ≤ v n) :
    (fun n => (X n).expect P n) ≳ₙ fun _ => L :=
  pin_asympGE_of_polySequence (LUV.expectAffineSeq_polySequence X hX) hworld hdet hge

/-! ## T2: eventual pinning of a fixed LUV; the snapshot identity -/

/-- **T2 (headline). Eventual pinning of a fixed LUV:** for a reader `P` over `DP` (every stage
satisfiable) and a single e.c. `[0,1]`-LUV `X` (`hcode : X.MachineThresholdCodes`) settled at `y`
(`hdet : LUV.DeterminedVia X DP y`): `𝔼^P_n(X) → y`. Grade (a), no generability: a **constant**
target needs no coefficient. This is the "eventual" grade of anson-042 and exactly what the
corpus's "4.8.10 has no timeliness clause" (anson-2-010, chat 05 L11043) is true of: the day index
of the *LUV* does not move. Stating it for a sequence `X_n` with the day index moving is T1 and
needs `hz`. Route: the engine `pin_tendsto_of_polySequence` at the constant family, with FAF's
`LUV.expectAffine_polySequence` shifted to the diagonal (`PolySequence.shift`, as in FAF's
`LUV.expect_converges`). Reader `P`; one-way.
Source: anson-042 ("eventual vs timely"); anson-2-010 (chat 05 L11043); anson-043 (the snapshot identity, instantiated in `Column.lean`); FAF `thm:ec` (`Properties/ExpectationConvergence.lean`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem pinning_fixed {X : LUV} {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hcode : X.MachineThresholdCodes)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {y : ℝ} (hdet : LUV.DeterminedVia X DP y) :
    Tendsto (fun n => X.expect P n) atTop (𝓝 y) := by
  have hpoly : AffineCombination.PolySequence (fun n => X.expectAffine (n + 1)) :=
    (X.expectAffine_polySequence hcode).shift
      (fun n => by simp [LUV.expectAffine])
      (fun n p hp => by
        simp only [LUV.expectAffine, List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [EF.rank])
  exact pin_tendsto_of_polySequence (X := fun _ => X) (P := P) (DP := DP) hpoly hworld
    (fun _ => hdet) tendsto_const_nhds

/-- **T2, `≈ₙ` form:** `𝔼^P_n(X) ≈ₙ y` for a fixed settled e.c. LUV. Reader `P`; one-way.
Source: anson-042 ("eventual" grade)
Kind: L (restatement of `pinning_fixed`)
Fidelity: exact
Hyps: (a) none -/
theorem pinning_fixed_asympEq {X : LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hcode : X.MachineThresholdCodes)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {y : ℝ} (hdet : LUV.DeterminedVia X DP y) :
    (fun n => X.expect P n) ≈ₙ fun _ => y :=
  convergesTo_iff_asympEq_const.1 (pinning_fixed (P := P) hcode hworld hdet)

/-- **T2, in FAF's `thm:ec` vocabulary: the limiting expectation of a settled LUV is its settled
value.** `LUV.expectInf P DP X …` (FAF's `𝔼_∞(X)`, the limit `thm:ec` provides for every e.c. LUV
valued by every completed world) equals `y`, by uniqueness of limits
(`LUV.expectInf_eq_of_convergesTo`). This is the snapshot identity of anson-043 in its general
form — "the settled contract's limiting price is the snapshot" — exact, with no `1/2n` rounding
(FAF's LUV has thresholds at every rational; the corpus's rounding of the target to the `1/n` grid
does not occur). Stated at the LUV (`expectInf`, the full-precision limit), not at the corpus's
precision-`n` contract `C_n` (`contract X n`, T8 (i)); the contract-level identity within `1/n` is
a corollary of `contract_value_near` not shipped (FAF has no constant-family `PolySequence` to run
affine coherence at a fixed combination). Reader `P`; one-way.
Source: anson-043 (chat 03 L4437–4455, the identity `H⁺_∞(C_n) = H_{F(n)}(P^{(n)}) ± 1/2n`); FAF `LUV.expectInf` (`thm:ec`)
Kind: C
Fidelity: stronger: exact, no rounding — at the LUV (`expectInf`) in place of the precision-`n` contract; the contract-level form within `1/n` is a corollary of T8 (i), not shipped
Hyps: (a) none -/
theorem pinning_fixed_expectInf {X : LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hcode : X.MachineThresholdCodes)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {y : ℝ} (hdet : LUV.DeterminedVia X DP y) :
    X.expectInf P DP hcode hworld (determinedVia_exists_valuesAt hdet) = y :=
  (X.expectInf_eq_of_convergesTo P DP hcode hworld (determinedVia_exists_valuesAt hdet)
    (pinning_fixed (P := P) hcode hworld hdet)).symm

/-! ## T1: the pinning lemma, approximant form (the timely grade; `hz` is the (c)) -/

/-- **T1 (headline). The pinning lemma, approximant form** (anson-042's Computable LUV Tracking /
Pinning lemma; anson-2-010's centering route; root-deference-038's honest L variant): for a reader
`P` over `DP` (every stage satisfiable), an e.c. family `X` of `[0,1]`-LUVs (`hX`) each settled at
`v_n` (`hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n)` — settlement as an FAF fact; the settlement
stage `σ(n)` of the corpus does not appear, since `DeterminedVia` quantifies over completed-theory
worlds and "decided by `σ(n)`" implies it), and a `P`-generable rational approximant `ẑ` of the
target (`hz : PGenerableRat P ẑ`, FAF's `def:ece`; `hlim : ẑ_n − v_n → 0`):
`𝔼^P_n(X_n) ≈ₙ v_n`, per day, full limit (`≈ₙ` is `Tendsto (f − g) atTop (𝓝 0)`,
`Framework/Asymptotics.lean`).

Route (the one `li-quote-lane`'s `readability_ofApprox` walks for `X_n := α_{j,n}`, generalized —
`pinning_ledger` below recovers that instance): the affine sequence
`A_n := mesh_{n+1}(X_n) − ⟨feature of ẑ_n⟩` is a `PolySequence` (FAF's
`LUV.expectAffineSeq_polySequence` at `hX` for the mesh, `hz`'s feature for the constant through
`polySequence_addConstEF`); its prices are bounded (`v_n ∈ [0,1]` by `determinedVia_mem_Icc`, and
the approximation error is a convergent, hence bounded, sequence); its completed-theory value is
within `1/(n+1) + |ẑ_n − v_n|` of `0` (`determinedVia_expectApprox_near`); FAF's vanishing-error
affine provability induction `PolySequence.affine_provind_theory_tendsto_zero` gives `price → 0`,
the price is `𝔼^P_n(X_n) − ẑ_n`, and `hlim` finishes.

**`hz` is the H-class clause of the corpus, surfacing as a type.** FAF's endpoints converge to a
*constant*; a varying target enters only as a coefficient of the combination, and a coefficient
enters a `PolySequence` only if it is machine-metered. The corpus's "`v_n` is `𝒞`-computable"
(anson-042), "(A4) power" (root-deference-038) and the 2b cost story are this clause. It is **not
(a)**: FAF has one trader class, so the corpus's relativized `𝒞_A`-computability of `v_n` is
rendered as generability of the approximant in the plain class — a modelling substitution. On a
convergent target `hz` is idle (`pinning_ofTendsto` discharges it with the constant approximant),
so the witness on which this theorem *as written* is load-bearing is a target with no limit
(`Witnesses.lean`). Reader `P` (the deference story's `A`); one-way.
Source: anson-042 (chat 10 L9411, L16147–16200; chat 07 "Vanishing Lemma"); anson-2-010 (chat 05 L10790–10800, the centering route `B'_n := C_n − m*_n/n`); root-deference-038 ([[deference-in-logical-induction-v6]] §5.4 T1 line 582), the honest L variant; [[AUDIT]] §3.3 (`faithful_tracking`, the squeeze this replaces)
Kind: C
Fidelity: variant: plain trader class — the corpus's `𝒞_A`-computable target rendered as `P`-generability of an approximant (`hz`); `[0,1]`-LUV families via the diagonal mesh in place of the source's general e.c. affine combinations with `W(X_n) ∈ [0,1]` (the general form is FAF's `affine_provind_theory_tendsto_zero` plus the same `hz`); settlement rendered as `DeterminedVia` (time-free; the stage `σ(n)` and the source's `𝒞`-computable settlement time `τ` do not appear — a weaker hypothesis than the source's stage-`t` world quantifier, hence a stronger theorem on that axis); real targets admitted
Hyps: (c) `hz` — generability of the target/approximant in FAF's one trader class, standing in for the corpus's `𝒞_A`-computability of `v_n` ((A4) power / 2b); all else (a) -/
theorem pinning_ofApprox {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    (zhat : ℕ → ℚ) (hz : PGenerableRat P zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - v n) atTop (𝓝 0)) :
    (fun n => (X n).expect P n) ≈ₙ v := by
  obtain ⟨feat, hfeat⟩ := hz
  have hneg : PGenerableWeighting (fun n => EF.mul (EF.const (-1)) (feat n)) :=
    PGenerableWeighting.mul (pgenerableWeighting_const (-1)) hfeat.toWeighting
  set As : ℕ → AffineCombination := fun n =>
    ((X n).expectAffine (n + 1)).addConstEF (EF.mul (EF.const (-1)) (feat n)) with hAs
  have hpoly : AffineCombination.PolySequence As :=
    polySequence_addConstEF (LUV.expectAffineSeq_polySequence X hX) _ hneg
  have hprices : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hconst : ∀ n, (EF.mul (EF.const (-1)) (feat n)).denote P = -(zhat n : ℝ) := by
    intro n
    simp [hfeat.denote n]
  have hvalue : ∀ n (w : Valuation),
      (As n).value P w = (X n).expectApprox w (n + 1) - zhat n := by
    intro n w
    rw [hAs]
    dsimp only
    rw [AffineCombination.addConstEF_value, LUV.expectAffine_value, hconst]
    ring
  have hprice : ∀ n, (As n).price P n = (X n).expect P n - zhat n := by
    intro n
    rw [AffineCombination.price, hvalue]
    rfl
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, |(zhat n : ℝ) - v n| ≤ B := by
    obtain ⟨B, hB⟩ := (hlim.abs).bddAbove_range
    exact ⟨B, fun n => hB (Set.mem_range_self n)⟩
  have hvmem : ∀ n, 0 ≤ v n ∧ v n ≤ 1 := fun n => determinedVia_mem_Icc (hdet n) hworld
  have hbounded : BoundedAffinePrices As P := by
    refine ⟨2 + B, ?_, fun n m => ?_⟩
    · have h0 := hB 0
      have h0' := abs_nonneg ((zhat 0 : ℝ) - v 0)
      linarith
    rw [AffineCombination.price, hvalue]
    have h1 := (X n).expectApprox_nonneg (P m) (n + 1) (fun s => (hprices m s).1)
    have h2 := (X n).expectApprox_le_one (P m) (n + 1) (fun s => (hprices m s).2)
    obtain ⟨h3, h4⟩ := hvmem n
    obtain ⟨h5, h6⟩ := abs_le.mp (hB n)
    rw [abs_le]
    constructor <;> linarith
  have hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C := by
    refine ⟨1, fun n => ?_⟩
    rw [hAs]
    dsimp only
    rw [AffineCombination.addConstEF_magnitude]
    exact LUV.expectAffine_magnitude_le_one _ P _
  have hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ w : PCWorld,
      w.ConsistentWithTheory DP → |(As n).value P w.payout| ≤ ε := by
    intro ε hε
    have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim2 : Tendsto (fun n => |(zhat n : ℝ) - v n|) atTop (𝓝 0) := by
      have := hlim.abs
      rwa [abs_zero] at this
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hlim2.eventually (eventually_le_nhds (half_pos hε))] with n hn1 hn2 w hw
    rw [hvalue]
    have hnear := determinedVia_expectApprox_near (hdet n) (Nat.succ_pos n) w hw
    calc |(X n).expectApprox w.payout (n + 1) - zhat n|
        = |((X n).expectApprox w.payout (n + 1) - v n) + (v n - zhat n)| := by
          congr 1
          ring
      _ ≤ |(X n).expectApprox w.payout (n + 1) - v n| + |v n - zhat n| := abs_add_le _ _
      _ = |(X n).expectApprox w.payout (n + 1) - v n| + |(zhat n : ℝ) - v n| := by
          rw [abs_sub_comm (v n) (zhat n : ℝ)]
      _ ≤ 1 / ((n + 1 : ℕ) : ℝ) + |(zhat n : ℝ) - v n| := by gcongr
      _ = 1 / ((n : ℝ) + 1) + |(zhat n : ℝ) - v n| := by push_cast; rfl
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := by ring
  have hlim0 := hpoly.affine_provind_theory_tendsto_zero P DP hbounded hmag hworld hval
  unfold AsympEq at hlim0 ⊢
  have h1 : Tendsto (fun n => (X n).expect P n - zhat n) atTop (𝓝 0) := by
    refine hlim0.congr fun n => ?_
    dsimp only
    rw [hprice, sub_zero]
  have h3 := h1.add hlim
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

/-- **T1′, machine-computed approximants:** the corpus's literal form — "a machine computes
rationals `ẑ_n` with `|ẑ_n − v_n| → 0`" — with the machine FAF's machine-metered rational code
stream `MachineRatCodes` (the plain-class counterpart of the corpus's `𝒞_A`-machine). Instance of
`pinning_ofApprox` through `PGenerableRat.ofMachineRatCodes`. Reader `P`; one-way.
Source: anson-042 ("`v_n` `𝒞`-computable", the approximant reading)
Kind: L (instance of `pinning_ofApprox`)
Fidelity: variant: plain trader class (the `𝒞`-machine rendered as FAF's `MachineRatCodes`)
Hyps: (c) `hz` (machine-metered codes for the approximant, in place of the corpus's relativized machine class); all else (a) -/
theorem pinning_ofMachineApprox {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    (zhat : ℕ → ℚ) (hz : MachineRatCodes zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - v n) atTop (𝓝 0)) :
    (fun n => (X n).expect P n) ≈ₙ v :=
  pinning_ofApprox hX hworld hdet zhat (PGenerableRat.ofMachineRatCodes hz P) hlim

/-- **T1″, the exact approximant:** a rational target `v` that is itself `P`-generable
(`hv : PGenerableRat P v` — the corpus's "`v_n` is `𝒞`-computable" literally, in the plain class)
is tracked: `𝔼^P_n(X_n) ≈ₙ v_n`. Instance of `pinning_ofApprox` at `ẑ = v`. Reader `P`; one-way.
Source: anson-042 ("`v_n ∈ ℚ ∩ [0,1]` `𝒞`-computable"); root-deference-038 (L variant, "if the target is e.c.")
Kind: L (instance of `pinning_ofApprox`)
Fidelity: variant: plain trader class
Hyps: (c) `hv` (generability of the target in FAF's one class, for the corpus's `𝒞`-computability); all else (a) -/
theorem pinning_exact {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (v : ℕ → ℚ) (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n)) (hv : PGenerableRat P v) :
    (fun n => (X n).expect P n) ≈ₙ (fun n => (v n : ℝ)) :=
  pinning_ofApprox hX hworld hdet v hv (by
    simp only [sub_self]
    exact tendsto_const_nhds)

/-- **The uniqueness corollary of anson-2-022** (Theorem 2's "`A_n(φ)` is the asymptotically unique
calibrated predictor"): the reader's day-`n` expectation of a settled e.c. family coincides
asymptotically with *every* generable approximant of the target, so any two such approximants agree
asymptotically. The first clause is `pinning_ofApprox` restated; the second is trivial from the two
approximation hypotheses alone (`ẑ¹_n − v_n → 0` and `ẑ²_n − v_n → 0`) and does not use the
inductor, nor any generability of `ẑ²` — kind L, said so. Reader `P`; one-way.
Source: anson-2-022, Corollary of Theorem 2 (chat 01 L1539–1546)
Kind: L
Fidelity: exact (as a corollary; the content is T1)
Hyps: (c) `hz₁` (as `pinning_ofApprox`; the second clause needs no generability at all) -/
theorem pinning_approximants_agree {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {v : ℕ → ℝ} (hdet : ∀ n, LUV.DeterminedVia (X n) DP (v n))
    (z₁ z₂ : ℕ → ℚ) (hz₁ : PGenerableRat P z₁)
    (hlim₁ : Tendsto (fun n => (z₁ n : ℝ) - v n) atTop (𝓝 0))
    (hlim₂ : Tendsto (fun n => (z₂ n : ℝ) - v n) atTop (𝓝 0)) :
    ((fun n => (X n).expect P n) ≈ₙ (fun n => (z₁ n : ℝ))) ∧
      ((fun n => (z₁ n : ℝ)) ≈ₙ (fun n => (z₂ n : ℝ))) := by
  have h₁ := pinning_ofApprox hX hworld hdet z₁ hz₁ hlim₁
  have hv₁ : v ≈ₙ fun n => (z₁ n : ℝ) := by
    unfold AsympEq
    have := hlim₁.neg
    rw [neg_zero] at this
    exact this.congr fun n => by ring
  have hv₂ : v ≈ₙ fun n => (z₂ n : ℝ) := by
    unfold AsympEq
    have := hlim₂.neg
    rw [neg_zero] at this
    exact this.congr fun n => by ring
  exact ⟨h₁.trans hv₁, hv₁.symm.trans hv₂⟩

/-! ## One-sided forms at the paper's premise (no determinacy) -/

/-- The singleton-combination family `n ↦ 0 + 1·X_n` of an e.c. LUV family is FAF's
`LUVCombination.BoundedSequence` at any market (polynomial mesh from `hX`, unit `L¹` norm).
Source: none: infrastructure (`li-quote-lane` `ofLUV_mesh_polySequence`, `li-asymp-calc` `l1Norm_ofLUV`)
Kind: L
Fidelity: n/a -/
noncomputable def ofLUV_boundedSequence {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (P : History) : LUVCombination.BoundedSequence (fun n => LUVCombination.ofLUV (X n)) P where
  poly := ⟨ofLUV_mesh_polySequence X hX⟩
  bounded := ⟨1, fun n => (l1Norm_ofLUV (X n) P).2.le⟩

/-- **T1, one-sided `≲ₙ` form at the paper's premise:** if every completed-theory world values
every `X_n` (`hwv`) and every such value is `≤ c` (`hval`), the reader's expectations are `≲ₙ c`.
No determinacy and no generability: FAF's `lic_expect_combination_provind_le` (`thm:expprovind`)
at the singleton combinations. The one-sided world bound is the corpus's "`W(X_n) ≤ v`" with a
*constant* `v`. Reader `P`; one-way.
Source: anson-042 (the one-sided reading); FAF `thm:expprovind`
Kind: L (one application of FAF's endpoint)
Fidelity: exact (constant bound)
Hyps: (a) none -/
theorem pinning_le_of_worldBound {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hwv : ∀ n (w : PCWorld), w.ConsistentWithTheory DP → ∃ x : ℝ, w.ValuesAt (X n) x)
    (c : ℝ) (hval : ∀ n (w : PCWorld), w.ConsistentWithTheory DP →
      ∀ x : ℝ, w.ValuesAt (X n) x → x ≤ c) :
    (fun n => (X n).expect P n) ≲ₙ fun _ => c := by
  have h := lic_expect_combination_provind_le (ofLUV_boundedSequence hX P)
    (worldValued_ofLUV hwv) c
    (fun n w hw ν hν => by
      rw [ofLUV_value]
      exact hval n w hw (ν (X n)) ((valuesAt_ofLUV_iff w (X n) ν).1 hν)) hworld
  intro ε hε
  filter_upwards [h ε hε] with n hn
  rwa [ofLUV_expect] at hn

/-- **T1, one-sided `≳ₙ` form at the paper's premise:** dual of `pinning_le_of_worldBound`.
Reader `P`; one-way.
Source: anson-042 (the one-sided reading); FAF `thm:expprovind`
Kind: L (one application of FAF's endpoint)
Fidelity: exact (constant bound)
Hyps: (a) none -/
theorem pinning_ge_of_worldBound {X : ℕ → LUV} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hX : LUV.MachineThresholdCodeSeq X)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hwv : ∀ n (w : PCWorld), w.ConsistentWithTheory DP → ∃ x : ℝ, w.ValuesAt (X n) x)
    (c : ℝ) (hval : ∀ n (w : PCWorld), w.ConsistentWithTheory DP →
      ∀ x : ℝ, w.ValuesAt (X n) x → c ≤ x) :
    (fun n => (X n).expect P n) ≳ₙ fun _ => c := by
  have h := lic_expect_combination_provind_ge (ofLUV_boundedSequence hX P)
    (worldValued_ofLUV hwv) c
    (fun n w hw ν hν => by
      rw [ofLUV_value]
      exact hval n w hw (ν (X n)) ((valuesAt_ofLUV_iff w (X n) ν).1 hν)) hworld
  intro ε hε
  filter_upwards [h ε hε] with n hn
  rwa [ofLUV_expect] at hn

/-! ## The ledger instance -/

/-- **T1 at the ledger LUV family — `li-quote-lane`'s `readability_ofApprox` (Lemma 2.1, ledger
tracking) re-derived from the general pinning lemma**, so that the ledger case and the general case
are visibly the same theorem: `X_n := α_{j,n}` with its e.c. certificate `ledgerLuv_thresholdCodes`
and its settlement `ledgerLuv_determinedVia` (T1.2 of that package, a theorem, not a hypothesis).
The reader `P` is any inductor over the ledger-augmented process `DP_H ⊕ ledger`; `hworld` is T1.5
of that package. Reader `P`; one-way.
Source: [[route-recurring-ccee]] §2 Lemma 2.1 (`li-quote-lane` `readability_ofApprox`); anson-042 at the ledger
Kind: L (instance of `pinning_ofApprox`; the same statement as `readability_ofApprox`)
Fidelity: variant: plain trader class (as `pinning_ofApprox`)
Hyps: (c) `hz` (as `pinning_ofApprox`); all else (a) -/
theorem pinning_ledger (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ)
    (zhat : ℕ → ℚ) (hz : PGenerableRat P zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - a j n) atTop (𝓝 0)) :
    (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) :=
  pinning_ofApprox (ledgerLuv_thresholdCodes j) hworld
    (fun n => ledgerLuv_determinedVia base a e hmem j n) zhat hz hlim

end Cleanroom.Deference.DefTrackingPin
