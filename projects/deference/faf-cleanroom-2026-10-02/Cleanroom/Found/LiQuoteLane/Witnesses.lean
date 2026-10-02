import Cleanroom.Found.LiQuoteLane.Readability
import Cleanroom.Found.LiQuoteLane.PaperQuotation
import Cleanroom.Found.LiQuoteLane.PaperWitness
import Cleanroom.Found.LiQuoteLane.MirrorPair

/-!
# `li-quote-lane` · Witnesses: full-package inhabitants of T3.1 and T2.1/T2.4 over real objects

Adopted from the audit probes (round 1: `run/wp/li-quote-lane/audit-r1-probes/`, adversarial B2
and non-blocking 1, fidelity N2; round 2: `audit-r2-probes/`, fidelity B1 / adversarial
non-blocking 1 and 2). Everything here is over FAF's real objects: the base is `paperDP 𝗜𝚺₁`, the
reader is FAF's `liaHistory` over the ledger process (T6.1's argument), `hworld` is T1.5 at the
real base (`ledgerProcess_paperDP_hworld`), and the world quantifier is shown non-empty by
compactness.

* **T3.1 (`readability`), full package inhabited — primary witness `readability_unpair`.** The
  oscillating table `a j n = 1/(unpair₂ n + 1)` (FAF's harmonic weight reindexed by FAF's ruler
  `UnaryRuler.unpairSnd`, so `MachineRatCodes` by `MachineRatCodes.comp` and `PGenerableRat` at
  every market) is `1` along `⟨m, 0⟩` and `1/2` along `⟨m, 1⟩`, so it has no limit
  (`unpairTable_not_convergent`), and `readability` at it forces the reader's expectation of the
  ledger LUV to have no limit either (`unpair_expect_not_convergent`): the market tracks a
  published number that never settles. **Grade: N+ for the statement as written** — this is the
  witness on which `hL` is load-bearing, since a table with a rational limit needs no `hL`
  (`readability_ofTendsto`). N− relative to the intended application (the table is not a market's
  quotes, and a LIA table meeting `hL` is not exhibited — findings F2).
* **T3.1, the convergent witnesses `readability_harmonic`, `readability_twoPowInv` — regraded
  N− for `readability` (audit round 2, fidelity B1).** The harmonic table `1/(n+1)` and the table
  `(2^n)⁻¹` both converge to `0`, so their conclusions hold with no `hL` at all
  (`readability_harmonic_ofTendsto`, `readability_twoPowInv_ofTendsto` derive them from
  `readability_ofTendsto`): the package of hypotheses is inhabited over real objects, which is
  real, but `hL` is idle. They remain N+ for `readability_ofTendsto` (day-varying tables, real
  reader, genuine full-limit conclusion), and `readability_twoPowInv` keeps its separate point:
  its `hL` holds through no value-bounded route (FAF's `pGenerableRat_two_pow_inv`).
* **T2.1's package with two distinct markets, `X` outside the ledger family
  (`cleanMirrorPair`, primary)**: `H := liaHistory (paperDP 𝗜𝚺₁)` with the `MarketComputation`
  its inductor certificate supplies, `X := LUV.indicatorOf (witnessQuoted 0 n)` (indicator LUVs
  of the tag-`0` base atoms, e.c. by FAF's `indicatorOf_machineThresholdCodeSeq`),
  `f := succDeferral`, payout `σ n := n + 2 > f n`; `A`'s process is the mirror ledger over
  `paperDP 𝗜𝚺₁`, every stage satisfiable, `A := liaHistory` over it an inductor. `X n` is a
  sentence no ledger literal mentions. Grade: N+ for `CrossQuotePackage` (T2.1) and for
  `crossQuotePackage_mirror` (T2.4), on a declaration rather than in prose.
* **The same instance with `X := ledgerLuv 7` (`paperMirrorPair`, kept)**, with the disclosure
  the round-2 adversarial audit asked for: since `realizedExpectation` ignores the item index and
  the ledger publishes every item, `A`'s process also decides the quoted family `ledgerLuv 7 n`
  itself at the same number — `X` is an alias of its own quote in `A`'s world, and a family of
  fresh atoms `H`'s process never pins as a quantity. Still two distinct markets, nothing circular
  (`H`'s process is `paperDP 𝗜𝚺₁` and never sees family 3); N+ stands, but `cleanMirrorPair` is
  the instance with content in `X`.

Scope: one-way throughout.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## T3.1 primary witness: the oscillating table `1/(unpair₂ n + 1)` -/

/-- The oscillating table, the same for every item: `a j n = 1/(unpair₂ n + 1)` — FAF's harmonic
weight reindexed by the second unpairing coordinate. It is `1` at every `n = ⟨m, 0⟩` and `1/2` at
every `n = ⟨m, 1⟩`, so it has no limit (`unpairTable_not_convergent`), and `readability`'s
conclusion at it is not available from any convergent-table argument (`readability_ofTendsto`
does not apply): this is the table on which `hL` does work.
Source: none: infrastructure (T3.1 witness; audit r2 adversarial non-blocking 1, probe `AdvR2ReadabilityOscillating.lean`, adopted)
Kind: D
Fidelity: n/a -/
def unpairTable (_j n : ℕ) : ℚ := 1 / (((Nat.unpair n).2 : ℚ) + 1)

/-- The oscillating table is computable in `(j, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unpairTable_computable : Computable fun p : ℕ × ℕ => unpairTable p.1 p.2 := by
  have h : Primrec fun p : ℕ × ℕ => (((Nat.unpair p.2).2 : ℚ) + 1)⁻¹ :=
    ratInv_prim.comp (ratAdd_prim.comp
      (ratNatCast_prim.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
      (Primrec.const 1))
  exact h.to_comp.of_eq fun p => by simp [unpairTable, one_div]

/-- The oscillating table is `[0,1]`-valued (FAF's `harmonicWeight_mem` at `unpair₂ n`).
Source: none: infrastructure (FAF `harmonicWeight_mem`)
Kind: L
Fidelity: n/a -/
lemma unpairTable_mem : ∀ j n, 0 ≤ unpairTable j n ∧ unpairTable j n ≤ 1 :=
  fun _ n => harmonicWeight_mem (Nat.unpair n).2

/-- Machine-metered rational codes for the oscillating table: the harmonic weight's codes
reindexed by FAF's ruler `UnaryRuler.unpairSnd` (`MachineRatCodes.comp`).
Source: none: infrastructure (FAF `harmonicWeight_polyRatCodes`, `MachineRatCodes.comp`, `UnaryRuler.unpairSnd`)
Kind: L
Fidelity: n/a -/
lemma unpairTable_machineRatCodes (j : ℕ) : MachineRatCodes (fun n => unpairTable j n) :=
  ((DigitRatCodes.ofPolyRatCodes harmonicWeight_polyRatCodes).toMachine.comp
    UnaryRuler.unpairSnd).of_eq fun _ => rfl

/-- The oscillating table is `P`-generable at every market — `readability`'s `hL`.
Source: none: infrastructure (FAF `PGenerableRat.ofMachineRatCodes`)
Kind: L
Fidelity: n/a -/
lemma unpairTable_pgenerable (P : History) (j : ℕ) :
    PGenerableRat P (fun n => unpairTable j n) :=
  PGenerableRat.ofMachineRatCodes (unpairTable_machineRatCodes j) P

/-- The table is `1` at every `⟨m, 0⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unpairTable_pair_zero (j m : ℕ) : unpairTable j (Nat.pair m 0) = 1 := by
  simp [unpairTable, Nat.unpair_pair]

/-- The table is `1/2` at every `⟨m, 1⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unpairTable_pair_one (j m : ℕ) : unpairTable j (Nat.pair m 1) = 1 / 2 := by
  norm_num [unpairTable, Nat.unpair_pair]

/-- **The oscillating table has no limit** (the N+ ground of `readability_unpair`): it is `1`
along `⟨m, 0⟩ → ∞` and `1/2` along `⟨m, 1⟩ → ∞`.
Source: none: infrastructure (T3.1 witness; audit r2 adversarial non-blocking 1)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem unpairTable_not_convergent (j : ℕ) :
    ¬ ∃ L : ℝ, Tendsto (fun n => (unpairTable j n : ℝ)) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h0 : Tendsto (fun m : ℕ => Nat.pair m 0) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.left_le_pair m 0) tendsto_id
  have h1 : Tendsto (fun m : ℕ => Nat.pair m 1) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.left_le_pair m 1) tendsto_id
  have e0 := hL.comp h0
  have e1 := hL.comp h1
  simp only [Function.comp_def, unpairTable_pair_zero, unpairTable_pair_one, Rat.cast_one,
    Rat.cast_div, Rat.cast_ofNat] at e0 e1
  have hL0 : L = 1 := tendsto_nhds_unique e0 tendsto_const_nhds
  have hL1 : L = 1 / 2 := tendsto_nhds_unique e1 tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

/-- The ledger process over `paperDP 𝗜𝚺₁` with the oscillating table, next-day publication.
Source: none: infrastructure (T3.1 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev unpairProcess : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) unpairTable (fun _ => PublicationSchedule.succ)

/-- FAF's LIA over the oscillating ledger process is an inductor over it (T1.4 + FAF's
`LIA_is_logical_inductor`).
Source: none: infrastructure (T3.1 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem unpair_inductor : IsLogicalInductor (liaHistory unpairProcess) unpairProcess :=
  LIA_is_logical_inductor _
    (ledgerProcess_computable (paperDP_computable 𝗜𝚺₁) unpairTable_computable
      succSchedule_computable)

/-- **T3.1's full hypothesis package inhabited at a non-convergent table (N+ for the statement as
written):** FAF's LIA over the oscillating ledger process prices every item's ledger LUV at
`1/(unpair₂ n + 1)` in the full per-day limit — a published number that never settles, which the
reader is forced to track (`unpair_expect_not_convergent`). This is the witness on which `hL`
does work: for a table with a rational limit the conclusion holds with no `hL`
(`readability_ofTendsto`), and this table has none (`unpairTable_not_convergent`). N− relative to
the intended LIA-table application, as the T3.1 row says (the table is not a market's quotes;
findings F2).
Source: mandate T3.1 (non-vacuity obligation); audit r2 fidelity B1 / adversarial non-blocking 1 (probe adopted)
Kind: N+
Fidelity: n/a
Hyps: (a) none (every hypothesis of `readability` discharged from FAF's facts) -/
theorem readability_unpair (j : ℕ) :
    (fun n => (ledgerLuv j n).expect (liaHistory unpairProcess) n) ≈ₙ
      (fun n => (unpairTable j n : ℝ)) :=
  haveI := unpair_inductor
  readability (liaHistory unpairProcess) (paperDP 𝗜𝚺₁) unpairTable
    (fun _ => PublicationSchedule.succ) (ledgerProcess_paperDP_hworld 𝗜𝚺₁ unpairTable _)
    unpairTable_mem j (unpairTable_pgenerable _ j)

/-- **The reader's expectation of the ledger LUV has no limit** at the oscillating table: it is
forced to oscillate with the published number. No convergent-table witness can say this.
Source: none: infrastructure (T3.1 witness; audit r2 adversarial non-blocking 1)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem unpair_expect_not_convergent (j : ℕ) :
    ¬ ∃ L : ℝ, Tendsto (fun n => (ledgerLuv j n).expect (liaHistory unpairProcess) n) atTop
      (𝓝 L) := by
  rintro ⟨L, hL⟩
  apply unpairTable_not_convergent j
  refine ⟨L, ?_⟩
  have h := readability_unpair j
  unfold AsympEq at h
  have := hL.sub h
  simpa using this

/-! ## T3.1 convergent witness 1: the harmonic table (N− for `readability`, `hL` idle) -/

/-- The harmonic table, the same for every item: `a j n = 1/(n+1)`.
Source: none: infrastructure (T3.1 witness; FAF `harmonicWeight_polyRatCodes`)
Kind: D
Fidelity: n/a -/
def harmonicTable (_j n : ℕ) : ℚ := 1 / ((n : ℚ) + 1)

/-- The harmonic table is computable in `(j, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma harmonicTable_computable : Computable fun p : ℕ × ℕ => harmonicTable p.1 p.2 := by
  have h : Primrec fun p : ℕ × ℕ => ((p.2 : ℚ) + 1)⁻¹ :=
    ratInv_prim.comp (ratAdd_prim.comp (ratNatCast_prim.comp Primrec.snd) (Primrec.const 1))
  exact h.to_comp.of_eq fun p => by simp [harmonicTable, one_div]

/-- The harmonic table is `[0,1]`-valued.
Source: none: infrastructure (FAF `harmonicWeight_mem`)
Kind: L
Fidelity: n/a -/
lemma harmonicTable_mem : ∀ j n, 0 ≤ harmonicTable j n ∧ harmonicTable j n ≤ 1 :=
  fun _ n => harmonicWeight_mem n

/-- The harmonic table is `P`-generable at every market (FAF's `PGenerableRat.ofPolyRatCodes`
on FAF's own witness) — `readability`'s `hL`.
Source: none: infrastructure (FAF `harmonicWeight_polyRatCodes`)
Kind: L
Fidelity: n/a -/
lemma harmonicTable_pgenerable (P : History) (j : ℕ) :
    PGenerableRat P (fun n => harmonicTable j n) :=
  PGenerableRat.ofPolyRatCodes harmonicWeight_polyRatCodes P

/-- The harmonic table is not constant (the day-varying ground; it does converge, to `0`).
Source: none: infrastructure (FAF `harmonicWeight_not_constant`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma harmonicTable_not_constant (j : ℕ) : ¬ ∀ m n, harmonicTable j m = harmonicTable j n :=
  harmonicWeight_not_constant

/-- The harmonic table tends to `0`.
Source: none: infrastructure (audit r2 fidelity B1)
Kind: L
Fidelity: n/a -/
lemma harmonicTable_tendsto_zero (j : ℕ) :
    Tendsto (fun n => (harmonicTable j n : ℝ)) atTop (𝓝 ((0 : ℚ) : ℝ)) := by
  rw [Rat.cast_zero]
  refine (tendsto_one_div_add_atTop_nhds_zero_nat).congr fun n => ?_
  simp [harmonicTable]

/-- The ledger process over `paperDP 𝗜𝚺₁` with the harmonic table, next-day publication.
Source: none: infrastructure (T3.1 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev harmonicProcess : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) harmonicTable (fun _ => PublicationSchedule.succ)

/-- T1.4 at the harmonic instance.
Source: none: infrastructure (T3.1 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem harmonicProcess_computable : ComputableDeductiveProcess harmonicProcess :=
  ledgerProcess_computable (paperDP_computable 𝗜𝚺₁) harmonicTable_computable
    succSchedule_computable

/-- FAF's LIA over the harmonic ledger process is an inductor over it.
Source: none: infrastructure (T3.1 witness; FAF `LIA_is_logical_inductor`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem harmonic_inductor : IsLogicalInductor (liaHistory harmonicProcess) harmonicProcess :=
  LIA_is_logical_inductor _ harmonicProcess_computable

/-- T1.5 at the harmonic instance: every stage of the process is satisfiable.
Source: none: infrastructure (T3.1 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem harmonic_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (harmonicProcess.D n) :=
  ledgerProcess_paperDP_hworld 𝗜𝚺₁ harmonicTable _

/-- The world quantifier of T1.2 is non-empty at the harmonic instance (compactness).
Source: none: infrastructure (T3.1 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem harmonic_theoryWorld : ∃ v : PCWorld, v.ConsistentWithTheory harmonicProcess :=
  DeductiveProcess.exists_consistentWithTheory _ harmonic_hworld

/-- **T3.1's full hypothesis package, inhabited at the harmonic table (N− for `readability`:
`hL` idle; N+ for `readability_ofTendsto`):** FAF's LIA over the harmonic ledger process prices
every item's ledger LUV at `1/(n+1)` in the full per-day limit. Regraded in audit round 2
(fidelity B1): the table converges to `0`, so this conclusion holds with no `hL` at all
(`readability_harmonic_ofTendsto` below derives it from `readability_ofTendsto`); the package of
hypotheses is inhabited over real objects, but the hypothesis `readability` adds is not
exercised. The witness on which `hL` does work is `readability_unpair`. N− relative to the
intended LIA-table application as well (findings F2).
Source: mandate T3.1 (non-vacuity obligation); audit r1 adversarial B2 / fidelity N2; regraded audit r2 fidelity B1
Kind: N−
Fidelity: n/a
Hyps: (a) none (every hypothesis of `readability` discharged from FAF's facts) -/
theorem readability_harmonic (j : ℕ) :
    (fun n => (ledgerLuv j n).expect (liaHistory harmonicProcess) n) ≈ₙ
      (fun n => (harmonicTable j n : ℝ)) :=
  haveI := harmonic_inductor
  readability (liaHistory harmonicProcess) (paperDP 𝗜𝚺₁) harmonicTable
    (fun _ => PublicationSchedule.succ) harmonic_hworld harmonicTable_mem j
    (harmonicTable_pgenerable _ j)

/-- `readability_harmonic`'s conclusion with no `hL`: the harmonic table tends to `0`, so
`readability_ofTendsto` applies. This is the in-library form of the round-2 regrade.
Source: audit r2 fidelity B1 (probe `FidelityConvergentTable.lean`, adopted)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem readability_harmonic_ofTendsto (j : ℕ) :
    (fun n => (ledgerLuv j n).expect (liaHistory harmonicProcess) n) ≈ₙ
      (fun n => (harmonicTable j n : ℝ)) :=
  haveI := harmonic_inductor
  readability_ofTendsto (liaHistory harmonicProcess) (paperDP 𝗜𝚺₁) harmonicTable
    (fun _ => PublicationSchedule.succ) harmonic_hworld harmonicTable_mem j 0
    (harmonicTable_tendsto_zero j)

/-! ## T3.1 convergent witness 2: the table `(2^n)⁻¹` (generable, not value-bounded) -/

/-- The table `a j n := (2^n)⁻¹`, the same for every item — FAF's own witness that `def:ece`
admits sequences with no poly-size rational codes (`pGenerableRat_two_pow_inv`).
Source: none: infrastructure (T3.1 witness; FAF `pGenerableRat_two_pow_inv`)
Kind: D
Fidelity: n/a -/
noncomputable def twoPowInvTable (_j n : ℕ) : ℚ := (((2 ^ n : ℕ) : ℚ))⁻¹

/-- The table is computable in `(j, n)` (FAF's `ratPow_prim`, `ratInv_prim`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoPowInvTable_computable : Computable fun p : ℕ × ℕ => twoPowInvTable p.1 p.2 := by
  have h : Primrec fun p : ℕ × ℕ => ((2 ^ p.2 : ℕ) : ℚ) :=
    (ratPow_prim.comp (Primrec.const (2 : ℚ)) Primrec.snd).of_eq (fun p => by
      simp [Nat.cast_pow])
  exact (ratInv_prim.comp h).to_comp

/-- The table is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoPowInvTable_mem : ∀ j n, 0 ≤ twoPowInvTable j n ∧ twoPowInvTable j n ≤ 1 := by
  intro j n
  unfold twoPowInvTable
  constructor
  · positivity
  · have h1 : (1 : ℚ) ≤ ((2 ^ n : ℕ) : ℚ) := by exact_mod_cast Nat.one_le_two_pow
    exact inv_le_one_of_one_le₀ h1

/-- The table is not constant: day `0` publishes `1`, day `1` publishes `1/2` (it does converge,
to `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma twoPowInvTable_varies : twoPowInvTable 0 0 ≠ twoPowInvTable 0 1 := by
  norm_num [twoPowInvTable]

/-- The table `(2^n)⁻¹` tends to `0`.
Source: none: infrastructure (audit r2 fidelity B1)
Kind: L
Fidelity: n/a -/
lemma twoPowInvTable_tendsto_zero (j : ℕ) :
    Tendsto (fun n => (twoPowInvTable j n : ℝ)) atTop (𝓝 ((0 : ℚ) : ℝ)) := by
  rw [Rat.cast_zero]
  have h : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine h.congr fun n => ?_
  simp [twoPowInvTable, one_div, inv_pow]

/-- The ledger process over `paperDP 𝗜𝚺₁` with the `(2^n)⁻¹` table, next-day publication.
Source: none: infrastructure (T3.1 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev twoPowInvProcess : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) twoPowInvTable (fun _ => PublicationSchedule.succ)

/-- FAF's LIA over the `(2^n)⁻¹` ledger process is an inductor over it (T1.4 + FAF's
`LIA_is_logical_inductor`).
Source: none: infrastructure (T3.1 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem twoPowInv_inductor : IsLogicalInductor (liaHistory twoPowInvProcess) twoPowInvProcess :=
  LIA_is_logical_inductor _
    (ledgerProcess_computable (paperDP_computable 𝗜𝚺₁) twoPowInvTable_computable
      succSchedule_computable)

/-- **T3.1's full hypothesis package, inhabited at the table `(2^n)⁻¹` (N− for `readability`:
`hL` idle; N+ for `readability_ofTendsto`):** FAF's LIA over the `(2^n)⁻¹` ledger process prices
item `0`'s ledger LUV at `(2^n)⁻¹` in the full per-day limit. Here `hL` holds through
`PGenerableRat.ofMachineRatCodes` and through no value-bounded route (FAF's docstring on
`pGenerableRat_two_pow_inv`), so this witness inhabits `hL` strictly beyond the "e.c. rational
sequence" reading of (L) — but, regraded in audit round 2 (fidelity B1), the table converges to
`0`, so the conclusion holds with no `hL` at all (`readability_twoPowInv_ofTendsto`); the
hypothesis side is exercised, the conclusion side is not. The witness on which `hL` does work is
`readability_unpair`.
Source: mandate T3.1 (non-vacuity obligation); audit r1 fidelity N2; regraded audit r2 fidelity B1
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem readability_twoPowInv :
    (fun n => (ledgerLuv 0 n).expect (liaHistory twoPowInvProcess) n) ≈ₙ
      (fun n => (twoPowInvTable 0 n : ℝ)) :=
  haveI := twoPowInv_inductor
  readability (liaHistory twoPowInvProcess) (paperDP 𝗜𝚺₁) twoPowInvTable
    (fun _ => PublicationSchedule.succ)
    (ledgerProcess_paperDP_hworld 𝗜𝚺₁ twoPowInvTable _) twoPowInvTable_mem 0
    (pGenerableRat_two_pow_inv (liaHistory twoPowInvProcess)).1

/-- `readability_twoPowInv`'s conclusion with no `hL`: the table tends to `0`, so
`readability_ofTendsto` applies. The in-library form of the round-2 regrade.
Source: audit r2 fidelity B1 (probe `FidelityConvergentTable.lean`, adopted)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem readability_twoPowInv_ofTendsto :
    (fun n => (ledgerLuv 0 n).expect (liaHistory twoPowInvProcess) n) ≈ₙ
      (fun n => (twoPowInvTable 0 n : ℝ)) :=
  haveI := twoPowInv_inductor
  readability_ofTendsto (liaHistory twoPowInvProcess) (paperDP 𝗜𝚺₁) twoPowInvTable
    (fun _ => PublicationSchedule.succ)
    (ledgerProcess_paperDP_hworld 𝗜𝚺₁ twoPowInvTable _) twoPowInvTable_mem 0 0
    (twoPowInvTable_tendsto_zero 0)

/-! ## T2.1 / T2.4 witnesses: the mirror pair over `paperDP 𝗜𝚺₁`, two distinct markets -/

/-- `H`'s exact market program, read off `LIA_is_logical_inductor`'s certificate for
`liaHistory (paperDP 𝗜𝚺₁)`.
Source: none: infrastructure (T2.4 witness)
Kind: D
Fidelity: n/a -/
noncomputable def paperM : MarketComputation (liaHistory (paperDP 𝗜𝚺₁)) :=
  (LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁)).marketComputable.nonemptyComputation.some

/-- Payout two days after the question: `σ n = n + 2` (root-deference-036's `σ`, strictly after
the deferral `f n = n + 1`).
Source: none: infrastructure (T2.4 witness)
Kind: D
Fidelity: n/a -/
def payoutSchedule : PublicationSchedule := ⟨fun n => n + 2, fun n => by omega⟩

/-- Payout is strictly after the deferral: `succDeferral n = n + 1 < n + 2 = payoutSchedule n`.
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: n/a -/
lemma payout_after_deferral (n : ℕ) : succDeferral.f n < payoutSchedule.e n := by
  show n + 1 < n + 2
  omega

/-- The payout schedule is computable in `(j, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutSchedule_computable :
    Computable fun p : ℕ × ℕ => ((fun _ : ℕ => payoutSchedule) p.1).e p.2 :=
  (Primrec.succ.comp (Primrec.succ.comp Primrec.snd)).to_comp.of_eq fun _ => rfl

/-! ### The primary instance: `X` outside the ledger family -/

/-- One poly-fueled program emits `⌜witnessQuoted 0 n⌝` from `n` (the pair shell of T1.3's
certificate, `Codes.lean`, at the tag-`0` atoms).
Source: none: infrastructure (T2.4 witness; audit r2 adversarial non-blocking 2, probe `AdvR2MirrorCleanX.lean`, adopted)
Kind: L
Fidelity: n/a -/
lemma witnessQuoted_polySentenceCodes : PolySentenceCodes (fun n => witnessQuoted 0 n) :=
  ⟨_, (((PolyFueled.const 1).pair ((PolyFueled.const 0).pair
    ((PolyFueled.const 0).pair PolyFueled.id))).succ_comp).of_eq fun _ => rfl⟩

/-- The atoms `⟨0, ⟨0, n⟩⟩` are an e.c. sentence sequence (FAF's two bridges).
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: n/a -/
lemma witnessQuoted_machineSentenceCodes : MachineSentenceCodes (fun n => witnessQuoted 0 n) :=
  RpnSentenceCodes.toMachine
    (RpnSentenceCodes.ofPolySentenceCodes witnessQuoted_polySentenceCodes)

/-- The quoted family of the primary mirror witness: indicator LUVs of the tag-`0` base atoms
`witnessQuoted 0 n` (FAF's `LUV.indicatorOf`) — sentences of `H`'s language that no ledger
literal mentions.
Source: none: infrastructure (T2.4 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev cleanX : ℕ → LUV := fun n => LUV.indicatorOf (witnessQuoted 0 n)

/-- The family is e.c. (FAF's `indicatorOf_machineThresholdCodeSeq`).
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: n/a -/
lemma cleanX_codes : LUV.MachineThresholdCodeSeq cleanX :=
  LUV.indicatorOf_machineThresholdCodeSeq witnessQuoted_machineSentenceCodes

/-- `A`'s process in the primary mirror witness: `paperDP 𝗜𝚺₁` plus the ledger of `H`'s realized
day-`(n+1)` expectations of `cleanX n`, published at `n + 2`.
Source: none: infrastructure (T2.4 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev cleanMirrorProcess : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) (realizedExpectation paperM cleanX succDeferral)
    (fun _ => payoutSchedule)

/-- **T2.1's package inhabited with two distinct markets and a quoted family outside the ledger
(N+, primary):** `CrossQuotePackage` for `H = liaHistory (paperDP 𝗜𝚺₁)` and
`DPA = cleanMirrorProcess` (a different process, hence a different `liaHistory`), deferral
`succDeferral`, quoted family `cleanX` (indicators of tag-`0` base atoms), quote LUVs
`ledgerLuv 0`. `A`'s ledger names `H`'s expectation of `X n` under `ledgerLuv j n` only; `X n`
itself is a sentence no ledger literal mentions.
Source: mandate T2.1 / T2.4 (N+ obligation); audit r2 adversarial non-blocking 2 / fidelity non-blocking 4 (probe adopted)
Kind: N+
Fidelity: variant (as `crossQuotePackage_mirror`: ledger-recorded determinacy)
Hyps: (a) none -/
theorem cleanMirrorPair :
    CrossQuotePackage (liaHistory (paperDP 𝗜𝚺₁)) cleanMirrorProcess succDeferral cleanX
      (fun n => ledgerLuv 0 n) :=
  crossQuotePackage_mirror paperM cleanX succDeferral (paperDP 𝗜𝚺₁) (fun _ => payoutSchedule)

/-- `A := liaHistory cleanMirrorProcess` is an inductor over `A`'s process (T2.4's
`mirrorPair_inductor` at the primary witness).
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem cleanMirror_inductor :
    IsLogicalInductor (liaHistory cleanMirrorProcess) cleanMirrorProcess :=
  mirrorPair_inductor paperM cleanX cleanX_codes succDeferral (paperDP 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) (fun _ => payoutSchedule) payoutSchedule_computable

/-- T1.5 at the primary mirror witness: every stage of `A`'s process is satisfiable (the `hworld`
a headline over `CrossQuotePackage` must carry; `Defs.lean`).
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem cleanMirror_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (cleanMirrorProcess.D n) :=
  ledgerProcess_paperDP_hworld 𝗜𝚺₁ _ _

/-- The world quantifier of `cleanMirrorPair.reflected` is non-empty (compactness).
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem cleanMirror_theoryWorld : ∃ v : PCWorld, v.ConsistentWithTheory cleanMirrorProcess :=
  DeductiveProcess.exists_consistentWithTheory _ cleanMirror_hworld

/-- The scope clause at the primary witness: at day `n`, no literal of the quote LUV
`ledgerLuv 0 n` is in `A`'s process's schedule yet (it enters at `n + 2`), so `A`'s day-`n`
price of it is a forecast. Stated on the schedule's `lits n`; the `D n` form (the base is
cleanroom-free, so the literal is in neither summand) is not proved here.
Source: none: infrastructure (T2.4 scope clause at the witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem cleanMirror_forecast (n : ℕ) (r : ℚ) (b : Bool) :
    (ledgerFamily, ledgerPayload 0 n (Encodable.encode r), b) ∉
      (ledgerSchedule (realizedExpectation paperM cleanX succDeferral)
        (fun _ => payoutSchedule)).lits n :=
  ledgerLuv_absent_before_payout _ _ 0 n r b (by show n < n + 2; omega)

/-! ### The instance with `X := ledgerLuv 7` (kept, with its alias disclosed) -/

/-- The quoted family of the first mirror witness: item `7`'s ledger LUVs, an e.c. `[0,1]`-LUV
family of `H`'s language (T1.3). **Disclosure (audit r2 adversarial non-blocking 2 / fidelity
non-blocking 4):** `realizedExpectation` ignores the item index and the ledger publishes every
item, so `A`'s process decides `ledgerLuv 7 n` — this family itself — at the same number as the
quote: in `A`'s world `X n` is an alias of its own quote, and it is a family of fresh atoms `H`'s
process (`paperDP 𝗜𝚺₁`, which never sees family 3) does not pin as a quantity. Nothing is
circular, but `X` carries no content; the instance with content in `X` is `cleanMirrorPair`.
Source: none: infrastructure (T2.4 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev mirrorX : ℕ → LUV := fun n => ledgerLuv 7 n

/-- `A`'s process in the first mirror witness: `paperDP 𝗜𝚺₁` plus the ledger of `H`'s realized
day-`(n+1)` expectations of `X n`, published at `n + 2`.
Source: none: infrastructure (T2.4 witness)
Kind: D
Fidelity: n/a -/
noncomputable abbrev mirrorProcess : DeductiveProcess :=
  ledgerProcess (paperDP 𝗜𝚺₁) (realizedExpectation paperM mirrorX succDeferral)
    (fun _ => payoutSchedule)

/-- **T2.1's package inhabited with two distinct markets (N+):** `CrossQuotePackage` for
`H = liaHistory (paperDP 𝗜𝚺₁)` and `DPA = mirrorProcess` (a different process, hence a different
`liaHistory`), deferral `succDeferral`, quoted family `ledgerLuv 7`, quote LUVs `ledgerLuv 0`.
See `mirrorX` for the alias disclosure; `cleanMirrorPair` is the primary instance.
Source: mandate T2.1 / T2.4 (N+ obligation); audit r1 adversarial 1
Kind: N+
Fidelity: variant (as `crossQuotePackage_mirror`: ledger-recorded determinacy)
Hyps: (a) none -/
theorem paperMirrorPair :
    CrossQuotePackage (liaHistory (paperDP 𝗜𝚺₁)) mirrorProcess succDeferral mirrorX
      (fun n => ledgerLuv 0 n) :=
  crossQuotePackage_mirror paperM mirrorX succDeferral (paperDP 𝗜𝚺₁) (fun _ => payoutSchedule)

/-- T1.5 at the mirror witness: every stage of `A`'s process is satisfiable.
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem paperMirror_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (mirrorProcess.D n) :=
  ledgerProcess_paperDP_hworld 𝗜𝚺₁ _ _

/-- The world quantifier of `paperMirrorPair.reflected` is non-empty (compactness).
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem paperMirror_theoryWorld : ∃ v : PCWorld, v.ConsistentWithTheory mirrorProcess :=
  DeductiveProcess.exists_consistentWithTheory _ paperMirror_hworld

/-- `A := liaHistory mirrorProcess` is an inductor over `A`'s process (T2.4's
`mirrorPair_inductor` at the witness).
Source: none: infrastructure (T2.4 witness)
Kind: L
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem paperMirror_inductor : IsLogicalInductor (liaHistory mirrorProcess) mirrorProcess :=
  mirrorPair_inductor paperM mirrorX (ledgerLuv_thresholdCodes 7) succDeferral (paperDP 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) (fun _ => payoutSchedule) payoutSchedule_computable

/-- The scope clause at the witness: at day `n`, no literal of the quote LUV `ledgerLuv 0 n` is
in `A`'s process's schedule yet (it enters at `n + 2`), so `A`'s day-`n` price of it is a
forecast. Stated on the schedule's `lits n` (see `cleanMirror_forecast`).
Source: none: infrastructure (T2.4 scope clause at the witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem paperMirror_forecast (n : ℕ) (r : ℚ) (b : Bool) :
    (ledgerFamily, ledgerPayload 0 n (Encodable.encode r), b) ∉
      (ledgerSchedule (realizedExpectation paperM mirrorX succDeferral)
        (fun _ => payoutSchedule)).lits n :=
  ledgerLuv_absent_before_payout _ _ 0 n r b (by show n < n + 2; omega)

end Cleanroom.Found.LiQuoteLane
