import Cleanroom.Deference.DefTrackingPin.Column
import Cleanroom.Found.LiQuoteLane.Witnesses
import Cleanroom.Found.LiQuoteLane.PaperWitness

/-!
# `def-tracking-pin` · Witnesses: the hypothesis packages inhabited over real objects

* **T1 at a target with no limit** (`pinning_unpair`): FAF's LIA over `li-quote-lane`'s oscillating
  ledger process (base `paperDP 𝗜𝚺₁`, table `1/(unpair₂ n + 1)`, which has no limit —
  `unpairTable_not_convergent`) tracks the table through the *general* pinning lemma at the ledger
  LUV family. N+ for `pinning_ofApprox` as written: on this target `hz` is load-bearing
  (`pinning_ofTendsto` does not apply), and the reader's expectation has no limit either
  (`unpair_expect_not_convergent`). The LUV-level generalization is what is new; the ledger
  statement is `readability_unpair`. N− relative to the intended LIA-table instance (the table is
  not a market's quotes).
* **T5/T6 at the paper process** (`paperDeferredProcess`, `paperDeferredReader`): `DPA = DPH =
  paperDP 𝗜𝚺₁`, lookahead `F n := n + 1`, item `j` the atom `witnessQuoted j 0` published at day
  `F n`. A real base, two distinct processes (the fixed market's `paperDP 𝗜𝚺₁`, the reader's
  `paperDP 𝗜𝚺₁ ⊕ ledger`), day-varying published numbers (the *values* `liaQuote (paperDP 𝗜𝚺₁)
  (n+1) φ_j` are not shown to vary — that would evaluate the LIA; both polarities occur,
  `paperDeferred_both_polarities`), and a target `limitingBelief (liaHistory (paperDP 𝗜𝚺₁))
  (φ j)` with no computable description handed in. N+ for T3/T6 by construction (real-limit clause).
* **T3 at a verified non-constant table** (`pinning_harmonic_tendsto`): the harmonic ledger
  (`harmonicTable_not_constant`, limit `0`), through `pinning_tendsto` — the non-constancy clause of
  the mandate's T3 trap, which the paper witness does not verify (audit r1 fidelity N1).
* **T4's (a) instance** (`atom_learned_harmonic`): the harmonic table (limit `0`) at the threshold
  `1/2`: the reader's price of `⌜α_{j,n} > 1/2⌝` tends to `0`, no pattern hypothesis.
* **T4's `hpat` package at a live pattern** (`atom_learned_unpair_live`, **N+**; after audit r2
  adversarial N2's probe): on the oscillating table at `q = 3/4` the atom `⌜α_{j,n} > 3/4⌝` is
  affirmed exactly on the days `⟨m, 0⟩` and refuted on every other day — a pattern with no limit
  (`unpair_pattern_not_convergent`), so `ledger_atom_learned_ofTendsto` cannot apply and `hpat`
  is load-bearing; both if-split certificates come from FAF's `MachineSentenceCodes.ifZero` on
  the ruler `n ↦ unpair₂ n` (`unpair_hpat₁`, `unpair_hpat₂`), and the reader's price has no limit
  either (`unpair_live_price_not_convergent`). The constant-pattern N− `atom_learned_harmonic_const`
  is kept as the degenerate example.
* **T2 at the paper pair** (`paperDeferred_snapshot`): the snapshot identity, exact.
* **`deferred_tracking`'s full package at a constant lookahead** (`deferred_tracking_constLookahead`,
  **N−**; after audit r2 adversarial N1's probe): `deferred_tracking` asks only `Computable F`, so
  `F ≡ c` with a day-constant quoted sentence makes the deferred table the constant
  `liaQuote (paperDP 𝗜𝚺₁) c ψ`, and `MachineRatCodes.const` discharges `hz`. N− because the
  target is constant and `hz` is idle (`_hzFree`: the same conclusion through T3). `hz` at a
  *genuine* lookahead (`n ≤ F n`, day-varying table) — the intended instance — stays unexhibited.

Scope: one-way throughout.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## T1: the oscillating table -/

/-- **T1's full package inhabited at a target with no limit (N+ for `pinning_ofApprox` as
written):** FAF's LIA over the oscillating ledger process prices every item's ledger LUV at
`1/(unpair₂ n + 1)` in the full per-day limit, through the general pinning lemma at the family
`X_n := α_{j,n}`, `v_n := unpairTable j n`, `hz := unpairTable_pgenerable`. The target has no limit
(`unpairTable_not_convergent`), so `pinning_ofTendsto` does not apply and `hz` does work; the
reader's expectation has no limit either (`unpair_expect_not_convergent`). N− relative to the
intended LIA-table instance (findings F-A).
Source: mandate T1 (non-vacuity obligation; fake-success trap (i)); `li-quote-lane` `readability_unpair`
Kind: N+
Fidelity: n/a
Hyps: (a) none (every hypothesis of `pinning_ofApprox` discharged from FAF's facts) -/
theorem pinning_unpair (j : ℕ) :
    (fun n => (ledgerLuv j n).expect (liaHistory unpairProcess) n) ≈ₙ
      (fun n => (unpairTable j n : ℝ)) :=
  haveI := unpair_inductor
  pinning_exact (ledgerLuv_thresholdCodes j)
    (ledgerProcess_paperDP_hworld 𝗜𝚺₁ unpairTable (fun _ => PublicationSchedule.succ))
    (fun n => unpairTable j n)
    (fun n => ledgerLuv_determinedVia (paperDP 𝗜𝚺₁) unpairTable
      (fun _ => PublicationSchedule.succ) unpairTable_mem j n)
    (unpairTable_pgenerable _ j)

/-! ## T5/T6: the deferred pair over `paperDP 𝗜𝚺₁` -/

/-- The witness lookahead `F n := n + 1`.
Source: mandate T6 ("say which `F`")
Kind: D
Fidelity: n/a -/
def witnessLookahead (n : ℕ) : ℕ := n + 1

/-- `n ≤ F n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessLookahead_le (n : ℕ) : n ≤ witnessLookahead n := Nat.le_succ n

/-- `F` is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessLookahead_computable : Computable witnessLookahead := Computable.succ

/-- The quoted sentence of item `j`: the tag-`0` atom `⟨0, ⟨j, 0⟩⟩` (`li-quote-lane`'s
`witnessQuoted j 0`), published every day.
Source: mandate T6 (`quoted j n := φ j`)
Kind: D
Fidelity: n/a -/
def witnessSentence (j : ℕ) : Sentence := witnessQuoted j 0

/-- The quoted family is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessSentence_computable : Computable witnessSentence :=
  (witnessQuoted_computable.comp (Computable.id.pair (Computable.const 0))).of_eq fun _ => rfl

/-- The witness schedule: every item published at day `F n = n + 1`.
Source: mandate T5 (`F n ≤ (e j).e n`)
Kind: D
Fidelity: n/a -/
def witnessSchedule : ℕ → PublicationSchedule :=
  fun _ => deferredSchedule witnessLookahead witnessLookahead_le

/-- The witness schedule is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessSchedule_computable :
    Computable fun p : ℕ × ℕ => (witnessSchedule p.1).e p.2 :=
  (Primrec.succ.comp Primrec.snd).to_comp

/-- **The deferred ledger process over `paperDP 𝗜𝚺₁`** with `F n := n + 1`.
Source: mandate T5 (N+ obligation)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperDeferredProcess : DeductiveProcess :=
  deferredProcess (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) witnessLookahead (fun j _ => witnessSentence j)
    witnessSchedule

/-- **The reader of the paper deferred pair**: FAF's LIA over `paperDeferredProcess`.
Source: mandate T5 (N+ obligation)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperDeferredReader : History :=
  deferredReader (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) witnessLookahead (fun j _ => witnessSentence j)
    witnessSchedule

/-- The base is free of the ledger family (every FAF-built process is).
Source: none: infrastructure (`bli-found` `paperDP_cleanroomFree`)
Kind: L
Fidelity: n/a -/
theorem paperDeferred_free :
    ProcessFreeOf (ledgerSchedule (deferredTable (paperDP 𝗜𝚺₁) witnessLookahead
      (fun j _ => witnessSentence j)) witnessSchedule) (paperDP 𝗜𝚺₁) :=
  processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁)

/-- **T5 (N+): the paper deferred pair exists** — the reader is a logical inductor over the
deferred ledger process, every field from FAF's own facts (`paperDP_computable`,
`LIA_is_logical_inductor`).
Source: mandate T5 (N+ obligation); anson-2-022 Theorem 1
Kind: N+
Fidelity: variant: plain trader class; autonomous target
Hyps: (a) none -/
theorem paperDeferred_inductor : IsLogicalInductor paperDeferredReader paperDeferredProcess :=
  deferred_inductor _ _ (paperDP_computable 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) _
    witnessLookahead_computable _ (witnessSentence_computable.comp Computable.fst) _
    witnessSchedule_computable

/-- Every stage of the paper deferred process is satisfiable.
Source: none: infrastructure (`li-quote-lane` T1.5 at `paperDP`)
Kind: L
Fidelity: n/a -/
theorem paperDeferred_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (paperDeferredProcess.D n) :=
  deferredProcess_hworld paperDeferred_free (paperDP_hworld 𝗜𝚺₁)

/-- **Both ledger polarities occur** in the paper deferred pair, for every item and day — trivially:
`r = -1` is affirmed and `r = 2` denied by *every* `[0,1]`-valued table, so this adds nothing beyond
`deferredTable_mem` and is not evidence that the quotes vary (audit r2 fidelity N4, adversarial N5).
The N+ grounds for T5 are the construction's objects: a real base, two distinct processes,
day-varying published atoms, and the real-limit target of `paperDeferred_column_tendsto`.
Source: mandate T5 (the ledger's polarity structure, for the record)
Kind: L (one application of `ledgerSchedule_both_polarities`)
Fidelity: n/a
Hyps: (a) none -/
theorem paperDeferred_both_polarities (j n : ℕ) :
    (∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule (deferredTable (paperDP 𝗜𝚺₁) witnessLookahead
          (fun j _ => witnessSentence j)) witnessSchedule).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule (deferredTable (paperDP 𝗜𝚺₁) witnessLookahead
          (fun j _ => witnessSentence j)) witnessSchedule).lits s :=
  ledgerSchedule_both_polarities
    (deferredTable (paperDP 𝗜𝚺₁) witnessLookahead (fun j _ => witnessSentence j)) witnessSchedule
    (fun j n => deferredTable_mem (paperDP 𝗜𝚺₁) witnessLookahead (fun j _ => witnessSentence j) j n)
    j n

/-- **T6 (N+): the paper deferred pair reaches `H_∞` column-wise** — for every item `j`, the
reader's day-`n` expectation of `α_{j,n}` tends to `limitingBelief (liaHistory (paperDP 𝗜𝚺₁))
(witnessQuoted j 0)`, a real limit with no computable description handed in; `hz`-free.
Source: mandate T6 (N+ obligation); anson-043 corollary
Kind: N+
Fidelity: variant: item-indexed columns; autonomous target
Hyps: (a) none -/
theorem paperDeferred_column_tendsto (j : ℕ) :
    Tendsto (fun n => (ledgerLuv j n).expect paperDeferredReader n) atTop
      (𝓝 (limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (witnessSentence j))) :=
  deferred_column_tendsto_lia _ _ (paperDP_computable 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    witnessLookahead witnessLookahead_le witnessLookahead_computable witnessSentence
    witnessSentence_computable witnessSchedule witnessSchedule_computable paperDeferred_free
    (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) j

/-! ## T3's content at a verified non-constant table: the harmonic ledger -/

/-- **T3's full package inhabited at a table verified to vary (N+ for `pinning_tendsto`'s
content):** over the harmonic ledger process (base `paperDP 𝗜𝚺₁`, table `1/(n+1)`, which is **not
constant** — `harmonicTable_not_constant` — and tends to `0`), FAF's LIA's day-`n` expectation of
`α_{j,n}` tends to `0`, through `pinning_tendsto` with no generability. Complements
`paperDeferred_column_tendsto`, whose limit is a real with no computable description but whose
table values are not shown to vary (audit r1 fidelity N1): between them, the real-limit clause and
the non-constancy clause of the mandate's T3 trap are each verified, on different witnesses. The
limit here is rational, so this witness alone does not meet the "not handed in as a rational"
clause.
Source: mandate T3 (non-vacuity obligation); `li-quote-lane` `harmonicProcess`
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem pinning_harmonic_tendsto (j : ℕ) :
    Tendsto (fun n => (ledgerLuv j n).expect (liaHistory harmonicProcess) n) atTop (𝓝 0) := by
  haveI := harmonic_inductor
  have hconv : Tendsto (fun n => (harmonicTable j n : ℝ)) atTop (𝓝 0) := by
    have := harmonicTable_tendsto_zero j
    rwa [Rat.cast_zero] at this
  exact pinning_tendsto (P := liaHistory harmonicProcess) (ledgerLuv_thresholdCodes j)
    harmonic_hworld
    (fun n => ledgerLuv_determinedVia (paperDP 𝗜𝚺₁) harmonicTable
      (fun _ => PublicationSchedule.succ) harmonicTable_mem j n) hconv

/-- **T2 (N+): the snapshot identity at the paper deferred pair** — the reader's limiting
expectation of the day-`n` ledger LUV is the fixed market's day-`(n+1)` price of `φ_j`, exactly.
Source: mandate T2 (snapshot identity, N+ obligation); anson-043
Kind: N+
Fidelity: stronger: exact, no rounding
Hyps: (a) none -/
theorem paperDeferred_snapshot (j n : ℕ) :
    Tendsto (fun m => (ledgerLuv j n).expect paperDeferredReader m) atTop
      (𝓝 (liaHistory (paperDP 𝗜𝚺₁) (n + 1) (witnessSentence j))) :=
  deferred_snapshot _ _ (paperDP_computable 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) witnessLookahead
    witnessLookahead_computable _ (witnessSentence_computable.comp Computable.fst) _
    witnessSchedule_computable paperDeferred_free (paperDP_hworld 𝗜𝚺₁) j n

/-! ## T4's (a) instance: the harmonic table at threshold `1/2` -/

/-- **T4's (a) instance inhabited (N+ for `ledger_atom_learned_ofTendsto`):** over the harmonic
ledger process (base `paperDP 𝗜𝚺₁`, table `1/(n+1) → 0`), FAF's LIA prices the atom
`⌜α_{j,n} > 1/2⌝` at `→ 0` — no pattern hypothesis. (The pattern is eventually constant: the
atom is refuted for `n ≥ 1`.)
Source: mandate T4 ((a) instance); `li-quote-lane` `harmonicProcess`
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem atom_learned_harmonic (j : ℕ) :
    (fun n => liaHistory harmonicProcess n ((ledgerLuv j n).gt (1 / 2))) ≈ₙ fun _ => 0 := by
  haveI := harmonic_inductor
  have hconv : Tendsto (fun n => (harmonicTable j n : ℝ)) atTop (𝓝 0) := by
    have := harmonicTable_tendsto_zero j
    rwa [Rat.cast_zero] at this
  have h := ledger_atom_learned_ofTendsto (liaHistory harmonicProcess) (paperDP 𝗜𝚺₁)
    harmonicTable (fun _ => PublicationSchedule.succ) harmonic_hworld j (1 / 2) hconv
    (by norm_num)
  rw [if_neg (by norm_num)] at h
  exact h

/-- **T4's `hpat` package inhabited at a constant pattern (N−):** at the threshold `q = -1`, every
`[0,1]`-table has the constant polarity `q < a_{j,n}`, so the two subfamilies of
`ledger_atom_learned` are the e.c. family `n ↦ ⌜α_{j,n} > −1⌝` (`ledgerLuv_gt_sentenceCodes`) and
the constant `∼⊤` (`MachineSentenceCodes.const`), and the reader's price of the atom tends to `1`.
N−: the pattern is constant, so `ledger_atom_learned_ofTendsto` would also apply (the hypothesis
`hpat` is inhabited but not exercised); it shows the package is not empty. The witness on which
`hpat` is load-bearing is `atom_learned_unpair_live` below (N+).
Source: mandate T4 (non-vacuity obligation)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem atom_learned_harmonic_const (j : ℕ) :
    (fun n => liaHistory harmonicProcess n ((ledgerLuv j n).gt (-1))) ≈ₙ fun _ => 1 := by
  haveI := harmonic_inductor
  have hlt : ∀ n, (-1 : ℚ) < harmonicTable j n := fun n => by
    linarith [(harmonicTable_mem j n).1]
  have h := ledger_atom_learned (liaHistory harmonicProcess) (paperDP 𝗜𝚺₁) harmonicTable
    (fun _ => PublicationSchedule.succ) harmonic_hworld j (-1)
    ((ledgerLuv_gt_sentenceCodes j (-1)).of_eq fun n => by rw [if_pos (hlt n)])
    ((MachineSentenceCodes.const (∼(⊤ : Sentence))).of_eq fun n => by rw [if_pos (hlt n)])
  have hconst : (fun n => if (-1 : ℚ) < harmonicTable j n then (1 : ℝ) else 0) = fun _ => 1 :=
    funext fun n => if_pos (hlt n)
  rw [hconst] at h
  exact h

/-! ## T4's `hpat` package at a live pattern: the oscillating table at `3/4` (N+) -/

/-- The cut of `1/(k+1)` at `3/4`: `3/4 < 1/(k+1)` iff `k = 0`.
Source: none: infrastructure (audit r2 adversarial probe `AdvT4LivePattern.lean`, lifted)
Kind: L
Fidelity: n/a -/
lemma unpair_cut (k : ℕ) : ((3 : ℚ) / 4 < 1 / ((k : ℚ) + 1)) ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have h2 : (1 : ℚ) / ((k : ℚ) + 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · rintro rfl
    norm_num

/-- The oscillating table's polarity at `3/4` is the test `unpair₂ n = 0`: the atom
`⌜α_{j,n} > 3/4⌝` is affirmed on the days `⟨m, 0⟩` and refuted on every other day.
Source: none: infrastructure (`li-quote-lane` `unpairTable`)
Kind: L
Fidelity: n/a -/
lemma unpair_pattern (j n : ℕ) : ((3 : ℚ) / 4 < unpairTable j n) ↔ n.unpair.2 = 0 := by
  unfold unpairTable
  exact unpair_cut _

/-- `hpat₁` at the live pattern: the affirmed subfamily, padded with `⊤`, is e.c. — FAF's
`MachineSentenceCodes.ifZero` on the ruler `n ↦ unpair₂ n` (`UnaryRuler.unpairSnd`).
Source: none: infrastructure (T4's `hpat₁` discharged)
Kind: L
Fidelity: n/a -/
theorem unpair_hpat₁ (j : ℕ) :
    MachineSentenceCodes
      (fun n => if (3 : ℚ) / 4 < unpairTable j n then (ledgerLuv j n).gt (3 / 4) else ⊤) :=
  (MachineSentenceCodes.ifZero (ledgerLuv_gt_sentenceCodes j (3 / 4))
    (MachineSentenceCodes.const ⊤) UnaryRuler.unpairSnd).of_eq fun n => by
    by_cases h : n.unpair.2 = 0 <;> simp [h, unpair_pattern]

/-- `hpat₂` at the live pattern: the refuted subfamily, padded with `∼⊤`, is e.c.
Source: none: infrastructure (T4's `hpat₂` discharged)
Kind: L
Fidelity: n/a -/
theorem unpair_hpat₂ (j : ℕ) :
    MachineSentenceCodes
      (fun n => if (3 : ℚ) / 4 < unpairTable j n then ∼(⊤ : Sentence)
        else (ledgerLuv j n).gt (3 / 4)) :=
  (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (∼(⊤ : Sentence)))
    (ledgerLuv_gt_sentenceCodes j (3 / 4)) UnaryRuler.unpairSnd).of_eq fun n => by
    by_cases h : n.unpair.2 = 0 <;> simp [h, unpair_pattern]

/-- **T4's full package inhabited at a live pattern (N+ for `ledger_atom_learned` as written):**
FAF's LIA over the oscillating ledger process (base `paperDP 𝗜𝚺₁`, table `1/(unpair₂ n + 1)`)
prices `⌜α_{j,n} > 3/4⌝` at `≈ₙ 𝟙[unpair₂ n = 0]`, through `ledger_atom_learned` with both `hpat`
certificates discharged (`unpair_hpat₁`, `unpair_hpat₂`). The pattern has no limit
(`unpair_pattern_not_convergent`), so the (a) instance `ledger_atom_learned_ofTendsto` cannot apply
and `hpat` is load-bearing; the reader's price has no limit either
(`unpair_live_price_not_convergent`). Lifted from audit r2 adversarial N2's probe.
Source: mandate T4 (non-vacuity obligation; the live-pattern witness the round-1 package lacked)
Kind: N+
Fidelity: n/a
Hyps: (a) none (every hypothesis of `ledger_atom_learned` discharged from FAF's facts) -/
theorem atom_learned_unpair_live (j : ℕ) :
    (fun n => liaHistory unpairProcess n ((ledgerLuv j n).gt (3 / 4))) ≈ₙ
      (fun n => if (3 : ℚ) / 4 < unpairTable j n then (1 : ℝ) else 0) :=
  haveI := unpair_inductor
  ledger_atom_learned (liaHistory unpairProcess) (paperDP 𝗜𝚺₁) unpairTable
    (fun _ => PublicationSchedule.succ)
    (ledgerProcess_paperDP_hworld 𝗜𝚺₁ unpairTable (fun _ => PublicationSchedule.succ))
    j (3 / 4) (unpair_hpat₁ j) (unpair_hpat₂ j)

/-- The target pattern has no limit (`1` on `⟨m,0⟩`, `0` on `⟨m,1⟩`): `hpat` is load-bearing in
`atom_learned_unpair_live`, since `ledger_atom_learned_ofTendsto` needs a convergent table.
Source: none: infrastructure (non-degeneracy of `atom_learned_unpair_live`)
Kind: L
Fidelity: n/a -/
theorem unpair_pattern_not_convergent (j : ℕ) :
    ¬ ∃ L : ℝ, Tendsto (fun n => if (3 : ℚ) / 4 < unpairTable j n then (1 : ℝ) else 0) atTop
      (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h0 : Tendsto (fun m : ℕ => Nat.pair m 0) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.left_le_pair m 0) tendsto_id
  have h1 : Tendsto (fun m : ℕ => Nat.pair m 1) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.left_le_pair m 1) tendsto_id
  have hA : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 L) := by
    refine (hL.comp h0).congr fun m => ?_
    norm_num [Function.comp, unpairTable_pair_zero]
  have hB : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 L) := by
    refine (hL.comp h1).congr fun m => ?_
    norm_num [Function.comp, unpairTable_pair_one]
  have e1 : L = 1 := tendsto_nhds_unique hA tendsto_const_nhds
  have e0 : L = 0 := tendsto_nhds_unique hB tendsto_const_nhds
  rw [e1] at e0
  norm_num at e0

/-- The reader's price of the live atom has no limit either: the conclusion of
`atom_learned_unpair_live` is not an instance of any convergent form.
Source: none: infrastructure (non-degeneracy of `atom_learned_unpair_live`)
Kind: L
Fidelity: n/a -/
theorem unpair_live_price_not_convergent (j : ℕ) :
    ¬ ∃ L : ℝ, Tendsto (fun n => liaHistory unpairProcess n ((ledgerLuv j n).gt (3 / 4))) atTop
      (𝓝 L) := by
  rintro ⟨L, hL⟩
  apply unpair_pattern_not_convergent j
  refine ⟨L, ?_⟩
  have h := atom_learned_unpair_live j
  unfold AsympEq at h
  have := hL.sub h
  rw [sub_zero] at this
  exact this.congr fun n => by ring

/-! ## `deferred_tracking`'s full package at a constant lookahead (N−) -/

/-- **`deferred_tracking`'s full hypothesis package inhabited (N−)**: constant lookahead `F ≡ c`,
day-constant quoted sentence `ψ`, base `paperDP 𝗜𝚺₁` on both sides, the successor schedule
(at `c = 0` the mandate's publication-after-lookahead condition `F n ≤ (e j).e n` holds too);
`hz` discharged by `MachineRatCodes.const`, because the deferred table is then the constant
`liaQuote (paperDP 𝗜𝚺₁) c ψ`. N−: the target is constant, so `hz` is idle
(`deferred_tracking_constLookahead_hzFree`). `hz` at a genuine lookahead (`n ≤ F n`, a day-varying
table) — the intended instance — is unexhibited, and no FAF fact is expected to give it. Lifted
from audit r2 adversarial N1's probe.
Source: mandate T5 / [[STANDARDS]] §3 (witness of `deferred_tracking`'s full package)
Kind: N−
Fidelity: n/a
Hyps: (a) none (every hypothesis of `deferred_tracking`, including `hz`, discharged) -/
theorem deferred_tracking_constLookahead (c j : ℕ) (ψ : Sentence) :
    (fun n => (ledgerLuv j n).expect
      (deferredReader (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (fun _ => c) (fun _ _ => ψ)
        (fun _ => PublicationSchedule.succ)) n) ≈ₙ
      (fun n => (deferredTable (paperDP 𝗜𝚺₁) (fun _ => c) (fun _ _ => ψ) j n : ℝ)) :=
  deferred_tracking (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) (fun _ => c) (Computable.const c) (fun _ _ => ψ)
    (Computable.const ψ) (fun _ => PublicationSchedule.succ) succSchedule_computable
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁) j
    (PGenerableRat.ofMachineRatCodes
      ((MachineRatCodes.const (liaQuote (paperDP 𝗜𝚺₁) c ψ)).of_eq fun _ => rfl) _)

/-- Why `deferred_tracking_constLookahead` is N−: the same conclusion with **no `hz`**, through T3
(`pinning_ofTendsto`) at the constant target.
Source: none: infrastructure (degeneracy of `deferred_tracking_constLookahead`)
Kind: L
Fidelity: n/a -/
theorem deferred_tracking_constLookahead_hzFree (c j : ℕ) (ψ : Sentence) :
    (fun n => (ledgerLuv j n).expect
      (deferredReader (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (fun _ => c) (fun _ _ => ψ)
        (fun _ => PublicationSchedule.succ)) n) ≈ₙ
      (fun n => (deferredTable (paperDP 𝗜𝚺₁) (fun _ => c) (fun _ _ => ψ) j n : ℝ)) :=
  haveI := deferred_inductor (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) (fun _ => c) (Computable.const c) (fun _ _ => ψ)
    (Computable.const ψ) (fun _ => PublicationSchedule.succ) succSchedule_computable
  pinning_ofTendsto (ledgerLuv_thresholdCodes j)
    (deferredProcess_hworld
      (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
      (paperDP_hworld 𝗜𝚺₁))
    (fun n => deferred_determined (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (fun _ => c) (fun _ _ => ψ)
      (fun _ => PublicationSchedule.succ) j n)
    ((tendsto_const_nhds (x := ((liaQuote (paperDP 𝗜𝚺₁) c ψ : ℚ) : ℝ))).congr fun _ => rfl)

end Cleanroom.Deference.DefTrackingPin
