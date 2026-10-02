import Cleanroom.Deference.DefFrozenSibling.Defs
import Cleanroom.Deference.DefFrozenSibling.Engine
import Cleanroom.Li.LiCoupledPair.Siblings
import Cleanroom.Found.LiQuoteLane.Witnesses
import Cleanroom.Found.LiQuoteLane.Computability
import Cleanroom.Bli.BliFound.PaperInstances
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Freeze.LIAPerturbation
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `def-frozen-sibling` · OffG: T5, Target-Soundness fails off `G` — the counter-model

[[frozen-deliberation-deference-v6]] §Target-Soundness (anson-024; root-deference-045): "Off `G`,
TS does not follow — provably. Take a slow sequence with each `P^{(n)}` settling just after
`F(n)`, so each `Y_n` is a pre-settlement credence … a valid family exists whose diagonal is
pinned at, say, `0.6` while truth alternates: each member is mispriced on a single (stage,
sentence) pair, negligible for its own asymptotic calibration, so each remains a genuine
inductor, yet the diagonal is miscalibrated."

**The counter-model, over FAF, one-way** (`offGSystem`, `tsFails_offG`): a `FrozenSystem` whose
contract family consists of fresh atoms (family `16`, payload `⟨n, 0⟩`) decided in the shared
process at stage `F n + 1 = n + 2` with alternating polarity — one day *after* the horizon
`F = succDeferral` — so that no day is in `G` for any tolerance; every sibling is FAF's LIA on its
frozen process **perturbed at the single pair `(F N, contract N)` to `3/5`**, an inductor by FAF's
corrected `thm:ifp` (`lic_iff_of_finiteSupportPerturbation`, through the one-coordinate
perturbation `perturbAt` and its market computability); the diagonal `Y ≡ 3/5`; the predictor `A`
is FAF's LIA over the shared process plus the contract ledger settled to `3/5`; the advised
reasoner is FAF's LIA over the shared process plus the two-item ledger (`A`'s actual expectation
of the contract, and `3/5`). Because `Y` is constant, **no joint fixed point is needed**: `A` is
built first, its expectations are a computable table, the advised reasoner and the siblings read
it — the plan's one-way shape. The perturbation sits on a sentence undecided at `F N` in the
sibling's process: the corpus's "a pre-settlement credence the criterion leaves free".

This is the **only** module of the package importing the LIA compiler
(`LogicalInduction.Construction.LIACompiler`, through `LIA_is_logical_inductor`) and FAF's
freeze layer; a slice kill costs this file alone ([[plan]] §0.5).

Kind N+, Status `proved`: the source's claim — TS fails off `G` on this family — is confirmed
over FAF (the mandate's `refuted` against the universal "TS off `G`" is nobody's claim,
[[STANDARDS]] §6, audit r1 fidelity N3); the surviving neighbour is the definitional
`timely_tolerance` (`Defs.lean`). The old Lean's `TS_off_G_fails` was a witness on
bare sequences ([[AUDIT]]: "N− at best"); here every datum is a market, a process or a decided
atom, and the three inductor fields are FAF theorems.
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair
open Filter Topology

/-! ## A. One-coordinate perturbation of a computable market (FAF's `liaPerturbed`, at an
arbitrary coordinate) -/

/-- The history `P` with the single coordinate `(d, ψ)` moved to `r` (FAF's `liaPerturbed` at an
arbitrary day and sentence).
Source: FAF `Construction/Freeze/LIAPerturbation.lean` (`liaPerturbed`); mandate T5
Kind: D
Fidelity: n/a -/
noncomputable def perturbAt (P : History) (d : ℕ) (ψ : Sentence) (r : ℚ) : History :=
  fun n φ => if n = d ∧ φ = ψ then (r : ℝ) else P n φ

/-- `perturbAt_at`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma perturbAt_at (P : History) (d : ℕ) (ψ : Sentence) (r : ℚ) :
    perturbAt P d ψ r d ψ = (r : ℝ) := by
  rw [perturbAt, if_pos ⟨rfl, rfl⟩]

/-- A rational quote table with one entry overridden.
Source: FAF `perturbedQuote`
Kind: D
Fidelity: n/a -/
def perturbedTable (mq : ℕ → ℕ → ℚ) (d c : ℕ) (r : ℚ) : ℕ → ℕ → ℚ :=
  fun n c' => if n = d ∧ c' = c then r else mq n c'

/-- `computable_perturbedTable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma computable_perturbedTable {mq : ℕ → ℕ → ℚ} (d c : ℕ) (r : ℚ)
    (h : Computable (fun z : ℕ => Encodable.encode (mq z.unpair.1 z.unpair.2))) :
    Computable (fun z : ℕ => Encodable.encode (perturbedTable mq d c r z.unpair.1 z.unpair.2)) := by
  have h1 : Computable (fun z : ℕ => decide (z.unpair.1 = d)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const d)).decide.to_comp
  have h2 : Computable (fun z : ℕ => decide (z.unpair.2 = c)) :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const c)).decide.to_comp
  refine (Computable.cond h1
    (Computable.cond h2 (Computable.const (Encodable.encode r)) h) h).of_eq (fun z => ?_)
  rw [perturbedTable]
  by_cases ha : z.unpair.1 = d
  · by_cases hb : z.unpair.2 = c
    · simp [ha, hb]
    · simp [ha, hb]
  · simp [ha]

/-- **The perturbed market is computable** (FAF's `computableMarket_liaPerturbed` at an arbitrary
coordinate).
Source: FAF `computableMarket_liaPerturbed` (`app:ifp`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem computableMarket_perturbAt {P : History} (hP : ComputableMarket P) (d : ℕ) (ψ : Sentence)
    (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : ComputableMarket (perturbAt P d ψ r) := by
  obtain ⟨hrange, mq, code, hexact, hcode⟩ := hP
  have hrange' : ∀ n φ, 0 ≤ perturbAt P d ψ r n φ ∧ perturbAt P d ψ r n φ ≤ 1 := by
    intro n φ
    rw [perturbAt]
    split_ifs
    · exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
    · exact hrange n φ
  refine ComputableMarket.ofComputableTable (perturbedTable mq d (Encodable.encode ψ) r) hrange'
    (fun n φ => ?_)
    (computable_perturbedTable d _ r (LIAPerturbation.computable_of_marketCode hcode))
  rw [perturbAt, perturbedTable]
  by_cases hc : n = d ∧ φ = ψ
  · rw [if_pos hc, if_pos ⟨hc.1, by rw [hc.2]⟩]
  · rw [if_neg hc, if_neg ?_, hexact n φ]
    intro hd
    exact hc ⟨hd.1, Encodable.encode_injective hd.2⟩

/-- **Moving one price keeps the criterion** (FAF's corrected `thm:ifp`,
`lic_iff_of_finiteSupportPerturbation`, with the support `{(d, ψ)}`).
Source: FAF `thm:ifp` (`lic_iff_of_finiteSupportPerturbation`); mandate T5
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem perturbAt_inductor {P : History} {DP : DeductiveProcess} (hLI : IsLogicalInductor P DP)
    (d : ℕ) (ψ : Sentence) (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsLogicalInductor (perturbAt P d ψ r) DP :=
  (FreezeOracle.lic_iff_of_finiteSupport P (perturbAt P d ψ r) DP hLI.marketComputable
    (computableMarket_perturbAt hLI.marketComputable d ψ r h0 h1)
    ⟨{(d, ψ)}, fun d' φ h => by
      rw [perturbAt, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h (Finset.mem_singleton_self _)⟩).mp hLI

/-! ## B. The contract family and the shared process: fresh atoms decided one day after the
horizon, alternating -/

/-- The fresh-atom family of the counter-model's contracts (`bli-found` registry: `8`–`15`
reserved, `16` free; a registry row is requested in the report).
Source: mandate T5 ("a contract family of fresh tag-`0` atoms", here the run's own allocator)
Kind: D
Fidelity: n/a -/
def contractFamily : ℕ := 16

/-- The contract propositions: the fresh atom of family `16` with payload `⟨n, 0⟩` (day first).
Source: mandate T5
Kind: D
Fidelity: n/a -/
def contract5 (n : ℕ) : Sentence := freshAtom contractFamily (Nat.pair n 0)

/-- The stage-`s` entries of the contract schedule: the contracts of days `n` with `n + 2 ≤ s`,
with polarity `n` even.
Source: mandate T5 ("decided at stage `F n + 1`, with alternating polarity")
Kind: D
Fidelity: n/a -/
def enum5 (s : ℕ) : List (ℕ × ℕ × Bool) :=
  (List.range (s - 1)).map fun n => (contractFamily, Nat.pair n 0, decide (n % 2 = 0))

/-- `mem_enum5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_enum5 {s : ℕ} {x : ℕ × ℕ × Bool} :
    x ∈ enum5 s ↔ ∃ n, n < s - 1 ∧ (contractFamily, Nat.pair n 0, decide (n % 2 = 0)) = x := by
  simp [enum5, List.mem_map, List.mem_range]

/-- `enum5_mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enum5_mono : ∀ s, ∀ x ∈ enum5 s, x ∈ enum5 (s + 1) := by
  intro s x hx
  rw [mem_enum5] at hx ⊢
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨n, by omega, rfl⟩

/-- The contract schedule.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def contractSchedule : LiteralSchedule := LiteralSchedule.ofList enum5 enum5_mono

/-- `contractSchedule_functional`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma contractSchedule_functional : contractSchedule.Functional := by
  rintro s f p ⟨h1, h2⟩
  rw [contractSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum5] at h1 h2
  obtain ⟨n, -, hn⟩ := h1
  obtain ⟨m, -, hm⟩ := h2
  simp only [Prod.mk.injEq] at hn hm
  obtain ⟨-, hp1, hb1⟩ := hn
  obtain ⟨-, hp2, hb2⟩ := hm
  rw [← hp2, Nat.pair_eq_pair] at hp1
  rw [hp1.1] at hb1
  rw [hb1] at hb2
  exact Bool.noConfusion hb2

/-- `enum5_primrec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enum5_primrec : Primrec enum5 := by
  have hg : Primrec₂ fun (_ n : ℕ) => (contractFamily, Nat.pair n 0, decide (n % 2 = 0)) :=
    (Primrec.const contractFamily).pair
      ((Primrec₂.natPair.comp Primrec.snd (Primrec.const 0)).pair
        (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
          (Primrec.const 0)).decide)
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.id
    (Primrec.const 1))) hg

/-- **The shared process of the counter-model**: FAF's `paperDP 𝗜𝚺₁` with the contract atoms
adjoined, each decided at stage `n + 2` with alternating polarity.
Source: mandate T5
Kind: D
Fidelity: n/a -/
noncomputable def base5 : DeductiveProcess := extendBy (paperDP 𝗜𝚺₁) contractSchedule

/-- `base5_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base5_computable : ComputableDeductiveProcess base5 :=
  extendBy_ofList_computable (paperDP_computable 𝗜𝚺₁) enum5 enum5_mono enum5_primrec

/-- `base5_hworld`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base5_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base5.D n) :=
  extendBy_hworld contractSchedule_functional
    (ProcessFreeOf.of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) _) (paperDP_hworld 𝗜𝚺₁)

/-- `base5_tagFree`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base5_tagFree {t : ℕ} (h9 : cleanroomBaseTag ≤ t)
    (h16 : t ≠ cleanroomBaseTag + contractFamily) : TagFreeProcess t base5 := by
  intro k φ hφ
  rw [base5, extendBy_D, Finset.mem_union] at hφ
  rcases hφ with h | h
  · exact paperDP_tagFree 𝗜𝚺₁ h9 k φ h
  · rw [Finset.mem_image] at h
    obtain ⟨x, hx, rfl⟩ := h
    rw [contractSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum5] at hx
    obtain ⟨n, -, rfl⟩ := hx
    by_cases hn : n % 2 = 0
    · simp only [hn, decide_true, literalOf_true]
      exact freshAtom_tagFree_of_ne h16
    · simp only [hn, decide_false, literalOf_false]
      exact (freshAtom_tagFree_of_ne h16).neg

/-- `base5_freeOf_ledger`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base5_freeOf_ledger (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ProcessFreeOf (ledgerSchedule a e) base5 :=
  ProcessFreeOf.of_tagFree fun f hf => by
    rw [ledgerSchedule_families a e f hf]
    exact base5_tagFree (by simp [cleanroomBaseTag, ledgerFamily])
      (by simp [cleanroomBaseTag, ledgerFamily, contractFamily])

/-- Even days: the contract is in stage `n + 2` of the shared process.
Source: mandate T5 ("truth alternating")
Kind: L
Fidelity: n/a -/
theorem contract5_mem_of_even (n : ℕ) (hn : n % 2 = 0) : contract5 n ∈ base5.D (n + 2) := by
  rw [base5, extendBy_D]
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨(contractFamily, Nat.pair n 0, true), ?_, by simp [contract5]⟩
  rw [contractSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum5]
  exact ⟨n, by omega, by simp [hn]⟩

/-- Odd days: the contract's negation is in stage `n + 2`.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem contract5_neg_mem_of_odd (n : ℕ) (hn : n % 2 = 1) : ∼contract5 n ∈ base5.D (n + 2) := by
  rw [base5, extendBy_D]
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨(contractFamily, Nat.pair n 0, false), ?_, by simp [contract5]⟩
  rw [contractSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum5]
  exact ⟨n, by omega, by simp [hn]⟩

/-- `contract5_not_mem_paper`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem contract5_not_mem_paper (n k : ℕ) :
    contract5 n ∉ (paperDP 𝗜𝚺₁).D k ∧ ∼contract5 n ∉ (paperDP 𝗜𝚺₁).D k := by
  constructor
  · intro h
    have hc := paperDP_cleanroomFree 𝗜𝚺₁ k _ h
    exact hc.freshAtomCode_notMem contractFamily (Nat.pair n 0) (by simp [contract5])
  · intro h
    have hc := paperDP_cleanroomFree 𝗜𝚺₁ k _ h
    exact hc.freshAtomCode_notMem contractFamily (Nat.pair n 0) (by simp [contract5])

/-- An atom is never a negation (by formula complexity).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atom_ne_neg (a : ℕ) (φ : Sentence) : (Formula.atom a : Sentence) ≠ ∼φ := by
  intro h
  have := congrArg Formula.complexity h
  rw [Formula.neg_def] at this
  simp [Formula.complexity] at this

/-- **Not decided by the horizon**: neither the contract nor its negation is in stage `n + 1`
(the horizon `F n = n + 1`) of the shared process — the schedule decides day `n` only at
stage `n + 2`, and FAF's `paperDP` never mentions the fresh atom.
Source: mandate T5 ("decided at stage `F n + 1`, not at `F n`")
Kind: L
Fidelity: n/a -/
theorem contract5_not_mem_succ (n : ℕ) :
    contract5 n ∉ base5.D (n + 1) ∧ ∼contract5 n ∉ base5.D (n + 1) := by
  have hp := contract5_not_mem_paper n (n + 1)
  have hlit : ∀ x ∈ contractSchedule.lits (n + 1),
      literalOf x ≠ contract5 n ∧ literalOf x ≠ ∼contract5 n := by
    intro x hx
    rw [contractSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum5] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    have hmn : m ≠ n := by omega
    have hne : freshAtom contractFamily (Nat.pair m 0) ≠ contract5 n := by
      intro h
      rw [contract5, freshAtom_inj, Nat.pair_eq_pair] at h
      exact hmn h.2.1
    by_cases h2 : m % 2 = 0
    · simp only [h2, decide_true, literalOf_true]
      exact ⟨hne, atom_ne_neg _ _⟩
    · simp only [h2, decide_false, literalOf_false]
      constructor
      · intro h
        exact atom_ne_neg _ _ h.symm
      · intro h
        rw [Formula.neg_def, Formula.neg_def] at h
        exact hne (Formula.imp.inj h).1
  constructor
  · intro h
    rw [base5, extendBy_D, Finset.mem_union, Finset.mem_image] at h
    rcases h with h | ⟨x, hx, hxe⟩
    · exact hp.1 h
    · exact (hlit x hx).1 hxe
  · intro h
    rw [base5, extendBy_D, Finset.mem_union, Finset.mem_image] at h
    rcases h with h | ⟨x, hx, hxe⟩
    · exact hp.2 h
    · exact (hlit x hx).2 hxe

/-- The contract family is e.c. (one poly-fueled program writes the atom's code from `n`; FAF's
two bridges, as `li-quote-lane`'s `witnessQuoted_machineSentenceCodes`).
Source: mandate T5; `li-quote-lane` `Codes.lean`
Kind: L
Fidelity: n/a -/
theorem contract5_polySentenceCodes : PolySentenceCodes contract5 :=
  ⟨_, (((PolyFueled.const 1).pair ((PolyFueled.const (cleanroomBaseTag + contractFamily)).pair
    (PolyFueled.id.pair (PolyFueled.const 0)))).succ_comp).of_eq fun _ => rfl⟩

/-- `contract5_codes`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem contract5_codes : MachineSentenceCodes contract5 :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes contract5_polySentenceCodes)

/-! ## C. The predictor: FAF's LIA over the shared process plus the contract ledger settled to
`3/5` -/

/-- The constant diagonal `Y ≡ 3/5`.
Source: [[frozen-deliberation-deference-v6]] §Target-Soundness ("pinned at, say, `0.6`")
Kind: D
Fidelity: n/a -/
def Y5 : ℕ → ℚ := fun _ => 3 / 5

/-- The predictor's process: `base5` plus the contract ledger settled to `3/5` at
`payoutSchedule` (`σ n = n + 2`).
Source: mandate T5
Kind: D
Fidelity: n/a -/
noncomputable def DPA5 : DeductiveProcess :=
  ledgerProcess base5 (fun _ n => Y5 n) (fun _ => payoutSchedule)

/-- `DPA5_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DPA5_computable : ComputableDeductiveProcess DPA5 :=
  ledgerProcess_computable base5_computable
    ((Computable.const ((3 : ℚ) / 5)).of_eq fun _ => rfl) payoutSchedule_computable

/-- `A5_inductor`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem A5_inductor : IsLogicalInductor (liaHistory DPA5) DPA5 :=
  LIA_is_logical_inductor DPA5 DPA5_computable

/-- A market program for the predictor (FAF's LIA is a computable market).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def M5 : MarketComputation (liaHistory DPA5) :=
  Classical.choice A5_inductor.marketComputable.nonemptyComputation

/-- The published quote table: the predictor's exact rational day-`n` expectation of the contract
LUV `C_n` (FAF's `expectQuoteAt`).
Source: mandate T5 ("`h 0 n := a n` the LIA's actual expectation")
Kind: D
Fidelity: n/a -/
noncomputable def a5 (n : ℕ) : ℚ := M5.expectQuoteAt (ledgerLuv 0) n n

/-- `a5_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem a5_eq (n : ℕ) : (a5 n : ℝ) = (ledgerLuv 0 n).expect (liaHistory DPA5) n :=
  (M5.expectQuoteAt_cast (ledgerLuv 0) n n).symm

/-- `a5_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem a5_mem (n : ℕ) : 0 ≤ a5 n ∧ a5 n ≤ 1 := M5.expectQuoteAt_mem_Icc _ n n

/-- `a5_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem a5_computable : Computable a5 :=
  ((M5.expectQuoteAt_computable (ledgerLuv_thresholdCodes 0)).comp
    (Computable.id.pair Computable.id)).of_eq fun _ => rfl

/-! ## D. The advised reasoner and the siblings -/

/-- The two-item `H`-side table of the counter-model: the quote `a5` and the constant `3/5`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
noncomputable def table5 : ℕ → ℕ → ℚ := frozenTable a5 Y5

/-- The two-item schedules: the quote published the same day, the settled value at `n + 2`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def sched5 : ℕ → PublicationSchedule := frozenSched PublicationSchedule.sameDay payoutSchedule

/-- `table5_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem table5_mem (j n : ℕ) : 0 ≤ table5 j n ∧ table5 j n ≤ 1 := by
  unfold table5 frozenTable Y5
  split_ifs
  · exact a5_mem n
  · norm_num

/-- `table5_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem table5_computable : Computable fun p : ℕ × ℕ => table5 p.1 p.2 := by
  have hc : Computable fun p : ℕ × ℕ => decide (p.1 = 0) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide.to_comp
  refine (Computable.cond hc (a5_computable.comp Computable.snd)
    (Computable.const ((3 : ℚ) / 5))).of_eq fun p => ?_
  simp only [table5, frozenTable, Y5]
  by_cases h : p.1 = 0 <;> simp [h]

/-- `sched5_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sched5_computable : Computable fun p : ℕ × ℕ => (sched5 p.1).e p.2 := by
  have hc : Computable fun p : ℕ × ℕ => decide (p.1 = 0) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide.to_comp
  refine (Computable.cond hc Computable.snd
    (Primrec.succ.comp (Primrec.succ.comp Primrec.snd)).to_comp).of_eq fun p => ?_
  simp only [sched5, frozenSched, PublicationSchedule.sameDay, payoutSchedule]
  by_cases h : p.1 = 0 <;> simp [h]

/-- The advised reasoner's process: `base5` plus the two-item ledger.
Source: mandate T5
Kind: D
Fidelity: n/a -/
noncomputable def DPH5 : DeductiveProcess := ledgerProcess base5 table5 sched5

/-- `DPH5_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DPH5_computable : ComputableDeductiveProcess DPH5 :=
  ledgerProcess_computable base5_computable table5_computable sched5_computable

/-- Sibling `N`'s process: the two-item ledger frozen at day `N`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
noncomputable def sibProc5 (N : ℕ) : DeductiveProcess := siblingProcess base5 table5 sched5 N

/-- `sibProc5_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sibProc5_computable (N : ℕ) : ComputableDeductiveProcess (sibProc5 N) :=
  siblingProcess_computable base5_computable table5_computable sched5_computable N

/-- **The perturbed sibling**: FAF's LIA on the frozen process, with its day-`N + 1` price of the
contract `P^{(N)}` moved to `3/5`. The contract is undecided at `N + 1` in every process that
contains `base5` stage-wise (`contract5_not_mem_succ`), so the moved price is a pre-settlement
credence.
Source: [[frozen-deliberation-deference-v6]] §Target-Soundness ("each member mispriced on a single (stage, sentence) pair"); mandate T5
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def sib5 (N : ℕ) : History :=
  perturbAt (liaHistory (sibProc5 N)) (N + 1) (contract5 N) (3 / 5)

/-- `sib5_inductor`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sib5_inductor (N : ℕ) : IsLogicalInductor (sib5 N) (sibProc5 N) :=
  perturbAt_inductor (LIA_is_logical_inductor _ (sibProc5_computable N)) _ _ _ (by norm_num)
    (by norm_num)

/-! ## E. The counter-model as a `FrozenSystem` -/

/-- **The off-`G` counter-model** (T5): a `FrozenSystem` with the shared process `base5`
(`paperDP 𝗜𝚺₁` plus the alternating contract atoms decided one day after the horizon),
`F = succDeferral`, settlement at `n + 2`, the predictor FAF's LIA over the contract ledger settled
to `3/5`, the advised reasoner FAF's LIA over the two-item ledger, and every sibling the perturbed
LIA with its horizon price of the contract moved to `3/5`. One-way: no joint fixed point, because
the diagonal is constant.
Source: [[frozen-deliberation-deference-v6]] §Target-Soundness (anson-024); [[deference-in-logical-induction-v6]] §5.7 (root-deference-045); mandate T5
Kind: N+
Fidelity: exact (the source's "pinned at `0.6` while truth alternates")
Hyps: (a) none -/
noncomputable def offGSystem : FrozenSystem where
  base := base5
  DPA0 := base5
  shared := fun _ => subset_rfl
  eq := PublicationSchedule.sameDay
  eY := payoutSchedule
  F := succDeferral
  σ := payoutSchedule
  eq_lt_F := fun n => Nat.lt_succ_self n
  F_lt_σ := fun n => by show n + 1 < n + 2; omega
  σ_le_eY := fun _ => le_rfl
  contract := contract5
  contract_codes := contract5_codes
  contract_ledgerFree := fun _ =>
    freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, ledgerFamily, contractFamily])
  contract_projFree := fun _ =>
    freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, contractFamily])
  A := liaHistory DPA5
  Hplus := liaHistory DPH5
  sib := sib5
  a := a5
  Y := Y5
  Y_eq := fun n => (perturbAt_at _ _ _ _).symm
  a_eq := a5_eq
  A_inductor := A5_inductor
  Hplus_inductor := LIA_is_logical_inductor DPH5 DPH5_computable
  sib_inductor := sib5_inductor
  hworldA := ledgerProcess_hworld (base5_freeOf_ledger _ _) base5_hworld
  hworldH := ledgerProcess_hworld (base5_freeOf_ledger _ _) base5_hworld
  hworldSib := fun N => sibling_hworld (base5_freeOf_ledger _ _) base5_hworld N
  determinedA := fun n =>
    ledgerLuv_determinedVia base5 _ _ (fun _ _ => ⟨by norm_num [Y5], by norm_num [Y5]⟩) 0 n
  determinedH := fun j n => ledgerLuv_determinedVia base5 _ _ table5_mem j n
  determinedSib := fun N j n hN => siblingLuv_determinedVia base5 _ _ table5_mem N j n hN

/-- **T5 — Target-Soundness fails off `G`** (headline, N+; Status `proved`: the source's claim
confirmed over FAF, with the surviving neighbour `timely_tolerance`). There is a
frozen-deliberation system and a vanishing tolerance schedule such that **no day is timely** —
every contract is decided in the shared process one day after the horizon, so the decided clause
fails at every `n` — while the diagonal is pinned at `3/5` and the decided values alternate (`1`
on even days, `0` on odd days), with every datum of the witness pinned: shared process `base5`,
horizon `succDeferral`, settlement `payoutSchedule`, the contract family `contract5`, the
predictor FAF's LIA over `DPA5`, the advised reasoner FAF's LIA over `DPH5`, every sibling the
perturbed LIA `sib5`. **The failure is in the statement** (repair round 1, audit r1 N3): the shared
process has a completed-theory world (the conjunct `∃ v`, added in repair round 2, audit r2
fidelity N7), and in every such world the relayed verdict `Y_n = 3/5` is at least `2/5` from the
contract's payout, at every `n` — the diagonal is never within a vanishing tolerance of the truth.
**The tolerance conjuncts are decorative** (audit r2 adversarial N3): the decided clause fails at
every day, so no day is timely at *any* tolerance (`offG_not_timely_any`), and the content is the
world-distance conjunct and the pins. (A docstring-only remark, not in the statement: among
contracts with `Y_n = 3/5` the outcome frequency is `1/2`, not `3/5`.) The diagonal is constant
because the source prescribes it ("pinned at, say, `0.6`"); the truth table alternates.
Source: [[frozen-deliberation-deference-v6]] §Target-Soundness ("Off `G`, TS does not follow — provably"; anson-024); [[deference-in-logical-induction-v6]] §5.7 (root-deference-045); lean-deference-024 (`TS_off_G_fails`, [[AUDIT]]: "a witness on bare sequences")
Kind: N+
Fidelity: exact (the source's slow family, over FAF's LIA and `thm:ifp`; constant diagonal as the source prescribes); stronger: every day is off `G`, for every tolerance, and the world distance `≥ 2/5` holds at every day in every world, of which one exists
Hyps: (a) none -/
theorem tsFails_offG :
    ∃ S : FrozenSystem, ∃ ε : ℕ → ℚ,
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
      (∀ n, ¬ Timely S ε n) ∧ (∀ n, ¬ DecidedBy S n) ∧
      (∀ n, S.Y n = 3 / 5) ∧
      (∀ n, n % 2 = 0 → S.contract n ∈ S.base.D (S.F.f n + 1)) ∧
      (∀ n, n % 2 = 1 → ∼S.contract n ∈ S.base.D (S.F.f n + 1)) ∧
      (∃ v : PCWorld, v.ConsistentWithTheory S.base) ∧
      (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory S.base →
        (2 / 5 : ℝ) ≤ |(S.Y n : ℝ) - v.payout (S.contract n)|) ∧
      S.base = base5 ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧ S.contract = contract5 ∧
      S.A = liaHistory DPA5 ∧ S.Hplus = liaHistory DPH5 ∧ S.sib = sib5 := by
  refine ⟨offGSystem, fun n => 1 / ((n : ℚ) + 1), ?_, ?_, ?_, fun _ => rfl, ?_, ?_,
    offGSystem.base_theoryWorld, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have he : (fun n : ℕ => (((1 / ((n : ℚ) + 1)) : ℚ) : ℝ)) =
        fun n : ℕ => 1 / ((n : ℝ) + 1) := by
      funext n
      simp
    rw [he]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n hT
    exact (contract5_not_mem_succ n).1 (hT.1.elim id (fun h => absurd h (contract5_not_mem_succ n).2))
  · intro n h
    exact h.elim (contract5_not_mem_succ n).1 (contract5_not_mem_succ n).2
  · intro n hn
    exact contract5_mem_of_even n hn
  · intro n hn
    exact contract5_neg_mem_of_odd n hn
  · intro n v hv
    show (2 / 5 : ℝ) ≤ |((Y5 n : ℚ) : ℝ) - v.payout (contract5 n)|
    unfold PCWorld.payout
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have hh : v.Holds (contract5 n) := hv.holds_of_mem_stage ⟨_, contract5_mem_of_even n hn⟩
      rw [if_pos hh]
      norm_num [Y5]
    · have hh : v.Holds (∼contract5 n) :=
        hv.holds_of_mem_stage ⟨_, contract5_neg_mem_of_odd n hn⟩
      rw [PCWorld.holds_neg] at hh
      rw [if_neg hh]
      norm_num [Y5]

/-- **The moved coordinate**: at `(F N, contract N)` the perturbed sibling's price is `3/5` by
construction (`perturbAt_at`). Whether FAF's LIA's own quote at that coordinate differs from
`3/5` is not established here (`liaQuote_mem` keeps it in `[0,1]`; nothing pins it); the
counter-model moves a pre-settlement price the criterion leaves free, and its content is
`tsFails_offG`'s world-distance conjunct, not this lemma.
Source: mandate T5; FAF `liaPerturbed_ne` (the same remark at the LIA's own coordinate)
Kind: L
Fidelity: n/a -/
theorem sib5_at (N : ℕ) : sib5 N (N + 1) (contract5 N) = ((3 / 5 : ℚ) : ℝ) :=
  perturbAt_at _ _ _ _

/-! ## E′. The counter-model read closely (repair round 2) -/

/-- At the counter-model no day is timely at **any** tolerance: the decided clause fails at every
day, so the `ε → 0` conjunct of `tsFails_offG` does no work (audit r2 adversarial N3).
Source: audit r2 adversarial N3 (probe `PinnedSystems.lean`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem offG_not_timely_any (ε : ℕ → ℚ) (n : ℕ) : ¬ Timely offGSystem ε n := fun h =>
  h.1.elim (contract5_not_mem_succ n).1 (contract5_not_mem_succ n).2

/-- The constant diagonal `3/5` is generable at the predictor (`MachineRatCodes.const`): the (c)
`hz` of T1 is discharged at the counter-model.
Source: audit r2 fidelity N3 (probe `PointwiseCeiling.lean`)
Kind: L
Fidelity: n/a -/
theorem hz_offG : PGenerableRat offGSystem.A offGSystem.Y :=
  PGenerableRat.ofMachineRatCodes (MachineRatCodes.const (3 / 5)) _

/-- T1 at the counter-model: the predictor's quote tends to the constant diagonal `3/5`.
Source: audit r2 fidelity N3; T1 (`tracking_exact`)
Kind: L
Fidelity: n/a -/
theorem a5_asymp : (fun n => (a5 n : ℝ)) ≈ₙ fun _ => (((3 / 5 : ℚ)) : ℝ) :=
  tracking_exact offGSystem hz_offG

/-- The parity ruler `n ↦ n % 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem parity_ruler : UnaryRuler (fun n : ℕ => n % 2) :=
  (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two

/-- The even-day contract subfamily (`⊤` on odd days) is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem evenContract_codes :
    MachineSentenceCodes (fun n => if n % 2 = 0 then contract5 n else (⊤ : Sentence)) :=
  MachineSentenceCodes.ifZero contract5_codes (MachineSentenceCodes.const ⊤) parity_ruler

/-- The advised reasoner's process has a consistent world at every stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DPH5_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH5.D n) :=
  ledgerProcess_hworld (base5_freeOf_ledger table5 sched5) base5_hworld

/-- On even days the contract is a theorem of the advised reasoner's completed theory (it is in
stage `n + 2` of `base5 ⊆ DPH5`); on odd days the subfamily is `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem evenContract_holds (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DPH5) :
    v.Holds (if n % 2 = 0 then contract5 n else (⊤ : Sentence)) := by
  by_cases h : n % 2 = 0
  · rw [if_pos h]
    refine hv.holds_of_mem_stage ⟨n + 2, ?_⟩
    show contract5 n ∈ (ledgerProcess base5 table5 sched5).D (n + 2)
    exact (offGSystem.base_subset_processH (n + 2)) (contract5_mem_of_even n h)
  · rw [if_neg h]
    exact PCWorld.holds_top v

/-- The advised reasoner's price of the even-day contract subfamily tends to `1` (FAF's
provability induction on an e.c. family of eventual theorems).
Source: FAF `lic_provind_true`
Kind: C
Fidelity: n/a -/
theorem evenContract_price_one :
    (fun n => liaHistory DPH5 n (if n % 2 = 0 then contract5 n else (⊤ : Sentence))) ≈ₙ
      fun _ => 1 := by
  haveI : IsLogicalInductor (liaHistory DPH5) DPH5 := LIA_is_logical_inductor DPH5 DPH5_computable
  exact lic_provind_true (liaHistory DPH5) DPH5 _ evenContract_codes
    (fun n v hv => evenContract_holds n v hv) DPH5_hworld

/-- **T5's ceiling on a base-language family off `G`** (headline, N+; repair round 2, audit r2
fidelity N3): pointwise object-level deference `H⁺_n(P^{(n)}) ≈ₙ a_n` **fails** at the
counter-model. The advised reasoner's price of the decided contract tends to `1` on even days
(`evenContract_price_one`) while the quote tends to `3/5` (`a5_asymp`, T1 with the constant
approximant), so the two sequences are `2/5` apart on every late even day. This is the
*conclusion* of v6 T5's negative ("pointwise object-level deference is false") on a family inside
the base language — the source's own *argument* (the anti-inductive contract `𝟙[a_n ≤ ½]`) is
unavailable there (findings F5, `ledgerLiteral_not_mem_of_tagFree`); the slow family replaces it.
Roles: `Hplus` the advised reasoner (`liaHistory DPH5`), `a_n` the predictor's quote (`a5`).
Source: [[frozen-deliberation-deference-v6]] T5 (the negative: "`H⁺_n(P^{(n)}) ≈ₙ a_n` is false"); anson-025; findings F5 (third option); audit r2 fidelity N3 (probe `PointwiseCeiling.lean`)
Kind: N+
Fidelity: variant: the source's conclusion by a different witness (the slow family in place of the anti-inductive contract), over FAF
Hyps: (a) none -/
theorem pointwise_deference_fails_offG :
    ¬ ((fun n => liaHistory DPH5 n (contract5 n)) ≈ₙ fun n => (a5 n : ℝ)) := by
  intro h
  have h1 := asympEq_iff_eventuallyWithin.1 h (1 / 10) (by norm_num)
  have h2 := asympEq_iff_eventuallyWithin.1 a5_asymp (1 / 10) (by norm_num)
  have h3 := asympEq_iff_eventuallyWithin.1 evenContract_price_one (1 / 10) (by norm_num)
  unfold EventuallyWithin at h1 h2 h3
  rw [Filter.eventually_atTop] at h1 h2 h3
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  obtain ⟨N3, hN3⟩ := h3
  set n := 2 * (N1 + N2 + N3) with hn
  have heven : n % 2 = 0 := by omega
  have e1 := hN1 n (by omega)
  have e2 := hN2 n (by omega)
  have e3 := hN3 n (by omega)
  simp only [if_pos heven] at e3
  obtain ⟨a1, a2⟩ := abs_le.1 e1
  obtain ⟨b1, b2⟩ := abs_le.1 e2
  obtain ⟨c1, c2⟩ := abs_le.1 e3
  push_cast at b1 b2
  linarith

/-! ## F. Open statements of record -/

/-- The contract family of the pinned two-way witness: `li-quote-lane`'s `witnessQuoted 0 n` by
definition, the atoms `⟨0, ⟨0, n⟩⟩`. **Tag `0` is FAF's halting-claim tag** (repair round 2, audit
r2 adversarial B1 / fidelity N4; the round-1 docstring's "atoms `paperDP` never mentions" was
false): `theoremDP`'s event rows write `haltingClaimSentence z`, a tag-`0` atom, into stages of
`paperDP` whenever `IΣ₁` proves the halting instance (`halting_atom_mem_paperDP`). Whether a
`pinnedContract n` *itself* ever enters a stage of `paperDP 𝗜𝚺₁` comes down to whether
`Encodable.encode universalHaltingSchema = 0`, which is not decided here or in `li-quote-lane`
("not claimed either way", its `witnessQuoted` docstring) — so whether `G` is non-empty at
`frozenSystem_exists`'s pin is **unknown**.
Source: mandate D1 (existence, "every datum pinned as `sealedSystem_exists` pins them"); `li-quote-lane` `witnessQuoted`
Kind: D
Fidelity: n/a -/
def pinnedContract (n : ℕ) : Sentence := Formula.atom (Nat.pair 0 (Nat.pair 0 n))

/-- The pinned contract atoms carry FAF's halting-claim tag (`ComputationClaimKind.halting`).
Source: audit r2 adversarial B1 (probe `OpenPairTagZero.lean`); FAF `ComputationClaimKind.godelCode`
Kind: L
Fidelity: n/a -/
theorem pinnedContract_tag (n : ℕ) :
    ∀ a ∈ sentenceAtomCodes (pinnedContract n),
      a.unpair.1 = ComputationClaimKind.halting.godelCode := by
  intro a ha
  rw [pinnedContract, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  simp [ComputationClaimKind.godelCode]

/-- `theoremDP`'s event `(0, z)` names the halting-claim atom.
Source: audit r2 adversarial B1; FAF `eventAtom`
Kind: L
Fidelity: n/a -/
theorem eventAtom_zero (z : ℕ) : eventAtom (Nat.pair 0 z) = haltingClaimSentence z := by
  simp [eventAtom]

/-- The halting-claim atom carries tag `0` — the same tag as `pinnedContract`.
Source: audit r2 adversarial B1; FAF `sentenceAtomCodes_computationClaimSentence`
Kind: L
Fidelity: n/a -/
theorem haltingClaim_tag (z : ℕ) :
    ∀ a ∈ sentenceAtomCodes (haltingClaimSentence z), a.unpair.1 = 0 := fun a ha => by
  have h := sentenceAtomCodes_computationClaimSentence (haltingClaim z) a ha
  simpa [haltingClaim, ComputationClaimKind.godelCode] using h

/-- **`paperDP 𝗜𝚺₁` mentions tag-`0` atoms**: a provable halting instance puts one into a stage
(`theoremDP_covers`, `theoremDP_subset_paperDP`). The record of why the round-1 claim was false.
Source: audit r2 adversarial B1 (probe `OpenPairTagZero.lean`); FAF `theoremDP_covers`, `theoremDP_subset_paperDP`
Kind: L
Fidelity: n/a -/
theorem halting_atom_mem_paperDP (z : ℕ) (hz : eventFires 𝗜𝚺₁ (Nat.pair 0 z)) :
    ∃ k, haltingClaimSentence z ∈ (paperDP 𝗜𝚺₁).D k := by
  obtain ⟨k, hk⟩ := theoremDP_covers 𝗜𝚺₁ hz
  rw [eventAtom_zero] at hk
  exact ⟨k, theoremDP_subset_paperDP 𝗜𝚺₁ k hk⟩

/-- **OPEN of record — joint existence of a frozen-deliberation system over `paperDP 𝗜𝚺₁`**, every
datum pinned: shared and predictor base `paperDP 𝗜𝚺₁`, same-day quote publication, horizon
`succDeferral`, settlement `payoutSchedule`, the settled value published at `payoutSchedule`, the
tag-`0` contract family, and the three markets FAF's LIA on their own processes (so `a_eq` is the
LIA's rational expectation and `Y_eq` the LIA sibling's quote). The two-way recursion: `A`'s
process reads the siblings' verdicts, the siblings and `Hplus` read `A`'s expectations. This is
`li-coupled-pair`'s `sealedSystem_exists` with the expectation pin in place of the sentence-price
pin; its `SealedSpec` recursion was not adapted here (`frozenSystem_of_uniform` is not on disk;
report §D1 records why). **Which rows are partial over this statement** (repair round 2, audit r2
adversarial B1): the three global two-way rows (`tracking`, `metaTrust`, `metaTrust_expect`),
whose hypotheses need only `A_inductor` with `Y` the sibling's verdict (and `hz`, which has no
discharge at this pin: the diagonal is a sibling-LIA run). The nine on-`G` two-way rows are
partial over `timely_cofinite_const` instead: **whether `G` is non-empty at this pin is not
established** — tag `0` is FAF's halting-claim tag, `paperDP 𝗜𝚺₁` does write tag-`0` atoms into its
stages (`halting_atom_mem_paperDP`), and whether a `pinnedContract n` itself is among them is the
undecided question `encode universalHaltingSchema = 0` (`li-quote-lane` claims it neither way).
The round-1 docstring's "`paperDP` never mentions tag-`0` atoms, so at this pin every day is off
`G`" was false in its reason and unproved in its conclusion. Non-vacuity of `G` at a vanishing
tolerance is the business of `timely_cofinite_const` (over `base0`, where every day is decided,
`pinned_base0_decided`) and, one-way, of `onGSystem`.
Source: mandate D1 (existence); anson-017; root-deference-037; `li-coupled-pair` T4.3
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem frozenSystem_exists : ∃ S : FrozenSystem,
    S.base = paperDP 𝗜𝚺₁ ∧ S.DPA0 = paperDP 𝗜𝚺₁ ∧ S.eq = PublicationSchedule.sameDay ∧
    S.eY = payoutSchedule ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧
    S.contract = pinnedContract ∧ S.A = liaHistory S.processA ∧
    S.Hplus = liaHistory S.processH ∧ (∀ N, S.sib N = liaHistory (S.processSib N)) := by
  sorry

/-- The stage-`s` entries of the lag-`0` contract schedule: the contracts of days `n ≤ s`, with
polarity `n` even (decided at stage `n`, before the horizon `n + 1`).
Source: mandate D2 (non-vacuity of `G`: "a contract family decided in `base` … with alternating polarity")
Kind: D
Fidelity: n/a -/
def enum0 (s : ℕ) : List (ℕ × ℕ × Bool) :=
  (List.range (s + 1)).map fun n => (contractFamily, Nat.pair n 0, decide (n % 2 = 0))

/-- `enum0_mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enum0_mono : ∀ s, ∀ x ∈ enum0 s, x ∈ enum0 (s + 1) := by
  intro s x hx
  simp only [enum0, List.mem_map, List.mem_range] at hx ⊢
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨n, by omega, rfl⟩

/-- The shared process with the contracts decided at stage `n`: `paperDP 𝗜𝚺₁` plus the lag-`0`
schedule.
Source: mandate D2
Kind: D
Fidelity: n/a -/
noncomputable def base0 : DeductiveProcess :=
  extendBy (paperDP 𝗜𝚺₁) (LiteralSchedule.ofList enum0 enum0_mono)

/-- **OPEN of record — non-vacuity of `G` at a vanishing tolerance** (finding F3): at the pinned
two-way system over `base0` (contracts decided at stage `n < F n`, alternating, every market FAF's
LIA on its process), for every `δ > 0` almost every day is timely — i.e. the sibling family
converges **along its diagonal**: `sib n (n+1) (contract n) → truthAt n` as `n → ∞`. The
per-member criterion gives `sib n m (contract n) → truthAt n` as `m → ∞` for each `n`, not along
`m = F n`; whether FAF's LIA family has the diagonal property is unknown. Bundled with the
existence of the system (which is itself the OPEN pair). "On `G`, `Y_n → truth`" is true by
definition and says nothing about whether `G` is non-empty. **Read at its pins** (repair round 2,
audit r2 adversarial B1 (iii)/N1): every day is decided with decided value `Y0`
(`pinned_base0_decided`, `OnG.lean` §G), so the last conjunct is literally `S.Y n − Y0 n → 0`
(`cofinite_const_iff`), and once it holds every on-`G` theorem of the package applies at `t ≡ 0`
with the schedule `ε n := |S.Y n − Y0 n|` (`timely_all_of_diagonal`, `engineA_of_diagonal`) — this
is **the OPEN pair the nine on-`G` two-way rows are partial over**.
Source: [[frozen-deliberation-deference-v6]] §6 ("On `G`, `Y_n → truth`"); anson-023's quantifier-order flag; mandate D2 (F3)
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem timely_cofinite_const : ∃ S : FrozenSystem,
    S.base = base0 ∧ S.DPA0 = base0 ∧ S.eq = PublicationSchedule.sameDay ∧
    S.eY = payoutSchedule ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧
    S.contract = contract5 ∧ S.A = liaHistory S.processA ∧
    S.Hplus = liaHistory S.processH ∧ (∀ N, S.sib N = liaHistory (S.processSib N)) ∧
    ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n := by
  sorry

/-- **OPEN of record — can FAF's unperturbed LIA family lose a timely day to a strictly later
horizon?** (T13, finding F8; restated in repair round 1 after audit r1 adversarial B1.) Two
frozen-deliberation systems over `base0` with every datum pinned as `timely_cofinite_const` pins
them — same shared process, same contracts `contract5`, same-day quote, `A`, `Hplus` and every
sibling FAF's LIA on its own process (so the two sibling families are the *same construction*,
read at different horizons) — the first at horizon `succDeferral` (settlement `n + 2`), the
second at the strictly later horizon `n + 2` (settlement `n + 3`), a non-negative tolerance
schedule, and a day timely for the first and not for the second: the sibling's verdict one day
later, farther from the decided value. Neither proved nor refuted. The first-round statement of
this row (free systems, `F ≤ F'`) was proved by relabeling the sibling family with `F' = F`
(`timely_not_horizon_only`, `OnG.lean` §F) and so was mis-stated as open; the pins here remove
every freedom but the horizon. Bundled with the existence of the two pinned systems (the OPEN
pair over `base0`). The monotone direction (the source's "grow `G`") is not expected to hold for
the LIA family either, but nothing here decides it. **The tolerance is a free existential**
(repair round 2, audit r2 adversarial N1): at these pins both systems are decided at every day
with decided value `Y0`, so the last three conjuncts are exactly the one-day strict comparison
`|S.Y n − Y0 n| < |S'.Y n − Y0 n|` (`notMono_tol_iff`, `OnG.lean` §G; the general reduction is
`exists_tol_iff`, `Defs.lean` §F) — the row asks for one day on which the `(n+2)`-horizon
sibling's verdict is strictly farther from the decided value than the `(n+1)`-horizon one's.
Source: root-fa-2-011 (ii); [[legitimacy-theory-v1]] §7.2 ("grow `G`"); mandate T13
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem timely_not_mono_open : ∃ (S S' : FrozenSystem) (ε : ℕ → ℚ) (n : ℕ),
    S.base = base0 ∧ S.DPA0 = base0 ∧ S.eq = PublicationSchedule.sameDay ∧
    S.eY = payoutSchedule ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧
    S.contract = contract5 ∧ S.A = liaHistory S.processA ∧
    S.Hplus = liaHistory S.processH ∧ (∀ N, S.sib N = liaHistory (S.processSib N)) ∧
    S'.base = base0 ∧ S'.DPA0 = base0 ∧ S'.eq = PublicationSchedule.sameDay ∧
    (∀ m, S'.F.f m = m + 2) ∧ (∀ m, S'.σ.e m = m + 3) ∧ (∀ m, S'.eY.e m = m + 3) ∧
    S'.contract = contract5 ∧ S'.A = liaHistory S'.processA ∧
    S'.Hplus = liaHistory S'.processH ∧ (∀ N, S'.sib N = liaHistory (S'.processSib N)) ∧
    (∀ m, 0 ≤ ε m) ∧ Timely S ε n ∧ ¬ Timely S' ε n := by
  sorry


end Cleanroom.Deference.DefFrozenSibling
