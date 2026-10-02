import Cleanroom.Bli.BliExactBase.Splice
import Cleanroom.Bli.BliExactBase.Mixing
import Cleanroom.Bli.BliLinkage.LiaPackage

/-!
# `bli-exact-base` — K7b: the segment tables; exact `D_PC` (small form) and `D_ND` on `[0, H)`;
what the literal `D_PC` cannot be

**The tables.** `segmentPrice n` is the uniform mixture over a complete family of worlds
consistent with `(paperDP 𝗜𝚺₁).D n` for the day-`n` small atoms (`Mixing.exists_mixture`, a
choice over a finite set — never a computation: `smallSet n` has more than `2^(2^n)` members).
Spliced into FAF's LIA at horizon `H` (`Splice.spliceHistory H segmentPrice`), they give the
inductor of K7a (`spliceSegment_isLogicalInductor`) that on every day `n < H`:

* agrees on the small sentences with a stage mixture — **`D_PCsmall_on H`**
  (`segment_D_PCsmall_on`, Kind `C`), the segment claim of record;
* is non-dogmatic — **`D_ND_on H`** (`segment_D_ND_on`, Kind `C`): every day-`n` small sentence is
  decided true by the stage, decided false, or priced strictly inside `(0,1)`.

**What is false, and for every finite perturbation.** `bli-found`'s `D_PC` is coherence on the
*whole algebra* over the small atoms. The atom-free tautologies `tautChain k = ⊤ ⋎ ⊥ ⋎ … ⋎ ⊥`
(`bli-linkage` `LiaPackage`) lie in every such algebra; FAF's LIA prices all but finitely many of
them at `0` on every day (finite support, `quote_eq_zero_of_not_mem`); a finite-support
perturbation moves finitely many. So **no finite-support perturbation of the LIA over any process
is a stage mixture on any algebra on any day** (`not_coherentOn_of_finiteSupportPerturbation`, Kind
`P`): the literal `D_PC_on H` fails for every splice and every `H ≥ 1`
(`not_D_PC_on_splice`), and FAF's LIA itself is `D_PC` over no process (`not_D_PC_lia`). This is
stronger than the mandate's "`¬ D_PC` at the splice because days `≥ H` are the LIA": the segment
form of the *literal* predicate is already empty, which is why `D_PCsmall_on` is the statement of
record (findings F1).

**Non-vacuity (N+).** The splice differs from the LIA on day `4` on a small tautology
(`splice_ne_lia_day4`: the LIA lists at most `2945` sentences on day `4`, `LiaSupport`, while
`16384` chains are small there); and the fresh coordinate `freshCoord` (family `10`, mentioned by
no stage of `paperDP 𝗜𝚺₁`) is small from day `2` and priced strictly inside `(0,1)` on every
segment day `n ≥ 2` (`splice_freshCoord_interior`) — the uncertain coordinate K7c/K7d need.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliLinkageB
open Cleanroom.Bli.BliLinkage (tautChain holds_tautChain tautChain_injective tautChain_mem_smallSet
  coherentOn_valid_one liaStates_support_card_le_day4 atom_pair_small)

/-! ## The segment tables -/

/-- **The day-`n` segment table**: the uniform mixture over a complete family of worlds consistent
with the stage `(paperDP 𝗜𝚺₁).D n` for the day-`n` small atoms (`exists_mixture`; the stage has a
consistent world by FAF's `paperDP_hworld`). Data by choice over a finite set, not computed.
Source: mandate § 2 ("the tables (D + C)"); [[bli-program]] §3.6 (vi)
Kind: D
Fidelity: exact -/
noncomputable def segmentPrice (n : ℕ) : Sentence → ℚ :=
  Classical.choose (exists_mixture ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n))

/-- The defining property of `segmentPrice n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentPrice_spec (n : ℕ) :
    (∀ φ, 0 ≤ segmentPrice n φ ∧ segmentPrice n φ ≤ 1) ∧
    (∀ A', CoherentOn ((paperDP 𝗜𝚺₁).D n) A' (fun φ => (segmentPrice n φ : ℝ))) ∧
    ∀ φ, sentenceAtomCodes φ ⊆ smallAtoms n →
      (∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) → v.Holds φ) ∨
      (∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) → ¬ v.Holds φ) ∨
      (0 < segmentPrice n φ ∧ segmentPrice n φ < 1) :=
  Classical.choose_spec (exists_mixture ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n))

/-- Every table value is in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentPrice_mem_Icc (n : ℕ) (φ : Sentence) :
    0 ≤ segmentPrice n φ ∧ segmentPrice n φ ≤ 1 := (segmentPrice_spec n).1 φ

/-- The range clause of `def:market` for the segment tables, in the form K7a consumes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentPrice_inUnit (H : ℕ) :
    ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ segmentPrice n φ ∧ segmentPrice n φ ≤ 1 :=
  fun n _ φ _ => segmentPrice_mem_Icc n φ

/-- **The day-`n` table is a stage mixture on every algebra** (as a real-valued assignment).
Source: mandate § 2
Kind: L
Fidelity: exact -/
theorem segmentPrice_coherentOn (n : ℕ) (A : Finset ℕ) :
    CoherentOn ((paperDP 𝗜𝚺₁).D n) A (fun φ => (segmentPrice n φ : ℝ)) :=
  (segmentPrice_spec n).2.1 A

/-- **The day-`n` table is non-dogmatic on the small sentences.**
Source: mandate § 2
Kind: L
Fidelity: exact -/
theorem segmentPrice_trichotomy (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) :
    (∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) → v.Holds φ) ∨
    (∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) → ¬ v.Holds φ) ∨
    (0 < segmentPrice n φ ∧ segmentPrice n φ < 1) :=
  (segmentPrice_spec n).2.2 φ (atoms_subset_smallAtoms hφ)

/-- **The segment table as a `bli-finite` table** on `bli-trajectory`'s `smallIndex` (the stable
name for `bli-witness-lia`).
Source: mandate § Deliverables (`segmentTable n : Table smallIndex n`)
Kind: D
Fidelity: exact -/
noncomputable def segmentTable (n : ℕ) : Table Cleanroom.Bli.BliTrajectory.smallIndex n :=
  fun φ => segmentPrice n φ.1

/-- The segment table lies in the unit cube.
Source: mandate § Deliverables (`InUnit`)
Kind: L
Fidelity: n/a -/
theorem segmentTable_inUnit (n : ℕ) : (segmentTable n).InUnit :=
  fun φ => segmentPrice_mem_Icc n φ.1

/-! ## K7a at the segment tables -/

/-- **K7a instantiated**: the splice of the segment tables at every horizon is a logical inductor
over `paperDP 𝗜𝚺₁`.
Source: mandate § 1 (judged item 1); [[bli-program]] §3.6 (vi)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceSegment_isLogicalInductor (H : ℕ) :
    IsLogicalInductor (spliceHistory H segmentPrice) (paperDP 𝗜𝚺₁) :=
  splice_isLogicalInductor H segmentPrice (segmentPrice_inUnit H)

/-! ## K7b: the segment forms -/

/-- **K7b (coherence) — the spliced inductor agrees with a stage mixture on the small sentences on
every day `n < H`** (`D_PCsmall_on H`). The mixture is the day-`n` table itself.
Source: [[bli-program]] §2.6 (`D_PC`, "on the small sentences"), §3.6 (vi); mandate § 2 (judged
item 2, `segment_D_PC_on` in the small form of record — see `not_D_PC_on_splice` for why)
Kind: C
Fidelity: weaker: small-sentence agreement in place of coherence on the whole algebra over the small atoms (the literal form is false for every finite perturbation of the LIA, `not_D_PC_on_splice`)
Hyps: (a) -/
theorem segment_D_PCsmall_on (H : ℕ) :
    D_PCsmall_on H (spliceHistory H segmentPrice) (paperDP 𝗜𝚺₁) := by
  intro n hn
  obtain ⟨k, W, w, hW, hw0, hw1, hrep⟩ := segmentPrice_coherentOn n (smallAtoms n)
  refine ⟨k, W, w, hW, hw0, hw1, fun φ hφ => ?_⟩
  rw [spliceHistory_eq_tbl_of_lt hn hφ]
  exact hrep φ (atoms_subset_smallAtoms hφ)

/-- **K7b (non-dogmatism) — the spliced inductor is `D_ND` on every day `n < H`**: each day-`n`
small sentence is decided true by the stage, decided false by it, or priced strictly inside
`(0,1)`. A sentence decided by the completed theory but not yet by the stage counts as undecided
and gets an interior price (the stage-relative reading of `D_ND`).
Source: [[bli-program]] §2.6 (`D_ND`), §3.6 (vi); mandate § 2 (judged item 2)
Kind: C
Fidelity: exact (segment form)
Hyps: (a) -/
theorem segment_D_ND_on (H : ℕ) :
    D_ND_on H (spliceHistory H segmentPrice) (paperDP 𝗜𝚺₁) := by
  intro n hn φ hφ
  rw [spliceHistory_eq_tbl_of_lt hn hφ]
  rcases segmentPrice_trichotomy n hφ with h | h | ⟨h0, h1⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩)

/-- **On a segment day the splice is a base for which `bli-linkage`'s package clause
`PCPσ ∧ E1x` is satisfiable** — a fully coherent `P n` agreeing with it on the small sentences
exists; contrast FAF's LIA, for which none exists on day `4` for any process
(`LiaPackage.not_lia_small_coherent_mixture_exists`).
Source: mandate § 2; bli-linkage report § Interface notes 2
Kind: L
Fidelity: n/a -/
theorem segment_day_mixture_exists {H n : ℕ} (hn : n < H) :
    ∃ P : Sentence → ℝ, CoherentOn ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) P ∧
      ∀ φ ∈ smallSet n, P φ = spliceHistory H segmentPrice n φ :=
  (coherentOnSmall_iff_exists_mixture_agree _ _ _).1 (segment_D_PCsmall_on H n hn)

/-! ## The literal `D_PC` is empty for every finite perturbation of the LIA -/

/-- The chains `tautChain k` have no atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sentenceAtomCodes_tautChain : ∀ k, sentenceAtomCodes (tautChain k) = ∅
  | 0 => rfl
  | k + 1 => by
      show sentenceAtomCodes (tautChain k ⋎ ⊥) = ∅
      rw [sentenceAtomCodes_or, sentenceAtomCodes_tautChain k]
      rfl

/-- **No finite-support perturbation of FAF's LIA is a stage mixture on any algebra on any day**
(over any deductive process, relative to any finite `D`). The atom-free tautologies
`tautChain k` lie in every algebra; the LIA's day-`n` belief state has finite support and prices
every unlisted sentence at `0`; the perturbation moves finitely many coordinates; so some chain is
priced `0` while a mixture prices every tautology at `1` (`coherentOn_valid_one`).
Source: this package (findings F1); bli-linkage `LiaPackage` (the chains, `coherentOn_valid_one`);
FAF `RationalBeliefState.quote_eq_zero_of_not_mem`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_coherentOn_of_finiteSupportPerturbation (DP : DeductiveProcess) {P : History}
    (hP : FiniteSupportPerturbation (liaHistory DP) P) (n : ℕ) (D : Finset Sentence)
    (A : Finset ℕ) : ¬ CoherentOn D A (P n) := by
  classical
  intro hcoh
  obtain ⟨S, hS⟩ := hP
  have hfin : (((liaStates DP n).support : Set Sentence) ∪
      ((S.image Prod.snd : Finset Sentence) : Set Sentence)).Finite :=
    (Finset.finite_toSet _).union (Finset.finite_toSet _)
  have hinf : (Set.range tautChain).Infinite :=
    Set.infinite_range_of_injective tautChain_injective
  obtain ⟨φ, hφr, hφn⟩ := (hinf.sdiff hfin).nonempty
  obtain ⟨k, rfl⟩ := hφr
  simp only [Set.mem_union, Finset.mem_coe, Finset.mem_image, not_or, not_exists, not_and] at hφn
  obtain ⟨hsup, hpatch⟩ := hφn
  have hoff : (n, tautChain k) ∉ S := fun h => hpatch (n, tautChain k) h rfl
  have h0 : P n (tautChain k) = 0 := by
    rw [← hS n _ hoff, liaHistory_eq_quote_cast]
    change (((liaStates DP n).quote (tautChain k) : ℚ) : ℝ) = 0
    rw [RationalBeliefState.quote_eq_zero_of_not_mem _ hsup]
    norm_num
  have h1 : P n (tautChain k) = 1 :=
    coherentOn_valid_one hcoh (by rw [sentenceAtomCodes_tautChain]; exact Finset.empty_subset _)
      (fun v => holds_tautChain v k)
  rw [h0] at h1
  norm_num at h1

/-- **The literal `D_PC_on H` is empty for every finite-support perturbation of the LIA**, `H ≥ 1`.
Source: this package (findings F1)
Kind: L
Fidelity: n/a -/
theorem not_D_PC_on_of_finiteSupportPerturbation (DP : DeductiveProcess) {P : History}
    (hP : FiniteSupportPerturbation (liaHistory DP) P) {H : ℕ} (hH : 0 < H) :
    ¬ D_PC_on H P DP :=
  fun h => not_coherentOn_of_finiteSupportPerturbation DP hP 0 _ _ (h 0 hH)

/-- **The mandate's literal K7b statement is false for every splice and every table**: no
`spliceHistory H t` is `D_PC_on H` for `H ≥ 1` — not because days `≥ H` are the LIA, but because
`bli-found`'s `CoherentOn` reaches infinitely many sentences on every day. The segment claim of
record is `segment_D_PCsmall_on`.
Source: mandate § 2 (`not_D_PC_splice`, strengthened); findings F1
Kind: L
Fidelity: n/a -/
theorem not_D_PC_on_splice (H : ℕ) (hH : 0 < H) (t : ℕ → Sentence → ℚ) :
    ¬ D_PC_on H (spliceHistory H t) (paperDP 𝗜𝚺₁) :=
  not_D_PC_on_of_finiteSupportPerturbation _ (splice_finiteSupportPerturbation H t) hH

/-- The all-days `D_PC` is false at every splice (the mandate's `not_D_PC_splice`).
Source: mandate § Definitions (`¬ D_PC (spliceHistory …) (paperDP 𝗜𝚺₁)`)
Kind: L
Fidelity: n/a -/
theorem not_D_PC_splice (H : ℕ) (t : ℕ → Sentence → ℚ) :
    ¬ D_PC (spliceHistory H t) (paperDP 𝗜𝚺₁) :=
  fun h => not_coherentOn_of_finiteSupportPerturbation _ (splice_finiteSupportPerturbation H t)
    0 _ _ (h 0)

/-- **FAF's LIA is `D_PC` over no deductive process** (the trivial perturbation).
Source: this package (findings F1); bli-slides-044 (the gap, sharpened: not even one day)
Kind: L
Fidelity: n/a -/
theorem not_D_PC_lia (DP : DeductiveProcess) : ¬ D_PC (liaHistory DP) DP :=
  fun h => not_coherentOn_of_finiteSupportPerturbation DP ⟨∅, fun _ _ _ => rfl⟩ 0 _ _ (h 0)

/-! ## Non-vacuity -/

/-- Some small day-`4` chain is off the LIA's day-`4` support, for every process: `16384` chains
are small on day `4` and the LIA lists at most `2945` sentences there.
Source: bli-linkage `LiaSupport.liaStates_support_card_le_day4`, `LiaPackage.tautChain_mem_smallSet`
Kind: L
Fidelity: n/a -/
theorem exists_tautChain_offSupport_day4 (DP : DeductiveProcess) :
    ∃ k, 4 + 4 * k ≤ sizeBound 4 ∧ tautChain k ∉ (liaStates DP 4).support := by
  classical
  have hcard : (liaStates DP 4).support.card < ((Finset.range 16384).image tautChain).card := by
    rw [Finset.card_image_of_injective _ tautChain_injective, Finset.card_range]
    exact lt_of_le_of_lt (liaStates_support_card_le_day4 DP) (by norm_num)
  obtain ⟨φ, hφ, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hφ
  rw [Finset.mem_range] at hk
  refine ⟨k, ?_, hnot⟩
  simp only [sizeBound]
  norm_num
  omega

/-- **N+ for K7a — the splice differs from the LIA**: at every horizon `H > 4`, on day `4`, on a
small sentence (a tautology the LIA does not list, priced `0` by it and `1` by the table).
Source: mandate § 1 ("the splice differs from the LIA on every segment day on some small sentence");
bli-linkage `LiaSupport`
Kind: N+
Fidelity: weaker: shown on day `4` (the only day with a numeral support bound in the run; the counting generalizes to every `n ≥ 4` given `∑_{j≤n}(j(n+1)^j+j+1) < 2^(2^n−2)`, not proved)
Hyps: (a) -/
theorem splice_ne_lia_day4 (H : ℕ) (hH : 4 < H) :
    ∃ φ ∈ smallSet 4, spliceHistory H segmentPrice 4 φ ≠ liaHistory (paperDP 𝗜𝚺₁) 4 φ := by
  obtain ⟨k, hk, hoff⟩ := exists_tautChain_offSupport_day4 (paperDP 𝗜𝚺₁)
  have hsmall := tautChain_mem_smallSet hk
  refine ⟨tautChain k, hsmall, ?_⟩
  rw [spliceHistory_eq_tbl_of_lt hH hsmall, liaHistory_eq_quote_cast]
  change ((segmentPrice 4 (tautChain k) : ℚ) : ℝ) ≠
    (((liaStates (paperDP 𝗜𝚺₁) 4).quote (tautChain k) : ℚ) : ℝ)
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ hoff]
  have h1 : ((segmentPrice 4 (tautChain k) : ℚ) : ℝ) = 1 :=
    coherentOn_valid_one (segmentPrice_coherentOn 4 (smallAtoms 4))
      (atoms_subset_smallAtoms hsmall) (fun v => holds_tautChain v k)
  rw [h1]
  norm_num

/-- The fresh-atom family of this package (registry on `bli-found`'s `freshAtom`: `8`–`15` reserved;
`8`/`9` are used by `bli-leak`/`bli-extrapolation`, so `10`).
Source: mandate § Definitions (`freshCoord`)
Kind: D
Fidelity: n/a -/
def freshFamily : ℕ := 10

/-- **The uncertain coordinate**: a run-family fresh atom with a one-digit payload (day `0`, rest
`0`). Mentioned by no stage of `paperDP 𝗜𝚺₁` (`paperDP_cleanroomFree`), hence undecided at every
stage and priced strictly inside by every segment table (`segmentPrice_freshCoord_interior`).
Source: mandate § Definitions (`freshCoord`); bli-linkage report § Interface notes 2
Kind: D
Fidelity: exact -/
def freshCoord : Sentence := freshAtom freshFamily (Nat.pair 0 0)

/-- `freshCoord` is small from day `2` (its code is `380`, five base-4 digits; the mandate's "from
day `1`" is off by one: `sizeBound 1 = 4` admits no atom).
Source: mandate § Definitions (`freshCoord`, "`tokenSize` lemma")
Kind: L
Fidelity: n/a -/
theorem freshCoord_mem_smallSet {n : ℕ} (hn : 2 ≤ n) : freshCoord ∈ smallSet n := by
  have hcode : freshAtomCode freshFamily (Nat.pair 0 0) + 5 < 4 ^ 5 := by decide
  have hlen := length_natDigits4_le_of_lt_pow hcode
  have h16 : 16 ≤ sizeBound n :=
    calc 16 = sizeBound 2 := by norm_num [sizeBound]
      _ ≤ sizeBound n := sizeBound_mono hn
  exact (atom_pair_small n (freshAtomCode freshFamily (Nat.pair 0 0)) (by omega)).1

/-- No stage of `paperDP 𝗜𝚺₁` mentions `freshCoord`'s atom.
Source: bli-found `paperDP_cleanroomFree`
Kind: L
Fidelity: n/a -/
theorem freshCoord_free (k : ℕ) :
    ∀ φ ∈ (paperDP 𝗜𝚺₁).D k, freshAtomCode freshFamily (Nat.pair 0 0) ∉ sentenceAtomCodes φ :=
  fun φ hφ => (paperDP_cleanroomFree 𝗜𝚺₁ k φ hφ).freshAtomCode_notMem _ _

/-- `freshCoord` is undecided at every stage of `paperDP 𝗜𝚺₁`.
Source: mandate § Definitions (`freshCoord`: "undecided on every stage")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem freshCoord_undecided (n : ℕ) :
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ v.Holds freshCoord) ∧
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ ¬ v.Holds freshCoord) :=
  free_atom_undecided (freshCoord_free n) (paperDP_hworld 𝗜𝚺₁ n)

/-- Every segment table from day `2` on prices `freshCoord` strictly inside `(0, 1)`.
Source: mandate § 2 (N+: "a day-`1` undecided sentence priced strictly inside")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem segmentPrice_freshCoord_interior {n : ℕ} (hn : 2 ≤ n) :
    0 < segmentPrice n freshCoord ∧ segmentPrice n freshCoord < 1 := by
  rcases segmentPrice_trichotomy n (freshCoord_mem_smallSet hn) with h | h | h
  · obtain ⟨-, v, hv, hvn⟩ := freshCoord_undecided n
    exact absurd (h v hv) hvn
  · obtain ⟨⟨v, hv, hvy⟩, -⟩ := freshCoord_undecided n
    exact absurd hvy (h v hv)
  · exact h

/-- **N+ for K7b** — on every segment day `n` with `2 ≤ n < H` the spliced inductor prices the
undecided coordinate `freshCoord` strictly inside `(0, 1)`: the non-dogmatism clause is exercised
on a sentence the stage leaves open, not on a decided one.
Source: mandate § 2 (N+)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem splice_freshCoord_interior {H n : ℕ} (hn : 2 ≤ n) (hnH : n < H) :
    0 < spliceHistory H segmentPrice n freshCoord ∧
      spliceHistory H segmentPrice n freshCoord < 1 := by
  rw [spliceHistory_eq_tbl_of_lt hnH (freshCoord_mem_smallSet hn)]
  obtain ⟨h0, h1⟩ := segmentPrice_freshCoord_interior hn
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

/-- **K7a+K7b packaged** (the 70 % milestone's sentence on a finite segment): at every horizon
`H > 4`, the splice of the segment tables is a logical inductor over `paperDP 𝗜𝚺₁` that is
small-sentence coherent and non-dogmatic on every day `< H`, prices the undecided `freshCoord`
strictly inside on every day in `[2, H)`, and differs from the LIA on day `4`.
Source: [[bli-program]] §5 (the 70 % milestone), §3.6 (vi); mandate § 1–2
Kind: N+
Fidelity: exact (for the small form of `D_PC`)
Hyps: (a) -/
theorem segment_package (H : ℕ) (hH : 4 < H) :
    IsLogicalInductor (spliceHistory H segmentPrice) (paperDP 𝗜𝚺₁) ∧
    D_PCsmall_on H (spliceHistory H segmentPrice) (paperDP 𝗜𝚺₁) ∧
    D_ND_on H (spliceHistory H segmentPrice) (paperDP 𝗜𝚺₁) ∧
    (∀ n, 2 ≤ n → n < H → 0 < spliceHistory H segmentPrice n freshCoord ∧
      spliceHistory H segmentPrice n freshCoord < 1) ∧
    ∃ φ ∈ smallSet 4, spliceHistory H segmentPrice 4 φ ≠ liaHistory (paperDP 𝗜𝚺₁) 4 φ :=
  ⟨spliceSegment_isLogicalInductor H, segment_D_PCsmall_on H, segment_D_ND_on H,
    fun _ hn hnH => splice_freshCoord_interior hn hnH, splice_ne_lia_day4 H hH⟩

/-! ## § 10 (b): the seam — the first day after the segment (continuation 2) -/

/-- **The seam at horizon `4`, every table**: the splice at horizon `4` is **not** small-sentence
coherent on day `4` — the first day after its segment, where it is the LIA
(`spliceHistory_eq_lia_of_ge`), which prices a small tautology at `0` on day `4`
(`exists_tautChain_offSupport_day4`, the numeral support bound) while every stage mixture prices
it `1` (`CoherentOnSmall.valid_one`). The mandate's "`X3`-style witness: the day after the
segment", in the small form (for the literal `D_PC` the first failure is day `0`,
`not_D_PC_on_splice`, so the seam is a small-form statement).
Source: mandate § 10 (b); `bli-exactness` X3 (analogue); findings F1
Kind: P
Fidelity: exact at `H = 4` (the only horizon with a numeral support bound in the run; a horizon-`H` seam for every `H ≥ 4` needs the all-`n ≥ 4` support gap)
Hyps: (a) -/
theorem seam_day4 (t : ℕ → Sentence → ℚ) :
    ¬ D_PCsmall_on 5 (spliceHistory 4 t) (paperDP 𝗜𝚺₁) := by
  intro h
  obtain ⟨k, hk, hoff⟩ := exists_tautChain_offSupport_day4 (paperDP 𝗜𝚺₁)
  have hsmall := tautChain_mem_smallSet hk
  have h1 : spliceHistory 4 t 4 (tautChain k) = 1 :=
    (h 4 (by norm_num)).valid_one hsmall (fun v => holds_tautChain v k)
  rw [spliceHistory_eq_lia_of_ge le_rfl, liaHistory_eq_quote_cast] at h1
  change (((liaStates (paperDP 𝗜𝚺₁) 4).quote (tautChain k) : ℚ) : ℝ) = 1 at h1
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ hoff] at h1
  norm_num at h1

/-- **The exact/asymptotic gap at the seam** (mandate § 10 (b)): the segment tables spliced at
horizon `4` carry small-sentence coherence on every day `< 4` and lose it on day `4` — the exact
package holds exactly up to the horizon and fails on the day after.
Source: mandate § 10 (b); [[bli-program]] §5
Kind: C
Fidelity: exact at `H = 4`
Hyps: (a) -/
theorem seam_package :
    D_PCsmall_on 4 (spliceHistory 4 segmentPrice) (paperDP 𝗜𝚺₁) ∧
      ¬ D_PCsmall_on 5 (spliceHistory 4 segmentPrice) (paperDP 𝗜𝚺₁) :=
  ⟨segment_D_PCsmall_on 4, seam_day4 _⟩

end Cleanroom.Bli.BliExactBase
