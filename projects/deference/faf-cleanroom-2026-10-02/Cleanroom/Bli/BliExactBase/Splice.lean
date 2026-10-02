import Cleanroom.Bli.BliFound.StateSentence
import Cleanroom.Bli.BliAssemble.SmallList
import LogicalInduction.Construction.Freeze.Oracle

/-!
# `bli-exact-base` — K7a: the finite-segment splice is a logical inductor over `paperDP 𝗜𝚺₁`

**Construction-facing module** (mandate § Memory): it imports FAF's `thm:ifp`
(`FreezeOracle.lic_iff_of_finiteSupport`, the proof name of `lic_iff_of_finiteSupportPerturbation`)
and the paper market program (`paperMarketComputation 𝗜𝚺₁`, through `bli-found`'s
`StateSentence`). The theorem files of the package import this module, not FAF's freeze kit.

**What is built.** Given a horizon `H` and any table `t : ℕ → Sentence → ℚ`, the *splice*
`spliceHistory H t` is FAF's LIA over `paperDP 𝗜𝚺₁` with the prices of the day-`n` small
sentences (`smallSet n`, `n < H`) replaced by `t n`. The replacement is at **finitely many
`(day, sentence)` pairs** — the support `segmentPatch H` — which is the hypothesis of FAF's
*corrected* `thm:ifp` (`FiniteSupportPerturbation`); the paper's own "finitely many days" form is
false (`not_overgeneral_ifp`) and is not what is used here.

**How the patch is computed.** The segment is presented as a finite association list
`segmentEntries H t` keyed by `(day, code)`, built from `bli-assemble`'s computable enumeration
`smallList n` of `smallSet n`; `spliceQuote H t` looks the key up (`lookupOr`) and falls through
to the paper market's own quote table `paperQuote 𝗜𝚺₁`. The list is a *fixed finite constant*
of the program, so the lookup is computable whatever `t` is (`computable_lookupOr`): the
tables are data exhibited by a choice (`Tables.lean`), never computed, and `ComputableMarket`
(a `Prop`) is proved from FAF's `ComputableMarket.ofComputableTable` with the paper market's
`quote_comp_computable` — the finite-list generalization of FAF's one-coordinate template
`LIAPerturbation.computableMarket_liaPerturbed`.

**The headline** `splice_isLogicalInductor`: for every `H` and every `t` with values in `[0,1]`
on the small sentences, `IsLogicalInductor (spliceHistory H t) (paperDP 𝗜𝚺₁)` — Kind `C`, every
hypothesis grade (a): FAF's `paperLIA`, FAF's `thm:ifp`, and the two certificates proved here.
No agreement between `t` and the LIA is required. Off the patch the splice **is** the LIA
(`spliceHistory_eq_lia_of_ge`, `spliceHistory_eq_lia_of_not_small`), on it the splice **is** the
table (`spliceHistory_eq_tbl_of_lt`).
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliAssemble

/-! ## Association-list lookup with fallthrough -/

/-- Lookup in a finite association list keyed by `(day, code)`, falling through to `f` when the
key is absent (first match wins).
Source: mandate § Definitions (`spliceQuote`: "lookup in `tbl` at `(n, c)`, else `liaQuote`")
Kind: D
Fidelity: exact -/
def lookupOr : List (ℕ × ℕ × ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
  | [], f, n, c => f n c
  | e :: l, f, n, c => if n = e.1 ∧ c = e.2.1 then e.2.2 else lookupOr l f n c

/-- A key matching no entry falls through.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lookupOr_eq_of_forall_ne {l : List (ℕ × ℕ × ℚ)} {f : ℕ → ℕ → ℚ} {n c : ℕ}
    (h : ∀ e ∈ l, ¬ (n = e.1 ∧ c = e.2.1)) : lookupOr l f n c = f n c := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [lookupOr, if_neg (h e (by simp))]
    exact ih fun e' he' => h e' (by simp [he'])

/-- With pairwise distinct keys, a listed entry is returned.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lookupOr_eq_of_mem {l : List (ℕ × ℕ × ℚ)} {f : ℕ → ℕ → ℚ} {n c : ℕ} {q : ℚ}
    (hnd : (l.map fun e => (e.1, e.2.1)).Nodup) (h : (n, c, q) ∈ l) : lookupOr l f n c = q := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 h with rfl | h'
    · simp [lookupOr]
    · have hne : ¬ (n = e.1 ∧ c = e.2.1) := by
        rintro ⟨rfl, rfl⟩
        exact hnd.1 (List.mem_map.2 ⟨(e.1, e.2.1, q), h', rfl⟩)
      rw [lookupOr, if_neg hne]
      exact ih hnd.2 h'

/-- A lookup over `[0,1]`-valued entries with a `[0,1]`-valued fallthrough lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lookupOr_mem_Icc {l : List (ℕ × ℕ × ℚ)} {f : ℕ → ℕ → ℚ} {n c : ℕ}
    (hl : ∀ e ∈ l, 0 ≤ e.2.2 ∧ e.2.2 ≤ 1) (hf : 0 ≤ f n c ∧ f n c ≤ 1) :
    0 ≤ lookupOr l f n c ∧ lookupOr l f n c ≤ 1 := by
  induction l with
  | nil => exact hf
  | cons e l ih =>
    rw [lookupOr]
    split_ifs
    · exact hl e (by simp)
    · exact ih fun e' he' => hl e' (by simp [he'])

/-- The two unpaired components of `z` are `(a, b)` iff `z = Nat.pair a b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unpair_eq_iff_eq_pair {z a b : ℕ} :
    (z.unpair.1 = a ∧ z.unpair.2 = b) ↔ z = Nat.pair a b := by
  constructor
  · rintro ⟨h1, h2⟩
    calc z = Nat.pair z.unpair.1 z.unpair.2 := (Nat.pair_unpair z).symm
      _ = Nat.pair a b := by rw [h1, h2]
  · rintro rfl
    simp [Nat.unpair_pair]

/-- **A fixed finite association list keeps a computable table computable**: the lookup is a
finite nest of equality tests against constants, whatever the entries' values are (they are
constants of the program). This is why the segment tables need no computability certificate.
Source: mandate § Definitions (`SegmentTables`: "a finite list keeps `spliceQuote` computable");
FAF `LIAPerturbation.computable_perturbedQuote` (the one-entry template)
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma computable_lookupOr (l : List (ℕ × ℕ × ℚ)) {f : ℕ → ℕ → ℚ}
    (hf : Computable fun z : ℕ => Encodable.encode (f z.unpair.1 z.unpair.2)) :
    Computable fun z : ℕ => Encodable.encode (lookupOr l f z.unpair.1 z.unpair.2) := by
  induction l with
  | nil => exact hf
  | cons e l ih =>
    have htest : Computable fun z : ℕ => decide (z = Nat.pair e.1 e.2.1) :=
      (Primrec.eq.comp Primrec.id (Primrec.const (Nat.pair e.1 e.2.1))).decide.to_comp
    refine (Computable.cond htest (Computable.const (Encodable.encode e.2.2)) ih).of_eq
      fun z => ?_
    by_cases hz : z = Nat.pair e.1 e.2.1
    · have hu : z.unpair.1 = e.1 ∧ z.unpair.2 = e.2.1 := unpair_eq_iff_eq_pair.2 hz
      simp [lookupOr, hz]
    · have hu : ¬ (z.unpair.1 = e.1 ∧ z.unpair.2 = e.2.1) :=
        fun h => hz (unpair_eq_iff_eq_pair.1 h)
      simp [lookupOr, hz, hu]

/-! ## The segment as a finite list -/

/-- **The segment entries**: for every day `n < H` and every day-`n` small sentence `φ` (enumerated
by `bli-assemble`'s `smallList n`), the entry `(n, ⌜φ⌝, t n φ)`. A finite list, keyed by
`(day, code)`, with pairwise distinct keys.
Source: mandate § Definitions (`SegmentTables`)
Kind: D
Fidelity: exact -/
def segmentEntries (H : ℕ) (t : ℕ → Sentence → ℚ) : List (ℕ × ℕ × ℚ) :=
  (List.range H).flatMap fun n => (smallList n).map fun φ => (n, Encodable.encode φ, t n φ)

/-- Membership in the segment entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_segmentEntries {H : ℕ} {t : ℕ → Sentence → ℚ} {e : ℕ × ℕ × ℚ} :
    e ∈ segmentEntries H t ↔
      ∃ n, n < H ∧ ∃ φ ∈ smallSet n, e = (n, Encodable.encode φ, t n φ) := by
  rw [segmentEntries, List.mem_flatMap]
  constructor
  · rintro ⟨n, hn, he⟩
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 he
    exact ⟨n, List.mem_range.1 hn, φ, mem_smallSet.2 (mem_smallList.1 hφ), rfl⟩
  · rintro ⟨n, hn, φ, hφ, rfl⟩
    exact ⟨n, List.mem_range.2 hn, List.mem_map.2 ⟨φ, mem_smallList.2 (mem_smallSet.1 hφ), rfl⟩⟩

/-- Every entry's day is below the horizon.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma day_lt_of_mem_segmentEntries {H : ℕ} {t : ℕ → Sentence → ℚ} {e : ℕ × ℕ × ℚ}
    (h : e ∈ segmentEntries H t) : e.1 < H := by
  obtain ⟨n, hn, φ, -, rfl⟩ := mem_segmentEntries.1 h
  exact hn

/-- The keys `(day, code)` of the segment entries are pairwise distinct (`smallList_nodup` within
a day, the day component across days).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentEntries_keys_nodup (H : ℕ) (t : ℕ → Sentence → ℚ) :
    ((segmentEntries H t).map fun e => (e.1, e.2.1)).Nodup := by
  rw [segmentEntries, List.map_flatMap, List.nodup_flatMap]
  refine ⟨fun n _ => ?_, ?_⟩
  · rw [List.map_map]
    refine (smallList_nodup n).map fun φ ψ h => ?_
    exact Encodable.encode_injective (by simpa using congrArg Prod.snd h)
  · refine List.pairwise_lt_range.imp fun {a b} hab => ?_
    intro x hxa hxb
    simp only [List.map_map, List.mem_map, Function.comp] at hxa hxb
    obtain ⟨φ, -, rfl⟩ := hxa
    obtain ⟨ψ, -, h⟩ := hxb
    have : b = a := by simpa using congrArg Prod.fst h
    omega

/-- Entries of a `[0,1]`-valued table are `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segmentEntries_inUnit {H : ℕ} {t : ℕ → Sentence → ℚ}
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) :
    ∀ e ∈ segmentEntries H t, 0 ≤ e.2.2 ∧ e.2.2 ≤ 1 := by
  intro e he
  obtain ⟨n, hn, φ, hφ, rfl⟩ := mem_segmentEntries.1 he
  exact ht n hn φ hφ

/-- **The support of the perturbation**: the finitely many `(day, sentence)` pairs
`{(n, φ) | n < H, φ ∈ smallSet n}`. This is the object FAF's corrected `thm:ifp` asks for —
finitely many *coordinates*, not finitely many days.
Source: mandate § Definitions (`segmentPatch`); FAF `FiniteSupportPerturbation`
Kind: D
Fidelity: exact -/
noncomputable def segmentPatch (H : ℕ) : Finset (ℕ × Sentence) :=
  (Finset.range H).biUnion fun n => (smallSet n).image fun φ => (n, φ)

/-- Membership in the patch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_segmentPatch {H n : ℕ} {φ : Sentence} :
    (n, φ) ∈ segmentPatch H ↔ n < H ∧ φ ∈ smallSet n := by
  rw [segmentPatch, Finset.mem_biUnion]
  constructor
  · rintro ⟨m, hm, h⟩
    obtain ⟨ψ, hψ, h'⟩ := Finset.mem_image.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    exact ⟨Finset.mem_range.1 hm, hψ⟩
  · rintro ⟨hn, hφ⟩
    exact ⟨n, Finset.mem_range.2 hn, Finset.mem_image.2 ⟨φ, hφ, rfl⟩⟩

/-! ## The splice -/

/-- **The exact rational table of the splice**: the segment entry at `(n, c)` if there is one, else
the paper market's own quote `paperQuote 𝗜𝚺₁ n c` (FAF's `paperMarketComputation`, whose cast is
`liaHistory (paperDP 𝗜𝚺₁)`). Lean-`noncomputable` because it reads the LIA; its *computability
in the paper's sense* is `splice_computableMarket`.
Source: mandate § Definitions (`spliceQuote`)
Kind: D
Fidelity: exact -/
noncomputable def spliceQuote (H : ℕ) (t : ℕ → Sentence → ℚ) (n c : ℕ) : ℚ :=
  lookupOr (segmentEntries H t) (paperQuote 𝗜𝚺₁) n c

/-- **The spliced market**: the real cast of `spliceQuote` at the sentence's code. Off
`segmentPatch H` it is `liaHistory (paperDP 𝗜𝚺₁)`; on it, the table `t`.
Source: mandate § Definitions (`spliceHistory`); [[bli-program]] §3.6 (vi) (K7)
Kind: D
Fidelity: exact -/
noncomputable def spliceHistory (H : ℕ) (t : ℕ → Sentence → ℚ) : History :=
  fun n φ => (spliceQuote H t n (Encodable.encode φ) : ℝ)

/-- The splice as a rational history (`bli-trajectory`'s `RatHistory`), for `bli-assemble`'s L2.
Source: mandate § 5 (K7e)
Kind: D
Fidelity: exact -/
noncomputable def spliceRat (H : ℕ) (t : ℕ → Sentence → ℚ) : ℕ → Sentence → ℚ :=
  fun n φ => spliceQuote H t n (Encodable.encode φ)

/-- `spliceHistory` is the cast of `spliceRat`, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceHistory_eq_cast (H : ℕ) (t : ℕ → Sentence → ℚ) (n : ℕ) (φ : Sentence) :
    spliceHistory H t n φ = (spliceRat H t n φ : ℝ) := rfl

/-- **Days `≥ H` are the LIA.**
Source: mandate § 1 (`spliceHistory_eq_lia_of_ge`)
Kind: L
Fidelity: exact -/
theorem spliceHistory_eq_lia_of_ge {H : ℕ} {t : ℕ → Sentence → ℚ} {n : ℕ} (hn : H ≤ n)
    (φ : Sentence) : spliceHistory H t n φ = liaHistory (paperDP 𝗜𝚺₁) n φ := by
  unfold spliceHistory spliceQuote
  rw [lookupOr_eq_of_forall_ne, ← paperQuote_eq_liaHistory]
  rintro e he ⟨h1, -⟩
  have := day_lt_of_mem_segmentEntries he
  omega

/-- **A sentence not small on day `n` is priced by the LIA** (on every day).
Source: mandate § 1
Kind: L
Fidelity: exact -/
theorem spliceHistory_eq_lia_of_not_small {H : ℕ} {t : ℕ → Sentence → ℚ} {n : ℕ} {φ : Sentence}
    (hφ : φ ∉ smallSet n) : spliceHistory H t n φ = liaHistory (paperDP 𝗜𝚺₁) n φ := by
  unfold spliceHistory spliceQuote
  rw [lookupOr_eq_of_forall_ne, ← paperQuote_eq_liaHistory]
  rintro e he ⟨h1, h2⟩
  obtain ⟨m, -, ψ, hψ, rfl⟩ := mem_segmentEntries.1 he
  simp only at h1 h2
  subst h1
  exact hφ (Encodable.encode_injective h2 ▸ hψ)

/-- **On a segment day the small sentences are priced by the table.**
Source: mandate § 1 (`spliceHistory_eq_tbl_of_lt`)
Kind: L
Fidelity: exact -/
theorem spliceHistory_eq_tbl_of_lt {H : ℕ} {t : ℕ → Sentence → ℚ} {n : ℕ} {φ : Sentence}
    (hn : n < H) (hφ : φ ∈ smallSet n) : spliceHistory H t n φ = (t n φ : ℝ) := by
  unfold spliceHistory spliceQuote
  rw [lookupOr_eq_of_mem (segmentEntries_keys_nodup H t)
    (mem_segmentEntries.2 ⟨n, hn, φ, hφ, rfl⟩)]

/-- Off the patch the splice is the LIA.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spliceHistory_eq_lia_of_not_mem_patch {H : ℕ} {t : ℕ → Sentence → ℚ} {n : ℕ}
    {φ : Sentence} (h : (n, φ) ∉ segmentPatch H) :
    spliceHistory H t n φ = liaHistory (paperDP 𝗜𝚺₁) n φ := by
  rw [mem_segmentPatch, not_and_or] at h
  rcases h with h | h
  · exact spliceHistory_eq_lia_of_ge (not_lt.1 h) φ
  · exact spliceHistory_eq_lia_of_not_small h

/-- **The splice is a finite-support perturbation of the LIA**: the two markets agree off the
finitely many `(day, sentence)` pairs of `segmentPatch H`.
Source: mandate § 1; FAF `FiniteSupportPerturbation` (`Properties/FinitePerturbations.lean:439`)
Kind: L
Fidelity: exact -/
theorem splice_finiteSupportPerturbation (H : ℕ) (t : ℕ → Sentence → ℚ) :
    FiniteSupportPerturbation (liaHistory (paperDP 𝗜𝚺₁)) (spliceHistory H t) :=
  ⟨segmentPatch H, fun _ _ h => (spliceHistory_eq_lia_of_not_mem_patch h).symm⟩

/-- **The splice's table is computable** in the paper's sense: the paper market's program along
the paired input (`quote_comp_computable`), patched by the finite list.
Source: mandate § 1; FAF `MarketComputation.quote_comp_computable`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceQuote_computable (H : ℕ) (t : ℕ → Sentence → ℚ) :
    Computable fun z : ℕ => Encodable.encode (spliceQuote H t z.unpair.1 z.unpair.2) := by
  unfold spliceQuote
  refine computable_lookupOr _ ?_
  have := (paperMarketComputation 𝗜𝚺₁).quote_comp_computable
    (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  exact Computable.encode.comp this

/-- **The spliced market is a computable market** (FAF's `def:market`): range in `[0,1]`, the exact
rational table `spliceQuote H t`, and a program for it.
Source: mandate § 1; FAF `ComputableMarket.ofComputableTable` (`Framework/Criterion.lean:1091`);
template `LIAPerturbation.computableMarket_liaPerturbed`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem splice_computableMarket (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) :
    ComputableMarket (spliceHistory H t) := by
  refine ComputableMarket.ofComputableTable (spliceQuote H t) ?_ (fun _ _ => rfl)
    (spliceQuote_computable H t)
  intro n φ
  have h := lookupOr_mem_Icc (f := paperQuote 𝗜𝚺₁) (segmentEntries_inUnit ht)
    (paperQuote_mem 𝗜𝚺₁ n φ) (c := Encodable.encode φ)
  show (0 : ℝ) ≤ ((lookupOr (segmentEntries H t) (paperQuote 𝗜𝚺₁) n (Encodable.encode φ) : ℚ) : ℝ) ∧
    ((lookupOr (segmentEntries H t) (paperQuote 𝗜𝚺₁) n (Encodable.encode φ) : ℚ) : ℝ) ≤ 1
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- **K7a — the spliced base is a logical inductor over `paperDP 𝗜𝚺₁`.** For every horizon `H` and
every table `t` with values in `[0,1]` on the small sentences, `spliceHistory H t` — FAF's LIA
with the day-`n` small sentences re-priced by `t n` on **finitely many `(day, sentence)` pairs**
(`segmentPatch H`, days `< H`) — satisfies the logical induction criterion over `paperDP 𝗜𝚺₁`.
By FAF's corrected `thm:ifp` (`lic_iff_of_finiteSupportPerturbation`, proof name
`FreezeOracle.lic_iff_of_finiteSupport`) from `paperLIA`: no hypothesis on the moved prices, no
agreement with the LIA. The paper's printed "finitely many days" form is false
(`not_overgeneral_ifp`) and is not used.
Source: [[bli-program]] §3.6 (vi) (K7), §4 row K7; mandate § 1 (judged item 1); FAF `thm:ifp`
(`API.lean:597`), `paperLIA` (`Construction/Paper/TheoremDP.lean:442`)
Kind: C
Fidelity: exact
Hyps: (a) `paperLIA`, `thm:ifp`, `splice_computableMarket`, `splice_finiteSupportPerturbation`;
`ht` is the `[0,1]` range clause of `def:market` -/
theorem splice_isLogicalInductor (H : ℕ) (t : ℕ → Sentence → ℚ)
    (ht : ∀ n < H, ∀ φ ∈ smallSet n, 0 ≤ t n φ ∧ t n φ ≤ 1) :
    IsLogicalInductor (spliceHistory H t) (paperDP 𝗜𝚺₁) :=
  (FreezeOracle.lic_iff_of_finiteSupport (liaHistory (paperDP 𝗜𝚺₁)) (spliceHistory H t)
    (paperDP 𝗜𝚺₁) (paperLIA 𝗜𝚺₁).marketComputable (splice_computableMarket H t ht)
    (splice_finiteSupportPerturbation H t)).mp (paperLIA 𝗜𝚺₁)

/-- The splice at horizon `0` is the LIA itself (every day is `≥ 0`): the trivial end of the
family, recorded so the segment statements are read at `H ≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem spliceHistory_zero (t : ℕ → Sentence → ℚ) :
    spliceHistory 0 t = liaHistory (paperDP 𝗜𝚺₁) := by
  funext n φ
  exact spliceHistory_eq_lia_of_ge (Nat.zero_le n) φ

end Cleanroom.Bli.BliExactBase
