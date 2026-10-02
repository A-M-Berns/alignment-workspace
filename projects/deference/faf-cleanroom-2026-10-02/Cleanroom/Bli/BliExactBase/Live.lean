import Cleanroom.Bli.BliExactBase.Open
import Cleanroom.Bli.BliExactBase.QuoteLane

/-!
# `bli-exact-base` · Live: the non-vacuity guard of the OPEN rows — what it admits and what it
excludes (repair round 1)

Audit round 1 (both lenses, B1) showed that the quote-lane clause
`∃ C round, ReflectsRounded DP C round P ∧ D_NNUcell C smallCodes P` of the three OPEN rows
`worldMarket_exists`, `bundleMarket_LI_exists`, `weakening_exists` was satisfiable by **any**
market: `D_NNUcell` quantifies over the pinned coordinates — those whose day-`(n+1)` cell literals
are all small on day `n` — and `ReflectsRounded` constrains truth values only, so a reflecting
family whose literals are padded with a tautology chain of token size above `sizeBound (n+1)`
still reflects, is pinned nowhere, and makes `D_NNUcell` vacuous. Round 0's statement of
`bundleMarket_LI_exists` was therefore a theorem of FAF's LIA
(`bundleMarket_LI_exists_unguarded` below — the record of findings F21), and the other two rows
carried no self-trust content.

Repair round 1's guard is `Open.LiveLane C index`: every sentence is pinned from some day on, and
every day has a cell with representative `< 1`. Audit round 2 (fidelity B2, adversarial N1) then
showed that `ReflectsRounded ∧ LiveLane` still held at **every** history: `ReflectsRounded`
constrains truth values only, so the *certain lane* — `⊤` at the cell `P`'s rounded price
selects, `⊥` elsewhere — reflects every history and is live (`certFamily`,
`certFamily_reflects_live`), and under it `D_NNUcell` is "today's price is tomorrow's rounded
price" (`certFamily_identity`, `certFamily_dogmatic`), not self-trust. Repair round 2's guard is
`Open.OwnQuoteLane C round P`: the literals are the quotation atoms of a `BooleanQuoteCode` of
the market's own cell truth. This module shows the two guards are the right ones:

* **they are satisfiable by the package's own objects** — the splice's cell family at
  `halfRound`/`twoCells` is an own quote lane of the splice (`spliceCF_ownQuoteLane`), reflects
  the splice's rounded price (`spliceCF_reflectsRounded`) and is live on `smallCodes`
  (`spliceCF_live`; `quoteLane_clause_inhabited`: the lane conjuncts of the OPEN rows hold at
  every splice, so what is open in each row is the market, not the lane);
* **`OwnQuoteLane` implies reflection and stage freshness**: `ownQuoteLane_reflectsRounded`,
  `ownQuoteLane_literal_fresh`, `ownQuoteLane_stageFresh`, `ownQuoteLane_literal_undecided` (the
  adversarial audit's stage-undecidedness clause, derived);
* **under both guards `D_NNUcell` is pointwise self-trust at the market's own quotation atoms**
  (`D_NNUcell_own_pointwise`; `D_NNUcell_live_pointwise` is the liveness half, at the family's
  literals);
* **they exclude the padding and the certain lane**: `padFamily` (audit r1, incorporated)
  reflects, is pinned nowhere, satisfies `D_NNUcell` for every market
  (`quoteLane_clause_trivial`), and is not live (`padFamily_not_live`); `certFamily` (audit r2,
  incorporated) reflects and is live but is not an own quote lane
  (`certFamily_not_ownQuoteLane`, `not_ownQuoteLane_of_constant`).

Sources: audit r1 fidelity B1 / adversarial B1 (`run/wp/bli-exact-base/audit-r1-probes/`);
audit r2 fidelity B2 / adversarial N1 (`run/wp/bli-exact-base/audit-r2-probes/`);
mandate § 9, § 3 (a)–(c); [[bli-program]] §2.6, §3.8, §5.
-/

namespace Cleanroom.Bli.BliExactBase.Live

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB Cleanroom.Bli.BliAssemble
open Cleanroom.Bli.BliExactBase
open Cleanroom.Bli.BliLinkage (tautChain holds_tautChain tokenSize_tautChain)

/-! ## Every sentence is eventually small -/

/-- Every sentence is small from the day numbered by its own token size on (`k ≤ 2 ^ (2 ^ k)`).
Source: none: infrastructure (`SmallOn`, `sizeBound`)
Kind: L
Fidelity: n/a -/
theorem smallOn_eventually (φ : Sentence) : ∃ N, ∀ n ≥ N, SmallOn n φ := by
  refine ⟨tokenSize φ, fun n hn => SmallOn.mono hn ?_⟩
  show tokenSize φ ≤ 2 ^ (2 ^ tokenSize φ)
  have h1 : tokenSize φ ≤ 2 ^ tokenSize φ := Nat.lt_two_pow_self.le
  have h2 : 2 ^ tokenSize φ ≤ 2 ^ (2 ^ tokenSize φ) := Nat.lt_two_pow_self.le
  exact h1.trans h2

/-! ## The splice's own lane is live -/

/-- Real-valued `halfRound` — `0` below `1/2`, `1` at or above — the `round` of `ReflectsRounded`
at the splice, whose own rounding is on rationals.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def roundR (_m : ℕ) (x : ℝ) : ℕ := if x < 1 / 2 then 0 else 1

/-- `roundR` on a cast is `halfRound`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundR_cast (m : ℕ) (q : ℚ) : roundR m (q : ℝ) = halfRound m q := by
  unfold roundR halfRound
  have : ((q : ℝ) < 1 / 2) ↔ (q < 1 / 2) := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_lt
  simp only [this]

/-- **The splice's cell family reflects the rounding of the splice's own price**
(`ReflectsRounded` at `roundR`), for every horizon, table and representatives: the reflection
conjunct of the OPEN rows holds at every splice.
Source: mandate § 3 (a); audit r1 adversarial probe `spliceCF_reflects` (horizon `0`), generalized
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceCF_reflectsRounded (H : ℕ) (t : ℕ → Sentence → ℚ) (rep : ℕ → ℕ → ℚ) :
    ReflectsRounded (paperDP 𝗜𝚺₁)
      (spliceCF H t halfRound halfRound_computable twoCells halfRound_mem_twoCells rep)
      roundR (spliceHistory H t) := by
  intro m φ r v hv
  rw [spliceCF_literal, spliceCellSentence_reflected H t halfRound halfRound_computable m _ r v hv,
    ← spliceValue_eq_history H t m φ, roundR_cast]

/-- **The splice's cell family is live on the small codes**: every sentence is pinned from some
day on — it is eventually small, and its day-`(n+1)` cell literals of both cells are
machine-metered families in the day, hence eventually day-`n` small — and cell `0` has
representative `< 1`. The `pinned_eventually_splice` mechanism at an arbitrary coordinate.
Source: mandate § 3 (b); `QuoteLane.pinned_eventually_splice`
Kind: C
Fidelity: exact (`∃ N₀` per sentence, depending on the splice's quote code)
Hyps: (a) `hrep` (cell `0`'s representative below `1`, as at `rep01`) -/
theorem spliceCF_live (H : ℕ) (t : ℕ → Sentence → ℚ) (rep : ℕ → ℕ → ℚ)
    (hrep : ∀ m, rep m 0 < 1) :
    LiveLane (spliceCF H t halfRound halfRound_computable twoCells halfRound_mem_twoCells rep)
      smallCodes := by
  refine ⟨fun φ => ?_, fun m => ⟨0, by simp [spliceCF_cells, twoCells], hrep m⟩⟩
  obtain ⟨N, hN⟩ := smallOn_eventually φ
  obtain ⟨N₀, h₀⟩ := spliceCellSentence_eventually_small H t (Encodable.encode φ) 0
  obtain ⟨N₁, h₁⟩ := spliceCellSentence_eventually_small H t (Encodable.encode φ) 1
  refine ⟨max N (max N₀ N₁), fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨hnN, hn0, hn1⟩ := hn
  rw [mem_pinned]
  refine ⟨List.mem_map.2 ⟨φ, mem_smallList.2 (SmallOn.mono (Nat.le_succ n) (hN n hnN)), rfl⟩,
    fun r hr => ?_⟩
  simp only [spliceCF_cells, twoCells, Finset.mem_insert, Finset.mem_singleton] at hr
  rw [spliceCF_literal, sentenceOfCode_encode]
  rcases hr with rfl | rfl
  · exact h₀ n hn0
  · exact h₁ n hn1

/-! ## What the guard says -/

/-- **Under the liveness guard alone, `D_NNUcell` is pointwise at the family's literals**: for
every sentence `φ`, from some day on, `Q n φ = ∑_r rep r · Q n (lit_{n+1,φ,r})` — the identity
at the *family's* day-`(n+1)` literals for `φ`, which are then small. This is self-trust only
when those literals are the market's own quotation atoms (`OwnQuoteLane`): see
`D_NNUcell_own_pointwise`; at the certain lane it is dogmatism (`certFamily_dogmatic`; audit r2
fidelity N7).
Source: [[bli-program]] §3.6 (ii) (`D-NNU(Q)` at every coordinate, eventually)
Kind: L
Fidelity: exact (at the family's literals; self-trust needs `OwnQuoteLane`) -/
theorem D_NNUcell_live_pointwise {DP : DeductiveProcess} {C : CellFamilyT DP}
    {index : ℕ → List ℕ} {Q : History} (hL : LiveLane C index) (hD : D_NNUcell C index Q)
    (φ : Sentence) :
    ∃ N₀, ∀ n ≥ N₀,
      Q n φ = ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.literal (n + 1) φ r) := by
  obtain ⟨N₀, hN⟩ := hL.1 φ
  refine ⟨N₀, fun n hn => ?_⟩
  have := hD n _ (hN n hn)
  rwa [sentenceOfCode_encode] at this

/-! ## The own-quote-lane guard (repair round 2) -/

/-- **A lane of the market's own quotation atoms reflects the rounding of its own price**:
`OwnQuoteLane` implies `ReflectsRounded`, through FAF's `BooleanQuoteCode.reflected` at the
paper's quotation presentation. So round 1's reflection conjunct is a corollary of round 2's.
Source: audit r2 fidelity B2; FAF `BooleanQuoteCode.reflected`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem ownQuoteLane_reflectsRounded {C : CellFamilyT (paperDP 𝗜𝚺₁)} {round : ℕ → ℝ → ℕ}
    {P : History} (h : OwnQuoteLane C round P) : ReflectsRounded (paperDP 𝗜𝚺₁) C round P := by
  obtain ⟨T, code, hT, hlit⟩ := h
  intro m φ r v hv
  rw [hlit, code.reflected (paperQuotationPresentation 𝗜𝚺₁) _ v hv]
  exact hT m φ r

/-- **The day-`(n+1)` literals of an own quote lane are atoms no sentence of stage `n` mentions**
— the quotation atom's input is `⟨code, ⟨n+1, ⟨⌜φ⌝, r⟩⟩⟩ > n` (`quotationClaimCode_fresh_of_lt`).
This is the adversarial audit's stage-undecidedness clause, derived from the quotation guard
rather than assumed.
Source: audit r2 adversarial N1; `QuoteLane.quotationClaimCode_fresh_of_lt`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem ownQuoteLane_literal_fresh {C : CellFamilyT (paperDP 𝗜𝚺₁)} {round : ℕ → ℝ → ℕ}
    {P : History} (h : OwnQuoteLane C round P) (n : ℕ) (φ : Sentence) (r : ℕ) :
    ∀ ψ ∈ (paperDP 𝗜𝚺₁).D n,
      ∀ a ∈ sentenceAtomCodes (C.literal (n + 1) φ r), a ∉ sentenceAtomCodes ψ := by
  obtain ⟨T, code, -, hlit⟩ := h
  intro ψ hψ a ha
  rw [hlit, BooleanQuoteCode.sentence, quoteAtom, quotationClaimSentence, sentenceAtomCodes_atom,
    Finset.mem_singleton] at ha
  subst ha
  refine quotationClaimCode_fresh_of_lt 𝗜𝚺₁ ?_ ψ hψ
  calc n < n + 1 := Nat.lt_succ_self n
    _ ≤ Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) r) := Nat.left_le_pair _ _
    _ ≤ Nat.pair _ (Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) r)) := Nat.right_le_pair _ _

/-- An own quote lane is `StageFresh` on every segment and index (the mandate's K7c (c) form).
Source: mandate § 3 (c); audit r2 adversarial N1
Kind: L
Fidelity: n/a -/
theorem ownQuoteLane_stageFresh {C : CellFamilyT (paperDP 𝗜𝚺₁)} {round : ℕ → ℝ → ℕ}
    {P : History} (h : OwnQuoteLane C round P) (H N₀ : ℕ) (index : ℕ → List ℕ) :
    StageFresh H N₀ C index :=
  fun n _ _ c _ r _ ψ hψ a ha => ownQuoteLane_literal_fresh h n (sentenceOfCode c) r ψ hψ a ha

/-- **The day-`(n+1)` literals of an own quote lane are undecided at stage `n`**: some world
consistent with `(paperDP 𝗜𝚺₁).D n` holds the literal and some does not (`free_atom_undecided` at
a stage-fresh atom). The property the certain lane lacks: its literals are `⊤`/`⊥`, decided at
every stage.
Source: audit r2 adversarial N1 ("the clause must be semantic undecidedness"); `Mixing.free_atom_undecided`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem ownQuoteLane_literal_undecided {C : CellFamilyT (paperDP 𝗜𝚺₁)} {round : ℕ → ℝ → ℕ}
    {P : History} (h : OwnQuoteLane C round P) (n : ℕ) (φ : Sentence) (r : ℕ) :
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ v.Holds (C.literal (n + 1) φ r)) ∧
    (∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ ¬ v.Holds (C.literal (n + 1) φ r)) := by
  have hfree := ownQuoteLane_literal_fresh h n φ r
  obtain ⟨T, code, -, hlit⟩ := h
  rw [hlit, BooleanQuoteCode.sentence, quoteAtom, quotationClaimSentence] at hfree ⊢
  exact free_atom_undecided
    (fun ψ hψ => hfree ψ hψ _ (by rw [sentenceAtomCodes_atom]; exact Finset.mem_singleton_self _))
    (paperDP_hworld 𝗜𝚺₁ n)

/-- **The splice's own lane is an own quote lane**: `T := spliceCellTruth H t halfRound`,
`code := spliceCellQuote`, which on `⟨m, ⟨⌜φ⌝, r⟩⟩` says "`roundR m (spliceHistory H t m φ) = r`"
(`spliceValue_eq_history`, `roundR_cast`), and the literals are its quotation atoms by definition.
Source: mandate § 3 (a); audit r2 fidelity B2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem spliceCF_ownQuoteLane (H : ℕ) (t : ℕ → Sentence → ℚ) (rep : ℕ → ℕ → ℚ) :
    OwnQuoteLane (spliceCF H t halfRound halfRound_computable twoCells halfRound_mem_twoCells rep)
      roundR (spliceHistory H t) :=
  ⟨spliceCellTruth H t halfRound, spliceCellQuote H t halfRound halfRound_computable,
    fun m φ r => by
      simp only [spliceCellTruth, Nat.unpair_pair]
      rw [← spliceValue_eq_history H t m φ, roundR_cast],
    fun _ _ _ => rfl⟩

/-- **The lane conjuncts of the OPEN rows hold at every splice**: an own-quote, live cell family
exists for `spliceHistory H t`. So what each OPEN row leaves open is the market (`D_NNUcell`
together with the criterion and coherence), not the existence of a lane. (Unlike round 1's
`ReflectsRounded ∧ LiveLane`, which held at every history, `certFamily_reflects_live`, the clause
`OwnQuoteLane ∧ LiveLane` is not inhabited for free: a constant lane fails it,
`not_ownQuoteLane_of_constant`, and a non-computable market has no quote code of its cell truth.)
Source: audit r1 B1 ("add a non-degeneracy clause that the package's own objects satisfy"); audit r2 fidelity B2
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem quoteLane_clause_inhabited (H : ℕ) (t : ℕ → Sentence → ℚ) :
    ∃ (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
      OwnQuoteLane C round (spliceHistory H t) ∧ LiveLane C smallCodes :=
  ⟨_, roundR, spliceCF_ownQuoteLane H t (fun _ r => (r : ℚ)),
    spliceCF_live H t (fun _ r => (r : ℚ)) (fun _ => by simp)⟩

/-- **Under both guards, `D_NNUcell` is pointwise self-trust at the market's own quotation
atoms**: there is a quote code of `P`'s cell truth such that, for every sentence `φ`, from some
day on, `P n φ = ∑_r rep r · P n ⌜round_{n+1}(P_{n+1}(φ)) = r⌝` with the literal that code's
quotation atom — [[bli-program]] §3.6 (ii)'s `D-NNU(Q)` at every coordinate, eventually, over
the market's own `quote_{n+1,φ,I}` literals.
Source: [[bli-program]] §3.6 (ii), §3.8; audit r2 fidelity B2/N7
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem D_NNUcell_own_pointwise {C : CellFamilyT (paperDP 𝗜𝚺₁)} {round : ℕ → ℝ → ℕ}
    {P : History} (hO : OwnQuoteLane C round P) (hL : LiveLane C smallCodes)
    (hD : D_NNUcell C smallCodes P) (φ : Sentence) :
    ∃ (T : ℕ → Prop) (code : BooleanQuoteCode 𝗜𝚺₁ T),
      (∀ (m : ℕ) (ψ : Sentence) (r : ℕ),
        T (Nat.pair m (Nat.pair (Encodable.encode ψ) r)) ↔ round m (P m ψ) = r) ∧
      ∃ N₀, ∀ n ≥ N₀,
        P n φ = ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) *
          P n (code.sentence (Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) r))) := by
  obtain ⟨T, code, hT, hlit⟩ := hO
  refine ⟨T, code, hT, ?_⟩
  obtain ⟨N₀, hN⟩ := D_NNUcell_live_pointwise hL hD φ
  refine ⟨N₀, fun n hn => ?_⟩
  rw [hN n hn]
  exact Finset.sum_congr rfl fun r _ => by rw [hlit]

/-- **A lane with a constant literal is not an own quote lane**: a quotation atom is an atom,
not `⊤` or `⊥`.
Source: audit r2 fidelity B2 (probe `ConstLane.lane_clause_quote_free`), adversarial N1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_ownQuoteLane_of_constant {C : CellFamilyT (paperDP 𝗜𝚺₁)} {round : ℕ → ℝ → ℕ}
    {P : History}
    (hconst : ∃ (m : ℕ) (φ : Sentence) (r : ℕ),
      C.literal m φ r = (⊤ : Sentence) ∨ C.literal m φ r = (⊥ : Sentence)) :
    ¬ OwnQuoteLane C round P := by
  rintro ⟨T, code, -, hlit⟩
  obtain ⟨m, φ, r, h⟩ := hconst
  rw [hlit, BooleanQuoteCode.sentence, quoteAtom, quotationClaimSentence] at h
  rcases h with h | h <;>
    · have := congrArg sentenceAtomCodes h
      simp at this

/-! ## What the round-1 guard admitted: the certain lane (audit r2 adversarial N1 / fidelity B2,
incorporated) -/

/-- **The certain lane of a history `P`**: cell `r`'s literal is `⊤` when `roundR m (P m φ) = r`
and `⊥` otherwise; cells `{0, 1}`; representatives `0`, `1`. A `CellFamilyT` for every history,
with no quotation atom in it.
Source: audit r2 adversarial N1 (probe `AdvCertLane.certFamily`), fidelity B2 (probe `ConstLane.constLane`)
Kind: D
Fidelity: n/a (a counterexample family) -/
noncomputable def certFamily (P : History) : CellFamilyT (paperDP 𝗜𝚺₁) where
  literal m φ r := if roundR m (P m φ) = r then (⊤ : Sentence) else (⊥ : Sentence)
  cells := twoCells
  rep := fun _ r => (r : ℚ)
  excl := by
    intro m φ r r' hne v _ ⟨h, h'⟩
    by_cases h1 : roundR m (P m φ) = r
    · by_cases h2 : roundR m (P m φ) = r'
      · exact hne (h1.symm.trans h2)
      · rw [if_neg h2] at h'
        exact h'
    · rw [if_neg h1] at h
      exact h
  exh := by
    intro m φ v _
    refine ⟨roundR m (P m φ), ?_, ?_⟩
    · unfold roundR twoCells
      split_ifs <;> simp
    · rw [if_pos rfl]
      exact PCWorld.holds_top v

/-- The certain lane reflects the rounding of **every** history's own price.
Source: audit r2 adversarial N1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem certFamily_reflects (P : History) :
    ReflectsRounded (paperDP 𝗜𝚺₁) (certFamily P) roundR P := by
  intro m φ r v _
  show v.Holds (if roundR m (P m φ) = r then (⊤ : Sentence) else (⊥ : Sentence)) ↔ _
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => PCWorld.holds_top v⟩
  · exact ⟨fun hb => absurd hb (fun hb => hb), fun h' => absurd h' h⟩

/-- The certain lane is live on the small codes, for every history (`⊤`/`⊥` are eventually small,
cell `0` has representative `0`).
Source: audit r2 adversarial N1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem certFamily_live (P : History) : LiveLane (certFamily P) smallCodes := by
  refine ⟨fun φ => ?_, fun m => ⟨0, by simp [certFamily, twoCells],
    by show ((0 : ℕ) : ℚ) < 1; norm_num⟩⟩
  obtain ⟨N, hN⟩ := smallOn_eventually φ
  obtain ⟨N₁, hN₁⟩ := smallOn_eventually (⊤ : Sentence)
  obtain ⟨N₂, hN₂⟩ := smallOn_eventually (⊥ : Sentence)
  refine ⟨max N (max N₁ N₂), fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨hnN, hn1, hn2⟩ := hn
  rw [mem_pinned]
  refine ⟨List.mem_map.2 ⟨φ, mem_smallList.2 (SmallOn.mono (Nat.le_succ n) (hN n hnN)), rfl⟩,
    fun r _ => ?_⟩
  show SmallOn n (if roundR (n + 1) (P (n + 1) (sentenceOfCode (Encodable.encode φ))) = r
    then (⊤ : Sentence) else (⊥ : Sentence))
  split_ifs
  · exact hN₁ n hn1
  · exact hN₂ n hn2

/-- **Round 1's lane clause `ReflectsRounded ∧ LiveLane` held at every history** — the record of
why repair round 2 replaced `ReflectsRounded` by `OwnQuoteLane` in the three OPEN rows: the
clause restricted the market not at all.
Source: audit r2 adversarial N1 (`lane_conjuncts_for_every_history`), fidelity B2 (`lane_clause_quote_free`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem certFamily_reflects_live (P : History) :
    ∃ (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
      ReflectsRounded (paperDP 𝗜𝚺₁) C round P ∧ LiveLane C smallCodes :=
  ⟨certFamily P, roundR, certFamily_reflects P, certFamily_live P⟩

/-- **The certain lane is not an own quote lane** (round 2's guard excludes it).
Source: audit r2 fidelity B2
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem certFamily_not_ownQuoteLane (P : History) (round : ℕ → ℝ → ℕ) :
    ¬ OwnQuoteLane (certFamily P) round P :=
  not_ownQuoteLane_of_constant ⟨0, ⊤, 0, by
    show (if roundR 0 (P 0 ⊤) = 0 then (⊤ : Sentence) else (⊥ : Sentence)) = ⊤ ∨
      (if roundR 0 (P 0 ⊤) = 0 then (⊤ : Sentence) else (⊥ : Sentence)) = ⊥
    split_ifs <;> simp⟩

/-- Under the certain lane, where `P n ⊤ = 1` and `P n ⊥ = 0`, the `D_NNUcell` identity at `φ`
reads "today's price is tomorrow's rounded price".
Source: audit r2 adversarial N1 (`certFamily_identity`)
Kind: L
Fidelity: n/a -/
theorem certFamily_identity (P : History) (n : ℕ) (φ : Sentence)
    (htop : P n ⊤ = 1) (hbot : P n ⊥ = 0) :
    (P n φ = ∑ r ∈ (certFamily P).cells (n + 1),
        ((certFamily P).rep (n + 1) r : ℝ) * P n ((certFamily P).literal (n + 1) φ r)) ↔
      P n φ = (if P (n + 1) φ < 1 / 2 then 0 else 1) := by
  have hsum : ∑ r ∈ (certFamily P).cells (n + 1),
      ((certFamily P).rep (n + 1) r : ℝ) * P n ((certFamily P).literal (n + 1) φ r) =
      (if P (n + 1) φ < 1 / 2 then 0 else 1) := by
    show ∑ r ∈ twoCells (n + 1), ((r : ℚ) : ℝ) *
      P n (if roundR (n + 1) (P (n + 1) φ) = r then (⊤ : Sentence) else (⊥ : Sentence)) = _
    rw [twoCells, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    unfold roundR
    split_ifs <;> simp_all
  rw [hsum]

/-- **`D_NNUcell` with the certain lane is dogmatism**: at a market that prices `⊤` at `1` and
`⊥` at `0` from some day on, it forces every price into `{0, 1}` from some day on. So the lane
round 1 admitted did not make any OPEN row closable; it made the rows disjunctions over lanes
the program never meant (what round 2's `OwnQuoteLane` removes).
Source: audit r2 adversarial N1 (`certFamily_dogmatic`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem certFamily_dogmatic (P : History) {N : ℕ}
    (hcoh : ∀ n ≥ N, P n ⊤ = 1 ∧ P n ⊥ = 0)
    (hD : D_NNUcell (certFamily P) smallCodes P) (φ : Sentence) :
    ∃ N', ∀ n ≥ N', P n φ = 0 ∨ P n φ = 1 := by
  obtain ⟨N₀, hN₀⟩ := D_NNUcell_live_pointwise (certFamily_live P) hD φ
  refine ⟨max N N₀, fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  have h := (certFamily_identity P n φ (hcoh n hn.1).1 (hcoh n hn.1).2).1 (hN₀ n hn.2)
  rw [h]
  split_ifs <;> simp

/-! ## What the guard excludes: the padding (audit r1 adversarial B1, incorporated) -/

/-- **Pad every literal of a cell family with a tautology chain** of token size `> sizeBound m`:
reflection, exclusivity and exhaustiveness survive (a tautology conjunct changes no truth value),
and no padded day-`(n+1)` literal is day-`n` small.
Source: audit r1 adversarial B1 (probe `AdvOpenTrivial.padFamily`)
Kind: D
Fidelity: n/a (a counterexample family) -/
noncomputable def padFamily {DP : DeductiveProcess} (C : CellFamilyT DP) : CellFamilyT DP where
  literal m φ r := C.literal m φ r ⋏ tautChain (sizeBound m)
  cells := C.cells
  rep := C.rep
  excl := by
    intro m φ r r' hne v hv ⟨h, h'⟩
    exact C.excl m φ r r' hne v hv
      ⟨((PCWorld.holds_and _ _ _).1 h).1, ((PCWorld.holds_and _ _ _).1 h').1⟩
  exh := by
    intro m φ v hv
    obtain ⟨r, hr, h⟩ := C.exh m φ v hv
    exact ⟨r, hr, (PCWorld.holds_and _ _ _).2 ⟨h, holds_tautChain v _⟩⟩

/-- Padding preserves reflection.
Source: audit r1 adversarial B1
Kind: L
Fidelity: n/a -/
theorem padFamily_reflects {DP : DeductiveProcess} {C : CellFamilyT DP} {round : ℕ → ℝ → ℕ}
    {P : History} (h : ReflectsRounded DP C round P) :
    ReflectsRounded DP (padFamily C) round P := by
  intro m φ r v hv
  show v.Holds (C.literal m φ r ⋏ _) ↔ _
  rw [PCWorld.holds_and, ← h m φ r v hv]
  exact ⟨fun h => h.1, fun h => ⟨h, holds_tautChain v _⟩⟩

/-- A padded day-`(n+1)` literal is not small on day `n`.
Source: audit r1 adversarial B1
Kind: L
Fidelity: n/a -/
theorem padFamily_not_smallOn {DP : DeductiveProcess} (C : CellFamilyT DP) (n : ℕ) (φ : Sentence)
    (r : ℕ) : ¬ SmallOn n ((padFamily C).literal (n + 1) φ r) := by
  intro h
  unfold SmallOn at h
  change tokenSize (C.literal (n + 1) φ r ⋏ tautChain (sizeBound (n + 1))) ≤ sizeBound n at h
  rw [tokenSize_and, tokenSize_tautChain] at h
  have := sizeBound_mono (show n ≤ n + 1 by omega)
  omega

/-- The padded family's pinned set is empty on every day (cells nonempty).
Source: audit r1 adversarial B1
Kind: L
Fidelity: n/a -/
theorem padFamily_pinned_empty {DP : DeductiveProcess} (C : CellFamilyT DP)
    (hne : ∀ m, (C.cells m).Nonempty) (index : ℕ → List ℕ) (n : ℕ) :
    pinned (padFamily C) index n = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  obtain ⟨-, h⟩ := (mem_pinned (padFamily C) index n c).1 hc
  obtain ⟨r, hr⟩ := hne (n + 1)
  exact padFamily_not_smallOn C n _ r (h r hr)

/-- `D_NNUcell` holds vacuously for the padded family, for every market.
Source: audit r1 adversarial B1
Kind: L
Fidelity: n/a -/
theorem padFamily_D_NNUcell {DP : DeductiveProcess} (C : CellFamilyT DP)
    (hne : ∀ m, (C.cells m).Nonempty) (index : ℕ → List ℕ) (Q : History) :
    D_NNUcell (padFamily C) index Q := by
  intro n c hc
  rw [padFamily_pinned_empty C hne index n] at hc
  exact absurd hc List.not_mem_nil

/-- **Any reflecting family can be replaced by one for which the unguarded `D_NNUcell` clause is
empty** — the defect of round 0's OPEN rows (findings F21).
Source: audit r1 adversarial B1 (probe `quoteLane_clause_trivial`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem quoteLane_clause_trivial {DP : DeductiveProcess} (C : CellFamilyT DP)
    (hne : ∀ m, (C.cells m).Nonempty) (round : ℕ → ℝ → ℕ) (P : History)
    (h : ReflectsRounded DP C round P) :
    ∃ C' : CellFamilyT DP, ReflectsRounded DP C' round P ∧ D_NNUcell C' smallCodes P :=
  ⟨padFamily C, padFamily_reflects h, padFamily_D_NNUcell C hne smallCodes P⟩

/-- **The guard excludes the padding**: a padded family is not live (nothing is ever pinned).
Source: audit r1 B1 (the repair's check)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem padFamily_not_live {DP : DeductiveProcess} (C : CellFamilyT DP)
    (hne : ∀ m, (C.cells m).Nonempty) : ¬ LiveLane (padFamily C) smallCodes := by
  intro h
  obtain ⟨N₀, hN⟩ := h.1 ⊥
  have := hN N₀ le_rfl
  rw [padFamily_pinned_empty C hne smallCodes N₀] at this
  exact absurd this List.not_mem_nil

/-- **Round 0's unguarded route-(β) statement is a theorem of FAF's LIA**: `spliceHistory 0 t` is
the LIA (`spliceHistory_zero`), and its padded cell family reflects and is pinned nowhere. It is
*not* the bundle market as an LI; this is why the OPEN rows carry `LiveLane` (findings F21).
Source: audit r1 adversarial B1 (probe `bundleMarket_LI_exists_trivial`), fidelity B1 (probe
`bundleMarket_LI_exists_degenerate`)
Kind: T
Fidelity: n/a (round 0's statement, shown empty)
Hyps: (a) -/
theorem bundleMarket_LI_exists_unguarded :
    ∃ (P : History) (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
      ComputableMarket P ∧ IsLogicalInductor P (paperDP 𝗜𝚺₁) ∧
      ReflectsRounded (paperDP 𝗜𝚺₁) C round P ∧ D_NNUcell C smallCodes P := by
  obtain ⟨C', hC', hD⟩ := quoteLane_clause_trivial
    (spliceCF 0 (fun _ _ => 0) halfRound halfRound_computable twoCells halfRound_mem_twoCells
      (fun _ _ => 0))
    (fun m => ⟨0, by simp [spliceCF_cells, twoCells]⟩) roundR (spliceHistory 0 fun _ _ => 0)
    (spliceCF_reflectsRounded 0 _ _)
  exact ⟨spliceHistory 0 fun _ _ => 0, C', roundR,
    splice_computableMarket 0 _ (fun n hn => absurd hn (Nat.not_lt_zero n)),
    splice_isLogicalInductor 0 _ (fun n hn => absurd hn (Nat.not_lt_zero n)), hC', hD⟩

/-- The witness of `bundleMarket_LI_exists_unguarded` is the LIA itself.
Source: `Splice.spliceHistory_zero`
Kind: L
Fidelity: n/a -/
theorem unguarded_witness_is_lia :
    spliceHistory 0 (fun _ _ => (0 : ℚ)) = liaHistory (paperDP 𝗜𝚺₁) := spliceHistory_zero _

end Cleanroom.Bli.BliExactBase.Live
