import Cleanroom.Bli.BliFound.Size
import Cleanroom.Bli.BliFinite.Bridge
import Cleanroom.Bli.BliSuperbelief.Dogmatism
import Cleanroom.Bli.BliSuperbelief.CoherentGrid
import LogicalInduction.Construction.LIA
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-superbelief` · Paper: the FAF-side facts of E6/E7 at `liaStates`

**The only file of the package importing `Cleanroom.Bli.BliFound` (for `smallSet`),
`Construction.LIA` and `Construction.Paper.TheoremDP`.** Kept small on purpose.

* `smallIndex` — the BLI-area instance of `bli-finite`'s `SmallIndex` (`⟨smallSet, smallSet_mono⟩`).
* **E6(c)**, the FAF fact: a sentence off the day-`n` LIA state's support quotes `0`
  (`liaQuote_eq_zero_of_not_mem_support`, FAF's `quote_eq_zero_of_not_mem` verbatim), and the
  state's support is inside the trading firm's day-`n` strategy support
  (`liaStates_support_subset_firm`, the first conjunct of `MarketMakerAccepts` through
  `MarketMaker_accepts`), so a sentence off the firm's support quotes `0` too.
* **E6(d)**: on a **support-entry day** — `φ ∈ smallSet n`, `φ ∉ (liaStates DP n).support`, and the
  day-`(n+1)` quote above half a grid step — the realized day-`(n+1)` state is off the product face
  of the day-`n` table (`supportEntry_not_mem_faceProd`), hence null under every balanced
  superbelief on day `n` (`supportEntry_null`): conditioning on it is null. Conditional theorems
  over **every** `DP`, `n`, `φ`; the existence of such a day for `liaStates (paperDP 𝗜𝚺₁)` is
  `exists_supportEntry_day_paperDP`, **OPEN** (no finite-day LIA quote has been evaluated in FAF;
  `liaStates` is a `Nat.find` over the market maker's search).
* **E7(c)**: if `φ` and `∼φ` are both small on day `n` and both off the LIA state's support, the
  day-`n` actual table is incoherent (`lia_not_coherent_of_offSupport_pair`) and the coherent
  grid over it is infeasible — no balance solution (`lia_coherentGrid_infeasible`).

Nothing about the LIA is assumed: (c) is FAF's acceptance test; (d) composes it with
`Dogmatism.lean`. No repair (clamped `E1c`, interior market maker, `D_ND`) is proved or assumed
here — those are `bli-transfer` L5, `bli-coherent-mm` M2 and `bli-trajectory`'s.

Sources: bli-soto-a-034 (the support problem), bli-slides-018; [[bli-program]] §3.4 Dogmatism,
§3.5(ii), §3.10 rows E6/E7, §7 items 5, 11.
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFinite Cleanroom.Bli.BliFound

/-- **The BLI-area small-sentence index**: `bli-found`'s `smallSet` with its monotonicity, as an
instance of `bli-finite`'s parameter.
Source: [[bli-program]] §2.1; mandate design decision 1
Kind: D
Fidelity: exact -/
noncomputable def smallIndex : SmallIndex := ⟨smallSet, fun m => smallSet_mono (Nat.le_succ m)⟩

/-- Unfolding lemma for `smallIndex`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smallIndex_S (m : ℕ) : smallIndex.S m = smallSet m := rfl

/-! ## E6(c): the FAF fact -/

/-- **A sentence off the LIA state's support quotes `0`** — FAF's convention (bli-soto-a-034), as
`RationalBeliefState.quote_eq_zero_of_not_mem` at `liaStates DP n`; for every `DP`, `n`, `φ`.
Source: bli-soto-a-034; FAF `Construction/MarketMaker.lean` `quote_eq_zero_of_not_mem`
Kind: L
Fidelity: exact -/
theorem liaQuote_eq_zero_of_not_mem_support (DP : DeductiveProcess) (n : ℕ) {φ : Sentence}
    (h : φ ∉ (liaStates DP n).support) : liaQuote DP n φ = 0 :=
  (liaStates DP n).quote_eq_zero_of_not_mem h

/-- **The LIA state's support lies inside the trading firm's day-`n` strategy support**: the first
conjunct of `MarketMakerAccepts` (`MarketMaker_accepts`), after one unfolding of `liaStates`.
Source: FAF `Construction/MarketMaker.lean` `MarketMakerAccepts` (`B.support ⊆ T.support`),
`Construction/LIA.lean` `liaStates`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaStates_support_subset_firm (DP : DeductiveProcess) (n : ℕ) :
    (liaStates DP n).support ⊆
      ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i)).support := by
  rw [liaStates]
  exact (MarketMaker_accepts _ _ _ _).1

/-- A sentence off the firm's day-`n` strategy support quotes `0` on day `n`.
Source: bli-soto-a-034; FAF `MarketMakerAccepts`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem liaQuote_eq_zero_of_not_mem_firm_support (DP : DeductiveProcess) (n : ℕ) {φ : Sentence}
    (h : φ ∉ ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i)).support) :
    liaQuote DP n φ = 0 :=
  liaQuote_eq_zero_of_not_mem_support DP n fun h' => h (liaStates_support_subset_firm DP n h')

/-- The LIA's rational history reads the LIA quote — definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ofBeliefStates_liaStates (DP : DeductiveProcess) (n : ℕ) (φ : Sentence) :
    ofBeliefStates (liaStates DP) n φ = liaQuote DP n φ := rfl

/-! ## E6(d): support-entry days -/

/-- A day-`(n+1)` quote above half a grid step puts `φ` **into** the day-`(n+1)` support (a
sentence off the support quotes `0`): E6(d)'s hypothesis package is literally a support-entry
day — off the support on day `n`, on it on day `n+1`.
Source: none: infrastructure (audit r2 adversarial §3.4, probe `SupportEntryShape.lean`)
Kind: L
Fidelity: n/a -/
lemma supportEntry_mem_support_next (DP : DeductiveProcess) (𝓜 : Mesh) (n : ℕ) {φ : Sentence}
    (hnext : 1 / (2 * (𝓜.d (n + 1) : ℚ)) < liaQuote DP (n + 1) φ) :
    φ ∈ (liaStates DP (n + 1)).support := by
  by_contra hoff
  rw [liaQuote_eq_zero_of_not_mem_support DP (n + 1) hoff] at hnext
  have : (0 : ℚ) < 1 / (2 * (𝓜.d (n + 1) : ℚ)) := by
    have := 𝓜.d_pos (n + 1)
    positivity
  linarith

/-- **E6(d).** On a support-entry day of FAF's LIA — `φ` small on day `n`, off the day-`n` state's
support (so quoted `0`), with day-`(n+1)` quote above half a grid step `1/(2 d(n+1))` (so its
rounded price is positive) — the realized day-`(n+1)` state is **not** on the product face of the
day-`n` actual table. Conditional over every `DP`, `n`, `φ`; the three hypotheses are concrete
facts about one day. `hnext` forces `φ ∈ (liaStates DP (n+1)).support`
(`supportEntry_mem_support_next`), so the package is a support-entry day in the literal sense;
it is also load-bearing — with a zero day-`(n+1)` quote the face condition holds at `φ`
(`roundVal_zero`), so `hoff` alone does not give the conclusion (audit r2 adversarial §3.4).
Source: [[bli-program]] §3.4 Dogmatism ("FAF's LIA violates this whenever a sentence enters the
support"); bli-soto-a-034; bli-slides-018
Kind: C
Fidelity: exact (threshold `<`, not the mandate's `≤`: ties round down)
Hyps: (a) the three day facts; `𝓜.d_pos` -/
theorem supportEntry_not_mem_faceProd (DP : DeductiveProcess) (𝓜 : Mesh) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (hoff : φ ∉ (liaStates DP n).support)
    (hnext : 1 / (2 * (𝓜.d (n + 1) : ℚ)) < liaQuote DP (n + 1) φ) :
    actualState smallIndex 𝓜.d (ofBeliefStates (liaStates DP)) (n + 1) ∉
      faceProd smallIndex 𝓜.d n (actualTable smallIndex (ofBeliefStates (liaStates DP)) n) :=
  not_mem_faceProd_of_zero_moved (ofBeliefStates (liaStates DP)) n ⟨φ, hφ⟩
    (liaQuote_eq_zero_of_not_mem_support DP n hoff)
    ((roundVal_pos_iff_of_mem (𝓜.d_pos _) ((liaStates DP (n + 1)).quote_mem_Icc φ)).mpr hnext)

/-- **The realized state is null on a support-entry day** under every balanced superbelief on
day `n` (non-degenerate or not): T3/T4/`TB`-style conditioning on it divides by zero. The finding
is filed in `bli-superbelief-findings`; the repairs are other packages' targets.
Source: [[bli-program]] §3.4 Dogmatism, §7 item 5; bli-slides-018
Kind: C
Fidelity: exact
Hyps: (a) the three day facts; (a) `IsProb ∧ Balanced` at the day-`n` actual table -/
theorem supportEntry_null (DP : DeductiveProcess) (𝓜 : Mesh) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (hoff : φ ∉ (liaStates DP n).support)
    (hnext : 1 / (2 * (𝓜.d (n + 1) : ℚ)) < liaQuote DP (n + 1) φ)
    {F : Superbelief smallIndex (n + 1)} (hF : IsProb 𝓜.d F)
    (hb : Balanced 𝓜.d F (actualTable smallIndex (ofBeliefStates (liaStates DP)) n)) :
    F (actualState smallIndex 𝓜.d (ofBeliefStates (liaStates DP)) (n + 1)) = 0 :=
  null_of_not_mem_faceProd hF hb (supportEntry_not_mem_faceProd DP 𝓜 n hφ hoff hnext)

/-! ## E7(c): an off-support pair makes the coherent grid infeasible -/

/-- **E7(c).** If `φ` and `∼φ` are both small on day `n` and both off the LIA state's support,
the day-`n` actual table is not `CoherentOn · D B` for any `D`, `B`. Quantified over every `D`:
at an unsatisfiable `D` (e.g. `⊥ ∈ D`) `CoherentOn t D B` holds for no `t` at all
(`ConsistentWith` empties the world support), so there the conclusion is trivially true; the
content is at consistent `D` (audit r2 adversarial §3.5). Same for the three theorems below.
Source: [[bli-program]] §3.5(ii); bli-soto-a-034
Kind: C
Fidelity: exact
Hyps: (a) the four day facts -/
theorem lia_not_coherent_of_offSupport_pair (DP : DeductiveProcess) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (hnφ : ∼φ ∈ smallSet n) (h1 : φ ∉ (liaStates DP n).support)
    (h2 : ∼φ ∉ (liaStates DP n).support) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentOn (actualTable smallIndex (ofBeliefStates (liaStates DP)) n) D B :=
  not_coherent_of_offSupport_pair (𝒮 := smallIndex) hφ hnφ
    (liaQuote_eq_zero_of_not_mem_support DP n h1) (liaQuote_eq_zero_of_not_mem_support DP n h2) D B

/-- **The coherent grid is infeasible on such a day**: no balance solution over
`coherentGrid smallIndex 𝓜.d (n+1) D B` at the day-`n` actual table — the generated face is
empty. B1 must use the product grid (the program's resolution).
Source: [[bli-program]] §3.5(ii) ("infeasible on every day where `liaStates` is incoherent")
Kind: C
Fidelity: exact
Hyps: (a) the four day facts; `𝓜.d_pos` -/
theorem lia_coherentGrid_infeasible (DP : DeductiveProcess) (𝓜 : Mesh) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (hnφ : ∼φ ∈ smallSet n) (h1 : φ ∉ (liaStates DP n).support)
    (h2 : ∼φ ∉ (liaStates DP n).support) (D : Finset Sentence) (B : ℕ) :
    faceGen (coherentGrid smallIndex 𝓜.d (n + 1) D B)
      (actualTable smallIndex (ofBeliefStates (liaStates DP)) n) = ∅ :=
  faceGen_coherentGrid_eq_empty_of_not_coherent (𝓜.d_pos _)
    (lia_not_coherent_of_offSupport_pair DP n hφ hnφ h1 h2 D B)

/-- **E7(c), one-sided form.** If `φ` and `∼φ` are both small on day `n`, `φ` is off the LIA
state's support and `∼φ` is not quoted exactly `1`, the day-`n` actual table is not
`CoherentOn · D B` for any `D`, `B` — the program's "every day with an off-support `φ`" (the pair
form `lia_not_coherent_of_offSupport_pair` is the case `∼φ` off the support).
Source: [[bli-program]] §3.5(ii); bli-soto-a-034; audit r1 (fidelity §3.3)
Kind: C
Fidelity: stronger: one off-support sentence with `liaQuote (∼φ) ≠ 1` suffices
Hyps: (a) the four day facts -/
theorem lia_not_coherent_of_offSupport_neg_ne_one (DP : DeductiveProcess) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (hnφ : ∼φ ∈ smallSet n) (h1 : φ ∉ (liaStates DP n).support)
    (h2 : liaQuote DP n (∼φ) ≠ 1) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentOn (actualTable smallIndex (ofBeliefStates (liaStates DP)) n) D B :=
  not_coherent_of_zero_of_neg_ne_one (𝒮 := smallIndex) hφ hnφ
    (liaQuote_eq_zero_of_not_mem_support DP n h1) h2 D B

/-- **The coherent grid is infeasible on such a day, one-sided form**: an off-support `φ` whose
negation is not quoted exactly `1` empties the generated face over the coherent grid.
Source: [[bli-program]] §3.5(ii); audit r1 (fidelity §3.3)
Kind: C
Fidelity: stronger: as `lia_not_coherent_of_offSupport_neg_ne_one`
Hyps: (a) the four day facts; `𝓜.d_pos` -/
theorem lia_coherentGrid_infeasible_of_neg_ne_one (DP : DeductiveProcess) (𝓜 : Mesh) (n : ℕ)
    {φ : Sentence} (hφ : φ ∈ smallSet n) (hnφ : ∼φ ∈ smallSet n)
    (h1 : φ ∉ (liaStates DP n).support) (h2 : liaQuote DP n (∼φ) ≠ 1) (D : Finset Sentence)
    (B : ℕ) :
    faceGen (coherentGrid smallIndex 𝓜.d (n + 1) D B)
      (actualTable smallIndex (ofBeliefStates (liaStates DP)) n) = ∅ :=
  faceGen_coherentGrid_eq_empty_of_not_coherent (𝓜.d_pos _)
    (lia_not_coherent_of_offSupport_neg_ne_one DP n hφ hnφ h1 h2 D B)

/-! ## The concrete day: open -/

/-- **OPEN.** A support-entry day with a nonzero next-day quote exists for the paper's inductor
`liaStates (paperDP 𝗜𝚺₁)`: some `φ ∈ smallSet n` is off the day-`n` support and quoted positively
on day `n+1`. (With a mesh `𝓜` fine enough that `1/(2 d(n+1))` is below that quote, this is the
hypothesis package of `supportEntry_not_mem_faceProd` at a named day.) Not proved: `liaStates` is
a `Nat.find` over the market maker's candidate enumeration and no finite-day quote of the LIA
has been evaluated in FAF (`smallSet 0 = {⊥}` makes day `0 → 1` uninformative; `⊤ ∈ smallSet 1`
is the first candidate for day `1 → 2`). Listed in `bli-superbelief-open.txt`.
Source: [[bli-program]] §4 row E6 ("N+: a concrete `paperDP` day"); mandate E6(iii)
Kind: OPEN
Fidelity: exact
Hyps: (a) none -/
theorem exists_supportEntry_day_paperDP :
    ∃ (n : ℕ) (φ : Sentence), φ ∈ smallSet n ∧ φ ∉ (liaStates (paperDP 𝗜𝚺₁) n).support ∧
      0 < liaQuote (paperDP 𝗜𝚺₁) (n + 1) φ := by
  sorry

end Cleanroom.Bli.BliSuperbelief
