import Cleanroom.Bli.BliMeasure.Constraints
import Mathlib.Data.Rat.Encodable

/-!
# `bli-measure` · Introspective: the coherent-introspective inductor (target 9, statement only)

[[bli-program-construction]] §3.11's `OPEN` strengthening of B3 ("exact for the
coherent-introspective inductor — a market maker whose fixed point also respects the quote
atoms"), stated precisely over this package's objects and **not attempted**: a coherent base (a
`CoherentBase`, inexploitable by every e.c. trader — the `PCInductor` grade) whose day-`n` prices
of its **own** interval-quote atoms about its day-`m` prices (`n < m`) are exactly B3's day-`n`
mass on the day-`m` candidates whose value lies in the interval — so that the B2 superbelief is
exact over it. Route note (mandate): Soto's fixed-point obstruction (bli-soto-a-058 (ii)) — the
market maker would need the quote atoms' prices continuous in the state (`ctsInd`).

**The quote atoms are pinned** (repair round 2; audit r2 adversarial B1, fidelity N2 (b)).
Round 1's statement took the quote family as a parameter constrained only by a semantic clause
("every completed-theory world of `DP` holds `quoteAt m φ lo hi` iff `lo < 𝐐_m φ ≤ hi`"), which
the propositional constants `⊤`/`⊥` satisfy for every base (the audit's probe
`trivialQuoteAt_faithful`), so the statement did not pin the object; and the clause was relative
to the *base* process `DP`, which decides nothing about the base, so with genuine fresh atoms it
was unsatisfiable. The statement of record now has:

* `introQuote m φ lo hi` — **a fresh atom of record** (`bli-found`'s allocator, family `9`,
  day-first payload `Nat.pair m (encode (φ, lo, hi))`), injective in `(m, φ, lo, hi)`, never a
  state atom, never `⊤`/`⊥`;
* `IntroQuoteProcess DP DP' base` — **the adjoined quote process**: `DP' ⊇ DP` adds nothing but
  the base's own *true* quote literals (`introQuoteLit base`: the atom when `lo < 𝐐_m φ ≤ hi`,
  its negation otherwise), and eventually adds each — the shape in which bli-paper-038 lets a
  true decidable claim about a market enter the paper's process, and in which `bli-found`'s
  `bliDP` adjoins the state literals. The base is run over `DP'` (that is the fixed point: the
  base's prices decide which literals `DP'` carries, and `DP'` decides the base), and it is
  inexploitable over `DP'`. Round 1's semantic clause is now a *theorem* of this shape
  (`IntroQuoteProcess.holds_introQuote_iff`), so the new statement implies the old and not
  conversely.

The mandate's "with the quote atoms of `bli-found`'s quotation lane (`quoteAt`, as `D_NNU` takes
them)" is **deviated from** and disclosed: `bli-found`'s concrete `StateSentence.quoteAt T`
quotes the *paper* market's code through FAF's `RationalQuoteCode`, which an arbitrary (possibly
noncomputable) base has no code for; `D_NNU`'s abstract parameter is what round 1 took and what
B1 shows does not pin the object. Fresh atoms with the adjoined-process clause are the honest
rendering of "the base's own quote atoms" for an abstract base.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

/-! ## The quote atoms of record -/

/-- The fresh-atom family of the interval-quote atoms about a coherent base's own prices
(`bli-found`'s registry: families `8`–`15` are reserved; `8` is already taken, unregistered, by
`bli-extrapolation` and `bli-rvc-ui`, so this package takes `9` — API request, findings F11).
Source: [[bli-measure-mandate]] target 9; `bli-found` `Tags.lean` (family registry)
Kind: D
Fidelity: n/a -/
abbrev introQuoteFamily : ℕ := 9

/-- The tag of the quote atoms: `cleanroomBaseTag + introQuoteFamily`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev introQuoteTag : ℕ := cleanroomBaseTag + introQuoteFamily

/-- **The interval-quote atom** `⌜𝐐_m(φ) ∈ (lo, hi]⌝` about a coherent base's own day-`m` price
of `φ`: a fresh atom of family `introQuoteFamily` with day-first payload
`Nat.pair m (encode (φ, lo, hi))`. Its meaning is fixed by the adjoined process
(`IntroQuoteProcess`), not by any clause on worlds.
Source: [[bli-program-construction]] §3.11 (the quote atoms `⌜𝐐_m(φ) ∈ I⌝`); [[bli-measure-mandate]] target 9
Kind: D
Fidelity: variant: a fresh atom of record in place of `bli-found`'s paper-market `quoteAt T` (see the module docstring) -/
def introQuote (m : ℕ) (φ : Sentence) (lo hi : ℚ) : Sentence :=
  freshAtom introQuoteFamily (Nat.pair m (Encodable.encode (φ, lo, hi)))

/-- Distinct quotes are distinct atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma introQuote_inj {m m' : ℕ} {φ φ' : Sentence} {lo hi lo' hi' : ℚ}
    (h : introQuote m φ lo hi = introQuote m' φ' lo' hi') :
    m = m' ∧ φ = φ' ∧ lo = lo' ∧ hi = hi' := by
  unfold introQuote at h
  obtain ⟨-, hp⟩ := freshAtom_inj.mp h
  obtain ⟨hm, he⟩ := Nat.pair_eq_pair.mp hp
  have := Encodable.encode_injective he
  obtain ⟨rfl, rfl, rfl⟩ := this
  exact ⟨hm, rfl, rfl, rfl⟩

/-- A quote atom mentions no state atom (families `9` vs `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma introQuote_tagFree_stateTag (m : ℕ) (φ : Sentence) (lo hi : ℚ) :
    TagFreeSentence stateTag (introQuote m φ lo hi) :=
  freshAtom_tagFree_of_ne (by decide)

/-- A quote atom is never a state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma introQuote_ne_stateAtom (m : ℕ) (φ : Sentence) (lo hi : ℚ) (m' q : ℕ) :
    introQuote m φ lo hi ≠ stateAtom m' q :=
  freshAtom_ne_of_family_ne (by decide)

/-- A quote atom is an atom: never `⊤` (the audit's trivial family is excluded).
Source: audit r2 adversarial B1
Kind: L
Fidelity: n/a -/
lemma introQuote_ne_verum (m : ℕ) (φ : Sentence) (lo hi : ℚ) :
    introQuote m φ lo hi ≠ (⊤ : Sentence) := by
  intro h; cases h

/-- A quote atom is an atom: never `⊥`.
Source: audit r2 adversarial B1
Kind: L
Fidelity: n/a -/
lemma introQuote_ne_falsum (m : ℕ) (φ : Sentence) (lo hi : ℚ) :
    introQuote m φ lo hi ≠ (⊥ : Sentence) := by
  intro h; cases h

/-- The quote atom about day `m` reads day `m` (`atomDay`), as every fresh family of the run.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomDay_introQuote (m : ℕ) (φ : Sentence) (lo hi : ℚ) :
    ∀ a ∈ sentenceAtomCodes (introQuote m φ lo hi), atomDay a = m := by
  intro a ha
  rw [introQuote, sentenceAtomCodes_freshAtom, Finset.mem_singleton] at ha
  subst ha
  simp

/-! ## The adjoined quote process -/

/-- **The quote literal the base's own price makes true**: the atom `introQuote m φ lo hi` when
`lo < 𝐐_m φ ≤ hi`, its negation otherwise.
Source: [[bli-program-construction]] §3.11; bli-paper-038 (true decidable claims about the market enter the process)
Kind: D
Fidelity: exact -/
noncomputable def introQuoteLit {DP : DeductiveProcess} (base : CoherentBase DP) (m : ℕ)
    (φ : Sentence) (lo hi : ℚ) : Sentence :=
  if lo < base.Q m φ ∧ base.Q m φ ≤ hi then introQuote m φ lo hi else ∼introQuote m φ lo hi

/-- **The adjoined quote process**: `DP'` extends `DP`, adds nothing but the base's own true
quote literals, and eventually adds each of them. This is the shape in which `bli-found`'s
`bliDP` adjoins the state literals to the base process, applied to the base's quotes of its own
prices; with the base run over `DP'` it is the fixed point target 9 asks for.
Source: [[bli-program-construction]] §3.11; bli-paper-038; `bli-found` `bliDP` (the adjoining shape)
Kind: D
Fidelity: exact -/
def IntroQuoteProcess (DP DP' : DeductiveProcess) (base : CoherentBase DP') : Prop :=
  (∀ n, DP.D n ⊆ DP'.D n) ∧
  (∀ n, ∀ ψ ∈ DP'.D n, ψ ∈ DP.D n ∨ ∃ (m : ℕ) (φ : Sentence) (lo hi : ℚ),
    ψ = introQuoteLit base m φ lo hi) ∧
  (∀ (m : ℕ) (φ : Sentence) (lo hi : ℚ), ∃ N, ∀ n, N ≤ n → introQuoteLit base m φ lo hi ∈ DP'.D n)

/-- **Round 1's semantic clause is a theorem of the adjoined process**: every completed-theory
world of `DP'` holds the quote atom iff the base's price lies in the interval. So the statement
of record implies round 1's and not conversely (the trivial family `⊤`/`⊥` satisfied round 1's
clause, `introQuote_ne_verum`/`_ne_falsum` exclude it here).
Source: audit r2 adversarial B1 (the clause); [[bli-program-construction]] §3.11
Kind: L
Fidelity: exact
Hyps: (a) `h` -/
theorem IntroQuoteProcess.holds_introQuote_iff {DP DP' : DeductiveProcess}
    {base : CoherentBase DP'} (h : IntroQuoteProcess DP DP' base) (m : ℕ) (φ : Sentence)
    (lo hi : ℚ) (v : PCWorld) (hv : v.ConsistentWithTheory DP') :
    v.Holds (introQuote m φ lo hi) ↔ (lo < base.Q m φ ∧ base.Q m φ ≤ hi) := by
  obtain ⟨N, hN⟩ := h.2.2 m φ lo hi
  have hlit : v.Holds (introQuoteLit base m φ lo hi) :=
    hv.holds_of_mem_stage ⟨N, hN N le_rfl⟩
  unfold introQuoteLit at hlit
  split_ifs at hlit with hc
  · exact ⟨fun _ => hc, fun _ => hlit⟩
  · rw [PCWorld.holds_neg] at hlit
    exact ⟨fun hq => absurd hq hlit, fun hc' => absurd hc' hc⟩

/-- The adjoined process mentions no state atom when the base process does not, so B3 over it
is in the setting of this package's coherence headline (`b3History_coherentOn`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IntroQuoteProcess.tagFree_stateTag {DP DP' : DeductiveProcess}
    {base : CoherentBase DP'} (h : IntroQuoteProcess DP DP' base)
    (hfree : TagFreeProcess stateTag DP) : TagFreeProcess stateTag DP' := by
  intro k ψ hψ
  rcases h.2.1 k ψ hψ with hψ | ⟨m, φ, lo, hi, rfl⟩
  · exact hfree k ψ hψ
  · unfold introQuoteLit
    split_ifs
    · exact introQuote_tagFree_stateTag m φ lo hi
    · exact (introQuote_tagFree_stateTag m φ lo hi).neg

/-! ## The open statement -/

/-- **OPEN — the coherent-introspective inductor.** For a base process with a consistent world at
every stage, mentioning neither state atoms nor quote atoms, there are an adjoined quote process
`DP' ⊇ DP` (adding exactly the base's own true quote literals, each eventually), a coherent base
over `DP'` inexploitable by every e.c. trader over `DP'`, and a mesh, such that for `n < m` and
every `φ` within the day-`m` atom bound the base's day-`n` price of its own quote atom
`⌜𝐐_m(φ) ∈ (lo, hi]⌝` is B3's day-`n` mass on the day-`m` candidates `q` whose value of `φ`
lies in `(lo, hi]`: `∑_q 𝐏_n(⌜𝑸_m = q⌝)`. Not attempted (route note: Soto's fixed-point
obstruction, bli-soto-a-058 (ii), needs `ctsInd`).
Source: [[bli-program-construction]] §3.11 (`OPEN`; §3.5 is the coherent market maker it strengthens); [[bli-measure-mandate]] target 9
Kind: OPEN
Fidelity: variant: fresh quote atoms of record with the adjoined-process clause in place of the
mandate's `bli-found` quotation-lane parameter (module docstring); the summand is `𝐏_n(⌜𝑸_m = q⌝)`
and `φ` is within the day-`m` bound (repair round 1); the quote atoms and their deciding process
are pinned (repair round 2)
Hyps: (a) `hcons`; (a) `hfree` (B3's coherence setting); (a) `hfreeQ` (the quote atoms are fresh
for the base process — without it `DP' ⊇ DP` could not carry the true literals) -/
theorem coherentIntrospective_open (DP : DeductiveProcess)
    (_hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (_hfree : TagFreeProcess stateTag DP) (_hfreeQ : TagFreeProcess introQuoteTag DP) :
    ∃ (DP' : DeductiveProcess) (base : CoherentBase DP') (𝓜 : Mesh),
      IntroQuoteProcess DP DP' base ∧
      (∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (ratHistory base.Q) DP') ∧
      ∀ n m, n < m → ∀ (φ : Sentence), atomBound φ ≤ base.𝔅.B m → ∀ (lo hi : ℚ),
        (base.Q n (introQuote m φ lo hi) : ℝ) =
          ∑ q ∈ (wstates base.𝔅 𝓜 m).filter (fun q =>
              (lo : ℝ) < (b3StateSystem base 𝓜).val m q φ ∧ (b3StateSystem base 𝓜).val m q φ ≤ hi),
            b3History base 𝓜 n (stateAtom m q) := by
  sorry

end Cleanroom.Bli.BliMeasure
