import Cleanroom.Bli.BliFound.State

/-!
# `bli-found` · Constraints: the BLI constraint predicates as first-class `Prop`s (F7's objects)

**D5 / T6** of the mandate. Every predicate is a `Prop` over an abstract **state system**
(`StateSystem`: the written-out states a BLI may believe in, day by day, their price tables, and
the realized one), so that `bli-finite`'s tables, Roman's dot grid and the denominator grid are
*instantiations*, not re-definitions; and over FAF's `History` for the markets `Q` (the base
logical inductor) and `P` (the BLI).

Conventions, fixed here once:

* **Days go `n → n + 1`** (bli-slides-017's convention; bli-slides-001's `n − 1 → n` is the same
  predicate re-indexed). No `Nat` subtraction anywhere.
* **Product form everywhere.** Every conditional `P_n(φ | σ) = x` is written
  `P_n(φ ⋏ σ) = x · P_n(σ)`. FAF's `conditionalQuote` (junk value `1` at price `0`) appears in no
  predicate; division appears nowhere.
* **Flags** (program F7): each docstring names the flags it carries — `E1x`/`E1r` (exact vs
  rounded agreement), `E2x`/`E2i` (exact vs interval faith), `linked`/`unlinked` (whether the
  state sentence is B2's quotation-claim conjunction `StateSentence.stateSentence`, which the
  LIA's own process decides, or B1's fresh atom `stateAtom`), `productGrid`/`coherentGrid` (what
  `S.states` ranges over — a parameter here, never baked in). Consumers' `Hyps:` lines cite these
  names. **Every predicate in the main body conditions on B1's `stateAtom`** and so is
  `unlinked` by construction; the B2 state sentence is never a `stateAtom`
  (`Grid.stateSentence_ne_stateAtom`), so the `linked` variants are stated through the
  **σ-parametric forms** at the end of the file (`E2xσ`, `E2iσ`, `E3σ`, `E3finσ`, `E4σ`, `E5σ`,
  `TBσ`, `IsBLI_AppBσ`, `IsBLI_Romanσ`; repair round 2, audit r2 adversarial N1), which take the
  state-sentence family as a parameter and specialize to the main body at `σ := stateAtom`
  (`E2x_eq_E2xσ` etc.).
* **Scope of faith.** `E2x`/`E2i`/`E3` quantify `φ` over `Sminus m m` (the Notion reading of
  bli-soto-a-003: no information about market states on or after the *earliest* state's day);
  see findings F-2 for why the unrestricted reading is not well defined (the day-`m` table does
  not price a later day's state atom).
* `FS` (support = face) needs the face of a grid and is **not defined here** — `bli-superbelief`.

Sanity checks at the end: on a concrete two-state system with a constant market, `Sminus m m`
is nonempty, and `E2x`, `E4`, `E5` are *falsifiable* (they are not vacuous by a typing accident).

Sources: Appendix B (`main.tex:431–436`) via bli-paper-034–038; bli-slides-001, 017, 030, 048;
bli-soto-a-003; [[bli-program]] §2.3/§2.6; mandate D5.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional Finset

/-! ## The state system -/

/-- **The written-out states a BLI may believe in**, day by day, with their price tables and the
realized one. `val m q φ` is `Q̂[φ]` for the state with code `q`; `actual m` is the code of the
realized day-`m` state. Which codes `states m` ranges over — a rounded table set (`productGrid`),
a coherent grid (`coherentGrid`), Roman's dot grid — is the instantiation's choice.
Source: [[bli-program]] §2.3/§2.6; bli-paper-033; mandate D5
Kind: D
Fidelity: exact (abstract in the grid) -/
structure StateSystem where
  /-- The candidate state codes on day `m`. -/
  states : ℕ → Finset ℕ
  /-- The price the state with code `q` assigns to `φ` on day `m`. -/
  val : ℕ → ℕ → Sentence → ℝ
  /-- The realized state's code on day `m`. -/
  actual : ℕ → ℕ
  /-- The realized state is a candidate. -/
  actual_mem : ∀ m, actual m ∈ states m

namespace StateSystem

/-- The BLI's process over a base: the base with the state-learning process adjoined
(`State.bliDP`).
Source: [[bli-program]] §2.3; mandate D4/D5
Kind: D
Fidelity: exact -/
def process (S : StateSystem) (DP : DeductiveProcess) : DeductiveProcess :=
  bliDP DP S.states S.actual

end StateSystem

/-- The superbelief `P_n(⌜𝑸_{n+1} = q⌝)` ([[bli-program]] §2.6).
Source: [[bli-program]] §2.6
Kind: D
Fidelity: exact -/
def superbelief (P : History) (n q : ℕ) : ℝ := P n (stateAtom (n + 1) q)

/-! ## The constraints -/

/-- **E1x — exact small agreement** (flag `E1x`): `P_n φ = Q_n φ` for every day-`n` small `φ`.
Roman's constraint 1 (bli-slides-017, exact, no rounding); bli-slides-030 (i).
Source: bli-slides-017 (1); bli-slides-030 (i); mandate D5
Kind: D
Fidelity: exact -/
def E1x (Q P : History) : Prop := ∀ n φ, φ ∈ smallSet n → P n φ = Q n φ

/-- **E1r — rounded agreement** (flag `E1r`): `P_n φ` is the *written-out actual state's* price
`S.val n (S.actual n) φ` for every day-`n` small `φ` — how Appendix B's
`P_n(φ) := D_n(Q_n(φ))` reads without importing a rounding map (the rounded actual table *is*
the realized state).
Source: bli-paper-034 (`main.tex:431`); mandate D5
Kind: D
Fidelity: variant: the rounding `D_n` is carried by `S.actual`/`S.val`, not applied to `Q` -/
def E1r (S : StateSystem) (P : History) : Prop :=
  ∀ n φ, φ ∈ smallSet n → P n φ = S.val n (S.actual n) φ

/-- **E2x — exact faith in a written-out future state** (flag `E2x`), product form: for `n < m`,
every candidate `q ∈ S.states m`, and every `φ ∈ Sminus m m`,
`P_n(φ ⋏ ⌜𝑸_m = q⌝) = Q̂[φ] · P_n(⌜𝑸_m = q⌝)`. Constraint 2 of Appendix B; scope `Sminus m m`
(the Notion reading, bli-soto-a-003).
Source: bli-paper-035 (`main.tex:432`); bli-slides-017 (2); mandate D5
Kind: D
Fidelity: variant: product form (no `conditionalQuote`); scope `Sminus m m` -/
def E2x (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ φ ∈ Sminus m m,
    P n (φ ⋏ stateAtom m q) = S.val m q φ * P n (stateAtom m q)

/-- **E2i — interval faith** (flag `E2i`), product form with slack `ε m · P_n(⌜𝑸_m = q⌝)`:
`|P_n(φ ⋏ σ) − Q̂[φ] · P_n(σ)| ≤ ε m · P_n(σ)`.
Source: [[bli-program]] §2.6; mandate D5
Kind: D
Fidelity: variant: product form -/
def E2i (ε : ℕ → ℝ) (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ φ ∈ Sminus m m,
    |P n (φ ⋏ stateAtom m q) - S.val m q φ * P n (stateAtom m q)| ≤ ε m * P n (stateAtom m q)

/-- **E3 — latest state wins** (two states), product form: for `n < m < o`, candidates
`q₁ ∈ S.states m`, `q₂ ∈ S.states o`, and `φ ∈ Sminus m m`,
`P_n(φ ⋏ (σ_m ⋏ σ_o)) = Q̂₂[φ] · P_n(σ_m ⋏ σ_o)` where `Q̂₂` is the *later* state's table.
Source: bli-paper-036 (`main.tex:433`); bli-slides-017 (3); mandate D5
Kind: D
Fidelity: variant: product form; scope `Sminus m m` (the earlier day) -/
def E3 (S : StateSystem) (P : History) : Prop :=
  ∀ n m o, n < m → m < o → ∀ q₁ ∈ S.states m, ∀ q₂ ∈ S.states o, ∀ φ ∈ Sminus m m,
    P n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) =
      S.val o q₂ φ * P n (stateAtom m q₁ ⋏ stateAtom o q₂)

/-- The conjunction of the state atoms of a list of `(day, code)` pairs.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stateConj (l : List (ℕ × ℕ)) : Sentence :=
  sentenceConjunction (l.map fun x => stateAtom x.1 x.2)

/-- **E3fin — latest state wins** (finite conjunctions): for a nonempty list of `(day, code)`
pairs with strictly increasing days, all after `n` and all candidates, and `φ ∈ Sminus d d` for
the *earliest* day `d`, `P_n(φ ⋏ ⋀σ) = Q̂_last[φ] · P_n(⋀σ)`.
Source: bli-paper-036 ("similarly for longer conjunctions"); mandate D5
Kind: D
Fidelity: variant: product form -/
def E3fin (S : StateSystem) (P : History) : Prop :=
  ∀ n (l : List (ℕ × ℕ)) (hne : l ≠ []),
    (∀ x ∈ l, n < x.1 ∧ x.2 ∈ S.states x.1) → l.IsChain (fun x y => x.1 < y.1) →
    ∀ φ ∈ Sminus (l.head hne).1 (l.head hne).1,
      P n (φ ⋏ stateConj l) = S.val (l.getLast hne).1 (l.getLast hne).2 φ * P n (stateConj l)

/-- **E4 — balance** (Appendix B's constraint 4 with the *corrected* left-hand side, Known
issue 1): for every day-`n` small `φ`,
`P_n φ = ∑_{q ∈ S.states (n+1)} P_n(⌜𝑸_{n+1} = q⌝) · Q̂[φ]`. The scope `φ ∈ smallSet n` is
bli-slides-017 (4)'s; Appendix B's `Q ∈ 𝒟_n` needs `Q` to price `φ`, i.e. `φ` small on the
*state's* day (`smallSet (n+1)` here), so on Appendix B's reading this predicate quantifies over
fewer `φ` and is the weaker constraint (audit r1, fidelity §3.1). `IsBLI_AppB` inherits this.
Source: bli-paper-037 (`main.tex:434–435`); bli-slides-017 (4); mandate D5
Kind: D
Fidelity: exact to bli-slides-017 (re-indexed `n → n + 1`); weaker than Appendix B by the day of the scope -/
def E4 (S : StateSystem) (P : History) : Prop :=
  ∀ n φ, φ ∈ smallSet n →
    P n φ = ∑ q ∈ S.states (n + 1), P n (stateAtom (n + 1) q) * S.val (n + 1) q φ

/-- **E5 — partition**: the superbeliefs over the day-`(n+1)` candidates sum to `1`, and
distinct candidates are exclusive in product form (`P_n(σ_q ⋏ σ_{q'}) = 0`).
Source: bli-slides-017 (5); Appendix B's implicit partition; mandate D5
Kind: D
Fidelity: exact -/
def E5 (S : StateSystem) (P : History) : Prop :=
  ∀ n, (∑ q ∈ S.states (n + 1), P n (stateAtom (n + 1) q) = 1) ∧
    ∀ q₁ ∈ S.states (n + 1), ∀ q₂ ∈ S.states (n + 1), q₁ ≠ q₂ →
      P n (stateAtom (n + 1) q₁ ⋏ stateAtom (n + 1) q₂) = 0

/-- **LNK — the state entails its quotes, closed-interval form** (flag `linked`; **superseded by
`StateSentence.LNKcell`**, kept only so that the mandate's D5 name resolves). A *process fact*,
parametric in an interval-quote family `quoteAt m φ lo hi` ("`Q̂_m[φ] ∈ [lo, hi]`"): in every
completed-theory world of `DP`, the state atom of `(m, q)` forces every interval quote of `φ`
whose closed interval contains `S.val m q φ`. **Two defects, disclosed** (findings F-13; audit r1
fidelity B2, adversarial N2): (i) the antecedent hard-codes B1's fresh atom `stateAtom`, so the
predicate cannot even be applied to the B2 state sentence `StateSentence.stateSentence` (a
different `Sentence`); (ii) paired with the package's own quote family `StateSentence.quoteAt T`
it is **refutable for every state system** over `paperDP T`
(`Unlinked.lnk_quoteAt_refutable`): at `lo = hi` the interval quote is a propositional
contradiction and the fresh atom is free. With an arbitrary `quoteAt` it is vacuously satisfiable
(`quoteAt := fun _ _ _ _ => ⊤`). Dependents state linkage as `LNKcell`.
Source: [[bli-program]] §2.3/§2.6; mandate D5 (first pass's rendering)
Kind: D
Fidelity: variant: closed intervals, parametric in `quoteAt`; refutable at `quoteAt T` (flagged) -/
def LNK (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (S : StateSystem) (DP : DeductiveProcess) :
    Prop :=
  ∀ m, ∀ q ∈ S.states m, ∀ φ ∈ smallSet m, ∀ lo hi : ℚ,
    (lo : ℝ) ≤ S.val m q φ → S.val m q φ ≤ hi →
    ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (stateAtom m q) → v.Holds (quoteAt m φ lo hi)

/-- **COMP**: the market is computable (FAF's `ComputableMarket`).
Source: mandate D5
Kind: D
Fidelity: exact -/
abbrev COMP (P : History) : Prop := ComputableMarket P

/-- **LIC**: the market is a logical inductor over `DP` (FAF's `IsLogicalInductor`).
Source: mandate D5
Kind: D
Fidelity: exact -/
abbrev LIC (P : History) (DP : DeductiveProcess) : Prop := IsLogicalInductor P DP

/-- **TB — total Bayesian update**, product form, every sentence: `P_{n+1}(ψ) · P_n(σ) = P_n(ψ ⋏ σ)`
for `σ = ⌜𝑸_{n+1} = actual (n+1)⌝`.
Source: bli-slides-048; Appendix B (`main.tex:440`); mandate D5
Kind: D
Fidelity: variant: product form -/
def TB (S : StateSystem) (P : History) : Prop :=
  ∀ n ψ, P (n + 1) ψ * P n (stateAtom (n + 1) (S.actual (n + 1))) =
    P n (ψ ⋏ stateAtom (n + 1) (S.actual (n + 1)))

/-! ## σ-parametric forms: the same predicates over an abstract state-sentence family

Every predicate above conditions on B1's fresh atom `stateAtom m q`. The B2 state sentence
`StateSentence.stateSentence T round m q` is a different `Sentence` (`⊤` or a conjunction of
tag-`2` literals, never an atom: `Grid.stateSentence_ne_stateAtom`), so faith in, balance over
or a partition of B2 states was **unstatable** with the main body (audit r2 adversarial N1,
probe P1). The forms below take the state-sentence family `σ : ℕ → ℕ → Sentence` ("`𝑸_m = q`"
as whatever sentence the encoding uses) as a parameter and specialize to the main body at
`σ := stateAtom` by `rfl`. They are **additions** to the definitions of record (repair round 2),
not changes: every main-body predicate is untouched. -/

/-- **E2xσ — exact faith, σ-parametric.** `E2x` with the state sentence `σ m q` in place of
`stateAtom m q`; `E2x S P = E2xσ stateAtom S P`.
Source: mandate D5 (`E2x`); audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `E2x`, with the state-sentence family a parameter -/
def E2xσ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ φ ∈ Sminus m m,
    P n (φ ⋏ σ m q) = S.val m q φ * P n (σ m q)

/-- **E2iσ — interval faith, σ-parametric.**
Source: [[bli-program]] §2.6; audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `E2i`, with the state-sentence family a parameter -/
def E2iσ (σ : ℕ → ℕ → Sentence) (ε : ℕ → ℝ) (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ φ ∈ Sminus m m,
    |P n (φ ⋏ σ m q) - S.val m q φ * P n (σ m q)| ≤ ε m * P n (σ m q)

/-- **E3σ — latest state wins (two states), σ-parametric.**
Source: bli-paper-036; audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `E3`, with the state-sentence family a parameter -/
def E3σ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  ∀ n m o, n < m → m < o → ∀ q₁ ∈ S.states m, ∀ q₂ ∈ S.states o, ∀ φ ∈ Sminus m m,
    P n (φ ⋏ (σ m q₁ ⋏ σ o q₂)) = S.val o q₂ φ * P n (σ m q₁ ⋏ σ o q₂)

/-- The conjunction of the state sentences `σ` of a list of `(day, code)` pairs.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stateConjσ (σ : ℕ → ℕ → Sentence) (l : List (ℕ × ℕ)) : Sentence :=
  sentenceConjunction (l.map fun x => σ x.1 x.2)

/-- **E3finσ — latest state wins (finite conjunctions), σ-parametric.**
Source: bli-paper-036; audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `E3fin`, with the state-sentence family a parameter -/
def E3finσ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  ∀ n (l : List (ℕ × ℕ)) (hne : l ≠ []),
    (∀ x ∈ l, n < x.1 ∧ x.2 ∈ S.states x.1) → l.IsChain (fun x y => x.1 < y.1) →
    ∀ φ ∈ Sminus (l.head hne).1 (l.head hne).1,
      P n (φ ⋏ stateConjσ σ l) =
        S.val (l.getLast hne).1 (l.getLast hne).2 φ * P n (stateConjσ σ l)

/-- **E4σ — balance, σ-parametric.**
Source: bli-paper-037; audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `E4`, with the state-sentence family a parameter -/
def E4σ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  ∀ n φ, φ ∈ smallSet n →
    P n φ = ∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) * S.val (n + 1) q φ

/-- **E5σ — partition, σ-parametric.**
Source: bli-slides-017 (5); audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `E5`, with the state-sentence family a parameter -/
def E5σ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  ∀ n, (∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) = 1) ∧
    ∀ q₁ ∈ S.states (n + 1), ∀ q₂ ∈ S.states (n + 1), q₁ ≠ q₂ →
      P n (σ (n + 1) q₁ ⋏ σ (n + 1) q₂) = 0

/-- **TBσ — total Bayesian update, σ-parametric.**
Source: bli-slides-048; audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `TB`, with the state-sentence family a parameter -/
def TBσ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  ∀ n ψ, P (n + 1) ψ * P n (σ (n + 1) (S.actual (n + 1))) =
    P n (ψ ⋏ σ (n + 1) (S.actual (n + 1)))

/-- **The main body is the `σ := stateAtom` instance**, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E2x_eq_E2xσ (S : StateSystem) (P : History) : E2x S P = E2xσ stateAtom S P := rfl

/-- `E2i_eq_E2iσ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E2i_eq_E2iσ (ε : ℕ → ℝ) (S : StateSystem) (P : History) :
    E2i ε S P = E2iσ stateAtom ε S P := rfl

/-- `E3_eq_E3σ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E3_eq_E3σ (S : StateSystem) (P : History) : E3 S P = E3σ stateAtom S P := rfl

/-- `E3fin_eq_E3finσ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E3fin_eq_E3finσ (S : StateSystem) (P : History) : E3fin S P = E3finσ stateAtom S P := rfl

/-- `E4_eq_E4σ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E4_eq_E4σ (S : StateSystem) (P : History) : E4 S P = E4σ stateAtom S P := rfl

/-- `E5_eq_E5σ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E5_eq_E5σ (S : StateSystem) (P : History) : E5 S P = E5σ stateAtom S P := rfl

/-- `TB_eq_TBσ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem TB_eq_TBσ (S : StateSystem) (P : History) : TB S P = TBσ stateAtom S P := rfl

/-! ## Coherence via FAF worlds -/

/-- **Coherence on a finite Boolean algebra, relative to a stage.** `p` is coherent on the
algebra generated by the atoms `A`, relative to the finite stage `D`, when it is a convex
combination of the `payout`s of finitely many `PCWorld`s consistent with `D`, on every sentence
whose atoms lie in `A`.
Source: bli-slides-003/011; [[bli-program]] §2.6; mandate D5
Kind: D
Fidelity: exact -/
def CoherentOn (D : Finset Sentence) (A : Finset ℕ) (p : Sentence → ℝ) : Prop :=
  ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ),
    (∀ i, (W i).ConsistentWith D) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    ∀ φ, sentenceAtomCodes φ ⊆ A → p φ = ∑ i, w i * (W i).payout φ

/-- The state atoms of days `≤ h`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stateAtomsUpTo (S : StateSystem) (h : ℕ) : Finset Sentence :=
  (Finset.range (h + 1)).biUnion fun m => (S.states m).image (stateAtom m)

/-- The atoms of the day-`n` small sentences and of the state atoms of days `≤ h n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pcpAtoms (S : StateSystem) (h : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (smallSet n ∪ stateAtomsUpTo S (h n)).biUnion sentenceAtomCodes

/-- **PCP h — finite coherence of `P_n`** on the Boolean algebra generated by `smallSet n` and
the state atoms of days `≤ h n`, relative to `DP.D n`.
Source: [[bli-program]] §2.6; mandate D5
Kind: D
Fidelity: exact -/
def PCP (h : ℕ → ℕ) (S : StateSystem) (DP : DeductiveProcess) (P : History) : Prop :=
  ∀ n, CoherentOn (DP.D n) (pcpAtoms S h n) (P n)

/-- **D_PC — the base is propositionally coherent on the small sentences**, relative to its
process (bli-slides-003; Appendix B's "propositionally coherent logical inductor").
Source: bli-paper-030/033; mandate D5
Kind: D
Fidelity: exact -/
def D_PC (Q : History) (DP : DeductiveProcess) : Prop :=
  ∀ n, CoherentOn (DP.D n) ((smallSet n).biUnion sentenceAtomCodes) (Q n)

/-- **D_ND — non-dogmatism of the base on the small sentences**: every day-`n` small `φ` is
decided true by the stage, decided false by it, or priced strictly inside `(0, 1)`.
Source: [[bli-program]] §2.6; mandate D5
Kind: D
Fidelity: exact -/
def D_ND (Q : History) (DP : DeductiveProcess) : Prop :=
  ∀ n, ∀ φ ∈ smallSet n,
    (∀ v : PCWorld, v.ConsistentWith (DP.D n) → v.Holds φ) ∨
    (∀ v : PCWorld, v.ConsistentWith (DP.D n) → ¬ v.Holds φ) ∨
    (0 < Q n φ ∧ Q n φ < 1)

/-- **D_NNU — exact finite-time no-net-expected-update** on the coordinates whose next-day
quotes are small: with `cells (n+1)` a finite set of intervals and `quoteAt (n+1) φ lo hi` the
quote "`Q_{n+1}(φ) ∈ [lo, hi]`", whenever every such quote is small on day `n`,
`|∑_I mid(I) · Q_n(quoteAt (n+1) φ I) − Q_n φ| ≤ ε (n+1)`.
Source: [[bli-program]] §2.6; mandate D5
Kind: D
Fidelity: variant: parametric in `quoteAt` and the cells -/
def D_NNU (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ)) (ε : ℕ → ℝ)
    (Q : History) : Prop :=
  ∀ n φ, φ ∈ smallSet n → (∀ I ∈ cells (n + 1), SmallOn n (quoteAt (n + 1) φ I.1 I.2)) →
    |∑ I ∈ cells (n + 1), (((I.1 + I.2) / 2 : ℚ) : ℝ) * Q n (quoteAt (n + 1) φ I.1 I.2) - Q n φ|
      ≤ ε (n + 1)

/-! ## The bundles -/

/-- **`S` writes out `Q`** — the tie between a state system and its base inductor that
Appendix B's bundle leaves implicit: the realized day-`m` table is the rounding `D m` of the base
market's day-`m` quotes on the small sentences, `S.val m (S.actual m) φ = D m (Q m φ)`
(bli-paper-034's "`D_n(𝑸_n(φ))`"). Neither `IsBLI_AppB` nor `E1r` mentions `Q`; "`P` is a BLI *of
`Q`*" is `IsBLI_AppB S P ∧ RoundsOf S Q D`.
Source: bli-paper-034; Appendix B (`main.tex:431`); audit r1 (fidelity §3.3)
Kind: D
Fidelity: exact -/
def RoundsOf (S : StateSystem) (Q : History) (D : ℕ → ℝ → ℝ) : Prop :=
  ∀ m, ∀ φ ∈ smallSet m, S.val m (S.actual m) φ = D m (Q m φ)

/-- **Appendix B's BLI**: `E1r ∧ E2x ∧ E3 ∧ E4 ∧ E5` (its own list, with the implicit partition
made explicit as `E5`). Flags: `E1r`, `E2x`, `unlinked`; grid-agnostic. **Mentions no base
inductor `Q`**: the tie is the instantiation of `S` (`RoundsOf S Q D`), which a dependent
conjoins. The bundle alone excludes nothing — the constant-`1` market on a one-state system
satisfies it (`isBLI_AppB_const_one`); `COMP`/`LIC`/coherence are separate by design. `E4`'s
scope is bli-slides-017's, weaker than Appendix B's by the day of the scope (see `E4`).
Source: Appendix B (`main.tex:431–436`); bli-slides-001; mandate D5
Kind: D
Fidelity: exact to the constraint list (modulo the conventions in the module docstring and `E4`'s scope) -/
def IsBLI_AppB (S : StateSystem) (P : History) : Prop :=
  E1r S P ∧ E2x S P ∧ E3 S P ∧ E4 S P ∧ E5 S P

/-- **Roman's BLI** (bli-slides-017): `E1x ∧ E2x ∧ E3 ∧ E4 ∧ E5` with *exact* constraint 1. The
grid is a `StateSystem` parameter and is **not** baked in (Known issue 3: Roman's `D` without
`0` is inconsistent with `E1x` at a price-`0` sentence — `bli-superbelief`'s theorem).
Flags: `E1x`, `E2x`, `unlinked`.
Source: bli-slides-017; mandate D5
Kind: D
Fidelity: exact -/
def IsBLI_Roman (S : StateSystem) (Q P : History) : Prop :=
  E1x Q P ∧ E2x S P ∧ E3 S P ∧ E4 S P ∧ E5 S P

/-- **Appendix B's BLI, σ-parametric**: `IsBLI_AppB` with the state-sentence family a parameter
(the `linked` bundle is this at `σ := StateSentence.stateSentence T round hround`);
`IsBLI_AppB S P = IsBLI_AppBσ stateAtom S P`.
Source: Appendix B (`main.tex:431–436`); audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `IsBLI_AppB`, with the state-sentence family a parameter -/
def IsBLI_AppBσ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  E1r S P ∧ E2xσ σ S P ∧ E3σ σ S P ∧ E4σ σ S P ∧ E5σ σ S P

/-- **Roman's BLI, σ-parametric.**
Source: bli-slides-017; audit r2 (adversarial N1)
Kind: D
Fidelity: variant: as `IsBLI_Roman`, with the state-sentence family a parameter -/
def IsBLI_Romanσ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (Q P : History) : Prop :=
  E1x Q P ∧ E2xσ σ S P ∧ E3σ σ S P ∧ E4σ σ S P ∧ E5σ σ S P

/-- `IsBLI_AppB_eq_IsBLI_AppBσ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsBLI_AppB_eq_IsBLI_AppBσ (S : StateSystem) (P : History) :
    IsBLI_AppB S P = IsBLI_AppBσ stateAtom S P := rfl

/-- `IsBLI_Roman_eq_IsBLI_Romanσ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsBLI_Roman_eq_IsBLI_Romanσ (S : StateSystem) (Q P : History) :
    IsBLI_Roman S Q P = IsBLI_Romanσ stateAtom S Q P := rfl

/-! ## Sanity checks (T6): the predicates are well-typed and not vacuous on a concrete system -/

/-- A two-state system: states `{0, 1}` every day, table `q ↦ (φ ↦ q)`, actual state `m % 2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def twoStateSystem : StateSystem where
  states _ := {0, 1}
  val _ q _ := (q : ℝ)
  actual m := m % 2
  actual_mem m := by
    have := Nat.mod_lt m (show 0 < 2 by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- The scope of faith is nonempty: `⊥ ∈ Sminus 1 1`. -/
example : (⊥ : Sentence) ∈ Sminus 1 1 := falsum_mem_Sminus 1 1

/-- `E2x` is falsifiable: the constant market `1/2` violates it at `n = 0`, `m = 1`, `q = 0`,
`φ = ⊥` (`1/2 ≠ 0 · 1/2`). -/
example : ¬ E2x twoStateSystem (fun _ _ => (1 / 2 : ℝ)) := by
  intro h
  have := h 0 1 (by norm_num) 0 (by simp [twoStateSystem]) ⊥ (falsum_mem_Sminus 1 1)
  simp [twoStateSystem] at this

/-- `E5` is falsifiable: the constant market `1/2` sums to `1` but is not exclusive. -/
example : ¬ E5 twoStateSystem (fun _ _ => (1 / 2 : ℝ)) := by
  intro h
  have := (h 0).2 0 (by simp [twoStateSystem]) 1 (by simp [twoStateSystem]) (by norm_num)
  norm_num at this

/-- `E4` is falsifiable: the market pricing `⊥` at `0` and everything else at `1` has, at
`n = 0`, `φ = ⊥`: left side `0`, right side `1 · 0 + 1 · 1 = 1`. (A *constant* market satisfies
E4 on this system, since the right side collapses to `P_n(σ_1)`.) -/
example : ¬ E4 twoStateSystem (fun _ φ => if φ = ⊥ then (0 : ℝ) else 1) := by
  intro h
  have := h 0 ⊥ (falsum_mem_smallSet 0)
  have hne : stateAtom 1 1 ≠ (⊥ : Sentence) := by
    unfold stateAtom freshAtom
    intro h
    cases h
  simp [twoStateSystem, hne] at this

/-- `E1x` holds trivially for `P = Q`, `E1r` for the market that copies the actual table. -/
example (Q : History) : E1x Q Q := fun _ _ _ => rfl

example : E1r twoStateSystem (fun n φ => twoStateSystem.val n (twoStateSystem.actual n) φ) :=
  fun _ _ _ => rfl

/-- One candidate a day, every value `1`.
Source: none: infrastructure; audit r1 (adversarial N5, probe P6)
Kind: D
Fidelity: n/a -/
def oneState : StateSystem where
  states _ := {0}
  val _ _ _ := 1
  actual _ := 0
  actual_mem _ := Finset.mem_singleton_self 0

/-- **The Appendix-B bundle admits the constant-`1` market** on `oneState`: `IsBLI_AppB` alone
excludes nothing (findings F-15). Recorded so that `bli-superbelief` does not rediscover it; the
degenerate solution is excluded only by `COMP`/`LIC`/coherence, which the bundle omits by design.
Source: audit r1 (adversarial N5, probe P6); findings F-12/F-15
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem isBLI_AppB_const_one : IsBLI_AppB oneState (fun _ _ => (1 : ℝ)) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp [oneState],
    fun _ _ _ _ _ _ _ _ _ _ _ => by simp [oneState], fun n φ _ => by simp [oneState],
    fun n => ⟨by simp [oneState], fun q₁ h₁ q₂ h₂ hne => ?_⟩⟩
  simp only [oneState, Finset.mem_singleton] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) hne

end Cleanroom.Bli.BliFound
