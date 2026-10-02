import Cleanroom.Bli.BliFound.Constraints

/-!
# `bli-exactness` — definitions of record: the exact predicates and theory-respect

**FAF-free in the sense of the mandate** (no `Construction.*` import): everything here is stated
over FAF's `History`, `Sentence` and `PCWorld` (Framework level, through `bli-found`'s
`Constraints`), parametric in a quote family `quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence` exactly
as `bli-found`'s `D_NNU`/`LNK` are. The FAF files of this package instantiate `quoteAt` at
`bli-found`'s `quoteAt T` ("`lo < 𝑸_m(φ) ≤ hi`" about the paper market's own price).

* `ExactReflection quoteAt cells P` — slide 40's `ℙ_n(φ | ℙ_m(φ) = p) = p` at interval resolution,
  product form, midpoint representative, **over a cell family** `cells m` (a finite set of cells
  per quoted day, as `ExactNNUAt`; Soto's dyadic partition at one resolution). One definition,
  two readings: when `quoteAt` quotes `P`'s *own* price it is exact reflection; when it quotes a
  *base* `𝑸 ≠ P` it is `ExactSelfTrustX` (the exact form of `bli-found`'s `E2x` with quote cells
  for state atoms). The mandate's shape quantified over **every** rational cell
  (`ExactReflectionAllCells`, retained only to record its collapse: audit r1, both lenses — it
  forces mass `0` on every negative-midpoint cell and so has no nonnegative inhabitant with
  positive mass on a cell such as `(−3, 1]`, which every completed-theory world holds whenever
  `𝑸_m(φ) < 1`; `exactReflectionAllCells_zero_on_negative_mid`). STANDARDS §3 wins over the
  mandate here.
* `ExactReflectionInterval quoteAt cells P` / `ExactSelfTrustXInterval` — **the refuted object of
  record** (repair round 2): the *interval* form "the conditional of `φ` given the cell lies in the
  cell", `lo · P_n(χ_I) < P_n(φ ⋏ χ_I) ≤ hi · P_n(χ_I)` at every cell of positive mass; and
  `ExactNNUAtInterval`/`ExactNNUInterval`, `∑ lo_I · P_n(χ_I) ≤ P_n(φ) ≤ ∑ hi_I · P_n(χ_I)`. The
  midpoint identities imply them on non-degenerate cells (`ExactReflection.interval`,
  `ExactNNUAt.interval`), so a violation of the interval form is a violation of the midpoint form
  that is **not** the F5 artifact of the representative. X1 and X3 refute the interval forms; the
  midpoint forms are kept as the identities Soto's bundle market imposes by definition and as
  `bli-found`'s `D_NNU` body.
* The F5 artifact, isolated: under theory-respect a `𝒲`-**decided** sentence has conditional
  probability `0` or `1` on every cell (`decided_conditional`), so *midpoint*-exactness fails for
  it at every cell with interior midpoint — for `⊤` as much as for the liar
  (`decided_fails_midpoint`, `top_fails_midpoint`). The liar theorems of `Liar.lean` are
  therefore stated in the **interval** form, which `⊤` does *not* satisfy at a cell reaching `1`
  (`top_exact_interval`, the encoding check) and does satisfy at every cell with `hi < 1`
  (`top_fails_below_cell`).
* **The midpoint predicate over every sentence collapses at `⊤`** (audit r2 adversarial B2,
  adopted): a history coherent at `⊤` on a cell of the family with `mid ≠ 1` and positive mass on it
  does not satisfy `ExactReflection` (`coherentTop_forces_zero`, `coherentTop_not_exactReflection`).
  So on a family inside `[0, 1]` its inhabitants are `⊤`-incoherent or give `⊤`'s cells mass `0`;
  there is no N+ inhabitant in STANDARDS' sense. The interval form asks only that `⊤`'s cells with
  `hi < 1` carry no mass (`coherentTop_interval_below_cell`).
* `sotoBundleHistory quoteAt cells w` — Soto's `n = 1` bundle market with **both** of its clauses
  (PDF 20 p. 1): cell `I` of day `m` priced at `w I` on every earlier day, the conjunction
  `φ ⋏ χ_I` at `mid I · w I` (self-trust clause), every object-level sentence at the marginal
  `∑ mid I · w I` (Reflection clause). Under two injectivity facts about `quoteAt` (which
  `bli-found`'s `quoteAt T` has, `Perturb.lean`) it satisfies `ExactSelfTrustX` on the whole family
  **and** `ExactNNUAt` at every object-level sentence, with positive cell masses and object-level
  prices in `(0, 1)` (`sotoBundle_exactSelfTrustX`, `sotoBundle_exactNNUAt`), and the interval
  forms too. Graded **N−**: a by-definition valuation, `⊤`-incoherent as every positive-mass
  inhabitant of the midpoint predicate must be (`sotoBundle_top_incoherent`), pricing `⊤` below `1`
  (`sotoBundle_top_lt_one`, findings F15 on PDF 20). Repair round 1's one-clause `bundleHistory`
  (object-level prices `0`, violating `ExactNNUAt`) is withdrawn (audit r2 fidelity B1).
* `ExactNNUAt`/`ExactNNU` — the body of `bli-found`'s `D_NNU` at `ε = 0` **without** the
  `SmallOn` guard (Known issue 4: the guard is vacuous on day 1, see `Perturb.lean`).
* `ExactIntro quoteAt Q` — Soto's D-INTRO (PDF 07 p. 4) at the `(lo, hi]` convention.
* `EntailsIn`/`RespectsEntailment` — the *two* coherence facts the liar theorems use, relative
  to a class of worlds `𝒲` (instantiated at the completed-theory worlds of `paperDP T`). Not
  `bli-found`'s `CoherentOn` (Known issue 3: no finite perturbation of the LIA satisfies it).
  A finite linear combination of payouts of worlds in `𝒲` satisfies it for every pair
  (`mixture_respectsEntailment`), which is the generator of every witness in this package.

**Conventions (Known issue 6).** Cells are `(lo, hi]`: `quoteAt m φ lo hi` reads
"`lo < 𝑸_m(φ) ≤ hi`", so `ExactIntro` uses `lo < Q n φ ∧ Q n φ ≤ hi`. FAF's
`IntrospectionIntervalQuote.reflected` uses the open interval; no theorem in this package
depends on an end point (the one place it matters — the liar's threshold sitting exactly on a
cell boundary — is recorded in the findings, not used).
-/

namespace Cleanroom.Bli.BliExactness

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-! ## The midpoint representative -/

/-- The midpoint of a cell `(lo, hi]`, the representative value `bli-soto-b-025`'s bundle market
assigns to the cell (`(m + 0.5)/2^{k+1}`). Using the midpoint for "`ℙ_m(φ) = p`" makes exact
reflection "self-trust up to the cell width" — the inventory's flag, disclosed here once.
Source: [[bli-soto-b-inventory]] 025 (convention); slide 40 (`p`)
Kind: D
Fidelity: variant: midpoint representative in place of the point value `p` -/
def mid (I : ℚ × ℚ) : ℚ := (I.1 + I.2) / 2

/-- `mid` unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mid_mk (lo hi : ℚ) : mid (lo, hi) = (lo + hi) / 2 := rfl

/-! ## The exact predicates -/

/-- **Exact reflection at interval resolution, product form, over a cell family** (slide 40,
bullet 2, the condition "a natural idea is to universally enforce `ℙ_n(φ | ℙ_m(φ) = p) = p`"):
for all `n < m`, every sentence `φ` and every cell `I = (lo, hi]` **of the family `cells m`**,
`P_n(φ ⋏ ⌜lo < 𝑸_m(φ) ≤ hi⌝) = mid(I) · P_n(⌜lo < 𝑸_m(φ) ≤ hi⌝)`.
Written without `conditionalQuote` and without division. The family is the user's: Soto's bundle
market is the dyadic partition `(k/2^{r}, (k+1)/2^{r}]` of `(0, 1]` at one resolution
(bli-soto-b-025/027); for a family inside `[0, 1]` the midpoint lies in `[0, 1]` automatically.
When `quoteAt` quotes `P`'s **own** price (`bli-found`'s `quoteAt T` with
`P := liaHistory (paperDP T)`) this is reflection about oneself; read with a base `𝑸 ≠ P` it is
`ExactSelfTrustX` below. The midpoint makes it "self-trust up to the cell width" (see `mid`,
findings F5); the single-price form `ℙ_n(φ | 𝑸_m(φ) = p) = p` of the desiderata (D-ST-x) has no
faithful `quoteAt` rendering, since the point cell `(p, p]` is empty under `(lo, hi]`.
**Who inhabits it — and who cannot** (repair round 2, audit r2 adversarial B2). The zero history
(N−) and Soto's two-clause bundle market `sotoBundleHistory` (N−: by-definition valuation with
positive cell masses, `⊤`-incoherent). **No `⊤`-coherent history with positive mass on a cell about
`𝑸_m(⊤)` of midpoint `≠ 1` satisfies it** (`coherentTop_forces_zero`): the identity at `φ := ⊤`
reads `P(χ) = mid · P(χ)`. On any family inside `[0, 1]` every nonempty cell has `mid < 1`, so the
predicate over every sentence has no inhabitant that is both coherent at `⊤` and non-trivial
there; the completed-theory instance is `Liar.lean` `pointWorld_not_exactReflection`. This is
why the refuted object of record is the interval form `ExactReflectionInterval` below, and why the
midpoint form is kept only as the identity Soto's market imposes by definition. X1's witnesses are
witnesses of the *per-cell* failure and never of the predicate's satisfiable side.
Source: slide 40 bullet 2 ([[bli-slides-inventory]] 041); [[bli-program-desiderata]] D-ST-x;
[[bli-soto-b-inventory]] 024 (epistemic self-trust), 025 (the partition), 027
Kind: D
Fidelity: variant: interval resolution over a cell family, midpoint representative; product
form (the mandate's all-cells shape is `ExactReflectionAllCells`, see its docstring); quantified
over **every** sentence `φ`, where bli-soto-b-027 as transcribed says "all `φ` in the day-`m`
support" (a strengthening; `⊤` enters the LIA's support at some finite day, so the restriction
does not rescue the midpoint form from `coherentTop_forces_zero`) -/
def ExactReflection (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ))
    (P : History) : Prop :=
  ∀ n m, n < m → ∀ (φ : Sentence), ∀ I ∈ cells m,
    P n (φ ⋏ quoteAt m φ I.1 I.2) = ((mid I : ℚ) : ℝ) * P n (quoteAt m φ I.1 I.2)

/-- **Exact self-trust in the base's quote cells** (`D-ST-x` of the desiderata at interval
resolution; Soto's "epistemic self-trust from the beginning"; Abram 2025-01-25): the same identity
as `ExactReflection`, read with `quoteAt` quoting a *base* market `𝑸` rather than `P` itself. One
definition, two instantiations; the `abbrev` exists so the ledger can cite each reading.
Source: [[bli-soto-a-inventory]] 010; [[bli-soto-b-inventory]] 024, 027;
[[bli-journal-2025-01-25-epistemic-self-trust]]; [[bli-program-desiderata]] D-ST-x
Kind: D
Fidelity: variant: as `ExactReflection` -/
abbrev ExactSelfTrustX (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ))
    (P : History) : Prop :=
  ExactReflection quoteAt cells P

/-- **Exact reflection in the interval form — the refuted object of record** (repair round 2,
audit r2 adversarial B1 and B2 (iii) (α)): for all `n < m`, every sentence `φ` and every cell
`I = (lo, hi]` of the family **of positive mass**, the conditional of `φ` given the cell lies in the
cell, `lo · P_n(χ_I) < P_n(φ ⋏ χ_I) ≤ hi · P_n(χ_I)`. Written without division. This is the form
X1 refutes at the liar (`exact_reflection_fails_liar`) and X3 refutes on a logical inductor
(`x3_interval_violation`, `x3_not_exactReflectionInterval`). The midpoint identity implies it on
non-degenerate cells (`ExactReflection.interval`), so a violation of this form is a violation of
`ExactReflection` that is **not** the F5 artifact of the representative (`decided_fails_midpoint`).
Unlike the midpoint form it admits `⊤`-coherent inhabitants in principle: `⊤` is interval-exact at a
cell reaching `1` (`top_exact_interval`) and fails only at cells with `hi < 1`
(`top_fails_below_cell`), so a `⊤`-coherent inhabitant must give `⊤`'s below-`1` cells mass `0`
(`coherentTop_interval_below_cell`) — a consistent belief — where the midpoint form forces mass `0`
on *every* cell of midpoint `≠ 1` (`coherentTop_forces_zero`). Whether a coherent history
satisfies it for every `φ` at once, at `bli-found`'s `quoteAt T`, is open (report § Open).
Source: slide 40 bullet 2 (interval reading); audit r2 adversarial B1, B2 (iii) (α); repair r1's
X1 precedent
Kind: D
Fidelity: variant: interval resolution over a cell family, conditional-in-cell form with a
positive-mass guard; over every sentence `φ` (bli-soto-b-027: the day-`m` support) -/
def ExactReflectionInterval (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) (P : History) : Prop :=
  ∀ n m, n < m → ∀ (φ : Sentence), ∀ I ∈ cells m,
    0 < P n (quoteAt m φ I.1 I.2) →
      (I.1 : ℝ) * P n (quoteAt m φ I.1 I.2) < P n (φ ⋏ quoteAt m φ I.1 I.2) ∧
        P n (φ ⋏ quoteAt m φ I.1 I.2) ≤ (I.2 : ℝ) * P n (quoteAt m φ I.1 I.2)

/-- **Exact self-trust in the interval form**: `ExactReflectionInterval` read with `quoteAt`
quoting a base market `𝑸` (as `ExactSelfTrustX` is to `ExactReflection`).
Source: as `ExactSelfTrustX`; audit r2 adversarial B2 (iii) (α)
Kind: D
Fidelity: variant: as `ExactReflectionInterval` -/
abbrev ExactSelfTrustXInterval (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) (P : History) : Prop :=
  ExactReflectionInterval quoteAt cells P

/-- **Midpoint ⟹ interval** on non-degenerate cells (`lo < hi`): if `P_n(φ ⋏ χ_I) = mid I · P_n(χ_I)`
and `P_n(χ_I) > 0` then `lo · P_n(χ_I) < P_n(φ ⋏ χ_I) ≤ hi · P_n(χ_I)`. So the interval form is the
weaker predicate and its violation the stronger refutation.
Source: none: relation of record between the two definitions
Kind: L
Fidelity: n/a -/
theorem ExactReflection.interval {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} {P : History} (h : ExactReflection quoteAt cells P)
    (hcells : ∀ m, ∀ I ∈ cells m, I.1 < I.2) :
    ExactReflectionInterval quoteAt cells P := by
  intro n m hnm φ I hI hpos
  rw [h n m hnm φ I hI]
  have hlt : I.1 < I.2 := hcells m I hI
  have hlo : (I.1 : ℝ) < ((mid I : ℚ) : ℝ) := by
    have : I.1 < mid I := by simp only [mid]; linarith
    exact_mod_cast this
  have hhi : ((mid I : ℚ) : ℝ) ≤ (I.2 : ℝ) := by
    have : mid I ≤ I.2 := by simp only [mid]; linarith
    exact_mod_cast this
  exact ⟨mul_lt_mul_of_pos_right hlo hpos, mul_le_mul_of_nonneg_right hhi hpos.le⟩

/-- **The mandate's all-cells shape — retained only to record its collapse.** Quantifies over
*every* rational cell `(lo, hi)`, including cells outside `[0, 1]` and overlapping cells of
different widths, each with its own midpoint. Audit round 1 (both lenses) showed this is
over-strong in a way unrelated to the liar: `exactReflectionAllCells_zero_on_negative_mid` —
a nonnegative history satisfying it has mass `0` on every cell with negative midpoint, e.g.
`(−3, 1]`, which at `bli-found`'s `quoteAt T` is a sentence every completed-theory world holds.
No source states this shape (slide 40: point values; Soto: one dyadic partition). Not a
definition of record; no headline is stated over it.
Source: mandate § Definitions (the prescribed shape); audit r1 fidelity B2 / adversarial B1
Kind: D
Fidelity: variant: over-strong (every rational cell) — superseded by `ExactReflection` -/
def ExactReflectionAllCells (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (P : History) : Prop :=
  ∀ n m, n < m → ∀ (φ : Sentence) (lo hi : ℚ),
    P n (φ ⋏ quoteAt m φ lo hi) = ((mid (lo, hi) : ℚ) : ℝ) * P n (quoteAt m φ lo hi)

/-- **Why the all-cells shape was abandoned**: under `ExactReflectionAllCells`, a nonnegative
history gives every cell with negative midpoint mass `0` (the identity would make
`P_n(φ ⋏ χ) = mid · P_n(χ) < 0`). The adversarial auditor's probe, adopted.
Source: audit r1 adversarial B1 (probe `ExactReflectionForcesZero.lean`)
Kind: L
Fidelity: n/a -/
theorem exactReflectionAllCells_zero_on_negative_mid
    (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (P : History) (hP : ∀ n ψ, 0 ≤ P n ψ)
    (h : ExactReflectionAllCells quoteAt P) {n m : ℕ} (hnm : n < m) (φ : Sentence)
    {lo hi : ℚ} (hneg : mid (lo, hi) < 0) :
    P n (quoteAt m φ lo hi) = 0 := by
  have hid := h n m hnm φ lo hi
  have h0 := hP n (φ ⋏ quoteAt m φ lo hi)
  have h1 := hP n (quoteAt m φ lo hi)
  have hnegR : ((mid (lo, hi) : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
  by_contra hne
  have hpos : 0 < P n (quoteAt m φ lo hi) := lt_of_le_of_ne h1 (Ne.symm hne)
  have := mul_neg_of_neg_of_pos hnegR hpos
  linarith

/-- The all-cells shape implies the family-relative one for every family (so every refutation of
`ExactReflection` below is also a refutation of the mandate's shape).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ExactReflectionAllCells.toCells {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence} {P : History}
    (h : ExactReflectionAllCells quoteAt P) (cells : ℕ → Finset (ℚ × ℚ)) :
    ExactReflection quoteAt cells P :=
  fun n m hnm φ I _ => h n m hnm φ I.1 I.2

/-- **Exact no-net-update at one coordinate, unguarded**: with `cells (n+1)` a finite set of
cells, `∑_{I ∈ cells (n+1)} mid(I) · P_n(⌜𝑸_{n+1}(φ) ∈ I⌝) = P_n(φ)`. This is the body of
`bli-found`'s `D_NNU` at `ε = 0` **without** the `SmallOn n (quoteAt (n+1) φ I)` guard; the guard
is vacuous on day 1 (`Perturb.lean`, `not_smallOn_one_quoteAt`), which is why the X3 witness
violates this predicate and not `D_NNU` itself.
Source: [[bli-program]] §2.6 constraint 4; bli-paper-2-008 (a) exact form; `bli-found` `D_NNU`
Kind: D
Fidelity: variant: unguarded, `ε = 0` -/
def ExactNNUAt (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ))
    (P : History) (n : ℕ) (φ : Sentence) : Prop :=
  ∑ I ∈ cells (n + 1), ((mid I : ℚ) : ℝ) * P n (quoteAt (n + 1) φ I.1 I.2) = P n φ

/-- **Exact no-net-update everywhere**: `ExactNNUAt` at every day and sentence.
Source: as `ExactNNUAt`
Kind: D
Fidelity: variant: unguarded, `ε = 0` -/
def ExactNNU (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ))
    (P : History) : Prop :=
  ∀ n φ, ExactNNUAt quoteAt cells P n φ

/-- The unguarded exact predicate implies `bli-found`'s guarded `D_NNU` at `ε = 0` (the guard is
simply dropped; the absolute difference is `0`).
Source: none: infrastructure (relation of record between the two definitions)
Kind: L
Fidelity: n/a -/
theorem ExactNNU.d_nnu {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} {P : History} (h : ExactNNU quoteAt cells P) :
    D_NNU quoteAt cells (fun _ => 0) P := by
  intro n φ _ _
  have := h n φ
  unfold ExactNNUAt at this
  simp only [mid] at this
  rw [this, sub_self, abs_zero]

/-- **Exact no-net-update in the interval form, at one coordinate** (repair round 2, audit r2
adversarial B1): the day-`n` price lies between the lower and upper cell-weighted sums,
`∑_{I ∈ cells (n+1)} lo_I · P_n(⌜𝑸_{n+1}(φ) ∈ I⌝) ≤ P_n(φ) ≤ ∑_{I ∈ cells (n+1)} hi_I · P_n(⌜…⌝)`.
The midpoint form `ExactNNUAt` implies it for nonnegative masses on cells with `lo ≤ hi`
(`ExactNNUAt.interval`); X3 refutes this weaker form on a logical inductor
(`x3_not_exactNNUAtInterval`), so its midpoint refutation is not the artifact of the representative.
Source: [[bli-program]] §2.6 constraint 4 (interval reading); audit r2 adversarial B1
Kind: D
Fidelity: variant: interval (two-sided bound) form of `D_NNU`'s body, unguarded -/
def ExactNNUAtInterval (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ))
    (P : History) (n : ℕ) (φ : Sentence) : Prop :=
  ∑ I ∈ cells (n + 1), (I.1 : ℝ) * P n (quoteAt (n + 1) φ I.1 I.2) ≤ P n φ ∧
    P n φ ≤ ∑ I ∈ cells (n + 1), (I.2 : ℝ) * P n (quoteAt (n + 1) φ I.1 I.2)

/-- **Exact no-net-update in the interval form, everywhere.**
Source: as `ExactNNUAtInterval`
Kind: D
Fidelity: variant: as `ExactNNUAtInterval` -/
def ExactNNUInterval (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ))
    (P : History) : Prop :=
  ∀ n φ, ExactNNUAtInterval quoteAt cells P n φ

/-- **Midpoint ⟹ interval** for no-net-update: with nonnegative cell masses and `lo ≤ hi` on every
cell, `∑ lo_I · P(χ_I) ≤ ∑ mid_I · P(χ_I) = P(φ) ≤ ∑ hi_I · P(χ_I)`.
Source: none: relation of record between the two definitions
Kind: L
Fidelity: n/a -/
theorem ExactNNUAt.interval {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} {P : History} {n : ℕ} {φ : Sentence}
    (h : ExactNNUAt quoteAt cells P n φ) (hcells : ∀ I ∈ cells (n + 1), I.1 ≤ I.2)
    (hP : ∀ I ∈ cells (n + 1), 0 ≤ P n (quoteAt (n + 1) φ I.1 I.2)) :
    ExactNNUAtInterval quoteAt cells P n φ := by
  unfold ExactNNUAt at h
  unfold ExactNNUAtInterval
  rw [← h]
  constructor
  · refine Finset.sum_le_sum fun I hI => ?_
    have : (I.1 : ℝ) ≤ ((mid I : ℚ) : ℝ) := by
      have : I.1 ≤ mid I := by simp only [mid]; linarith [hcells I hI]
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this (hP I hI)
  · refine Finset.sum_le_sum fun I hI => ?_
    have : ((mid I : ℚ) : ℝ) ≤ (I.2 : ℝ) := by
      have : mid I ≤ I.2 := by simp only [mid]; linarith [hcells I hI]
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this (hP I hI)

/-- **Exact same-day introspection** (Soto, PDF 07 p. 4, "Introspection":
`P(C ∧ “P(⌜φ⌝) < p”) = P(C) · 𝟙(P(φ) < p)`, here the `C := ⊤` instance) at the `(lo, hi]` cell
convention of `quoteAt`: `Q_n(⌜lo < 𝑸_n(φ) ≤ hi⌝) = 𝟙(lo < Q_n(φ) ≤ hi)`. FAF's
`IntrospectionIntervalQuote.reflected` reads the open interval `a < x < b`; nothing in this package
depends on the end-point convention. **Used by no theorem of this package**: the refutation X2
proves (`lia_never_exact_on_liar`, `market_never_exact_on_liar`) is at the liar's *own atom*,
read semantically through `liar_reflected`; `¬ ExactIntro (quoteAt T) Q` would need, besides
theory-respect on the pair, a monotonicity fact `Q n L ≥ Q n (L ⋏ χ)`, and is not claimed
(report § X2). Note also that `quoteAt T` quotes the *paper market's* price, so
`ExactIntro (quoteAt T) Q` reads as introspection only at `Q := liaHistory (paperDP T)`.
Source: Soto PDF 07 p. 4 ([[bli-soto-a-inventory]] 058 (i)); PDF 04 p. 5 footnote 3 (036)
Kind: D
Fidelity: variant: `(lo, hi]` cells in place of the point form; `C := ⊤` -/
def ExactIntro (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (Q : History) : Prop :=
  ∀ (n : ℕ) (φ : Sentence) (lo hi : ℚ),
    Q n (quoteAt n φ lo hi) = if (lo : ℝ) < Q n φ ∧ Q n φ ≤ (hi : ℝ) then 1 else 0

/-! ## Theory-respect on the two sentences actually used -/

/-- **Entailment relative to a class of worlds**: every world in `𝒲` holding `ψ` holds `φ`.
At `𝒲 := TheoryWorlds DP` this is "`ψ ⊨ φ` over the completed theory".
Source: mandate § Definitions (theory-respect on a finite list)
Kind: D
Fidelity: exact -/
def EntailsIn (𝒲 : PCWorld → Prop) (ψ φ : Sentence) : Prop :=
  ∀ v : PCWorld, 𝒲 v → v.Holds ψ → v.Holds φ

/-- **The two coherence facts the liar theorems use**: `p` respects `ψ ⊨ φ` by
`p(φ ⋏ ψ) = p(ψ)`, and `ψ ⊨ ∼φ` by `p(φ ⋏ ψ) = 0`. This replaces `bli-found`'s `CoherentOn`
(Known issue 3), which quantifies over every sentence of an algebra and is satisfied by no finite
perturbation of the LIA; here only the pair `(φ, ψ)` actually used is constrained.
Source: mandate § Definitions; bli-slides-041 ("respects the provable equivalence
`L ↔ (ℙ_m(L) < ½)` in conjunction with each partition event")
Kind: D
Fidelity: exact -/
def RespectsEntailment (𝒲 : PCWorld → Prop) (p : Sentence → ℝ) (φ ψ : Sentence) : Prop :=
  (EntailsIn 𝒲 ψ φ → p (φ ⋏ ψ) = p ψ) ∧ (EntailsIn 𝒲 ψ (∼φ) → p (φ ⋏ ψ) = 0)

/-- The completed-theory worlds of a deductive process, as a class of worlds.
Source: FAF `PCWorld.ConsistentWithTheory`
Kind: D
Fidelity: exact -/
def TheoryWorlds (DP : DeductiveProcess) : PCWorld → Prop :=
  fun v => v.ConsistentWithTheory DP

/-- A single world's payout respects every entailment of a class it belongs to.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem payout_respectsEntailment {𝒲 : PCWorld → Prop} {v : PCWorld} (hv : 𝒲 v)
    (φ ψ : Sentence) : RespectsEntailment 𝒲 v.payout φ ψ := by
  constructor
  · intro h
    unfold PCWorld.payout
    by_cases hψ : v.Holds ψ
    · rw [if_pos hψ, if_pos ((PCWorld.holds_and v φ ψ).2 ⟨h v hv hψ, hψ⟩)]
    · rw [if_neg hψ, if_neg (fun hc => hψ ((PCWorld.holds_and v φ ψ).1 hc).2)]
  · intro h
    unfold PCWorld.payout
    rw [if_neg]
    intro hc
    obtain ⟨hφ, hψ⟩ := (PCWorld.holds_and v φ ψ).1 hc
    exact (PCWorld.holds_neg v φ).1 (h v hv hψ) hφ

/-- **The witness generator**: a finite linear combination of payouts of worlds in `𝒲` respects
every entailment of `𝒲`, for every pair of sentences — no sign or normalization condition on the
weights is needed, since both identities are linear. Every N+ witness of the package's liar
theorems is of this form (a one-world point mass).
Source: mandate § Definitions ("prove once that a finite convex combination of payouts …")
Kind: L
Fidelity: n/a -/
theorem mixture_respectsEntailment {𝒲 : PCWorld → Prop} {k : ℕ} (W : Fin k → PCWorld)
    (w : Fin k → ℝ) (hW : ∀ i, 𝒲 (W i)) (φ ψ : Sentence) :
    RespectsEntailment 𝒲 (fun χ => ∑ i, w i * (W i).payout χ) φ ψ := by
  constructor
  · intro h
    exact Finset.sum_congr rfl fun i _ => by
      rw [(payout_respectsEntailment (hW i) φ ψ).1 h]
  · intro h
    exact Finset.sum_eq_zero fun i _ => by
      rw [(payout_respectsEntailment (hW i) φ ψ).2 h, mul_zero]

/-- The constant history of one world's payouts (the point-mass day-`n` valuation every N+
witness below uses; constant in `n`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pointWorldHistory (v : PCWorld) : History := fun _ ψ => v.payout ψ

/-- `pointWorldHistory` unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma pointWorldHistory_apply (v : PCWorld) (n : ℕ) (ψ : Sentence) :
    pointWorldHistory v n ψ = v.payout ψ := rfl

/-! ## Decided sentences under theory-respect: the F5 artifact isolated -/

/-- **A decided sentence has conditional `0` or `1`**: if every world of `𝒲` holds `ψ`, or every
one refutes it, then any `p` respecting the entailments between `ψ` and `χ` has
`p(ψ ⋏ χ) = p(χ)` or `p(ψ ⋏ χ) = 0`. This is the whole mechanism behind the liar's
"straddling caveat is void" (`liar_decided`) — and it has nothing to do with self-reference.
Source: audit r1 (fidelity B1, adversarial B2): the honest positive statement
Kind: L
Fidelity: n/a -/
theorem decided_conditional (𝒲 : PCWorld → Prop) (ψ χ : Sentence) (p : Sentence → ℝ)
    (hdec : (∀ v : PCWorld, 𝒲 v → v.Holds ψ) ∨ (∀ v : PCWorld, 𝒲 v → ¬ v.Holds ψ))
    (hresp : RespectsEntailment 𝒲 p ψ χ) :
    p (ψ ⋏ χ) = p χ ∨ p (ψ ⋏ χ) = 0 := by
  rcases hdec with h | h
  · exact Or.inl (hresp.1 fun v hv _ => h v hv)
  · exact Or.inr (hresp.2 fun v hv _ => (PCWorld.holds_neg v ψ).2 (h v hv))

/-- **The F5 artifact**: *midpoint*-exactness fails for every `𝒲`-decided sentence at every cell
with interior midpoint and positive mass, under theory-respect alone — the conditional is `0` or
`1` (`decided_conditional`) and `0 < mid < 1`. The liar is one instance
(`Liar.lean` `liar_midpoint_fails_any_cell`); so is `⊤` (`top_fails_midpoint`). This is why the
liar headlines are stated in the interval form, not this one.
Source: findings F5; audit r1 fidelity B1 (probe `decided_fails_midpoint`, adopted)
Kind: L
Fidelity: n/a -/
theorem decided_fails_midpoint (𝒲 : PCWorld → Prop) (ψ χ : Sentence) (p : Sentence → ℝ)
    (hdec : (∀ v : PCWorld, 𝒲 v → v.Holds ψ) ∨ (∀ v : PCWorld, 𝒲 v → ¬ v.Holds ψ))
    {lo hi : ℚ} (hmid₀ : 0 < mid (lo, hi)) (hmid₁ : mid (lo, hi) < 1)
    (hresp : RespectsEntailment 𝒲 p ψ χ) (hpos : 0 < p χ) :
    p (ψ ⋏ χ) ≠ ((mid (lo, hi) : ℚ) : ℝ) * p χ := by
  have hmid₀R : (0 : ℝ) < ((mid (lo, hi) : ℚ) : ℝ) := by exact_mod_cast hmid₀
  have hmid₁R : ((mid (lo, hi) : ℚ) : ℝ) < 1 := by exact_mod_cast hmid₁
  rcases decided_conditional 𝒲 ψ χ p hdec hresp with h | h
  · rw [h]
    intro heq
    nlinarith [mul_pos hpos (sub_pos.2 hmid₁R)]
  · rw [h]
    intro heq
    have := mul_pos hmid₀R hpos
    linarith

/-- `⊤` fails midpoint-exactness at every interior-midpoint cell under theory-respect: the
statement shape of the former "FAF strengthening" of X1 (b), with `⊤` for the liar.
Source: audit r1 fidelity B1 (probe `top_fails_midpoint`, adopted)
Kind: L
Fidelity: n/a -/
theorem top_fails_midpoint (𝒲 : PCWorld → Prop) (χ : Sentence) (p : Sentence → ℝ)
    {lo hi : ℚ} (hmid₀ : 0 < mid (lo, hi)) (hmid₁ : mid (lo, hi) < 1)
    (hresp : RespectsEntailment 𝒲 p (⊤ : Sentence) χ) (hpos : 0 < p χ) :
    p ((⊤ : Sentence) ⋏ χ) ≠ ((mid (lo, hi) : ℚ) : ℝ) * p χ :=
  decided_fails_midpoint 𝒲 ⊤ χ p (Or.inl fun v _ => PCWorld.holds_top v) hmid₀ hmid₁ hresp hpos

/-- **Encoding check for the interval form**: `⊤` *is* exactly reflected, in the interval sense
`lo · p(χ) < p(⊤ ⋏ χ) ≤ hi · p(χ)`, at every cell reaching `1` (`lo < 1 ≤ hi`) of positive mass,
under the same theory-respect hypothesis the liar theorems use. So "the conditional lies outside
the cell" is a property some decided sentences have at some cells and the liar has at **every**
one-sided cell (`Liar.lean` `exact_reflection_fails_liar`): the impossibility is not an artifact of
the hypothesis package. (A false sentence is likewise exactly reflected at a cell with `lo < 0 ≤ hi`;
inside `[0, 1]` the `(lo, hi]` convention puts `0` in no cell — findings F6.)
Source: STANDARDS §3 (impossibility results get an encoding check); audit r1
Kind: L
Fidelity: n/a -/
theorem top_exact_interval (𝒲 : PCWorld → Prop) (χ : Sentence) (p : Sentence → ℝ)
    {lo hi : ℚ} (hlo : lo < 1) (hhi : 1 ≤ hi)
    (hresp : RespectsEntailment 𝒲 p (⊤ : Sentence) χ) (hpos : 0 < p χ) :
    (lo : ℝ) * p χ < p ((⊤ : Sentence) ⋏ χ) ∧ p ((⊤ : Sentence) ⋏ χ) ≤ (hi : ℝ) * p χ := by
  have h : p ((⊤ : Sentence) ⋏ χ) = p χ := hresp.1 fun v _ _ => PCWorld.holds_top v
  have hloR : (lo : ℝ) < 1 := by exact_mod_cast hlo
  have hhiR : (1 : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi
  rw [h]
  constructor
  · nlinarith [mul_pos hpos (sub_pos.2 hloR)]
  · nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hhiR)]


/-- **`⊤` fails interval-exactness at every cell with `hi < 1` of positive mass** under
theory-respect — the companion of `top_exact_interval`: a true sentence's conditional `1` lies
outside any cell below `1`. At a cell *below* the liar's threshold (`hi < p ≤ 1`) the liar and `⊤`
therefore fail identically; the liar's one-sided failure is separated from `⊤`'s only at cells
*above* the threshold (`Liar.lean` `liar_oneSided_witness_of_ne`, register corrected in repair
round 2).
Source: audit r2 adversarial N1 (probe `top_fails_below_cell`, adopted); STANDARDS §3
Kind: L
Fidelity: n/a -/
theorem top_fails_below_cell (𝒲 : PCWorld → Prop) (χ : Sentence) (p : Sentence → ℝ)
    {lo hi : ℚ} (hhi : hi < 1) (hresp : RespectsEntailment 𝒲 p (⊤ : Sentence) χ) (hpos : 0 < p χ) :
    ¬ ((lo : ℝ) * p χ < p ((⊤ : Sentence) ⋏ χ) ∧ p ((⊤ : Sentence) ⋏ χ) ≤ (hi : ℝ) * p χ) := by
  have h : p ((⊤ : Sentence) ⋏ χ) = p χ := hresp.1 fun v _ _ => PCWorld.holds_top v
  rw [h]
  rintro ⟨-, h2⟩
  have hhiR : (hi : ℝ) < 1 := by exact_mod_cast hhi
  nlinarith [mul_pos hpos (sub_pos.2 hhiR)]

/-! ## The midpoint predicate over every sentence collapses at `⊤` -/

/-- **Coherence at `⊤` on one cell plus the midpoint identity forces zero mass on that cell**
when `mid ≠ 1`: instantiating `ExactReflection` at `φ := ⊤` gives `P_n(⊤ ⋏ χ_I) = mid I · P_n(χ_I)`,
and `P_n(⊤ ⋏ χ_I) = P_n(χ_I)` (the weakest propositional constraint there is) then reads
`P_n(χ_I) = mid I · P_n(χ_I)`. For a family inside `[0, 1]` every nonempty cell has `mid < 1`, so a
`⊤`-coherent inhabitant of the midpoint predicate over every sentence gives probability `0`, on every
day `n < m`, to every cell about `𝑸_m(⊤)`. No liar, no self-reference, no FAF: the obstruction is
the midpoint representative at a decided sentence (findings F5, F15). `pointWorld_not_exactReflection`
(`Liar.lean`) is the completed-theory instance.
Source: audit r2 adversarial B2 (probe `coherentTop_forces_zero`, adopted); findings F15
Kind: L
Fidelity: n/a -/
theorem coherentTop_forces_zero (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) (P : History) (h : ExactReflection quoteAt cells P)
    {n m : ℕ} (hnm : n < m) {I : ℚ × ℚ} (hI : I ∈ cells m) (hmid : mid I ≠ 1)
    (htop : P n ((⊤ : Sentence) ⋏ quoteAt m ⊤ I.1 I.2) = P n (quoteAt m ⊤ I.1 I.2)) :
    P n (quoteAt m ⊤ I.1 I.2) = 0 := by
  have hid := h n m hnm ⊤ I hI
  rw [htop] at hid
  have hmidR : ((mid I : ℚ) : ℝ) ≠ 1 := by exact_mod_cast hmid
  by_contra hne
  have h1 : P n (quoteAt m ⊤ I.1 I.2) * (1 - ((mid I : ℚ) : ℝ)) = 0 := by linarith
  rcases mul_eq_zero.1 h1 with h0 | h0
  · exact hne h0
  · exact hmidR (by linarith)

/-- **No history coherent at `⊤` on a cell of the family with `mid ≠ 1` and positive mass on it
satisfies `ExactReflection`.** This is the encoding check STANDARDS §3 asks of the midpoint
predicate over every sentence, and it fails it: its inhabitants with positive mass on a cell about
`𝑸_m(⊤)` of midpoint `≠ 1` are all `⊤`-incoherent (`sotoBundleHistory` below is one, by
necessity — `sotoBundle_top_incoherent`). The interval form `ExactReflectionInterval` does not
collapse this way (`top_exact_interval`; `coherentTop_interval_below_cell` is the honest
constraint it imposes).
Source: audit r2 adversarial B2 (probe `coherentTop_not_exactReflection`, adopted)
Kind: L
Fidelity: n/a -/
theorem coherentTop_not_exactReflection (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) (P : History)
    {n m : ℕ} (hnm : n < m) {I : ℚ × ℚ} (hI : I ∈ cells m) (hmid : mid I ≠ 1)
    (htop : P n ((⊤ : Sentence) ⋏ quoteAt m ⊤ I.1 I.2) = P n (quoteAt m ⊤ I.1 I.2))
    (hpos : P n (quoteAt m ⊤ I.1 I.2) ≠ 0) :
    ¬ ExactReflection quoteAt cells P :=
  fun h => hpos (coherentTop_forces_zero quoteAt cells P h hnm hI hmid htop)

/-- **What the interval form asks of a `⊤`-coherent history**: under `ExactReflectionInterval`,
coherence at `⊤` on a cell with `hi < 1` forbids positive mass on that cell — the history must
believe its future price of `⊤` lands in a cell reaching `1`, a consistent belief (`top_exact_interval`
is satisfied there). Contrast `coherentTop_forces_zero`: the midpoint form forbids positive mass on
*every* cell of midpoint `≠ 1`, including the top cell of any family inside `[0, 1]`.
Source: audit r2 adversarial B2 (iii) (α); STANDARDS §3
Kind: L
Fidelity: n/a -/
theorem coherentTop_interval_below_cell (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) (P : History) (h : ExactReflectionInterval quoteAt cells P)
    {n m : ℕ} (hnm : n < m) {I : ℚ × ℚ} (hI : I ∈ cells m) (hhi : I.2 < 1)
    (htop : P n ((⊤ : Sentence) ⋏ quoteAt m ⊤ I.1 I.2) = P n (quoteAt m ⊤ I.1 I.2)) :
    ¬ 0 < P n (quoteAt m ⊤ I.1 I.2) := by
  intro hpos
  obtain ⟨-, h2⟩ := h n m hnm ⊤ I hI hpos
  rw [htop] at h2
  have hhiR : (I.2 : ℝ) < 1 := by exact_mod_cast hhi
  nlinarith [mul_pos hpos (sub_pos.2 hhiR)]

/-! ## Inhabitants of the exact identities: the zero history and Soto's bundle market -/

/-- **The all-zero history satisfies exact self-trust** (`0 = mid · 0`): the predicate is
inhabited, degenerately (N−). No non-degenerate inhabitant exists for the midpoint predicate over
every sentence: every inhabitant with positive mass on a cell about `𝑸_m(⊤)` of midpoint `≠ 1` is
`⊤`-incoherent (`coherentTop_forces_zero`); the best available is `sotoBundleHistory` below.
Source: mandate § X6 (v) ("non-vacuity of `ExactSelfTrustX`: the all-zero history (N−)")
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem zeroHistory_exactSelfTrustX (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) :
    ExactSelfTrustX quoteAt cells (fun _ _ => (0 : ℝ)) := by
  intro n m _ φ I _
  simp

/-- **Soto's `n = 1` bundle market with both of its defining clauses, as a `History`** (PDF 20
p. 1, bli-soto-b-025; in the order the page gives them): *Reflection clause* — an object-level
sentence `ψ` (neither a cell sentence of the family nor a conjunction with one) is priced on day `n`
at the marginal `∑_{I ∈ cells (n+1)} mid I · w I` ("`Q_k(φ) := ∑ (m+0.5)/2^{k+1} · Q_k(Q_{k+1}(φ) ∈ cell_m)`,
that is, Reflection principle by definition"); *self-trust clause* — a cell sentence
`quoteAt m φ I.1 I.2` with `n < m`, `I ∈ cells m` is priced at the cell mass `w I`, and the
conjunction `φ ⋏ quoteAt m φ I.1 I.2` at `mid I · w I` ("Epistemic self-trust by definition").
Defined by classical case analysis on the shape of the sentence; `sotoBundle_quote`/`sotoBundle_conj`/
`sotoBundle_obj` compute it under two injectivity facts about `quoteAt`. **What it is not**: a
coherent valuation. It is `⊤`-incoherent at every cell of positive mass with `mid ≠ 1`
(`sotoBundle_top_incoherent`) — as every positive-mass inhabitant of `ExactSelfTrustX` must be
(`coherentTop_forces_zero`) — and prices `⊤` and `⊥` alike at the marginal, which is `< 1` for a
probability on cells inside `[0, 1]` (`sotoBundle_top_lt_one`, findings F15: Soto's page says
coherence is "translated into our derived object-level beliefs", which holds only up to the cell
half-width). Meta-level sentences (cells about cells) do not marginalize. Repair round 1's
`bundleHistory` kept only the self-trust clause and priced every object-level sentence at `0`
(audit r2 fidelity B1); it is replaced by this.
Source: Soto PDF 20 p. 1–2 ([[bli-soto-b-inventory]] 025); audit r2 fidelity B1 (probe
`SotoBundleBothClauses`, adopted), adversarial B2
Kind: D
Fidelity: variant: Soto's `n = 1` bundle at a general cell family, as a `History`; the marginal is
taken over `cells (n+1)` (Soto's single horizon) -/
noncomputable def sotoBundleHistory (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) (w : ℚ × ℚ → ℝ) : History := fun n ψ =>
  open Classical in
  if h : ∃ t : ℕ × Sentence × (ℚ × ℚ), n < t.1 ∧ t.2.2 ∈ cells t.1 ∧
      ψ = quoteAt t.1 t.2.1 t.2.2.1 t.2.2.2 then
    w (Classical.choose h).2.2
  else if h' : ∃ t : ℕ × Sentence × (ℚ × ℚ), n < t.1 ∧ t.2.2 ∈ cells t.1 ∧
      ψ = t.2.1 ⋏ quoteAt t.1 t.2.1 t.2.2.1 t.2.2.2 then
    ((mid (Classical.choose h').2.2 : ℚ) : ℝ) * w (Classical.choose h').2.2
  else ∑ I ∈ cells (n + 1), ((mid I : ℚ) : ℝ) * w I

/-- **Cell injectivity of a quote family relative to a cell family**: two cell sentences of the
family that coincide name the same cell (whatever their days and quoted sentences).
`bli-found`'s `quoteAt T` has it (`Perturb.lean` `quoteAt_cellInjective`).
Source: none: infrastructure (hypothesis of `sotoBundle_quote`)
Kind: D
Fidelity: n/a -/
def CellInjective (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (cells : ℕ → Finset (ℚ × ℚ)) :
    Prop :=
  ∀ (m m' : ℕ) (φ φ' : Sentence) (I I' : ℚ × ℚ), I ∈ cells m → I' ∈ cells m' →
    quoteAt m φ I.1 I.2 = quoteAt m' φ' I'.1 I'.2 → I = I'

/-- **Conjunction/cell disjointness of a quote family**: a conjunction `φ ⋏ quoteAt …` is never
itself a cell sentence. `bli-found`'s `quoteAt T` has it (`Perturb.lean`
`quoteAt_conjDisjoint`).
Source: none: infrastructure (hypothesis of `sotoBundle_conj`)
Kind: D
Fidelity: n/a -/
def ConjDisjoint (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) : Prop :=
  ∀ (m m' : ℕ) (φ φ' : Sentence) (lo hi lo' hi' : ℚ),
    φ ⋏ quoteAt m φ lo hi ≠ quoteAt m' φ' lo' hi'

/-- **An object-level sentence** relative to a quote family: neither a cell sentence (for any day,
sentence and cell) nor a conjunction `φ ⋏ quoteAt m φ lo hi`. At `bli-found`'s `quoteAt T` every
non-conjunction is object-level — atoms and `⊤` in particular (`Perturb.lean`
`objectLevel_quoteAt_of_not_isAnd`).
Source: Soto PDF 20 p. 1 ("object-level" vs "meta-level" sentences); none: infrastructure
Kind: D
Fidelity: variant: a syntactic shape condition, not Soto's informal partition of the language -/
def ObjectLevel (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence) (ψ : Sentence) : Prop :=
  (∀ m φ lo hi, ψ ≠ quoteAt m φ lo hi) ∧ (∀ m φ lo hi, ψ ≠ φ ⋏ quoteAt m φ lo hi)

/-- `sotoBundleHistory` prices a cell sentence of the family at its cell mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sotoBundle_quote {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) (w : ℚ × ℚ → ℝ)
    {n m : ℕ} (hnm : n < m) (φ : Sentence) {I : ℚ × ℚ} (hI : I ∈ cells m) :
    sotoBundleHistory quoteAt cells w n (quoteAt m φ I.1 I.2) = w I := by
  have hex : ∃ t : ℕ × Sentence × (ℚ × ℚ), n < t.1 ∧ t.2.2 ∈ cells t.1 ∧
      quoteAt m φ I.1 I.2 = quoteAt t.1 t.2.1 t.2.2.1 t.2.2.2 := ⟨(m, φ, I), hnm, hI, rfl⟩
  unfold sotoBundleHistory
  rw [dif_pos hex]
  obtain ⟨-, hc, heq⟩ := Classical.choose_spec hex
  exact congrArg w (hinj _ _ _ _ _ _ hI hc heq).symm

/-- `sotoBundleHistory` prices the conjunction of `φ` with a cell sentence of the family at the
cell's midpoint times its mass (the self-trust clause).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sotoBundle_conj {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) (hne : ConjDisjoint quoteAt)
    (w : ℚ × ℚ → ℝ) {n m : ℕ} (hnm : n < m) (φ : Sentence) {I : ℚ × ℚ} (hI : I ∈ cells m) :
    sotoBundleHistory quoteAt cells w n (φ ⋏ quoteAt m φ I.1 I.2) = ((mid I : ℚ) : ℝ) * w I := by
  have hnot : ¬ ∃ t : ℕ × Sentence × (ℚ × ℚ), n < t.1 ∧ t.2.2 ∈ cells t.1 ∧
      φ ⋏ quoteAt m φ I.1 I.2 = quoteAt t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    rintro ⟨t, -, -, h⟩
    exact hne _ _ _ _ _ _ _ _ h
  have hex : ∃ t : ℕ × Sentence × (ℚ × ℚ), n < t.1 ∧ t.2.2 ∈ cells t.1 ∧
      φ ⋏ quoteAt m φ I.1 I.2 = t.2.1 ⋏ quoteAt t.1 t.2.1 t.2.2.1 t.2.2.2 :=
    ⟨(m, φ, I), hnm, hI, rfl⟩
  unfold sotoBundleHistory
  rw [dif_neg hnot, dif_pos hex]
  obtain ⟨-, hc, heq⟩ := Classical.choose_spec hex
  obtain ⟨-, hq⟩ := Formula.and_inj.1 heq
  exact congrArg (fun J : ℚ × ℚ => ((mid J : ℚ) : ℝ) * w J) (hinj _ _ _ _ _ _ hI hc hq).symm

/-- `sotoBundleHistory` prices an object-level sentence at the marginal `∑_{I ∈ cells (n+1)} mid I · w I`
(the Reflection clause).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sotoBundle_obj {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (w : ℚ × ℚ → ℝ) (n : ℕ) {ψ : Sentence}
    (hψ : ObjectLevel quoteAt ψ) :
    sotoBundleHistory quoteAt cells w n ψ = ∑ I ∈ cells (n + 1), ((mid I : ℚ) : ℝ) * w I := by
  have h1 : ¬ ∃ t : ℕ × Sentence × (ℚ × ℚ), n < t.1 ∧ t.2.2 ∈ cells t.1 ∧
      ψ = quoteAt t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    rintro ⟨t, -, -, h⟩
    exact hψ.1 _ _ _ _ h
  have h2 : ¬ ∃ t : ℕ × Sentence × (ℚ × ℚ), n < t.1 ∧ t.2.2 ∈ cells t.1 ∧
      ψ = t.2.1 ⋏ quoteAt t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    rintro ⟨t, -, -, h⟩
    exact hψ.2 _ _ _ _ h
  unfold sotoBundleHistory
  rw [dif_neg h1, dif_neg h2]

/-- **Soto's bundle market satisfies the exact self-trust identity on the whole family**, for every
mass function `w`. Grade **N−** for `ExactSelfTrustX`/`ExactReflection` (repair round 2, audit r2
adversarial B2 / fidelity B1): it satisfies the identity *by definition* on the two shapes it
constrains and is `⊤`-incoherent at every cell of positive mass with `mid ≠ 1`
(`sotoBundle_top_incoherent`) — which `coherentTop_forces_zero` shows every positive-mass inhabitant
of this predicate must be. What it establishes is that the midpoint predicate over every sentence does
not collapse to the zero history: positive cell masses and object-level prices in `(0, 1)` are
consistent with it (`sotoBundle_quote`, `sotoBundle_obj`) — **and** with exact no-net-update at every
object-level sentence at the same time (`sotoBundle_exactNNUAt`): the two exact identities of the
program (constraints 2 and 4) are jointly satisfiable, with positive masses, which repair round 1's
one-clause inhabitant was not (audit r2 fidelity B1's probe `B_not_exactNNUAt`). A *coherent*
inhabitant for every `φ` at once is open (report § Open).
Source: Soto PDF 20 p. 1–2 ([[bli-soto-b-inventory]] 025); mandate X6 (v) (non-vacuity);
audit r2 fidelity B1 (i), adversarial B2 (ii)
Kind: N-
Fidelity: n/a
Hyps: (a) `hinj`, `hne` (proved for `quoteAt T` in `Perturb.lean`) -/
theorem sotoBundle_exactSelfTrustX {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) (hne : ConjDisjoint quoteAt)
    (w : ℚ × ℚ → ℝ) :
    ExactSelfTrustX quoteAt cells (sotoBundleHistory quoteAt cells w) := by
  intro n m hnm φ I hI
  rw [sotoBundle_conj hinj hne w hnm φ hI, sotoBundle_quote hinj w hnm φ hI]

/-- **Soto's bundle market satisfies exact no-net-update at every object-level sentence, every
day** — the Reflection clause, as Soto states it ("Reflection principle by definition"). Together
with `sotoBundle_exactSelfTrustX`: the two exact identities X3 refutes on a logical inductor are
jointly satisfiable with positive cell masses.
Source: Soto PDF 20 p. 1 (the Reflection clause); audit r2 fidelity B1 (i) (probe
`sotoHistory_exactNNUAt`, adopted)
Kind: L
Fidelity: exact (Soto's `n = 1` clause at a general family)
Hyps: (a) `hinj`; (a) `hψ` (object-level; discharged for atoms and `⊤` at `quoteAt T` in `Perturb.lean`) -/
theorem sotoBundle_exactNNUAt {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) (w : ℚ × ℚ → ℝ) (n : ℕ)
    {ψ : Sentence} (hψ : ObjectLevel quoteAt ψ) :
    ExactNNUAt quoteAt cells (sotoBundleHistory quoteAt cells w) n ψ := by
  unfold ExactNNUAt
  rw [sotoBundle_obj w n hψ]
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [sotoBundle_quote hinj w (Nat.lt_succ_self n) ψ hI]

/-- Soto's bundle market satisfies the **interval** form of exact reflection on any family of
non-degenerate cells (`lo < hi`), for every `w`: `ExactReflection.interval`. Grade N− for the same
reason as `sotoBundle_exactSelfTrustX` (by-definition valuation; `⊤`-incoherent). Unlike the
midpoint form, the interval form admits `⊤`-coherent inhabitants in principle
(`coherentTop_interval_below_cell`); none is exhibited here (report § Open).
Source: audit r2 adversarial B2 (iii) (α)
Kind: N-
Fidelity: n/a
Hyps: (a) `hinj`, `hne`; (a) `hcells` (non-degenerate cells) -/
theorem sotoBundle_exactReflectionInterval {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) (hne : ConjDisjoint quoteAt)
    (w : ℚ × ℚ → ℝ) (hcells : ∀ m, ∀ I ∈ cells m, I.1 < I.2) :
    ExactReflectionInterval quoteAt cells (sotoBundleHistory quoteAt cells w) :=
  (sotoBundle_exactSelfTrustX hinj hne w).interval hcells

/-- Soto's bundle market satisfies the **interval** form of no-net-update at every object-level
sentence, for nonnegative masses on cells with `lo ≤ hi`: `ExactNNUAt.interval`.
Source: audit r2 adversarial B1 (the interval reading of no-net-update)
Kind: L
Fidelity: n/a
Hyps: (a) `hinj`; (a) `hψ`; (a) `hw`, `hcells` -/
theorem sotoBundle_exactNNUAtInterval {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) {w : ℚ × ℚ → ℝ}
    (hw : ∀ I, 0 ≤ w I) (n : ℕ) (hcells : ∀ I ∈ cells (n + 1), I.1 ≤ I.2) {ψ : Sentence}
    (hψ : ObjectLevel quoteAt ψ) :
    ExactNNUAtInterval quoteAt cells (sotoBundleHistory quoteAt cells w) n ψ :=
  (sotoBundle_exactNNUAt hinj w n hψ).interval hcells
    (fun I hI => by rw [sotoBundle_quote hinj w (Nat.lt_succ_self n) ψ hI]; exact hw I)

/-- **Soto's bundle market is incoherent at `⊤`** on every cell of the family with `w I ≠ 0` and
`mid I ≠ 1`: `P_n(⊤ ⋏ χ_I) = mid I · w I ≠ w I = P_n(χ_I)`. Derived from `coherentTop_forces_zero`:
coherence at `⊤` there would force `w I = 0`. So the incoherence is not a defect of this particular
construction but of the midpoint predicate it inhabits.
Source: audit r2 adversarial B2 (probe `bundleHistory_top_incoherent`, adopted and re-derived)
Kind: L
Fidelity: n/a -/
theorem sotoBundle_top_incoherent {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) (hne : ConjDisjoint quoteAt)
    (w : ℚ × ℚ → ℝ) {n m : ℕ} (hnm : n < m) {I : ℚ × ℚ} (hI : I ∈ cells m) (hw : w I ≠ 0)
    (hmid : mid I ≠ 1) :
    sotoBundleHistory quoteAt cells w n ((⊤ : Sentence) ⋏ quoteAt m ⊤ I.1 I.2) ≠
      sotoBundleHistory quoteAt cells w n (quoteAt m ⊤ I.1 I.2) := by
  intro htop
  have h0 := coherentTop_forces_zero quoteAt cells _ (sotoBundle_exactSelfTrustX hinj hne w)
    hnm hI hmid htop
  rw [sotoBundle_quote hinj w hnm ⊤ hI] at h0
  exact hw h0

/-- **Soto's bundle market prices `⊤` strictly below `1`** whenever `w` is a probability on
`cells (n+1)` and every cell has midpoint `< 1` — every family inside `[0, 1]`, Soto's dyadic
partition included (with all mass on the top cell `(1 − 2^{−(k+1)}, 1]`, `P_k(⊤) = 1 − 2^{−(k+2)}`,
`sotoBundle_obj_single`). Finding F15 about PDF 20 p. 2: "those Coherence properties will also be
translated into our derived object-level beliefs" holds only up to the cell half-width; at the
exact level the marginalized market is incoherent at `⊤`. `⊤` must be object-level for the family
(true at `quoteAt T`: `Perturb.lean` `objectLevel_quoteAt_top`).
Source: Soto PDF 20 p. 1–2 ([[bli-soto-b-inventory]] 025, 027); audit r2 adversarial B2 (iv)
Kind: P
Fidelity: exact (Soto's `n = 1` market at a general family; the dyadic instance is the docstring's)
Hyps: (a) `htop` (object-level `⊤`, discharged at `quoteAt T`); (a) `hw`, `hsum`, `hmid` -/
theorem sotoBundle_top_lt_one {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (w : ℚ × ℚ → ℝ) (n : ℕ)
    (htop : ObjectLevel quoteAt (⊤ : Sentence))
    (hw : ∀ I ∈ cells (n + 1), 0 ≤ w I) (hsum : ∑ I ∈ cells (n + 1), w I = 1)
    (hmid : ∀ I ∈ cells (n + 1), mid I < 1) :
    sotoBundleHistory quoteAt cells w n (⊤ : Sentence) < 1 := by
  rw [sotoBundle_obj w n htop]
  have hex : ∃ I ∈ cells (n + 1), (0 : ℝ) < w I := by
    by_contra hcon
    have hall : ∀ I ∈ cells (n + 1), w I ≤ 0 :=
      fun I hI => not_lt.1 fun hlt => hcon ⟨I, hI, hlt⟩
    have : ∑ I ∈ cells (n + 1), w I ≤ ∑ I ∈ cells (n + 1), (0 : ℝ) :=
      Finset.sum_le_sum hall
    rw [Finset.sum_const_zero, hsum] at this
    exact absurd this (by norm_num)
  obtain ⟨J, hJ, hJpos⟩ := hex
  calc ∑ I ∈ cells (n + 1), ((mid I : ℚ) : ℝ) * w I
      < ∑ I ∈ cells (n + 1), w I := by
        refine Finset.sum_lt_sum (fun I hI => ?_) ⟨J, hJ, ?_⟩
        · have h1 : ((mid I : ℚ) : ℝ) ≤ 1 := by exact_mod_cast (hmid I hI).le
          exact mul_le_of_le_one_left (hw I hI) h1
        · have h1 : ((mid J : ℚ) : ℝ) < 1 := by exact_mod_cast hmid J hJ
          exact mul_lt_of_lt_one_left hJpos h1
    _ = 1 := hsum

/-- The object-level price of Soto's bundle market when all mass sits on one cell `J` of
`cells (n+1)`: exactly `mid J`. At Soto's dyadic top cell `(1 − 2^{−(k+1)}, 1]` this is
`1 − 2^{−(k+2)}` — the value findings F15 records for `P_k(⊤)`.
Source: Soto PDF 20 p. 1–2; audit r2 adversarial B2 (iv)
Kind: L
Fidelity: n/a -/
theorem sotoBundle_obj_single {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (n : ℕ) {J : ℚ × ℚ} (hJ : J ∈ cells (n + 1)) {ψ : Sentence}
    (hψ : ObjectLevel quoteAt ψ) :
    sotoBundleHistory quoteAt cells (fun I => if I = J then (1 : ℝ) else 0) n ψ =
      ((mid J : ℚ) : ℝ) := by
  rw [sotoBundle_obj _ n hψ]
  simp [Finset.sum_ite_eq', hJ]

end Cleanroom.Bli.BliExactness
