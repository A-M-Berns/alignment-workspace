import LogicalInduction.Framework.Criterion
import Mathlib.Algebra.BigOperators.Intervals

/-!
# `li-pseudorandom` — definitions of record

Package `li-pseudorandom` (faf-cleanroom run, 2026-09-29), the definitions module. Everything a
dependent needs to *state* pseudorandomness of a constructed family over FAF's objects is defined
here, as `def`s (never as `Classical.choose` of an existential):

* `truthR` — the only bridge from `Bool` streams to FAF's `truth : ℕ → ℝ`;
* `CausalRule` — a **strictly causal** bounded weight rule: the day-`n` weight may read the truth
  values of days `< n` only (never day `n`: the `≤ n` variant admits the omniscient rule and makes
  the diagonal theorem false);
* the potential of the derandomized test-martingale argument (`tilt`, `mass`, `factor`, `mart`,
  `pot`) and the diagonal sequence `diag R p` built from it by day recursion (`diagStep`,
  `diagPrefix`, `diag`) — T1's object;
* `restrict`, `clamp`, `builderRule`, `CausalBuilder`, `diagBuilder` — the rule "clamp the day-`n`
  denotation of the `k`-th enumerated weighting on the market built from the truth prefix", and the
  diagonal sequence over such rules for a market builder `B : (ℕ → Bool) → History` — T5's object;
* `atomFamily`, `literalOf`, `atomDP` — the deductive process that decides the literal atoms
  `atom (a j)` / `∼atom (a j)` with delay profile `g` — T6's process.

Nothing here is called `PseudorandomFrequency`, `DivergentWeighting` or `PGenerableWeighting`:
those are FAF's and are used as such in `Fixed.lean`/`Family.lean`. `diag`, `builderRule` and
`diagBuilder` are noncomputable as written (they compare real potentials); computability of the
family of record is T7's separate certificate (`Computable.lean`).

FAF pin `159ec3f`; the only FAF import is `Framework.Criterion` (`EF`, `History`,
`DeductiveProcess`, `PCWorld`, `Sentence`).
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction
open scoped BigOperators

/-! ## Truth streams -/

/-- The `{0,1}`-valued real stream of a Boolean stream: `truthR x n = 1` if `x n`, else `0`.
The only bridge from `Bool` streams to FAF's `truth : ℕ → ℝ` (`TheoryTruth.isBoolean` is the
converse direction).
Source: mandate § Definitions of record
Kind: D
Fidelity: exact -/
noncomputable def truthR (x : ℕ → Bool) : ℕ → ℝ := fun n => if x n then 1 else 0

/-- The stream `x` cut off at day `n`: `x j` for `j < n`, `false` from day `n` on.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def restrict (x : ℕ → Bool) (n : ℕ) : ℕ → Bool := fun j => if j < n then x j else false

/-- Clamp a real into `[0,1]`: `max 0 (min 1 r)`. The identity on `[0,1]` (`clamp_of_mem_Icc`
in `Diagonal.lean`); used so that a rule's weights lie in `[0,1]` for **every** stream, not only
for the stream finally chosen.
Source: mandate T1 trap (ii)
Kind: D
Fidelity: n/a -/
noncomputable def clamp (r : ℝ) : ℝ := max 0 (min 1 r)

/-! ## Strictly causal bounded weight rules -/

/-- **A strictly causal bounded weight rule.** `w x n ∈ [0,1]` for every stream `x` and day `n`,
and the day-`n` weight depends only on the truth values of days `< n` (`causal`). Strictness is
the content: with `≤ n` the omniscient rule "weight `1` on day `n` iff `x n`" would be admitted and
the diagonal theorem (`diag_pseudorandom`, `Diagonal.lean`) would be false.
Source: mandate § Definitions of record; T1
Kind: D
Fidelity: exact -/
structure CausalRule where
  /-- The weight of day `n` on the stream `x`. -/
  w : (ℕ → Bool) → ℕ → ℝ
  nonneg : ∀ x n, 0 ≤ w x n
  le_one : ∀ x n, w x n ≤ 1
  /-- Strict causality: day `n`'s weight reads days `< n` only. -/
  causal : ∀ x y n, (∀ j < n, x j = y j) → w x n = w y n

/-! ## The potential

Rules are indexed by `k := (Nat.unpair i).1` and tilts by `m := (Nat.unpair i).2`, so that the
single index `i` runs over all pairs `(k, m)`; rule `i` is activated at day `i` with tilt
`tilt i = 1/(m+2) ≤ 1/2` and mass `mass i = 2^{-(i+1)}` (total mass `≤ 1`). For a sign `s ∈ {1,-1}`
the running product `mart R p x s i n = ∏_{i ≤ j < n} (1 + s · tilt i · w_k(x, j) · (truthR x j − p j))`
is a nonnegative supermartingale under a `p`-coin; the potential `pot R p x n` is the finite sum
of all activated products through day `n − 1`. -/

/-- The tilt of index `i`: `1 / ((Nat.unpair i).2 + 2)`, in `(0, 1/2]`.
Source: mandate T1 (construction)
Kind: D
Fidelity: n/a -/
noncomputable def tilt (i : ℕ) : ℝ := 1 / (((Nat.unpair i).2 : ℝ) + 2)

/-- The mass of index `i`: `(1/2)^(i+1)`; the masses sum to at most `1`.
Source: mandate T1 (construction)
Kind: D
Fidelity: n/a -/
noncomputable def mass (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 1)

/-- One factor of the running product of index `i` at day `j` with sign `s`:
`1 + s · tilt i · w_k(x, j) · (truthR x j − p j)`, `k := (Nat.unpair i).1`.
Source: mandate T1 (construction)
Kind: D
Fidelity: n/a -/
noncomputable def factor (R : ℕ → CausalRule) (p : ℕ → ℝ) (x : ℕ → Bool) (s : ℝ) (i j : ℕ) :
    ℝ :=
  1 + s * tilt i * (R (Nat.unpair i).1).w x j * (truthR x j - p j)

/-- The running product of index `i` with sign `s` over the window `[i, n)`.
Source: mandate T1 (construction)
Kind: D
Fidelity: n/a -/
noncomputable def mart (R : ℕ → CausalRule) (p : ℕ → ℝ) (x : ℕ → Bool) (s : ℝ) (i n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico i n, factor R p x s i j

/-- The potential through days `< n`: `∑_{i < n} mass i · (mart(+) + mart(−))`, a finite sum at
every day. `pot R p x n` depends only on `x` at days `< n` (`pot_congr`, `Diagonal.lean`).
Source: mandate T1 (construction)
Kind: D
Fidelity: n/a -/
noncomputable def pot (R : ℕ → CausalRule) (p : ℕ → ℝ) (x : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, mass i * (mart R p x 1 i n + mart R p x (-1) i n)

/-! ## The diagonal sequence -/

open Classical in
/-- The day-`n` choice given the prefix `past` (only its values on days `< n` matter): `true`
iff setting day `n` to `true` gives the strictly smaller potential through day `n`; ties go to
`false`.
Source: mandate T1 (construction)
Kind: D
Fidelity: n/a -/
noncomputable def diagStep (R : ℕ → CausalRule) (p : ℕ → ℝ) (n : ℕ) (past : ℕ → Bool) : Bool :=
  decide (pot R p (Function.update past n true) (n + 1) <
    pot R p (Function.update past n false) (n + 1))

/-- The diagonal prefix through day `n − 1` (`false` from day `n` on), by recursion on `n`.
Source: mandate T1 (construction)
Kind: D
Fidelity: n/a -/
noncomputable def diagPrefix (R : ℕ → CausalRule) (p : ℕ → ℝ) : ℕ → (ℕ → Bool)
  | 0 => fun _ => false
  | n + 1 => Function.update (diagPrefix R p n) n (diagStep R p n (diagPrefix R p n))

/-- **The diagonal sequence** of T1: day `n` is chosen by `diagStep` from the prefix of days
`< n`, i.e. by course-of-values recursion on the day, from the rules `R` and the target `p`. A
`def`, not a `Classical.choose`. Noncomputable as written (it compares real potentials); the
computability of the family of record is T7's certificate.
Source: mandate T1; [[anson-inventory]] anson-034 (the diagonalization sub-target)
Kind: D
Fidelity: exact -/
noncomputable def diag (R : ℕ → CausalRule) (p : ℕ → ℝ) (n : ℕ) : Bool :=
  diagStep R p n (diagPrefix R p n)

/-! ## Rules from market builders (T5's objects) -/

/-- The rule "clamp the day-`n` denotation of the feature `W n` on the market the builder `B`
makes from the truth prefix of days `< n`". Strictly causal by construction (it reads
`restrict x n`), so no hypothesis on `B` is needed to *define* it; the hypothesis `CausalBuilder`
enters only in the theorem that identifies its realized weights with `(W n).denote (B x)`.
Source: mandate T5
Kind: D
Fidelity: variant: the feature is evaluated on `B (restrict x n)`, not on `B x` as in the
mandate's rule; the realized weights agree under `CausalBuilder B g` with `j < g j`
(`builderRule_w_eq`, `Fixed.lean`) -/
noncomputable def builderRule (B : (ℕ → Bool) → History) (W : ℕ → EF) : CausalRule where
  w x n := clamp ((W n).denote (B (restrict x n)))
  nonneg _ _ := le_max_left _ _
  le_one _ _ := max_le zero_le_one (min_le_left _ _)
  causal x y n h := by
    have : restrict x n = restrict y n := by
      funext j
      unfold restrict
      split_ifs with hj
      · exact h j hj
      · rfl
    simp only [this]

/-- **Causal builder for delay `g`.** A map from truth streams to histories such that the
market at days `≤ n` depends only on the truth values `x j` with `g j ≤ n` (those the process has
decided by day `n`). Excludes markets that read a truth value before its decision day — the
"omniscient" markets of the mandate's § Context 1, against which no fixed family is pseudorandom.
The strictness `∀ j, j < g j` carried by every theorem is load-bearing: the omniscient builder is
a `CausalBuilder` for `g = id` and not for delay one (`omniscient_causalBuilder_id`,
`omniscient_not_causalBuilder_succ`, `Witnesses.lean`).
Source: mandate T5
Kind: D
Fidelity: exact -/
def CausalBuilder (B : (ℕ → Bool) → History) (g : ℕ → ℕ) : Prop :=
  ∀ x y n, (∀ j, g j ≤ n → x j = y j) → ∀ m ≤ n, ∀ φ, B x m φ = B y m φ

/-- The diagonal sequence over the builder rules of an enumeration `gen` of feature progressions:
`diag (fun k => builderRule B (gen k)) p`. With `gen` the enumeration of FAF's P-generable
weightings (`genWeighting`, `Countable.lean`) and `B x := liaHistory (atomDP a x g)` this is the
family of record `truthStar` (`Family.lean`).
Source: mandate T5/T6
Kind: D
Fidelity: variant: through `builderRule` (rules on the prefix-built market); equal to the
mandate's diagonal under `CausalBuilder` -/
noncomputable def diagBuilder (B : (ℕ → Bool) → History) (gen : ℕ → ℕ → EF) (p : ℕ → ℝ) :
    ℕ → Bool :=
  diag (fun k => builderRule B (gen k)) p

/-! ## The atom-deciding process (T6's objects) -/

/-- The atom family at placement `a`: `n ↦ atom (a n)`.
Source: mandate T6
Kind: D
Fidelity: exact -/
def atomFamily (a : ℕ → ℕ) : ℕ → Sentence := fun n => LO.Propositional.Formula.atom (a n)

/-- The literal decided for member `j`: `atom (a j)` if `x j`, else `∼atom (a j)`.
Source: mandate T6
Kind: D
Fidelity: exact -/
def literalOf (a : ℕ → ℕ) (x : ℕ → Bool) (j : ℕ) : Sentence :=
  if x j then LO.Propositional.Formula.atom (a j) else ∼(LO.Propositional.Formula.atom (a j))

/-- **The atom-deciding process.** Stage `n` reveals the literal of every member `j ≤ n` whose
delay day `g j` has arrived (`g j ≤ n`). Parameters: `a` the atom placement (dependents pass their
allocator; `a = id` is this package's certified instance), `x` the truth stream, `g` the delay
profile (with `∀ j, j < g j` in every theorem that needs decision to come strictly after day `j`).
Composes with other processes by FAF's `DeductiveProcess.union`.
Source: mandate T6; [[bli-program]] §3.2(b) (L3), §3.6(iii) (K3)
Kind: D
Fidelity: exact -/
def atomDP (a : ℕ → ℕ) (x : ℕ → Bool) (g : ℕ → ℕ) : DeductiveProcess where
  D n := ((Finset.range (n + 1)).filter (fun j => g j ≤ n)).image (literalOf a x)
  mono n := by
    apply Finset.image_subset_image
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega

end Cleanroom.Li.LiPseudorandom
