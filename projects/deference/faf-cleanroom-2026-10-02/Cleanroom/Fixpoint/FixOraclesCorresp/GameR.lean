import Cleanroom.Fixpoint.FixOraclesCorresp.PenniesGadget
import Cleanroom.Fixpoint.FixOraclesCorresp.Liar
import Mathlib.Data.Fintype.Fin

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.GameR`: Theorem 5.1, abstract polynomial version

Target 15 (fixpoint-lit-2-007). Given polynomial evaluation maps
`polyEv c d i x = ∑ k, c i k * ∏ i', x i' ^ d i k i'` with degrees bounded by `B`, and thresholds `p`,
FTC's game `G_R` has the players `Player I B = I ⊕ (I × Fin B) ⊕ (I × Fin B)` — the main players
`mainP i`, the copy players `copyP i j` and the auxiliary players `auxP i j` — each with two actions:

* main `i` gets `∑ k, c i k * [every copy `(i', j)` with `j < d i k i'` plays `1`]` if it plays `1`,
  and `p i` if it plays `0`;
* each triple `(copyP i j, auxP i j, mainP i)` plays Lemma A.1's variant Matching Pennies with the
  main player as Matrix (`PenniesGadget.lean`), which forces `x (copyP i j) = x (mainP i)` at every
  mixed Nash equilibrium (`copy_forcing`);
* hence main `i`'s expected payoff from `1` is `∑ k, c i k * ∏ i', x (mainP i') ^ d i k i' = polyEv c d i x`
  (independent copies give the powers, `prod_copies`) and from `0` is `p i` (`gain_main`).

**Headline** (`gameR_nash_reflective`): for every mixed Nash equilibrium `σ` of `gameR c d p`, the
main players' answer vector `fun i => (σ (mainP i)).val 1` is reflective for `polyEv c d` at `p`.
Together with `exists_isMixedNashEq` (two-action Nash existence) this is a second existence proof
for polynomial reflective oracles — **not Kakutani-free**, since `exists_isMixedNashEq` rests on
`exists_reflective`, which rests on `fix-kakutani` (the ledger says so).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set StrategicGame Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Fintype K] {B : ℕ}

/-- **The players of `G_R`**: main players `I`, copy players `I × Fin B`, auxiliary players `I × Fin B`.
Source: FTC 2015 §5 ("the main players `i = 1..n`, the copy players `g(i,j)`, and the auxiliary
players `h(i,j)`")
Kind: D
Fidelity: exact (`m = n(2B + 1)` players)
Hyps: n/a -/
abbrev Player (I : Type*) (B : ℕ) : Type _ := I ⊕ ((I × Fin B) ⊕ (I × Fin B))

/-- The main player `i`.
Source: FTC 2015 §5 ("the main players `i = 1, …, n`")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev mainP (i : I) : Player I B := Sum.inl i

/-- The copy player `g(i, j)`.
Source: FTC 2015 §5 ("the copy players `g(i, j) := j · n + i`")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev copyP (i : I) (j : Fin B) : Player I B := Sum.inr (Sum.inl (i, j))

/-- The auxiliary player `h(i, j)`.
Source: FTC 2015 §5 ("the auxiliary players `h(i, j) := (B_R + j) · n + i`")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev auxP (i : I) (j : Fin B) : Player I B := Sum.inr (Sum.inr (i, j))

/-- The set of copy players main `i`'s monomial `k` reads: `{copyP i' j | j < d i k i'}`.
Source: FTC 2015 §5 (`f_{i,k}(a) = c_{i,k}` iff `a_{g(i',j)} = 1` for all `i'` and `j ≤ d_{i,k,i'}`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def copies (d : I → K → I → ℕ) (i : I) (k : K) : Finset (Player I B) :=
  (Finset.univ.filter fun q : I × Fin B => (q.2 : ℕ) < d i k q.1).image fun q => copyP q.1 q.2

/-- **The payoff of `G_R`**.
Source: FTC 2015 §5 (the displays for `u_i`, `f_{i,k}` and the copy/auxiliary tables)
Kind: D
Fidelity: exact (the copy/auxiliary tables are Lemma A.1's, with `a_i` as Matrix)
Hyps: n/a -/
noncomputable def gameRPayoff (c : I → K → ℝ) (d : I → K → I → ℕ) (p : I → ℝ)
    (a : Player I B → Fin 2) : Player I B → ℝ := fun q =>
  match q with
  | Sum.inl i =>
    if a (mainP i) = 1 then ∑ k, c i k * agreeInd (copies d i k) (fun _ => 1) a else p i
  | Sum.inr (Sum.inl ij) =>
    if a (copyP ij.1 ij.2) = a (auxP ij.1 ij.2) then 1 else 0
  | Sum.inr (Sum.inr ij) =>
    if a (mainP ij.1) = 0 then (if a (copyP ij.1 ij.2) = 1 ∧ a (auxP ij.1 ij.2) = 0 then 1 else 0)
    else (if a (copyP ij.1 ij.2) = 0 ∧ a (auxP ij.1 ij.2) = 1 then 1 else 0)

/-- **The game `G_R`** as a two-action game over EconCSLib.
Source: FTC 2015 Theorem 5.1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable abbrev gameR (c : I → K → ℝ) (d : I → K → I → ℕ) (p : I → ℝ) :
    StrategicGame (Player I B) ℝ :=
  twoActionGame (gameRPayoff (B := B) c d p)

/-- **Copy forcing**: at a mixed Nash equilibrium of `G_R`, every copy player mixes exactly as its
main player (Lemma A.1 applied to the triple `(copyP i j, auxP i j, mainP i)`).
Source: FTC 2015 §5 ("we show in Appendix A that at Nash equilibrium, these payoffs force
`s_{g(i,j)} = s_i`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem copy_forcing (c : I → K → ℝ) (d : I → K → I → ℕ) (p : I → ℝ)
    {σ : MixedProfile (gameR (B := B) c d p)} (h : IsMixedNashEq (gameR c d p) σ) (i : I)
    (j : Fin B) : (σ (copyP i j)).val 1 = (σ (mainP i)).val 1 :=
  pennies_gadget (gameRPayoff c d p) (row := copyP i j) (col := auxP i j) (mat := mainP i)
    (by simp) (by simp) (by simp) (fun _ => rfl) (fun _ => rfl) h

/-- The agreement indicator on `insert m T` when `τ m = v m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem agreeInd_insert_of_eq {N : Type*} [Fintype N] [DecidableEq N] {T : Finset N} {v τ : N → Fin 2} {m : N}
    (h : τ m = v m) : agreeInd (insert m T) v τ = agreeInd T v τ := by
  unfold agreeInd
  simp [h]

/-- The agreement indicator on `insert m T` vanishes when `τ m ≠ v m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem agreeInd_insert_of_ne {N : Type*} [Fintype N] [DecidableEq N] {T : Finset N} {v τ : N → Fin 2} {m : N}
    (h : τ m ≠ v m) : agreeInd (insert m T) v τ = 0 := by
  unfold agreeInd
  simp [h]

/-- The agreement indicator on a singleton.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem agreeInd_singleton {N : Type*} [Fintype N] [DecidableEq N] {v τ : N → Fin 2} {m : N} :
    agreeInd {m} v τ = if τ m = v m then 1 else 0 := by
  unfold agreeInd
  simp

/-- Main `i`'s payoff as a combination of agreement indicators.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem gameRPayoff_main (c : I → K → ℝ) (d : I → K → I → ℕ) (p : I → ℝ) (τ : Player I B → Fin 2)
    (i : I) :
    gameRPayoff c d p τ (mainP i) =
      (∑ k, c i k * agreeInd (insert (mainP i) (copies d i k)) (fun _ => 1) τ) +
        agreeInd {mainP i} (fun _ => 0) τ * p i := by
  show (if τ (mainP i) = 1 then ∑ k, c i k * agreeInd (copies d i k) (fun _ => 1) τ else p i) = _
  rw [agreeInd_singleton]
  by_cases h1 : τ (mainP i) = 1
  · have hk : ∀ k, agreeInd (insert (mainP i) (copies d i k)) (fun _ => 1) τ =
        agreeInd (copies d i k) (fun _ => 1) τ :=
      fun k => agreeInd_insert_of_eq (v := fun _ => 1) (T := copies d i k) h1
    simp only [h1, if_true, hk]
    simp
  · have h0 : τ (mainP i) = 0 := by
      have : ∀ t : Fin 2, t ≠ 1 → t = 0 := by decide
      exact this _ h1
    have hk : ∀ k, agreeInd (insert (mainP i) (copies d i k)) (fun _ => 1) τ = 0 :=
      fun k => agreeInd_insert_of_ne (v := fun _ => 1) (T := copies d i k) h1
    simp only [hk, h0, if_true]
    simp

omit [Fintype K] in
/-- The main player is not one of the copies.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mainP_not_mem_copies (d : I → K → I → ℕ) (i i' : I) (k : K) :
    mainP i ∉ copies (B := B) d i' k := by
  simp [copies]

/-- Main `i`'s raw expected payoff at any family of probability vectors.
Source: FTC 2015 §5 ("the expected payoff of strategy 1 to player `i` is exactly `P(M_i() = 1)`,
while the payoff of strategy 0 is always `p_i`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem rawEP_main (c : I → K → ℝ) (d : I → K → I → ℕ) (p : I → ℝ) (ρ : Player I B → Fin 2 → ℝ)
    (hρ : ∀ q, ∑ s, ρ q s = 1) (i : I) :
    rawEP (gameRPayoff c d p) ρ (mainP i) =
      (∑ k, c i k * ∏ q ∈ insert (mainP i) (copies d i k), ρ q 1) + p i * ρ (mainP i) 0 := by
  unfold rawEP
  simp_rw [gameRPayoff_main, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sum_prod_agreeInd ρ hρ (insert (mainP i) (copies d i k)) (fun _ => 1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · rw [← Finset.prod_singleton (fun j => ρ j 0) (mainP i),
      ← sum_prod_agreeInd ρ hρ {mainP i} (fun _ => 0), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring

/-- **Main `i`'s gain** is `∑ k, c i k * ∏ q ∈ copies d i k, x q − p i`.
Source: FTC 2015 §5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem gain_main (c : I → K → ℝ) (d : I → K → I → ℕ) (p : I → ℝ) (x : Player I B → ℝ) (i : I) :
    gain (gameRPayoff c d p) (mainP i) x = (∑ k, c i k * ∏ q ∈ copies d i k, x q) - p i := by
  unfold gain
  rw [rawEP_main c d p _ (sum_update_wt x (mainP i) 1) i,
    rawEP_main c d p _ (sum_update_wt x (mainP i) 0) i]
  have hins : ∀ (k : K) (s : Fin 2),
      ∏ q ∈ insert (mainP i) (copies d i k),
        Function.update (fun j => wt (x j)) (mainP i) (pureWt s) q 1 =
      pureWt s 1 * ∏ q ∈ copies d i k, x q := by
    intro k s
    rw [Finset.prod_insert (mainP_not_mem_copies d i i k), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq' : q ≠ mainP i := fun h => mainP_not_mem_copies d i i k (h ▸ hq)
    rw [Function.update_of_ne hq']
    rfl
  simp only [hins, Function.update_self]
  simp [pureWt]

omit [Fintype K] in
/-- **Independent copies give the powers**: if `x (copyP i' j) = y i'` for all `i', j`, then
`∏ q ∈ copies d i k, x q = ∏ i', y i' ^ d i k i'` (degrees bounded by `B`).
Source: FTC 2015 §5 ("the copy players will provide us with independent samples … allowing us to
simulate up to `B_R` independent calls")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem prod_copies (d : I → K → I → ℕ) (hd : ∀ i k i', d i k i' ≤ B) (x : Player I B → ℝ)
    (y : I → ℝ) (hx : ∀ i' (j : Fin B), x (copyP i' j) = y i') (i : I) (k : K) :
    ∏ q ∈ copies d i k, x q = ∏ i', y i' ^ d i k i' := by
  unfold copies
  rw [Finset.prod_image (fun a _ b _ h => by simpa [copyP] using h)]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i' _ => ?_
  simp only [hx]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
    Fin.card_filter_val_lt, min_eq_right (hd i k i')]

/-- **Target 15, Theorem 5.1 (abstract polynomial version)**: at every mixed Nash equilibrium `σ` of
`G_R`, the main players' answer vector `x i = (σ (mainP i)).val 1` is reflective for the polynomial
evaluation maps `polyEv c d` at the thresholds `p`. Proof: copy forcing makes main `i`'s gain
`polyEv c d i x − p i` (`gain_main`, `prod_copies`), and Theorem 4.1 (`isMixedNashEq_iff_reflective`)
turns the equilibrium conditions at the main players into the sign conditions.
Source: FTC 2015 Theorem 5.1; [[fixpoint-lit-2-inventory]] 007
Kind: P
Fidelity: variant: abstract (polynomial evaluation maps in place of bounded closed machines — the
paper's polynomial representation is a hypothesis here, finding F9); the oracle's answers off `R`
(`P(O_x(M,p) = 1) = 0`) have no abstract analogue
Hyps: (a) none — `hd` (degrees `≤ B`) is the paper's "bounded"; no sign or range condition on `c` is
needed for this direction; (c) evaluation maps in place of oracle machines -/
theorem gameR_nash_reflective (c : I → K → ℝ) (d : I → K → I → ℕ) (hd : ∀ i k i', d i k i' ≤ B)
    (p : I → ℝ) {σ : MixedProfile (gameR (B := B) c d p)} (h : IsMixedNashEq (gameR c d p) σ) :
    Reflective (polyEv c d) p (fun i => (σ (mainP i)).val 1) := by
  have hR := (isMixedNashEq_iff_reflective _ σ).1 h
  intro i
  have hi := hR (mainP i)
  have hgain : gain (gameRPayoff c d p) (mainP i) (toCube σ) =
      polyEv c d i (fun i => (σ (mainP i)).val 1) - p i := by
    rw [gain_main]
    unfold polyEv
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact prod_copies d hd (toCube σ) (fun i => (σ (mainP i)).val 1)
      (fun i' j => copy_forcing c d p h i' j) i k
  simp only [evOf, hgain, toCube] at hi
  exact ⟨fun hlt => hi.1 (by linarith), fun hlt => hi.2 (by linarith)⟩

/-- **Existence of polynomial reflective oracles through `G_R`** (the paper's route): a mixed Nash
equilibrium of `G_R` exists (`exists_isMixedNashEq`) and its main answer vector is reflective. This
route is *not* Kakutani-free: `exists_isMixedNashEq` rests on `exists_reflective`, i.e. on
`fix-kakutani`.
Source: FTC 2015 Theorem 5.1 ("the existence of oracles reflective on `R` follows from the existence
of Nash equilibria in `G_R`")
Kind: C
Fidelity: variant: abstract; the Nash existence used is itself Kakutani-based (see the ledger)
Hyps: (a) all; (c) evaluation maps in place of oracle machines -/
theorem exists_reflective_via_gameR (c : I → K → ℝ) (d : I → K → I → ℕ)
    (hd : ∀ i k i', d i k i' ≤ B) (p : I → ℝ) :
    ∃ σ : MixedProfile (gameR (B := B) c d p), IsMixedNashEq (gameR c d p) σ ∧
      Reflective (polyEv c d) p (fun i => (σ (mainP i)).val 1) := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNashEq (gameRPayoff (B := B) c d p)
  exact ⟨σ, hσ, gameR_nash_reflective c d hd p hσ⟩

/-! ### N+ witness of target 15: the liar through `G_R` -/

/-- Coefficients of the liar `ev x = 1 − x` as a polynomial: monomials `[1, −1]`.
Source: FTC 2015 §1 (the liar) as an instance of §5's polynomial form; audit round 1 (adversarial 3.3)
Kind: D
Fidelity: exact
Hyps: n/a -/
def liarC : Unit → Fin 2 → ℝ := fun _ => ![1, -1]

/-- Degrees of the liar as a polynomial: monomial `0` is the constant, monomial `1` is `x`.
Source: as `liarC`
Kind: D
Fidelity: exact
Hyps: n/a -/
def liarD : Unit → Fin 2 → Unit → ℕ := fun _ => ![fun _ => 0, fun _ => 1]

/-- `polyEv liarC liarD = liarEv`: the liar is a polynomial evaluation map of degree `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polyEv_liar : polyEv liarC liarD = liarEv := by
  funext i x
  simp [polyEv, liarC, liarD, liarEv, Fin.sum_univ_two]
  ring

/-- The liar's degrees are bounded by `B = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem liarD_le : ∀ i k i', liarD i k i' ≤ 1 := by
  intro i k i'
  fin_cases k <;> simp [liarD]

/-- **N+ witness of target 15**: in the liar's `G_R` (three players — main, one copy, one auxiliary;
`B = 1`), *every* mixed Nash equilibrium has the main player answering `1 − p`, for `p ∈ (0, 1)`: the
gadget forces the copy to the main player's mixture, the main player's gain is `(1 − x) − p`, and
`reflective_liar_iff` pins `x = 1 − p`. A concrete forcing that exercises the copy/auxiliary machinery
on a case checkable by hand.
Source: FTC 2015 Theorem 5.1 applied to the liar of §1; audit round 1 (adversarial 3.3)
Kind: N+
Fidelity: exact (for the abstract polynomial version)
Hyps: (a) none -/
theorem gameR_liar_forces_main {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {σ : MixedProfile (gameR (B := 1) liarC liarD (fun _ => p))}
    (h : IsMixedNashEq (gameR liarC liarD (fun _ => p)) σ) :
    (σ (mainP ())).val 1 = 1 - p := by
  have hR := gameR_nash_reflective liarC liarD liarD_le (fun _ => p) h
  rw [polyEv_liar] at hR
  have hx : (fun i : Unit => (σ (mainP i)).val 1) ∈ cube Unit := by
    intro i _
    have h0 := (σ (mainP i)).2.1 0
    have h1 := (σ (mainP i)).2.1 1
    have hs := (σ (mainP i)).2.2
    simp only [Fin.sum_univ_two] at hs
    exact ⟨h1, by linarith⟩
  exact (reflective_liar_iff hp hx).1 hR

/-- Such an equilibrium exists (`exists_isMixedNashEq`), so the forcing in `gameR_liar_forces_main` is
not vacuous.
Source: FTC 2015 Theorem 5.1 applied to the liar
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem gameR_liar_exists (p : ℝ) :
    ∃ σ : MixedProfile (gameR (B := 1) liarC liarD (fun _ => p)),
      IsMixedNashEq (gameR liarC liarD (fun _ => p)) σ :=
  exists_isMixedNashEq _

/-! ### Theorem 2.1 (ii) through `G_R`: reflective on `R`, prescribed off `R` — the analogue §5 omits

FTC §5 closes with "Theorem 5.1 is a special case of Theorem 2.1 (i). The proof can be adapted to
also show an analog of Theorem 2.1 (ii), but we omit the details here." The adaptation: substitute
the prescribed answers `x₀` off `R` into each polynomial, which leaves a polynomial in the
`R`-coordinates (`substOff`, `restrictDeg`, `polyEv_extendBy`), and build `G_R` for *that*
polynomial family on the query type `R`. Its Nash equilibria give answer vectors on `R` which,
extended by `x₀` off `R`, are reflective on `R` (`gameR_nash_reflectiveOn`) and agree with `x₀` off
`R` by construction. `exists_reflectiveOn_via_gameR` is the (Kakutani-based) existence;
`exists_reflectiveOn_via_gameR_brouwer` (`BrouwerOnly.lean`) the Brouwer-only twin. -/

/-- **Coefficients after substituting the prescribed answers off `R`**: for `i ∈ R`, monomial `k` of
`polyEv c d i` evaluated at `extendBy R x₀ y` has, in the `R`-coordinates `y`, the coefficient
`c i k * ∏ i' ∉ R, x₀ i' ^ d i k i'`.
Source: FTC 2015 §5 ("the proof can be adapted to also show an analog of Theorem 2.1 (ii)"): the
substitution the adaptation needs; repair round 2 (audit round 2, fidelity B1)
Kind: D
Fidelity: exact
Hyps: n/a -/
def substOff (R : Finset I) (x₀ : I → ℝ) (c : I → K → ℝ) (d : I → K → I → ℕ) : R → K → ℝ :=
  fun i k => c i k * ∏ i' ∈ Rᶜ, x₀ i' ^ d i k i'

/-- **Degrees restricted to the queries of `R`**.
Source: as `substOff`
Kind: D
Fidelity: exact
Hyps: n/a -/
def restrictDeg (R : Finset I) (d : I → K → I → ℕ) : R → K → R → ℕ :=
  fun i k i' => d i k i'

/-- **Re-expansion**: for `i ∈ R`, substituting `x₀` off `R` into the polynomial evaluation map
`polyEv c d i` gives the polynomial evaluation map `polyEv (substOff R x₀ c d) (restrictDeg R d)`
at `⟨i, hi⟩` in the `R`-coordinates: `polyEv c d i (extendBy R x₀ y) = polyEv (substOff R x₀ c d)
(restrictDeg R d) ⟨i, hi⟩ y`. (Split each monomial's product over `R` and `Rᶜ`.)
Source: FTC 2015 §5, the omitted adaptation; repair round 2
Kind: P
Fidelity: exact
Hyps: none -/
theorem polyEv_extendBy (c : I → K → ℝ) (d : I → K → I → ℕ) {R : Finset I} (x₀ : I → ℝ)
    (y : R → ℝ) {i : I} (hi : i ∈ R) :
    polyEv c d i (extendBy R x₀ y) = polyEv (substOff R x₀ c d) (restrictDeg R d) ⟨i, hi⟩ y := by
  unfold polyEv substOff restrictDeg
  refine Finset.sum_congr rfl fun k _ => ?_
  have hR : ∏ i' ∈ R, extendBy R x₀ y i' ^ d i k i' = ∏ i' : R, y i' ^ d i k i' := by
    rw [← Finset.prod_coe_sort R]
    exact Finset.prod_congr rfl fun i' _ => by rw [extendBy_apply_of_mem _ _ i'.2]
  have hRc : ∏ i' ∈ Rᶜ, extendBy R x₀ y i' ^ d i k i' = ∏ i' ∈ Rᶜ, x₀ i' ^ d i k i' :=
    Finset.prod_congr rfl fun i' hi' => by
      rw [extendBy_apply_of_not_mem _ _ (Finset.mem_compl.1 hi')]
  rw [← Finset.prod_mul_prod_compl R, hR, hRc]
  ring

/-- **Theorem 2.1 (ii) through `G_R`** (the analogue §5 omits): at every mixed Nash equilibrium of
`G_R` built for the polynomial family in the `R`-coordinates with the prescribed answers `x₀`
substituted off `R` (`substOff`, `restrictDeg`), the main players' answers, extended by `x₀` off
`R`, form a vector reflective on `R` for `polyEv c d` at `p` — and it agrees with `x₀` off `R` by
construction (`extendBy_apply_of_not_mem`). With `x₀ = 0` this is the paper's Theorem 5.1 shape
(`P(O_x(M,p) = 1) = 0` off `R`); with `x₀` arbitrary it is Theorem 2.1 (ii)'s.
Source: FTC 2015 §5 ("The proof can be adapted to also show an analog of Theorem 2.1 (ii), but we
omit the details here") — the omitted adaptation, in the abstract polynomial setting; repair round 2
(audit round 2, fidelity B1)
Kind: P
Fidelity: variant: abstract (polynomial representation as hypothesis class, F9; finite `R ⊆ I`, `I`
finite because `polyEv` is)
Hyps: (a) none — `hd` is the paper's "bounded"; (c) evaluation maps in place of oracle machines -/
theorem gameR_nash_reflectiveOn (R : Finset I) (x₀ : I → ℝ) (c : I → K → ℝ) (d : I → K → I → ℕ)
    (hd : ∀ i k i', d i k i' ≤ B) (p : I → ℝ)
    {σ : MixedProfile (gameR (B := B) (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i))}
    (h : IsMixedNashEq (gameR (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i)) σ) :
    ReflectiveOn R (polyEv c d) p (extendBy R x₀ (fun i : R => (σ (mainP i)).val 1)) := by
  intro i hi
  have hr := gameR_nash_reflective (substOff R x₀ c d) (restrictDeg R d)
    (fun i k i' => hd i k i') (fun i : R => p i) h ⟨i, hi⟩
  rw [polyEv_extendBy c d x₀ _ hi, extendBy_apply_of_mem _ _ hi]
  exact hr

/-- **Theorem 2.1 (ii) through `G_R`, existence** (Kakutani-based, via `exists_isMixedNashEq`; the
Brouwer-only twin is `exists_reflectiveOn_via_gameR_brouwer`): for polynomial evaluation maps,
finite `R ⊆ I` and prescribed `x₀ ∈ [0,1]^I`, a mixed Nash equilibrium of the substituted `G_R`
exists, and the vector it induces lies in the cube, agrees with `x₀` off `R` and is reflective on
`R`.
Source: FTC 2015 §5, the omitted Theorem 2.1 (ii) analogue; repair round 2
Kind: C
Fidelity: variant: abstract; **not Kakutani-free** (`exists_isMixedNashEq` rests on `exists_reflective`)
Hyps: (a) all; (c) evaluation maps in place of oracle machines -/
theorem exists_reflectiveOn_via_gameR (R : Finset I) (c : I → K → ℝ) (d : I → K → I → ℕ)
    (hd : ∀ i k i', d i k i' ≤ B) (p : I → ℝ) {x₀ : I → ℝ} (hx₀ : x₀ ∈ cube I) :
    ∃ σ : MixedProfile (gameR (B := B) (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i)),
      IsMixedNashEq (gameR (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i)) σ ∧
      extendBy R x₀ (fun i : R => (σ (mainP i)).val 1) ∈ cube I ∧
      (∀ i ∉ R, extendBy R x₀ (fun i : R => (σ (mainP i)).val 1) i = x₀ i) ∧
      ReflectiveOn R (polyEv c d) p (extendBy R x₀ (fun i : R => (σ (mainP i)).val 1)) := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNashEq
    (gameRPayoff (B := B) (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i))
  exact ⟨σ, hσ, extendBy_mem_cube hx₀ (fun i _ => toCube_mem_cube σ (mainP i) (mem_univ _)),
    fun i hi => extendBy_apply_of_not_mem _ _ hi, gameR_nash_reflectiveOn R x₀ c d hd p hσ⟩

/-! ### N+ witness: the prescription off `R` changes the answer forced on `R` -/

/-- Coefficients of `ev 0 x = 1 − x 0 · x 1` (the liar about query `0`, gated by query `1`) and
`ev 1 x = x 0`.
Source: none: infrastructure (witness of `gameR_nash_reflectiveOn`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def prodLiarC : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![1, 0]]

/-- Degrees of `prodLiarC`'s monomials: `1`, `x 0 · x 1`; `x 0`, `1`.
Source: as `prodLiarC`
Kind: D
Fidelity: exact
Hyps: n/a -/
def prodLiarD : Fin 2 → Fin 2 → Fin 2 → ℕ := ![![![0, 0], ![1, 1]], ![![1, 0], ![0, 0]]]

/-- `polyEv prodLiarC prodLiarD = ![fun x => 1 − x 0 * x 1, fun x => x 0]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polyEv_prodLiar :
    polyEv prodLiarC prodLiarD = ![fun x => 1 - x 0 * x 1, fun x => x 0] := by
  funext i x
  fin_cases i
  · simp [polyEv, prodLiarC, prodLiarD, Fin.sum_univ_two, Fin.prod_univ_two]
    ring
  · simp [polyEv, prodLiarC, prodLiarD, Fin.sum_univ_two, Fin.prod_univ_two]

/-- The degrees of `prodLiarD` are bounded by `B = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prodLiarD_le : ∀ i k i', prodLiarD i k i' ≤ 1 := by
  intro i k i'
  fin_cases i <;> fin_cases k <;> fin_cases i' <;> simp [prodLiarD]

/-- The sign conditions at the main player of the substituted `G_R` for `prodLiar` with `R = {0}`
and the prescription `x₀ = ![0, t]`: at every equilibrium, `x := (σ (mainP i)).val 1` satisfies
`p < 1 − x·t → x = 1` and `1 − x·t < p → x = 0`, and lies in `[0, 1]`.
Source: none: infrastructure (the common step of the two witnesses below)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prodLiar_main_conditions {p t : ℝ}
    {σ : MixedProfile (gameR (B := 1) (substOff {0} ![0, t] prodLiarC prodLiarD)
      (restrictDeg {0} prodLiarD) (fun _ => p))}
    (h : IsMixedNashEq (gameR (substOff {0} ![0, t] prodLiarC prodLiarD)
      (restrictDeg {0} prodLiarD) (fun _ => p)) σ)
    (i : ({0} : Finset (Fin 2))) :
    (σ (mainP i)).val 1 ∈ Icc (0 : ℝ) 1 ∧
      (p < 1 - (σ (mainP i)).val 1 * t → (σ (mainP i)).val 1 = 1) ∧
      (1 - (σ (mainP i)).val 1 * t < p → (σ (mainP i)).val 1 = 0) := by
  have hR := gameR_nash_reflectiveOn {0} ![0, t] prodLiarC prodLiarD prodLiarD_le (fun _ => p) h
  rw [polyEv_prodLiar] at hR
  have hi0 : (i : Fin 2) = 0 := Finset.mem_singleton.1 i.2
  have hi : i = ⟨0, Finset.mem_singleton_self 0⟩ := Subtype.ext hi0
  have h0 := hR 0 (Finset.mem_singleton_self 0)
  have hmem : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by simp
  simp only [Matrix.cons_val_zero] at h0
  rw [extendBy_apply_of_mem _ _ (Finset.mem_singleton_self 0), extendBy_apply_of_not_mem _ _ hmem]
    at h0
  simp only [Matrix.cons_val_one] at h0
  subst hi
  exact ⟨toCube_mem_cube σ (mainP _) (mem_univ _), h0.1, h0.2⟩

/-- **N+ witness of `gameR_nash_reflectiveOn`, prescription `x₀ 1 = 1`**: for `ev 0 x = 1 − x 0 · x 1`
with `R = {0}` and `p ∈ (0, 1)`, prescribing `x 1 = 1` makes the substituted game the liar's `G_R`,
and *every* mixed Nash equilibrium has the main player at `1 − p`.
Source: FTC 2015 §5's omitted Theorem 2.1 (ii) analogue, on an instance checkable by hand; repair
round 2
Kind: N+
Fidelity: exact (for the abstract polynomial version)
Hyps: (a) none -/
theorem gameR_prodLiar_forces_main_one {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {σ : MixedProfile (gameR (B := 1) (substOff {0} ![0, 1] prodLiarC prodLiarD)
      (restrictDeg {0} prodLiarD) (fun _ => p))}
    (h : IsMixedNashEq (gameR (substOff {0} ![0, 1] prodLiarC prodLiarD)
      (restrictDeg {0} prodLiarD) (fun _ => p)) σ) (i : ({0} : Finset (Fin 2))) :
    (σ (mainP i)).val 1 = 1 - p := by
  obtain ⟨hx, h1, h0⟩ := prodLiar_main_conditions h i
  rw [mul_one] at h1 h0
  rcases lt_trichotomy p (1 - (σ (mainP i)).val 1) with hlt | heq | hgt
  · have := h1 hlt
    linarith [hp.1]
  · linarith
  · have := h0 hgt
    linarith [hp.2]

/-- **N+ witness of `gameR_nash_reflectiveOn`, prescription `x₀ 1 = 0`**: the same `c`, `d`, `R`
and `p ∈ (0, 1)`, but prescribing `x 1 = 0` makes query `0` constantly `1 > p`, and *every* mixed
Nash equilibrium has the main player at `1`. So the answer forced on `R` depends on the answers
prescribed off `R` — the substitution `substOff` is doing real work.
Source: as `gameR_prodLiar_forces_main_one`
Kind: N+
Fidelity: exact (for the abstract polynomial version)
Hyps: (a) none -/
theorem gameR_prodLiar_forces_main_zero {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {σ : MixedProfile (gameR (B := 1) (substOff {0} ![0, 0] prodLiarC prodLiarD)
      (restrictDeg {0} prodLiarD) (fun _ => p))}
    (h : IsMixedNashEq (gameR (substOff {0} ![0, 0] prodLiarC prodLiarD)
      (restrictDeg {0} prodLiarD) (fun _ => p)) σ) (i : ({0} : Finset (Fin 2))) :
    (σ (mainP i)).val 1 = 1 := by
  obtain ⟨-, h1, -⟩ := prodLiar_main_conditions h i
  rw [mul_zero, sub_zero] at h1
  exact h1 hp.2

/-- Such equilibria exist (`exists_isMixedNashEq`), so the two forcings are not vacuous.
Source: as `gameR_prodLiar_forces_main_one`
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem gameR_prodLiar_exists (p t : ℝ) :
    ∃ σ : MixedProfile (gameR (B := 1) (substOff {0} ![0, t] prodLiarC prodLiarD)
      (restrictDeg {0} prodLiarD) (fun _ => p)),
      IsMixedNashEq (gameR (substOff {0} ![0, t] prodLiarC prodLiarD)
        (restrictDeg {0} prodLiarD) (fun _ => p)) σ :=
  exists_isMixedNashEq _

end Cleanroom.Fixpoint.FixOraclesCorresp
