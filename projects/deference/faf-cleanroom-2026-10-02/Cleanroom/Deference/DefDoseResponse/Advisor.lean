import Cleanroom.Deference.DefDoseResponse.Defs
import Cleanroom.Li.LiProjection.Prescribe
import Cleanroom.Found.LiQuoteLane.MirrorPair
import Cleanroom.Found.LiQuoteLane.Codes
import Cleanroom.Deference.DefTrackingPin.Pin

/-!
# `def-dose-response` · Advisor: the committed stream and the steered advisor (D4)

The note's committed stream is `a_n(u) := E^A_n(⌜E^{H^{(1)}}_{f(n)}(u)⌝_n)` (§2.3 step 1). Over FAF
(`li-quote-lane`'s mirror pair, scope **one-way, `A` reads `H`**): the advisor `A` is a market
over the mirror ledger process `ledgerProcess baseA (realizedExpectation M X f) σ`, whose item-`0`
ledger LUV `ledgerLuv 0 n` is determined at the production arm's realized day-`f n` expectation
of `X n` (`crossQuotePackage_mirror`); the **stream value** is `A`'s day-`n` expectation of that
LUV — as an exact rational through `A`'s market program (`quoteStream`, FAF's `expectQuoteAt`,
the same device `realizedExpectation` uses on `H`'s side), and as the real `quoteStreamR`
(`LUV.expect`), equal by `expectQuoteAt_cast`.

**The steered advisor** `steeredAdvisor A v N` is `li-projection`'s finite `patch` of `A` at the
mesh coordinates `(n, ⌜ledgerLuv 0 n > i/(n+1)⌝)`, `n < N`, `i ≤ n`, set to `1` below `v` and `0`
at or above it. It is a logical inductor **exactly** (`prescribe_finiteSupport`, FAF's corrected
`thm:ifp`), and its day-`n` quote of the `u`-column for `n < N` is the mesh rounding of `v`
(`steeredAdvisor_quote`), which **is `v`** when `v` is exact at the day-`n` mesh, i.e.
`v = k/(n+1)` for some `k ≤ n+1` (`steeredAdvisor_quote_exact`). This is where finding **F6**
lives: "steering targets dyadic" (note §2.1) does not make the prescription exact at a
non-dyadic mesh (the day-`2` mesh is thirds: at `v = ½` the quote is `2/3`,
`steeredAdvisor_half_day_two` — the rounding is the ceiling `⌈v(n+1)⌉/(n+1)`, not the mandate's
floor); exactness at every mesh `≤ N` needs `v`'s denominator to divide `lcm(1, …, N)`, and the
witness of `Witnesses.lean` takes `v = 1`. Days `≥ N` are untouched (`steeredAdvisor_unmodified`).

**The mirror-ledger pinning** `mirror_quote_tendsto` is the engine of T2(b-half): for any
inductor over the mirror ledger of a market `H` whose day-`f n` expectations of `X n` converge
to `L`, the quote stream converges to `L` (`def-tracking-pin`'s `pinning_tendsto`, grade (a)).
`Steering.lean` instantiates `H` with the production arm.
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefTrackingPin
open Filter Topology

/-! ## The committed stream -/

/-- **The quote LUV family**: item `0` of the advisor's ledger, `⌜𝔼^H_{f n}(X n)⌝` of `A`'s language.
Source: [[dose-response]] §2.3 step 1 (the LUV naming the lookahead expectation); `li-quote-lane` T2.4
Kind: D
Fidelity: exact (`li-quote-lane`'s `ledgerLuv 0`)
Hyps: n/a -/
abbrev quoteLuv : ℕ → LUV := fun n => ledgerLuv 0 n

/-- **The committed stream, exact rational form**: `A`'s day-`n` expectation of the day-`n` quote
LUV, computed through `A`'s market program (FAF's `MarketComputation.expectQuoteAt`).
Source: [[dose-response]] §2.3 step 1 ("`a_n(X) := E^A_n(⌜E^{H^{(1)}}_{f(n)}(X)⌝_n)`"); mandate D4
Kind: D
Fidelity: exact
Hyps: n/a -/
def quoteStream {A : History} (MA : MarketComputation A) (n : ℕ) : ℚ :=
  MA.expectQuoteAt quoteLuv n n

/-- **The committed stream, real form**: `𝔼^A_n(ledgerLuv 0 n)`.
Source: [[dose-response]] §2.3 step 1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def quoteStreamR (A : History) (n : ℕ) : ℝ := (quoteLuv n).expect A n

/-- The rational stream casts to the real one (FAF's `expectQuoteAt_cast`).
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteStream_cast {A : History} (MA : MarketComputation A) (n : ℕ) :
    (quoteStream MA n : ℝ) = quoteStreamR A n :=
  (MA.expectQuoteAt_cast quoteLuv n n).symm

/-- The stream is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteStream_mem {A : History} (MA : MarketComputation A) (n : ℕ) :
    0 ≤ quoteStream MA n ∧ quoteStream MA n ≤ 1 :=
  MA.expectQuoteAt_mem_Icc quoteLuv n n

/-- **The committed stream is computable** — the hypothesis `armBase_isLogicalInductor` needs of
the stream the arms read: FAF's `MarketComputation.expectQuoteAt_computable` at the e.c.
certificate `ledgerLuv_thresholdCodes 0`, on the diagonal `(n, n)` (as `li-quote-lane`'s
`realizedExpectation_computable`).
Source: mandate D4 ("exact rationals through `A`'s market program"); adversarial audit r2 N2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteStream_computable {A : History} (MA : MarketComputation A) :
    Computable (quoteStream MA) :=
  ((MA.expectQuoteAt_computable (ledgerLuv_thresholdCodes 0)).comp
    (Computable.id.pair Computable.id)).of_eq fun _ => rfl

/-! ## The mirror-ledger pinning (the engine of T2(b-half)) -/

/-- **The advisor's quote converges to the arm's destination.** For any inductor `A` over the
mirror ledger of a market `H` (`A` reads `H`'s realized day-`f n` expectations of `X n`, every stage
satisfiable), if those expectations converge to `L` then `A`'s quote stream converges to `L`:
`def-tracking-pin`'s convergent-target pinning on the ledger family determined at the realized
values (`crossQuotePackage_mirror`'s `reflected`). No generability of anything. Scope: one-way
(`A` reads a fixed `H`).
Source: [[dose-response]] §6.3 T2(b) ("the quote stream converges pointwise … apply [LI 4.8.10] in both directions"); anson-054; `def-tracking-pin` T3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem mirror_quote_tendsto {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (baseA : DeductiveProcess) (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (ledgerProcess baseA (realizedExpectation M X f) σ)]
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess baseA (realizedExpectation M X f) σ).D n))
    {L : ℝ} (hconv : Tendsto (fun n => (X n).expect H (f.f n)) atTop (𝓝 L)) :
    Tendsto (quoteStreamR A) atTop (𝓝 L) :=
  pinning_tendsto (ledgerLuv_thresholdCodes 0) hworldA
    (fun n => (crossQuotePackage_mirror M X f baseA σ).reflected n) hconv

/-! ## The steered advisor -/

/-- The threshold sentences of the `u`-column's ledger LUV are injective in the threshold.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerLuv_gt_injective (j n : ℕ) : Function.Injective (ledgerLuv j n).gt := by
  intro r r' h
  rw [ledgerLuv_gt, ledgerLuv_gt] at h
  unfold freshAtom at h
  have h1 : freshAtomCode ledgerFamily (ledgerPayload j n (Encodable.encode r)) =
      freshAtomCode ledgerFamily (ledgerPayload j n (Encodable.encode r')) := Formula.atom.inj h
  have h2 : (ledgerFamily, ledgerPayload j n (Encodable.encode r)) =
      (ledgerFamily, ledgerPayload j n (Encodable.encode r')) :=
    @freshAtomCode_injective (ledgerFamily, _) (ledgerFamily, _) h1
  have h3 := (ledgerPayload_inj.mp (Prod.mk.inj h2).2).2.2
  exact Encodable.encode_injective h3

/-- The mesh coordinates of the `u`-column on the steering days: `(n, ⌜ledgerLuv 0 n > i/(n+1)⌝)`
for `n < N`, `i ≤ n`.
Source: [[dose-response]] §6.2 ("prices on the day-`n` quote LUVs for `u`, `n < N*`"); mandate D4
Kind: D
Fidelity: exact (the day-`n` expectation reads exactly these `n+1` thresholds)
Hyps: n/a -/
def steeredSet (N : ℕ) : Finset (ℕ × Sentence) :=
  (Finset.range N).biUnion fun n =>
    (Finset.range (n + 1)).image fun i : ℕ => (n, (quoteLuv n).gt ((i : ℚ) / ((n : ℚ) + 1)))

/-- The prescribed table: `1` at a mesh threshold below `v`, `0` elsewhere.
Source: [[dose-response]] §6.2 (the steered advisor's prices); mandate D4
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def steeredTable (v : ℚ) : ℕ → Sentence → ℚ := fun n φ =>
  by classical exact
    if ∃ i, i ≤ n ∧ φ = (quoteLuv n).gt ((i : ℚ) / ((n : ℚ) + 1)) ∧ (i : ℚ) / ((n : ℚ) + 1) < v
    then 1 else 0

/-- **The steered advisor** `A_v`: `A` with its mesh prices of the `u`-column on days `< N` set to
the indicator of "threshold below `v`"; unmodified otherwise.
Source: [[dose-response]] §6.2 ("Steered advisor `A_v` … whose prices on the day-`n` quote LUVs for `u`, `n < N*`, are `v` … unmodified otherwise")
Kind: D
Fidelity: variant: the finite-support reading of Lemma 4.3 (the whole-day reading is refuted, `li-projection` T3.2)
Hyps: n/a -/
noncomputable def steeredAdvisor (A : History) (v : ℚ) (N : ℕ) : History :=
  patch A (steeredSet N) (steeredTable v)

/-- The prescribed table is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem steeredTable_mem (v : ℚ) (n : ℕ) (φ : Sentence) :
    0 ≤ steeredTable v n φ ∧ steeredTable v n φ ≤ 1 := by
  unfold steeredTable
  split_ifs <;> norm_num

/-- **T2(c)'s surviving neighbour (headline): the steered advisor is a logical inductor,
exactly** — `li-projection`'s `prescribe_finiteSupport` (FAF's corrected `thm:ifp`): the served
pair *is* a pair of inductors with the steered prefix; there is no criterion the pair violates.
`v` is unconstrained here (the patched table is an indicator, `steeredTable_mem`); the
*exact-prescription* reading — the prefix quotes equal to `v` — additionally needs `v` mesh-exact
on every steering day (`steeredAdvisor_quote_exact`, F6). What is refuted by `li-projection`
(`prescribe_wholeDay_closure_false`) is the whole-day *closure step* the note's proof of Lemma
4.3 invokes, not T2(c)'s conclusion, which this theorem proves in the finite-support variant.
Source: [[dose-response]] §6.2 ("`A_v` *is* an inductor outright ([LI 4.6.1])"), §6.3 T2(c); anson-054; `li-projection` T3.1
Kind: C
Fidelity: variant: finite-support prescription (the mesh coordinates the day-`n` expectation reads) in place of the note's whole-day overwrite, whose closure reading is false (`prescribe_wholeDay_closure_false`)
Hyps: (a) none -/
theorem steeredAdvisor_isLogicalInductor (A : History) (DP : DeductiveProcess)
    [IsLogicalInductor A DP] (v : ℚ) (N : ℕ) : IsLogicalInductor (steeredAdvisor A v N) DP :=
  prescribe_finiteSupport A DP (steeredSet N) (steeredTable v)
    (fun p _ => steeredTable_mem v p.1 p.2)

/-- The steered advisor is unmodified from day `N` on.
Source: [[dose-response]] §6.2 ("unmodified otherwise")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem steeredAdvisor_unmodified (A : History) (v : ℚ) {N n : ℕ} (hn : N ≤ n) (φ : Sentence) :
    steeredAdvisor A v N n φ = A n φ := by
  unfold steeredAdvisor
  apply patch_notMem
  intro h
  unfold steeredSet at h
  rw [Finset.mem_biUnion] at h
  obtain ⟨m, hm, hmem⟩ := h
  rw [Finset.mem_image] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  have := (Prod.mk.inj hi).1
  rw [Finset.mem_range] at hm
  omega

/-- The steered advisor is unmodified off the `u`-column's mesh thresholds.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem steeredAdvisor_unmodified_of_ne (A : History) (v : ℚ) (N n : ℕ) {φ : Sentence}
    (hφ : ∀ i, i ≤ n → φ ≠ (quoteLuv n).gt ((i : ℚ) / ((n : ℚ) + 1))) :
    steeredAdvisor A v N n φ = A n φ := by
  unfold steeredAdvisor
  apply patch_notMem
  intro h
  unfold steeredSet at h
  rw [Finset.mem_biUnion] at h
  obtain ⟨m, _, hmem⟩ := h
  rw [Finset.mem_image] at hmem
  obtain ⟨i, hi, hiφ⟩ := hmem
  obtain ⟨rfl, hφ'⟩ := Prod.mk.inj hiφ
  rw [Finset.mem_range] at hi
  exact hφ i (by omega) hφ'.symm

/-- The prescribed table at a mesh threshold of day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem steeredTable_gt (v : ℚ) {n i : ℕ} (hi : i ≤ n) :
    steeredTable v n ((quoteLuv n).gt ((i : ℚ) / ((n : ℚ) + 1))) =
      if (i : ℚ) / ((n : ℚ) + 1) < v then 1 else 0 := by
  unfold steeredTable
  by_cases hv : (i : ℚ) / ((n : ℚ) + 1) < v
  · rw [if_pos ⟨i, hi, rfl, hv⟩, if_pos hv]
  · rw [if_neg, if_neg hv]
    rintro ⟨i', _, hφ, hv'⟩
    have h1 := ledgerLuv_gt_injective 0 n hφ
    have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    have : (i : ℚ) = i' := by
      have := congrArg (fun x => x * ((n : ℚ) + 1)) h1
      simpa [div_mul_cancel₀, hpos.ne'] using this
    exact hv (this ▸ hv')

/-- **The steered advisor's quote on a steering day is the mesh rounding of `v`**: for `n < N`,
`𝔼^{A_v}_n(ledgerLuv 0 n) = #{i ≤ n : i/(n+1) < v}/(n+1)`.
Source: [[dose-response]] §6.2 ("the committed stream has `a_n(u) = v` for `n < N*`"); mandate D4 (the rounding trap)
Kind: P
Fidelity: exact (the rounding made explicit)
Hyps: (a) none -/
theorem steeredAdvisor_quote (A : History) (v : ℚ) {N n : ℕ} (hn : n < N) :
    quoteStreamR (steeredAdvisor A v N) n =
      (((Finset.range (n + 1)).filter fun i : ℕ => (i : ℚ) / ((n : ℚ) + 1) < v).card : ℝ) /
        ((n : ℝ) + 1) := by
  unfold quoteStreamR
  simp only [LUV.expect, LUV.expectApprox]
  have hmem : ∀ i ∈ Finset.range (n + 1),
      steeredAdvisor A v N n ((quoteLuv n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) =
        if (i : ℚ) / ((n : ℚ) + 1) < v then (1 : ℝ) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
    rw [hcast]
    unfold steeredAdvisor
    rw [patch_mem _ _ _ (by
      unfold steeredSet
      rw [Finset.mem_biUnion]
      exact ⟨n, Finset.mem_range.mpr hn, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩⟩),
      steeredTable_gt v (Nat.lt_succ_iff.mp hi)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hmem, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- The count of mesh points below `k/(n+1)` is `k`, for `k ≤ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem card_mesh_below (n k : ℕ) (hk : k ≤ n + 1) :
    ((Finset.range (n + 1)).filter fun i : ℕ => (i : ℚ) / ((n : ℚ) + 1) < (k : ℚ) / ((n : ℚ) + 1)).card
      = k := by
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have : ((Finset.range (n + 1)).filter fun i : ℕ => (i : ℚ) / ((n : ℚ) + 1) < (k : ℚ) / ((n : ℚ) + 1))
      = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [div_lt_div_iff_of_pos_right hpos, Nat.cast_lt]
    omega
  rw [this, Finset.card_range]

/-- **The prescription is exact at an exact mesh point (headline).** If `v = k/(n+1)` with
`k ≤ n+1` then the steered advisor's day-`n` quote of the `u`-column is exactly `v`, for `n < N`.
With `v` exact at every mesh `≤ N` (e.g. `v = 0`, `v = 1`, or any `v` whose denominator divides
`lcm(1, …, N)`), the committed stream has `a_n(u) = v` on every steering day — the hypothesis of
`non_attribution` and T2.
Source: [[dose-response]] §6.2 ("the committed stream has `a_n(u) = v` for `n < N*`"); mandate D4; finding F6
Kind: C
Fidelity: exact under the mesh-exactness hypothesis (the note's "dyadic" is not enough — F6)
Hyps: (a) none -/
theorem steeredAdvisor_quote_exact (A : History) {v : ℚ} {N n : ℕ} (hn : n < N) {k : ℕ}
    (hk : k ≤ n + 1) (hv : v = (k : ℚ) / ((n : ℚ) + 1)) :
    quoteStreamR (steeredAdvisor A v N) n = (v : ℝ) := by
  rw [steeredAdvisor_quote A v hn, hv, card_mesh_below n k hk]
  push_cast
  ring

/-- The steered advisor's rational quote (through any market program for it) is exactly `v` on an
exact steering day. (The mandate's D4 writes the rounding as `⌊v(n+1)⌋/(n+1)`; the actual
rounding, `steeredAdvisor_quote`, counts the mesh points *strictly below* `v`, which is
`⌈v(n+1)⌉/(n+1)` — a ceiling, not a floor; repair round 1, fidelity B3. At an exact mesh point the
two agree, which is all this lemma uses.)
Source: mandate D4 (the exact-prescription clause for `n < N*`); finding F6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteStream_steeredAdvisor_exact {A : History} {v : ℚ} {N : ℕ}
    (MS : MarketComputation (steeredAdvisor A v N)) {n : ℕ} (hn : n < N) {k : ℕ}
    (hk : k ≤ n + 1) (hv : v = (k : ℚ) / ((n : ℚ) + 1)) : quoteStream MS n = v := by
  have h := quoteStream_cast MS n
  rw [steeredAdvisor_quote_exact A hn hk hv] at h
  exact_mod_cast h

/-- **F6's worked instance: a dyadic target is not exact at a non-dyadic mesh, and the rounding
is a ceiling.** At `v = ½` on day `2` (mesh thirds) the thresholds `0` and `1/3` lie below `½`
and `2/3` does not, so the steered quote is `2/3` — not `½`, and not the floor `1/3`.
Source: finding F6; the fidelity audit's probe `MeshRounding.lean` (repair round 1, B3)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem steeredAdvisor_half_day_two (A : History) :
    quoteStreamR (steeredAdvisor A (1 / 2) 3) 2 = 2 / 3 := by
  rw [steeredAdvisor_quote A (1 / 2) (by norm_num : 2 < 3)]
  have h : ((Finset.range (2 + 1)).filter fun i : ℕ => (i : ℚ) / (((2 : ℕ) : ℚ) + 1) < 1 / 2)
      = (Finset.range (2 + 1)).filter fun i : ℕ =>
          (i : ℚ) / (((2 : ℕ) : ℚ) + 1) < ((2 : ℕ) : ℚ) / (((2 : ℕ) : ℚ) + 1) := by
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    interval_cases i <;> norm_num
  rw [h, card_mesh_below 2 2 (by norm_num)]
  norm_num

end Cleanroom.Deference.DefDoseResponse
