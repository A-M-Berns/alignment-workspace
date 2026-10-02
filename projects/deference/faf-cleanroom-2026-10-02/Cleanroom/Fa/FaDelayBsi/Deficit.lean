import Cleanroom.Fa.FaDelayBsi.Split
import Cleanroom.Fa.FaDelayBsi.Locality

/-!
# `fa-delay-bsi` · Deficit (T4, finite-sum form): violations against the within-freeze update mass

The deficit bound T6 ([[delay-program]] §6 lines 252–260, root-fa-029 (Bound), vq-wiki-039 (b),
lean-deference-054 "surviving form"):
`∑_k w_{d_k} ≤ O(1) + (C/ε)·∑_k |𝔼^H_{d_k}(V) − 𝔼^H_{T_{k(d_k)}}(V)|`, `C = 2`, with **no frozen
term**. What this file proves is the split composed with `withinFreezeUpdate` over FAF's
`LUV.expect`: `∑_{k<K} w_{d_k} ≤ ∑_{k<K} w^{frozen}_{d_k} + (2/ε) ∑_{k<K} withinFreezeUpdate (d k)`
(kind `L`, exact to BSI's first display), in the plain and the refined (current-violation) forms.
The frozen-term-free bound is **not** the split minus a term (T3 refutes that route: the plain
frozen sum is not finite); it needs the v3 trader (`fa-forcing-trader`, outside this package's
import closure) and is stated OPEN in `Open.lean`.
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Finset

/-- **The live credence on day `n`** in the current question: `𝔼^H_n(X_{k(n)})`.
Source: BSI §1 (`ℙ^H_n(X_{k(n)})`)
Kind: D
Fidelity: exact (expectation of the block's LUV)
Hyps: n/a -/
noncomputable def liveCredence (S : FreezeSchedule) (H : History) (X : ℕ → LUV) (n : ℕ) : ℝ :=
  (X (S.blockOf n)).expect H n

/-- **The frozen credence on day `n`**: the human's credence in the current question at the last
freeze, `𝔼^H_{T_{k(n)}}(X_{k(n)})`.
Source: BSI §5 line 96 ("its credence at the last freeze, `ℙ^H_{T_{k(n)}}(X_{k(n)})`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def frozenCredence (S : FreezeSchedule) (H : History) (X : ℕ → LUV) (n : ℕ) : ℝ :=
  (X (S.blockOf n)).expect H (S.T (S.blockOf n))

/-- The within-freeze update mass is the live-minus-frozen displacement.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem withinFreezeUpdate_eq (S : FreezeSchedule) (H : History) (X : ℕ → LUV) (n : ℕ) :
    withinFreezeUpdate S H X n = |liveCredence S H X n - frozenCredence S H X n| := rfl

/-- On a freeze day the frozen credence is the live credence, so the update mass is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem withinFreezeUpdate_T (S : FreezeSchedule) (H : History) (X : ℕ → LUV) (k : ℕ) :
    withinFreezeUpdate S H X (S.T k) = 0 := by
  unfold withinFreezeUpdate
  rw [S.blockOf_T, sub_self, abs_zero]

/-- Under the **strict** `ClosesWithinBlocks`, the live credence at the horizon `f (d k)` (in the
question current *at the horizon*) is the realized credence `𝔼^H_{f(d_k)}(X_{k(d_k)})` of the
question current on the *scheduled* day — the question has not retired within the window. The
horizon is any day of the block of `d k` after `d k`; **BSI's own horizon `T_{k(d)+1}` is the next
block's first day and is excluded** (`not_closesWithinBlocks_of_horizon_T`; the off-by-one of
[[delay-and-visibility]] §3) — the last within-block day `T_{k+1} − 1` is the nearest instance.
At BSI's horizon the identification fails and the realized credence is the end-of-block credence
of the scheduled question (`realized_horizon_T`). (An earlier docstring called BSI's horizon "the
instance"; audit r1 adversarial B2 corrected it.)
Source: BSI §5 line 94; [[fa-delay-bsi-mandate]] Known issue 4
Kind: L
Fidelity: variant: horizon strictly inside the block (BSI's `T_{k+1}` excluded)
Hyps: (a) none -/
theorem liveCredence_horizon {S : FreezeSchedule} {f d : DeferralFunction}
    (h : ClosesWithinBlocks S f d) (H : History) (X : ℕ → LUV) (k : ℕ) :
    liveCredence S H X (f.f (d.f k)) = realized H f (fun n => X (S.blockOf n)) (d.f k) := by
  show (X (S.blockOf (f.f (d.f k)))).expect H (f.f (d.f k)) =
    (X (S.blockOf (d.f k))).expect H (f.f (d.f k))
  rw [h k]

/-- At BSI's horizon `f (d k) = T_{k(d k)+1}`, the realized credence of the scheduled question is
its **end-of-block** credence `𝔼^H_{T_{k+1}}(X_k)` — BSI's quote target `ℙ^H_{T_{k(n)+1}}(X_{k(n)})`
(§1 line 33). This is *not* `liveCredence` on that day (whose question is `X_{k+1}`): the
`realized` object, which `CrossQuotePackage` quotes, carries BSI's horizon correctly, and only
`liveCredence_horizon`'s identification needs the strict clause.
Source: BSI §1 line 33; BSI §5 line 94; audit r1 adversarial B2
Kind: L
Fidelity: exact (BSI's quote target at its own horizon)
Hyps: (a) none -/
theorem realized_horizon_T {S : FreezeSchedule} {f d : DeferralFunction} (H : History)
    (X : ℕ → LUV) (k : ℕ) (hk : f.f (d.f k) = S.T (S.blockOf (d.f k) + 1)) :
    realized H f (fun n => X (S.blockOf n)) (d.f k) =
      (X (S.blockOf (d.f k))).expect H (S.T (S.blockOf (d.f k) + 1)) := by
  show (X (S.blockOf (d.f k))).expect H (f.f (d.f k)) = _
  rw [hk]

/-- **T1 instance on a real object** (mandate T1 "Traps"; audit r1 adversarial non-blocking 7):
`fa-theorem-a`'s upper gate `Ind_δ(a_n > t)` (`quoteRampAbove`, a `PGenerableWeighting` of `A`'s
market by `quoteRampAbove_pgenerable`) has a day-`n` value depending only on `A`'s prices through
day `n` — `pgenerable_price_local` applied.
Source: [[fa-delay-bsi-mandate]] T1; `Cleanroom.Fa.FaTheoremA.quoteRampAbove_pgenerable`
Kind: L
Fidelity: exact (instance)
Hyps: (a) `hY` (the quote family is e.c.) -/
theorem quoteRampAbove_price_local (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (t δ : ℚ)
    (n : ℕ) (V V' : History) (h : ∀ m ≤ n, ∀ φ, V m φ = V' m φ) :
    (quoteRampAbove Y t δ n).denote V = (quoteRampAbove Y t δ n).denote V' :=
  pgenerable_price_local (quoteRampAbove_pgenerable Y hY t δ) n V V' h

/-- **T4 (headline), finite-sum form.** For any quote sequence `a`, any index map `d`, rationals
`t`, `ε > 0`, `δ > 0`, and `K` terms:
`∑_{k<K} violWeight (a_{d_k}) (𝔼^H_{d_k}(X_{k(d_k)})) ≤ ∑_{k<K} frozenWeight (a_{d_k}) (𝔼^H_{T_{k(d_k)}}(X_{k(d_k)})) + (2/ε) ∑_{k<K} withinFreezeUpdate S H X (d_k)`
— BSI Theorem C's first display over FAF's `LUV.expect`, the frozen term kept (T3 shows it
cannot be dropped by arithmetic).
Scope: sequence-level in the quote, `LUV.expect`-level in the credences; any index map.
Source: BSI §5 Theorem C first display (lean-deference-054); [[delay-program]] §6 T6 (root-fa-029 (Bound)); [[delay-and-visibility]] §5 (vq-wiki-039 (b))
Kind: L
Fidelity: exact (BSI's first display, finite sums)
Hyps: (a) none -/
theorem deficit_finite_sum (S : FreezeSchedule) (H : History) (X : ℕ → LUV) (a : ℕ → ℝ)
    (d : ℕ → ℕ) {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (K : ℕ) :
    ∑ k ∈ range K, violWeight t ε δ (a (d k)) (liveCredence S H X (d k)) ≤
      ∑ k ∈ range K, frozenWeight t ε δ (a (d k)) (frozenCredence S H X (d k)) +
        (2 / (ε : ℝ)) * ∑ k ∈ range K, withinFreezeUpdate S H X (d k) :=
  sum_violWeight_le hε hδ a (liveCredence S H X) (frozenCredence S H X) d K

/-- **T4, finite-sum form on the quote**: `deficit_finite_sum` at `a := quoteSeq Y A`
(`A`'s day-`n` expectation of the quote family `Y`), which is the deck's `accelerator Y A`.
Scope: as `deficit_finite_sum`; the quote is `A`'s market object, nothing is assumed about it.
Source: BSI §5 Theorem C first display; [[delay-program]] §6 T6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem deficit_finite_sum_quote (S : FreezeSchedule) (H A : History) (X Y : ℕ → LUV)
    (d : ℕ → ℕ) {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (K : ℕ) :
    ∑ k ∈ range K, violWeight t ε δ (quoteSeq Y A (d k)) (liveCredence S H X (d k)) ≤
      ∑ k ∈ range K, frozenWeight t ε δ (quoteSeq Y A (d k)) (frozenCredence S H X (d k)) +
        (2 / (ε : ℝ)) * ∑ k ∈ range K, withinFreezeUpdate S H X (d k) :=
  deficit_finite_sum S H X (quoteSeq Y A) d hε hδ K

/-- **T4, refined finite-sum form**: the frozen term restricted to current-violation days
(`liveCredence < t − ε`) — the shape whose first sum the v3 trader bounds (OPEN, `Open.lean`).
Scope: as `deficit_finite_sum`.
Source: BSI §5 line 100; [[delay-program]] §6 T6 (root-fa-029)
Kind: L
Fidelity: stronger: the frozen term carries the current-violation indicator
Hyps: (a) none -/
theorem deficit_finite_sum_live (S : FreezeSchedule) (H : History) (X : ℕ → LUV) (a : ℕ → ℝ)
    (d : ℕ → ℕ) {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (K : ℕ) :
    ∑ k ∈ range K, violWeight t ε δ (a (d k)) (liveCredence S H X (d k)) ≤
      ∑ k ∈ range K, frozenWeight t ε δ (a (d k)) (frozenCredence S H X (d k)) *
          (if liveCredence S H X (d k) < (t : ℝ) - ε then (1 : ℝ) else 0) +
        (2 / (ε : ℝ)) * ∑ k ∈ range K, withinFreezeUpdate S H X (d k) :=
  sum_violWeight_le_live hε hδ a (liveCredence S H X) (frozenCredence S H X) d K

end Cleanroom.Fa.FaDelayBsi
