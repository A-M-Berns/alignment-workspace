import Cleanroom.Bli.BliExactness.Liar

/-!
# `bli-exactness` — X1 (d3): a `ℙ`-liar for the BLI market itself (conditional on bli-assemble)

The mandate expected (d3) to be OPEN: "a `ℙ`-state atom restores the liar … the FAF form needs
B1 as a `MarketComputation` with a quote code (bli-assemble's OPEN `bliOv_computableTable`)".
It is **provable conditional on exactly that hypothesis**: FAF's diagonal constructor
`parameterizedDiagonalQuoteCodeOfMarket` takes *any* `MarketComputation` and produces a public
atom reflected, in every completed-theory world of `paperDP 𝗜𝚺₁`, as "this market's own
same-day price of me is below `p`" (`parameterizedDiagonalQuoteCodeOfMarket_public_price_iff`) —
the theory `𝗜𝚺₁` proves the universal quote schemas for every code, so no extension of the
deductive process is needed. Hence:

* `marketLiar M p m` — the liar of **any** computable market `P` (from a `MarketComputation P`),
  with `marketLiar_reflected`;
* `market_never_exact_on_liar` — no computable market is ever exactly right about its own liar
  (X2 (ii) generalized from the LIA to every `MarketComputation`);
* `bli_liar_restoration` — **if** `bliHistory Q 𝓜 sk c` is a `ComputableMarket` (which
  bli-assemble's open target would deliver at the dyadic mesh and write-out coding for a
  computable base), there is a sentence family reflected as "`ℙ_m(L_m) < p`" about the BLI
  market's own price, and `bli_never_exact_on_own_liar`: B1 then prices its own liar wrongly in
  every completed-theory world, on every day. So the escape of X1 (d1)–(d2) (B1 prices the
  *paper* liar by its base and `E2x`'s scope excludes it) is an escape from the *base's* liar
  only: a liar about `ℙ` itself bites `ℙ` as soon as `ℙ` is a market in FAF's sense. This is the
  **same-day** form (X2's shape); the cell-reflection form of X1 (b) about `ℙ_m` is not stated.

The hypothesis `ComputableMarket (bliHistory …)` is carried explicitly (ledger status
`partial: conditional on bli-assemble OPEN`; see `bli_liar_restoration`'s docstring for exactly
which open statement implies it and at which parameters); nothing here uses `sorry`. **This module
contains no open statement.** The package's open items (X5 (v), X7-LI) are prose entries in
`run/wp/bli-exactness/bli-exactness-open.txt` and the report, not Lean statements (report § Open).
-/

namespace Cleanroom.Bli.BliExactness

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

/-- **The liar of an arbitrary computable market**: FAF's public diagonal atom built from a
`MarketComputation P` over `𝗜𝚺₁` at threshold `p` — "`P`'s own day-`m` price of me is below `p`".
At `M := paperMarketComputation T` this is `liar T p m`.
Source: FAF `parameterizedDiagonalQuoteCodeOfMarket` (`Construction/Quotation/Packages.lean:1223`);
mandate X1 (d3)
Kind: D
Fidelity: exact -/
noncomputable def marketLiar {P : History} (M : MarketComputation P) (p : ℚ) (m : ℕ) : Sentence :=
  (parameterizedDiagonalQuoteCodeOfMarket M 𝗜𝚺₁ p).toBooleanQuoteCode.sentence m

/-- **Reflection of a market's liar**: in every completed-theory world of `paperDP 𝗜𝚺₁`,
`marketLiar M p m` holds iff `P m (marketLiar M p m) < p` — the market's own real price.
Source: FAF `BooleanQuoteCode.reflected` at `paperQuotationPresentation 𝗜𝚺₁`,
`parameterizedDiagonalQuoteCodeOfMarket_public_price_iff`
Kind: L (FAF composition of two lemmas; regraded from C in repair r1)
Fidelity: exact
Hyps: (a) -/
theorem marketLiar_reflected {P : History} (M : MarketComputation P) (p : ℚ) (m : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    v.Holds (marketLiar M p m) ↔ P m (marketLiar M p m) < (p : ℝ) :=
  ((parameterizedDiagonalQuoteCodeOfMarket M 𝗜𝚺₁ p).toBooleanQuoteCode.reflected
    (paperQuotationPresentation 𝗜𝚺₁) m v hv).trans
    (parameterizedDiagonalQuoteCodeOfMarket_public_price_iff M 𝗜𝚺₁ p m)

/-- **No computable market is exactly right about its own liar** (X2 (ii) for every
`MarketComputation`): on every day and in every completed-theory world,
`P m (marketLiar M p m) ≠ v.payout (marketLiar M p m)` for `p ∈ (0, 1]`.
Source: mandate X2 (ii), X1 (d3); `no_sharp_fixed_point`
Kind: C
Fidelity: stronger: any computable market, not only the LIA
Hyps: (a) -/
theorem market_never_exact_on_liar {P : History} (M : MarketComputation P) {p : ℚ} (hp₀ : 0 < p)
    (hp₁ : p ≤ 1) (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    P m (marketLiar M p m) ≠ v.payout (marketLiar M p m) := by
  intro heq
  have hpay : v.payout (marketLiar M p m) = if P m (marketLiar M p m) < (p : ℝ) then 1 else 0 := by
    unfold PCWorld.payout
    rw [marketLiar_reflected M p m v hv]
  rw [hpay] at heq
  exact no_sharp_fixed_point (p : ℝ) (by exact_mod_cast hp₀) (by exact_mod_cast hp₁) ⟨_, heq⟩

/-- **X1 (d3) — a `ℙ`-liar for the BLI market, conditional on B1 being a computable market**: if
`bliHistory Q 𝓜 sk c` is a `ComputableMarket`, there is a sentence family `L` reflected in every
completed-theory world of `paperDP 𝗜𝚺₁` as "`ℙ_m(L_m) < p`" about the BLI market's **own** price.
No extension of the deductive process is needed: `𝗜𝚺₁` proves the universal quote schemas for
every code. **What this is and is not** (audit r1 N1/N5): it is the *same-day* (X2-shaped) liar
about `ℙ`'s own price — the cell-reflection form of X1 (b) for `ℙ` (cells about `ℙ_m`, `n < m`)
would need `ℙ`'s interval quote code and is not stated. The hypothesis `hQ` is for arbitrary
`Q 𝓜 sk c` and is false for a noncomputable base; bli-assemble's OPEN `bliOv_computableTable`
(`ComputableTable Q → ComputableTable (bliOv Q dyadicMesh (tentSkeleton …) (writeOutCoding …))`)
would deliver it at those parameters, for a computable base that is an inductor, through
`bliHistory_isLogicalInductor_of … |>.marketComputable` (which also needs a `SpliceCertificate`,
itself OPEN there). For other `𝓜`, `sk`, `c` no package states it. The reading "`L_m` is a
liar" needs `0 < p ≤ 1` (for `p > 1` the reflected sentence is simply true everywhere); the
reflection itself holds for every `p`.
Source: mandate X1 (d3) ("state it OPEN with that pointer"); FAF `parameterizedDiagonalQuoteCodeOfMarket`
Kind: C
Fidelity: exact (conditional; same-day form)
Hyps: (b′) `hQ` — a sibling-package OPEN, carried explicitly: implied by bli-assemble's L2 row at
`dyadicMesh`/`tentSkeleton`/`writeOutCoding` once its two OPEN obligations land (STANDARDS §3 has
no bin for this; "(b′)" marks the pattern for the consolidator, audit r2 fidelity N4) -/
theorem bli_liar_restoration (Q : BliFinite.RatHistory) (𝓜 : BliFinite.Mesh)
    (sk : BliFinite.Skeleton smallIndex 𝓜.d)
    (c : StateCoding 𝓜) (hQ : ComputableMarket (bliHistory Q 𝓜 sk c)) (p : ℚ) :
    ∃ L : ℕ → Sentence, ∀ (m : ℕ) (v : PCWorld), v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      (v.Holds (L m) ↔ bliHistory Q 𝓜 sk c m (L m) < (p : ℝ)) := by
  obtain ⟨M⟩ := hQ.nonemptyComputation
  exact ⟨marketLiar M p, fun m v hv => marketLiar_reflected M p m v hv⟩

/-- **B1 is never exactly right about its own liar** (conditional on bli-assemble): under the same
hypothesis, the restored liar is priced by `bliHistory` at a value differing from its truth value
in every completed-theory world, on every day. The escape of (d1)–(d2) is from the *base's* liar
only.
Source: mandate X1 (d3); X2 (ii)
Kind: C
Fidelity: exact (conditional)
Hyps: `hQ` as `bli_liar_restoration` -/
theorem bli_never_exact_on_own_liar (Q : BliFinite.RatHistory) (𝓜 : BliFinite.Mesh)
    (sk : BliFinite.Skeleton smallIndex 𝓜.d)
    (c : StateCoding 𝓜) (hQ : ComputableMarket (bliHistory Q 𝓜 sk c)) {p : ℚ} (hp₀ : 0 < p)
    (hp₁ : p ≤ 1) :
    ∃ L : ℕ → Sentence, ∀ (m : ℕ) (v : PCWorld), v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      (v.Holds (L m) ↔ bliHistory Q 𝓜 sk c m (L m) < (p : ℝ)) ∧
      bliHistory Q 𝓜 sk c m (L m) ≠ v.payout (L m) := by
  obtain ⟨M⟩ := hQ.nonemptyComputation
  exact ⟨marketLiar M p, fun m v hv =>
    ⟨marketLiar_reflected M p m v hv, market_never_exact_on_liar M hp₀ hp₁ m v hv⟩⟩

end Cleanroom.Bli.BliExactness
