import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Expectations
import LogicalInduction.Properties.Calibration

/-!
# `fa-delay-bsi` · Locality (T1): generators read prices, not the deductive state — and the constant route they do have

The **price-route half** of the refutation of BSI's Theorem B ([[delay-and-visibility]] §3,
[[delay-program]] §3, root-fa-028, lean-deference-053, vq-wiki-036). BSI's Lemma 3 asserts a
human-side target `p^H_n` (`¼` pre-mid, the decided truth value `σ_k` post-mid) is generable
because the post-mid branch "reads decided atoms, a hard constant for the poly-time generator".
Over FAF, a generable rational sequence is one denoted day by day by an expressible-feature
progression (`GeneratedRatFeature`, `PGenerableRat`); an expressible feature (`EF`) is built from
**price** features, rational constants, `+`, `×`, `max`, safe reciprocal and shared `let`, and
`EF.denote : EF → History → ℝ` takes no deductive process. A generable target therefore has
exactly two kinds of input: the market's prices through the day (the locality lemmas below) and
the **emitted syntax itself** — in particular constant leaves `EF.const (q n)`.

What this file proves is the price-route half: a feature's denotation depends only on the prices
on days `≤ rank` (`EF.denote_eq_of_agree`), a `PGenerableWeighting`'s day-`n` value only on prices
on days `≤ n` (`pgenerable_price_local`), and a generable target's day-`n` value is fixed by the
market's own prices through day `n` *together with the day-`n` feature* (`generatedRat_price_local`).
So if `σ_{k(n)}` is read off `H`'s prices, `H`'s prices already carry it (by a margin, when read
through a ramp), and Theorem 4.4.5 with that target concludes what it assumes.

What this file does **not** prove, and no lemma here touches (audit r1, fidelity B1): BSI's
actual move is the **constant route**. FAF admits
`PGenerableRat.ofMachineRatCodes : MachineRatCodes q → ∀ P, PGenerableRat P q` through the
constant leaf `ratCodeFeature q n := EF.const (q n)` (`constantRoute_generable` restates it), and
a constant leaf satisfies every locality lemma with no agreement hypothesis at all
(`constantRoute_locality_vacuous`). On that route the live question is whether `n ↦ σ_{k(n)}` is
machine-writable: `MachineRatCodes` is three `MachineDigits`, each a `MachineTokenStream`, i.e.
emitted by some `F ∈ Complexity.FP` of the unary day (`Framework/Machine/WriteOutMachine.lean:345`).
That is exactly the sources' *hardness* claim ("to produce the numeral `σ_k` the generator must
compute it in time `poly(n)`, and `σ_k` is Ackermann-hard") and it is **not formalized here**:
BSI's environment `𝓔` is not built (mandate: "XL, not worth building"), so there is no named `σ`
about which to state `¬ MachineRatCodes (σ ∘ k)`, and a statement over an arbitrary
`σ : ℕ → Bool` is either trivially true (cardinality) or trivially false (constant `σ`) — a fake
OPEN either way. The refutation's status over FAF: price route closed (here), constant route the
sources' argument (ATTRIBUTION-UNVETTED), see [[fa-delay-bsi-findings]] F1.

FAF has no congruence/locality lemma for `EF.denote` (grep 2026-10-01: `Framework/Criterion.lean`
has `denoteWith_eq_ratCast` and the `rank_*` simp lemmas, nothing relating `denote` on histories
that agree below the rank) — **FAF API request**: `EF.denoteWith_eq_of_agree`.

This file imports only FAF's `Framework.Criterion`, `Framework.Expectations` and
`Properties.Calibration`, so the lemmas are cheap to cite.
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction

/-- **T1 (headline), environment form.** An expressible feature's denotation under any variable
environment `ρ` depends only on the prices on days `≤ e.rank`: two histories agreeing on every
sentence on every day `m ≤ e.rank` give the same value. Induction on `EF`, generalized over `ρ`
for the `letE` case (`rank_letE = max`, `rank_var = 0`, `rank_const = 0`).
Scope: sequence-level (FAF's `EF` syntax); no market, no process.
Source: [[delay-and-visibility]] §3 (vq-wiki-036: "a generator reads *prices*, not `D_H`"); [[delay-program]] §3 lines 141–161 (root-fa-028); BSI §3 Lemma 3 (lean-deference-053); FAF API request
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem EF.denoteWith_eq_of_agree (e : EF) (ρ : List ℝ) (V V' : History)
    (h : ∀ m ≤ e.rank, ∀ φ, V m φ = V' m φ) :
    e.denoteWith ρ V = e.denoteWith ρ V' := by
  induction e generalizing ρ with
  | price φ n => exact h n le_rfl φ
  | const q => rfl
  | add a b iha ihb =>
      simp only [EF.denoteWith]
      rw [iha ρ (fun m hm φ => h m (hm.trans (Nat.le_max_left _ _)) φ),
        ihb ρ (fun m hm φ => h m (hm.trans (Nat.le_max_right _ _)) φ)]
  | mul a b iha ihb =>
      simp only [EF.denoteWith]
      rw [iha ρ (fun m hm φ => h m (hm.trans (Nat.le_max_left _ _)) φ),
        ihb ρ (fun m hm φ => h m (hm.trans (Nat.le_max_right _ _)) φ)]
  | max a b iha ihb =>
      simp only [EF.denoteWith]
      rw [iha ρ (fun m hm φ => h m (hm.trans (Nat.le_max_left _ _)) φ),
        ihb ρ (fun m hm φ => h m (hm.trans (Nat.le_max_right _ _)) φ)]
  | safeRecip a iha =>
      simp only [EF.denoteWith]
      rw [iha ρ h]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp only [EF.denoteWith]
      rw [ihx ρ (fun m hm φ => h m (hm.trans (Nat.le_max_left _ _)) φ)]
      exact ihbody _ (fun m hm φ => h m (hm.trans (Nat.le_max_right _ _)) φ)

/-- **T1, closed form.** `e.denote V = e.denote V'` whenever `V` and `V'` agree on all days
`≤ e.rank`. The deductive process is not an argument of `denote` at all; this lemma says the
*future* of the price history is not one either.
Scope: sequence-level (FAF's `EF` syntax).
Source: as `EF.denoteWith_eq_of_agree`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem EF.denote_eq_of_agree (e : EF) (V V' : History)
    (h : ∀ m ≤ e.rank, ∀ φ, V m φ = V' m φ) : e.denote V = e.denote V' :=
  EF.denoteWith_eq_of_agree e [] V V' h

/-- **T1 (headline). A `PGenerableWeighting`'s day-`n` value depends only on prices on days
`≤ n` — and on the emitted syntax.** From `hW.rank_le n` and `EF.denote_eq_of_agree`. What this
rules out: a generable weighting of `H`'s market reading `H`'s prices *after* day `n`, or any
input that is neither a price nor part of the feature itself. What it does **not** rule out: a
constant leaf (`EF.const`), which satisfies the conclusion with no agreement hypothesis — BSI's
"hard constant" route (`constantRoute_generable`). A weighting that *reads* the decided atoms
from `D_H` at denotation time is not an `EF`; a weighting whose generator *wrote them in* as
constants is one, whenever the constant stream is machine-writable.
Scope: one market (the weighting's own); any process. Price route only.
Source: [[delay-and-visibility]] §3 (vq-wiki-036); [[delay-program]] §3 (root-fa-028); lean-deference-053; FAF `PGenerableWeighting.rank_le` (`Properties/Calibration.lean`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem pgenerable_price_local {W : ℕ → EF} (hW : PGenerableWeighting W) (n : ℕ)
    (V V' : History) (h : ∀ m ≤ n, ∀ φ, V m φ = V' m φ) :
    (W n).denote V = (W n).denote V' :=
  EF.denote_eq_of_agree (W n) V V' (fun m hm φ => h m (hm.trans (hW.rank_le n)) φ)

/-- **T1 (headline), sharp form. A generable rational target's day-`n` value is fixed by the
market's own prices through day `n` and by the day-`n` feature.** If `feature` generates `q` at
the market `P` (`GeneratedRatFeature`, the certificate `PGenerableRat P q` ranges over), then on
any history `V'` agreeing with `P` through day `n`, the day-`n` feature still denotes `q n`. For
BSI's human-side target `p^H_n := σ_{k(n)}` (post-mid) this closes the **price route** only: if
the generating feature reads `σ_{k(n)}` off `H`'s prices, then `H`'s prices through day `n`
already carry `σ_{k(n)}` (by a margin, when read through a ramp — audit r1 adversarial
non-blocking 10), and Theorem 4.4.5 with that target concludes what it assumes. It says nothing
against the **constant route** `ratCodeFeature (σ ∘ k)`, on which the conclusion holds for every
`V'` without any agreement hypothesis (`constantRoute_locality_vacuous`); that route is open
exactly when `σ ∘ k` is machine-writable, which is the sources' hardness claim, not formalized
(module docstring). The dichotomy "prices carry `σ` or the target is not generable" that an
earlier version of this docstring stated omitted this horn (audit r1 fidelity B1).
Scope: one market; any process. Price route only.
Source: [[delay-and-visibility]] §3 (vq-wiki-036); BSI §3 Lemma 3 ("the generator at indices `≥ m_k` can afford to read `D_H`'s day-`m_k` output"; lean-deference-053); FAF `GeneratedRatFeature` (`Framework/Expectations.lean`)
Kind: P
Fidelity: weaker: the price-route half of the sources' obstruction; the FP-writability half (`¬ MachineRatCodes (σ ∘ k)`) is not stated
Hyps: (a) none -/
theorem generatedRat_price_local {P : History} {q : ℕ → ℚ} {feature : ℕ → EF}
    (hq : GeneratedRatFeature P q feature) (n : ℕ) (V' : History)
    (h : ∀ m ≤ n, ∀ φ, P m φ = V' m φ) :
    (feature n).denote V' = (q n : ℝ) := by
  rw [← hq.denote n]
  exact (EF.denote_eq_of_agree (feature n) P V'
    (fun m hm φ => h m (hm.trans (hq.rank_le n)) φ)).symm

/-- **T1, `PGenerableRat` form.** For a generable rational sequence `q` at `P`, *some* feature
progression denotes `q` on every history agreeing with `P` through the day. (The existential is
FAF's `PGenerableRat`; the content is `generatedRat_price_local`.)
Scope: one market; any process.
Source: as `generatedRat_price_local`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem pgenerableRat_price_local {P : History} {q : ℕ → ℚ} (hq : PGenerableRat P q) :
    ∃ feature : ℕ → EF, ∀ n (V' : History), (∀ m ≤ n, ∀ φ, P m φ = V' m φ) →
      (feature n).denote V' = (q n : ℝ) := by
  obtain ⟨feature, hf⟩ := hq
  exact ⟨feature, fun n V' h => generatedRat_price_local hf n V' h⟩

/-! ## The constant route (what the locality lemmas do not touch) -/

/-- **BSI Lemma 3's move over FAF: the constant route.** Every machine-writable rational stream
is generable at every market, through the constant leaf `ratCodeFeature q n := EF.const (q n)` —
FAF's `PGenerableRat.ofMachineRatCodes`, restated so that the package names the route the
locality lemmas do not touch. BSI's "the post-mid branch reads decided atoms, a hard constant for
the poly-time generator" is this constructor at `q := p^H`; its hypothesis `MachineRatCodes p^H`
(three digit streams, each emitted by an `F ∈ Complexity.FP` of the unary day) is the object of
the sources' hardness claim and is what a refutation of Theorem B over FAF must deny.
Scope: any market; no process.
Source: BSI §4 Lemma 3 (lean-deference-053); FAF `PGenerableRat.ofMachineRatCodes` (`Framework/Expectations.lean:157`); audit r1 fidelity B1 (probe `audit-r1-probes/ConstantRoute.lean`)
Kind: L
Fidelity: exact (FAF's constructor, restated)
Hyps: (a) none -/
theorem constantRoute_generable {q : ℕ → ℚ} (hq : MachineRatCodes q) (P : History) :
    PGenerableRat P q :=
  PGenerableRat.ofMachineRatCodes hq P

/-- **The locality lemmas are vacuous on the constant route.** The constant leaf denotes its
payload on every history, with no agreement hypothesis: `generatedRat_price_local`'s conclusion
for `ratCodeFeature q` is `rfl`. So nothing in this file bears on whether a given stream is
machine-writable; the locality lemmas cut the price route only.
Scope: any history.
Source: audit r1 fidelity B1 (probe `audit-r1-probes/ConstantRoute.lean`); FAF `ratCodeFeature`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem constantRoute_locality_vacuous (q : ℕ → ℚ) (n : ℕ) (V' : History) :
    (ratCodeFeature q n).denote V' = (q n : ℝ) := rfl

end Cleanroom.Fa.FaDelayBsi
