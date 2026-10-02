import Cleanroom.Bli.BliAssemble.Chain

/-!
# `bli-assemble` · Map: the expression map (target 3)

`tentMap Q 𝓜 c hQ : ExprMap (ratHistory Q) (bliOv Q 𝓜 (tentSkeleton smallIndex 𝓜) c)` — the
`bli-transfer` expression map whose bodies are `chainExpr` (tent terms times chain constants),
with the six fields discharged:

* `closed` — the bodies have no `var`/`letE`: `tentExpr` is `PriceLeavesIn`, which forbids them
  (`freeBound_eq_zero_of_priceLeavesIn`), and the `const` factors are closed.
* `leaves` — every price leaf is `price φ n` with `φ ∈ smallSet n` on the firing day `n`
  (`tentExpr_priceLeavesIn` read through `priceQueries_of_priceLeavesIn`), so `p.1 ≤ n` and
  `SmallOn p.1 p.2`.
* `fires` — `denoteRat_chainExpr` (target 2(c)) at `V := Q`, cast to the real history by FAF's
  `EF.denote_eq_ratCast`; the overlay on a large Tier-A sentence is `bliOv`, which is
  `tierAPrice` there.
* `silent` — an un-fired sentence is small, or Tier B, where `bliOv` is `Q` by definition.
* `ov_range` — `tierAPrice_mem_Icc` on Tier A, the base's range `hQ` on Tier B.

`hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1` is the base's range, which `Headline.lean` derives from
`[IsLogicalInductor (ratHistory Q) DP]` (`IsLogicalInductor.price_mem_Icc`), never assumes.

The map returns `none` on small sentences, so the dropped guard of `bli-transfer` (Known issue 6)
never matters; and `fires` holds on **every** sentence `tierA` accepts — `tentMap_fires_two_chain`
audits it on a two-atom chain with a small part (mandate trap for target 2).

Sources: [[bli-program]] §3.1 (i)–(ii), §3.4; mandate target 3.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

/-! ## Shape lemmas for `PriceLeavesIn` terms -/

/-- A `PriceLeavesIn` term has no free variable (no `var`, no `letE`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freeBound_eq_zero_of_priceLeavesIn {A : Finset Sentence} {n : ℕ} :
    ∀ {e : EF}, PriceLeavesIn A n e → EF.freeBound e = 0
  | .price _ _, _ => rfl
  | .const _, _ => rfl
  | .add a b, h => by
      simp only [EF.freeBound, freeBound_eq_zero_of_priceLeavesIn h.1,
        freeBound_eq_zero_of_priceLeavesIn h.2, Nat.max_self]
  | .mul a b, h => by
      simp only [EF.freeBound, freeBound_eq_zero_of_priceLeavesIn h.1,
        freeBound_eq_zero_of_priceLeavesIn h.2, Nat.max_self]
  | .max a b, h => by
      simp only [EF.freeBound, freeBound_eq_zero_of_priceLeavesIn h.1,
        freeBound_eq_zero_of_priceLeavesIn h.2, Nat.max_self]
  | .safeRecip _, h => h.elim
  | .var _, h => h.elim
  | .letE _ _, h => h.elim

/-- The price queries of a `PriceLeavesIn A n` term are day-`n` queries of sentences in `A`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceQueries_of_priceLeavesIn {A : Finset Sentence} {n : ℕ} :
    ∀ {e : EF}, PriceLeavesIn A n e → ∀ p ∈ e.priceQueries, p.1 = n ∧ p.2 ∈ A
  | .price φ k, h, p, hp => by
      simp only [EF.priceQueries, List.mem_singleton] at hp
      subst hp
      exact ⟨h.2, h.1⟩
  | .const _, _, p, hp => by simp [EF.priceQueries] at hp
  | .add a b, h, p, hp => by
      simp only [EF.priceQueries, List.mem_append] at hp
      rcases hp with hp | hp
      · exact priceQueries_of_priceLeavesIn h.1 p hp
      · exact priceQueries_of_priceLeavesIn h.2 p hp
  | .mul a b, h, p, hp => by
      simp only [EF.priceQueries, List.mem_append] at hp
      rcases hp with hp | hp
      · exact priceQueries_of_priceLeavesIn h.1 p hp
      · exact priceQueries_of_priceLeavesIn h.2 p hp
  | .max a b, h, p, hp => by
      simp only [EF.priceQueries, List.mem_append] at hp
      rcases hp with hp | hp
      · exact priceQueries_of_priceLeavesIn h.1 p hp
      · exact priceQueries_of_priceLeavesIn h.2 p hp
  | .safeRecip _, h, _, _ => h.elim
  | .var _, h, _, _ => h.elim
  | .letE _ _, h, _, _ => h.elim

/-- `chainExpr` is closed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainExpr_closed (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ)
    (p : List (ℕ × ℕ) × Option Sentence) : EF.Closed (chainExpr 𝓜 c n p) := by
  unfold EF.Closed chainExpr
  split_ifs
  · simp only [EF.freeBound, freeBound_eq_zero_of_priceLeavesIn (tentExpr_priceLeavesIn _ _ _ _),
      Nat.max_self]
  · rfl

/-- Every leaf of `chainExpr 𝓜 c n p` is a day-`n` price of a day-`n` small sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainExpr_leaves (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ)
    (p : List (ℕ × ℕ) × Option Sentence) :
    ∀ q ∈ (chainExpr 𝓜 c n p).priceQueries, q.1 ≤ n ∧ SmallOn q.1 q.2 := by
  intro q hq
  unfold chainExpr at hq
  split_ifs at hq
  · simp only [EF.priceQueries, List.append_nil] at hq
    obtain ⟨h1, h2⟩ := priceQueries_of_priceLeavesIn (tentExpr_priceLeavesIn _ _ _ _) q hq
    refine ⟨h1.le, ?_⟩
    rw [h1]
    exact mem_smallSet.mp h2
  · simp [EF.priceQueries] at hq

/-- The bodies' rank discipline: every body reads days `≤ k` (the splice's rank law needs it).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentExprMap_rank (𝓜 : Mesh) (c : StateCoding 𝓜) :
    ∀ k ψ e, tentExprMap 𝓜 c k ψ = some e → e.rank ≤ k := by
  intro k ψ e h
  obtain ⟨-, s, -, rfl⟩ := tentExprMap_eq_some h
  exact EF.rank_le_of_priceQueries _ k (fun p hp => (chainExpr_leaves 𝓜 c k s p hp).1)

/-! ## The expression map -/

/-- **The expression map of the tent re-pricing** (target 3): `bli-transfer`'s `ExprMap` for the
base `ratHistory Q` and the re-pricing `bliOv Q 𝓜 (tentSkeleton smallIndex 𝓜) c`, with bodies
`tentExprMap 𝓜 c`. Every field is proved: closedness and leaves from `tentExpr_priceLeavesIn`;
`fires` from the chain bridge `denoteRat_chainExpr` (target 2(c)) and FAF's rational/real cast
`EF.denote_eq_ratCast`; `silent` because the map is `none` exactly on small or Tier-B sentences,
where `bliOv` is the base; `ov_range` from `tierAPrice_mem_Icc` and the base's range `hQ`.
Source: [[bli-program]] §3.1 (i)–(ii), §3.4; mandate target 3
Kind: D
Fidelity: exact
Hyps: (a) `hQ` (the base's range; derived from the inductor instance in `Headline.lean`) -/
def tentMap (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) :
    ExprMap (ratHistory Q) (bliOv Q 𝓜 (tentSkeleton smallIndex 𝓜) c) where
  expr := tentExprMap 𝓜 c
  closed := by
    intro k ψ e h
    obtain ⟨-, s, -, rfl⟩ := tentExprMap_eq_some h
    exact chainExpr_closed 𝓜 c k s
  leaves := by
    intro k ψ e h
    obtain ⟨-, s, -, rfl⟩ := tentExprMap_eq_some h
    exact chainExpr_leaves 𝓜 c k s
  fires := by
    intro k ψ e h
    obtain ⟨hs, ⟨l, s⟩, ht, rfl⟩ := tentExprMap_eq_some h
    rw [overlay_large hs, bliOv_of_tierA ht,
      EF.denote_eq_ratCast _ (ratHistory Q) Q (fun _ _ => rfl), denoteRat_chainExpr c k Q ht]
  silent := by
    intro k ψ h
    rcases tentExprMap_eq_none h with hs | ht
    · exact Or.inr hs
    · left
      rw [bliOv_of_tierB ht]
      rfl
  ov_range := fun k ψ => bliOv_mem_Icc hQ 𝓜 _ c k ψ

/-- The map's bodies are `tentExprMap` (unfolding).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tentMap_expr (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) : (tentMap Q 𝓜 c hQ).expr = tentExprMap 𝓜 c := rfl

/-! ## Audit: the map fires, correctly, on a two-atom chain with a small part -/

/-- **Audit of the bridge beyond single atoms** (mandate trap for target 2): on
`φ ⋏ (σ_m ⋏ σ_o)` — a day-`n`-future two-entry chain with a small part `φ` small on the latest
day `o` and mentioning no future atom — the map fires and its body denotes, at every rational
history `V`, the Tier-A price `chainMass · tableVal`. Instance of `tentExprMap_of_tierA` and
`denoteRat_chainExpr` at `tierA_and_two`.
Source: mandate target 2 (trap: "audit it on a two-atom chain with a small part")
Kind: C
Fidelity: exact
Hyps: (a) the syntactic hypotheses of `tierA_and_two` -/
theorem tentMap_fires_two_chain (𝓜 : Mesh) (c : StateCoding 𝓜) {n m o q₁ q₂ : ℕ}
    (hnm : n < m) (hq₁ : q₁ ∈ c.states m) (hno : n < o) (hq₂ : q₂ ∈ c.states o) (hmo : m < o)
    {φ : Sentence} (hφ : NoFutureState c n φ) (hsmall : SmallOn o φ) (V : RatHistory) :
    tentExprMap 𝓜 c n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) =
        some (chainExpr 𝓜 c n ([(m, q₁), (o, q₂)], some φ)) ∧
      (chainExpr 𝓜 c n ([(m, q₁), (o, q₂)], some φ)).denoteRat V =
        tierAPrice (tentSkeleton smallIndex 𝓜) c n (actualTable smallIndex V n)
          ([(m, q₁), (o, q₂)], some φ) := by
  have ht := tierA_and_two c hnm hq₁ hno hq₂ hmo hφ hsmall
  have hs : ¬ SmallOn n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) :=
    not_smallOn_and_of_right (not_smallOn_and_of_left (not_smallOn_stateAtom c hnm hq₁))
  exact ⟨tentExprMap_of_tierA hs ht, denoteRat_chainExpr c n V ht⟩

end

end Cleanroom.Bli.BliAssemble
