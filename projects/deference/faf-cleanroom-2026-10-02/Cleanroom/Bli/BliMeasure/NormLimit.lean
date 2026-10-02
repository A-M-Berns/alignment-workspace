import Cleanroom.Bli.BliMeasure.Norm
import LogicalInduction.Properties.LimitCoherence
import LogicalInduction.Properties.AffinePersistence

/-!
# `bli-measure` · NormLimit: the online normalizer tends to one (target 6 (c), proved)

Conjecture 2's online repair (`Norm.lean`) normalizes the day-`n` prices of the world
conjunctions `φ_u`, `u : FiniteWorld B`. Target 6 (c) asked whether the normalizer
`∑_u P_n(φ_u)` tends to `1` for a logical inductor and a fixed `B`; rounds 0–2 stated it `OPEN`
(`normSum_tendsto_one_open`, retired here). It is proved (repair round 2, push):

* each term converges to the limiting belief `P_∞(φ_u)` (FAF `lic_limitingBelief_tendsto`,
  `thm:con`), so the finite sum converges to `∑_u P_∞(φ_u)` (`tendsto_finset_sum`);
* `P_∞` is Gaifman-coherent (FAF `lic_limitingBelief_gaifman`, `thm:lc`): finitely additive on
  propositionally exclusive pairs, invariant under propositional equivalence, `1` at `⊤`;
* the `φ_u` are pairwise exclusive (`eq_of_holds_worldConj`: a world holds at most one) and
  exhaustive (`exists_holds_worldConj`: every world holds one), so by induction over the list
  of worlds `∑_u P_∞(φ_u) = P_∞(⋁_u φ_u) = P_∞(⊤) = 1` (`gaifman_sum_worldConj`).

Corollary (`normWeights_tendsto`): **the online weights converge to the limiting belief of the
world conjunctions**, `normWeights P n B u → P_∞(φ_u)` — the day-`n` normalization converges to
the limit world measure Soto's Conjecture 2 is after, with no look-ahead. Everything here is over
FAF's `IsLogicalInductor` class with the standing consistency hypothesis `hcons`; nothing is
specific to B3.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Filter Topology

/-! ## The world conjunctions are an exclusive, exhaustive family -/

/-- The disjunction `⋁_{u ∈ l} φ_u` of the world conjunctions of a list of worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worldDisj {B : ℕ} : List (FiniteWorld B) → Sentence
  | [] => ⊥
  | u :: l => worldConj u ⋎ worldDisj l

/-- A world holds `⋁_{u ∈ l} φ_u` iff it holds some `φ_u`, `u ∈ l`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_worldDisj (v : PCWorld) {B : ℕ} :
    ∀ l : List (FiniteWorld B), v.Holds (worldDisj l) ↔ ∃ u ∈ l, v.Holds (worldConj u)
  | [] => ⟨fun h => (h : False).elim, fun ⟨_, h, _⟩ => (List.not_mem_nil h).elim⟩
  | u :: l => by
    rw [worldDisj, PCWorld.holds_or, holds_worldDisj v l]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- **Exclusivity**: a world holds at most one world conjunction over `B` atoms.
Source: none: infrastructure (bli-soto-a-041: the `φ_W` are exclusive)
Kind: L
Fidelity: n/a -/
lemma eq_of_holds_worldConj (v : PCWorld) {B : ℕ} {u u' : FiniteWorld B}
    (hu : v.Holds (worldConj u)) (hu' : v.Holds (worldConj u')) : u = u' := by
  rw [holds_worldConj] at hu hu'
  funext i
  exact Bool.eq_iff_iff.mpr ((hu i).symm.trans (hu' i))

/-- **Exhaustiveness**: every world holds some world conjunction over `B` atoms (the one reading
its own bits).
Source: none: infrastructure (bli-soto-a-041: the `φ_W` are exhaustive)
Kind: L
Fidelity: n/a -/
lemma exists_holds_worldConj (v : PCWorld) (B : ℕ) : ∃ u : FiniteWorld B, v.Holds (worldConj u) := by
  classical
  refine ⟨fun i => decide (v i.val), ?_⟩
  rw [holds_worldConj]
  intro i
  exact (decide_eq_true_iff).symm

/-! ## A Gaifman-coherent valuation sums to one over the family -/

/-- A Gaifman-coherent valuation gives `⊥` the value `0`.
Source: none: infrastructure (FAF `GaifmanCoherent`)
Kind: L
Fidelity: n/a -/
lemma gaifman_bot_eq_zero {L : Valuation} (hL : GaifmanCoherent L) :
    L (⊥ : Sentence) = 0 := by
  have hadd : L ((⊤ : Sentence) ⋎ ⊥) = L ⊤ + L ⊥ :=
    hL.disjoint_add (fun _ h => (h.2 : False).elim)
  have hc : L ((⊤ : Sentence) ⋎ ⊥) = L ⊤ :=
    hL.congr (fun v => ⟨fun _ => PCWorld.holds_top v,
      fun h => (PCWorld.holds_or v _ _).mpr (Or.inl h)⟩)
  linarith

/-- A Gaifman-coherent valuation is additive over the world conjunctions of a duplicate-free
list of worlds.
Source: none: infrastructure (FAF `GaifmanCoherent.disjoint_add`, iterated)
Kind: L
Fidelity: n/a -/
lemma gaifman_worldDisj_eq_sum {L : Valuation} (hL : GaifmanCoherent L) {B : ℕ} :
    ∀ l : List (FiniteWorld B), l.Nodup →
      L (worldDisj l) = (l.map (fun u => L (worldConj u))).sum
  | [], _ => by simp [worldDisj, gaifman_bot_eq_zero hL]
  | u :: l, hnd => by
    rw [worldDisj, List.map_cons, List.sum_cons,
      ← gaifman_worldDisj_eq_sum hL l (List.nodup_cons.mp hnd).2]
    apply hL.disjoint_add
    intro v hv
    obtain ⟨u', hu'l, hu'⟩ := (holds_worldDisj v l).mp hv.2
    exact (List.nodup_cons.mp hnd).1 (eq_of_holds_worldConj v hv.1 hu' ▸ hu'l)

/-- **A Gaifman-coherent valuation sums to one over the world conjunctions**: the `φ_u` are
exclusive and exhaustive, so `∑_u L(φ_u) = L(⋁_u φ_u) = L(⊤) = 1`.
Source: bli-soto-a-042 (the sketch "in the limit the LI prices worlds coherently"); FAF `GaifmanCoherent`
Kind: P
Fidelity: exact
Hyps: (a) `hL` -/
theorem gaifman_sum_worldConj {L : Valuation} (hL : GaifmanCoherent L) (B : ℕ) :
    ∑ u : FiniteWorld B, L (worldConj u) = 1 := by
  rw [← Finset.sum_map_toList, ← gaifman_worldDisj_eq_sum hL _ (Finset.nodup_toList _),
    ← hL.top_eq_one]
  apply hL.congr
  intro v
  refine ⟨fun _ => PCWorld.holds_top v, fun _ => ?_⟩
  rw [holds_worldDisj]
  obtain ⟨u, hu⟩ := exists_holds_worldConj v B
  exact ⟨u, Finset.mem_toList.mpr (Finset.mem_univ u), hu⟩

/-! ## (c): the normalizer tends to one; the weights tend to the limiting belief -/

/-- **(c) — the online normalizer tends to one** for a logical inductor and a fixed atom bound:
each `P_n(φ_u)` converges to `P_∞(φ_u)` (`lic_limitingBelief_tendsto`), and the limiting belief is
Gaifman-coherent (`lic_limitingBelief_gaifman`), so the limits sum to `1` over the exclusive,
exhaustive family `{φ_u}`. Replaces the `OPEN` row `normSum_tendsto_one_open` of rounds 0–2.
Source: [[bli-measure-mandate]] target 6 (c); bli-soto-a-042 (Conjecture 2, sketch: "in the limit the LI prices worlds coherently")
Kind: C (FAF's `thm:con` and `thm:lc` composed with `gaifman_sum_worldConj`)
Fidelity: exact
Hyps: (a) `hcons` (the standing consistency hypothesis of FAF's LIC theorems); `[IsLogicalInductor P DP]` -/
theorem normSum_tendsto_one (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (B : ℕ) :
    ConvergesTo (fun n => normSum P n B) 1 := by
  have hG := lic_limitingBelief_gaifman P DP hcons
  have hlim : Tendsto (fun n => normSum P n B) atTop
      (𝓝 (∑ u : FiniteWorld B, limitingBelief P (worldConj u))) := by
    unfold normSum
    exact tendsto_finsetSum _ (fun u _ => lic_limitingBelief_tendsto P DP hcons (worldConj u))
  rwa [gaifman_sum_worldConj hG B] at hlim

/-- **The online weights converge to the limiting belief of the world conjunctions**:
`normWeights P n B u → P_∞(φ_u)`. Eventually the normalizer is nonzero (it tends to `1`), so the
default branch is left behind and the weight is the quotient `P_n(φ_u) / ∑_{u'} P_n(φ_{u'})`,
which tends to `P_∞(φ_u) / 1`. This is Soto's Conjecture 2 in the limit, with no look-ahead.
Source: bli-soto-a-042 (Conjecture 2); [[bli-measure-mandate]] target 6 (natural strengthening of (c))
Kind: C
Fidelity: stronger: the limit of the weights themselves, not only of the normalizer
Hyps: (a) `hcons`; `[IsLogicalInductor P DP]` -/
theorem normWeights_tendsto (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (B : ℕ) (u : FiniteWorld B) :
    ConvergesTo (fun n => normWeights P n B u) (limitingBelief P (worldConj u)) := by
  have hS := normSum_tendsto_one P DP hcons B
  have hu := lic_limitingBelief_tendsto P DP hcons (worldConj u)
  have hdiv : Tendsto (fun n => P n (worldConj u) / normSum P n B) atTop
      (𝓝 (limitingBelief P (worldConj u) / 1)) := hu.div hS one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  exact (hS.eventually_ne one_ne_zero).mono (fun n hn => by simp [normWeights, hn])

end Cleanroom.Bli.BliMeasure
