import Cleanroom.Li.LiPseudorandom.Family
import LogicalInduction.Properties.Conditioning

/-!
# `li-pseudorandom` — the family inside a union process (the plan's `paperDP T` shape)

The plan's `### li-pseudorandom` asks for the family *inside* `paperDP T`; the mandate re-scoped
the process to `atomDP` alone and told dependents whose inductor is the LIA over
`DP₀.union (atomDP …)` to prove the union's locality lemma themselves. The round-1 adversarial
audit (item 1, probe `UnionAndAdaptive.lean` §1) pointed out that it is a five-line corollary of
the package's own `liaHistory_congr` + `atomDP_D_congr`, so it belongs here rather than in six
dependents. FAF's `DeductiveProcess.union` (`Properties/Conditioning.lean`, not
`Framework/Criterion.lean` as the mandate says) is `D n := DP.D n ∪ extra.D n`.

* `liaHistory_union_atomDP_causal` — the LIA over `DP₀.union (atomDP a x g)` is a causal builder
  for delay `g`, for any fixed `DP₀`;
* `unionStar DP₀ a g p` — the diagonal family over that builder (a `def`, like `truthStar`);
* `unionStar_pseudorandom_all` / `unionStar_pseudorandom` — T5 on it: pseudorandom with frequency
  `p` relative to the LIA over `DP₀.union (atomDP a (unionStar …) g)`, every `f`;
* `unionStar_theoryTruth` — `TheoryTruth` for the union process, from `atomDP`'s stages.

With `DP₀ := paperDP T` this is the plan's stated instance. What is **not** delivered: `hworld`
for the union (a world consistent with every stage of `DP₀ ∪ atomDP`), which needs the placement
`a` to be fresh for `DP₀` and a consistency proof for `DP₀` — the dependent's obligation, since it
depends on `DP₀`; and the union's `ComputableDeductiveProcess` certificate (T7-level).
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology

/-- **The LIA over `DP₀ ∪ atomDP a x g` is a causal builder for delay `g`**, for any fixed
process `DP₀`: stages `≤ n` of the union read only the `x j` with `g j ≤ n` (`atomDP_D_congr`),
and the LIA's prices at days `≤ n` read only stages `≤ n` (`liaHistory_congr`).
Source: mandate T5 (the union case); plan `### li-pseudorandom` (`paperDP T`); round-1
adversarial audit, item 1
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem liaHistory_union_atomDP_causal (DP₀ : DeductiveProcess) (a g : ℕ → ℕ) :
    CausalBuilder (fun x => liaHistory (DP₀.union (atomDP a x g))) g := by
  intro x y n h m hm φ
  refine liaHistory_congr (n := n) ?_ m hm φ
  intro m' hm'
  show DP₀.D m' ∪ (atomDP a x g).D m' = DP₀.D m' ∪ (atomDP a y g).D m'
  rw [atomDP_D_congr (a := a) h m' hm']

/-- **The family of record inside a union process**: the diagonal over the LIA of
`DP₀.union (atomDP a x g)` and the enumeration of record, at constant target `p`. A `def` from
`diag`, like `truthStar`.
Source: plan `### li-pseudorandom` (`paperDP T` instance); mandate T5/T6
Kind: D
Fidelity: variant: rules evaluated on the prefix-built market (as `truthStar`); equal to the
mandate's under `CausalBuilder` -/
noncomputable def unionStar (DP₀ : DeductiveProcess) (a g : ℕ → ℕ) (p : ℝ) : ℕ → Bool :=
  diagBuilder (fun x => liaHistory (DP₀.union (atomDP a x g))) genWeighting (fun _ => p)

/-- **T5 on the union builder, paper form.** For every P-generable weighting divergent on the
LIA over `DP₀.union (atomDP a (unionStar DP₀ a g p) g)`, the weighted truth frequency of
`unionStar DP₀ a g p` tends to `p`. Hypotheses: `0 ≤ p ≤ 1`, `∀ j, j < g j`.
Source: plan `### li-pseudorandom` (`paperDP T` instance); mandate T5; LI paper `def:pseudorandom`
Kind: C
Fidelity: exact (relative to the LIA over the union)
Hyps: (a) -/
theorem unionStar_pseudorandom_all (DP₀ : DeductiveProcess) (a g : ℕ → ℕ) (hg : ∀ j, j < g j)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (liaHistory (DP₀.union (atomDP a (unionStar DP₀ a g p) g))) →
      weightedAverage
        (fun i => (W i).denote (liaHistory (DP₀.union (atomDP a (unionStar DP₀ a g p) g))))
        (truthR (unionStar DP₀ a g p)) ≈ₙ (fun _ => p) :=
  diagBuilder_pseudorandom_of_causal (fun x => liaHistory (DP₀.union (atomDP a x g))) g
    (liaHistory_union_atomDP_causal DP₀ a g) hg genWeighting genWeighting_covers p hp

/-- **T5 on the union builder, FAF's predicate.** `unionStar DP₀ a g p` inhabits
`PseudorandomFrequency` at frequency `p` relative to the LIA over
`DP₀.union (atomDP a (unionStar …) g)`, for every `f`. With `DP₀ := paperDP T` this is the
plan's stated instance (its `hworld` and `IsLogicalInductor` certificate are the dependent's).
Source: plan `### li-pseudorandom`; mandate T5; FAF `PseudorandomFrequency`
Kind: C
Fidelity: stronger: all `f`
Hyps: (a) -/
theorem unionStar_pseudorandom (DP₀ : DeductiveProcess) (a g : ℕ → ℕ) (hg : ∀ j, j < g j)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ f : DeferralFunction,
      PseudorandomFrequency (truthR (unionStar DP₀ a g p)) p f
        (liaHistory (DP₀.union (atomDP a (unionStar DP₀ a g p) g))) :=
  pseudorandomFrequency_of_causal (fun x => liaHistory (DP₀.union (atomDP a x g))) g
    (liaHistory_union_atomDP_causal DP₀ a g) hg genWeighting genWeighting_covers p hp

/-- **`TheoryTruth` for a union process containing `atomDP`**: a world consistent with every
stage of `DP₀ ∪ atomDP a x g` is consistent with every stage of `atomDP a x g`, so it pays
`truthR x n` on `atom (a n)` (`atomDP_theoryTruth`).
Source: mandate T6.1 (benford bundle), union case
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem union_atomDP_theoryTruth (DP₀ : DeductiveProcess) {a g : ℕ → ℕ} (hg : ∀ j, j < g j)
    (x : ℕ → Bool) :
    AffineCombination.TheoryTruth (atomFamily a) (DP₀.union (atomDP a x g)) (truthR x) := by
  intro n v hv
  refine atomDP_theoryTruth hg x n v ?_
  intro m φ hφ
  exact hv m φ (Finset.mem_union_right _ hφ)

/-- `TheoryTruth` for the family of record inside a union process.
Source: plan `### li-pseudorandom`; mandate T6.3 (benford bundle), union case
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem unionStar_theoryTruth (DP₀ : DeductiveProcess) (a g : ℕ → ℕ) (hg : ∀ j, j < g j)
    (p : ℝ) :
    AffineCombination.TheoryTruth (atomFamily a) (DP₀.union (atomDP a (unionStar DP₀ a g p) g))
      (truthR (unionStar DP₀ a g p)) :=
  union_atomDP_theoryTruth DP₀ hg _

end Cleanroom.Li.LiPseudorandom
