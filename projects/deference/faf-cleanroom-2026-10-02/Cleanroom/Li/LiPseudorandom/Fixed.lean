import Cleanroom.Li.LiPseudorandom.Diagonal
import Cleanroom.Li.LiPseudorandom.Locality

/-!
# `li-pseudorandom` — T5 (the causal-builder theorem) and T4 (the fixed-history form)

**T5.** Let `B : (ℕ → Bool) → History` be causal for delay `g` (`CausalBuilder B g`: the market at
days `≤ n` reads only the truth values `x j` with `g j ≤ n`), with `∀ j, j < g j`, and let `gen`
enumerate the P-generable weightings (`∀ W, PGenerableWeighting W → ∃ k, gen k = W`; `genWeighting`
of `Countable.lean` is one). Then `x := diagBuilder B gen (fun _ => p)` is pseudorandom with
frequency `p` relative to the market `B x` it itself builds, against **every** P-generable
divergent weighting (`diagBuilder_pseudorandom_of_causal`, the paper's `def:pseudorandom` over all
P-generable divergent weightings) — hence FAF's `PseudorandomFrequency … f (B x)` for **every**
deferral function `f` at once (`pseudorandomFrequency_of_causal`; `Fidelity: stronger`, no
patience is used), and the `VariedPseudorandom` form at a day-varying rational target
(`variedPseudorandom_of_causal`).

Proof: T3 (`PGenerableWeighting.denote_congr`) and causality of `B` make the realized weights of
the builder rule `k` on `x` equal to `clamp ((gen k n).denote (B x))` (`builderRule_w_eq`); for a
divergent weighting the clamp is the identity; T1 (`diag_pseudorandom_const`) gives the limit.

Scope (verbatim, per the mandate): **causal builder for delay `g`; excludes markets that read a
truth value before its decision day.** A non-causal `B` is exactly the omniscient market of the
mandate's § Context 1, against which no fixed family is pseudorandom; the hypothesis is the
content.

**T4.** The constant builder `fun _ => P` is causal for any `g`, so every history `P` has a
pseudorandom family (`pseudorandomFrequency_of_history`). **Fixed history; the family depends on
`P`; not the inductor form** (that is T6, `Family.lean`): this `x` must not be used with
`P := liaHistory (atomDP a x g)` — that is circular.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology

/-- Under causality, the realized weight of the builder rule on `x` is the clamped denotation on
the market `B x` itself (the restriction to days `< n` is invisible to a rank-`≤ n` feature).
Source: mandate T5 (proof); T3
Kind: L
Fidelity: exact
Hyps: (a) -/
lemma builderRule_w_eq {B : (ℕ → Bool) → History} {g : ℕ → ℕ} (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) {W : ℕ → EF} (hW : PGenerableWeighting W) (x : ℕ → Bool) (n : ℕ) :
    (builderRule B W).w x n = clamp ((W n).denote (B x)) := by
  show clamp ((W n).denote (B (restrict x n))) = clamp ((W n).denote (B x))
  congr 1
  apply PGenerableWeighting.denote_congr hW n
  apply hB (restrict x n) x n
  intro j hj
  unfold restrict
  rw [if_pos (lt_of_lt_of_le (hg j) hj)]

/-- The realized weights of the builder rule on `x` are the denotations on `B x`, as functions,
when those denotations lie in `[0,1]`.
Source: mandate T5 (proof)
Kind: L
Fidelity: exact
Hyps: (a) -/
lemma builderRule_w_eq_denote {B : (ℕ → Bool) → History} {g : ℕ → ℕ} (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) {W : ℕ → EF} (hW : PGenerableWeighting W) (x : ℕ → Bool)
    (hrange : ∀ n, 0 ≤ (W n).denote (B x) ∧ (W n).denote (B x) ≤ 1) :
    (builderRule B W).w x = fun n => (W n).denote (B x) := by
  funext n
  rw [builderRule_w_eq hB hg hW, clamp_of_mem_Icc (hrange n)]

/-- **T5, paper form.** For a causal builder `B` (delay `g`, `∀ j, j < g j`), a covering
enumeration `gen` of the P-generable weightings, and `p ∈ [0,1]`, the diagonal family
`x := diagBuilder B gen (fun _ => p)` satisfies, for every P-generable weighting `W` divergent on
`B x`, `weightedAverage ((W i).denote (B x)) (truthR x) ≈ₙ p` — the LI paper's `def:pseudorandom`
with frequency `p` over all P-generable divergent weightings, relative to the market `B x`.
Scope: causal builder for delay `g`; excludes markets that read a truth value before its decision
day.
Source: mandate T5; LI paper `def:pseudorandom` (`main.tex:1273`); [[anson-inventory]] anson-034
Kind: C
Fidelity: exact (paper's definition, relative to `B x`)
Hyps: (a) -/
theorem diagBuilder_pseudorandom_of_causal (B : (ℕ → Bool) → History) (g : ℕ → ℕ)
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (B (diagBuilder B gen (fun _ => p))) →
      weightedAverage (fun i => (W i).denote (B (diagBuilder B gen (fun _ => p))))
        (truthR (diagBuilder B gen (fun _ => p))) ≈ₙ (fun _ => p) := by
  intro W hWgen hWdiv
  obtain ⟨k, rfl⟩ := hcov W hWgen
  have hw : (builderRule B (gen k)).w (diagBuilder B gen (fun _ => p)) =
      fun n => (gen k n).denote (B (diagBuilder B gen (fun _ => p))) :=
    builderRule_w_eq_denote hB hg hWgen _ hWdiv.1
  have h := diag_pseudorandom_const (fun k => builderRule B (gen k)) p hp k
    (by
      show Tendsto (prefixSum ((builderRule B (gen k)).w (diagBuilder B gen (fun _ => p))))
        atTop atTop
      rw [hw]
      exact hWdiv.2)
  change weightedAverage ((builderRule B (gen k)).w (diagBuilder B gen (fun _ => p)))
    (truthR (diagBuilder B gen (fun _ => p))) ≈ₙ (fun _ => p) at h
  rw [hw] at h
  exact h

/-- **T5, FAF form.** The same family inhabits FAF's `PseudorandomFrequency` for **every**
deferral function `f`: the patience conjunct is simply not used.
Scope: causal builder for delay `g`; excludes markets that read a truth value before its decision
day.
Source: mandate T5; FAF `PseudorandomFrequency`
Kind: C
Fidelity: stronger: all `f` at once (the family defeats every P-generable divergent weighting,
patient or not)
Hyps: (a) -/
theorem pseudorandomFrequency_of_causal (B : (ℕ → Bool) → History) (g : ℕ → ℕ)
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ f : DeferralFunction, PseudorandomFrequency (truthR (diagBuilder B gen (fun _ => p))) p f
      (B (diagBuilder B gen (fun _ => p))) :=
  fun _ W hWgen hWdiv _ => diagBuilder_pseudorandom_of_causal B g hB hg gen hcov p hp W hWgen hWdiv

/-- **T5, existential form** (the mandate's `exists_pseudorandom_of_causal`): some `x` is
pseudorandom with frequency `p` relative to `B x` for every `f`. The witness is `diagBuilder`.
Source: mandate T5
Kind: L
Fidelity: weaker: existential packaging of `pseudorandomFrequency_of_causal`
Hyps: (a) -/
theorem exists_pseudorandom_of_causal (B : (ℕ → Bool) → History) (g : ℕ → ℕ)
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∃ x : ℕ → Bool, ∀ f : DeferralFunction, PseudorandomFrequency (truthR x) p f (B x) :=
  ⟨_, pseudorandomFrequency_of_causal B g hB hg gen hcov p hp⟩

/-- **T5 at a day-varying rational target** (the `VariedPseudorandom` form of T9). For
`q : ℕ → ℚ` with values in `[0,1]`, `x := diagBuilder B gen (fun n => q n)` is `q`-varied
pseudorandom relative to `B x` for every `f`: the same potential with `p` replaced by `q n`.
Source: mandate T9 (varied form); FAF `VariedPseudorandom` (`def:seqprand`, PE5 orientation)
Kind: C
Fidelity: stronger: all `f`; no generability of `q` is needed to inhabit the predicate
Hyps: (a) -/
theorem variedPseudorandom_of_causal (B : (ℕ → Bool) → History) (g : ℕ → ℕ)
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (q : ℕ → ℚ)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) :
    ∀ f : DeferralFunction, VariedPseudorandom (truthR (diagBuilder B gen (fun n => (q n : ℝ))))
      q f (B (diagBuilder B gen (fun n => (q n : ℝ)))) := by
  intro f
  have hp : ∀ n, 0 ≤ (q n : ℝ) ∧ (q n : ℝ) ≤ 1 := fun n => by
    exact_mod_cast hq n
  have key : ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (B (diagBuilder B gen (fun n => (q n : ℝ)))) →
      weightedAverage (fun i => (W i).denote (B (diagBuilder B gen (fun n => (q n : ℝ)))))
        (fun n => truthR (diagBuilder B gen (fun n => (q n : ℝ))) n - (q n : ℝ)) ≈ₙ
        (fun _ => 0) := by
    intro W hWgen hWdiv
    obtain ⟨k, rfl⟩ := hcov W hWgen
    have hw : (builderRule B (gen k)).w (diagBuilder B gen (fun n => (q n : ℝ))) =
        fun n => (gen k n).denote (B (diagBuilder B gen (fun n => (q n : ℝ)))) :=
      builderRule_w_eq_denote hB hg hWgen _ hWdiv.1
    have h := diag_pseudorandom (fun k => builderRule B (gen k)) (fun n => (q n : ℝ)) hp k
      (by
        show Tendsto (prefixSum ((builderRule B (gen k)).w
          (diagBuilder B gen (fun n => (q n : ℝ))))) atTop atTop
        rw [hw]
        exact hWdiv.2)
    change weightedAverage ((builderRule B (gen k)).w (diagBuilder B gen (fun n => (q n : ℝ))))
      (fun n => truthR (diagBuilder B gen (fun n => (q n : ℝ))) n - (q n : ℝ)) ≈ₙ
      (fun _ => 0) at h
    rw [hw] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro W hWgen hWdiv _
    exact (asympEq_iff_asympLE_asympGE.1 (key W hWgen hWdiv)).2
  · intro W hWgen hWdiv _
    exact (asympEq_iff_asympLE_asympGE.1 (key W hWgen hWdiv)).1

/-! ## T4: the fixed-history form -/

/-- A constant builder is causal for every delay profile.
Source: mandate T4
Kind: L
Fidelity: exact -/
lemma causalBuilder_const (P : History) (g : ℕ → ℕ) : CausalBuilder (fun _ => P) g :=
  fun _ _ _ _ _ _ _ => rfl

/-- **T4, paper form.** Every history `P` has a family pseudorandom with frequency `p ∈ [0,1]`
over all P-generable weightings divergent on `P`: `x := diagBuilder (fun _ => P) gen (fun _ => p)`.
Fixed history; the family depends on `P`; not the inductor form.
Source: mandate T4; LI paper `def:pseudorandom` (`main.tex:1273`)
Kind: C
Fidelity: exact (paper's definition at a fixed history)
Hyps: (a) -/
theorem diagBuilder_pseudorandom_of_history (P : History) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W P →
      weightedAverage (fun i => (W i).denote P)
        (truthR (diagBuilder (fun _ => P) gen (fun _ => p))) ≈ₙ (fun _ => p) :=
  diagBuilder_pseudorandom_of_causal (fun _ => P) (fun j => j + 1)
    (causalBuilder_const P _) (fun j => Nat.lt_succ_self j) gen hcov p hp

/-- **T4, FAF form.** `PseudorandomFrequency (truthR x) p f P` for every `f`, with
`x := diagBuilder (fun _ => P) gen (fun _ => p)`. Fixed history; the family depends on `P`; not the
inductor form — do not use with `P := liaHistory (atomDP a x g)` (circular); the inductor form is
T6.
Source: mandate T4; FAF `PseudorandomFrequency`
Kind: C
Fidelity: stronger: all `f` at once
Hyps: (a) -/
theorem pseudorandomFrequency_of_history (P : History) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ f : DeferralFunction,
      PseudorandomFrequency (truthR (diagBuilder (fun _ => P) gen (fun _ => p))) p f P :=
  pseudorandomFrequency_of_causal (fun _ => P) (fun j => j + 1)
    (causalBuilder_const P _) (fun j => Nat.lt_succ_self j) gen hcov p hp

/-- **T4, existential form** (the mandate's `exists_pseudorandom_of_history`).
Source: mandate T4
Kind: L
Fidelity: weaker: existential packaging
Hyps: (a) -/
theorem exists_pseudorandom_of_history (P : History) (gen : ℕ → ℕ → EF)
    (hcov : ∀ W, PGenerableWeighting W → ∃ k, gen k = W) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∃ x : ℕ → Bool, ∀ f : DeferralFunction, PseudorandomFrequency (truthR x) p f P :=
  ⟨_, pseudorandomFrequency_of_history P gen hcov p hp⟩

end Cleanroom.Li.LiPseudorandom
