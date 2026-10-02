/-
  `dp-learner-nr` targets 1(c) and 8(c): the leak at the LI level, and Conjecture F(v)'s world
  argument.

  Kept separate (the only `LogicalInduction`-importing file besides `Diagonal.lean`) so that a
  slice kill costs one file.
-/

import Cleanroom.Decision.DpTrollBridge.LILesion

open LO
open LogicalInduction
open scoped LogicalInduction
open Filter Topology

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Decision.DpTrollBridge

/-! ## Target 1(c): monotonicity of prices, and the leak composed with `li_lesion_conj` -/

/-- The two-share affine combination `[incon n] − [incon n ⋏ cross n]` (value `≥ 0` in every
Boolean world).
Source: none: infrastructure (the monotonicity step of target 1(c))
Kind: D -/
def monoAffine (cross incon : ℕ → Sentence) (n : ℕ) : AffineCombination where
  const := .const 0
  terms := [(.const 1, incon n), (.const (-1), incon n ⋏ cross n)]

/-- Price of `monoAffine` on day `m`. Source: none: infrastructure. Kind: L -/
lemma monoAffine_price (cross incon : ℕ → Sentence) (P : History) (n m : ℕ) :
    (monoAffine cross incon n).price P m = P m (incon n) - P m (incon n ⋏ cross n) := by
  simp only [monoAffine, AffineCombination.price, AffineCombination.value, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- Value of `monoAffine` under a valuation `w`. Source: none: infrastructure. Kind: L -/
lemma monoAffine_value (cross incon : ℕ → Sentence) (P : History) (n : ℕ) (w : Valuation) :
    (monoAffine cross incon n).value P w = w (incon n) - w (incon n ⋏ cross n) := by
  simp only [monoAffine, AffineCombination.value, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- Magnitude of `monoAffine`: `2`. Source: none: infrastructure. Kind: L -/
lemma monoAffine_magnitude (cross incon : ℕ → Sentence) (P : History) (n : ℕ) :
    (monoAffine cross incon n).magnitude P = 2 := by
  simp only [monoAffine, AffineCombination.magnitude, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  norm_num

/-- `monoAffine` is a polynomial affine family (FAF's `PolySequence`) when `cross` and `incon`
are machine-codeable — the same construction as `dp-troll-bridge`'s `lesionAffine_polySequence`
with the two sentences swapped.
Source: none: infrastructure
Kind: L -/
noncomputable def monoAffine_polySequence (cross incon : ℕ → Sentence)
    (hc : MachineSentenceCodes cross) (hi : MachineSentenceCodes incon) :
    AffineCombination.PolySequence (monoAffine cross incon) where
  termCount := fun _ => 2
  coefficient := fun z => if z.unpair.2 = 0 then .const 1 else .const (-1)
  sentence := fun z =>
    if z.unpair.2 = 0 then incon z.unpair.1 else incon z.unpair.1 ⋏ cross z.unpair.1
  termCount_poly := UnaryRuler.const 2
  const_poly := MachineSpliceStream.serialize_const 0
  coefficient_poly :=
    ((MachineSpliceStream.serialize_const 1).ifZero (MachineSpliceStream.serialize_const (-1))
      UnaryRuler.unpairSnd).of_eq (fun z => by
        by_cases h : z.unpair.2 = 0 <;> simp [h])
  sentence_poly :=
    ((hi.comp UnaryRuler.unpairFst).ifZero ((hi.and hc).comp UnaryRuler.unpairFst)
      UnaryRuler.unpairSnd).of_eq (fun z => by
        by_cases h : z.unpair.2 = 0 <;> simp [h])
  terms_eq := by
    intro n
    have h2 : List.range 2 = [0, 1] := rfl
    simp [monoAffine, h2, Nat.unpair_pair]
  const_rank := by intro n; simp [monoAffine]
  coefficient_rank := by intro n j hj; split <;> simp
  const_closed := by intro n ρ V; simp [monoAffine]
  coefficient_closed := by intro z ρ V; split <;> simp

/-- **Monotonicity of an inductor's prices on the diagonal** (target 1(c)): for machine-codeable
`cross`, `incon`, `P n (incon n) ≥ P n (incon n ⋏ cross n) − δ` eventually, for every `δ > 0`.
FAF's affine provability induction (`affine_provind_theory_ge`) at `b := 0`: the combination
`[incon] − [incon ⋏ cross]` has value `≥ 0` in *every* Boolean world (no theory hypothesis).
Source: [[non-responsiveness]] "NR2" (the first inequality of the leak, `P(□⊥) ≥ P(Cross ∧ (Cross
→ □⊥))`, at the LI level); [[dp-learner-nr-mandate]] target 1(c) ("an affine-coherence
monotonicity — find FAF's lemma or derive it")
Kind: C
Fidelity: variant: asymptotic (`− δ`, eventually) where the finite leak is exact
Hyps: (a) none beyond FAF's `IsLogicalInductor` and the codes -/
theorem li_mono (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (cross incon : ℕ → Sentence)
    (hc : MachineSentenceCodes cross) (hi : MachineSentenceCodes incon)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, P n (incon n ⋏ cross n) - δ ≤ P n (incon n) := by
  have hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hpoly := monoAffine_polySequence cross incon hc hi
  have hbounded : BoundedAffinePrices (monoAffine cross incon) P := by
    refine ⟨1, zero_le_one, fun n m => ?_⟩
    rw [monoAffine_price, abs_le]
    constructor <;>
      linarith [(hP m (incon n ⋏ cross n)).1, (hP m (incon n ⋏ cross n)).2,
        (hP m (incon n)).1, (hP m (incon n)).2]
  have hmag : ∃ C : ℝ, ∀ n, (monoAffine cross incon n).magnitude P ≤ C :=
    ⟨2, fun n => by rw [monoAffine_magnitude]⟩
  have hge := hpoly.affine_provind_theory_ge P DP hbounded hmag hworld 0 (fun n v _ => by
    rw [monoAffine_value]
    by_cases hb : v.Holds (incon n ⋏ cross n)
    · have hi' : v.Holds (incon n) := ((PCWorld.holds_and v _ _).mp hb).1
      simp [PCWorld.payout, hb, hi']
    · by_cases hi' : v.Holds (incon n) <;> simp [PCWorld.payout, hb, hi'])
  have := hge δ hδ
  filter_upwards [this] with n hn
  rw [monoAffine_price] at hn
  linarith

/-- **The leak at the LI level** (target 1(c)): if `cross n 🡒 incon n` holds in every
completed-theory world (the semantic "T ⊢ Cross_n → □⊥"), then for every `δ > 0`, eventually
`P n (incon n) ≥ P n (cross n) − δ`. Composition of `li_mono` with `dp-troll-bridge`'s coherence
step `li_lesion_conj` (`P n (incon n ⋏ cross n) − P n (cross n) → 0`).
Source: [[non-responsiveness]] "NR2" ("a believed theorem `Cross → □⊥` forces `P(□⊥) ≥ P(Cross ∧
(Cross → □⊥)) ≥ P(Cross) − ε`"); [[dp-core-inventory]] 104; [[dp-learner-nr-mandate]] target 1(c)
Kind: C
Fidelity: variant: asymptotic and eventual where the finite leak is exact
Hyps: (c) `hthm` is the semantic rendering of "T ⊢ cross n → □⊥" (as in `li_lesion_conj`) -/
theorem li_leak (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (cross incon : ℕ → Sentence)
    (hc : MachineSentenceCodes cross) (hi : MachineSentenceCodes incon)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, P n (cross n) - δ ≤ P n (incon n) := by
  have hconj := li_lesion_conj P DP cross incon hc hi hthm hworld
  have ht : Tendsto (fun n => (P n (incon n ⋏ cross n) - P n (cross n)) - 0) atTop (𝓝 0) := hconj
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (δ / 2) (by linarith)
  have hmono := li_mono P DP cross incon hc hi hworld (δ / 2) (by linarith)
  rw [Filter.eventually_atTop] at hmono ⊢
  obtain ⟨M, hM⟩ := hmono
  refine ⟨max N M, fun n hn => ?_⟩
  have h1 := hN n (le_of_max_le_left hn)
  have h2 := hM n (le_of_max_le_right hn)
  rw [Real.dist_eq, sub_zero, abs_lt] at h1
  linarith [h1.1]

/-! ## Target 8(c): Conjecture F(v), the LI-level world argument -/

/-- **The decided crosser has no lesion at `n`** (Conjecture F(v), LI level): if `cross n` holds in
every completed-theory world (the decided crosser) and some completed-theory world refutes
`incon n` (`hcon`, Σ₁-soundness-as-a-world, as in `dp-troll-bridge`'s `li_responsive_lesion_open`),
then the lesion "`cross n 🡒 incon n` holds in every completed-theory world" **fails** at `n` —
one world.
Source: [[policy-level-fdt-learner]] §6 Conjecture F (v); [[non-responsiveness-learnability]] §5
E1 ("the Löbian sentence for round `t` is unprovable by Proposition 10's argument");
[[dp-core-inventory]] 111(v); [[dp-learner-nr-mandate]] target 8(c)
Kind: L (a squeeze: under `hcross`, the lesion "every consistent world holds `cross n 🡒 incon n`"
is equivalent to "every consistent world holds `incon n`", so its negation is exactly `hcon` and
the theorem is `hcross → (hcon → hcon)` up to that equivalence — Proposition 10's shape at the
semantic level with Gödel 2 (`T ⊬ □⊥`, the one non-trivial ingredient) assumed as `hcon`; the row
is dictated by the mandate at this shape, and adds nothing beyond it)
Fidelity: variant: "T ⊢" rendered semantically (completed-theory worlds)
Hyps: (c) `hcross` is the semantic rendering of "T ⊢ Cross_n" (the decided crosser); (c) `hcon`
is Σ₁-soundness-as-a-world -/
theorem li_decided_crosser_no_lesion (DP : DeductiveProcess) (cross incon : ℕ → Sentence) (n : ℕ)
    (hcross : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n))
    (hcon : ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ¬ v.Holds (incon n)) :
    ¬ ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n) := by
  intro h
  obtain ⟨v, hv, hni⟩ := hcon
  exact hni ((holds_imp v _ _).mp (h v hv) (hcross v hv))

/-- The per-round form: a family that is a decided crosser at every round, against a theory with
a consistent world refuting `incon n` at every round, has no lesion at any round.
Source: [[policy-level-fdt-learner]] §6 Conjecture F (v) ("for every `t`"); [[dp-learner-nr-mandate]] target 8(c)
Kind: L
Hyps: (c) as in `li_decided_crosser_no_lesion` -/
theorem li_decided_crosser_no_lesion_all (DP : DeductiveProcess) (cross incon : ℕ → Sentence)
    (hcross : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n))
    (hcon : ∀ n, ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ¬ v.Holds (incon n)) :
    ∀ n, ¬ ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n) :=
  fun n => li_decided_crosser_no_lesion DP cross incon n (hcross n) (hcon n)

end Cleanroom.Decision.DpLearnerNr
