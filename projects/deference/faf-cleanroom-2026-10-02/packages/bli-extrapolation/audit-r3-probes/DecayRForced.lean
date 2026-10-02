import Cleanroom.Bli.BliExtrapolation.Decay

/-!
# Audit r3 (fidelity) probe: under `decay_scheme_is_half_rule`'s hypotheses the source's `r` is forced

PDF 06 p. 2 introduces eq. (1) for the case "if we only have information up to `φ(m)`": the
quantity `r := P(φ(1..m)) − P(∀mφ)` is read off the base's knowledge of the first `m` instances and
the decay fills in beyond `m`. `decay_scheme_is_half_rule` assumes the halving hypotheses at every
index of the prefix (including the first `m`), with every instance beyond the base (`B ≤ k 0`). This
probe shows that under those hypotheses `r` is not free: it equals `(½)^m · P(¬U)`. So the Lean
proves the display only in the regime where the base carries no information about the instances —
not the source's regime — and the `m` parameter adds nothing to `decay_scheme_pow`.
Not imported by the library.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld Finset

theorem decay_r_forced (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)] (e : ℕ ≃ ℕ)
    {B : ℕ} (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k i : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (hlev : level e (S.univSentence u) ≤ k 0)
    (hinst : ∀ n, S.inst u (i n) = Formula.atom (e (k n)))
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))) (m : ℕ) :
    extrapolateVal S e q (instPrefix (fun j => S.inst u (i j)) m) -
        extrapolateVal S e q (S.univSentence u) =
      (1 / 2) ^ m * extrapolateVal S e q (∼S.univSentence u) := by
  rw [decay_scheme_pow S e q u hq0 hq1 hbase k i hk hkB hlev hinst hhalf m]
  ring

end Cleanroom.Bli.BliExtrapolation
