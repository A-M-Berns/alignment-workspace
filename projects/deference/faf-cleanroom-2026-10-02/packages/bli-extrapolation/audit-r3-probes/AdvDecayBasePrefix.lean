import Cleanroom.Bli.BliExtrapolation.Decay

/-!
Audit round 3, adversarial lens — PDF 06 eq. (1) in the source's own regime.

PDF 06 p. 2: "if we only have information up to ϕ(m), we can set
`r := P(ϕ(1) ∧ … ∧ ϕ(m)) − P(∀mϕ(m)) ≥ 0`, and define `P(ϕ(1) ∧ … ∧ ϕ(k)) := P(∀mϕ(m)) + r/2^{k−m}`
for `k ≥ m`." The excess `r` is a *base-given* quantity: the first `m` instances are inside the
base, and the scheme extends them. In the shipped `decay_scheme_is_half_rule` (Decay.lean) every
instance of the prefix is at a halving level beyond the base (`k 0 ≥ B`), so
`P(⋀_{j<m}) − P(U) = (½)^m · P(¬U)` is forced, and the `m ≥ 1` cases of the display are
`decay_scheme_pow` at `n` and at `m` divided. This file proves the display in the source's regime
with the package's own tools: for *any* sentence `E₀` of level `≤ k 0` (in particular a prefix of
base-level instances, or any base-level event),

  `P(E₀ ∧ ⋀_{j<n} a_j) = P(U ∧ E₀) + (½)^n · P(¬U ∧ E₀)`      (`decay_scheme_general`)

and for `E₀ = ⋀_{j<m} inst u j` (any `m`, the instances at any levels `≤ k 0`),

  `P(E₀ ∧ ⋀_{j<n} a_j) = P(U) + (P(E₀) − P(U)) / 2^n`           (`eq1_base_prefix`),

which is eq. (1) with the base-given `r = P(E₀) − P(U)`. The proof is `negUnivPrefix_val_succ`'s
argument with `∼U ⋏ E₀` in place of `∼U`, plus `extrapolateVal_univ_and_instPrefix`.

Not imported by the library.
-/

namespace Cleanroom.Bli.BliExtrapolation.AuditR3Adv

open LogicalInduction LO.Propositional BoolPCWorld Finset

/-- `E ⋏ atom (a 0) ⋏ … ⋏ atom (a (n-1))`, left-nested from `E`. -/
def prefixFrom (E : Sentence) (a : ℕ → ℕ) : ℕ → Sentence
  | 0 => E
  | n + 1 => prefixFrom E a n ⋏ Formula.atom (a n)

lemma prefixFrom_imp (E : Sentence) (a : ℕ → ℕ) (v : PCWorld) :
    ∀ n, v.Holds (prefixFrom E a n) → v.Holds E
  | 0, h => h
  | n + 1, h => prefixFrom_imp E a v n ((PCWorld.holds_and _ _ _).mp h).1

lemma holds_prefixFrom_and (E F : Sentence) (a : ℕ → ℕ) (v : PCWorld) :
    ∀ n, v.Holds (E ⋏ prefixFrom F a n) ↔ v.Holds (prefixFrom (E ⋏ F) a n)
  | 0 => Iff.rfl
  | n + 1 => by
      have ih := holds_prefixFrom_and E F a v n
      rw [PCWorld.holds_and] at ih
      show v.Holds (E ⋏ (prefixFrom F a n ⋏ Formula.atom (a n))) ↔
        v.Holds (prefixFrom (E ⋏ F) a n ⋏ Formula.atom (a n))
      rw [PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_and, ← ih]
      tauto

section

variable (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)] (e : ℕ ≃ ℕ) {B : ℕ}

lemma level_prefixFrom (E : Sentence) (k : ℕ → ℕ) (hk : StrictMono k) (hE : level e E ≤ k 0) :
    ∀ n, level e (prefixFrom E (fun n => e (k n)) n) ≤ k n
  | 0 => by simpa [prefixFrom] using hE
  | n + 1 => by
      rw [prefixFrom, level_and, level_atom, Equiv.symm_apply_apply]
      exact max_le ((level_prefixFrom E k hk hE n).trans (hk (Nat.lt_succ_self n)).le)
        (hk (Nat.lt_succ_self n))

/-- The halving step from an arbitrary `U`-refuting start `E` of level `≤ k 0`
(`negUnivPrefix_val_succ` with `E` in place of `∼U`). -/
theorem prefixFrom_val_succ (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (E : Sentence) (hE : level e E ≤ k 0)
    (hEU : ∀ v : PCWorld, v.Holds E → ¬ v.Holds (S.univSentence u))
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))) (n : ℕ) :
    extrapolateVal S e q (prefixFrom E (fun n => e (k n)) (n + 1)) =
      (1 / 2) * extrapolateVal S e q (prefixFrom E (fun n => e (k n)) n) := by
  unfold extrapolateVal
  show chainVal e (sotoRule S e q) (prefixFrom E (fun n => e (k n)) n ⋏
    Formula.atom (e (k n))) = _
  apply chainVal_and_atom e _ (level_prefixFrom e E k hk hE n) (1 / 2)
  intro w hw
  by_cases hc : AxConsistent S {conj e w}
  · right
    rw [sotoRule_of_le S e q (hkB.trans (hk.monotone (Nat.zero_le n))) w]
    have hnU : ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) :=
      hEU _ (prefixFrom_imp _ _ _ n hw)
    obtain ⟨h1, h2⟩ := hhalf n w hc hnU
    simp [axClause, h1, h2]
  · left
    exact sotoPMF_zero_of_inconsistent S e hq0 hq1 hbase _ w hc

theorem prefixFrom_val_pow (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (E : Sentence) (hE : level e E ≤ k 0)
    (hEU : ∀ v : PCWorld, v.Holds E → ¬ v.Holds (S.univSentence u))
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n)))) :
    ∀ n, extrapolateVal S e q (prefixFrom E (fun n => e (k n)) n) =
      (1 / 2) ^ n * extrapolateVal S e q E
  | 0 => by simp [prefixFrom]
  | n + 1 => by
      rw [prefixFrom_val_succ S e q u hq0 hq1 hbase k hk hkB E hE hEU hhalf n,
        prefixFrom_val_pow q u hq0 hq1 hbase k hk hkB E hE hEU hhalf n]
      ring

/-- Under `U`, adding instance atoms at the halving levels costs no mass, whatever the start
`E₀` (`extrapolateVal_univ_and_instPrefix`'s argument). -/
theorem univ_and_prefixFrom (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k i : ℕ → ℕ)
    (hinst : ∀ n, S.inst u (i n) = Formula.atom (e (k n))) (E₀ : Sentence) :
    ∀ n, extrapolateVal S e q (S.univSentence u ⋏ prefixFrom E₀ (fun n => e (k n)) n) =
      extrapolateVal S e q (S.univSentence u ⋏ E₀)
  | 0 => rfl
  | n + 1 => by
      have ih := univ_and_prefixFrom q u hq0 hq1 hbase k i hinst E₀ n
      rw [← ih]
      unfold extrapolateVal
      have hunit := sotoRule_inUnit S e hq0
      have hzero : chainVal e (sotoRule S e q) (∼Formula.atom (e (k n)) ⋏
          (S.univSentence u ⋏ prefixFrom E₀ (fun n => e (k n)) n)) = 0 := by
        apply le_antisymm _ (chainVal_mem_Icc e hunit _).1
        have h0 := extrapolateVal_univ_and_neg_inst S e q hq0 hq1 hbase u (i n)
        unfold extrapolateVal at h0
        rw [hinst n] at h0
        rw [← h0]
        apply chainVal_mono e hunit
        intro v hv
        rw [PCWorld.holds_and, PCWorld.holds_and] at hv
        exact (PCWorld.holds_and _ _ _).mpr ⟨hv.2.1, hv.1⟩
      rw [chainVal_split e (sotoRule S e q) (Formula.atom (e (k n)))
        (S.univSentence u ⋏ prefixFrom E₀ (fun n => e (k n)) n), hzero, add_zero]
      apply chainVal_congr
      intro v
      simp only [prefixFrom, PCWorld.holds_and]
      tauto

/-- **The display for an arbitrary start**: `P(E₀ ∧ ⋀_{j<n} a_j) = P(U ∧ E₀) + (½)^n · P(¬U ∧ E₀)`
for any `E₀` of level `≤ k 0`. -/
theorem decay_scheme_general (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k i : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (hlev : level e (S.univSentence u) ≤ k 0)
    (hinst : ∀ n, S.inst u (i n) = Formula.atom (e (k n)))
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n))))
    (E₀ : Sentence) (hE₀ : level e E₀ ≤ k 0) (n : ℕ) :
    extrapolateVal S e q (prefixFrom E₀ (fun n => e (k n)) n) =
      extrapolateVal S e q (S.univSentence u ⋏ E₀) +
        (1 / 2) ^ n * extrapolateVal S e q (∼S.univSentence u ⋏ E₀) := by
  have hE : level e (∼S.univSentence u ⋏ E₀) ≤ k 0 := by
    rw [level_and, level_neg]; exact max_le hlev hE₀
  have hEU : ∀ v : PCWorld, v.Holds (∼S.univSentence u ⋏ E₀) → ¬ v.Holds (S.univSentence u) :=
    fun v h => (PCWorld.holds_neg _ _).mp ((PCWorld.holds_and _ _ _).mp h).1
  rw [← univ_and_prefixFrom S e q u hq0 hq1 hbase k i hinst E₀ n,
    ← prefixFrom_val_pow S e q u hq0 hq1 hbase k hk hkB _ hE hEU hhalf n]
  unfold extrapolateVal
  rw [chainVal_split e (sotoRule S e q) (S.univSentence u) (prefixFrom E₀ (fun n => e (k n)) n)]
  congr 1
  apply chainVal_congr
  intro v
  exact holds_prefixFrom_and _ _ _ v n

/-- **PDF 06 eq. (1) with a base-given `r`**: for `E₀ = ⋀_{j<m} inst u j` (the first `m`
instances, at any levels `≤ k 0` — inside the base in the source's regime),
`P(E₀ ∧ ⋀_{j<n} a_j) = P(U) + (P(E₀) − P(U)) / 2^n`. -/
theorem eq1_base_prefix (q : FiniteWorld B → ℚ) (u : ℕ) (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hbase : BaseAxConsistent S e q) (k i : ℕ → ℕ) (hk : StrictMono k)
    (hkB : B ≤ k 0) (hlev : level e (S.univSentence u) ≤ k 0)
    (hinst : ∀ n, S.inst u (i n) = Formula.atom (e (k n)))
    (hhalf : ∀ n (w : FiniteWorld (k n)), AxConsistent S {conj e w} →
      ¬ (enumWorld e w).toPCWorld.Holds (S.univSentence u) →
      ¬ AxEntails S {conj e w} (Formula.atom (e (k n))) ∧
        ¬ AxEntails S {conj e w} (∼Formula.atom (e (k n))))
    (m : ℕ) (hE₀ : level e (instPrefix (fun j => S.inst u j) m) ≤ k 0) (n : ℕ) :
    extrapolateVal S e q (prefixFrom (instPrefix (fun j => S.inst u j) m) (fun n => e (k n)) n) =
      extrapolateVal S e q (S.univSentence u) +
        (extrapolateVal S e q (instPrefix (fun j => S.inst u j) m) -
          extrapolateVal S e q (S.univSentence u)) / 2 ^ n := by
  rw [decay_scheme_general S e q u hq0 hq1 hbase k i hk hkB hlev hinst hhalf _ hE₀ n]
  have hU := extrapolateVal_univ_and_instPrefix S e q hq0 hq1 hbase u (fun j => j) m
  have hs := chainVal_split e (sotoRule S e q) (S.univSentence u)
    (instPrefix (fun j => S.inst u j) m)
  change extrapolateVal S e q _ = extrapolateVal S e q _ + extrapolateVal S e q _ at hs
  rw [hU, hs, hU, one_div_pow]
  ring

end

end Cleanroom.Bli.BliExtrapolation.AuditR3Adv
