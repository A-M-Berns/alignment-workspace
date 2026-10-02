import Cleanroom.Li.LiPseudorandom.Family
import Cleanroom.Found.LiAsympCalc.Ramp
import Cleanroom.Deference.DefSelfTrust.Weights

/-!
# `def-self-trust` — target 7: uniform accuracy is false for real inductors on pseudorandom targets

vq-wiki-2-009 ([[route-transitivity]] §6.1): Corollary B.1's hypothesis `(UA)` — per-day
absolute accuracy of the forecast — is not a deference hypothesis: on a pseudorandom target with
frequency `p ∈ (0,1)`, `thm:benford` forces the inductor's price to `p` while the settled value
is `0/1`, so `|P_n(φ_n) − Val(φ_n)| ≥ min(p, 1−p) − o(1)` forever.

* **7a** (`price_far_from_truth_of_pseudorandom`, `uniformAccuracy_false_of_pseudorandom`): the
  general statement over any `[IsLogicalInductor P DP]` with FAF's `PseudorandomFrequency` as
  hypothesis (kind C, hypotheses (a): the pseudorandomness is FAF's definition, `thm:benford`
  is FAF's theorem).
* **7b** (`truthStar_deferred_benford`, **OPEN**): the `(UA)`-shaped form. Corollary B.1
  compares the forecast with `Y_n = E_{f(n)}(X_n)`, not with a truth value; for the
  literal-indicator source `Y_n` is the deferred *price* `P_{f n}(φ_n)`. The forecast `c ≡ p`
  satisfies `(UA)` against `Y_n` exactly when the deferred price tends to `p` — the
  **deferred-day form of `thm:benford`**, which FAF and `li-pseudorandom` do not supply (FAF's
  `thm:benford` is the diagonal `P_n(φ_n) → p`; finding F13). Round 1 recorded that missing
  theorem as a *hypothesis* of a headline (`UA_vs_settled`), which the round-1 adversarial
  audit (B2) showed to be a squeeze: its first conjunct was the hypothesis unfolded and its
  second (`min p (1−p) ≤ |p − truth n|`, `min_le_abs_sub_of_bool`) needs no market. Repair
  round 1 deleted it and states the missing content as a sorried OPEN theorem at the family of
  record, at a deferral strictly before the decision day (`f n < g n`); 7b's status is
  `open`. The settled-value half of the mandate's 7b sentence ("fails it against the settled
  value by `min p (1−p)`") is `min_le_abs_sub_of_bool`, market-free, and is not a headline.
* **7c** (`truthStar_uniformAccuracy_false`): the instance on `li-pseudorandom`'s family of
  record `truthStar`, over the LIA of `atomDP`; the `IsLogicalInductor` instance is li-pseudorandom's
  OPEN T7 certificate, taken as a binder exactly as `truthStar_learned` does — ledger
  `partial: inductor certificate rests on li-pseudorandom T7`.

* **4c(i)** (`pseudorandom_not_pgenerable`, `truthStar_not_pgenerable`): a `{0,1}` truth
  sequence pseudorandom with frequency `p ∈ (0,1)` relative to `P` is **not** `PGenerableRat P`
  — the theorem the corrigibility thesis needs ("legitimacy is not generable" is *possible*);
  on `truthStar` it needs no inductor certificate at all (pseudorandomness is relative to the
  LIA as a `History`).

FAF has no inhabited `PseudorandomFrequency` at `p ∈ (0,1)` with an inductor certificate;
`li-pseudorandom` supplies the family and leaves the certificate open (finding F10).
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Li.LiPseudorandom

/-- For `b ∈ {0, 1}` and `p ∈ [0,1]`, `min p (1 − p) ≤ |p − b|`.
Source: vq-wiki-2-009 ("`Y_n ∈ {0,1}`, so `|a_n − Y_n| ≥ min(p, 1−p)`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem min_le_abs_sub_of_bool {p b : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (hb : b = 0 ∨ b = 1) :
    min p (1 - p) ≤ |p - b| := by
  rcases hb with rfl | rfl
  · rw [sub_zero, abs_of_nonneg hp.1]; exact min_le_left _ _
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [hp.2])]; exact min_le_right _ _

/-- **7a — the price stays `min p (1−p)` away from the settled value**: for an e.c. family `φ`
with theory truth `truth ∈ {0,1}` that is pseudorandom with frequency `p` relative to `P`
(FAF's `PseudorandomFrequency`), for every `ε > 0` eventually
`min p (1 − p) − ε ≤ |P_n(φ_n) − truth n|`. From `thm:benford` (`P_n(φ_n) ≈ₙ p`) and the
pointwise `|p − b| ≥ min p (1−p)` for `b ∈ {0,1}`.
Source: vq-wiki-2-009 ("precise statement over one market: … `liminf_n |P_n(φ_n) − Val(φ_n)| ≥
min(p, 1−p)`"); FAF `lic_learning_pseudorandom_frequency` (`thm:benford`)
Kind: C
Fidelity: exact (as a `∀ ε, ∀ᶠ` statement, which is the `liminf ≥` reading)
Hyps: (a) -/
theorem price_far_from_truth_of_pseudorandom {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) (truth : ℕ → ℝ)
    (htruth : AffineCombination.TheoryTruth φ DP truth) (hbool : ∀ n, truth n = 0 ∨ truth n = 1)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (hpseudo : PseudorandomFrequency truth p f P) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, min p (1 - p) - ε ≤ |P n (φ n) - truth n| := by
  have hb := lic_learning_pseudorandom_frequency P DP φ hφ truth htruth p hp hworld f hpseudo
  intro ε hε
  have hb' : Tendsto (fun n => P n (φ n) - p) atTop (𝓝 0) := hb
  have habs : Tendsto (fun n => |P n (φ n) - p|) atTop (𝓝 0) := by
    have := hb'.abs
    simpa using this
  filter_upwards [habs.eventually (gt_mem_nhds hε)] with n hn
  have h1 := min_le_abs_sub_of_bool hp (hbool n)
  have h2 : |p - truth n| ≤ |P n (φ n) - p| + |P n (φ n) - truth n| := by
    calc |p - truth n| = |(P n (φ n) - truth n) - (P n (φ n) - p)| := by ring_nf
      _ ≤ |P n (φ n) - truth n| + |P n (φ n) - p| := abs_sub _ _
      _ = |P n (φ n) - p| + |P n (φ n) - truth n| := add_comm _ _
  linarith

/-- **7a, corollary — uniform accuracy is false** at `0 < p < 1`: it is not the case that for
every `ε > 0` eventually `|P_n(φ_n) − truth n| < ε`.
Source: vq-wiki-2-009 ("(UA) … is false in general")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem uniformAccuracy_false_of_pseudorandom {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) (truth : ℕ → ℝ)
    (htruth : AffineCombination.TheoryTruth φ DP truth) (hbool : ∀ n, truth n = 0 ∨ truth n = 1)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (hpseudo : PseudorandomFrequency truth p f P) :
    ¬ (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, |P n (φ n) - truth n| < ε) := by
  intro hUA
  have hm : 0 < min p (1 - p) := lt_min hp0 (by linarith)
  have h := price_far_from_truth_of_pseudorandom φ hφ truth htruth hbool p ⟨hp0.le, hp1.le⟩
    hworld f hpseudo (min p (1 - p) / 2) (by positivity)
  have h' := hUA (min p (1 - p) / 2) (by positivity)
  obtain ⟨n, hn1, hn2⟩ := (h.and h').exists
  linarith

/-- The family of record's truth values are Boolean.
Source: `li-pseudorandom` `truthR`
Kind: L
Fidelity: n/a -/
theorem truthR_bool (x : ℕ → Bool) (n : ℕ) : truthR x n = 0 ∨ truthR x n = 1 := by
  unfold truthR
  split_ifs <;> simp

/-- **7c — uniform accuracy is false on the family of record** (`truthStar a g p` over the LIA
of `atomDP`, `0 < p < 1`, injective `a`, delay `g` with `j < g j`): the LIA's price of
`atom (a n)` never tracks the settled value within every `ε`. The `IsLogicalInductor` instance
is li-pseudorandom's **OPEN T7** certificate, taken as a binder exactly as `truthStar_learned`
takes it; `hcodes` is (a) at `a = id`. Non-degeneracy: `truthStar_not_eventuallyConst`.
Source: vq-wiki-2-009; `li-pseudorandom` `truthStar_pseudorandom`, `truthStar_theoryTruth`,
`truthStar_hworld`
Kind: C
Fidelity: exact
Hyps: (a) except the `IsLogicalInductor` instance (OPEN T7 of `li-pseudorandom`; ledger
`partial: inductor certificate rests on li-pseudorandom T7`) -/
theorem truthStar_uniformAccuracy_false (a g : ℕ → ℕ) (ha : Function.Injective a)
    (hg : ∀ j, j < g j) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hcodes : MachineSentenceCodes (atomFamily a))
    [IsLogicalInductor (liaHistory (atomDP a (truthStar a g p) g)) (atomDP a (truthStar a g p) g)] :
    ¬ (∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      |liaHistory (atomDP a (truthStar a g p) g) n (atomFamily a n) -
        truthR (truthStar a g p) n| < ε) :=
  uniformAccuracy_false_of_pseudorandom (atomFamily a) hcodes (truthR (truthStar a g p))
    (truthStar_theoryTruth a g hg p) (truthR_bool _) hp0 hp1 (truthStar_hworld ha g p)
    succDeferral (truthStar_pseudorandom a g hg p ⟨hp0.le, hp1.le⟩ succDeferral)

/-! ## 7b — the deferred-day `thm:benford` on the family of record (OPEN) -/

/-- **OPEN (7b): the deferred-day `thm:benford` on the family of record.** For the family of
record `truthStar a g p` over the LIA of `atomDP`, `0 ≤ p ≤ 1`, injective `a`, delay `g` with
`j < g j`, and a deferral `f` that stays strictly before the decision day (`f n < g n`, so
`atom (a n)` is still undecided when the self-expert reads its price), the LIA's price of
`atom (a n)` **at the deferred day `f n`** tends to `p`:
`P_{f n}(φ_n) ≈ₙ p`. This is exactly what makes the constant forecast `c ≡ p` satisfy Corollary
B.1's `(UA)` against `Y_n = P_{f n}(φ_n)` on the literal-indicator source (in `∀ ε, ∀ᶠ` form
it *is* `(UA)` at `c ≡ p`), while against the settled value `truth ∈ {0,1}` that forecast is off
by `min p (1−p)` on every day (`min_le_abs_sub_of_bool`, market-free). Why it is open: FAF's
`lic_learning_pseudorandom_frequency` is the diagonal `P_n(φ_n) → p`; the off-diagonal price
would follow from pseudorandomness of the reindexed family `m ↦ φ_{f⁻¹ m}` relative to the same
market, and `truthStar` diagonalizes only against the enumerated day-`n` weightings evaluated on
the day-`n` market, so the price at a later day `f n` is not controlled by its definition — the
reindexed pseudorandomness is a statement `li-pseudorandom`'s `Lift.lean` schedules are shaped
for but do not give at a general injective `f` (finding F13). Whether it holds for `truthStar`
as defined is not known; a variant family diagonalizing jointly against the shifted weightings
would be the natural route. The restriction `f n < g n` matters: at `g n ≤ f n` the atom is
already decided at day `f n` and the deferred price is expected to track the settled value
instead (round-1 fidelity audit N2), so the statement is not expected to hold there. The
`IsLogicalInductor` instance is li-pseudorandom's OPEN T7 certificate, taken as a binder exactly
as `truthStar_learned` does. **Register: a conjecture, not an unproved step** (round-2
adversarial audit N5) — the missing piece is not a lemma pending a proof but a property of
`truthStar` as defined that is not known to hold; a dependent (`def-squeeze-diamond`, 7b)
should read it as "conjectured, plausibly needs a variant family". The binders `ha` and
`hcodes` do not appear in the conclusion: they are the hypotheses under which the statement is
*expected* to be provable (as in `truthStar_learned`), stated so that a proof can use them, not
a squeeze (round-2 fidelity audit N5).
Source: vq-wiki-2-009; mandate target 7b ("`Y_n` is itself `≈ p` (benford at day `f n`)");
finding F13
Kind: OPEN (conjecture)
Fidelity: exact
Hyps: n/a (the `IsLogicalInductor` instance is OPEN T7 of `li-pseudorandom`) -/
theorem truthStar_deferred_benford (a g : ℕ → ℕ) (ha : Function.Injective a)
    (hg : ∀ j, j < g j) {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hcodes : MachineSentenceCodes (atomFamily a)) (f : DeferralFunction)
    (hfg : ∀ n, f n < g n)
    [IsLogicalInductor (liaHistory (atomDP a (truthStar a g p) g)) (atomDP a (truthStar a g p) g)] :
    (fun n => liaHistory (atomDP a (truthStar a g p) g) (f n) (atomFamily a n)) ≈ₙ
      (fun _ => p) := by
  sorry

/-! ## 4c(i) — a pseudorandom truth sequence is not a generable weight of its own market -/

/-- The constant weighting `1`, as a feature progression.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def constOneW : ℕ → EF := fun _ => EF.const (1 : ℚ)

/-- The constant weighting `1` is generable, divergent, and patient for `succDeferral`.
Source: none: infrastructure (FAF `PGenerableWeighting`, `DivergentWeighting`, `DeferralPatient`)
Kind: L
Fidelity: n/a -/
theorem constOneW_weighting (P : History) :
    PGenerableWeighting constOneW ∧ DivergentWeighting constOneW P ∧
      DeferralPatient succDeferral constOneW P := by
  refine ⟨constWeighting 1, ⟨fun n => by simp [constOneW], ?_⟩, ⟨2, fun n => ?_⟩⟩
  · have hpre : prefixSum (fun n => (constOneW n).denote P) = fun n : ℕ => (n : ℝ) + 1 := by
      funext n
      simp only [prefixSum, constOneW, EF.denote_const, Rat.cast_one, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one]
      exact Nat.cast_succ n
    rw [hpre]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  · simp only [succDeferral, constOneW, EF.denote_const, Rat.cast_one, Finset.sum_const,
      nsmul_eq_mul, mul_one, Nat.card_Icc]
    have : n + 1 + 1 - n = 2 := by omega
    rw [this]
    norm_num

/-- Pseudorandomness at frequency `p > 0` forces the truth prefix sums to diverge (apply the
definition to the constant weighting `1`).
Source: mandate target 4c(i) ("`DivergentWeighting` follows from density `p > 0`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem prefixSum_truth_tendsto_atTop {P : History} {truth : ℕ → ℝ} {p : ℝ} (hp0 : 0 < p)
    (hpseudo : PseudorandomFrequency truth p succDeferral P) :
    Tendsto (prefixSum truth) atTop atTop := by
  obtain ⟨hgen, hdiv, hpat⟩ := constOneW_weighting P
  have havg := hpseudo _ hgen hdiv hpat
  have hden : ∀ n, prefixSum (fun i => (constOneW i).denote P) n = (n : ℝ) + 1 := by
    intro n
    simp only [prefixSum, constOneW, EF.denote_const, Rat.cast_one, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    exact Nat.cast_succ n
  have hnum : ∀ n, prefixSum (fun i => (constOneW i).denote P * truth i) n =
      prefixSum truth n := by
    intro n
    simp only [prefixSum, constOneW, EF.denote_const, Rat.cast_one, one_mul]
  have havg' : Tendsto (fun n => prefixSum truth n / ((n : ℝ) + 1)) atTop (𝓝 p) := by
    have h : ∀ n : ℕ, weightedAverage (fun i => (constOneW i).denote P) truth n =
        prefixSum truth n / ((n : ℝ) + 1) := by
      intro n
      rw [weightedAverage, if_neg (by rw [hden]; positivity), hnum, hden]
    have := havg
    unfold AsympEq at this
    simp only [h] at this
    simpa using this.add_const p
  -- eventually `prefixSum truth n ≥ (p/2)(n+1)`, which tends to `∞`
  have hev : ∀ᶠ n : ℕ in atTop, (p / 2) * ((n : ℝ) + 1) ≤ prefixSum truth n := by
    filter_upwards [havg'.eventually (lt_mem_nhds (by linarith : p / 2 < p))] with n hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [lt_div_iff₀ hpos] at hn
    linarith
  have hlin : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact tendsto_atTop_mono' atTop hev (Tendsto.const_mul_atTop (by positivity) hlin)

/-- **A `{0,1}` truth sequence pseudorandom with frequency `p ∈ (0,1)` relative to `P` (at
`succDeferral`) is not `PGenerableRat P`** (4c(i), the theorem the corrigibility thesis
needs: a legitimacy gate can fail to be generable). If it were, its feature `W` would be a
P-generable weighting, divergent (the prefix sums of `truth` diverge by pseudorandomness at the
constant weighting), and `succDeferral`-patient; pseudorandomness at `W` then says the
`W`-weighted average of `truth` tends to `p` — but `W_i · truth_i = truth_i` on a `{0,1}`
sequence, so that average is `1` wherever the mass is positive. Contradiction with `p < 1`.
Source: mandate target 4c(i); trust-lab-2-034 (ii-b) ("a gate needing `𝒞_A`-computation is not
`H`-generable"), here proved for the pseudorandom gate rather than assumed
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem pseudorandom_not_pgenerable {P : History} {truth : ℕ → ℝ}
    (hbool : ∀ n, truth n = 0 ∨ truth n = 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpseudo : PseudorandomFrequency truth p succDeferral P) (q : ℕ → ℚ)
    (hq : ∀ n, ((q n : ℚ) : ℝ) = truth n) : ¬ PGenerableRat P q := by
  rintro ⟨W, hW⟩
  have hden : ∀ n, (W n).denote P = truth n := fun n => by rw [hW.denote n, hq n]
  have hgen : PGenerableWeighting W := hW.toWeighting
  have hsum := prefixSum_truth_tendsto_atTop hp0 hpseudo
  have hW01 : ∀ n, 0 ≤ (W n).denote P ∧ (W n).denote P ≤ 1 := fun n => by
    rw [hden n]; rcases hbool n with h | h <;> rw [h] <;> norm_num
  have hdiv : DivergentWeighting W P := ⟨hW01, by
    have : (fun n => (W n).denote P) = truth := funext hden
    rw [this]; exact hsum⟩
  have hpat : DeferralPatient succDeferral W P := ⟨2, fun n => by
    simp only [succDeferral]
    rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
    linarith [(hW01 n).2, (hW01 (n + 1)).2]⟩
  have havg := hpseudo W hgen hdiv hpat
  -- the weighted average is eventually `1`
  have hsq : ∀ i, truth i * truth i = truth i := fun i => by
    rcases hbool i with h | h <;> rw [h] <;> norm_num
  have hev : ∀ᶠ n in atTop, weightedAverage (fun i => (W i).denote P) truth n = 1 := by
    filter_upwards [hsum.eventually (eventually_gt_atTop 0)] with n hn
    have hpre : prefixSum (fun i => (W i).denote P) n = prefixSum truth n := by
      simp only [prefixSum, hden]
    have hnum : prefixSum (fun i => (W i).denote P * truth i) n = prefixSum truth n := by
      simp only [prefixSum, hden, hsq]
    rw [weightedAverage, if_neg (by rw [hpre]; exact hn.ne'), hnum, hpre, div_self hn.ne']
  have hlim : Tendsto (fun n => weightedAverage (fun i => (W i).denote P) truth n) atTop
      (𝓝 p) := by
    have := havg
    unfold AsympEq at this
    simpa using this.add_const p
  have hlim1 : Tendsto (fun n => weightedAverage (fun i => (W i).denote P) truth n) atTop
      (𝓝 1) :=
    tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  exact absurd (tendsto_nhds_unique hlim hlim1) (by linarith)

/-- The truth values of the family of record, as a rational sequence.
Source: `li-pseudorandom` `truthR`
Kind: D
Fidelity: n/a -/
def truthQ (x : ℕ → Bool) (n : ℕ) : ℚ := if x n then 1 else 0

/-- `truthQ` casts to `truthR`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthQ_cast (x : ℕ → Bool) (n : ℕ) : ((truthQ x n : ℚ) : ℝ) = truthR x n := by
  unfold truthQ truthR
  split_ifs <;> simp

/-- **The family of record's truth sequence is not a generable weight of its own LIA** (4c(i)
on `truthStar`): `truthStar a g p` at `0 < p < 1` is pseudorandom relative to
`liaHistory (atomDP a (truthStar a g p) g)` at every deferral (`truthStar_pseudorandom`, no
inductor certificate needed), hence not `PGenerableRat` of that market. Hypotheses (a) —
this row does **not** rest on T7. Stated for every placement `a` because
`truthStar_pseudorandom` needs no injectivity; the instance of record is `a := id` (injective
and computable), for which `atomDP` has consistent stages — at a non-injective `a` a stage may
contain a literal and its negation, and the theorem is then about a possibly inconsistent
process (harmless: it only says the truth stream is not a generable weight).
Source: mandate target 4c(i) ("instantiate on `truthStar` … no inductor certificate needed for
this one"); `li-pseudorandom` `truthStar_pseudorandom`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem truthStar_not_pgenerable (a g : ℕ → ℕ) (hg : ∀ j, j < g j) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ¬ PGenerableRat (liaHistory (atomDP a (truthStar a g p) g)) (truthQ (truthStar a g p)) :=
  pseudorandom_not_pgenerable (truthR_bool _) hp0 hp1
    (truthStar_pseudorandom a g hg p ⟨hp0.le, hp1.le⟩ succDeferral) _ (truthQ_cast _)

end Cleanroom.Deference.DefSelfTrust
