import Cleanroom.Deference.DefArgmaxValue.LiarProbe
import Cleanroom.Deference.DefArgmaxValue.Characterize
import Cleanroom.Deference.DefArgmaxValue.Theorem
import Cleanroom.Deference.DefSelfTrust.Est

/-!
# `def-argmax-value` · TruthTeller: a second H3 witness, by the converse of Lemma 2 rather than
by decisiveness (repair round 1; audit r1 B1 / fidelity items 2–3)

Audit r1 found that every known inhabitant of `CondStableOn` is an eventually-decisive menu, on
which H3 holds for the trivial reason. The **truth-teller** is the liar with the comparison
reversed: `τ_n := a_{n,0}`, the selector's atom for option `0` of the menu `{1[τ_n], const s}`,
so that `τ_n` holds iff the self-expert's argmax is `0` iff `s_{f n} ≤ P_{f n}(τ_n)` — the
option that pays `1` exactly when it is chosen (`truthSentence_holds_iff`, `truthMenu_argmax_zero_iff`).

* The honest follower `truthFollower` (valued `1` when `τ_n`, `s` otherwise) has
  `E*(S_n) ≈ₙ (1 − s)·P_{f n}(τ_n) + s ≥ max(P_{f n}(τ_n), s) − o(1) = M_n − o(1)`
  (`truthFollower_estimate`, `truth_selfEndorseGE_instance`): **the self-endorsement instance holds
  whatever the price dynamics**, because being chosen raises the chosen option's value.
* Hence **H3 holds on the truth-teller menu** for the self-expert's own package
  (`condStableOn_truth_self`), by `condStableOn_of_selfEndorseGE_instance` — a proof that never
  mentions decisiveness and does not know whether the selection is eventually constant.
* The scoped theorem's full package is inhabited on it, both `i` (`scoped_value_truth`), with the
  composites selects of constants (`truthComposite_zero/one`).

Register (audit r2 B1, both lenses — **the dominance stratum**): in every `paperDP T`-world the
follower is valued `(1 − s)·1[τ_n] + s ≥ max(1[τ_n], s)`, i.e. **it pointwise dominates both
options** (`truthFollower_dominates`), so the conclusion of `scoped_value_truth` is one same-day
provind step with no hypothesis at all (`truth_value_without_hypotheses`), and the
self-endorsement instance — hence H3 — is one deferred provind step per option
(`truth_selfEndorseGE_instance_by_domination`): selection is good news in every world, the
clairvoyant case the page's one-sidedness admits. The witness is therefore **N+ (joint) /
N− (content)** for the scoped theorem, exactly as the decisive witness `scoped_value_witness`:
neither Lemma 1 nor Lemma 2 does work on it. It is also not proved to be an interior-mass
witness: H3's surplus here is `p_n(1 − p_n)` with `p_n := P_{f n}(τ_n)` (`truth_h3_surplus`),
the masses stay interior iff `p_n` does (`truth_masses_interior_iff_price_interior`), and whether
FAF's inductor keeps `p_n` frequently interior is `Open.lean`'s `truthPrice_frequently_interior`
(open problem 3 on this menu — the one OPEN of the package). Together with the liar (F23, F24):
for constant-coefficient feedback the H3-criterion "being chosen does not lower the chosen
option's value" *is* follower dominance, so that family cannot supply a content-bearing witness;
and the world-only regime's syntactic form is refuted (`WorldOnlyRefuted.lean`).

Single market (self); `[𝗣𝗔⁻ ⪯ T]`-level for the construction.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-! ## The truth-teller as the menu's own selection atom for option `0` -/

/-- The selector's quotes for the truth-teller: `[P_{f n}(a_{n,0}), s_{f n}]`.
Source: audit r1 B1 (the non-decisive candidate); mandate target 1a route (ii) (the template)
Kind: D
Fidelity: exact -/
def truthQuotes (c : Nat.Partrec.Code) (n : ℕ) : List ℚ :=
  [(paperMarketComputation T).quote (f.f n)
      (Encodable.encode (quoteAtom (Nat.pair (Encodable.encode c) (Nat.pair n 0)))),
    probeThreshold T f s n]

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The quotes are computable in `(c, n)`.
Source: none: infrastructure (`quote_of_atom_computable`, `probeThreshold_computable`)
Kind: L
Fidelity: n/a -/
theorem truthQuotes_computable (hs : 0 ≤ s) : Computable₂ (truthQuotes T f s) := by
  have h1 : Computable fun z : Nat.Partrec.Code × ℕ => (paperMarketComputation T).quote (f.f z.2)
      (Encodable.encode (quoteAtom (Nat.pair (Encodable.encode z.1) (Nat.pair z.2 0)))) :=
    quote_of_atom_computable (paperMarketComputation T) (f.computable.comp Computable.snd)
      (atomPayload_primrec 0)
  have h2 : Computable fun z : Nat.Partrec.Code × ℕ => probeThreshold T f s z.2 :=
    (probeThreshold_computable T f s hs).comp Computable.snd
  exact Computable.list_cons.comp h1 (Computable.list_cons.comp h2 (Computable.const []))

/-- **The truth-teller sentence** `τ_n := a_{n,0}`: the selector's atom for option `0` — holds iff
the self-expert's argmax on the truth-teller menu is `0`, iff `s_{f n} ≤ P_{f n}(τ_n)`.
Source: audit r1 B1; [[loop-direction]] §The liar probe (the comparison reversed)
Kind: D
Fidelity: exact -/
def truthSentence (hs : 0 ≤ s) (n : ℕ) : Sentence :=
  selectorAtom (truthQuotes T f s) eqRel T (truthQuotes_computable T f s hs) eqRel_primrec n 0

/-- The truth-teller family is e.c.
Source: none: infrastructure (`selectorAtom_codes`)
Kind: L
Fidelity: n/a -/
theorem truthSentence_codes (hs : 0 ≤ s) : MachineSentenceCodes (truthSentence T f s hs) :=
  selectorAtom_codes (truthQuotes T f s) eqRel T (truthQuotes_computable T f s hs) eqRel_primrec 0

/-- `argmaxList [p, q] = 0` iff `q ≤ p`, for nonnegative `p q` (ties to `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxList_pair_eq_zero_iff {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    argmaxList [p, q] = 0 ↔ q ≤ p := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have := (argmaxList_pair_eq_one_iff hp hq).2 hlt
    omega
  · intro hle
    unfold argmaxList
    have hm : List.foldl max 0 [p, q] = max p q := by
      simp only [List.foldl_cons, List.foldl_nil]
      rw [max_eq_right hp]
    rw [hm]
    simp only [List.findIdx_cons, List.findIdx_nil]
    rw [max_eq_left hle]
    simp

/-- **The truth-teller clause at the menu's own comparison**: a `paperDP T`-world holds `τ_n` iff
`s_{f n} ≤ P_{f n}(τ_n)`.
Source: audit r1 B1; mandate target 1a (the selection identity, route (ii))
Kind: L
Fidelity: exact -/
theorem truthSentence_holds_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (truthSentence T f s hs n) ↔
      ((probeThreshold T f s n : ℚ) : ℝ) ≤
        (liaHistory (paperDP T)) (f n) (truthSentence T f s hs n) := by
  have hq : 0 ≤ probeThreshold T f s n :=
    ((paperMarketComputation T).expectQuoteAt_mem_Icc _ _ _).1
  have hp : 0 ≤ (paperMarketComputation T).quote (f.f n)
      (Encodable.encode (truthSentence T f s hs n)) :=
    ((paperMarketComputation T).quote_mem_Icc _ _).1
  have hqe := (paperMarketComputation T).quote_exact (f.f n) (truthSentence T f s hs n)
  change (liaHistory (paperDP T)) (f n) (truthSentence T f s hs n) =
    (((paperMarketComputation T).quote (f.f n) (Encodable.encode (truthSentence T f s hs n)) : ℚ) : ℝ)
    at hqe
  have key : v.Holds (truthSentence T f s hs n) ↔
      argmaxList (truthQuotes T f s (selectorCode (truthQuotes T f s) eqRel
        (truthQuotes_computable T f s hs) eqRel_primrec) n) = 0 := by
    rw [truthSentence, selectorAtom_holds_iff (hv := hv)]
    simp [eqRel]
  rw [key]
  change argmaxList [(paperMarketComputation T).quote (f.f n)
    (Encodable.encode (truthSentence T f s hs n)), probeThreshold T f s n] = 0 ↔ _
  rw [argmaxList_pair_eq_zero_iff hp hq, hqe]
  exact (Rat.cast_le).symm

/-! ## The truth-teller menu -/

/-- **The truth-teller menu** `{1[τ_n], const s}`.
Source: audit r1 B1
Kind: D
Fidelity: exact -/
def truthMenu (hs : 0 ≤ s) : Menu 1 :=
  twoOptionMenu (fun n => literalIndicator (truthSentence T f s hs n)) (fun _ => constLUV s)
    (literalIndicator_machineThresholdCodeSeq (truthSentence_codes T f s hs)) (constLUV_codes hs)

/-- Option `0` is the truth-teller's indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem truthMenu_O_zero (hs : 0 ≤ s) :
    (truthMenu T f s hs).O 0 = fun n => literalIndicator (truthSentence T f s hs n) := rfl

/-- Option `1` is the constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem truthMenu_O_one (hs : 0 ≤ s) :
    (truthMenu T f s hs).O 1 = fun _ => constLUV s := rfl

/-- The truth-teller menu is world-valued for `s ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthMenu_valued (hs : 0 ≤ s ∧ s ≤ 1) : (truthMenu T f s hs.1).Valued (paperDP T) := by
  intro j
  fin_cases j
  · exact fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩
  · exact constLUV_valued hs (paperDP T)

/-- The quote of option `0` is the deferred price of the truth-teller, exactly.
Source: none: infrastructure (`literalIndicator_expect`)
Kind: L
Fidelity: n/a -/
theorem truthMenu_quote_zero (hs : 0 ≤ s) (n : ℕ) :
    (truthMenu T f s hs).quote (selfExpert T f) 0 n =
      (liaHistory (paperDP T)) (f n) (truthSentence T f s hs n) := by
  simp [Menu.quote, truthMenu, twoOptionMenu, literalIndicator_expect]

/-- The quote of option `1` is the threshold.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthMenu_quote_one (hs : 0 ≤ s) (n : ℕ) :
    (truthMenu T f s hs).quote (selfExpert T f) 1 n = ((probeThreshold T f s n : ℚ) : ℝ) := by
  simp [Menu.quote, truthMenu, twoOptionMenu, probeThreshold_cast]

/-- **The selection identity**: in every `paperDP T`-world, `τ_n` holds iff the self-expert's
least-index argmax on the truth-teller menu is `0` (`Menu.argmax_two`: option `0` wins iff
`m^1_n ≤ m^0_n`).
Source: audit r1 B1; mandate target 1a (the selection identity)
Kind: L
Fidelity: exact (definitional)
Hyps: (a) none -/
theorem truthMenu_argmax_zero_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    (truthMenu T f s hs).argmax (selfExpert T f) n = 0 ↔ v.Holds (truthSentence T f s hs n) := by
  rw [truthSentence_holds_iff T f s hs n v hv, Menu.argmax_two, truthMenu_quote_zero,
    truthMenu_quote_one]
  by_cases hc : ((probeThreshold T f s n : ℚ) : ℝ) ≤
      (liaHistory (paperDP T)) (f n) (truthSentence T f s hs n)
  · rw [if_pos hc]
    exact ⟨fun _ => hc, fun _ => rfl⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h hc⟩

/-- The argmax is `1` iff the truth-teller fails.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthMenu_argmax_one_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    (truthMenu T f s hs).argmax (selfExpert T f) n = 1 ↔ ¬ v.Holds (truthSentence T f s hs n) := by
  rw [← truthMenu_argmax_zero_iff T f s hs n v hv]
  generalize (truthMenu T f s hs).argmax (selfExpert T f) n = a
  fin_cases a <;> simp

/-! ## The honest follower -/

/-- **The truth-teller follower**: the select by `τ_n` between the indicator (when `τ_n`, i.e.
when option `0` is chosen) and the constant — valued `1` when `τ_n`, `s` otherwise, i.e.
`(1 − s)·1[τ_n] + s`.
Source: audit r1 B1
Kind: D
Fidelity: exact -/
def truthFollower (hs : 0 ≤ s) : ℕ → LUV :=
  selectLUV (truthSentence T f s hs) (fun n => literalIndicator (truthSentence T f s hs n))
    (fun _ => constLUV s)

/-- The follower is e.c.
Source: none: infrastructure (`selectLUV_codes`)
Kind: L
Fidelity: n/a -/
theorem truthFollower_codes (hs : 0 ≤ s) : LUV.MachineThresholdCodeSeq (truthFollower T f s hs) :=
  selectLUV_codes (truthSentence_codes T f s hs)
    (literalIndicator_machineThresholdCodeSeq (truthSentence_codes T f s hs)) (constLUV_codes hs)

/-- **The follower's world value** is `(1 − s)·1[τ_n] + s`.
Source: audit r1 B1
Kind: L
Fidelity: exact -/
theorem truthFollower_valuesAt (hs : 0 ≤ s ∧ s ≤ 1) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (truthFollower T f s hs.1 n)
      ((1 - (s : ℝ)) * v.payout (truthSentence T f s hs.1 n) + s) := by
  have h := selectLUV_valuesAt (truthSentence T f s hs.1)
    (fun n => literalIndicator (truthSentence T f s hs.1 n)) (fun _ => constLUV s) n v
    (literalIndicator_valuesAt _ (paperDP T) hv) (constLUV_valuesAt hs v)
  unfold PCWorld.payout truthFollower
  by_cases hτ : v.Holds (truthSentence T f s hs.1 n)
  · simpa [hτ, PCWorld.payout] using h
  · simpa [hτ, PCWorld.payout] using h

/-- **The follower follows the self-expert's argmax** on the truth-teller menu: when `τ_n` holds
the argmax is `0` and the select is valued as `1[τ_n]`; otherwise the argmax is `1` and the select
is valued as `const s`.
Source: audit r1 B1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem truthFollower_follows (hs : 0 ≤ s ∧ s ≤ 1) :
    Follows (paperDP T) (selfExpert T f) (truthMenu T f s hs.1) (truthFollower T f s hs.1) := by
  intro n v hv x hx
  have hsel := selectLUV_valuesAt (truthSentence T f s hs.1)
    (fun n => literalIndicator (truthSentence T f s hs.1 n)) (fun _ => constLUV s) n v
    (literalIndicator_valuesAt _ (paperDP T) hv) (constLUV_valuesAt hs v)
  show v.ValuesAt (selectLUV _ _ _ n) x
  by_cases hτ : v.Holds (truthSentence T f s hs.1 n)
  · have ha := (truthMenu_argmax_zero_iff T f s hs.1 n v hv).2 hτ
    rw [ha, truthMenu_O_zero] at hx
    rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]
    simpa [hτ] using hsel
  · have ha := (truthMenu_argmax_one_iff T f s hs.1 n v hv).2 hτ
    rw [ha, truthMenu_O_one] at hx
    rw [hx.eq (constLUV_valuesAt hs v)]
    simpa [hτ] using hsel

/-! ## The self-endorsement instance holds, whatever the prices do -/

/-- **The expert's estimate of the follower**: `E*(S_n) ≈ₙ (1 − s)·P_{f n}(τ_n) + s` (deferred
provind on `S − (1 − s)·1[τ] − s`, valued `0` in every world).
Source: audit r1 B1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truthFollower_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (selfExpert T f).estimate (truthFollower T f s hs.1) n) ≈ₙ
      (fun n => (1 - (s : ℝ)) * (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) + s) := by
  set G : ℕ → LUV := fun n => literalIndicator (truthSentence T f s hs.1 n) with hG
  have hSv : Valued (paperDP T) (truthFollower T f s hs.1) :=
    follows_valued (truthMenu_valued T f s hs) (truthFollower_follows T f s hs)
  have hGv : Valued (paperDP T) G := fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩
  have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := liaHistory (paperDP T))
    (DP := paperDP T) f hf (c₀ := fun _ => EF.const (-s)) (constWeighting _)
    (terms := [((fun _ => EF.const 1), truthFollower T f s hs.1),
      ((fun _ => EF.const (-(1 - s))), G)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact constWeighting _)
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact truthFollower_codes T f s hs.1
      · exact literalIndicator_machineThresholdCodeSeq (truthSentence_codes T f s hs.1))
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hSv
      · exact hGv)
    (B := 3) (by norm_num)
    (fun m => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
      push_cast
      have h0 : (0 : ℝ) ≤ s := by exact_mod_cast hs.1
      have h1 : (s : ℝ) ≤ 1 := by exact_mod_cast hs.2
      rw [abs_neg, abs_neg, abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)]
      norm_num
      linarith)
    (fun ε hε => Filter.Eventually.of_forall (fun n v hv ν hν => by
      have e1 : ν (truthFollower T f s hs.1 n) =
          (1 - (s : ℝ)) * v.payout (truthSentence T f s hs.1 n) + s :=
        (hν ((fun _ => EF.const 1), truthFollower T f s hs.1) (by simp)).eq
          (truthFollower_valuesAt T f s hs n v hv)
      have e2 : ν (G n) = v.payout (truthSentence T f s hs.1 n) :=
        (hν ((fun _ => EF.const (-(1 - s))), G) (by simp)).eq
          (literalIndicator_valuesAt _ (paperDP T) hv)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const, e1, e2]
      push_cast
      rw [abs_le]
      constructor <;> linarith)) (paperDP_hworld T)
  have hE : deferredExpect (liaHistory (paperDP T)) f (fun _ => EF.const (-s))
      [((fun _ => EF.const 1), truthFollower T f s hs.1), ((fun _ => EF.const (-(1 - s))), G)] =
      fun n => (selfExpert T f).estimate (truthFollower T f s hs.1) n -
        ((1 - (s : ℝ)) * (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) + s) := by
    funext n
    simp only [deferredExpect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const, Expert.self_estimate, hG, literalIndicator_expect]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **The self-endorsement instance holds on the truth-teller menu, whatever the prices do**:
`E*(S_n) ≳ₙ M_n`, since `(1 − s)·p + s ≥ max(p, s)` for `p ∈ [0,1]` and `s_{f n} → s`. Being chosen
raises the chosen option's value, so the expert endorses its selection — the opposite of the liar
(`selfEndorseGE_instance_refuted`). Register (audit r2 B1): the instance holds by domination
alone — `truth_selfEndorseGE_instance_by_domination` derives the same statement with no price
computation, since the follower is valued at least every option in every world.
Source: audit r1 B1; F23; audit r2 B1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truth_selfEndorseGE_instance (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (selfExpert T f).estimate (truthFollower T f s hs.1) n) ≳ₙ
      (fun n => (truthMenu T f s hs.1).maxQuote (selfExpert T f) n) := by
  intro ε hε
  have hest := asympEq_eventually_abs_le (truthFollower_estimate T f s hf hs)
    (show (0 : ℝ) < ε / 2 by linarith)
  have hthr := (tendsto_order.1 (probeThreshold_tendsto T f s hs)).2 ((s : ℝ) + ε / 2)
    (by linarith)
  filter_upwards [hest, hthr] with n hn1 hn2
  rw [abs_le] at hn1
  rw [Menu.maxQuote_two, truthMenu_quote_zero, truthMenu_quote_one]
  have hp1 : (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) ≤ 1 :=
    (paper_price_mem_Icc T _ _).2
  have hp0 : 0 ≤ (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) :=
    (paper_price_mem_Icc T _ _).1
  have h0 : (0 : ℝ) ≤ s := by exact_mod_cast hs.1
  have h1 : (s : ℝ) ≤ 1 := by exact_mod_cast hs.2
  have hA : (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) ≤
      (selfExpert T f).estimate (truthFollower T f s hs.1) n + ε := by nlinarith
  have hB : ((probeThreshold T f s n : ℚ) : ℝ) ≤
      (selfExpert T f).estimate (truthFollower T f s hs.1) n + ε := by nlinarith
  have := max_le hA hB
  linarith

/-- **H3 holds on the truth-teller menu for the self-expert's own package** — by the converse of
Lemma 2 (`condStableOn_of_selfEndorseGE_instance`), not by decisiveness: the proof never asks
whether the selection is eventually constant. The second inhabitant of `CondStableOn` in the
package. Register (audit r2 B1): the instance holds because the follower pointwise dominates the
menu (`truth_selfEndorseGE_instance_by_domination`) — selection is good news in every world — so
this is the **dominance stratum**, not an exercise of the scope condition's content; H3's surplus
is `p_n(1 − p_n)` (`truth_h3_surplus`) and the menu is an interior-mass witness iff
`P_{f n}(τ_n)` stays frequently interior, which is open (`Open.lean`
`truthPrice_frequently_interior`). Package-independent form: `condStableOn_truth_any_package`.
Source: audit r1 B1 / fidelity item 3; F23; audit r2 B1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_truth_self (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    CondStableOn (truthMenu T f s hs.1) (selectionPackage_self T f (truthMenu T f s hs.1)) :=
  condStableOn_of_selfEndorseGE_instance hf (truthMenu_valued T f s hs)
    (selectionPackage_self T f (truthMenu T f s hs.1)) (truthFollower_codes T f s hs.1)
    (truthFollower_follows T f s hs) (truth_selfEndorseGE_instance T f s hf hs) (paperDP_hworld T)

/-! ## The scoped theorem's full package on the truth-teller menu -/

/-- **The composite against the constant option** `½(S − K_s + 1)`: `(2 − s)/2` when `τ_n`
(`S = 1`), `½` otherwise (`S = s`) — a select of constants, slack `0`.
Source: mandate target 8a (the composite); audit r1 B1
Kind: D
Fidelity: exact (slack `0`) -/
def truthComposite_one (hs : 0 ≤ s ∧ s ≤ 1) :
    Composite (paperDP T) (truthFollower T f s hs.1) ((truthMenu T f s hs.1).O 1) where
  D := selectLUV (truthSentence T f s hs.1) (fun _ => constLUV ((2 - s) / 2))
    (fun _ => constLUV (1 / 2))
  codes := selectLUV_codes (truthSentence_codes T f s hs.1)
    (constLUV_codes (by linarith [hs.2])) (constLUV_codes (by norm_num))
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  reflected := fun n v hv xS xO hxS hxO => by
    have hS := truthFollower_valuesAt T f s hs n v hv
    have hK : v.ValuesAt ((truthMenu T f s hs.1).O 1 n) (s : ℝ) := by
      simp only [truthMenu_O_one]
      exact constLUV_valuesAt hs v
    rw [hxS.eq hS, hxO.eq hK]
    have hsel := selectLUV_valuesAt (truthSentence T f s hs.1) (fun _ => constLUV ((2 - s) / 2))
      (fun _ => constLUV (1 / 2)) n v
      (constLUV_valuesAt (s := (2 - s) / 2) ⟨by linarith [hs.2], by linarith [hs.1]⟩ v)
      (constLUV_valuesAt (s := 1 / 2) (by norm_num) v)
    refine ⟨_, hsel, ?_⟩
    unfold PCWorld.payout
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- **The composite against the truth-teller's indicator** `½(S − 1[τ] + 1)`: `½` when `τ_n`
(`S = 1 = 1[τ]`), `(1 + s)/2` otherwise (`S = s`, `1[τ] = 0`).
Source: mandate target 8a; audit r1 B1
Kind: D
Fidelity: exact (slack `0`) -/
def truthComposite_zero (hs : 0 ≤ s ∧ s ≤ 1) :
    Composite (paperDP T) (truthFollower T f s hs.1) ((truthMenu T f s hs.1).O 0) where
  D := selectLUV (truthSentence T f s hs.1) (fun _ => constLUV (1 / 2))
    (fun _ => constLUV ((1 + s) / 2))
  codes := selectLUV_codes (truthSentence_codes T f s hs.1) (constLUV_codes (by norm_num))
    (constLUV_codes (by linarith [hs.1]))
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  reflected := fun n v hv xS xO hxS hxO => by
    have hS := truthFollower_valuesAt T f s hs n v hv
    have hG : v.ValuesAt ((truthMenu T f s hs.1).O 0 n) (v.payout (truthSentence T f s hs.1 n)) := by
      simp only [truthMenu_O_zero]
      exact literalIndicator_valuesAt _ (paperDP T) hv
    rw [hxS.eq hS, hxO.eq hG]
    have hsel := selectLUV_valuesAt (truthSentence T f s hs.1) (fun _ => constLUV (1 / 2))
      (fun _ => constLUV ((1 + s) / 2)) n v (constLUV_valuesAt (s := 1 / 2) (by norm_num) v)
      (constLUV_valuesAt (s := (1 + s) / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩ v)
    refine ⟨_, hsel, ?_⟩
    unfold PCWorld.payout
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- **The scoped theorem's full package is inhabited on the truth-teller menu, both `i`** — with
H3 from the converse of Lemma 2 (`condStableOn_truth_self`). Register (audit r2 B1): **N+ (joint)
/ N− (content)** — the follower pointwise dominates both options in every world
(`truthFollower_dominates`), so this conclusion is same-day provind alone
(`truth_value_without_hypotheses`); Lemma 1, Lemma 2, concentration and H3 do no work here. The
dominance stratum, beside the decisive stratum of `scoped_value_witness`; interior mass unknown
(`truthPrice_frequently_interior`).
Source: mandate target 8 (N+); audit r1 B1; audit r2 B1
Kind: N+ (joint) / N− (content)
Fidelity: exact
Hyps: (a) none; `hf` -/
theorem scoped_value_truth (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) (i : Fin 2) :
    (fun n => (truthFollower T f s hs.1 n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => ((truthMenu T f s hs.1).O i n).expect (liaHistory (paperDP T)) n) := by
  have hTT : TotalTrust (liaHistory (paperDP T)) (paperDP T) ((selfExpert T f).recast (paperDP T)) :=
    selfTotalTrust T f hf.injective
  have hSv : Valued (paperDP T) (truthFollower T f s hs.1) :=
    follows_valued (truthMenu_valued T f s hs) (truthFollower_follows T f s hs)
  fin_cases i
  · exact scoped_value (DPE := paperDP T) (DPH := paperDP T) (fun _ hv => hv) hf
      (truthMenu_valued T f s hs) (selectionPackage_self T f (truthMenu T f s hs.1))
      (concentrationFolds_self T f hf (truthMenu T f s hs.1)
        (selectionPackage_self T f (truthMenu T f s hs.1)))
      (condStableOn_truth_self T f s hf hs) (truthFollower_codes T f s hs.1)
      (truthFollower_follows T f s hs) 0 (truthComposite_zero T f s hs) hTT
      (paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
        (truthComposite_zero T f s hs).codes
        ((truthComposite_zero T f s hs).valued hSv (truthMenu_valued T f s hs 0)))
      (paperDP_hworld T) (paperDP_hworld T)
  · exact scoped_value (DPE := paperDP T) (DPH := paperDP T) (fun _ hv => hv) hf
      (truthMenu_valued T f s hs) (selectionPackage_self T f (truthMenu T f s hs.1))
      (concentrationFolds_self T f hf (truthMenu T f s hs.1)
        (selectionPackage_self T f (truthMenu T f s hs.1)))
      (condStableOn_truth_self T f s hf hs) (truthFollower_codes T f s hs.1)
      (truthFollower_follows T f s hs) 1 (truthComposite_one T f s hs) hTT
      (paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
        (truthComposite_one T f s hs).codes
        ((truthComposite_one T f s hs).valued hSv (truthMenu_valued T f s hs 1)))
      (paperDP_hworld T) (paperDP_hworld T)

/-- Instance line at `𝗣𝗔`, `succDeferral`, `s = ½`. -/
example (i : Fin 2) :
    (fun n => (truthFollower 𝗣𝗔 succDeferral (1 / 2) (by norm_num) n).expect
      (liaHistory (paperDP 𝗣𝗔)) n) ≳ₙ
      (fun n => ((truthMenu 𝗣𝗔 succDeferral (1 / 2) (by norm_num)).O i n).expect
        (liaHistory (paperDP 𝗣𝗔)) n) :=
  scoped_value_truth 𝗣𝗔 succDeferral (1 / 2) Cleanroom.Found.LiQuoteLane.succDeferral_strict
    ⟨by norm_num, by norm_num⟩ i

/-! ## Register (audit r2 B1): the dominance stratum

In every `paperDP T`-world the honest follower is valued `(1 − s)·1[τ_n] + s ≥ max(1[τ_n], s)`:
**the follower pointwise dominates both options**. Hence the conclusion of `scoped_value_truth`
(both `i`) is one same-day provind step on `S − O^i`, with no Total Trust, no fold and no
`CondStableOn` (`truth_value_without_hypotheses`), and the self-endorsement instance — hence H3 —
is one deferred provind step per option plus `max`, with no price computation
(`truth_selfEndorseGE_instance_by_domination`). The truth-teller is therefore **N+ (joint) /
N− (content)** for the scoped theorem, exactly as the decisive witness: the second trivial
stratum (dominance) beside the first (decisiveness). Adopted from the two round-2 probes
(`audit-r2-probes/TruthDominance.lean`, `TruthDominates.lean`). -/

/-- **Pointwise domination** (audit r2 B1, both lenses): in every `paperDP T`-world the
truth-teller follower's value `(1 − s)·1[τ_n] + s` is at least every option's value (`1[τ_n]`
and `s`). Selection is good news in every world — the clairvoyant case the page's one-sidedness
admits — which is why H3 and Value are free on this menu.
Source: audit r2 adversarial B1 / fidelity B1 (probes `TruthDominance.lean`, `TruthDominates.lean`,
adopted)
Kind: L
Fidelity: exact -/
theorem truthFollower_dominates (hs : 0 ≤ s ∧ s ≤ 1) (i : Fin 2) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) (x y : ℝ)
    (hx : v.ValuesAt (truthFollower T f s hs.1 n) x)
    (hy : v.ValuesAt ((truthMenu T f s hs.1).O i n) y) : y ≤ x := by
  rw [hx.eq (truthFollower_valuesAt T f s hs n v hv)]
  have h0 : (0 : ℝ) ≤ s := by exact_mod_cast hs.1
  have h1 : (s : ℝ) ≤ 1 := by exact_mod_cast hs.2
  fin_cases i
  · have hy' : v.ValuesAt (literalIndicator (truthSentence T f s hs.1 n)) y := hy
    rw [hy'.eq (literalIndicator_valuesAt _ (paperDP T) hv)]
    unfold PCWorld.payout
    split_ifs <;> linarith
  · have hy' : v.ValuesAt (constLUV s) y := hy
    rw [hy'.eq (constLUV_valuesAt hs v)]
    unfold PCWorld.payout
    split_ifs <;> linarith

/-- **Same-day provind from domination** (generic): if `S` is valued at least `O` in every
`paperDP T`-world, the novice has `E^P_n(S_n) ≳ₙ E^P_n(O_n)` — no deference hypothesis of any
kind. The register certificate for every dominance-stratum witness.
Source: audit r2 fidelity B1 (probe adopted); none: infrastructure
Kind: L
Fidelity: n/a -/
theorem value_of_dominates {S O : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S)
    (hO : LUV.MachineThresholdCodeSeq O) (hSv : Valued (paperDP T) S) (hOv : Valued (paperDP T) O)
    (hdom : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) → ∀ x y,
      v.ValuesAt (S n) x → v.ValuesAt (O n) y → y ≤ x) :
    (fun n => (S n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => (O n).expect (liaHistory (paperDP T)) n) := by
  set ts : List (ℚ × (ℕ → LUV)) := [(1, S), (-1, O)] with hts
  have h := expect_listComb_ge_of_eventually (P := liaHistory (paperDP T)) (DP := paperDP T)
    (constStream_splice 0) (B := 1) (fun _ => by norm_num) (ts := ts)
    (fun p hp => by
      simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hS
      · exact hO)
    (listComb_worldValued _ (fun p hp => by
      simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hSv
      · exact hOv))
    0 (fun ε hε => Filter.Eventually.of_forall (fun n v hv ν hν => by
      have e1 := listComb_valuesAt_mem hν (p := (1, S)) (by simp [hts])
      have e2 := listComb_valuesAt_mem hν (p := (-1, O)) (by simp [hts])
      have := hdom n v hv _ _ e1 e2
      rw [listComb_value]
      simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      push_cast
      linarith))
    (paperDP_hworld T)
  have hE : (fun n => (listComb (fun _ => (0 : ℚ)) ts n).expect (liaHistory (paperDP T)) n) =
      fun n => (S n).expect (liaHistory (paperDP T)) n - (O n).expect (liaHistory (paperDP T)) n := by
    funext n
    rw [listComb_expect]
    simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hE] at h
  intro ε hε
  filter_upwards [h ε hε] with n hn
  try dsimp only at hn ⊢
  linarith

/-- **The conclusion of `scoped_value_truth`, for both `i`, from dominance alone**: one same-day
provind step on `S − O^i`. No Total Trust, no fold, no `CondStableOn`, not even `hf`. The N− (content)
certificate of the truth-teller witness, the twin of `witness_value_one_without_hypotheses`.
Source: audit r2 adversarial B1 / fidelity B1 (probes adopted)
Kind: C
Fidelity: exact (the statement of `scoped_value_truth`)
Hyps: (a) none -/
theorem truth_value_without_hypotheses (hs : 0 ≤ s ∧ s ≤ 1) (i : Fin 2) :
    (fun n => (truthFollower T f s hs.1 n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => ((truthMenu T f s hs.1).O i n).expect (liaHistory (paperDP T)) n) :=
  value_of_dominates T (truthFollower_codes T f s hs.1) ((truthMenu T f s hs.1).codes i)
    (follows_valued (truthMenu_valued T f s hs) (truthFollower_follows T f s hs))
    (truthMenu_valued T f s hs i) (truthFollower_dominates T f s hs i)

/-- **The self-endorsement instance on the truth-teller from deferred provind on domination alone**
(no price computation; `truthFollower_estimate` is never used): `E*(S_n) ≳ₙ m^j_n` for each `j`,
hence `≳ₙ M_n`. The same statement as `truth_selfEndorseGE_instance`; this proof shows H3 on the
truth-teller is the dominance stratum.
Source: audit r2 fidelity B1 (probe adopted)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truth_selfEndorseGE_instance_by_domination (hf : StrictlyIncreasingDeferral f)
    (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (selfExpert T f).estimate (truthFollower T f s hs.1) n) ≳ₙ
      (fun n => (truthMenu T f s hs.1).maxQuote (selfExpert T f) n) := by
  have hSv : Valued (paperDP T) (truthFollower T f s hs.1) :=
    follows_valued (truthMenu_valued T f s hs) (truthFollower_follows T f s hs)
  have hj : ∀ j : Fin 2, (fun n => (selfExpert T f).estimate (truthFollower T f s hs.1) n) ≳ₙ
      (fun n => (truthMenu T f s hs.1).quote (selfExpert T f) j n) := by
    intro j
    have h := expect_deferred_asympGE_of_eventually (P := liaHistory (paperDP T))
      (DP := paperDP T) f hf (c₀ := fun _ => EF.const 0) (constWeighting 0)
      (terms := [((fun _ => EF.const 1), truthFollower T f s hs.1),
        ((fun _ => EF.const (-1)), (truthMenu T f s hs.1).O j)])
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact constWeighting _)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact truthFollower_codes T f s hs.1
        · exact (truthMenu T f s hs.1).codes j)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hSv
        · exact truthMenu_valued T f s hs j)
      (B := 2) (by norm_num) (fun m => by simp [EF.denote_const]; try norm_num)
      (c := 0) le_rfl
      (Filter.Eventually.of_forall (fun n v hv ν hν => by
        have e1 := hν ((fun _ => EF.const 1), truthFollower T f s hs.1) (by simp)
        have e2 := hν ((fun _ => EF.const (-1)), (truthMenu T f s hs.1).O j) (by simp)
        have := truthFollower_dominates T f s hs j n v hv _ _ e1 e2
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
        push_cast
        linarith))
      (paperDP_hworld T)
    have hE : deferredExpect (liaHistory (paperDP T)) f (fun _ => EF.const 0)
        [((fun _ => EF.const 1), truthFollower T f s hs.1),
          ((fun _ => EF.const (-1)), (truthMenu T f s hs.1).O j)] =
        fun n => (selfExpert T f).estimate (truthFollower T f s hs.1) n -
          (truthMenu T f s hs.1).quote (selfExpert T f) j n := by
      funext n
      simp [deferredExpect, EF.denote_const, Expert.estimate, Menu.quote]
      try ring
    rw [hE] at h
    intro ε hε
    filter_upwards [h ε hε] with n hn
    try dsimp only at hn ⊢
    linarith
  intro ε hε
  filter_upwards [hj 0 ε hε, hj 1 ε hε] with n h0 h1
  rw [Menu.maxQuote_two]
  try dsimp only at h0 h1 ⊢
  rcases le_total ((truthMenu T f s hs.1).quote (selfExpert T f) 0 n)
      ((truthMenu T f s hs.1).quote (selfExpert T f) 1 n) with hle | hle
  · rw [max_eq_right hle]; linarith
  · rw [max_eq_left hle]; linarith

/-- **H3 holds on the truth-teller menu for every selection package of the self-expert** (the
menu-level form of `condStableOn_truth_self`; audit r2 fidelity N4) — by the converse of Lemma 2
from the dominance instance.
Source: audit r2 fidelity N4; audit r1 B1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_truth_any_package (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1)
    {I Q : Fin 2 → ℕ → LUV}
    (pkg : SelectionPackage (paperDP T) (selfExpert T f) (truthMenu T f s hs.1) I Q) :
    CondStableOn (truthMenu T f s hs.1) pkg :=
  condStableOn_of_selfEndorseGE_instance hf (truthMenu_valued T f s hs) pkg
    (truthFollower_codes T f s hs.1) (truthFollower_follows T f s hs)
    (truth_selfEndorseGE_instance_by_domination T f s hf hs) (paperDP_hworld T)

/-! ## The H3 surplus, and open problem 3 as a price question (audit r2 fidelity N1)

With `p_n := P_{f n}(τ_n)`: `Σ_j E*(Q^j) ≈ₙ (1 − s)p_n + s` (Step 1 and the follower's estimate),
`E*(I^0) ≈ₙ p_n`, `E*(I^1) ≈ₙ 1 − p_n`, `m^0_n = p_n`, `m^1_n = s_{f n} → s`, so H3's surplus is
`Σ_j E*(Q^j) − Σ_j E*(I^j)·m^j ≈ₙ p_n(1 − p_n)` — the mirror of the liar's forced deficit
`−s(1 − s)` (`probe_condStable_deficit_tendsto`), with the price unforced. The masses stay
interior iff `p_n` does (`truth_masses_interior_iff_price_interior`), which is `Open.lean`'s
`truthPrice_frequently_interior`. -/

/-- `E*(I^0_n) ≈ₙ P_{f n}(τ_n)`: the quoted bit `1[sel = 0]` is `1[τ_n]` in every world (deferred
provind at slack `0`).
Source: audit r2 fidelity N1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truth_selI_zero_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) 0) n) ≈ₙ
      (fun n => (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) := by
  have h := expect_deferred_const_mul (P := liaHistory (paperDP T)) (DP := paperDP T) f hf 1
    (X := fun n => literalIndicator (truthSentence T f s hs.1 n))
    (literalIndicator_machineThresholdCodeSeq (truthSentence_codes T f s hs.1))
    (selI_codes T f (truthMenu T f s hs.1) 0)
    (fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩) (fun _ => 0)
    tendsto_const_nhds
    (fun n v hv x hx => ⟨_, selI_reflected T f (truthMenu T f s hs.1) 0 n v hv, by
        rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]
        unfold PCWorld.payout
        by_cases hτ : v.Holds (truthSentence T f s hs.1 n)
        · have ha : (truthMenu T f s hs.1).argmax (selfExpert T f) n = 0 :=
            (truthMenu_argmax_zero_iff T f s hs.1 n v hv).2 hτ
          rw [ha]
          simp [hτ]
        · have ha : (truthMenu T f s hs.1).argmax (selfExpert T f) n = 1 :=
            (truthMenu_argmax_one_iff T f s hs.1 n v hv).2 hτ
          rw [ha]
          simp [hτ]⟩) (paperDP_hworld T)
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [Expert.self_estimate, literalIndicator_expect]

/-- `E*(I^1_n) ≈ₙ 1 − P_{f n}(τ_n)` (exhaustivity, `sum_estimate_I`).
Source: audit r2 fidelity N1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truth_selI_one_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) 1) n) ≈ₙ
      (fun n => 1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) := by
  have hI0 := truth_selI_zero_estimate T f s hf hs
  have hIsum := sum_estimate_I hf (selectionPackage_self T f (truthMenu T f s hs.1))
    (paperDP_hworld T)
  unfold AsympEq at hI0 hIsum ⊢
  have := hIsum.sub hI0
  refine (tendsto_congr (fun n => ?_)).mp (by simpa only [_root_.sub_zero, add_zero, zero_add, neg_zero, _root_.sub_self] using this)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero]
  ring

omit [Entailment.Consistent T] in
/-- The truth-teller's deferred price lies in `[0,1]`, as an absolute-value bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truth_price_abs_le (hs : 0 ≤ s) (n : ℕ) :
    |(liaHistory (paperDP T)) (f n) (truthSentence T f s hs n)| ≤ 1 := by
  rw [abs_le]
  have := paper_price_mem_Icc T (f n) (truthSentence T f s hs n)
  constructor <;> linarith [this.1, this.2]

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The threshold `s_{f n}` lies in `[0,1]`, as an absolute-value bound (belongs with
`LiarProbe.lean`; placed here to keep the rebuild local).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probeThreshold_abs_le (n : ℕ) : |((probeThreshold T f s n : ℚ) : ℝ)| ≤ 1 := by
  have h0q : 0 ≤ probeThreshold T f s n :=
    ((paperMarketComputation T).expectQuoteAt_mem_Icc _ _ _).1
  have h1q : probeThreshold T f s n ≤ 1 :=
    ((paperMarketComputation T).expectQuoteAt_mem_Icc _ _ _).2
  have h0 : (0 : ℝ) ≤ (probeThreshold T f s n : ℚ) := by exact_mod_cast h0q
  have h1 : ((probeThreshold T f s n : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1q
  rw [abs_le]; constructor <;> linarith

/-- **H3's surplus on the truth-teller is `p_n(1 − p_n)`**, `p_n := P_{f n}(τ_n)`:
`Σ_j E*(Q^j_n) − Σ_j E*(I^j_n)·m^j_n ≈ₙ p_n(1 − p_n)` for the self-expert's own package. The
mirror of the liar's forced deficit `−s(1 − s)` (`probe_condStable_deficit_tendsto`) — with the
price *unforced*: FAF's criterion pins nothing here. Whether `p_n` stays interior is
`Open.lean`'s `truthPrice_frequently_interior`.
Source: audit r2 fidelity N1; [[total-trust-implies-value]] §Necessity (the display); F23
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truth_h3_surplus (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => ∑ j, (selfExpert T f).estimate (selQ T f (truthMenu T f s hs.1) j) n -
        ∑ j, (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) j) n *
          (truthMenu T f s hs.1).quote (selfExpert T f) j n) ≈ₙ
      (fun n => (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) *
        (1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n))) := by
  have hQ : (fun n => ∑ j, (selfExpert T f).estimate (selQ T f (truthMenu T f s hs.1) j) n) ≈ₙ
      (fun n => (1 - (s : ℝ)) * (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) + s) :=
    (endorse_step1 hf (truthMenu_valued T f s hs) (selectionPackage_self T f (truthMenu T f s hs.1))
      (truthFollower_codes T f s hs.1) (truthFollower_follows T f s hs)
      (paperDP_hworld T)).symm.trans (truthFollower_estimate T f s hf hs)
  have hI0 := truth_selI_zero_estimate T f s hf hs
  have hI1 := truth_selI_one_estimate T f s hf hs
  have hp01 := truth_price_abs_le T f s hs.1
  have hq01 := probeThreshold_abs_le T f s
  have h1p01 : ∀ n, |1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)| ≤ 1 :=
    fun n => by
      rw [abs_le]
      have := paper_price_mem_Icc T (f n) (truthSentence T f s hs.1 n)
      constructor <;> linarith [this.1, this.2]
  have hT0 : (fun n => (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) 0) n *
      (truthMenu T f s hs.1).quote (selfExpert T f) 0 n) ≈ₙ
      (fun n => (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) *
        (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) := by
    have h := asympEq_mul_left_of_bounded hp01 hI0
    unfold AsympEq at h ⊢
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [truthMenu_quote_zero]
    ring
  have hT1 : (fun n => (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) 1) n *
      (truthMenu T f s hs.1).quote (selfExpert T f) 1 n) ≈ₙ
      (fun n => (1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) * s) := by
    have h1 := asympEq_mul_left_of_bounded hq01 hI1
    have h2 := asympEq_mul_left_of_bounded h1p01
      (asympEq_const_of_tendsto (probeThreshold_tendsto T f s hs))
    unfold AsympEq at h1 h2 ⊢
    have := h1.add h2
    refine (tendsto_congr (fun n => ?_)).mp (by simpa only [_root_.sub_zero, add_zero, zero_add, neg_zero, _root_.sub_self] using this)
    simp only [truthMenu_quote_one]
    ring
  unfold AsympEq at hQ hT0 hT1 ⊢
  have := hQ.sub (hT0.add hT1)
  refine (tendsto_congr (fun n => ?_)).mp (by simpa only [_root_.sub_zero, add_zero, zero_add, neg_zero, _root_.sub_self] using this)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero,
    truthMenu_quote_zero, truthMenu_quote_one]
  ring

/-- **The self-prediction mass variance on the truth-teller**: `Σ_j E*(I^j)(1 − E*(I^j)) ≈ₙ
2·p_n(1 − p_n)` (masses as the package's `E*(I^j)`, the ledger's disclosed mass notion).
Source: audit r2 fidelity N1; [[total-trust-implies-value]] §Necessity
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truth_massVariance_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => ∑ j : Fin 2, (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) j) n *
        (1 - (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) j) n)) ≈ₙ
      (fun n => 2 * ((liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) *
        (1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)))) := by
  have hI0 := truth_selI_zero_estimate T f s hf hs
  have hI1 := truth_selI_one_estimate T f s hf hs
  have hp01 := truth_price_abs_le T f s hs.1
  have h1p01 : ∀ n, |1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)| ≤ 1 :=
    fun n => by
      rw [abs_le]
      have := paper_price_mem_Icc T (f n) (truthSentence T f s hs.1 n)
      constructor <;> linarith [this.1, this.2]
  have hest : ∀ j : Fin 2, ∀ n,
      |(selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) j) n| ≤ 1 := fun j n => by
    rw [abs_le]
    have := (selfExpert T f).estimate_mem_Icc (selI T f (truthMenu T f s hs.1) j) n
    constructor <;> linarith [this.1, this.2]
  -- a(1 − a) − b(1 − b) = a·(1 − a) − b·(1 − b): use a·c ≈ b·d via a(c − d) + (a − b)d
  have key : ∀ (a b : ℕ → ℝ), (a ≈ₙ b) → (∀ n, |a n| ≤ 1) → (∀ n, |1 - b n| ≤ 1) →
      (fun n => a n * (1 - a n)) ≈ₙ (fun n => b n * (1 - b n)) := by
    intro a b hab ha hb
    have h1 : (fun n => a n * (1 - a n)) ≈ₙ (fun n => a n * (1 - b n)) :=
      asympEq_mul_left_of_bounded ha (by
        unfold AsympEq at hab ⊢
        refine (tendsto_congr (fun n => ?_)).mp (by simpa only [neg_zero] using hab.neg)
        try dsimp only
        ring)
    have h2 : (fun n => (1 - b n) * a n) ≈ₙ (fun n => (1 - b n) * b n) :=
      asympEq_mul_left_of_bounded hb hab
    unfold AsympEq at h1 h2 ⊢
    have := h1.add h2
    refine (tendsto_congr (fun n => ?_)).mp (by simpa only [_root_.sub_zero, add_zero, zero_add, neg_zero, _root_.sub_self] using this)
    try dsimp only
    ring
  have k0 := key _ _ hI0 (hest 0) h1p01
  have k1 := key _ _ hI1 (hest 1) (fun n => by
    have := hp01 n
    rw [abs_le] at this ⊢
    constructor <;> linarith [this.1, this.2])
  unfold AsympEq at k0 k1 ⊢
  have := k0.add k1
  refine (tendsto_congr (fun n => ?_)).mp (by simpa only [_root_.sub_zero, add_zero, zero_add, neg_zero, _root_.sub_self] using this)
  simp only [Fin.sum_univ_two]
  ring

/-- **The truth-teller's masses stay interior iff its price does**: `∃ c > 0, ∃ᶠ n, c ≤
Σ_j E*(I^j)(1 − E*(I^j))` ⟺ `∃ c > 0, ∃ᶠ n, c ≤ P_{f n}(τ_n) ≤ 1 − c`. So open problem 3 on this
menu — is the truth-teller an interior-mass inhabitant of `CondStableOn`? — is exactly the price
question `Open.lean` states OPEN (`truthPrice_frequently_interior`).
Source: audit r2 fidelity N1; F23 (open problem 3)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem truth_masses_interior_iff_price_interior (hf : StrictlyIncreasingDeferral f)
    (hs : 0 ≤ s ∧ s ≤ 1) :
    (∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop,
        c ≤ ∑ j : Fin 2, (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) j) n *
          (1 - (selfExpert T f).estimate (selI T f (truthMenu T f s hs.1) j) n)) ↔
      (∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop,
        c ≤ (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) ∧
          (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) ≤ 1 - c) := by
  have hV := truth_massVariance_estimate T f s hf hs
  constructor
  · rintro ⟨c, hc, hfreq⟩
    refine ⟨c / 4, by linarith, ?_⟩
    have hev := asympEq_eventually_abs_le hV (show (0 : ℝ) < c / 2 by linarith)
    refine (hfreq.and_eventually hev).mono (fun n ⟨hn1, hn2⟩ => ?_)
    rw [abs_le] at hn2
    have hp := paper_price_mem_Icc T (f n) (truthSentence T f s hs.1 n)
    have hprod : c / 4 ≤ (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) *
        (1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) := by linarith
    constructor <;> nlinarith [hp.1, hp.2]
  · rintro ⟨c, hc, hfreq⟩
    refine ⟨c * c, by positivity, ?_⟩
    have hev := asympEq_eventually_abs_le hV (show (0 : ℝ) < c * c by positivity)
    refine (hfreq.and_eventually hev).mono (fun n ⟨⟨hn1, hn2⟩, hn3⟩ => ?_)
    rw [abs_le] at hn3
    have hprod : c * c ≤ (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) *
        (1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) := by
      nlinarith
    linarith

end

end Cleanroom.Deference.DefArgmaxValue
