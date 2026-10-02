import Cleanroom.Deference.DefObstruction.Carrier

/-!
# `def-obstruction` · Tracking: 2a over the ledger process (T2) and the limit-agreement error (T6)

**2a.** For every `[0,1]`-valued table `a`, every inductor `H` over `ledgerProcess DPH a e`, and
every injective deferral `F`: under the cost-model certificates (`hR`, `hR'`, and `hG` for the
expectation reading), `∀ ε > 0, ∀ᶠ n, ½ − ε ≤ |a 0 n − 𝔼^H_{F n}(𝟙 g_n)|` (`tracking_fails`),
hence `¬ (a ≈ₙ Y)` (`not_tracking`) and `½ ≤ liminf |a 0 n − Y_n|` (`tracking_liminf`, proved
*from* the `∀ε` form because `liminf` over `ℝ` has junk conventions on unbounded sequences; here
the sequence is bounded by `1`). The whole content is `li-diagonal`'s Lemma B (re-proved over the
table-only carrier in `Carrier.lean`) plus Lemma 2.1 (`Core.lean`) plus one triangle inequality.

**Exact defect.** `½ ≤ |a 0 n − s_n|` holds for *every* `n` and *every* table (`exact_defect`,
`exact_defect_table`): the asymptotics of 2a live entirely in `Y_n − s_n → 0`, i.e. in Lemma B,
i.e. in the cost-model certificates. This is where the source's "an oracle for `A` included"
(§2.4) is exactly right (the settlement defect) and where it overreaches (the credence defect
needs the certificates; findings F-Oracle).

**No schedule hypothesis.** The mandate expected `(e 0).e n ≤ F.f n` to be needed. It is not:
Lemma B is a completed-theory provability induction (`Carrier.lean`), so the publication
schedule and the deferral are unrelated in every theorem of this file (findings F-Regimes).

**T6.** If the table converges to `L`, the credence defect converges to `max L (1 − L) ≥ ½`
(`defect_tendsto`), so `lim a = lim Y` is impossible whenever both limits exist
(`limit_agreement_fails`, `limit_agreement_impossible`), and `Y` can only converge to `0` or
`1` (`Y_limit_mem`). [[no-timely-pointwise-tower]] §6's "both sides sit at `½` in the limit" is
a local error (findings F-LimitAgreement).

Scope: one-way throughout (one reader, one arbitrary table); the `OneWayPair` and `DiagonalPair`
forms are corollaries at the end.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The exact defect -/

/-- **The exact settlement defect, every table, every day**: `½ ≤ |a 0 n − s_n|` with
`s_n = side (a 0) n = 𝟙[a 0 n ≤ ½]`. No market, no asymptotics, no hypothesis: Lemma 2.1 at the
published number. This is the part of 2a that is genuinely independent of `A`'s compute.
Scope: one-way (the table alone).
Source: [[self-referential-settlement-target]] §2.2 (the boxed bound's first two terms), §2.4; mandate T2 ("exact-defect refinement")
Kind: P
Fidelity: stronger: exact `½` with no rounding term (the ledger is exact), for every real-valued-in-`ℚ` table, not only `[0,1]`
Hyps: (a) none -/
theorem exact_defect_table (a : ℕ → ℕ → ℚ) (n : ℕ) :
    1 / 2 ≤ |(a 0 n : ℝ) - side (a 0) n| := by
  rw [side_eq_rho]
  exact defect_ge_half _

/-- The exact defect on a table-only pair.
Scope: one-way.
Source: mandate T2 ("exact-defect refinement")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem exact_defect (T : TablePair) (n : ℕ) : 1 / 2 ≤ |(T.a 0 n : ℝ) - side (T.a 0) n| :=
  exact_defect_table T.a n

/-! ## B. 2a: the anti-inductive settlement kills universal pointwise timely tracking -/

/-- **2a (headline 1), expectation reading.** For every `[0,1]`-valued table `a`, every inductor
`H` over `ledgerProcess DPH a e` (satisfiable stages), every injective deferral `F`: under the
cost-model certificates, for every `ε > 0` eventually `½ − ε ≤ |a 0 n − 𝔼^H_{F n}(𝟙 g_n)|`.
Universal pointwise timely tracking of the advised reader's own deferred credence is false by a
constant on the anti-inductive family `g_n`. Composition: `exact_defect` (Lemma 2.1 at the
published number) + `lemmaB_expect_table` (`lic_provind` through `thm:ei`, the LI step derived)
+ the triangle inequality.

**Where the corpus's `𝒞_H`-computability of the subfamily lives**: in `hR`, `hR'`, `hG` — the
e.c. certificates of the padded side families and of the padded `g` family along `F`
([[self-referential-settlement-target]] §2.2 "built from the β-ledger by an `O(n)` rule"). They
are (c) here and (a) at the witness (`Witness.lean`: `altPair_tracking_fails`, hypothesis-free).
**No schedule hypothesis**: `e` and `F` are unrelated (module docstring). The statement does not
let `a` range over `ℝ`: the ledger stores rationals; an oracle's rational outputs are a table like
any other.
Scope: one-way; deferral `F` (injective).
Source: [[self-referential-settlement-target]] §2.2–§2.4 (anson-002); [[no-timely-pointwise-tower]] §3; [[deference-in-logical-induction-v6]] §4.3; root-deference-026; lean-deference-013; root-fa-037 (2a half)
Kind: C
Fidelity: weaker: the credence bound is conditional on the e.c. side certificates (the source claims it "for every quote sequence, an oracle for `A` included"; that oracle-independence is delivered for the settlement only, `exact_defect_table`, and is conjectured false for the credence, `tracking_bound_fails_some_table`); variant: exact ledger (no rounding term `1/2n`); the family is the negated ledger literal `gDiag` itself, not a fresh atom with a biconditional axiom (equivalent in content — both are decided to `ρ(a_n)` by the same stage — not formalized; S6)
Hyps: (c) `hR`, `hR'`, `hG` — the cost model ("`A`'s side is e.c. along `F`"), (a) at the witness; `hf` — scope: injective deferral (holds for `succDeferral`, `doublingDeferral`); all else (a) (`hworld` is the carrier's, from `ledgerProcess_hworld` at construction) -/
theorem tracking_fails (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, 1 / 2 - ε ≤ |(T.a 0 n : ℝ) - T.Y F n| := by
  intro ε hε
  have hB := lemmaB_expect_table T F hf hR hR' hG
  filter_upwards [hB.eventually (Iio_mem_nhds hε)] with n hn
  have hn' : |T.Y F n - side (T.a 0) n| < ε := hn
  have h1 := exact_defect T n
  have h2 : |(T.a 0 n : ℝ) - side (T.a 0) n| ≤
      |(T.a 0 n : ℝ) - T.Y F n| + |T.Y F n - side (T.a 0) n| := abs_sub_le _ _ _
  linarith

/-- **2a, price reading**: the same bound with the reader's day-`F n` *price* of `g_n` in place
of the expectation (`lemmaB_table`; two certificates).
Scope: one-way; deferral `F` (injective).
Source: [[self-referential-settlement-target]] §2.2 (anson-002, the chat's `H⁺_{F(n)}(g_n)` read as the price)
Kind: C
Fidelity: variant: exact ledger; price reading
Hyps: (c) `hR`, `hR'` (the cost model); `hf` — scope: injective deferral -/
theorem tracking_fails_price (T : TablePair) (F : DeferralFunction)
    (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, 1 / 2 - ε ≤ |(T.a 0 n : ℝ) - T.Yprice F n| := by
  intro ε hε
  have hB := lemmaB_table T F hf hR hR'
  filter_upwards [hB.eventually (Iio_mem_nhds hε)] with n hn
  have hn' : |T.H (F n) (gDiag n) - side (T.a 0) n| < ε := hn
  have h1 := exact_defect T n
  have h2 : |(T.a 0 n : ℝ) - side (T.a 0) n| ≤
      |(T.a 0 n : ℝ) - T.Yprice F n| + |T.H (F n) (gDiag n) - side (T.a 0) n| :=
    abs_sub_le _ _ _
  linarith

/-- **2a as `¬ Tracking`**: the published table does not asymptotically equal the reader's
deferred credence, `¬ (a ≈ₙ Y)` over FAF's `AsympEq`.
Scope: one-way; deferral `F` (injective).
Source: [[self-referential-settlement-target]] §1 (the headline "to be killed"), §2.2; `SelfReferentialTarget.lean:tracking_fails` (the earlier form, over a named `hLIPI`)
Kind: C
Fidelity: exact (the earlier Lean's `¬ Approx a Y` with the LI step now derived)
Hyps: (c) `hR`, `hR'`, `hG` (the cost model); `hf` — scope: injective deferral -/
theorem not_tracking (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F)) :
    ¬ ((fun n => (T.a 0 n : ℝ)) ≈ₙ T.Y F) := by
  intro h
  unfold AsympEq at h
  have h1 : Tendsto (fun n => |(T.a 0 n : ℝ) - T.Y F n|) atTop (𝓝 0) := by
    simpa using h.abs
  have h2 := h1.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have h3 := tracking_fails T F hf hR hR' hG (1 / 4) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := (h3.and h2).exists
  have hn2' : |(T.a 0 n : ℝ) - T.Y F n| < 1 / 4 := hn2
  linarith

/-- The credence defect is bounded by `1` (both the table and the expectation lie in `[0,1]`),
so its `liminf` over `ℝ` is the genuine limit inferior.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem defect_le_one (T : TablePair) (F : DeferralFunction) (n : ℕ) :
    |(T.a 0 n : ℝ) - T.Y F n| ≤ 1 := by
  have ha0 : (0 : ℝ) ≤ T.a 0 n := by exact_mod_cast (T.range 0 n).1
  have ha1 : (T.a 0 n : ℝ) ≤ 1 := by exact_mod_cast (T.range 0 n).2
  obtain ⟨hY0, hY1⟩ := T.Y_mem_Icc F n
  rw [abs_le]
  constructor <;> linarith

/-- **2a, `liminf` form**: `½ ≤ liminf_n |a 0 n − Y_n|`. Proved *from* the `∀ε` form
(`tracking_fails`): Mathlib's `Filter.liminf` over `ℝ` is a `sSup` with junk conventions on
sequences unbounded above, so the bound `defect_le_one` is what makes this form say what it
reads; the `∀ε` form is primary.
Scope: one-way; deferral `F` (injective).
Source: [[self-referential-settlement-target]] §2.2 (the boxed `liminf ≥ ½`); `SelfReferentialTarget.lean:tracking_fails_liminf`
Kind: C
Fidelity: exact
Hyps: (c) `hR`, `hR'`, `hG` (the cost model); `hf` — scope: injective deferral -/
theorem tracking_liminf (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F)) :
    1 / 2 ≤ liminf (fun n => |(T.a 0 n : ℝ) - T.Y F n|) atTop := by
  have hco : IsCoboundedUnder (· ≥ ·) atTop (fun n => |(T.a 0 n : ℝ) - T.Y F n|) :=
    (isBoundedUnder_of ⟨1, fun n => defect_le_one T F n⟩).isCoboundedUnder_ge
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h := le_liminf_of_le hco (tracking_fails T F hf hR hR' hG ε hε)
  linarith

/-! ## C. The corollaries over `li-quote-lane`'s and `li-diagonal`'s carriers -/

/-- **2a over the one-way pair** (`A` an inductor publishing its own prices): the instance of
`tracking_fails` at `TablePair.ofOneWay`. The publisher's inductor certificate is not used.
Scope: one-way.
Source: [[self-referential-settlement-target]] §2.2 (anson-002); mandate T2 (`tracking_fails_oneWay`)
Kind: L (instance of `tracking_fails`)
Fidelity: exact
Hyps: (c) `hR`, `hR'`, `hG`; `hf` — scope: injective deferral -/
theorem tracking_fails_oneWay (p : OneWayPair) (F : DeferralFunction)
    (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide p.a F))
    (hR' : MachineSentenceCodes (padFalseSide p.a F))
    (hG : MachineSentenceCodes (padG F)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |(p.a 0 n : ℝ) - (LUV.indicatorOf (gDiag n)).expect p.H (F n)| :=
  tracking_fails (TablePair.ofOneWay p) F hf hR hR' hG

/-- **2a over the diagonal pair** (`A` reads `H`): `A`'s published price of the median threshold
`⌜Y_n > ½⌝` fails to track the reader's deferred credence of `g_n` by `½`. Two-way only in the
*object* (the pair's inhabitation is `li-coupled-pair`'s OPEN); the *proof* uses nothing of the
cross-reading — it is `tracking_fails_oneWay` with `DiagonalPair.a_eq_price` renaming the table.
Scope: two-way (`partial: over the OPEN pair`); deferral `F` (injective).
Source: [[self-referential-settlement-target]] §2.2 (anson-002); [[li-diagonal-mandate]] § Definitions of record (`DiagonalPair`); mandate T2
Kind: L (instance of `tracking_fails`)
Fidelity: variant: `A`'s price of the median threshold in place of `A`'s expectation (the pair's own disclosure)
Hyps: (c) `hR`, `hR'`, `hG`; `hf` — scope: injective deferral. (`D.cross.reflected` is the pair's standing (c), carried by the object and unused by this proof — not a hypothesis of the theorem.) -/
theorem tracking_fails_diagonalPair {F : DeferralFunction} (D : DiagonalPair F)
    (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide D.pair.a F))
    (hR' : MachineSentenceCodes (padFalseSide D.pair.a F))
    (hG : MachineSentenceCodes (padG F)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |D.pair.A n ((D.Y n).gt (1 / 2)) -
        (LUV.indicatorOf (gDiag n)).expect D.pair.H (F n)| := by
  intro ε hε
  filter_upwards [tracking_fails_oneWay D.pair F hf hR hR' hG ε hε] with n hn
  rwa [D.a_eq_price n] at hn

/-! ## D. T6: limit agreement is not untouched by the diagonal -/

/-- **The credence defect converges with the table**: if `a 0 n → L` then
`|a 0 n − Y_n| → max L (1 − L)`. The defect against the *side* is `max a (1 − a)`
(`defect_eq_max`), a continuous function of the quote, and `Y_n − s_n → 0` (Lemma B).
Scope: one-way; deferral `F` (injective).
Source: [[no-timely-pointwise-tower]] §6 (the sentence this refutes); anson-015; mandate T6
Kind: C
Fidelity: exact
Hyps: (c) `hR`, `hR'`, `hG` (the cost model); `hf` — scope: injective deferral -/
theorem defect_tendsto (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F)) {L : ℝ}
    (hL : Tendsto (fun n => (T.a 0 n : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n => |(T.a 0 n : ℝ) - T.Y F n|) atTop (𝓝 (max L (1 - L))) := by
  have h1 : Tendsto (fun n => |(T.a 0 n : ℝ) - side (T.a 0) n|) atTop (𝓝 (max L (1 - L))) := by
    have heq : (fun n => |(T.a 0 n : ℝ) - side (T.a 0) n|) =
        fun n => max (T.a 0 n : ℝ) (1 - T.a 0 n) := by
      funext n; rw [side_eq_rho, defect_eq_max]
    rw [heq]
    exact hL.max (tendsto_const_nhds.sub hL)
  have hB := lemmaB_expect_table T F hf hR hR' hG
  have h2 : Tendsto (fun n => |(T.a 0 n : ℝ) - T.Y F n| - |(T.a 0 n : ℝ) - side (T.a 0) n|)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hB
    rw [Real.norm_eq_abs]
    calc |(|(T.a 0 n : ℝ) - T.Y F n| - |(T.a 0 n : ℝ) - side (T.a 0) n|)|
        ≤ |((T.a 0 n : ℝ) - T.Y F n) - ((T.a 0 n : ℝ) - side (T.a 0) n)| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |T.Y F n - side (T.a 0) n| := by
          rw [abs_sub_comm]; congr 1; ring
  have h3 := h2.add h1
  rw [zero_add] at h3
  refine h3.congr fun n => ?_
  ring

/-- **T6 (headline). Limit agreement fails on the diagonal**: if the table converges to `L` and
the reader's deferred credence converges to `L'`, then `½ ≤ |L − L'|`. In particular
`lim a = lim Y` is impossible whenever both limits exist. Refutes [[no-timely-pointwise-tower]]
§6's "the diagonal is consistent with [limit agreement] (both sides sit at `½` in the limit)"
**wherever the side is e.c. along `F`** (the certificates): there `Y_n` never sits at `½`
(`Y_limit_mem`), and at `a → ½` the defect is exactly `½` (`max ½ ½ = ½`). On the constant-`½`
table the refutation is hypothesis-free (`halfPair_no_limit_agreement_at_half`, `Witness.lean`);
for a table with a non-e.c. side F-Oracle's conjecture would allow `a → ½`, `Y → ½`, so the
diagonal's compatibility with limit agreement is open exactly where 2a's credence form is
(findings F-LimitAgreement; repair round 1, audit B2).
Scope: one-way; deferral `F` (injective).
Source: [[no-timely-pointwise-tower]] §6 (anson-015, local error); mandate T6
Kind: P (real analysis after `defect_tendsto`)
Fidelity: exact, under the certificates (weaker than an unconditional refutation of §6's sentence)
Hyps: (c) `hR`, `hR'`, `hG` (the cost model); `hf` — scope: injective deferral -/
theorem limit_agreement_fails (T : TablePair) (F : DeferralFunction)
    (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F)) {L L' : ℝ}
    (hL : Tendsto (fun n => (T.a 0 n : ℝ)) atTop (𝓝 L))
    (hL' : Tendsto (T.Y F) atTop (𝓝 L')) :
    1 / 2 ≤ |L - L'| := by
  have h := defect_tendsto T F hf hR hR' hG hL
  have h' : Tendsto (fun n => |(T.a 0 n : ℝ) - T.Y F n|) atTop (𝓝 |L - L'|) :=
    (hL.sub hL').abs
  have heq := tendsto_nhds_unique h h'
  rw [← heq]
  rcases le_or_gt L (1 / 2) with hl | hl
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left hl.le

/-- **T6, the source's sentence negated**: the table and the reader's deferred credence never
share a limit.
Scope: one-way; deferral `F` (injective).
Source: [[no-timely-pointwise-tower]] §6 (anson-015)
Kind: L
Fidelity: exact
Hyps: (c) `hR`, `hR'`, `hG`; `hf` — scope: injective deferral -/
theorem limit_agreement_impossible (T : TablePair) (F : DeferralFunction)
    (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F)) (L : ℝ) :
    ¬ (Tendsto (fun n => (T.a 0 n : ℝ)) atTop (𝓝 L) ∧ Tendsto (T.Y F) atTop (𝓝 L)) := by
  rintro ⟨hL, hL'⟩
  have h := limit_agreement_fails T F hf hR hR' hG hL hL'
  rw [sub_self, abs_zero] at h
  linarith

/-- **The reader's deferred credence converges only to `0` or `1`** on the diagonal (it tracks
the `{0,1}`-valued side).
Scope: one-way; deferral `F` (injective).
Source: [[anson-inventory]] anson-015 (the inventory's refutation of [[no-timely-pointwise-tower]] §6: "if `Y_n` converges it converges to `0` or `1`, never `½`" is the inventory's sentence, not the note's)
Kind: L
Fidelity: exact, under the certificates (for a table with a non-e.c. side the conclusion is not derivable and F-Oracle conjectures it false)
Hyps: (c) `hR`, `hR'`, `hG`; `hf` — scope: injective deferral -/
theorem Y_limit_mem (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F)) {L' : ℝ}
    (hL' : Tendsto (T.Y F) atTop (𝓝 L')) : L' = 0 ∨ L' = 1 := by
  have hB := lemmaB_expect_table T F hf hR hR' hG
  have hB' : Tendsto (fun n => T.Y F n - side (T.a 0) n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hB
  have hs : Tendsto (fun n => side (T.a 0) n) atTop (𝓝 L') := by
    have := hL'.sub hB'
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    ring
  have hcl : IsClosed ({0, 1} : Set ℝ) := (Set.toFinite _).isClosed
  have hmem : L' ∈ ({0, 1} : Set ℝ) :=
    hcl.mem_of_tendsto hs (Eventually.of_forall fun n => by
      rcases side_eq_zero_or_one (T.a 0) n with h | h <;> simp [h])
  simpa using hmem

end Cleanroom.Deference.DefObstruction
