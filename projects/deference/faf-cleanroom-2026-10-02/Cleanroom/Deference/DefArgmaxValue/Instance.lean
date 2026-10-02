import Cleanroom.Deference.DefArgmaxValue.Theorem
import Cleanroom.Deference.DefArgmaxValue.Refuted
import Cleanroom.Deference.DefSqueezeDiamond.ProbeFollower
import Cleanroom.Deference.DefSelfTrust.Est

/-!
# `def-argmax-value` · Instance: the N+ witnesses (targets 4c N+, 8 N+)

* **`condStableOn_of_eventually_decisive`** (4c N+): on a two-option menu whose option `0` is
  eventually strictly top-quoted, every selection package satisfies `CondStableOn` — with
  equality: both sides are `≈ₙ E*(O^0)` (eventually `I^0 = 1`, `I^1 = 0`, `Q^0 ≈ O^0`, `Q^1 ≈ 0`
  in every world; deferred provind on the eventual world identities).
* **`condStableOn_probe_self`**: instantiated on `def-squeeze-diamond`'s probe menu `{G, K_½}`
  with `G := 1[θ_n]`, `θ` the liar of `LiarProbe.lean` at `s = ½` — pinned at `½`, undecided —
  and `K_½ = const ¼`: eventually decisive, so H3 holds non-trivially on a menu whose top option
  is a genuine diagonal source.
* **`scoped_value_witness`** (8 N+): the scoped theorem with **every hypothesis discharged** on
  that menu for the self-expert: Total Trust (`selfTotalTrust`), the fold
  (`concentrationFolds_self`), the package (`selectionPackage_self`), H3
  (`condStableOn_probe_self`), the follower (`probeFollower_follows`), the ramp quotes
  (`paperExpert_rampQuotesAvailable`), and the composites — on this menu the rescaled
  differences `½(S − O^i + 1)` are selects of constants by the selector sentence and `θ`
  (`probeComposite_zero`, `probeComposite_one`), so the rich ledger is built, not assumed.

Construction-facing; single market (self).
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## 4c N+ — eventually-decisive menus satisfy H3 with equality -/

/-- **Conditional-stability holds on an eventually-decisive two-option menu** (target 4c N+): if
option `0` is eventually strictly top-quoted, then for every selection package both sides of
`CondStableOn` are `≈ₙ E*(O^0_n)` — eventually `I^0 = 1`, `I^1 = 0` and `Q^0 ≈ O^0`, `Q^1 ≈ 0`
in every world — so H3 holds (with equality, not merely `≳ₙ`).
Source: mandate target 4c (N+: "`CondStableOn` holds with equality on eventually-decisive menus");
2-018
Kind: C
Fidelity: exact (stronger: equality)
Hyps: (a); `hf`; `hdec` (eventual decisiveness) -/
theorem condStableOn_of_eventually_decisive {DP : DeductiveProcess} {E : Expert DP}
    [IsLogicalInductor E.A DP] (hf : StrictlyIncreasingDeferral E.f) {M : Menu 1}
    (hM : M.Valued DP) {I Q : Fin 2 → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (hdec : ∀ᶠ n in atTop, M.quote E 1 n < M.quote E 0 n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : CondStableOn M pkg := by
  have hsel : ∀ᶠ n in atTop, M.argmax E n = 0 :=
    hdec.mono (fun n hn => by rw [Menu.argmax_two, if_pos hn.le])
  -- E*(Q 0) ≈ E*(O 0)
  have hQ0 : (fun n => E.estimate (Q 0) n) ≈ₙ (fun n => E.estimate (M.O 0) n) := by
    have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := E.A) (DP := DP) E.f hf
      (c₀ := fun _ => EF.const 0) (constWeighting 0)
      (terms := [((fun _ => EF.const 1), Q 0), ((fun _ => EF.const (-1)), M.O 0)])
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact constWeighting _)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact pkg.codes_Q 0
        · exact M.codes 0)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact pkg.valued_Q hM 0
        · exact hM 0)
      (B := 2) (by norm_num) (fun m => by simp [EF.denote_const]; try norm_num)
      (fun ε hε => by
        filter_upwards [hsel, (tendsto_order.1 pkg.slack_tendsto).2 ε hε] with n hn hs v hv ν hν
        obtain ⟨x, hx⟩ := hM 0 n v hv
        obtain ⟨z, hz, hb⟩ := pkg.reflected_Q 0 n v hv x hx
        have e1 : ν (Q 0 n) = z := (hν ((fun _ => EF.const 1), Q 0) (by simp)).eq hz
        have e2 : ν (M.O 0 n) = x := (hν ((fun _ => EF.const (-1)), M.O 0) (by simp)).eq hx
        rw [hn, if_pos rfl, mul_one] at hb
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const,
          e1, e2]
        push_cast
        have : (0 : ℝ) + (1 * z + (-1 * x + 0)) = z - x := by ring
        rw [this]
        exact hb.trans hs.le) hworld
    have hE : deferredExpect E.A E.f (fun _ => EF.const 0)
        [((fun _ => EF.const 1), Q 0), ((fun _ => EF.const (-1)), M.O 0)] =
        fun n => E.estimate (Q 0) n - E.estimate (M.O 0) n := by
      funext n
      simp [deferredExpect, EF.denote_const, Expert.estimate]
      try ring
    rw [hE] at h
    unfold AsympEq at h ⊢
    simpa using h
  -- E*(Q 1) ≈ 0, E*(I 0) ≈ 1, E*(I 1) ≈ 0
  have hQ1 : (fun n => E.estimate (Q 1) n) ≈ₙ (fun _ => (0 : ℝ)) := by
    have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := E.A) (DP := DP) E.f hf
      (c₀ := fun _ => EF.const 0) (constWeighting 0) (terms := [((fun _ => EF.const 1), Q 1)])
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact constWeighting 1)
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact pkg.codes_Q 1)
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact pkg.valued_Q hM 1)
      (B := 1) (by norm_num) (fun m => by simp [EF.denote_const])
      (fun ε hε => by
        filter_upwards [hsel, (tendsto_order.1 pkg.slack_tendsto).2 ε hε] with n hn hs v hv ν hν
        obtain ⟨x, hx⟩ := hM 1 n v hv
        obtain ⟨z, hz, hb⟩ := pkg.reflected_Q 1 n v hv x hx
        have e1 : ν (Q 1 n) = z := (hν ((fun _ => EF.const 1), Q 1) (by simp)).eq hz
        rw [hn, if_neg (by decide), mul_zero, _root_.sub_zero] at hb
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const, e1]
        push_cast
        have : (0 : ℝ) + (1 * z + 0) = z := by ring
        rw [this]
        exact hb.trans hs.le) hworld
    have hE : deferredExpect E.A E.f (fun _ => EF.const 0) [((fun _ => EF.const 1), Q 1)] =
        fun n => E.estimate (Q 1) n := by
      funext n
      simp [deferredExpect, EF.denote_const]
    rwa [hE] at h
  have hI : ∀ (j : Fin 2) (b : ℚ), (∀ᶠ n in atTop, (if M.argmax E n = j then (1 : ℝ) else 0) = b) →
      (fun n => E.estimate (I j) n) ≈ₙ (fun _ => (b : ℝ)) := by
    intro j b hb
    have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := E.A) (DP := DP) E.f hf
      (c₀ := fun _ => EF.const (-b)) (constWeighting _) (terms := [((fun _ => EF.const 1), I j)])
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact constWeighting 1)
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact pkg.codes_I j)
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact pkg.valued_I j)
      (B := 1 + |(b : ℝ)|) (by positivity)
      (fun m => by simp [EF.denote_const]; try linarith [abs_nonneg (b : ℝ)])
      (fun ε hε => by
        filter_upwards [hb] with n hn v hv ν hν
        have e1 : ν (I j n) = (if M.argmax E n = j then (1 : ℝ) else 0) :=
          (hν ((fun _ => EF.const 1), I j) (by simp)).eq (pkg.reflected_I j n v hv)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const, e1,
          hn]
        push_cast
        simp
        exact hε.le) hworld
    have hE : deferredExpect E.A E.f (fun _ => EF.const (-b)) [((fun _ => EF.const 1), I j)] =
        fun n => E.estimate (I j) n - b := by
      funext n
      simp [deferredExpect, EF.denote_const, Expert.estimate]
      ring
    rw [hE] at h
    unfold AsympEq at h ⊢
    simpa using h
  have hI0 := hI 0 1 (hsel.mono (fun n hn => by rw [hn, if_pos rfl]; norm_num))
  have hI1 := hI 1 0 (hsel.mono (fun n hn => by rw [hn, if_neg (by decide)]; norm_num))
  -- assemble
  have hleft : (fun n => ∑ j, E.estimate (Q j) n) ≈ₙ (fun n => E.estimate (M.O 0) n) := by
    have := hQ0.add hQ1
    unfold AsympEq at this
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    simp [Fin.sum_univ_two]
  have hright : (fun n => ∑ j, E.estimate (I j) n * M.quote E j n) ≈ₙ
      (fun n => E.estimate (M.O 0) n) := by
    have hb0 : ∀ n, |M.quote E 0 n| ≤ 1 := fun n => by
      rw [abs_le]; have := E.estimate_mem_Icc (M.O 0) n; constructor <;> linarith [this.1, this.2]
    have hb1 : ∀ n, |M.quote E 1 n| ≤ 1 := fun n => by
      rw [abs_le]; have := E.estimate_mem_Icc (M.O 1) n; constructor <;> linarith [this.1, this.2]
    have h0 := asympEq_mul_left_of_bounded hb0 hI0
    have h1 := asympEq_mul_left_of_bounded hb1 hI1
    have := h0.add h1
    unfold AsympEq at this
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    simp only [Fin.sum_univ_two, Menu.quote]
    ring
  exact (hleft.trans hright.symm).asympGE

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction)

/-! ## The witness menu: the pinned liar against the constant ¼ -/

/-- The diagonal source of the witness menu: `G_n := 1[θ_n]`, `θ` the liar of the probe at `s = ½`
(pinned at `½`, undecided).
Source: mandate target 4c ("instantiate on `probeData_self` with `G` the diagonal source")
Kind: D
Fidelity: exact -/
def witnessG : ℕ → LUV := fun n => literalIndicator (liarSentence T f (1 / 2) (by norm_num) n)

omit [Entailment.Consistent T] in
/-- The source is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessG_codes : LUV.MachineThresholdCodeSeq (witnessG T f) :=
  literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f (1 / 2) (by norm_num))

omit [Entailment.Consistent T] in
/-- The source is world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessG_valued : Valued (paperDP T) (witnessG T f) :=
  fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩

/-- **The witness menu** `{1[θ_n], const ¼}` — `def-squeeze-diamond`'s probe menu at `ε = ½`.
Source: mandate target 4c, 8c
Kind: D
Fidelity: exact -/
def witnessMenu : Menu 1 :=
  twoOptionMenu (witnessG T f) (probeConst (1 / 2)) (witnessG_codes T f)
    (constLUV_codes (probeConst_mem (by norm_num) (by norm_num)).1)

omit [Entailment.Consistent T] in
/-- The witness menu is valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessMenu_valued : (witnessMenu T f).Valued (paperDP T) := by
  intro j
  fin_cases j
  · exact witnessG_valued T f
  · exact constLUV_valued (probeConst_mem (by norm_num) (by norm_num)) (paperDP T)

/-- **The witness menu is eventually decisive**: `E*(G) = P_{f n}(θ_n) → ½` while
`E*(K_½) → ¼`.
Source: mandate target 4c (N+); `def-lattice-arrows` `probe_eventually_top`
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem witnessMenu_decisive (hf : StrictlyIncreasingDeferral f) :
    ∀ᶠ n in atTop, (witnessMenu T f).quote (selfExpert T f) 1 n <
      (witnessMenu T f).quote (selfExpert T f) 0 n := by
  have hG : Tendsto (fun n => (witnessMenu T f).quote (selfExpert T f) 0 n) atTop
      (𝓝 ((1 / 2 : ℚ) : ℝ)) := by
    have := liarPrice_tendsto_s T f (1 / 2) hf (by norm_num) (by norm_num)
    refine (tendsto_congr (fun n => ?_)).mp this
    simp [witnessMenu, twoOptionMenu, Menu.quote, witnessG, literalIndicator_expect]
  have hK : Tendsto (fun n => (witnessMenu T f).quote (selfExpert T f) 1 n) atTop
      (𝓝 (((1 - 1 / 2) / 2 : ℚ) : ℝ)) := by
    have := tendsto_of_asympEq_const (asympEq_comp_deferral (expect_constLUV_asympEq
      (P := liaHistory (paperDP T)) (DP := paperDP T) (probeConst_mem (ε := 1 / 2) (by norm_num)
        (by norm_num)) (paperDP_hworld T)) f)
    refine (tendsto_congr (fun n => ?_)).mp this
    simp [witnessMenu, twoOptionMenu, Menu.quote, probeConst]
  have h1 := (tendsto_order.1 hG).1 ((3 / 8 : ℚ) : ℝ) (by norm_num)
  have h2 := (tendsto_order.1 hK).2 ((3 / 8 : ℚ) : ℝ) (by norm_num)
  filter_upwards [h1, h2] with n hn1 hn2
  exact lt_trans hn2 hn1

/-- **H3 holds on the witness menu for the self-expert's own package** (target 4c N+): the
scope condition is satisfied on a menu whose top option is a pinned undecided diagonal source —
by eventual decisiveness (the selection is eventually the constant `0`), i.e. in the stratum
the page of record calls "automatically trivial" ([[total-trust-implies-value]] §Hypotheses,
"Reading"); N+ for inhabitation of the predicate, not an interior-mass witness (audit r1
fidelity item 2, B1).
Source: mandate target 4c (`condStableOn_probe`)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_probe_self (hf : StrictlyIncreasingDeferral f) :
    CondStableOn (witnessMenu T f) (selectionPackage_self T f (witnessMenu T f)) :=
  condStableOn_of_eventually_decisive (E := selfExpert T f) hf (witnessMenu_valued T f)
    (selectionPackage_self T f (witnessMenu T f)) (witnessMenu_decisive T f hf) (paperDP_hworld T)

/-! ## The follower and the composites -/

/-- The follower on the witness menu: `def-squeeze-diamond`'s `probeFollower` (the select by the
decided comparison `E*(K_½) ≤ E*(G)`).
Source: `def-squeeze-diamond` `probeFollower`
Kind: D
Fidelity: exact -/
def witnessS : ℕ → LUV :=
  Cleanroom.Deference.DefSqueezeDiamond.probeFollower T f (ε := 1 / 2) (by norm_num)
    (witnessG_codes T f)

/-- The selector sentence of the witness follower.
Source: `def-squeeze-diamond` `followSentence`
Kind: D
Fidelity: n/a -/
def witnessσ : ℕ → Sentence := followSentence T f (ε := 1 / 2) (by norm_num) (witnessG_codes T f)

omit [Entailment.Consistent T] in
/-- The follower follows the self-expert's argmax on the witness menu.
Source: `def-squeeze-diamond` `probeFollower_follows`
Kind: L
Fidelity: n/a -/
theorem witnessS_follows :
    Follows (paperDP T) (selfExpert T f) (witnessMenu T f) (witnessS T f) :=
  Cleanroom.Deference.DefSqueezeDiamond.probeFollower_follows T f (by norm_num) (by norm_num)
    (witnessG_codes T f) (witnessG_valued T f)

omit [Entailment.Consistent T] in
/-- The follower is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessS_codes : LUV.MachineThresholdCodeSeq (witnessS T f) :=
  Cleanroom.Deference.DefSqueezeDiamond.probeFollower_codes T f (by norm_num) (by norm_num)
    (witnessG_codes T f)

omit [Entailment.Consistent T] in
open Classical in
/-- The follower's world value: `payout θ_n` when the selector holds, `¼` otherwise.
Source: none: infrastructure (`selectLUV_valuesAt`)
Kind: L
Fidelity: n/a -/
theorem witnessS_valuesAt (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (witnessS T f n)
      (if v.Holds (witnessσ T f n) then v.payout (liarSentence T f (1 / 2) (by norm_num) n)
        else (((1 - 1 / 2) / 2 : ℚ) : ℝ)) :=
  selectLUV_valuesAt (witnessσ T f) (witnessG T f) (probeConst (1 / 2)) n v
    (literalIndicator_valuesAt _ (paperDP T) hv)
    (constLUV_valuesAt (probeConst_mem (by norm_num) (by norm_num)) v)

/-- **The composite against the constant option** `½(S − K_½ + 1)`: `½` when the selector fails
(`S = K`), else `⅞` or `⅜` by `θ` (`S = G`) — a select of constants.
Source: mandate target 8a (the composite, built on the witness menu)
Kind: D
Fidelity: exact -/
def witnessD1 : ℕ → LUV :=
  selectLUV (witnessσ T f)
    (selectLUV (liarSentence T f (1 / 2) (by norm_num)) (fun _ => constLUV (7 / 8))
      (fun _ => constLUV (3 / 8)))
    (fun _ => constLUV (1 / 2))

/-- **The composite against the source** `½(S − G + 1)`: `½` when the selector holds (`S = G`),
else `⅛` or `⅝` by `θ`.
Source: mandate target 8a
Kind: D
Fidelity: exact -/
def witnessD0 : ℕ → LUV :=
  selectLUV (witnessσ T f) (fun _ => constLUV (1 / 2))
    (selectLUV (liarSentence T f (1 / 2) (by norm_num)) (fun _ => constLUV (1 / 8))
      (fun _ => constLUV (5 / 8)))

omit [Entailment.Consistent T] in
/-- `witnessD1` is the composite of the follower against option `1`.
Source: mandate target 8a
Kind: C
Fidelity: exact (slack `0`)
Hyps: (a) none -/
def probeComposite_one : Composite (paperDP T) (witnessS T f) ((witnessMenu T f).O 1) where
  D := witnessD1 T f
  codes := selectLUV_codes (followSentence_codes T f _ _)
    (selectLUV_codes (liarSentence_codes T f _ _) (constLUV_codes (by norm_num))
      (constLUV_codes (by norm_num))) (constLUV_codes (by norm_num))
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  reflected := fun n v hv xS xO hxS hxO => by
    have hS := witnessS_valuesAt T f n v hv
    have hK : v.ValuesAt ((witnessMenu T f).O 1 n) (((1 - 1 / 2) / 2 : ℚ) : ℝ) :=
      constLUV_valuesAt (probeConst_mem (by norm_num) (by norm_num)) v
    rw [hxS.eq hS, hxO.eq hK]
    have hin := selectLUV_valuesAt (liarSentence T f (1 / 2) (by norm_num))
      (fun _ => constLUV (7 / 8)) (fun _ => constLUV (3 / 8)) n v
      (constLUV_valuesAt (s := 7 / 8) (by norm_num) v) (constLUV_valuesAt (s := 3 / 8) (by norm_num) v)
    have hout := selectLUV_valuesAt (witnessσ T f) _ (fun _ => constLUV (1 / 2)) n v hin
      (constLUV_valuesAt (s := 1 / 2) (by norm_num) v)
    refine ⟨_, hout, ?_⟩
    unfold PCWorld.payout
    split_ifs <;> push_cast <;> norm_num

omit [Entailment.Consistent T] in
/-- `witnessD0` is the composite of the follower against option `0`.
Source: mandate target 8a
Kind: C
Fidelity: exact (slack `0`)
Hyps: (a) none -/
def probeComposite_zero : Composite (paperDP T) (witnessS T f) ((witnessMenu T f).O 0) where
  D := witnessD0 T f
  codes := selectLUV_codes (followSentence_codes T f _ _) (constLUV_codes (by norm_num))
    (selectLUV_codes (liarSentence_codes T f _ _) (constLUV_codes (by norm_num))
      (constLUV_codes (by norm_num)))
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  reflected := fun n v hv xS xO hxS hxO => by
    have hS := witnessS_valuesAt T f n v hv
    have hG : v.ValuesAt ((witnessMenu T f).O 0 n)
        (v.payout (liarSentence T f (1 / 2) (by norm_num) n)) :=
      literalIndicator_valuesAt _ (paperDP T) hv
    rw [hxS.eq hS, hxO.eq hG]
    have hin := selectLUV_valuesAt (liarSentence T f (1 / 2) (by norm_num))
      (fun _ => constLUV (1 / 8)) (fun _ => constLUV (5 / 8)) n v
      (constLUV_valuesAt (s := 1 / 8) (by norm_num) v) (constLUV_valuesAt (s := 5 / 8) (by norm_num) v)
    have hout := selectLUV_valuesAt (witnessσ T f) (fun _ => constLUV (1 / 2)) _ n v
      (constLUV_valuesAt (s := 1 / 2) (by norm_num) v) hin
    refine ⟨_, hout, ?_⟩
    unfold PCWorld.payout
    split_ifs <;> push_cast <;> norm_num

/-! ## The scoped theorem with every hypothesis discharged (target 8 N+) -/

/-- **The scoped theorem's full hypothesis package is jointly inhabited on FAF's construction**
(target 8's N+ for joint satisfiability): for the self-expert on the witness menu
`{1[θ_n], const ¼}` — `θ` the pinned undecided liar — with the self-expert's own package, fold,
follower and composites, and Total Trust from `selfTotalTrust`, `E^P_n(S_n) ≳ₙ E^P_n(O^i_n)` for
both `i`. Every hypothesis of `scoped_value` is a theorem here. **Register (audit r1, B1 /
fidelity item 2): this witness lives in the decisive stratum.** The self-expert's selection on
`witnessMenu` is eventually the constant `0` (`witness_argmax_eventually_zero`, `Decisive.lean`),
so H3 holds with equality for the trivial reason (`I^0 ≈ 1`, `I^1 ≈ 0`), concentration is
provind on an indicator valued `0`, and the conclusion follows from the two pins alone
(`witness_value_one_without_hypotheses`, `Decisive.lean`: no Total Trust, no fold, no H3). It is
**N+ for joint satisfiability** (a non-constant pinned-undecided top option, every hypothesis a
theorem on FAF's inductor) and **N− for the content of H3, concentration and Lemma 2**: no menu is
known on which `CondStableOn` holds while the self-expert's selection keeps moving (open problem 3;
after repair round 2 the question is `Open.lean`'s `truthPrice_frequently_interior`, the
world-only route being refuted in `WorldOnlyRefuted.lean`), and on the two forced-oscillation
menus of the package (the probe, the punishing menu) H3 fails; the second inhabitant, the
truth-teller (`TruthTeller.lean`), is the dominance stratum (audit r2 B1).
Source: mandate target 8 ("N+ menus on which H3 holds non-trivially" — met in the source's own
sense, lean-deference-2-025 (ii) / lean-deference-067, not in [[STANDARDS]] §3's content sense),
8c (the self-instance as a consistency check)
Kind: N+
Fidelity: exact
Hyps: (a) none; `hf` -/
theorem scoped_value_witness (hf : StrictlyIncreasingDeferral f) (i : Fin 2) :
    (fun n => (witnessS T f n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => ((witnessMenu T f).O i n).expect (liaHistory (paperDP T)) n) := by
  have hTT : TotalTrust (liaHistory (paperDP T)) (paperDP T) ((selfExpert T f).recast (paperDP T)) :=
    selfTotalTrust T f hf.injective
  fin_cases i
  · exact scoped_value (DPE := paperDP T) (DPH := paperDP T) (fun _ hv => hv) hf
      (witnessMenu_valued T f) (selectionPackage_self T f (witnessMenu T f))
      (concentrationFolds_self T f hf (witnessMenu T f) (selectionPackage_self T f (witnessMenu T f))) (condStableOn_probe_self T f hf) (witnessS_codes T f)
      (witnessS_follows T f) 0 (probeComposite_zero T f) hTT
      (paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
        (probeComposite_zero T f).codes ((probeComposite_zero T f).valued
          (follows_valued (witnessMenu_valued T f) (witnessS_follows T f))
          (witnessMenu_valued T f 0)))
      (paperDP_hworld T) (paperDP_hworld T)
  · exact scoped_value (DPE := paperDP T) (DPH := paperDP T) (fun _ hv => hv) hf
      (witnessMenu_valued T f) (selectionPackage_self T f (witnessMenu T f))
      (concentrationFolds_self T f hf (witnessMenu T f) (selectionPackage_self T f (witnessMenu T f))) (condStableOn_probe_self T f hf) (witnessS_codes T f)
      (witnessS_follows T f) 1 (probeComposite_one T f) hTT
      (paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
        (probeComposite_one T f).codes ((probeComposite_one T f).valued
          (follows_valued (witnessMenu_valued T f) (witnessS_follows T f))
          (witnessMenu_valued T f 1)))
      (paperDP_hworld T) (paperDP_hworld T)

example (i : Fin 2) :
    (fun n => (witnessS 𝗣𝗔 succDeferral n).expect (liaHistory (paperDP 𝗣𝗔)) n) ≳ₙ
      (fun n => ((witnessMenu 𝗣𝗔 succDeferral).O i n).expect (liaHistory (paperDP 𝗣𝗔)) n) :=
  scoped_value_witness 𝗣𝗔 succDeferral Cleanroom.Found.LiQuoteLane.succDeferral_strict i

/-! ## 8b for the self-expert: `ValueOnStable` with one hypothesis left -/

/-- **The self-expert has scoped Value, given composites** (target 8b, the self-instance; repair
round 1, audit r1 B2): `ValueOnStable P (paperDP T) (selfExpert T f)` follows from
`valueOnStable_of_totalTrust` with Total Trust (`selfTotalTrust`), the fold on every selection
package (`concentrationFolds_self`) and ramp quotes on every e.c. valued LUV
(`paperExpert_rampQuotesAvailable`) all discharged at grade (a); the one hypothesis left is
`CompositesAvailable (paperDP T)` — the rich ledger (F13), the general two-LUV mesh construction
not built here (handoff item 1).
Source: mandate target 8b; audit r1 B2
Kind: C
Fidelity: exact
Hyps: (a) `hTT`, `hfold`, `hramp`; `hf`; (c) `hcomp` (the rich ledger) -/
theorem valueOnStable_self (hf : StrictlyIncreasingDeferral f)
    (hcomp : CompositesAvailable (paperDP T)) :
    ValueOnStable (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) :=
  valueOnStable_of_totalTrust hf (selfTotalTrust T f hf.injective) hcomp
    (fun _ hD hDv => paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective hD hDv)
    (fun _ M _ _ pkg => concentrationFolds_self T f hf M pkg) (paperDP_hworld T)

end

end Cleanroom.Deference.DefArgmaxValue
