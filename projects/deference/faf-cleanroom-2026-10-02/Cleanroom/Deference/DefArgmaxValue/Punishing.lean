import Cleanroom.Deference.DefArgmaxValue.LiarProbe
import Cleanroom.Deference.DefSqueezeDiamond.Diamond
import Cleanroom.Deference.DefSelfTrust.GateCollapse

/-!
# `def-argmax-value` · Punishing: Abram's punishing menu, `k+1` options (target 3)

`O^j_n := 1 − 1[sel_n = j]` — every option worth `0` if chosen, `1` otherwise
([[total-trust-implies-value]] §Necessity, 2026-07-24). Over FAF: the Kleene selector of
`Selector.lean` with `quotes c n := [P_{f n}(b_{n,0}), …, P_{f n}(b_{n,k})]` and
`rel a j := (a ≠ j)`, so that the public atom `b_{n,j}` holds in every `paperDP T`-world iff
the self-expert's least-index argmax on the menu `O^j_n := literalIndicator b_{n,j}` is **not**
`j` (`punishAtom_holds_iff`, world fact (α)); hence `O^j_n` is valued `1 − 1[sel_n = j]`
(`punishingMenu_valuesAt`, world fact (β)). No negation enters the market call: the selector's
own decision is already the complement.

The refutations (3b): the follower `S_n := const 0` *follows* (the selected option is valued
`0` in every world, `constZero_follows`), `Σ_j E^P_n(O^j_n) ≈ₙ k` (coherence: the atoms are
exhaustive and exclusive, `punishing_sum_expect`), so **Value fails for every `k ≥ 1`**
(`punishing_value_refuted`); `M_n ≳ₙ k/(k+1)` from coherence alone (`punishing_maxQuote_ge` —
vq-wiki-015's flagged "bounded away from `0`", proved without exploitability), so
**`SelfEndorsesGE` fails** (`punishing_selfEndorsesGE_refuted`); and the H3 sum identity
`Σ_j E*(Q^j) − Σ_j E*(I^j)·m^j ≈ₙ −Σ_j p_j(1 − p_j)` with `p_j := P_{f n}(sel_n = j)`
(`punishing_h3_deficit`, 2-023(b)); that the masses stay interior — in fact `p_j → 1/(k+1)` — is
`PunishingTie.lean`'s `punishing_masses_interior` (proved in repair round 1).

Construction-facing; single market (self); `[𝗣𝗔⁻ ⪯ T]`-level.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- `≲ₙ` over a finite sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympLE_finsetSum {ι : Type*} (s : Finset ι) {a b : ι → ℕ → ℝ}
    (h : ∀ i ∈ s, a i ≲ₙ b i) :
    (fun n => ∑ i ∈ s, a i n) ≲ₙ (fun n => ∑ i ∈ s, b i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (AsympEq.refl (fun _ => (0 : ℝ))).asympLE
  | insert x s hx ih =>
    have h1 := h x (Finset.mem_insert_self x s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simpa [Finset.sum_insert hx] using this

/-- A pointwise lower bound is an asymptotic lower bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympGE_of_forall_le {a b : ℕ → ℝ} (h : ∀ n, b n ≤ a n) : a ≳ₙ b :=
  fun ε hε => Filter.Eventually.of_forall (fun n => by linarith [h n])

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (k : ℕ)

/-! ## The construction (3a) -/

/-- The selector's quotes: the market's day-`f n` prices of the `k+1` atoms of the candidate `c`.
Source: mandate target 3a
Kind: D
Fidelity: exact -/
def punishQuotes (c : Nat.Partrec.Code) (n : ℕ) : List ℚ :=
  List.ofFn (fun i : Fin (k + 1) => (paperMarketComputation T).quote (f.f n)
    (Encodable.encode (quoteAtom (Nat.pair (Encodable.encode c) (Nat.pair n i)))))

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The quotes are computable in `(c, n)` (`Computable.list_ofFn` over `quote_of_atom_computable`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem punishQuotes_computable : Computable₂ (punishQuotes T f k) :=
  Computable.list_ofFn (fun i => quote_of_atom_computable (paperMarketComputation T)
    (f.computable.comp Computable.snd) (atomPayload_primrec (i : ℕ)))

/-- The selection relation of the punishing menu: "the argmax is not `j`".
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def neRel : ℕ → ℕ → Bool := fun a j => decide (¬ a = j)

/-- `neRel` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem neRel_primrec : Primrec₂ neRel := Primrec.eq.not.decide

/-- **The punishing atom** `b_{n,j}`: holds iff the self-expert's argmax on the menu is not `j`.
Source: mandate target 3a ("public atoms `a_{n,j}`", here with the complementary decision)
Kind: D
Fidelity: exact -/
def punishAtom (n j : ℕ) : Sentence :=
  selectorAtom (punishQuotes T f k) neRel T (punishQuotes_computable T f k) neRel_primrec n j

omit [Entailment.Consistent T] in
/-- The atoms at a fixed option are e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem punishAtom_codes (j : ℕ) : MachineSentenceCodes (fun n => punishAtom T f k n j) :=
  selectorAtom_codes (punishQuotes T f k) neRel T (punishQuotes_computable T f k) neRel_primrec j

/-- **The punishing menu** `O^j_n := literalIndicator b_{n,j}`, valued `1 − 1[sel_n = j]`.
Source: [[total-trust-implies-value]] §Necessity ("`O^j_n := 1 − 1[sel_n = j]`"); the arc
l. 572; lean-deference-066; mandate target 3a
Kind: D
Fidelity: exact -/
def punishingMenu : Menu k where
  O := fun j n => literalIndicator (punishAtom T f k n j)
  codes := fun j => literalIndicator_machineThresholdCodeSeq (punishAtom_codes T f k j)

omit [Entailment.Consistent T] in
/-- The self-expert's rational quotes of the punishing options are the selector's quotes.
Source: none: infrastructure (FAF `quote_exact`, `literalIndicator_expect`)
Kind: L
Fidelity: n/a -/
theorem punishQuotes_cast (n : ℕ) (i : Fin (k + 1)) :
    (((paperMarketComputation T).quote (f.f n) (Encodable.encode (quoteAtom (Nat.pair
      (Encodable.encode (selectorCode (punishQuotes T f k) neRel (punishQuotes_computable T f k)
        neRel_primrec)) (Nat.pair n i)))) : ℚ) : ℝ) =
      (punishingMenu T f k).quote (selfExpert T f) i n := by
  simp only [Menu.quote, punishingMenu, Expert.self_estimate, literalIndicator_expect]
  exact ((paperMarketComputation T).quote_exact (f.f n) (punishAtom T f k n i)).symm

omit [Entailment.Consistent T] in
/-- **World fact (α)**: a `paperDP T`-world holds `b_{n,j}` iff the self-expert's least-index
argmax on the punishing menu is not `j` — the fixed-point equation read through
`argmax_eq_argmaxList`.
Source: mandate target 3a (α)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem punishAtom_holds_iff (n : ℕ) (j : Fin (k + 1)) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (punishAtom T f k n j) ↔ (punishingMenu T f k).argmax (selfExpert T f) n ≠ j := by
  rw [punishAtom, selectorAtom_holds_iff (hv := hv)]
  simp only [neRel, decide_eq_true_eq]
  rw [punishQuotes, ← argmax_eq_argmaxList (selfExpert T f) (punishingMenu T f k) n _
    (punishQuotes_cast T f k n)]
  exact ⟨fun h hj => h (by rw [hj]), fun h hj => h (Fin.ext hj)⟩

omit [Entailment.Consistent T] in
/-- **World fact (β)**: `O^j_n` is valued `1 − 1[sel_n = j]`.
Source: mandate target 3a (β)
Kind: L
Fidelity: exact -/
theorem punishingMenu_valuesAt (n : ℕ) (j : Fin (k + 1)) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((punishingMenu T f k).O j n)
      (1 - (if (punishingMenu T f k).argmax (selfExpert T f) n = j then 1 else 0)) := by
  have h := literalIndicator_valuesAt (punishAtom T f k n j) (paperDP T) hv
  have e : v.payout (punishAtom T f k n j) =
      1 - (if (punishingMenu T f k).argmax (selfExpert T f) n = j then 1 else 0) := by
    unfold PCWorld.payout
    rw [punishAtom_holds_iff T f k n j v hv]
    by_cases hc : (punishingMenu T f k).argmax (selfExpert T f) n = j <;> simp [hc]
  rw [e] at h
  exact h

omit [Entailment.Consistent T] in
/-- The punishing menu is world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem punishingMenu_valued : (punishingMenu T f k).Valued (paperDP T) :=
  fun j n v hv => ⟨_, punishingMenu_valuesAt T f k n j v hv⟩

/-! ## The follower and the sums (3b) -/

omit [Entailment.Consistent T] in
/-- **The constant `0` follows the argmax on the punishing menu**: the selected option is valued
`0` in every world by (α)+(β).
Source: the arc l. 572 ("`Γ ⊢ Ŝ_n = Σ_j 1[sel=j](1 − 1[sel=j]) = 0`" — a world-value identity
here, there is no syntactic `Ŝ`; `Follows` is a value clause); mandate target 3b
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem constZero_follows :
    Follows (paperDP T) (selfExpert T f) (punishingMenu T f k) (fun _ => constLUV 0) := by
  intro n v hv x hx
  have h := punishingMenu_valuesAt T f k n ((punishingMenu T f k).argmax (selfExpert T f) n) v hv
  simp only [if_true, _root_.sub_self] at h
  rw [hx.eq h]
  simpa using constLUV_valuesAt (s := 0) ⟨le_rfl, zero_le_one⟩ v

omit [Entailment.Consistent T] in
/-- The world values of the options sum to `k` (exactly one atom fails).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem punishing_sum_values (n : ℕ) :
    (∑ j : Fin (k + 1), (1 - (if (punishingMenu T f k).argmax (selfExpert T f) n = j
      then (1 : ℝ) else 0))) = k := by
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq]

/-- **The option expectations sum to `k`, at the deferred day**: `Σ_j E*(O^j_n) ≈ₙ k` (deferred
provind on `Σ_j O^j − k`, valued `0` in every world).
Source: mandate target 3b(ii)–(iii)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem punishing_sum_estimate (hf : StrictlyIncreasingDeferral f) :
    (fun n => ∑ j, (selfExpert T f).estimate ((punishingMenu T f k).O j) n) ≈ₙ
      (fun _ => (k : ℝ)) := by
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    List.ofFn (fun j : Fin (k + 1) => ((fun _ => EF.const 1), (punishingMenu T f k).O j))
    with hterms
  have hmem : ∀ p ∈ terms, ∃ j, p = ((fun _ => EF.const 1), (punishingMenu T f k).O j) :=
    fun p hp => by
      obtain ⟨j, hj⟩ := List.mem_ofFn.1 hp
      exact ⟨j, hj.symm⟩
  have h := expect_deferred_asympEq_zero_of_slack (P := liaHistory (paperDP T)) (DP := paperDP T)
    f hf (c₀ := fun _ => EF.const (-(k : ℚ))) (constWeighting _) (terms := terms)
    (fun p hp => by obtain ⟨j, rfl⟩ := hmem p hp; exact constWeighting 1)
    (fun p hp => by obtain ⟨j, rfl⟩ := hmem p hp; exact (punishingMenu T f k).codes j)
    (fun p hp => by obtain ⟨j, rfl⟩ := hmem p hp; exact punishingMenu_valued T f k j)
    (B := (k : ℝ) + (k + 1)) (by positivity)
    (fun m => by
      simp only [hterms, List.map_ofFn, Function.comp_def, EF.denote_const, List.sum_ofFn,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      push_cast
      simp [abs_of_nonneg])
    (fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have hval : ∀ j : Fin (k + 1), ν ((punishingMenu T f k).O j n) =
          1 - (if (punishingMenu T f k).argmax (selfExpert T f) n = j then 1 else 0) :=
        fun j => (hν _ (List.mem_ofFn.2 ⟨j, rfl⟩)).eq (punishingMenu_valuesAt T f k n j v hv)
      simp only [hterms, List.map_ofFn, Function.comp_def, EF.denote_const, List.sum_ofFn,
        hval]
      push_cast
      simp only [one_mul]
      rw [punishing_sum_values]
      simp) (paperDP_hworld T)
  have hE : deferredExpect (liaHistory (paperDP T)) f (fun _ => EF.const (-(k : ℚ))) terms =
      fun n => (∑ j, (selfExpert T f).estimate ((punishingMenu T f k).O j) n) - k := by
    funext n
    simp only [deferredExpect, hterms, List.map_ofFn, Function.comp_def, EF.denote_const,
      List.sum_ofFn, Expert.self_estimate, one_mul]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **The option expectations sum to `k`, at the present day**: `Σ_j E^P_n(O^j_n) ≈ₙ k`
(`thm:expprovind` on `Σ_j O^j − k`; the atoms are exhaustive and exclusive in every world by (α)).
Source: mandate target 3b(ii)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem punishing_sum_expect :
    (fun n => ∑ j, ((punishingMenu T f k).O j n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun _ => (k : ℝ)) := by
  set ts : List (ℚ × (ℕ → LUV)) :=
    List.ofFn (fun j : Fin (k + 1) => ((1 : ℚ), (punishingMenu T f k).O j)) with hts
  have hmem : ∀ p ∈ ts, ∃ j, p = ((1 : ℚ), (punishingMenu T f k).O j) :=
    fun p hp => by
      obtain ⟨j, hj⟩ := List.mem_ofFn.1 hp
      exact ⟨j, hj.symm⟩
  have h := expect_listComb_eq_of_slack (P := liaHistory (paperDP T)) (DP := paperDP T)
    (constStream_splice (-(k : ℚ))) (B := k) (fun _ => by simp)
    (ts := ts) (fun p hp => by obtain ⟨j, rfl⟩ := hmem p hp; exact (punishingMenu T f k).codes j)
    (listComb_worldValued _ (fun p hp => by
      obtain ⟨j, rfl⟩ := hmem p hp; exact punishingMenu_valued T f k j))
    0 (slack := fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have hval : ∀ j : Fin (k + 1), ν ((punishingMenu T f k).O j n) =
          1 - (if (punishingMenu T f k).argmax (selfExpert T f) n = j then 1 else 0) :=
        fun j => (listComb_valuesAt_mem hν (p := ((1 : ℚ), (punishingMenu T f k).O j))
          (List.mem_ofFn.2 ⟨j, rfl⟩)).eq (punishingMenu_valuesAt T f k n j v hv)
      rw [listComb_value]
      simp only [hts, List.map_ofFn, Function.comp_def, List.sum_ofFn, hval]
      push_cast
      simp only [one_mul]
      rw [punishing_sum_values]
      simp) (paperDP_hworld T)
  have hE : (fun n => (listComb (fun _ => -(k : ℚ)) ts n).expect (liaHistory (paperDP T)) n) =
      fun n => (∑ j, ((punishingMenu T f k).O j n).expect (liaHistory (paperDP T)) n) - k := by
    funext n
    rw [listComb_expect]
    simp only [hts, List.map_ofFn, Function.comp_def, List.sum_ofFn]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **Unconditional argmax Value is refuted by the punishing menu, for every `k ≥ 1`**
(target 3b, load-bearing 1's `k+1`-fold form): if `E^P_n(S_n) ≳ₙ E^P_n(O^j_n)` for all `j` with
`S ≡ const 0`, then `0 ≈ (k+1)·E^P_n(S_n) ≳ₙ Σ_j E^P_n(O^j_n) ≈ₙ k ≥ 1`.
Source: [[total-trust-implies-value]] §Necessity ("argmax Value itself fails"); lean-deference-066
Kind: refuted
Fidelity: exact (`def-lattice`'s `Value`, instantiated at `punishingMenu` with `const 0`)
Hyps: (a); `hk : 1 ≤ k` -/
theorem punishing_value_refuted (hk : 1 ≤ k) :
    ¬ Value (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) := by
  intro hV
  have h := hV k (punishingMenu T f k) (punishingMenu_valued T f k) (fun _ => constLUV 0)
    (constLUV_codes le_rfl) (constZero_follows T f k)
  have hsum : (fun n => ∑ j : Fin (k + 1), ((punishingMenu T f k).O j n).expect
      (liaHistory (paperDP T)) n) ≲ₙ
      (fun n => ∑ _j : Fin (k + 1), (constLUV 0).expect (liaHistory (paperDP T)) n) :=
    asympLE_finsetSum Finset.univ (fun j _ => h j)
  refine not_asympGE_of_tendsto_neg (c := -(k : ℝ)) (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith) ?_ hsum
  have h0 := tendsto_of_asympEq_const (expect_constLUV_asympEq (P := liaHistory (paperDP T))
    (DP := paperDP T) (s := 0) ⟨le_rfl, zero_le_one⟩ (paperDP_hworld T))
  have hk' := tendsto_of_asympEq_const (punishing_sum_expect T f k)
  have := (h0.const_mul ((k : ℝ) + 1)).sub hk'
  refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  try ring

/-- **`M_n ≳ₙ k/(k+1)` from coherence alone** (target 3b(iii)): the maximum of `k+1` quotes
summing to `≈ₙ k` — vq-wiki-015's "`M_n` stays bounded away from `0`" is a theorem of coherence,
not of exploitability (findings F1).
Source: vq-wiki-015 (the flag); lean-deference-066 ("free money"); mandate target 3b(iii)
Kind: C
Fidelity: stronger: the explicit bound `k/(k+1)`
Hyps: (a); `hf` -/
theorem punishing_maxQuote_ge (hf : StrictlyIncreasingDeferral f) :
    (fun n => (punishingMenu T f k).maxQuote (selfExpert T f) n) ≳ₙ
      (fun _ => (k : ℝ) / (k + 1)) := by
  have hsum := punishing_sum_estimate T f k hf
  have havg : (fun n => (∑ j, (selfExpert T f).estimate ((punishingMenu T f k).O j) n) /
      ((k : ℝ) + 1)) ≈ₙ (fun _ => (k : ℝ) / (k + 1)) := by
    have := hsum.const_mul (1 / ((k : ℝ) + 1))
    refine (tendsto_congr (fun n => ?_)).mp this
    simp only
    ring
  refine asympGE_iff.2 (havg.symm.trans_asympLE ?_)
  refine asympGE_iff.1 (asympGE_of_forall_le (fun n => ?_))
  rw [div_le_iff₀ (by positivity)]
  have : ∑ j, (selfExpert T f).estimate ((punishingMenu T f k).O j) n ≤
      ∑ _j : Fin (k + 1), (punishingMenu T f k).maxQuote (selfExpert T f) n :=
    Finset.sum_le_sum (fun j _ => Menu.quote_le_maxQuote _ _ j n)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  linarith

/-- **`SelfEndorsesGE` is refuted by the punishing menu** for every `k ≥ 1`: the follower
`const 0` has `E*(S_n) → 0` while `M_n ≳ₙ k/(k+1) > 0`.
Source: mandate target 3b(iii) ("hence `¬ SelfEndorsesGE`")
Kind: refuted
Fidelity: exact
Hyps: (a); `hf`; `hk` -/
theorem punishing_selfEndorsesGE_refuted (hf : StrictlyIncreasingDeferral f) (hk : 1 ≤ k) :
    ¬ SelfEndorsesGE (paperDP T) (selfExpert T f) := by
  intro hSE
  have h := hSE k (punishingMenu T f k) (punishingMenu_valued T f k) (fun _ => constLUV 0)
    (constLUV_codes le_rfl) (constZero_follows T f k)
  have h' : (fun n => (selfExpert T f).estimate (fun _ => constLUV 0) n) ≳ₙ
      (fun _ => (k : ℝ) / (k + 1)) :=
    asympGE_iff.2 ((asympGE_iff.1 (punishing_maxQuote_ge T f k hf)).trans (asympGE_iff.1 h))
  refine not_asympGE_of_tendsto_neg (c := -((k : ℝ) / (k + 1))) (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) < (k : ℝ) / (k + 1) := by positivity
    linarith) ?_ h'
  have h0 := constZero_estimate_tendsto T f hf
  have := h0.sub (tendsto_const_nhds (x := (k : ℝ) / (k + 1)))
  simpa [Expert.self_estimate] using this

/-- Two-sided `SelfEndorses` is refuted by the punishing menu (a fortiori).
Source: mandate target 3b(iii)
Kind: refuted
Fidelity: exact
Hyps: (a); `hf`; `hk` -/
theorem punishing_selfEndorses_refuted (hf : StrictlyIncreasingDeferral f) (hk : 1 ≤ k) :
    ¬ SelfEndorses (paperDP T) (selfExpert T f) :=
  fun h => punishing_selfEndorsesGE_refuted T f k hf hk (SelfEndorsesGE.of_selfEndorses h)

/-! ## The H3 sum identity (3b(iv)) -/

/-- The selection indicators of the punishing menu: `I j n := 1[∼b_{n,j}] = 1[sel_n = j]`.
Source: mandate target 3b(iv)
Kind: D
Fidelity: exact -/
def punishI (j : Fin (k + 1)) (n : ℕ) : LUV := literalIndicator (∼ punishAtom T f k n j)

omit [Entailment.Consistent T] in
/-- **The punishing menu's selection package** (exact, slack `0`): indicators `1[∼b_{n,j}]`,
products `const 0` (`(1 − 1[sel=j])·1[sel=j] = 0`).
Source: mandate target 3b(iv); [[total-trust-implies-value]] §Necessity ("`1[sel_n=j]·O^j_n …
is provably `0`")
Kind: D
Fidelity: exact -/
def punishPackage :
    SelectionPackage (paperDP T) (selfExpert T f) (punishingMenu T f k) (punishI T f k)
      (fun _ _ => constLUV 0) where
  codes_I := fun j => literalIndicator_machineThresholdCodeSeq (punishAtom_codes T f k j).neg
  codes_Q := fun _ => constLUV_codes le_rfl
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  reflected_I := fun j n v hv => by
    have h := literalIndicator_valuesAt (∼ punishAtom T f k n j) (paperDP T) hv
    have e : v.payout (∼ punishAtom T f k n j) =
        (if (punishingMenu T f k).argmax (selfExpert T f) n = j then 1 else 0) := by
      unfold PCWorld.payout
      rw [PCWorld.holds_neg, punishAtom_holds_iff T f k n j v hv]
      by_cases hc : (punishingMenu T f k).argmax (selfExpert T f) n = j <;> simp [hc]
    rw [e] at h
    exact h
  reflected_Q := fun j n v hv x hx => by
    refine ⟨0, by simpa using constLUV_valuesAt (s := 0) ⟨le_rfl, zero_le_one⟩ v, ?_⟩
    rw [hx.eq (punishingMenu_valuesAt T f k n j v hv)]
    by_cases hc : (punishingMenu T f k).argmax (selfExpert T f) n = j <;> simp [hc]

/-- **The H3 sum identity on the punishing menu** (2-023(b), as an exact asymptotic identity):
`Σ_j E*(Q^j_n) − Σ_j E*(I^j_n)·m^j_n ≈ₙ −Σ_j p_j(n)(1 − p_j(n))` with
`p_j(n) := P_{f n}(∼b_{n,j}) = P_{f n}(sel_n = j)`: the left side is `≈ₙ 0`, each `m^j_n =
P_{f n}(b_{n,j}) ≈ₙ 1 − p_j(n)` by deferred coherence. Whether the right side is bounded away
from `0` — whether the self-prediction stays interior — is the liar dynamics, proved in
`PunishingTie.lean` (`punishing_masses_interior`, `p_j → 1/(k+1)`); the Value and self-endorsement
refutations above need none of it.
Source: 2-023(b); [[total-trust-implies-value]] §Necessity (the display
`−(1 − Σ_j P^A_n(sel=j)²)`); mandate target 3b(iv)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem punishing_h3_deficit (hf : StrictlyIncreasingDeferral f) :
    (fun n => (∑ _j : Fin (k + 1), (selfExpert T f).estimate (fun _ => constLUV 0) n) -
        ∑ j, (selfExpert T f).estimate (punishI T f k j) n *
          (punishingMenu T f k).quote (selfExpert T f) j n) ≈ₙ
      (fun n => -∑ j : Fin (k + 1), (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j) *
        (1 - (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j))) := by
  have h0 := constZero_estimate_tendsto T f hf
  have hsum0 : Tendsto (fun n => ∑ _j : Fin (k + 1), (selfExpert T f).estimate
      (fun _ => constLUV 0) n) atTop (𝓝 0) := by
    have := h0.const_mul ((k : ℝ) + 1)
    simp only [mul_zero] at this
    refine (tendsto_congr (fun n => ?_)).mp this
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Expert.self_estimate]
    try ring
  have hcoh : ∀ j : Fin (k + 1), (fun n => (liaHistory (paperDP T)) (f n) (punishAtom T f k n j)) ≈ₙ
      (fun n => 1 - (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j)) := by
    intro j
    have := deferred_neg_coherence (P := liaHistory (paperDP T)) (DP := paperDP T) f hf
      (punishAtom_codes T f k j) (paperDP_hworld T)
    unfold AsympEq at this ⊢
    refine (tendsto_congr (fun n => ?_)).mp this
    ring
  have hterm : ∀ j : Fin (k + 1), (fun n => (selfExpert T f).estimate (punishI T f k j) n *
      (punishingMenu T f k).quote (selfExpert T f) j n) ≈ₙ
      (fun n => (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j) *
        (1 - (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j))) := by
    intro j
    have hp : ∀ n, |(liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j)| ≤ 1 := fun n => by
      rw [abs_le]
      have := IsLogicalInductor.price_mem_Icc (P := liaHistory (paperDP T)) (DP := paperDP T)
        (f n) (∼ punishAtom T f k n j)
      constructor <;> linarith [this.1, this.2]
    have := asympEq_mul_left_of_bounded hp (hcoh j)
    refine (tendsto_congr (fun n => ?_)).mp this
    simp [punishI, Menu.quote, punishingMenu, Expert.self_estimate, literalIndicator_expect]
  have hsum := AsympEq.finsetSum (fun j => hterm j)
  unfold AsympEq at hsum0 hsum ⊢
  have := (hsum0.sub hsum)
  refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Expert.self_estimate]
  push_cast
  ring

/-! ## Instance lines -/

example : ¬ Value (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) (selfExpert 𝗣𝗔 succDeferral) :=
  punishing_value_refuted 𝗣𝗔 succDeferral 2 (by norm_num)

example : ¬ SelfEndorsesGE (paperDP 𝗣𝗔) (selfExpert 𝗣𝗔 succDeferral) :=
  punishing_selfEndorsesGE_refuted 𝗣𝗔 succDeferral 2
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num)

end

end Cleanroom.Deference.DefArgmaxValue
