import Cleanroom.Decision.DpFaithfulUdt.BestReply
import Cleanroom.Decision.DpLocalOpt.TwoPointWitness
import Cleanroom.Decision.DpEdtUdtFair.FairWitnesses

/-!
# Self-confirmation at the advocacy grade (T4), and the Stag Hunt rows (T2 witness, T4(c)–(e))

T4 of [[dp-faithful-udt-mandate]]. A pair `(s°, pol)` is *self-confirming* for the self-model
`C'` when `s°` is masked-prior-calibrated under `lift U C'` and Definition 18's `T_UDT` with that
prior approves `C'` itself (`SelfConfirming`). On almost-fair trees:

* `selfConfirming_iff_nash`: self-confirmation ⟺ (calibration ∧) `C'` is a mixed Nash
  equilibrium of the point game (`Nash`);
* `nash_iff_coherent`: Nash ⟺ mixed Definition-22 coherence (`dp-local-opt`'s `Coherent`, A30);

both **at the advocacy grade** (`TUdt`, Definition 18). The procedure-level version — "the
uniform-tie `UDT_{s°,pol}` reproduces `C'`" — is **refuted** on the Stag Hunt by the `(⅓, ⅓)`
self-model (`third_nash_coherent_not_udtProc`): Nash and coherent, yet Definition 17's uniform
tie-break outputs `(½, ½)`. Trembled `(H, H)` self-models output `(H, H)` — self-confirming in the
limit and not optimal (`twoStag_tremble_HH`): self-confirmation buys coherence, not optimality.
FA-16's tie damage: `T_UDT` approves the miscoordinating `(S, H)` of value `0` under the tying
self-model (`third_tUdt_miscoordinates`). T2's witness: the product self-model `β` on the Stag
Hunt gives `V_{s°}(pol_1 = S) = 2β`, `V_{s°}(pol_1 = H) = 1 − β`, and `UDT` plays `S` iff `β > ⅓`
(`twoStag_udtProc_product`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### Self-confirmation ⟺ Nash ⟺ coherence -/

section general

variable (U : Finset ι) (B : Tree Ω ι acts K) (C' : Proc ι acts K) (s₀ : State (RW Ω acts U) K)

/-- **Self-confirmation of `(s°, pol)` for the self-model `C'`**: the prior is masked-calibrated to
`C'` and `T_{UDT_{s°,pol}}` approves `C'` (Definition 18's advocacy grade: `supp C'(d) ⊆` the
argmax at every queried point). Stated with `TUdt`, never with `udtProc = C'` (the latter is
refuted below).
Source: `faithful.md` FA-12′ ("`(s°,ρ)` self-confirming … holds at the *advocacy* grade —
`T_{UDT_{s°,ρ}}(C', B)`"); Dead 13; mandate T4
Kind: D
Fidelity: exact (advocacy grade) -/
def SelfConfirming : Prop :=
  MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀ ∧ TUdt s₀ (polEv U) C' B

/-- Under masked prior calibration the `UDT` domain at a relocated point is all of `A_d`.
Source: `faithful.md` FA-5 ("the Definition 17 domain is all of `A_d`")
Kind: L -/
theorem udtDomain_polEv_eq_univ (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀)
    {d : ι} (h : d ∈ U) : udtDomain s₀ (polEv U) d = Finset.univ := by
  ext a
  simp only [mem_udtDomain, Finset.mem_univ, iff_true]
  rw [polEv_pr U B C' s₀ hcal.2 h]
  exact hcal.1 (.inl d) a

/-- Under the hypotheses of T2 the `UDT` argmax at `d ∈ U` is `BR_d(C')`.
Source: `faithful.md` FA-9
Kind: L -/
theorem udtArgmax_polEv_eq_BR (hB : AlmostFair B)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) :
    udtArgmax s₀ (polEv U) d = BR C' B d := by
  rw [udtArgmax_eq_argmaxFull s₀ (polEv U) d fun a => by
    rw [polEv_pr U B C' s₀ hcal.2 h]; exact hcal.1 (.inl d) a]
  unfold BR
  congr 1
  funext a
  exact polEv_V_eq_value U B C' s₀ hB hcal.2 h a (hcal.1 (.inl d) a)

/-- **`T_UDT` with the prior calibrated to `C'` approves `C` iff `supp C(d) ⊆ BR_d(C')` at every
queried point**, on almost-fair `B` with `U ⊇ queried B`: Definition 18's clause at `d` once the
domain is all of `A_d` and the argmax is `BR_d(C')`.
Source: `faithful.md` FA-12′, FA-16
Kind: C -/
theorem tUdt_polEv_iff (hB : AlmostFair B) (hU : queried B ⊆ U)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) (C : Proc ι acts K) :
    TUdt s₀ (polEv U) C B ↔ ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → a ∈ BR C' B d := by
  rw [tUdt_iff]
  refine forall₂_congr fun d hd => ?_
  rw [udtDomain_polEv_eq_univ U B C' s₀ hcal (hU hd), udtArgmax_polEv_eq_BR U B C' s₀ hB hcal (hU hd)]
  exact ⟨fun h => h Finset.univ_nonempty, fun h _ => h⟩

/-- **`T_UDT` with the calibrated prior approves `C'` iff `C'` is Nash**: the self-model is
approved iff it is a fixed point of componentwise best reply.
Source: `faithful.md` FA-12′
Kind: C -/
theorem tUdt_polEv_iff_nash (hB : AlmostFair B) (hU : queried B ⊆ U)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) :
    TUdt s₀ (polEv U) C' B ↔ Nash C' B :=
  tUdt_polEv_iff U B C' s₀ hB hU hcal C'

/-- **T4(a) — self-confirmation ⟺ Nash of the point game** (at the advocacy grade), on almost-fair
`B` with `U ⊇ queried B`: `(s°, pol)` is self-confirming for `C'` iff `s°` is masked-calibrated
to `C'` and `C'` is a mixed Nash equilibrium of the point game `d ↦ V_B(C'[d ↦ ·])`.
Scope: almost-fair trees, Definition 6, Definition 11 masked, Definition 18 (advocacy) — not
Definition 17's uniform-tie procedure (`third_nash_coherent_not_udtProc`).
Source: `faithful.md` FA-12′ ("`(s°,ρ)` self-confirming ⟺ `C'` is a mixed Nash equilibrium of the
point game … holds at the *advocacy* grade"); dp-cf-2-008, dp-cf-108
Kind: C
Fidelity: exact (advocacy grade)
Hyps: (a) `AlmostFair B`; (a) `queried B ⊆ U` -/
theorem selfConfirming_iff_nash (hB : AlmostFair B) (hU : queried B ⊆ U) :
    SelfConfirming U B C' s₀ ↔
      MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀ ∧ Nash C' B := by
  unfold SelfConfirming
  constructor
  · rintro ⟨hcal, hT⟩
    exact ⟨hcal, (tUdt_polEv_iff_nash U B C' s₀ hB hU hcal).mp hT⟩
  · rintro ⟨hcal, hN⟩
    exact ⟨hcal, (tUdt_polEv_iff_nash U B C' s₀ hB hU hcal).mpr hN⟩

/-- **Nash at `d` ⟺ pure Definition-22 coherence at `d`, on almost-fair trees**: with
`V_B(C') = ∑_a C'(d)(a) V_B(C'[d↦a])`, every supported action is a best reply iff no pure
deviation beats `C'`.
Source: `faithful.md` FA-12′ ("⟺ mixed-Definition-22 coherent"); [[decision-problems-v2]] §8
comment (ii)
Kind: P -/
theorem nashAt_iff_coherentPureAt (hB : AlmostFair B) (d : ι) :
    (∀ a, 0 < (C' d).w a → a ∈ BR C' B d) ↔ CoherentPureAt C' B d := by
  have hexp := value_eq_sum_deviatePure_of_almostFair C' d hB
  constructor
  · intro hN b
    obtain ⟨a₀, ha₀⟩ := FinDistr.exists_pos (C' d)
    have hmax := (mem_BR C' B d a₀).mp (hN a₀ ha₀)
    have hsum : value C' B = value (C'.deviatePure d a₀) B := by
      rw [hexp]
      apply sum_eq_of_support
      intro a ha
      exact le_antisymm (hmax a) ((mem_BR C' B d a).mp (hN a ha) a₀)
    rw [hsum]
    exact hmax b
  · intro hc a ha
    rw [mem_BR]
    have heq := eq_of_sum_eq_of_le (C' d) (fun b => value (C'.deviatePure d b) B) (value C' B)
      hc hexp.symm a ha
    intro b
    rw [heq]
    exact hc b

/-- **T4(b) — Nash ⟺ mixed Definition-22 coherence on almost-fair trees**: `C'` is a mixed Nash
equilibrium of the point game iff `C'` is `B`-coherent in the mixed sense of record (A30) —
which on almost-fair trees agrees with v2's pure Definition 22
(`coherentAt_iff_coherentPureAt_of_almostFair`; the two differ under self-succession,
`dp-local-opt`).
Scope: almost-fair trees, Definition 6.
Source: `faithful.md` FA-12′ ("⟺ mixed-Definition-22 coherent"); dp-cf-2-008
Kind: C
Fidelity: exact (mixed Definition 22 of record; agrees with the pure one on this scope)
Hyps: (a) `AlmostFair B` -/
theorem nash_iff_coherent (hB : AlmostFair B) : Nash C' B ↔ Coherent C' B := by
  unfold Nash Coherent
  refine forall₂_congr fun d _ => ?_
  rw [nashAt_iff_coherentPureAt B C' hB d, coherentAt_iff_coherentPureAt_of_almostFair C' d hB]

/-- **Self-confirmation ⟺ mixed Definition-22 coherence** (T4(a) + T4(b)): on almost-fair `B`
with `U ⊇ queried B`, `(s°, pol)` is self-confirming for `C'` iff `s°` is calibrated to `C'` and
`C'` is `B`-coherent. Self-confirmation buys coherence, not optimality
(`IsOptimal.coherent` is the converse; `twoStag_tremble_HH` is a coherent non-optimum).
Source: `faithful.md` FA-12′, answer to open problem 6 ("Self-confirmation of `(s°,ρ)`
characterizes mixed Definition-22 coherence — Nash of the point game — at the advocacy grade,
not optimality")
Kind: C
Fidelity: exact (advocacy grade; mixed Definition 22)
Hyps: (a) `AlmostFair B`; (a) `queried B ⊆ U` -/
theorem selfConfirming_iff_coherent (hB : AlmostFair B) (hU : queried B ⊆ U) :
    SelfConfirming U B C' s₀ ↔
      MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀ ∧ Coherent C' B := by
  rw [selfConfirming_iff_nash U B C' s₀ hB hU, nash_iff_coherent B C' hB]

end general

/-! ### Two-action argmax sets -/

section act2

/-- The argmax of a two-action function with a strict winner `a`. Source: none: infrastructure.
Kind: L -/
theorem argmaxFull_act2_eq_a (f : Act2 → ℚ) (h : f .b < f .a) : argmaxFull f = {Act2.a} := by
  ext x
  rw [mem_argmaxFull, Finset.mem_singleton]
  cases x
  · refine ⟨fun _ => rfl, fun _ b => ?_⟩
    cases b
    · exact le_rfl
    · exact h.le
  · constructor
    · intro hall; have := hall .a; linarith
    · intro hx; cases hx

/-- The argmax of a two-action function with a strict winner `b`. Source: none: infrastructure.
Kind: L -/
theorem argmaxFull_act2_eq_b (f : Act2 → ℚ) (h : f .a < f .b) : argmaxFull f = {Act2.b} := by
  ext x
  rw [mem_argmaxFull, Finset.mem_singleton]
  cases x
  · constructor
    · intro hall; have := hall .b; linarith
    · intro hx; cases hx
  · refine ⟨fun _ => rfl, fun _ b => ?_⟩
    cases b
    · exact h.le
    · exact le_rfl

/-- The argmax of a two-action function at a tie is everything. Source: none: infrastructure.
Kind: L -/
theorem argmaxFull_act2_eq_univ (f : Act2 → ℚ) (h : f .a = f .b) : argmaxFull f = Finset.univ := by
  ext x
  simp only [mem_argmaxFull, Finset.mem_univ, iff_true]
  intro b
  cases x <;> cases b <;> simp [h]

end act2

/-! ### The Stag Hunt rows -/

section stag

open Cleanroom.Found.DpCoreTree.Catalogue

variable (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- `(proc2 p q)[p1 ↦ S] = proc2 1 q`. Source: none: infrastructure. Kind: L -/
theorem proc2_deviatePure_p1_a :
    (proc2 p q hp0 hp1 hq0 hq1).deviatePure .p1 .a = proc2 1 q zero_le_one le_rfl hq0 hq1 := by
  show (proc2 p q hp0 hp1 hq0 hq1).deviate .p1 (FinDistr.pure .a) = _
  rw [pure_a_eq_act2, proc2_deviate_p1]

/-- `(proc2 p q)[p1 ↦ H] = proc2 0 q`. Source: none: infrastructure. Kind: L -/
theorem proc2_deviatePure_p1_b :
    (proc2 p q hp0 hp1 hq0 hq1).deviatePure .p1 .b = proc2 0 q le_rfl zero_le_one hq0 hq1 := by
  show (proc2 p q hp0 hp1 hq0 hq1).deviate .p1 (FinDistr.pure .b) = _
  rw [pure_b_eq_act2, proc2_deviate_p1]

/-- `(proc2 p q)[p2 ↦ S] = proc2 p 1`. Source: none: infrastructure. Kind: L -/
theorem proc2_deviatePure_p2_a :
    (proc2 p q hp0 hp1 hq0 hq1).deviatePure .p2 .a = proc2 p 1 hp0 hp1 zero_le_one le_rfl := by
  show (proc2 p q hp0 hp1 hq0 hq1).deviate .p2 (FinDistr.pure .a) = _
  rw [pure_a_eq_act2, proc2_deviate_p2]

/-- `(proc2 p q)[p2 ↦ H] = proc2 p 0`. Source: none: infrastructure. Kind: L -/
theorem proc2_deviatePure_p2_b :
    (proc2 p q hp0 hp1 hq0 hq1).deviatePure .p2 .b = proc2 p 0 hp0 hp1 le_rfl zero_le_one := by
  show (proc2 p q hp0 hp1 hq0 hq1).deviate .p2 (FinDistr.pure .b) = _
  rw [pure_b_eq_act2, proc2_deviate_p2]

/-- **The point game of the Stag Hunt** under the self-model `proc2 p q`: `V(C'[p1↦S]) = 2q`,
`V(C'[p1↦H]) = 1 − q`, `V(C'[p2↦S]) = 2p`, `V(C'[p2↦H]) = 1 − p`.
Source: `faithful.md` FA-12′ ("Product self-model `P(S) = β`: `2β` vs `1−β`")
Kind: P -/
theorem twoStag_pointGame :
    value ((proc2 p q hp0 hp1 hq0 hq1).deviatePure .p1 .a) twoStag = 2 * q ∧
    value ((proc2 p q hp0 hp1 hq0 hq1).deviatePure .p1 .b) twoStag = 1 - q ∧
    value ((proc2 p q hp0 hp1 hq0 hq1).deviatePure .p2 .a) twoStag = 2 * p ∧
    value ((proc2 p q hp0 hp1 hq0 hq1).deviatePure .p2 .b) twoStag = 1 - p := by
  rw [proc2_deviatePure_p1_a, proc2_deviatePure_p1_b, proc2_deviatePure_p2_a,
    proc2_deviatePure_p2_b, twoStag_value, twoStag_value, twoStag_value, twoStag_value]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- `BR` on the Stag Hunt under `proc2 p q`, as a function of the point. Source: none:
infrastructure. Kind: L -/
theorem twoStag_BR_p1 :
    BR (proc2 p q hp0 hp1 hq0 hq1) twoStag .p1 =
      argmaxFull fun a : Act2 => if a = .a then 2 * q else 1 - q := by
  unfold BR
  congr 1
  funext a
  obtain ⟨h1, h2, -, -⟩ := twoStag_pointGame p q hp0 hp1 hq0 hq1
  cases a
  · rw [h1]; rfl
  · rw [h2]; rfl

/-- `BR` at `p2`. Source: none: infrastructure. Kind: L -/
theorem twoStag_BR_p2 :
    BR (proc2 p q hp0 hp1 hq0 hq1) twoStag .p2 =
      argmaxFull fun a : Act2 => if a = .a then 2 * p else 1 - p := by
  unfold BR
  congr 1
  funext a
  obtain ⟨-, -, h3, h4⟩ := twoStag_pointGame p q hp0 hp1 hq0 hq1
  cases a
  · rw [h3]; rfl
  · rw [h4]; rfl

/-- The Stag Hunt is almost fair. Source: `dp-local-opt` `twoStag_HH_strict_local_max`. Kind: L -/
theorem twoStag_almostFair : AlmostFair twoStag := twoStag_HH_strict_local_max.1

/-- **T2's witness (N+), FA-12′'s product row**: on the Stag Hunt with the product self-model
`C' = proc2 β β` (`0 < β < 1`) and `s°` masked-prior-calibrated under `lift C'`, the disposition
values are `V_{s°}(pol_1 = S) = 2β`, `V_{s°}(pol_1 = H) = 1 − β`, and `UDT_{s°,pol}` plays `S` at
both points if `β > ⅓` and `H` at both if `β < ⅓` (the two implications are what is proved; at
`β = ⅓` the output is uniform, not stated).
Source: `faithful.md` FA-12′ ("Product self-model `P(S) = β`: `2β` vs `1−β`, plays `S` iff
`β > ⅓`")
Kind: N+
Fidelity: exact
Hyps: (a) `MaskedPriorCalibrated (lift univ (proc2 β β)) (Rel twoStag) s°` -/
theorem twoStag_udtProc_product (β : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ)
    (hcal : MaskedPriorCalibrated (lift Finset.univ (proc2 β β hβ0.le hβ1.le hβ0.le hβ1.le))
      (relocRoot Finset.univ twoStag) s₀) :
    s₀.V (polEv Finset.univ .p1 .a) = 2 * β ∧ s₀.V (polEv Finset.univ .p1 .b) = 1 - β ∧
    (1 / 3 < β → udtProc s₀ (polEv Finset.univ) = Proc.ofFun fun _ => Act2.a) ∧
    (β < 1 / 3 → udtProc s₀ (polEv Finset.univ) = profHH) := by
  have hB := twoStag_almostFair
  have hmem : ∀ d : Pt2, d ∈ (Finset.univ : Finset Pt2) := fun d => Finset.mem_univ d
  obtain ⟨h1, h2, h3, h4⟩ := twoStag_pointGame β β hβ0.le hβ1.le hβ0.le hβ1.le
  have hfs := hcal.1
  refine ⟨?_, ?_, fun hβ => ?_, fun hβ => ?_⟩
  · rw [polEv_V_eq_value _ twoStag _ s₀ hB hcal.2 (hmem .p1) _ (hfs (.inl .p1) .a), h1]
  · rw [polEv_V_eq_value _ twoStag _ s₀ hB hcal.2 (hmem .p1) _ (hfs (.inl .p1) .b), h2]
  · funext d
    show udtProc s₀ (polEv Finset.univ) d = FinDistr.pure Act2.a
    rw [udtProc_polEv_eq_pure_iff _ twoStag _ s₀ hB hcal (hmem d)]
    cases d
    · rw [twoStag_BR_p1]; apply argmaxFull_act2_eq_a; simp; linarith
    · rw [twoStag_BR_p2]; apply argmaxFull_act2_eq_a; simp; linarith
  · funext d
    cases d
    · show udtProc s₀ (polEv Finset.univ) .p1 = FinDistr.act2 0 le_rfl zero_le_one
      rw [← pure_b_eq_act2, udtProc_polEv_eq_pure_iff _ twoStag _ s₀ hB hcal (hmem .p1),
        twoStag_BR_p1]
      apply argmaxFull_act2_eq_b; simp; linarith
    · show udtProc s₀ (polEv Finset.univ) .p2 = FinDistr.act2 0 le_rfl zero_le_one
      rw [← pure_b_eq_act2, udtProc_polEv_eq_pure_iff _ twoStag _ s₀ hB hcal (hmem .p2),
        twoStag_BR_p2]
      apply argmaxFull_act2_eq_b; simp; linarith

/-- The `(⅓, ⅓)` self-model. Source: `faithful.md` FA-12′. Kind: D -/
abbrev third : Proc Pt2 (fun _ => Act2) ℚ :=
  proc2 (1 / 3) (1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `BR` under the `(⅓, ⅓)` self-model is everything at both points (`V(C'[d↦S]) = V(C'[d↦H]) = ⅔`).
Source: `faithful.md` FA-12′ ("`V(C'[d₁↦a]) = V(C'[d₁↦b]) = ⅔`")
Kind: P -/
theorem third_BR (d : Pt2) : BR third twoStag d = Finset.univ := by
  obtain ⟨h1, h2, h3, h4⟩ := twoStag_pointGame (1 / 3) (1 / 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  ext a
  simp only [mem_BR, Finset.mem_univ, iff_true]
  intro b
  unfold third
  cases d <;> cases a <;> cases b <;> simp only [h1, h2, h3, h4] <;> norm_num

/-- **T4(c) — refuted row: "self-confirming = Nash" at Definition 17's procedure level.** On the
Stag Hunt the `(⅓, ⅓)` self-model is Nash and (mixed) coherent, and some `s°` is masked-calibrated
to it; yet for *every* such `s°` Definition 17's uniform-tie `UDT_{s°,pol}` outputs `(½, ½) ≠
(⅓, ⅔)` at `p1`. The surviving neighbour is `selfConfirming_iff_nash` (advocacy grade: `T_UDT`
approves `(⅓,⅓)`, since every action is a best reply).
Quoted claim (faithful.md Dead 13, FA-12 original): "`(s°,ρ)` self-confirming ⟺ `C'` is a mixed
Nash equilibrium of the point game ⟺ mixed-Definition-22 coherent" read with self-confirmation as
`UDT_{s°,ρ} = C'` (Definition 17's procedure). Reading: the procedure-level identity, as the
source itself retracts ("not for Definition 17's uniform-tie procedure").
Source: `faithful.md` FA-12′ ("table `v(aa)=2, v(bb)=1`, `C'(a) = ⅓` at both points gives … Nash,
coherent while Definition 17 outputs `(½,½) ≠ (⅓,⅔)`"), Dead 13; dp-cf-2-008
Kind: N+ (refutation)
Fidelity: exact
Hyps: none -/
theorem third_nash_coherent_not_udtProc :
    Nash third twoStag ∧ Coherent third twoStag ∧
    (∃ s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ,
      MaskedPriorCalibrated (lift Finset.univ third) (relocRoot Finset.univ twoStag) s₀) ∧
    ∀ s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ,
      MaskedPriorCalibrated (lift Finset.univ third) (relocRoot Finset.univ twoStag) s₀ →
        (udtProc s₀ (polEv Finset.univ) .p1).w .a = 1 / 2 ∧ (third .p1).w .a = 1 / 3 ∧
        udtProc s₀ (polEv Finset.univ) ≠ third := by
  have hB := twoStag_almostFair
  have hN : Nash third twoStag := by
    intro d _ a _
    rw [third_BR]; exact Finset.mem_univ a
  have hfs : (third : Proc Pt2 (fun _ => Act2) ℚ).FullSupport := by
    intro d a
    cases d <;> cases a
    · show (0 : ℚ) < 1 / 3; norm_num
    · show (0 : ℚ) < 1 - 1 / 3; norm_num
    · show (0 : ℚ) < 1 / 3; norm_num
    · show (0 : ℚ) < 1 - 1 / 3; norm_num
  refine ⟨hN, (nash_iff_coherent twoStag third hB).mp hN,
    ⟨priorState _ _, maskedPriorCalibrated_priorState _ _ (lift_fullSupport _ hfs)⟩,
    fun s₀ hcal => ?_⟩
  have hw : (udtProc s₀ (polEv Finset.univ) .p1).w .a = 1 / 2 := by
    rw [udtProc_polEv_eq_bestReply _ twoStag third s₀ hB hcal (Finset.mem_univ _), uniformOn_w,
      third_BR, if_pos (Finset.mem_univ _), Finset.card_univ]
    have hc : Fintype.card Act2 = 2 := rfl
    rw [hc]; norm_num
  refine ⟨hw, rfl, fun heq => ?_⟩
  rw [heq] at hw
  have : (third .p1).w .a = 1 / 3 := rfl
  rw [this] at hw
  norm_num at hw

/-- The miscoordinating assignment `(S, H)` as a `proc2`. Source: none: infrastructure. Kind: L -/
theorem ofFun_SH_eq_proc2 :
    (Proc.ofFun fun d : Pt2 => match d with | .p1 => Act2.a | .p2 => Act2.b :
        Proc Pt2 (fun _ => Act2) ℚ) =
      proc2 1 0 zero_le_one le_rfl le_rfl zero_le_one := by
  funext d
  cases d
  · exact pure_a_eq_act2
  · exact pure_b_eq_act2

/-- **T4(e) — FA-16, tie damage across points (`N`)**: under the tying `(⅓, ⅓)` self-model,
`T_UDT` approves every per-point tie resolution, in particular the miscoordinating `(S, H)` of
value `0` (optimum `2`).
Source: `faithful.md` FA-16 ("`T_{UDT_{s°,ρ}}` approves every per-point resolution of ties,
hence the miscoordinating products")
Kind: N+
Fidelity: variant: the Stag Hunt's table in place of FA-11's coordination miniature
Hyps: (a) `MaskedPriorCalibrated (lift univ third) (Rel twoStag) s°` -/
theorem third_tUdt_miscoordinates (s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ)
    (hcal : MaskedPriorCalibrated (lift Finset.univ third) (relocRoot Finset.univ twoStag) s₀) :
    TUdt s₀ (polEv Finset.univ)
      (Proc.ofFun fun d : Pt2 => match d with | .p1 => Act2.a | .p2 => Act2.b) twoStag ∧
    value (Proc.ofFun fun d : Pt2 => match d with | .p1 => Act2.a | .p2 => Act2.b) twoStag = 0 := by
  constructor
  · rw [tUdt_polEv_iff _ twoStag third s₀ twoStag_almostFair (fun _ _ => Finset.mem_univ _) hcal]
    intro d _ a _
    rw [third_BR]; exact Finset.mem_univ a
  · rw [ofFun_SH_eq_proc2, twoStag_value]; norm_num

/-- **T4(d) — the Stag Hunt's bad fixed point**: for a near-`(H,H)` product self-model `proc2 β β`
with `0 < β < ⅓` (in particular the tremble `(H,H)^ε`, `β = ε/2`, `ε < ⅔`), `UDT_{s°,pol}` outputs
`(H, H)`; `(H, H)` is Nash and coherent (hence `T_UDT` with a calibrated prior approves it: it is
self-confirming in the limit) and not optimal (`1 < 2`). Self-confirmation buys coherence, not
optimality (`Coherent ⊄ IsOptimal`).
Source: `faithful.md` FA-12′ ("Self-model `(H,H)^ε`: values `ε` vs `1−ε/2`, output `(H,H)` —
self-confirming in the limit and non-optimal (`1 < 2`)"); `dp-local-opt`
`twoStag_HH_coherent_thm1_not_optimal`
Kind: N+
Fidelity: exact
Hyps: (a) `MaskedPriorCalibrated (lift univ (proc2 β β)) (Rel twoStag) s°` -/
theorem twoStag_HH_fixedPoint (β : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1 / 3)
    (s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ)
    (hcal : MaskedPriorCalibrated
      (lift Finset.univ (proc2 β β hβ0.le (by linarith) hβ0.le (by linarith)))
      (relocRoot Finset.univ twoStag) s₀) :
    udtProc s₀ (polEv Finset.univ) = profHH ∧ Nash profHH twoStag ∧ Coherent profHH twoStag ∧
    ¬ IsOptimal profHH twoStag ∧ value profHH twoStag = 1 ∧
    value (proc2 1 1 zero_le_one le_rfl zero_le_one le_rfl) twoStag = 2 := by
  obtain ⟨hcoh, -, -, hnot, hval, hSS⟩ := twoStag_HH_coherent_thm1_not_optimal
  obtain ⟨-, -, -, hH⟩ := twoStag_udtProc_product β hβ0 (by linarith) s₀ hcal
  exact ⟨hH hβ1, (nash_iff_coherent twoStag profHH twoStag_almostFair).mpr hcoh, hcoh, hnot,
    hval, hSS⟩

/-- **T4(d), the tremble form**: the tremble `(H,H)^ε` of Definition 10 is `proc2 (ε/2) (ε/2)`, so
for `0 < ε < ⅔` and `s°` masked-calibrated under `lift (H,H)^ε`, `UDT_{s°,pol} = (H, H)`.
Source: `faithful.md` FA-12′ ("Self-model `(H,H)^ε`: values `ε` vs `1−ε/2`, output `(H,H)`")
Kind: N+
Fidelity: exact (`ε` small is the explicit bound `ε < ⅔`)
Hyps: (a) `MaskedPriorCalibrated (lift univ (tremble profHH ε)) (Rel twoStag) s°` -/
theorem twoStag_tremble_HH (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 2 / 3)
    (s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ)
    (hcal : MaskedPriorCalibrated (lift Finset.univ (tremble profHH ε h0.le (by linarith)))
      (relocRoot Finset.univ twoStag) s₀) :
    udtProc s₀ (polEv Finset.univ) = profHH ∧ ¬ IsOptimal profHH twoStag := by
  rw [DpEdtUdtFair.tremble_proc2] at hcal
  have hβ0 : 0 < (1 - ε) * 0 + ε / 2 := by linarith
  have hβ1 : (1 - ε) * 0 + ε / 2 < 1 / 3 := by linarith
  obtain ⟨h, -, -, hnot, -, -⟩ := twoStag_HH_fixedPoint _ hβ0 hβ1 s₀ hcal
  exact ⟨h, hnot⟩

end stag

end Cleanroom.Decision.DpFaithfulUdt
