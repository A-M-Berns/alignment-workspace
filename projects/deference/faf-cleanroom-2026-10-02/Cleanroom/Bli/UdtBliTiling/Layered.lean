import Cleanroom.Bli.UdtBliTiling.Independent
import Cleanroom.Bli.UdtBliTiling.IndepCalc
import Cleanroom.Bli.UdtBliCore.WitnessLayers
import Cleanroom.Udt.UdtPaperTiling.Theorem1Witness

/-!
# `udt-bli-tiling` · Layered: the procedure-level form with Policy Fairness (T5, load-bearing 5)

Over a procedure layer `L : P.ProcLayer` with `PolicyFair L` (`udt-bli-core`'s predicate, the
run's one definition of (F)): **the value of a positive procedure is the ex-ante value of its
effective behaviour** (`procEU_eq_exAnteValue_of_policyFair`: the policy cell `pp = eff p` is the
union of the procedure cells with that `eff`, all of equal value under fairness — proved by the
fibre averaging `condExp_eq_of_fibers`). Hence **procedure-level tiling is policy-level
optimality of the effective behaviour** (`layered_tiles_iff`), and with T1: over a prior
satisfying T1's package, no positive procedure strictly beats a procedure whose effective
behaviour is a one-step policy (`layered_oneStep_tiles_of_independent`). The paper's own
statement is `udt-paper-tiling`'s `thm2_udt10_tiling`/`thm2_no_strict_selfMod` (whose proof
supports only the fixed-point form, [[udt-paper-tiling-findings]]); this file does not re-prove
it.

**Witnesses.** `PolicyFair` on the trivial layer is a tautology (`policyFair_trivialLayer`), so
the N+ must have ≥ 2 procedures of equal `eff` and different code:
* `layerOf fairU` (core, `policyFair_fair`): procedures `0` and `1` behave alike and score `1`;
  the layered tiling conclusion holds for both (`fair_layer_tiles`). But `layerPrior fairU` is
  *not* in T1's package (its policy points are perfectly correlated: only the two constant
  policies have mass, so `NDPOLICY` and `IndependentPoints` fail) — it is the N+ of the general
  layered lemma, not of the composition with T1 (finding on the mandate's suggested witness).
* `withBit corrDataFull` with `bitLayer`: the full-support independent prior with an extra
  implementation bit that the utility ignores; `(abPol, true)` and `(abPol, false)` are two
  procedures with the same effective behaviour `ab`, fairness holds (`policyFair_bitLayer`),
  T1's package holds (transferred from `corrPriorFull`), and the layered tiling conclusion holds
  for the one-step behaviour `ab` (`corrFullBit_tiles`) — the N+ of record for T5.
* N− (imported, no new fairness failure witness is built in this run): `not_policyFair_unfair`
  with `thm1_fails_unfair` (`unfair_layer_fails`), and `NoFair.no_fairness_no_tiling` (cited).

Sources: bli-paper-006/007 (`main.tex` 140–199: Policy Fairness, Theorem 2); bli-soto-b-045
(the outline); mandate T5.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Udt.UdtPaperTiling Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A] [Fintype A]

section General

variable {P : FiniteBLIPrior 𝒮 m 𝒟 A}

/-- A positive procedure has a positive effective behaviour (its policy cell contains its
procedure cell).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_eff_pos (L : P.ProcLayer) {p : L.Proc} (hp : 0 < L.procMass p) :
    0 < P.policyMass (L.eff p) := by
  apply lt_of_lt_of_le hp
  apply massOf_mono P.μ P.μ_nonneg
  intro ω hω
  show P.pp ω = L.eff p
  rw [L.pp_eff, hω]

/-- **Under Policy Fairness, the value of a positive procedure is the ex-ante value of its
effective behaviour**: `𝔼[U | proc = p] = 𝔼[U | pp = eff p]`. The policy cell is the union of
the procedure cells `proc = q` with `eff q = eff p`; each positive one has value `procEU p` by
fairness; the average is `procEU p`.
Source: bli-paper-004/005 (`main.tex` 140–147: Policy Fairness identifies `E_p(u | π* = ⌜π⌝)`
across implementations); mandate T5 (`procEU_eq_exAnteValue_of_policyFair`)
Kind: P (`condExp_eq_of_fibers`)
Fidelity: exact
Hyps: (a) `PolicyFair L`, `0 < procMass p`; does not use faith -/
theorem procEU_eq_exAnteValue_of_policyFair (L : P.ProcLayer) (hF : P.PolicyFair L) (p : L.Proc)
    (hp : 0 < L.procMass p) : L.procEU p = P.exAnteValue (L.eff p) := by
  symm
  unfold FiniteBLIPrior.exAnteValue
  apply condExp_eq_of_fibers P.μ P.U P.μ_nonneg _ L.proc (L.procEU p) (policyMass_eff_pos L hp)
  intro q hq
  have hq' : 0 < L.procMass q := by
    apply lt_of_lt_of_le hq
    apply massOf_mono P.μ P.μ_nonneg
    intro ω hω; exact hω.2
  have heff : L.eff q = L.eff p := by
    obtain ⟨ω, hω, _⟩ := (massOf_pos_iff P.μ P.μ_nonneg _).mp hq
    rw [← hω.1, L.pp_eff, hω.2]
  have e : condExp P.μ P.U (fun ω => P.pp ω = L.eff p ∧ L.proc ω = q) = L.procEU q := by
    unfold FiniteBLIPrior.ProcLayer.procEU
    apply condExp_congr
    intro ω
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [L.pp_eff, h, heff], h⟩
  rw [e]
  exact hF q p heff hq' hp

/-- **Procedure-level tiling is policy-level optimality of the effective behaviour**, under
Policy Fairness: for a positive procedure `p*`, no positive procedure strictly beats `p*` iff
`eff p*` is prior-optimal among positive-mass policies.
Source: bli-paper-005/007 (Theorems 1–2's shape: fairness reduces procedures to behaviours);
bli-soto-b-045 ("by fairness its actions look better"); mandate T5
Kind: P
Fidelity: exact
Hyps: (a) `PolicyFair L`, `0 < procMass p*`; does not use faith -/
theorem layered_tiles_iff (L : P.ProcLayer) (hF : P.PolicyFair L) (ps : L.Proc)
    (hps : 0 < L.procMass ps) :
    (∀ q, 0 < L.procMass q → L.procEU q ≤ L.procEU ps) ↔
      P.IsPriorOptimalOnSupport (L.eff ps) := by
  constructor
  · intro h π' hπ'
    obtain ⟨ω, hω, hμ⟩ := (massOf_pos_iff P.μ P.μ_nonneg _).mp hπ'
    have hq : 0 < L.procMass (L.proc ω) :=
      (massOf_pos_iff P.μ P.μ_nonneg _).mpr ⟨ω, rfl, hμ⟩
    have hπ'' : π' = L.eff (L.proc ω) := by rw [← hω]; exact L.pp_eff ω
    rw [hπ'', ← procEU_eq_exAnteValue_of_policyFair L hF _ hq,
      ← procEU_eq_exAnteValue_of_policyFair L hF ps hps]
    exact h _ hq
  · intro h q hq
    rw [procEU_eq_exAnteValue_of_policyFair L hF q hq,
      procEU_eq_exAnteValue_of_policyFair L hF ps hps]
    exact h _ (policyMass_eff_pos L hq)

/-- **The layered form of T1 (one level, Policy Fairness)**: over a prior with
`NDHOME ∧ NDPOLICY ∧ ReflectivePolicy ∧ LocalUtility ∧ IndependentPoints` and a procedure layer
with `PolicyFair`, no positive procedure strictly beats a positive procedure whose effective
behaviour is a one-step policy.
Source: bli-paper-006/007 (Theorem 2, over the run's `PolicyFair`; the paper's own proof is
`udt-paper-tiling`'s `thm2_udt10_tiling`, fixed-point form only); bli-soto-b-045; mandate T5
Kind: C (`layered_tiles_iff`, `oneStep_tiles_of_independent`)
Fidelity: exact (one level; fairness and independence both explicit)
Hyps: (a) the five structural predicates, `PolicyFair L`, `0 < procMass p*`; does not use faith -/
theorem layered_oneStep_tiles_of_independent [Nonempty A] (hhome : P.NDHOME) (hpol : P.NDPOLICY)
    (hR : P.ReflectivePolicy) (hL : P.LocalUtility) (hI : P.IndependentPoints) (L : P.ProcLayer)
    (hF : P.PolicyFair L) (ps : L.Proc) (h1 : P.IsOneStepPolicy (L.eff ps))
    (hps : 0 < L.procMass ps) :
    ∀ q, 0 < L.procMass q → L.procEU q ≤ L.procEU ps :=
  (layered_tiles_iff L hF ps hps).mpr
    (P.isPriorOptimalOnSupport_of_isPriorOptimal
      (oneStep_tiles_of_independent hhome hpol hR hL hI _ h1).1)

end General

/-! ## N+ for the general layered lemma: core's fair layer -/

namespace FairLayer

/-- **The fair layer tiles**: on `layerPrior fairU` with `layerOf fairU` (procedures `0`, `1`
behave as `const true`, `2` as `const false`; fairness holds), no positive procedure strictly
beats procedure `0`, nor procedure `1` (a different implementation of the same behaviour); and
`const true` is prior-optimal among positive policies. This is the N+ of `layered_tiles_iff`
with ≥ 2 procedures of equal `eff`. It is **not** an instance of T1's package
(`not_in_package`: `NDPOLICY` fails — the policy points are perfectly correlated).
Source: bli-paper-004 (Policy Fairness, "written in C++ rather than Python"); mandate T5
(witness)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fair_layer_tiles :
    (∀ q, 0 < (layerOf fairU).procMass q → (layerOf fairU).procEU q ≤ (layerOf fairU).procEU (0 : Fin 3)) ∧
    (∀ q, 0 < (layerOf fairU).procMass q → (layerOf fairU).procEU q ≤ (layerOf fairU).procEU (1 : Fin 3)) ∧
    (layerPrior fairU).IsPriorOptimalOnSupport (fun _ => true) ∧
    (layerOf fairU).eff (0 : Fin 3) = (layerOf fairU).eff (1 : Fin 3) ∧ (0 : Fin 3) ≠ 1 := by
  have hv : ∀ q : Fin 3, (layerOf fairU).procEU q ≤ 1 := by
    intro q; rw [procEU_layerOf]
    match q with
    | 0 => exact le_rfl
    | 1 => exact le_rfl
    | 2 => norm_num
  have h0 : ∀ q, 0 < (layerOf fairU).procMass q →
      (layerOf fairU).procEU q ≤ (layerOf fairU).procEU (0 : Fin 3) := by
    intro q _; rw [procEU_layerOf fairU 0]; exact hv q
  refine ⟨h0, fun q hq => ?_, ?_, rfl, by decide⟩
  · rw [procEU_layerOf fairU 1]; exact hv q
  · have := (layered_tiles_iff (layerOf fairU) (policyFair_fair).1 (0 : Fin 3)
      (by rw [procMass_layerOf]; norm_num)).mp h0
    exact this

/-- `layerPrior fairU` is outside T1's package: `NDPOLICY` fails (the policy `ab` has no mass).
Source: mandate T5 (the suggested N+ does not inhabit T1's package — finding)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem not_in_package : ¬ (layerPrior fairU).NDPOLICY := by
  intro h
  have hz : (layerPrior fairU).policyMass abPol = 0 := by
    unfold FiniteBLIPrior.policyMass layerPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    obtain ⟨i, j⟩ := ω
    rw [if_neg]
    intro he
    fin_cases j
    · exact const_ne_abPol true he
    · exact const_ne_abPol true he
    · exact const_ne_abPol false he
  have := h abPol
  rw [hz] at this
  exact lt_irrefl _ this

/-- **The unfair layer fails the layered conclusion** (imported N−, no new witness): procedures
`0` and `1` behave alike, both positive, with values `1` and `−1`, so procedure `0` strictly beats
procedure `1`; and `PolicyFair` fails there.
Source: bli-paper-004/005; `udt-paper-tiling`'s `thm1_fails_unfair`; core's
`not_policyFair_unfair`; mandate T5 (N−)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem unfair_layer_fails :
    ¬ (layerPrior unfairU).PolicyFair (layerOf unfairU) ∧
      ¬ (∀ q, 0 < (layerOf unfairU).procMass q →
          (layerOf unfairU).procEU q ≤ (layerOf unfairU).procEU (1 : Fin 3)) := by
  obtain ⟨_, h0, _, v0, v1⟩ := thm1_fails_unfair
  refine ⟨not_policyFair_unfair, fun h => ?_⟩
  have := h (0 : Fin 3) h0
  rw [v0, v1] at this
  norm_num at this

end FairLayer

/-! ## The implementation-bit layer over an independent prior (N+ of record for T5) -/

/-- Summing a function of the first coordinate over `Ω₀ × Bool` doubles it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prod_bool_fst {Ω₀ : Type} [Fintype Ω₀] (G : Ω₀ → ℚ) :
    ∑ ω : Ω₀ × Bool, G ω.1 = 2 * ∑ ω₀, G ω₀ := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _; ring

/-- Summing a function of the first coordinate on the fibre `snd = b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prod_bool_snd {Ω₀ : Type} [Fintype Ω₀] (G : Ω₀ → ℚ) (b : Bool) :
    ∑ ω : Ω₀ × Bool, (if ω.2 = b then G ω.1 else 0) = ∑ ω₀, G ω₀ := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω₀ _
  rw [Fintype.sum_bool]
  cases b <;> simp

variable (D : IndepData 𝒮 m 𝒟 A)

/-- **The prior with an implementation bit**: the base outcome gains a fair coin `b` that the
state, the small truths and the utility ignore; the policy law is unchanged. Procedures are
`(policy, bit)` (`bitLayer`), so every behaviour has two implementations.
Source: bli-paper-004 ("written in C++ rather than Python"); mandate T5 (the N+ must have ≥ 2
procedures of equal `eff`)
Kind: D
Fidelity: exact -/
def withBit : IndepData 𝒮 m 𝒟 A where
  Ω₀ := D.Ω₀ × Bool
  μ₀ := fun ω => D.μ₀ ω.1 * (1 / 2)
  μ₀_nonneg := fun ω => mul_nonneg (D.μ₀_nonneg ω.1) (by norm_num)
  μ₀_sum_one := by
    rw [sum_prod_bool_fst (fun ω₀ => D.μ₀ ω₀ * (1 / 2)), ← Finset.sum_mul, D.μ₀_sum_one]
    norm_num
  state₀ := fun ω => D.state₀ ω.1
  small₀ := fun ω => D.small₀ ω.1
  faith₀ := by
    intro T φ
    have h1 : integralOf (fun ω : D.Ω₀ × Bool => D.μ₀ ω.1 * (1 / 2))
        (fun ω => ind (D.small₀ ω.1 φ)) (fun ω => D.state₀ ω.1 = T) =
        integralOf D.μ₀ (fun ω₀ => ind (D.small₀ ω₀ φ)) (fun ω₀ => D.state₀ ω₀ = T) := by
      unfold integralOf
      rw [sum_prod_bool_fst (fun ω₀ => if D.state₀ ω₀ = T then
        D.μ₀ ω₀ * (1 / 2) * ind (D.small₀ ω₀ φ) else 0), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω₀ _; split_ifs <;> ring
    have h2 : massOf (fun ω : D.Ω₀ × Bool => D.μ₀ ω.1 * (1 / 2)) (fun ω => D.state₀ ω.1 = T) =
        massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ = T) := by
      unfold massOf
      rw [sum_prod_bool_fst (fun ω₀ => if D.state₀ ω₀ = T then D.μ₀ ω₀ * (1 / 2) else 0),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω₀ _; split_ifs <;> ring
    exact h1.trans ((D.faith₀ T φ).trans (by rw [h2]))
  ν := D.ν
  ν_nonneg := D.ν_nonneg
  ν_sum_one := D.ν_sum_one
  U₀ := fun ω π => D.U₀ ω.1 π

/-- The mass of a base event that ignores the bit is the original mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_withBit_fst (E : D.Ω₀ → Prop) [DecidablePred E] :
    massOf (withBit D).μ₀ (fun ω => E ω.1) = massOf D.μ₀ E := by
  change massOf (fun ω : D.Ω₀ × Bool => D.μ₀ ω.1 * (1 / 2)) (fun ω => E ω.1) = _
  unfold massOf
  rw [sum_prod_bool_fst (fun ω₀ => if E ω₀ then D.μ₀ ω₀ * (1 / 2) else 0), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _; split_ifs <;> ring

/-- The mass of the bit is `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_withBit_snd (b : Bool) : massOf (withBit D).μ₀ (fun ω => ω.2 = b) = 1 / 2 := by
  change massOf (fun ω : D.Ω₀ × Bool => D.μ₀ ω.1 * (1 / 2)) (fun ω => ω.2 = b) = _
  unfold massOf
  rw [sum_prod_bool_snd (fun ω₀ => D.μ₀ ω₀ * (1 / 2)) b, ← Finset.sum_mul, D.μ₀_sum_one, one_mul]

/-- **The one-step values ignore the bit.**
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_withBit (T : ↥𝒟) (a : A) : (withBit D).toPrior.EU T a = D.toPrior.EU T a := by
  rw [IndepCalc.EU_toPrior (withBit D), IndepCalc.EU_toPrior D]
  change (∑ ω : D.Ω₀ × Bool, D.μ₀ ω.1 * (1 / 2) *
      ∑ π, (if π T = a then D.ν π * D.U₀ ω.1 π else 0)) / massOf D.ν (fun π => π T = a) = _
  rw [sum_prod_bool_fst (fun ω₀ => D.μ₀ ω₀ * (1 / 2) *
    ∑ π, (if π T = a then D.ν π * D.U₀ ω₀ π else 0)), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ω₀ _; ring

/-- **The ex-ante values ignore the bit.**
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exAnteValue_withBit (π : Policy 𝒟 A) (hπ : 0 < D.ν π) :
    (withBit D).toPrior.exAnteValue π = D.toPrior.exAnteValue π := by
  rw [IndepCalc.exAnteValue_toPrior (withBit D) π hπ, IndepCalc.exAnteValue_toPrior D π hπ]
  change ∑ ω : D.Ω₀ × Bool, D.μ₀ ω.1 * (1 / 2) * D.U₀ ω.1 π = _
  rw [sum_prod_bool_fst (fun ω₀ => D.μ₀ ω₀ * (1 / 2) * D.U₀ ω₀ π), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _; ring

/-- One-step policies transfer across the bit.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isOneStepPolicy_withBit_iff (π : Policy 𝒟 A) :
    (withBit D).toPrior.IsOneStepPolicy π ↔ D.toPrior.IsOneStepPolicy π := by
  unfold FiniteBLIPrior.IsOneStepPolicy FiniteBLIPrior.IsOneStepChoice
  simp only [EU_withBit]

/-- **The implementation-bit layer**: procedures `(policy, bit)`, effective behaviour the policy.
Source: bli-paper-004; mandate T5
Kind: D
Fidelity: exact -/
def bitLayer : (withBit D).toPrior.ProcLayer where
  Proc := Policy 𝒟 A × Bool
  proc := fun ω => (ω.2, ω.1.2)
  eff := Prod.fst
  pp_eff := fun _ => rfl

/-- The procedure cell `(π, b)` is the pair `snd = b ∧ pp = π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma proc_eq_iff (π : Policy 𝒟 A) (b : Bool) (ω : (withBit D).toPrior.Ω) :
    (bitLayer D).proc ω = (π, b) ↔ (ω.1.2 = b ∧ ω.2 = π) := by
  change ((ω.2, ω.1.2) = (π, b)) ↔ _
  rw [Prod.mk.injEq]
  exact and_comm

/-- The mass of a procedure: `ν π / 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma procMass_bitLayer (π : Policy 𝒟 A) (b : Bool) :
    (bitLayer D).procMass (π, b) = D.ν π * (1 / 2) := by
  unfold FiniteBLIPrior.ProcLayer.procMass
  rw [massOf_congr _ (proc_eq_iff D π b)]
  change massOf (withBit D).μ (fun ω => ω.1.2 = b ∧ ω.2 = π) = _
  rw [(withBit D).massOf_rect (fun ω₀ => ω₀.2 = b) (fun π' => π' = π), massOf_withBit_snd]
  have : massOf (withBit D).ν (fun π' => π' = π) = D.ν π := by
    change massOf D.ν (fun π' => π' = π) = D.ν π
    unfold massOf; simp
  rw [this]; ring

/-- **The value of a procedure ignores the bit**: `procEU (π, b) = ∑_{ω₀} μ₀ ω₀ · U₀ ω₀ π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma procEU_bitLayer (π : Policy 𝒟 A) (b : Bool) (hπ : 0 < D.ν π) :
    (bitLayer D).procEU (π, b) = ∑ ω₀, D.μ₀ ω₀ * D.U₀ ω₀ π := by
  unfold FiniteBLIPrior.ProcLayer.procEU
  rw [condExp_congr _ _ (proc_eq_iff D π b)]
  refine (IndepCalc.condExp_base_policy (withBit D) (fun ω₀ => ω₀.2 = b) π hπ).trans ?_
  rw [massOf_withBit_snd]
  change (∑ ω : D.Ω₀ × Bool, if ω.2 = b then D.μ₀ ω.1 * (1 / 2) * D.U₀ ω.1 π else 0) / (1 / 2) = _
  rw [sum_prod_bool_snd (fun ω₀ => D.μ₀ ω₀ * (1 / 2) * D.U₀ ω₀ π) b, div_eq_iff (by norm_num),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω₀ _; ring

/-- **Policy Fairness holds on the implementation-bit layer** of every `IndepData` prior: the two
implementations of a behaviour have the same value.
Source: bli-paper-004 (Policy Fairness); mandate T5 (N+)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem policyFair_bitLayer : (withBit D).toPrior.PolicyFair (bitLayer D) := by
  rintro ⟨π, b⟩ ⟨π', b'⟩ hpq hp hq
  have hπ : π = π' := hpq
  subst hπ
  have hν : 0 < D.ν π := by
    rw [procMass_bitLayer] at hp
    linarith
  rw [procEU_bitLayer D π b hν, procEU_bitLayer D π b' hν]

/-! ### The N+ of record: `corrDataFull` with the bit -/

namespace CorrFullBit

/-- **N+ of record for T5**: on `corrPriorFull` with an implementation bit, T1's full package
holds, Policy Fairness holds on the bit layer, `ab` is a one-step policy, `(ab, true)` and
`(ab, false)` are two different positive procedures with the same effective behaviour, and no
positive procedure strictly beats either of them.
Source: mandate T5 (witness); bli-paper-004/007
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tiles :
    (withBit corrDataFull).toPrior.NDHOME ∧ (withBit corrDataFull).toPrior.NDPOLICY ∧
    (withBit corrDataFull).toPrior.ReflectivePolicy ∧ (withBit corrDataFull).toPrior.LocalUtility ∧
    (withBit corrDataFull).toPrior.IndependentPoints ∧
    (withBit corrDataFull).toPrior.PolicyFair (bitLayer corrDataFull) ∧
    (withBit corrDataFull).toPrior.IsOneStepPolicy abPol ∧
    ((abPol, true) : Policy twoTables Bool × Bool) ≠ (abPol, false) ∧
    (bitLayer corrDataFull).eff (abPol, true) = (bitLayer corrDataFull).eff (abPol, false) ∧
    0 < (bitLayer corrDataFull).procMass (abPol, true) ∧
    0 < (bitLayer corrDataFull).procMass (abPol, false) ∧
    (∀ q, 0 < (bitLayer corrDataFull).procMass q →
      (bitLayer corrDataFull).procEU q ≤ (bitLayer corrDataFull).procEU (abPol, true)) ∧
    (∀ q, 0 < (bitLayer corrDataFull).procMass q →
      (bitLayer corrDataFull).procEU q ≤ (bitLayer corrDataFull).procEU (abPol, false)) := by
  obtain ⟨_, _, _, _, _, _, hhome₀, _⟩ := CorrFull.structure_all
  have hν : ∀ π : Policy twoTables Bool, 0 < corrDataFull.ν π :=
    fun π => prodLaw_pos (fun _ _ => by simp [twoHalf]) π
  have hpt : ∀ T a, 0 < massOf (withBit corrDataFull).ν (fun π => π T = a) := fun T a => by
    change 0 < massOf (prodLaw twoHalf) (fun π => π T = a)
    rw [IndepData.massOf_prodLaw_point twoHalf twoHalf_sum]; simp [twoHalf]
  have hs : ∀ T, 0 < massOf (withBit corrDataFull).μ₀
      (fun ω₀ => (withBit corrDataFull).state₀ ω₀ = T) := by
    intro T
    change 0 < massOf (withBit corrDataFull).μ₀ (fun ω₀ => corrDataFull.state₀ ω₀.1 = T)
    rw [massOf_withBit_fst corrDataFull (fun ω₀ => corrDataFull.state₀ ω₀ = T)]
    have := FiniteBLIPrior.NDHOME.stateMass_pos corrPriorFull hhome₀ T
    unfold corrPriorFull at this
    rwa [corrDataFull.stateMass_toPrior] at this
  have hhome : (withBit corrDataFull).toPrior.NDHOME := (withBit corrDataFull).ndhome_toPrior hs hpt
  have hpol : (withBit corrDataFull).toPrior.NDPOLICY :=
    (withBit corrDataFull).ndpolicy_toPrior (fun π => hν π)
  have hR : (withBit corrDataFull).toPrior.ReflectivePolicy :=
    (withBit corrDataFull).reflectivePolicy_toPrior
  have hL : (withBit corrDataFull).toPrior.LocalUtility :=
    (withBit corrDataFull).localUtility_home twoHalf twoHalf_sum rfl (fun ω => corrU ω.1)
      (fun ω π => CorrFull.U₀_home ω.1 π)
  have hI : (withBit corrDataFull).toPrior.IndependentPoints :=
    (withBit corrDataFull).independentPoints_toPrior_of_prodLaw twoHalf twoHalf_sum rfl
  have hF := policyFair_bitLayer corrDataFull
  have h1 : (withBit corrDataFull).toPrior.IsOneStepPolicy abPol :=
    (isOneStepPolicy_withBit_iff corrDataFull abPol).mpr CorrFull.oneStep_ab.1
  have hm : ∀ b, 0 < (bitLayer corrDataFull).procMass (abPol, b) := by
    intro b; rw [procMass_bitLayer]; exact mul_pos (hν _) (by norm_num)
  refine ⟨hhome, hpol, hR, hL, hI, hF, h1, by simp, rfl, hm true, hm false, ?_, ?_⟩
  · exact layered_oneStep_tiles_of_independent hhome hpol hR hL hI (bitLayer corrDataFull) hF
      (abPol, true) h1 (hm true)
  · exact layered_oneStep_tiles_of_independent hhome hpol hR hL hI (bitLayer corrDataFull) hF
      (abPol, false) h1 (hm false)

end CorrFullBit

end Cleanroom.Bli.UdtBliTiling
