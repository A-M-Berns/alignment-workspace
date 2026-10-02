import Cleanroom.Bli.UdtBliSist.Defs
import Cleanroom.Bli.UdtBliCore.ProductUtil

/-!
# `udt-bli-sist` · Sist: the SIST verdict identity with honest hypotheses (T2 a–c, f)

**Reference-point utilities.** Over `udt-bli-core`'s `IndepData` (base outcome `ω₀`, independent
policy law `ν`), a utility of the form `U₀ ω₀ π = f ω₀ (π (ref ω₀))` — each base outcome reads the
policy at *one* reference table — has the one-step value
`EU T a = ∑_{ω₀} μ₀ ω₀ · ∑_b μ(pp·ref ω₀ = b | pp·T = a) · f ω₀ b` (`EU_ref`), and the same
shape for `condEU` (`condEU_ref`). SIST, the homework mugging and the skeleton instance are all
of this form (`ref` = the state's own table in Ask states, Omega's pick `J` in Rec states).

**The SIST shape** (`SistShaped`): `Ask`/`Rec` predicates on tables, Omega's simulated table `J`
as a base coordinate (mandate §3.5), stakes `cN ω₀` (the cost at Ask) and `VN ω₀` (the reward at
Rec) that may depend on the base outcome — so the "noisy `U`" of bli-soto-b-2-011 (ii) is the
general case, not a variant — and a residual `r ω₀ (π Q)` read at the observed point.

**The identity** (`sist_identity`): at an observed ask-like table `Q` with both points positive,
`EU Q give − EU Q refuse = recTerm − askTerm + resTerm`, where
`askTerm = ∑_{Ask states} μ₀ · cN · δ_Q(state)`, `recTerm = ∑_{Rec states} μ₀ · VN · δ_Q(J)`, and
`δ_Q(T) = μ(T = give | Q = give) − μ(T = give | Q = refuse)` is the correlation bracket of
bli-soto-b-2-006. No verdict is a hypothesis: the hypotheses are the utility's shape and two
positivities; the sign is computed from the masses, the stakes and the brackets. Corollaries:
constant stakes (`sist_identity_const`), **`H_point`** (`sist_hpoint`: `V·μ(Rec)·ρ̄^Rec −
c·μ(Ask)`), **`H_unif`** (`sist_hunif`: `V·μ(Rec) − c·μ(Ask)`, the `//////` arithmetic), the
**symmetric model** (`sist_symmetric`: `(V·μ(Rec) − c·μ(Ask))·ρ̄`, whose sign is `ρ̄`-free), and the
sign corollary (`sist_sign_symmetric`). The hand-typed witnesses (the `44.1` instance, the
auditor's table, the noisy-`U` instance) are in `SistWitness.lean`; the two-ask-table family that
inhabits the symmetric model at `ρ̄ = (1+ρ)/2` is `SymWitness.lean`; the N+ of record over a
skeleton is `Skeleton.lean`.

Sources: bli-soto-a-077 / bli-soto-b-047 (the `//////` argument), bli-soto-b-2-006 (the
correlation bracket, the symmetric model), bli-soto-a-2-013 (`H_unif`/`H_point`, Omega's `J`),
bli-soto-b-2-011 and bli-soto-a-078 (noisy `U`), [[bli-program]] §3.9 U5 (the pinned-Ask
display `100 μ(Rec) ρ > 10 μ(Ask)`), mandate T2.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-! ## `condPoint` at the observed table -/

section CondPoint

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- `μ(pp·Q = b | pp·Q = a) = [b = a]` at a positive point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condPoint_self (Q : ↥𝒟) (b a : A) (ha : 0 < P.ppMass Q a) :
    condPoint P Q Q b a = if b = a then 1 else 0 := by
  unfold condPoint
  rw [pairMass_self]
  split_ifs with h
  · subst h; exact div_self (ne_of_gt ha)
  · exact zero_div _

/-- A cell's mass is at most its branch's: `jointMass T' T a ≤ stateMass T'`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_le_stateMass [Fintype A] (T' T : ↥𝒟) (a : A) :
    P.jointMass T' T a ≤ P.stateMass T' := by
  rw [P.stateMass_eq_sum_jointMass T' T]
  exact Finset.single_le_sum (fun b _ => P.jointMass_nonneg T' T b) (Finset.mem_univ a)

/-- **The degenerate-kernel collapse**: if one table carries all the mass, every one-step value
at a positive point of that table is its updateful value, so the one-step and updateful rules
coincide there — the branch decomposition has one term. This is what a delta superbelief does to
SIST: the Ask/Rec split is unrepresentable.
Source: [[bli-program]] §3.9 U5 ("with the degenerate kernel the Ask/Rec split cannot be
represented … EU collapses to the home branch"); mandate T2(g)
Kind: L
Fidelity: exact
Hyps: (a) `stateMass T₀ = 1`, positivity of the point; does not use faith -/
theorem collapse [Fintype A] (T₀ : ↥𝒟) (h1 : P.stateMass T₀ = 1) (a : A)
    (ha : 0 < P.ppMass T₀ a) : P.EU T₀ a = P.homeEU T₀ a := by
  have hz : ∀ T, T ≠ T₀ → P.stateMass T = 0 := by
    intro T hT
    have hsum := P.sum_stateMass
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T₀), h1] at hsum
    have hrest : ∑ T' ∈ univ.erase T₀, P.stateMass T' = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun T' _ => P.stateMass_nonneg T')).mp hrest T
      (Finset.mem_erase.mpr ⟨hT, Finset.mem_univ _⟩)
  have hj : ∀ T, T ≠ T₀ → P.jointMass T T₀ a = 0 := fun T hT =>
    le_antisymm ((jointMass_le_stateMass P T T₀ a).trans (le_of_eq (hz T hT)))
      (P.jointMass_nonneg T T₀ a)
  have hpp : P.ppMass T₀ a = P.jointMass T₀ T₀ a := by
    rw [P.ppMass_eq_sum_jointMass T₀ a, ← Finset.add_sum_erase _ _ (Finset.mem_univ T₀)]
    rw [Finset.sum_eq_zero (fun T hT => hj T (Finset.ne_of_mem_erase hT)), add_zero]
  rw [P.EU_eq_sum_branch T₀ a, ← Finset.add_sum_erase _ _ (Finset.mem_univ T₀)]
  rw [Finset.sum_eq_zero (fun T hT => by
    rw [P.branchProb_eq_zero_of_jointMass_eq_zero (hj T (Finset.ne_of_mem_erase hT)), zero_mul])]
  unfold FiniteBLIPrior.branchProb FiniteBLIPrior.homeEU
  rw [hpp, div_self (by rw [← hpp]; exact ne_of_gt ha), add_zero, one_mul]

/-- **Under the collapse, one-step = updateful as maximizer sets** at the mass-one table.
Source: [[bli-program]] §3.9 U5; mandate T2(g)
Kind: L
Fidelity: exact
Hyps: (a) `stateMass T₀ = 1`, positivity of every point at `T₀`; does not use faith -/
theorem collapse_iff [Fintype A] (T₀ : ↥𝒟) (h1 : P.stateMass T₀ = 1)
    (hpos : ∀ a, 0 < P.ppMass T₀ a) (a : A) :
    P.IsOneStepChoice T₀ a ↔ P.IsUpdatefulChoice T₀ a := by
  unfold FiniteBLIPrior.IsOneStepChoice FiniteBLIPrior.IsUpdatefulChoice
  apply forall_congr'
  intro b
  rw [collapse P T₀ h1 a (hpos a), collapse P T₀ h1 b (hpos b)]

end CondPoint

/-! ## Reference-point utilities over `IndepData` -/

section RefPoint

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [Fintype A] [DecidableEq A]
variable (D : IndepData 𝒮 m 𝒟 A)

/-- The policy sum of a reference-point integrand splits over the value at the reference:
`∑_π [π T = a] ν π · f (π R) = ∑_b ν(π R = b ∧ π T = a) · f b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_policy_ref (R T : ↥𝒟) (a : A) (f : A → ℚ) :
    (∑ π, if π T = a then D.ν π * f (π R) else 0) =
      ∑ b, massOf D.ν (fun π => π R = b ∧ π T = a) * f b := by
  unfold massOf
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hT : π T = a
  · simp only [hT, and_true, if_true]
    rw [Finset.sum_eq_single (π R)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [hT]

/-- **The one-step value of a reference-point utility**: at a positive point,
`EU T a = ∑_{ω₀} μ₀ ω₀ · ∑_b μ(pp·ref ω₀ = b | pp·T = a) · f ω₀ b`.
Source: bli-soto-a-2-012 (ii) (the one-step value as a branch mixture); mandate §3.5 (Omega's
simulated table as a coordinate)
Kind: L
Fidelity: exact -/
lemma EU_ref (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (T : ↥𝒟) (a : A) :
    D.toPrior.EU T a =
      ∑ ω₀, D.μ₀ ω₀ * ∑ b, condPoint D.toPrior (ref ω₀) T b a * f ω₀ b := by
  unfold FiniteBLIPrior.EU condExp
  change D.toPrior.ppUtil T a / D.toPrior.ppMass T a = _
  rw [D.ppUtil_toPrior, D.ppMass_toPrior]
  have hinner : ∀ ω₀, (∑ π, if π T = a then D.ν π * D.U₀ ω₀ π else 0) =
      ∑ b, massOf D.ν (fun π => π (ref ω₀) = b ∧ π T = a) * f ω₀ b := by
    intro ω₀
    rw [← sum_policy_ref D (ref ω₀) T a (f ω₀)]
    apply Finset.sum_congr rfl
    intro π _
    rw [hU]
  simp only [hinner, condPoint, D.pairMass_toPrior, D.ppMass_toPrior]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω₀ _
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [div_eq_mul_inv]
  ring

/-- The joint utility of a reference-point utility on a branch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointUtil_ref (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (T' T : ↥𝒟) (a : A) :
    D.toPrior.jointUtil T' T a = ∑ ω₀, if D.state₀ ω₀ = T' then
      D.μ₀ ω₀ * ∑ b, massOf D.ν (fun π => π (ref ω₀) = b ∧ π T = a) * f ω₀ b else 0 := by
  rw [D.jointUtil_toPrior]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases h : D.state₀ ω₀ = T'
  · simp only [h, if_true]
    congr 1
    rw [← sum_policy_ref D (ref ω₀) T a (f ω₀)]
    apply Finset.sum_congr rfl
    intro π _
    rw [hU]
  · simp [h]

/-- **The branch value of a reference-point utility**: at a positive point,
`condEU T' T a = 𝔼_{μ₀}[∑_b μ(pp·ref = b | pp·T = a) · f · b | state₀ = T']`.
Source: bli-soto-a-2-012 (i); mandate §3.5
Kind: L
Fidelity: exact -/
lemma condEU_ref (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (T' T : ↥𝒟) (a : A) :
    D.toPrior.condEU T' T a =
      condExp D.μ₀ (fun ω₀ => ∑ b, condPoint D.toPrior (ref ω₀) T b a * f ω₀ b)
        (fun ω₀ => D.state₀ ω₀ = T') := by
  unfold FiniteBLIPrior.condEU condExp
  change D.toPrior.jointUtil T' T a / D.toPrior.jointMass T' T a = _
  rw [jointUtil_ref D ref f hU, D.jointMass_toPrior]
  unfold integralOf
  simp only [condPoint, D.pairMass_toPrior, D.ppMass_toPrior]
  have e : ∀ ω₀, (if D.state₀ ω₀ = T' then D.μ₀ ω₀ * ∑ b,
      massOf D.ν (fun π => π (ref ω₀) = b ∧ π T = a) / massOf D.ν (fun π => π T = a) * f ω₀ b
      else 0) =
      (if D.state₀ ω₀ = T' then D.μ₀ ω₀ * ∑ b,
        massOf D.ν (fun π => π (ref ω₀) = b ∧ π T = a) * f ω₀ b else 0) *
        (massOf D.ν (fun π => π T = a))⁻¹ := by
    intro ω₀
    split_ifs
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [div_eq_mul_inv]
      ring
    · rw [zero_mul]
  simp only [e]
  rw [← Finset.sum_mul, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- **The home value of a self-reading reference-point utility**: if every outcome in the branch
`state₀ = Q` reads the policy at `Q` itself, then at a positive point
`homeEU Q a = 𝔼_{μ₀}[f · a | state₀ = Q]`.
Source: bli-soto-a-011 (the updateful picture inside the home branch)
Kind: L
Fidelity: exact -/
lemma homeEU_ref_self (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (Q : ↥𝒟) (a : A)
    (hrefQ : ∀ ω₀, D.state₀ ω₀ = Q → ref ω₀ = Q) (ha : 0 < massOf D.ν (fun π => π Q = a)) :
    D.toPrior.homeEU Q a = condExp D.μ₀ (fun ω₀ => f ω₀ a) (fun ω₀ => D.state₀ ω₀ = Q) := by
  unfold FiniteBLIPrior.homeEU
  rw [condEU_ref D ref f hU Q Q a]
  unfold condExp
  congr 1
  apply integralOf_congr_fun
  intro ω₀ hω
  rw [hrefQ ω₀ hω]
  have hpp : 0 < D.toPrior.ppMass Q a := by rw [D.ppMass_toPrior]; exact ha
  simp only [condPoint_self D.toPrior Q _ a hpp]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

end RefPoint

/-! ## The SIST shape -/

section Sist

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)}
variable (D : IndepData 𝒮 m 𝒟 Bool)
variable (Ask Rec : ↥𝒟 → Prop) [DecidablePred Ask] [DecidablePred Rec]
variable (J : D.Ω₀ → ↥𝒟) (Q : ↥𝒟) (cN VN : D.Ω₀ → ℚ) (r : D.Ω₀ → Bool → ℚ)

/-- **The reference table of the SIST utility**: an Ask state reads the policy at its own table,
a Rec state at Omega's simulated table `J ω₀`, a residual state at the observed table `Q`.
Source: bli-soto-a-077 (Ask branches evaluate their own point; Rec branches the asked table's);
bli-soto-a-2-013 (iii) (Omega's simulated table as a variable); mandate §3.5
Kind: D
Fidelity: exact -/
def sistRef (ω₀ : D.Ω₀) : ↥𝒟 :=
  if Ask (D.state₀ ω₀) then D.state₀ ω₀ else if Rec (D.state₀ ω₀) then J ω₀ else Q

/-- **The SIST payoff** read at the reference point: `−cN ω₀` for `give` at an Ask state, `VN ω₀`
for `give` at a Rec state, `0` for `refuse` in both, and the residual `r ω₀ b` elsewhere. The
stakes may depend on the base outcome (noisy `U`, bli-soto-b-2-011 (ii)).
Source: bli-soto-a-077 (the four cases `−10, 0, +100, 0`); bli-soto-b-2-011 (ii); mandate T2
Kind: D
Fidelity: exact (the residual reads the observed point, as `udt-bli-core`'s F-13) -/
def sistPay (ω₀ : D.Ω₀) (b : Bool) : ℚ :=
  if Ask (D.state₀ ω₀) then -cN ω₀ * ind b
  else if Rec (D.state₀ ω₀) then VN ω₀ * ind b else r ω₀ b

/-- **The SIST shape of a prior's utility**: `U₀ ω₀ π = sistPay ω₀ (π (sistRef ω₀))`.
Source: mandate T2 (`U₀ ω π := if Ask … then −c·[…] else if Rec … then V·[…] else r (π Q̂)`)
Kind: D
Fidelity: exact -/
def SistShaped : Prop :=
  ∀ ω₀ π, D.U₀ ω₀ π = sistPay D Ask Rec cN VN r ω₀ (π (sistRef D Ask Rec J Q ω₀))

/-- **The Ask term**: `∑_{Ask states} μ₀ · cN · δ_Q(state)` — the expected cost, weighted by how
much the observed point moves each Ask table's own point.
Source: bli-soto-b-2-006 (the `−10·P(Ask)·∑_j …` term); mandate T2(a)
Kind: D
Fidelity: exact -/
def askTerm : ℚ :=
  ∑ ω₀, if Ask (D.state₀ ω₀) then
    D.μ₀ ω₀ * cN ω₀ * pointCorr D.toPrior Q (D.state₀ ω₀) true false else 0

/-- **The Rec term**: `∑_{Rec states} μ₀ · VN · δ_Q(J)` — the expected reward, weighted by how much
the observed point moves the point at Omega's simulated table.
Source: bli-soto-b-2-006 (the `100·P(Rec)·∑_j P(J = j)·[…]` term); mandate T2(a)
Kind: D
Fidelity: exact -/
def recTerm : ℚ :=
  ∑ ω₀, if Ask (D.state₀ ω₀) then 0 else if Rec (D.state₀ ω₀) then
    D.μ₀ ω₀ * VN ω₀ * pointCorr D.toPrior Q (J ω₀) true false else 0

/-- **The residual term**: `∑_{other states} μ₀ · (r give − r refuse)`.
Source: [[bli-program]] §7 item 11 (keep the residual and carry its term); mandate §5.3
Kind: D
Fidelity: exact -/
def resTerm : ℚ :=
  ∑ ω₀, if Ask (D.state₀ ω₀) then 0 else if Rec (D.state₀ ω₀) then 0 else
    D.μ₀ ω₀ * (r ω₀ true - r ω₀ false)

/-- `μ₀(Ask)`: the base mass of the Ask class.
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def askMass : ℚ := ∑ ω₀, if Ask (D.state₀ ω₀) then D.μ₀ ω₀ else 0

/-- `μ₀(Rec ∖ Ask)`: the base mass of the Rec class (Ask takes precedence where both hold).
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def recMass : ℚ :=
  ∑ ω₀, if Ask (D.state₀ ω₀) then 0 else if Rec (D.state₀ ω₀) then D.μ₀ ω₀ else 0

/-- **The SIST verdict identity** (load-bearing 1, the general form): at an observed table `Q`
with both points positive, for a utility of the SIST shape,
`EU Q give − EU Q refuse = recTerm − askTerm + resTerm`. Nothing about the verdict is assumed: the
sign is computed from the base masses, the stakes and the correlation brackets `δ_Q`.
Source: bli-soto-a-077 / bli-soto-b-047 (the `//////` decomposition); bli-soto-b-2-006 (the
bracket); bli-soto-b-2-011 (ii) and bli-soto-a-078 (expectations in place of certainties: the
stakes are base-random); mandate T2(a)
Kind: C (`EU_ref` twice, then the three cases of the shape, with `δ_Q(Q) = 1` at the residual)
Fidelity: exact
Hyps: (a) the utility's shape (definitional on every shipped witness), positivity of the two
points; does not use faith -/
theorem sist_identity (hU : SistShaped D Ask Rec J Q cN VN r)
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false)) :
    D.toPrior.EU Q true - D.toPrior.EU Q false =
      recTerm D Ask Rec J Q VN - askTerm D Ask Q cN + resTerm D Ask Rec r := by
  rw [EU_ref D _ _ hU Q true, EU_ref D _ _ hU Q false]
  unfold askTerm recTerm resTerm
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω₀ _
  have hppg : 0 < D.toPrior.ppMass Q true := by rw [D.ppMass_toPrior]; exact hg
  have hppr : 0 < D.toPrior.ppMass Q false := by rw [D.ppMass_toPrior]; exact hr
  unfold sistRef sistPay
  by_cases hA : Ask (D.state₀ ω₀)
  · simp only [hA, if_true, Fintype.sum_bool, ind_true, ind_false]
    unfold pointCorr
    ring
  · by_cases hR : Rec (D.state₀ ω₀)
    · simp only [hA, hR, if_true, if_false, Fintype.sum_bool, ind_true, ind_false]
      unfold pointCorr
      ring
    · simp only [hA, hR, if_false, Fintype.sum_bool, condPoint_self D.toPrior Q _ _ hppg,
        condPoint_self D.toPrior Q _ _ hppr]
      simp
      ring

/-- **Constant stakes**: with `cN ≡ c` and `VN ≡ V`, the identity reads
`EU Q give − EU Q refuse = V · recTerm' − c · askTerm' + resTerm` with the stake-free terms.
Source: bli-soto-a-077; mandate T2(a)
Kind: C
Fidelity: exact
Hyps: (a) as `sist_identity` -/
theorem sist_identity_const (V c : ℚ)
    (hU : SistShaped D Ask Rec J Q (fun _ => c) (fun _ => V) r)
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false)) :
    D.toPrior.EU Q true - D.toPrior.EU Q false =
      V * recTerm D Ask Rec J Q (fun _ => 1) - c * askTerm D Ask Q (fun _ => 1) +
        resTerm D Ask Rec r := by
  rw [sist_identity D Ask Rec J Q _ _ r hU hg hr]
  have h1 : recTerm D Ask Rec J Q (fun _ => V) = V * recTerm D Ask Rec J Q (fun _ => 1) := by
    unfold recTerm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω₀ _
    split_ifs <;> ring
  have h2 : askTerm D Ask Q (fun _ => c) = c * askTerm D Ask Q (fun _ => 1) := by
    unfold askTerm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω₀ _
    split_ifs <;> ring
  rw [h1, h2]

/-! ### Class forms of the terms -/

/-- The Ask term is the class sum `∑_{T ∈ Ask} μ(state = T) · 𝔼[cN | T]·…`; with unit stakes it is
`∑_{T ∈ Ask} stateMass T · δ_Q(T)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askTerm_unit_eq_class :
    askTerm D Ask Q (fun _ => 1) =
      ∑ T ∈ univ.filter Ask, D.toPrior.stateMass T * pointCorr D.toPrior Q T true false := by
  unfold askTerm
  simp only [D.stateMass_toPrior, Finset.sum_filter, mul_one]
  unfold massOf
  have e : ∀ T : ↥𝒟, (if Ask T then (∑ ω₀, if D.state₀ ω₀ = T then D.μ₀ ω₀ else 0) *
      pointCorr D.toPrior Q T true false else 0) =
      ∑ ω₀, if Ask T ∧ D.state₀ ω₀ = T then D.μ₀ ω₀ * pointCorr D.toPrior Q T true false
        else 0 := by
    intro T
    split_ifs with hT
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω₀ _
      by_cases h : D.state₀ ω₀ = T
      · simp [h, hT]
      · simp [h]
    · simp [hT]
  simp only [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases hA : Ask (D.state₀ ω₀)
  · rw [if_pos hA, Finset.sum_eq_single (D.state₀ ω₀)]
    · simp [hA]
    · intro T _ hT
      rw [if_neg]
      rintro ⟨_, h2⟩
      exact hT h2.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hA]
    symm
    apply Finset.sum_eq_zero
    intro T _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hA (h2 ▸ h1)

/-- **Base masses are class masses**: for any predicate `p` on tables,
`∑_{ω₀} [p (state₀ ω₀)] μ₀ ω₀ = classMass (filter p)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMass_eq_classMass (p : ↥𝒟 → Prop) [DecidablePred p] :
    (∑ ω₀, if p (D.state₀ ω₀) then D.μ₀ ω₀ else 0) = classMass D.toPrior (univ.filter p) := by
  unfold classMass
  simp only [D.stateMass_toPrior, Finset.sum_filter]
  unfold massOf
  have e : ∀ T : ↥𝒟, (if p T then (∑ ω₀, if D.state₀ ω₀ = T then D.μ₀ ω₀ else 0) else 0) =
      ∑ ω₀, if p T ∧ D.state₀ ω₀ = T then D.μ₀ ω₀ else 0 := by
    intro T
    split_ifs with hT
    · apply Finset.sum_congr rfl
      intro ω₀ _
      by_cases h : D.state₀ ω₀ = T
      · simp [h, hT]
      · simp [h]
    · simp [hT]
  simp only [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases hA : p (D.state₀ ω₀)
  · rw [if_pos hA, Finset.sum_eq_single (D.state₀ ω₀)]
    · simp [hA]
    · intro T _ hT
      rw [if_neg]
      rintro ⟨_, h2⟩
      exact hT h2.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hA]
    symm
    apply Finset.sum_eq_zero
    intro T _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hA (h2 ▸ h1)

/-- The Ask mass is the class mass of the Ask tables.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askMass_eq_classMass : askMass D Ask = classMass D.toPrior (univ.filter Ask) :=
  baseMass_eq_classMass D Ask

/-- The Rec mass is the class mass of the tables that are Rec and not Ask.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recMass_eq_classMass :
    recMass D Ask Rec = classMass D.toPrior (univ.filter (fun T => ¬ Ask T ∧ Rec T)) := by
  rw [← baseMass_eq_classMass D (fun T => ¬ Ask T ∧ Rec T)]
  unfold recMass
  apply Finset.sum_congr rfl
  intro ω₀ _
  split_ifs <;> simp_all

/-- With a base-independent residual `r₀`, the residual term is the residual class's mass times
the residual's swing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma resTerm_const (r₀ : Bool → ℚ) :
    resTerm D Ask Rec (fun _ b => r₀ b) =
      classMass D.toPrior (univ.filter (fun T => ¬ Ask T ∧ ¬ Rec T)) * (r₀ true - r₀ false) := by
  rw [← baseMass_eq_classMass D (fun T => ¬ Ask T ∧ ¬ Rec T)]
  unfold resTerm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω₀ _
  split_ifs <;> simp_all

/-! ### The named models -/

/-- **`H_point`** (the pinned-Ask model, the program's §3.9 display): if the only Ask table of
positive mass is the observed `Q`, the unit Ask term is `μ(Ask)` itself (`δ_Q(Q) = 1`), so
`EU Q give − EU Q refuse = V · recTerm' − c · μ(Ask) + resTerm`. Pay iff
`V · recTerm' + resTerm > c · μ(Ask)`, i.e. `V·μ(Rec)·ρ̄^Rec > c·μ(Ask)` when the residual is
action-blind.
Source: [[bli-program]] §3.9 U5 (`100 μ(Rec) ρ > 10 μ(Ask)`); bli-soto-a-2-013 (`H_point`);
mandate T2(b)
Kind: C
Fidelity: exact
Hyps: (a) `HPoint` and `Ask Q` of the shipped prior (`(c)` when assumed of an arbitrary one),
positivity; does not use faith -/
theorem sist_hpoint (V c : ℚ)
    (hU : SistShaped D Ask Rec J Q (fun _ => c) (fun _ => V) r)
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false))
    (hpoint : HPoint D.toPrior Ask Q) (hQ : Ask Q) :
    D.toPrior.EU Q true - D.toPrior.EU Q false =
      V * recTerm D Ask Rec J Q (fun _ => 1) - c * askMass D Ask + resTerm D Ask Rec r := by
  rw [sist_identity_const D Ask Rec J Q r V c hU hg hr]
  have hask : askTerm D Ask Q (fun _ => 1) = askMass D Ask := by
    rw [askTerm_unit_eq_class, askMass_eq_classMass]
    unfold classMass
    apply Finset.sum_congr rfl
    intro T hT
    have hAT : Ask T := (Finset.mem_filter.mp hT).2
    by_cases hTQ : T = Q
    · subst hTQ
      have hppg : 0 < D.toPrior.ppMass T true := by rw [D.ppMass_toPrior]; exact hg
      have hppr : 0 < D.toPrior.ppMass T false := by rw [D.ppMass_toPrior]; exact hr
      rw [pointCorr_self D.toPrior T true false (by decide) hppg hppr, mul_one]
    · rw [hpoint T hAT hTQ, zero_mul]
  rw [hask]

/-- Under `HUnif` on the Ask class, the unit Ask term is the Ask mass.
Source: mandate §3.4 ("`ρ̄ = 1` under `H_unif`")
Kind: L
Fidelity: exact -/
lemma askTerm_unit_of_hUnif (hunif : HUnif D.toPrior Ask Q)
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false)) :
    askTerm D Ask Q (fun _ => 1) = askMass D Ask := by
  unfold askTerm askMass
  apply Finset.sum_congr rfl
  intro ω₀ _
  split_ifs with hA
  · have hppg : 0 < D.toPrior.ppMass Q true := by rw [D.ppMass_toPrior]; exact hg
    have hppr : 0 < D.toPrior.ppMass Q false := by rw [D.ppMass_toPrior]; exact hr
    rw [pointCorr_of_hUnif D.toPrior hunif hA true false (by decide) hppg hppr]
    ring
  · rfl

/-- Under `HUnif` on the Ask class and Omega simulating an Ask table, the unit Rec term is the
Rec mass.
Source: mandate §3.4
Kind: L
Fidelity: exact -/
lemma recTerm_unit_of_hUnif (hunif : HUnif D.toPrior Ask Q)
    (hJ : ∀ ω₀, Rec (D.state₀ ω₀) → Ask (J ω₀))
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false)) :
    recTerm D Ask Rec J Q (fun _ => 1) = recMass D Ask Rec := by
  unfold recTerm recMass
  apply Finset.sum_congr rfl
  intro ω₀ _
  split_ifs with hA hR
  · rfl
  · have hppg : 0 < D.toPrior.ppMass Q true := by rw [D.ppMass_toPrior]; exact hg
    have hppr : 0 < D.toPrior.ppMass Q false := by rw [D.ppMass_toPrior]; exact hr
    rw [pointCorr_of_hUnif D.toPrior hunif (hJ ω₀ hR) true false (by decide) hppg hppr]
    ring
  · rfl

/-- **`H_unif`** (the "100 % correlated picture"): with the policy a.s. constant on the Ask class
and Omega simulating an Ask table, `EU Q give − EU Q refuse = V·μ(Rec) − c·μ(Ask) + resTerm` —
the `//////` arithmetic with the residual carried. At `(49/100, 49/100)` and `(100, 10)` this is
`44.1 + resTerm`.
Source: bli-soto-a-077 / bli-soto-b-047 (`0.49·(−10) + 0.49·100 = 44.1`); bli-slides-034;
mandate T2(c)
Kind: C
Fidelity: exact
Hyps: (a) `HUnif` and the landing of `J` in the Ask class on the shipped prior (`(c)` when
assumed of an arbitrary one), positivity; does not use faith -/
theorem sist_hunif (V c : ℚ)
    (hU : SistShaped D Ask Rec J Q (fun _ => c) (fun _ => V) r)
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false))
    (hunif : HUnif D.toPrior Ask Q) (hJ : ∀ ω₀, Rec (D.state₀ ω₀) → Ask (J ω₀)) :
    D.toPrior.EU Q true - D.toPrior.EU Q false =
      V * recMass D Ask Rec - c * askMass D Ask + resTerm D Ask Rec r := by
  rw [sist_identity_const D Ask Rec J Q r V c hU hg hr,
    askTerm_unit_of_hUnif D Ask Q hunif hg hr, recTerm_unit_of_hUnif D Ask Rec J Q hunif hJ hg hr]

/-- The weight Omega's pick puts on a table from the Rec class: `μ₀(Rec ∧ J = T)`.
Source: bli-soto-b-2-006 (`P(J = j)`); mandate T2(a)
Kind: D
Fidelity: exact -/
def pickMass (T : ↥𝒟) : ℚ :=
  ∑ ω₀, if Ask (D.state₀ ω₀) then 0 else if Rec (D.state₀ ω₀) ∧ J ω₀ = T then D.μ₀ ω₀ else 0

/-- The unit Rec term as a sum over the tables Omega may pick: `∑_T pickMass T · δ_Q(T)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recTerm_unit_eq_pick :
    recTerm D Ask Rec J Q (fun _ => 1) =
      ∑ T, pickMass D Ask Rec J T * pointCorr D.toPrior Q T true false := by
  unfold recTerm pickMass
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases hA : Ask (D.state₀ ω₀)
  · simp [hA]
  · by_cases hR : Rec (D.state₀ ω₀)
    · simp only [hA, hR, if_false, true_and]
      rw [Finset.sum_eq_single (J ω₀)]
      · simp
      · intro T _ hT
        rw [if_neg (Ne.symm hT), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hA, hR]

/-- **The symmetric model** (bli-soto-b-2-006): if Omega's pick is distributed over the Ask tables
as the Ask class is (`μ₀(Rec ∧ J = T) · μ(Ask) = μ(state = T) · μ(Rec)` for every Ask table `T`,
and `J` lands in the Ask class), then with `ρ̄ := classProfile (Ask) Q` the verdict is
`EU Q give − EU Q refuse = (V·μ(Rec) − c·μ(Ask)) · ρ̄ + resTerm`: **the correlation changes the
magnitude only**.
Source: bli-soto-b-2-006 (the formula `(100 P(Rec) − 10 P(Ask)) · ∑_j P(J = j)·[…]`); journal
l. 291 ("giving up $10 in an ε-probable world to gain ε probability of $100"); mandate T2(a)
Kind: C
Fidelity: exact (the symmetry hypothesis is the model's defining tie between Omega's pick and the
Ask weights, stated exactly)
Hyps: (a) the symmetry tie and `J`'s landing on the shipped prior (`(c)` when assumed of an
arbitrary one), `0 < μ(Ask)`, positivity; does not use faith -/
theorem sist_symmetric (V c : ℚ)
    (hU : SistShaped D Ask Rec J Q (fun _ => c) (fun _ => V) r)
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false))
    (hJ : ∀ ω₀, Rec (D.state₀ ω₀) → Ask (J ω₀))
    (hsym : ∀ T, Ask T → pickMass D Ask Rec J T * askMass D Ask =
      D.toPrior.stateMass T * recMass D Ask Rec)
    (hAsk : 0 < askMass D Ask) :
    D.toPrior.EU Q true - D.toPrior.EU Q false =
      (V * recMass D Ask Rec - c * askMass D Ask) *
        classProfile D.toPrior (univ.filter Ask) Q true false + resTerm D Ask Rec r := by
  rw [sist_identity_const D Ask Rec J Q r V c hU hg hr]
  have hpick : ∀ T, ¬ Ask T → pickMass D Ask Rec J T = 0 := by
    intro T hT
    unfold pickMass
    apply Finset.sum_eq_zero
    intro ω₀ _
    split_ifs with hA hRJ
    · rfl
    · exact absurd (hRJ.2 ▸ hJ ω₀ hRJ.1) hT
    · rfl
  have hrec : recTerm D Ask Rec J Q (fun _ => 1) * askMass D Ask =
      askTerm D Ask Q (fun _ => 1) * recMass D Ask Rec := by
    rw [recTerm_unit_eq_pick, askTerm_unit_eq_class, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : Ask T
    · rw [if_pos hT]
      have := hsym T hT
      calc pickMass D Ask Rec J T * pointCorr D.toPrior Q T true false * askMass D Ask
          = (pickMass D Ask Rec J T * askMass D Ask) * pointCorr D.toPrior Q T true false := by
            ring
        _ = _ := by rw [this]; ring
    · rw [if_neg hT, hpick T hT]
      ring
  unfold classProfile
  rw [← askTerm_unit_eq_class, ← askMass_eq_classMass]
  have hne : askMass D Ask ≠ 0 := ne_of_gt hAsk
  have hrec' : recTerm D Ask Rec J Q (fun _ => 1) =
      askTerm D Ask Q (fun _ => 1) * recMass D Ask Rec / askMass D Ask := by
    rw [eq_div_iff hne]; exact hrec
  rw [hrec']
  field_simp

/-- **The sign corollary of the symmetric model**: with a positive profile `ρ̄ > 0` and an
action-blind residual, `give` is the one-step choice iff `V·μ(Rec) ≥ c·μ(Ask)`, and the strict
verdict `give` iff `V·μ(Rec) > c·μ(Ask)` — the correlation never flips the sign.
Source: bli-soto-b-2-006 ("the verdict does not depend on how correlated the decisions are, only
its magnitude does"); mandate T2(a) corollary
Kind: C
Fidelity: exact
Hyps: (a) as `sist_symmetric`, `0 < ρ̄`, `resTerm = 0`; does not use faith -/
theorem sist_sign_symmetric (V c : ℚ)
    (hU : SistShaped D Ask Rec J Q (fun _ => c) (fun _ => V) r)
    (hg : 0 < massOf D.ν (fun π => π Q = true)) (hr : 0 < massOf D.ν (fun π => π Q = false))
    (hJ : ∀ ω₀, Rec (D.state₀ ω₀) → Ask (J ω₀))
    (hsym : ∀ T, Ask T → pickMass D Ask Rec J T * askMass D Ask =
      D.toPrior.stateMass T * recMass D Ask Rec)
    (hAsk : 0 < askMass D Ask)
    (hρ : 0 < classProfile D.toPrior (univ.filter Ask) Q true false)
    (hres : resTerm D Ask Rec r = 0) :
    (D.toPrior.IsOneStepChoice Q true ↔ c * askMass D Ask ≤ V * recMass D Ask Rec) ∧
      (D.toPrior.EU Q false < D.toPrior.EU Q true ↔ c * askMass D Ask < V * recMass D Ask Rec) := by
  have hid := sist_symmetric D Ask Rec J Q r V c hU hg hr hJ hsym hAsk
  rw [hres, add_zero] at hid
  constructor
  · unfold FiniteBLIPrior.IsOneStepChoice
    constructor
    · intro h
      have := h false
      rw [← sub_nonneg, hid] at this
      have := (mul_nonneg_iff_of_pos_right hρ).mp this
      linarith
    · intro h b
      cases b
      · rw [← sub_nonneg, hid]
        apply mul_nonneg _ (le_of_lt hρ)
        linarith
      · exact le_rfl
  · rw [← sub_pos, hid, mul_pos_iff_of_pos_right hρ]
    constructor <;> intro h <;> linarith

end Sist

end Cleanroom.Bli.UdtBliSist
