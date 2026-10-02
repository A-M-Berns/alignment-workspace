import Cleanroom.Decision.DpFirstpersonSc.ShadowFactor
import Cleanroom.Decision.DpFirstpersonSc.WitnessesLift
import Cleanroom.Decision.DpCalibration.Limit

/-!
# T13(a): the two limit-grade audits (dp-cf-150; FP-21′(ii))

Two candidate limit-grade audits of a base state `s` at `d` on the stamped problem, and which one
is the audit of record (continuation 2):

* **`LimitAuditPassAt`** (the mandate's `AuditLimitPrior`): Definition 10's algebraic limit
  applied to the occurrence evidence — `P_s(X) = lim_{ε→0⁺} ν_{stamp,C^ε}(λ ∈ X | occ(d))`
  (`limitCond` on the stamped problem, trailing-coefficient quotients of
  `nuPoly C (stamp U B)`), with the cross-multiplied `V`-clause, exactly as `dp-calibration`'s
  `LimitOCAt` reads an observation. The tremble polynomials transport along the stamping
  (`leafLawPoly_relabel`, `nuPoly_stamp_eq_sum`, `payPoly_stamp_eq_sum`), so when `occ(d)` is
  exactly a base event `λ⁻¹O` the limit audit at `d` **is** `LimitOCAt` at `O`
  (`limitAudit_iff_limitOCAt_of_occ_eq`), and when `μ_C(occ(d)) > 0` its `P`-clause is the
  strict audit's `P`-clause (`limitAudit_P_iff_strict_of_pos`): the limit grade is nested with
  the strict grade at a positive occurrence mass.
* **`AuditLimitOfEps`** (the mandate's second candidate, read literally: for every small `ε`,
  the strict audit against `priorState (tremble C ε) (stamp U B)` passes **exactly**). On
  Told-You-So at `d₁₀` under `procTake5` it passes **no** base state at all
  (`tys_take5_auditLimitOfEps_empty`): the per-`ε` referent is `(ε/2, 1 − ε/2)` on
  `((10,10), (10,5))`, which no fixed state matches at two values of `ε`. So the literal
  per-`ε` audit is a uniform-in-`ε` condition, not a limit; the mandate's "the limit of
  `ε`-audits passes `δ_{(10,5)}`" is `LimitAuditPassAt`'s verdict
  (`tys_take5_limitAudit_105`), and that is the audit of record (findings, report §T13).
* **The separation at a null observation** (`tys_take5_limit_separation`): the limit audit
  passes `δ_{(10,5)}` at `d₁₀` while the strict a.c. grade (`tys_take5_limit_not_ac`) rejects it;
  the grades are not nested where `μ_C(occ(d)) = 0`. And the limit audit, like `LimitOCAt`,
  factors through no strict shadow (`limitAudit_not_shadow_functional`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Cleanroom.Udt.UdtSupercondition
open Finset

section transport

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- The tremble polynomial of a leaf is unchanged by re-worlding (the path product reads only
the nodes). Source: none: infrastructure. Kind: L -/
theorem leafLawPoly_relabel {W : Type} (C : Proc ι acts K) :
    (T : Tree Ω ι acts K) → (f : T.Leaves → W) → ∀ ℓ',
      leafLawPoly C (relabel T f) ℓ' = leafLawPoly C T (relabelLeaves T f ℓ')
  | .leaf _ _, _, _ => rfl
  | .chance _ β child, f, ⟨i, ℓ'⟩ => by
      show Polynomial.C (β.w i) * leafLawPoly C (relabel (child i) _) ℓ' =
        Polynomial.C (β.w i) * leafLawPoly C (child i) _
      rw [leafLawPoly_relabel C (child i) (fun ℓ => f ⟨i, ℓ⟩) ℓ']
  | .decision d child, f, ⟨a, ℓ'⟩ => by
      show trembleW C d a * leafLawPoly C (relabel (child a) _) ℓ' =
        trembleW C d a * leafLawPoly C (child a) _
      rw [leafLawPoly_relabel C (child a) (fun ℓ => f ⟨a, ℓ⟩) ℓ']

variable (U : Finset ι) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- The tremble polynomial on the stamped problem. Source: none: infrastructure. Kind: L -/
theorem leafLawPoly_stamp (ℓ' : (stamp U B).Leaves) :
    leafLawPoly C (stamp U B) ℓ' = leafLawPoly C B (stampLeaves U B ℓ') :=
  leafLawPoly_relabel C B (stampWorld U B) ℓ'

/-- `nuPoly` on the stamped problem as a sum over the base leaves.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_stamp_eq_sum (Y : Finset (SW Ω acts U)) :
    nuPoly C (stamp U B) Y = ∑ ℓ, if stampWorld U B ℓ ∈ Y then leafLawPoly C B ℓ else 0 := by
  unfold nuPoly worldEv
  rw [Finset.sum_filter]
  exact Fintype.sum_equiv (stampLeaves U B) _ _ fun ℓ' => by rw [world_stamp, leafLawPoly_stamp]

/-- `payPoly` on the stamped problem as a sum over the base leaves.
Source: none: infrastructure. Kind: L -/
theorem payPoly_stamp_eq_sum (Y : Finset (SW Ω acts U)) :
    payPoly C (stamp U B) Y =
      ∑ ℓ, if stampWorld U B ℓ ∈ Y then leafLawPoly C B ℓ * Polynomial.C (payoff B ℓ) else 0 := by
  unfold payPoly worldEv
  rw [Finset.sum_filter]
  exact Fintype.sum_equiv (stampLeaves U B) _ _ fun ℓ' => by
    rw [world_stamp, leafLawPoly_stamp, payoff_stamp]

variable {d : ι} (hd : d ∈ U) {O : Finset Ω}

/-- When `occ(d) = λ⁻¹O` exactly, the stamped occurrence polynomial is `nuPoly O`.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_stamp_occW (hocc : occ d B = worldEv B O) :
    nuPoly C (stamp U B) (occW U hd) = nuPoly C B O := by
  rw [nuPoly_stamp_eq_sum]
  unfold nuPoly worldEv
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [stampWorld_mem_occW, hocc, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]

/-- When `occ(d) = λ⁻¹O` exactly, the stamped polynomial of `X ∧ occ(d)` is `nuPoly (X ∩ O)`.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_stamp_obsW_inter_occW (hocc : occ d B = worldEv B O) (X : Finset Ω) :
    nuPoly C (stamp U B) (obsW U X ∩ occW U hd) = nuPoly C B (X ∩ O) := by
  rw [nuPoly_stamp_eq_sum]
  unfold nuPoly worldEv
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Finset.mem_inter, stampWorld_mem_obsW, stampWorld_mem_occW, hocc, worldEv,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- The payoff version of `nuPoly_stamp_obsW_inter_occW`. Source: none: infrastructure.
Kind: L -/
theorem payPoly_stamp_obsW_inter_occW (hocc : occ d B = worldEv B O) (X : Finset Ω) :
    payPoly C (stamp U B) (obsW U X ∩ occW U hd) = payPoly C B (X ∩ O) := by
  rw [payPoly_stamp_eq_sum]
  unfold payPoly worldEv
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Finset.mem_inter, stampWorld_mem_obsW, stampWorld_mem_occW, hocc, worldEv,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- When `occ(d) = λ⁻¹O` exactly, the limiting occurrence conditional is Definition 10's
limiting conditional on `O`. Source: none: infrastructure. Kind: L -/
theorem limitCond_stamp_eq (hocc : occ d B = worldEv B O) (X : Finset Ω) :
    limitCond C (stamp U B) (obsW U X) (occW U hd) = limitCond C B X O := by
  unfold limitCond
  rw [nuPoly_stamp_obsW_inter_occW U C B hd hocc X, nuPoly_stamp_occW U C B hd hocc]

end transport

/-! ## The two limit-grade audits -/

section defs

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (U : Finset ι) {d : ι} (hd : d ∈ U)

/-- **The limit-grade audit of record** (the mandate's `AuditLimitPrior`): the base state `s`
passes at `d` iff, when `occ(d)` is tremble-realizable (`nuPoly (stamp) occ(d) ≠ 0`), (1)
`P_s(X) = lim_{ε→0⁺} ν_{stamp,C^ε}(λ ∈ X | occ(d))` for every `X` (the algebraic limit
`limitCond` of `dp-calibration`, trailing-coefficient quotients on the stamped problem) and (2)
for every `X` of positive limiting conditional probability, `V_s(X)` is the limiting
conditional expectation, cross-multiplied against the positive trailing coefficient — exactly
`LimitOCAt`'s shape with the observation replaced by the occurrence event. Vacuous (true for every
state) when `occ(d)` is tremble-null — no `d`-node in the tree, *or* every `d`-node behind a
zero-mass chance branch, since trembles perturb the procedure and not the chance nodes (audit r2
adversarial N2, probe `audit-r2-probes/LimitAuditVacuous.lean`: `deadTree` queries `d` behind a
`pure 0` coin and every base state passes) — as `LimitOCAt` is at a tremble-null observation. No
limit-grade headline sits at a tremble-null `occ(d)`.
Source: mandate T13(a) (`AuditLimitPrior`); `firstperson.md` FP-21′(ii); [[decision-problems-v2]]
Definition 10
Kind: D
Fidelity: variant: limit taken algebraically by lowest-order coefficients (as `LimitOCAt`);
`V`-clause cross-multiplied -/
def LimitAuditPassAt (s : State Ω K) : Prop :=
  nuPoly C (stamp U B) (occW U hd) ≠ 0 →
    (∀ X, s.pr X = limitCond C (stamp U B) (obsW U X) (occW U hd)) ∧
    (∀ X, 0 < limitCond C (stamp U B) (obsW U X) (occW U hd) →
      s.V X * (nuPoly C (stamp U B) (obsW U X ∩ occW U hd)).coeff
          (nuPoly C (stamp U B) (obsW U X ∩ occW U hd)).natTrailingDegree =
        (payPoly C (stamp U B) (obsW U X ∩ occW U hd)).coeff
          (nuPoly C (stamp U B) (obsW U X ∩ occW U hd)).natTrailingDegree)

/-- **The per-`ε` audit** (the mandate's `AuditLimitOfEps`, read literally): for every
sufficiently small positive `ε`, the strict audit against the trembled prior
`priorState (tremble C ε) (stamp U B)` passes exactly. A uniform-in-`ε` condition, not a limit:
see `tys_take5_auditLimitOfEps_empty`.
Source: mandate T13(a) (`AuditLimitOfEps`: "`∀ ε small, AuditPassAt (priorState (tremble C ε))
…`")
Kind: D
Fidelity: exact (the mandate's formula, as written) -/
def AuditLimitOfEps (π : SW Ω acts U → Ω) (s : State Ω K) : Prop :=
  ∃ ε₀ : K, 0 < ε₀ ∧ ∀ (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1), 0 < ε → ε < ε₀ →
    ∃ h : 0 < (priorState (tremble C ε h0 h1) (stamp U B)).pr (occW U hd),
      AuditPassAt (priorState (tremble C ε h0 h1) (stamp U B)) (occW U hd) h π s

/-- **When `occ(d)` is exactly a base event `λ⁻¹O`, the limit-grade audit at `d` is
Definition 10's limit calibration at `O`**: `LimitOCAt` with the state `s` and observation `O`.
On Told-You-So at `d₁₀` (`tys_occ_ten_eq`) this makes `dp-calibration`'s Lemma 2 computations
the limit-grade audit verdicts.
Source: mandate T13(a); `firstperson.md` FP-22′ (the exact license)
Kind: C
Fidelity: exact
Hyps: (a) `occ d B = worldEv B O` -/
theorem limitAudit_iff_limitOCAt_of_occ_eq {O : Finset Ω} (hocc : occ d B = worldEv B O)
    (s : State Ω K) :
    LimitAuditPassAt C B U hd s ↔ LimitOCAt (fun _ => s) (fun _ => O) C B d := by
  unfold LimitAuditPassAt LimitOCAt
  simp only [limitCond_stamp_eq U C B hd hocc, nuPoly_stamp_occW U C B hd hocc,
    nuPoly_stamp_obsW_inter_occW U C B hd hocc, payPoly_stamp_obsW_inter_occW U C B hd hocc]

/-- **At a positive occurrence mass the limit audit's `P`-clause is the strict audit's**: when
`μ_C(occ(d)) > 0`, `limitCond` is the plain conditional (`limitCond_eq_of_pos`), so clause (1)
of `LimitAuditPassAt` is `P_s = (π_* ŝ).P` with `ŝ` the strict referent — the limit grade is
nested with the strict grade off the null observations.
Source: mandate T13(a) ("nested with the strict and masked grades at `ν_C(O_d) > 0`"); report
§T13
Kind: P
Fidelity: exact (`P`-clause; the `V`-clauses differ in form — cross-multiplied against the
trailing coefficient versus guarded — and are not compared here)
Hyps: (a) `0 < μ(occ(d))` -/
theorem limitAudit_P_iff_strict_of_pos (h : 0 < (priorState C (stamp U B)).pr (occW U hd))
    (s : State Ω K) :
    (∀ X, s.pr X = limitCond C (stamp U B) (obsW U X) (occW U hd)) ↔
      s.P = (pushState Prod.fst (auditRef (priorState C (stamp U B)) (occW U hd) h)).P := by
  have hpos : 0 < nu C (stamp U B) (occW U hd) := by rwa [priorState_pr] at h
  have hX : ∀ X, (pushState Prod.fst (auditRef (priorState C (stamp U B)) (occW U hd) h)).pr X =
      limitCond C (stamp U B) (obsW U X) (occW U hd) := by
    intro X
    rw [pushState_pr, preEv_fst_eq_obsW, auditRef, jeffreyCond_pr, priorState_pr, priorState_pr,
      limitCond_eq_of_pos C (stamp U B) (obsW U X) (occW U hd) hpos]
  constructor
  · intro hP
    ext ω
    have := hP {ω}
    rw [← hX {ω}] at this
    simpa [State.pr, probOf_singleton] using this
  · intro hP X
    rw [← hX X]
    show probOf s.P X = probOf _ X
    rw [hP]

end defs

/-! ## Told-You-So at `d₁₀`: the two audits, the separation, the shadow -/

section tys

/-- `d₁₀ ∈ {d₁₀}`. Source: none: infrastructure. Kind: L -/
theorem tys_ten_mem : (Five10.ten : Five10) ∈ ({Five10.ten} : Finset Five10) :=
  Finset.mem_singleton_self _

/-- **The limit-grade audit passes `δ_{(10,5)}` at `d₁₀` under take-5** — the mandate's "the
limit of `ε`-audits passes `δ_{(10,5)}`": `occ(d₁₀) = λ⁻¹O₁₀`, and the state certain of `(10,5)`
is limit-calibrated there (`dp-calibration`'s `tys_take5_limitOC_at_ten_of_certain_105`).
Source: mandate T13(a) ("the limit of `ε`-audits passes `δ_(10,5)`")
Kind: N+
Fidelity: exact -/
theorem tys_take5_limitAudit_105 :
    LimitAuditPassAt procTake5 toldYouSo {Five10.ten} tys_ten_mem
      (State.dirac ((Five10.ten, Five10.five) : TysW) 5) := by
  rw [limitAudit_iff_limitOCAt_of_occ_eq _ _ _ _ tys_occ_ten_eq]
  exact tys_take5_limitOC_at_ten_of_certain_105

/-- **The limit-grade audit fails `s₁₀ = δ_{(10,10)}` at `d₁₀` under take-5** (Lemma 2's
separation as an audit verdict). Source: [[decision-problems-v2]] §3.1 Lemma 2; mandate T13(a).
Kind: N+ -/
theorem tys_take5_limitAudit_not_1010 :
    ¬ LimitAuditPassAt procTake5 toldYouSo {Five10.ten} tys_ten_mem (tysState .ten) := by
  rw [limitAudit_iff_limitOCAt_of_occ_eq _ _ _ _ tys_occ_ten_eq]
  exact tys_take5_strict_not_limit.2

/-- **The limit-grade audit passes `s₁₀` at `d₁₀` under `C₀ = (five, ten)`** (Proposition 8's
limit clause as an audit verdict). Source: [[decision-problems-v2]] §7.1 Proposition 8. Kind: N+ -/
theorem tys_fiveTen_limitAudit_1010 :
    LimitAuditPassAt procFiveTen toldYouSo {Five10.ten} tys_ten_mem (tysState .ten) := by
  rw [limitAudit_iff_limitOCAt_of_occ_eq _ _ _ _ tys_occ_ten_eq]
  exact tys_fiveTen_limitOC .ten (tys_queried .ten)

/-- **The separation at a null observation** (T13(a), N+): at `d₁₀` under take-5
(`μ_C(occ(d₁₀)) = 0`) the limit-grade audit passes `δ_{(10,5)}` while the strict a.c. grade —
no same-ontology model from `ν_C = δ_{(5,5)}` reaches it — rejects it: the grades are not nested
at a null observation.
Source: mandate T13(a) ("while a.c. against `ν_C` rejects it — the grades are not nested at a
null observation")
Kind: N+
Fidelity: exact -/
theorem tys_take5_limit_separation :
    LimitAuditPassAt procTake5 toldYouSo {Five10.ten} tys_ten_mem
      (State.dirac ((Five10.ten, Five10.five) : TysW) 5) ∧
    ¬ Nonempty (SameOntologyModel (toPMF (priorState procTake5 toldYouSo).P)
      (toPMF (State.dirac ((Five10.ten, Five10.five) : TysW) (5 : ℚ)).P)) :=
  ⟨tys_take5_limitAudit_105, tys_take5_limit_not_ac⟩

/-- **The limit-grade audit factors through no strict shadow** (the extension of record, limit
clause, for the audit of record): same strict shadow, opposite limit-audit verdicts on `s₁₀`.
Source: mandate "Extension of record" ("neither limit grade factors through any shadow")
Kind: N+
Fidelity: exact -/
theorem limitAudit_not_shadow_functional :
    shadow procTake5 toldYouSo = shadow procFiveTen toldYouSo ∧
    LimitAuditPassAt procFiveTen toldYouSo {Five10.ten} tys_ten_mem (tysState .ten) ∧
    ¬ LimitAuditPassAt procTake5 toldYouSo {Five10.ten} tys_ten_mem (tysState .ten) :=
  ⟨tys_take5_fiveTen_shadow_eq, tys_fiveTen_limitAudit_1010, tys_take5_limitAudit_not_1010⟩

set_option maxHeartbeats 1000000 in
/-- **The limit-grade audit factors through the stamped strict shadow no more than through the
base one** (repair round 2, audit r2 fidelity N4): `procTake5` and `procFiveTen` have the same
shadow on the *stamped* Told-You-So `stamp {d₁₀} toldYouSo` (`tys_take5_fiveTen_stamp_shadow_eq`,
both `δ_{((5,5), pol = ⊥, 5)}`), yet opposite limit-audit verdicts on `s₁₀` at `d₁₀`. With
`audit_stamped_shadow_functional` (the strict grade *is* a functional of the stamped shadow), this
is the exact statement of the extension of record: the strict and masked-local grades are
decidable from the stamped run law, the limit grade from neither strict run law.
Source: mandate "Extension of record" ("neither limit grade factors through any shadow"); audit
r2 fidelity N4
Kind: N+
Fidelity: exact -/
theorem limitAudit_not_stamped_shadow_functional :
    shadow procTake5 (stamp {Five10.ten} toldYouSo) =
      shadow procFiveTen (stamp {Five10.ten} toldYouSo) ∧
    LimitAuditPassAt procFiveTen toldYouSo {Five10.ten} tys_ten_mem (tysState .ten) ∧
    ¬ LimitAuditPassAt procTake5 toldYouSo {Five10.ten} tys_ten_mem (tysState .ten) :=
  ⟨tys_take5_fiveTen_stamp_shadow_eq, tys_fiveTen_limitAudit_1010, tys_take5_limitAudit_not_1010⟩

/-- The per-`ε` referent's probability of `(10,10)` at `d₁₀` under `procTake5^ε` is `ε/2`:
per-run clause 1 at `X = {(10,10)}` reads `P_s(X) · (ε/2) = (ε/2)²`.
Source: mandate T13(a) ("per-run SSC under `C^ε` is `(ε/2, 1 − ε/2)`")
Kind: L -/
theorem tys_take5_eps_referent (s : State TysW ℚ) (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hpos : 0 < ε)
    (hc : PerRunClause1At (fun _ => s) (tremble procTake5 ε h0 h1) toldYouSo .ten) :
    s.pr {(Five10.ten, Five10.ten)} = ε / 2 := by
  have h := hc {(Five10.ten, Five10.ten)}
  rw [tys_mass_occ_ten, tys_occ_ten_eq] at h
  have hinter : worldEv toldYouSo {(Five10.ten, Five10.ten)} ∩ worldEv toldYouSo (tysObs .ten) =
      worldEv toldYouSo ({(Five10.ten, Five10.ten)} ∩ tysObs .ten) := by
    ext ℓ; simp [worldEv]
  rw [hinter] at h
  change _ = nu (tremble procTake5 ε h0 h1) toldYouSo _ at h
  rw [tys_nu] at h
  simp only [tremble_w, procTake5, Proc.ofFun_w, five10_card] at h
  simp [tysObs] at h
  field_simp at h
  simp only [State.pr, probOf_singleton]
  rcases h with h | h
  · linarith
  · exact absurd h hpos.ne'

/-- **The literal per-`ε` audit is empty at `d₁₀` under take-5**: no base state passes the
strict audit against `priorState (tremble procTake5 ε) (stamp …)` for all small `ε`, because the
referent's probability of `(10,10)` is `ε/2`, which no fixed state matches at two values of
`ε`. So `AuditLimitOfEps` is not a limit-grade audit but a uniform-in-`ε` one, and the
mandate's "the limit of `ε`-audits passes `δ_{(10,5)}`" is `LimitAuditPassAt`'s verdict
(`tys_take5_limitAudit_105`), the audit of record.
Source: mandate T13(a) (the second candidate); findings F-T13
Kind: N+ (a refutation of the literal reading)
Fidelity: exact -/
theorem tys_take5_auditLimitOfEps_empty (s : State TysW ℚ) :
    ¬ AuditLimitOfEps procTake5 toldYouSo {Five10.ten} tys_ten_mem Prod.fst s := by
  rintro ⟨ε₀, hε₀, hall⟩
  have key : ∀ (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1), 0 < ε → ε < ε₀ →
      s.pr {(Five10.ten, Five10.ten)} = ε / 2 := by
    intro ε h0 h1 hpos hlt
    obtain ⟨h, hpass⟩ := hall ε h0 h1 hpos hlt
    exact tys_take5_eps_referent s ε h0 h1 hpos
      ((audit_iff_perRunClausesAt _ toldYouSo {Five10.ten} tys_ten_mem (fun _ => s) h).mp
        hpass).1
  set ε₁ : ℚ := min ε₀ 1 / 2 with hε₁
  have hε₁pos : 0 < ε₁ := by rw [hε₁]; positivity
  have hε₁le : ε₁ ≤ 1 := by
    rw [hε₁]; have := min_le_right ε₀ 1; linarith
  have hε₁lt : ε₁ < ε₀ := by
    rw [hε₁]; have := min_le_left ε₀ 1; linarith
  have e1 := key ε₁ hε₁pos.le hε₁le hε₁pos hε₁lt
  have e2 := key (ε₁ / 2) (by positivity) (by linarith) (by positivity) (by linarith)
  rw [e1] at e2
  linarith

end tys

end Cleanroom.Decision.DpFirstpersonSc
