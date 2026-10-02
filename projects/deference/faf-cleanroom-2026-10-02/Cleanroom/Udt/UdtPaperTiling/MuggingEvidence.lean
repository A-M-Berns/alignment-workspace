import Cleanroom.Bli.UdtBliCore.Product
import Cleanroom.Bli.UdtBliCore.Bridges
import Cleanroom.Bli.UdtBliCore.Updateful
import Cleanroom.Bli.UdtBliCore.Good
import Cleanroom.Bli.UdtBliCore.Mugging

/-!
# `udt-paper-tiling` · MuggingEvidence: Counterfactual Mugging with Evidence, Versions A and B (T13)

The paper's variant (`main.tex` 295–315, bli-paper-020): Omega's coin has a bias drawn uniformly
from `{0, 1/2, 1}`, the agent sees three demonstration flips, then the official flip `h`. The
**evidence state is the table**: the agent's day-`m` belief state is its posterior on `heads`,
`T_e(heads) = P(h | e)`, so `faith` holds by construction from the joint law — the honest reason
the belief state *is* the observation. The evidence classes are `lo` (no heads among three:
posterior `1/18`), `mid` (one or two heads: posterior `1/2`, merged because the policy is a
function of the belief state), `hi` (three heads: `17/18`), with prior masses `3/8, 1/4, 3/8`.
Actions are `Bool` (`true` = pay). The prior is `udt-bli-core`'s independent-policy construction
`IndepData.toPrior` with the uniform law on the eight policies.

* **Version A** (`VerA`): Omega's counterfactual reads the same evidence, `U_A = −10·[pay at
  e]·[h] + 100·[¬h]·[pay at e]`. The prior is `Reflective`, `ReflectivePolicy`, `LocalUtility`,
  `IndependentPointsGivenState`, hence **`NoCrossBranch`** (`udt-bli-core`'s
  `noCrossBranch_of_localUtility_indepGivenState`), and `udt-bli-core`'s `oneStep_iff_updateful`
  and `priorOptimal_iff_updateful_on_support` apply: the UDT 1.1 optimum is the updateful policy,
  which pays at `e` iff `P(h | e) ≤ 10/11` — exactly: `homeEU e pay = 100 − 110·P(h | e)`, so pay
  at `lo` and `mid` (`1690/18 > 0`, `45 > 0`) and refuse at `hi` (`−70/18 < 0`). The optimum is
  unique (`versionA`).
* **Version B** (`VerB`): Omega pays `100` with the *total* probability of paying,
  `U_B = −10·[pay at e]·[h] + 100·[¬h]·∑_{e'} P(e')·[pay at e']`. The ex-ante value of a policy is
  `∑_e P(e)·(50 − 10·P(h | e))·[pay at e]` (the coefficient is positive because the average bias
  is `1/2`, `P(¬h) = 1/2`), so the constant-pay policy is the unique prior-optimal policy
  (`versionB_optimal`); **`NoCrossBranch` fails** (`versionB_not_noCrossBranch`:
  `𝔼[U | state = lo ∧ pay at hi] ≠ 𝔼[U | state = lo ∧ refuse at hi]`); and the updateful rule
  refuses at `hi` (`versionB_updateful_refuses_hi`).
* The paper's moral — "UDT 1.1 behaves updatefully exactly when Omega's counterfactual does" — is
  the pair `NoCrossBranch (A)`, `¬ NoCrossBranch (B)` plus the imported lemma (`moral`, Kind L).
  bli-paper-021 (branch decomposition, "behaves updatefully") is imported, not re-proved:
  `EU_eq_sum_branch`, `EU_eq_sum_partition`, `oneStep_iff_updateful`, `eps_updateful`.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

namespace MugEv

/-- The posteriors `P(h | e)`: `1/18`, `1/2`, `17/18`.
Source: `main.tex` 299–305 (bli-paper-020); mandate T13 (verified grid)
Kind: D
Fidelity: exact (the three merged evidence classes) -/
def post : Fin 3 → ℚ
  | 0 => 1 / 18
  | 1 => 1 / 2
  | 2 => 17 / 18

/-- The prior masses of the evidence classes: `3/8`, `1/4`, `3/8`.
Source: mandate T13 (verified grid)
Kind: D
Fidelity: exact -/
def pE : Fin 3 → ℚ
  | 0 => 3 / 8
  | 1 => 1 / 4
  | 2 => 3 / 8

/-- The base law on `(e, h)`: `P(e) · P(h | e)`.
Source: mandate T13
Kind: D
Fidelity: exact -/
def μ₀ (ω : Fin 3 × Bool) : ℚ := pE ω.1 * (if ω.2 then post ω.1 else 1 - post ω.1)

/-- **The evidence table** of class `e`: price `P(h | e)` on `heads = p`, `0` elsewhere.
Source: mandate T13 ("the evidence state as the table")
Kind: D
Fidelity: exact -/
def tbl (e : Fin 3) : Table witIndex 1 := fun φ => if φ.1 = pW then post e else 0

/-- The tables are distinct. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma tbl_inj {e e' : Fin 3} (h : tbl e = tbl e') : e = e' := by
  have := congrFun h ⟨pW, pW_mem_S1⟩
  simp only [tbl, if_true] at this
  revert this
  match e, e' with
  | 0, 0 | 1, 1 | 2, 2 => intro _; rfl
  | 0, 1 | 0, 2 | 1, 0 | 1, 2 | 2, 0 | 2, 1 => intro h; norm_num [post] at h

/-- The carrier of evidence tables. Source: mandate T13. Kind: D. Fidelity: n/a -/
def evTables : Finset (Table witIndex 1) := {tbl 0, tbl 1, tbl 2}

/-- `tbl e ∈ evTables`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma tbl_mem (e : Fin 3) : tbl e ∈ evTables := by
  match e with
  | 0 => simp [evTables]
  | 1 => simp [evTables]
  | 2 => simp [evTables]

/-- The evidence table as an element of the carrier. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def ev (e : Fin 3) : ↥evTables := ⟨tbl e, tbl_mem e⟩

/-- `ev` is injective. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma ev_inj {e e' : Fin 3} : ev e = ev e' ↔ e = e' :=
  ⟨fun h => tbl_inj (congrArg Subtype.val h), fun h => h ▸ rfl⟩

/-- The underlying table of `ev e`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma ev_val (e : Fin 3) : (ev e).1 = tbl e := rfl

/-- `tbl e = tbl e' ↔ e = e'`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma tbl_eq_iff {e e' : Fin 3} : tbl e = tbl e' ↔ e = e' := ⟨tbl_inj, fun h => h ▸ rfl⟩

/-- `(0 : Fin 3) ≠ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f01 : (0 : Fin 3) ≠ 1 := by decide
/-- `(0 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f02 : (0 : Fin 3) ≠ 2 := by decide
/-- `(1 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f12 : (1 : Fin 3) ≠ 2 := by decide

/-- Every table of the carrier is some `ev e`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eq_ev (T : ↥evTables) : ∃ e, T = ev e := by
  rcases T with ⟨T, hT⟩
  simp only [evTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- The inverse of `ev`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def evInv (T : ↥evTables) : Fin 3 := if T = ev 0 then 0 else if T = ev 1 then 1 else 2

/-- `evInv (ev e) = e`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma evInv_ev (e : Fin 3) : evInv (ev e) = e := by
  match e with
  | 0 => simp [evInv]
  | 1 => simp [evInv]
  | 2 => simp [evInv]

/-- `ev (evInv T) = T`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ev_evInv (T : ↥evTables) : ev (evInv T) = T := by
  obtain ⟨e, rfl⟩ := eq_ev T
  rw [evInv_ev]

/-- `Fin 3 ≃ evTables`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def evEquiv : Fin 3 ≃ ↥evTables where
  toFun := ev
  invFun := evInv
  left_inv := evInv_ev
  right_inv := ev_evInv

/-- The carrier has three elements. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma card_evTables : Fintype.card ↥evTables = 3 := by
  rw [← Fintype.card_congr evEquiv]
  simp

/-- A policy on the evidence tables from a triple of actions.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def polOf (p : Bool × Bool × Bool) : Policy evTables Bool :=
  fun T => if T = ev 0 then p.1 else if T = ev 1 then p.2.1 else p.2.2

/-- `polOf p (ev e)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma polOf_ev (p : Bool × Bool × Bool) (e : Fin 3) :
    polOf p (ev e) = (match e with | 0 => p.1 | 1 => p.2.1 | 2 => p.2.2) := by
  match e with
  | 0 => simp [polOf]
  | 1 => simp [polOf]
  | 2 => simp [polOf]

/-- The eight policies as triples. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def polEquiv : (Bool × Bool × Bool) ≃ Policy evTables Bool where
  toFun := polOf
  invFun := fun π => (π (ev 0), π (ev 1), π (ev 2))
  left_inv := fun p => by rcases p with ⟨a, b, c⟩; simp
  right_inv := fun π => by
    funext T
    obtain ⟨e, rfl⟩ := eq_ev T
    match e with
    | 0 => simp
    | 1 => simp
    | 2 => simp

/-- Sums over policies expand over the eight triples.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_pol {M : Type} [AddCommMonoid M] (f : Policy evTables Bool → M) :
    ∑ π, f π = ∑ p : Bool × Bool × Bool, f (polOf p) :=
  (polEquiv.sum_comp f).symm

/-- The uniform policy law `1/8` is the product law with `1/2` per point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniform_eq_prodLaw : (fun _ : Policy evTables Bool => (1 / 8 : ℚ)) =
    prodLaw (fun (_ : ↥evTables) (_ : Bool) => (1 / 2 : ℚ)) := by
  funext π
  unfold prodLaw
  rw [Finset.prod_const, Finset.card_univ, card_evTables]
  norm_num

/-- The small truths of a world: `heads` is `h`, `q` is false.
Source: mandate T13
Kind: D
Fidelity: n/a -/
def small₀ (ω : Fin 3 × Bool) (φ : ↥(witIndex.S 1)) : Bool := if φ.1 = pW then ω.2 else false

/-- Every day-1 sentence is `p` or `q`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sentence_cases (φ : ↥(witIndex.S 1)) : φ.1 = pW ∨ φ.1 = qW := by
  have h : φ.1 ∈ ({pW, qW} : Finset _) := φ.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  exact h

/-- **Faith of the base law**: within `state = ev e`, the frequency of `heads` is the table's
price `P(h | e)` — true by construction of the posterior tables.
Source: mandate T13 ("faith holds by construction from the joint law")
Kind: L
Fidelity: exact -/
lemma faith₀ : ∀ (T : ↥evTables) (φ : ↥(witIndex.S 1)),
    integralOf μ₀ (fun ω => ind (small₀ ω φ)) (fun ω => ev ω.1 = T) =
      T.1 φ * massOf μ₀ (fun ω => ev ω.1 = T) := by
  intro T φ
  obtain ⟨e, rfl⟩ := eq_ev T
  rcases sentence_cases φ with hφ | hφ
  · simp only [integralOf, massOf, small₀, hφ, if_true, ev_inj, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fintype.sum_bool, ev_val, tbl, μ₀]
    match e with
    | 0 => simp [post, pE, ind] <;> norm_num
    | 1 => simp [post, pE, ind] <;> norm_num
    | 2 => simp [post, pE, ind] <;> norm_num
  · have hq : φ.1 ≠ pW := by rw [hφ]; exact pW_ne_qW.symm
    simp only [integralOf, massOf, small₀, hq, if_false, ev_inj, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fintype.sum_bool, ev_val, tbl, μ₀]
    match e with
    | 0 => simp [post, pE, ind] <;> norm_num
    | 1 => simp [post, pE, ind] <;> norm_num
    | 2 => simp [post, pE, ind] <;> norm_num

/-- The base law is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma μ₀_nonneg (ω : Fin 3 × Bool) : 0 ≤ μ₀ ω := by
  rcases ω with ⟨e, h⟩
  match e, h with
  | 0, true | 0, false | 1, true | 1, false | 2, true | 2, false => norm_num [μ₀, pE, post]

/-- The base law has mass one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma μ₀_sum_one : ∑ ω, μ₀ ω = 1 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, μ₀]
  norm_num [pE, post]

/-- The sum of the uniform policy law is one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ν_sum_one : ∑ π : Policy evTables Bool, (1 / 8 : ℚ) = 1 := by
  rw [sum_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- The data shared by both versions, as a function of the utility.
Source: mandate T13
Kind: D
Fidelity: exact -/
abbrev data (U : Fin 3 × Bool → Policy evTables Bool → ℚ) : IndepData witIndex 1 evTables Bool where
  Ω₀ := Fin 3 × Bool
  μ₀ := μ₀
  μ₀_nonneg := μ₀_nonneg
  μ₀_sum_one := μ₀_sum_one
  state₀ := fun ω => ev ω.1
  small₀ := small₀
  faith₀ := faith₀
  ν := fun _ => 1 / 8
  ν_nonneg := fun _ => by norm_num
  ν_sum_one := ν_sum_one
  U₀ := U

/-- The state mass of class `e` is `P(e)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma stateMass_eq (U : Fin 3 × Bool → Policy evTables Bool → ℚ) (e : Fin 3) :
    (data U).toPrior.stateMass (ev e) = pE e := by
  rw [IndepData.stateMass_toPrior]
  show massOf μ₀ (fun ω₀ : Fin 3 × Bool => ev ω₀.1 = ev e) = pE e
  simp only [massOf, ev_inj, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, μ₀]
  match e with
  | 0 => simp [pE, post] <;> norm_num
  | 1 => simp [pE, post] <;> norm_num
  | 2 => simp [pE, post] <;> norm_num

/-- Every state has positive mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma stateMass_pos (U : Fin 3 × Bool → Policy evTables Bool → ℚ) (T : ↥evTables) :
    0 < (data U).toPrior.stateMass T := by
  obtain ⟨e, rfl⟩ := eq_ev T
  rw [stateMass_eq]
  match e with
  | 0 => norm_num [pE]
  | 1 => norm_num [pE]
  | 2 => norm_num [pE]

/-- The structural facts shared by both versions: `NDPOLICY`, `NDPOL`, `Reflective`,
`ReflectivePolicy`, `IndependentPointsGivenState`.
Source: `udt-bli-core` `Product.lean`
Kind: L
Fidelity: n/a -/
lemma structure_all (U : Fin 3 × Bool → Policy evTables Bool → ℚ) :
    (data U).toPrior.NDPOLICY ∧ (data U).toPrior.NDPOL ∧ (data U).toPrior.Reflective ∧
    (data U).toPrior.ReflectivePolicy ∧ (data U).toPrior.IndependentPointsGivenState := by
  refine ⟨(data U).ndpolicy_toPrior (fun _ => by show (0 : ℚ) < 1 / 8; norm_num),
    (data U).ndpol_toPrior ?_, (data U).reflective_toPrior, (data U).reflectivePolicy_toPrior,
    (data U).independentPointsGivenState_toPrior_of_prodLaw (fun _ _ => 1 / 2)
      (fun _ => by norm_num [Fintype.sum_bool]) uniform_eq_prodLaw⟩
  intro T a
  show 0 < massOf (fun _ : Policy evTables Bool => (1 / 8 : ℚ)) (fun π => π T = a)
  rw [uniform_eq_prodLaw, IndepData.massOf_prodLaw_point _ (fun _ => by norm_num [Fintype.sum_bool])]
  norm_num

/-! ## Version A -/

namespace VerA

/-- **Version A's utility**: `−10·[pay at e]·[h] + 100·[¬h]·[pay at e]` — Omega's counterfactual
reads the same evidence.
Source: `main.tex` 299–303 (bli-paper-020)
Kind: D
Fidelity: exact -/
def U (ω : Fin 3 × Bool) (π : Policy evTables Bool) : ℚ :=
  if π (ev ω.1) then (if ω.2 then -10 else 100) else 0

/-- The Version A prior. Source: bli-paper-020. Kind: D. Fidelity: exact -/
abbrev prior : FiniteBLIPrior witIndex 1 evTables Bool := (data U).toPrior

/-- The per-world payoff when paying. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def g (ω : Fin 3 × Bool) : ℚ := if ω.2 then -10 else 100

/-- **The cell value in Version A depends on the policy only through its point at the state**:
`cellEU (ev e) π = [π (ev e)] · 𝔼[g | e]`.
Source: none: infrastructure (the rectangle factorization)
Kind: L
Fidelity: n/a -/
lemma cellEU_eq (T : ↥evTables) (π : Policy evTables Bool) :
    prior.cellEU T π = (if π T then 1 else 0) *
      (integralOf μ₀ g (fun ω₀ => ev ω₀.1 = T) / massOf μ₀ (fun ω₀ => ev ω₀.1 = T)) := by
  have hnum : integralOf prior.μ prior.U (fun ω => prior.state ω = T ∧ prior.pp ω = π) =
      integralOf (data U).μ₀ g (fun ω₀ => (data U).state₀ ω₀ = T) *
        integralOf (data U).ν (fun π' : Policy evTables Bool => if π' T then (1 : ℚ) else 0)
          (fun π' => π' = π) := by
    rw [← (data U).integralOf_rect]
    apply integralOf_congr_fun
    rintro ⟨ω₀, π'⟩ ⟨h₁, h₂⟩
    change ev ω₀.1 = T at h₁
    change π' = π at h₂
    change U ω₀ π' = _
    subst h₂
    simp only [U, g, h₁]
    split_ifs <;> ring
  have hden : massOf prior.μ (fun ω => prior.state ω = T ∧ prior.pp ω = π) =
      massOf (data U).μ₀ (fun ω₀ => (data U).state₀ ω₀ = T) * massOf (data U).ν (fun π' => π' = π) := by
    rw [← (data U).massOf_rect]
    rfl
  have hν : massOf (data U).ν (fun π' => π' = π) = 1 / 8 := by
    simp [massOf]
  have hν' : integralOf (data U).ν (fun π' : Policy evTables Bool => if π' T then (1 : ℚ) else 0)
      (fun π' => π' = π) = (1 / 8) * (if π T then 1 else 0) := by
    simp [integralOf]
  unfold FiniteBLIPrior.cellEU condExp
  rw [hnum, hden, hν, hν']
  change (integralOf μ₀ g (fun ω₀ => ev ω₀.1 = T) * (1 / 8 * (if π T then 1 else 0))) /
    (massOf μ₀ (fun ω₀ => ev ω₀.1 = T) * (1 / 8)) = _
  field_simp
  try ring

/-- **Local utility holds in Version A.**
Source: bli-paper-020 (Version A: Omega reads the same evidence)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem localUtility : prior.LocalUtility := by
  intro T π π' h _ _
  rw [cellEU_eq, cellEU_eq, h]

/-- **Version A is `NoCrossBranch`** (through `udt-bli-core`'s bridge from local utility and
independence given the state).
Source: bli-paper-020, 021
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem noCrossBranch : prior.NoCrossBranch :=
  prior.noCrossBranch_of_localUtility_indepGivenState localUtility (structure_all U).2.2.2.2

/-- **The home value of paying in class `e` is `100 − 110·P(h | e)`**, and of refusing `0`.
Source: `main.tex` 301–303 ("If the probability of heads is less than 10/11, one should accept")
Kind: L
Fidelity: exact -/
lemma homeEU_eq (e : Fin 3) :
    prior.homeEU (ev e) true = 100 - 110 * post e ∧ prior.homeEU (ev e) false = 0 := by
  constructor <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU condExp integralOf massOf
    show (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) / (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) = _
    simp only [Fintype.sum_prod_type, sum_pol, Fintype.sum_bool, Fin.sum_univ_three, prior, data,
      IndepData.toPrior, IndepData.μ, U, μ₀, ev_inj, polOf_ev]
    match e with
    | 0 => simp [post, pE] <;> norm_num
    | 1 => simp [post, pE] <;> norm_num
    | 2 => simp [post, pE] <;> norm_num

/-- **The threshold `10/11`, exact**: paying is the updateful choice in class `e` iff
`P(h | e) ≤ 10/11`.
Source: `main.tex` 301–303 (bli-paper-020)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem updateful_pay_iff (e : Fin 3) :
    prior.IsUpdatefulChoice (ev e) true ↔ post e ≤ 10 / 11 := by
  obtain ⟨hp, hr⟩ := homeEU_eq e
  unfold FiniteBLIPrior.IsUpdatefulChoice
  constructor
  · intro h
    have := h false
    rw [hp, hr] at this
    linarith
  · intro h b
    cases b
    · rw [hp, hr]; linarith
    · exact le_refl _

/-- The optimal policy of Version A: pay at `lo` and `mid`, refuse at `hi`.
Source: `main.tex` 301–303
Kind: D
Fidelity: exact -/
def πA : Policy evTables Bool := fun T => if T = ev 2 then false else true

/-- **Version A**: the UDT 1.1 optimum is unique and updateful — pay at `lo` (`P(h | e) = 1/18`)
and `mid` (`1/2`), refuse at `hi` (`17/18 > 10/11`). Via `udt-bli-core`'s
`priorOptimal_iff_updateful_on_support` (the prior is `NDPOLICY`, `ReflectivePolicy`,
`LocalUtility`), so the prior-optimal policies are exactly the pointwise updateful ones.
Source: `main.tex` 299–303 (bli-paper-020, Version A)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem versionA : prior.IsPriorOptimal πA ∧ (∀ π, prior.IsPriorOptimal π → π = πA) ∧
    prior.NoCrossBranch ∧ prior.Reflective ∧ prior.NDPOL := by
  obtain ⟨hpol, hndpol, hR, hRP, _⟩ := structure_all U
  have key : ∀ π, prior.IsPriorOptimal π ↔ ∀ T, 0 < prior.stateMass T → prior.IsUpdatefulChoice T (π T) :=
    fun π => prior.priorOptimal_iff_updateful_on_support hpol hRP localUtility π
  have hchoice : ∀ e b, prior.IsUpdatefulChoice (ev e) b ↔ b = πA (ev e) := by
    intro e b
    cases b
    · constructor
      · intro h
        have := h true
        obtain ⟨hp, hr⟩ := homeEU_eq e
        rw [hp, hr] at this
        match e with
        | 0 => norm_num [post] at this
        | 1 => norm_num [post] at this
        | 2 => simp [πA]
      · intro h
        match e with
        | 0 => simp [πA] at h
        | 1 => simp [πA] at h
        | 2 =>
          intro b
          obtain ⟨hp, hr⟩ := homeEU_eq 2
          cases b
          · exact le_refl _
          · rw [hp, hr]; norm_num [post]
    · rw [updateful_pay_iff]
      match e with
      | 0 => simp [πA, post]; norm_num
      | 1 => simp [πA, post]; norm_num
      | 2 => simp [πA, post]; norm_num
  refine ⟨?_, ?_, noCrossBranch, hR, hndpol⟩
  · rw [key]
    intro T _
    obtain ⟨e, rfl⟩ := eq_ev T
    exact (hchoice e _).mpr rfl
  · intro π hπ
    rw [key] at hπ
    funext T
    obtain ⟨e, rfl⟩ := eq_ev T
    exact (hchoice e _).mp (hπ (ev e) (stateMass_pos U (ev e)))

end VerA

/-! ## Version B -/

namespace VerB

/-- The indicator of paying in class `e'`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def x (π : Policy evTables Bool) (e' : Fin 3) : ℚ := if π (ev e') then 1 else 0

/-- **Version B's utility**: `−10·[pay at e]·[h] + 100·[¬h]·∑_{e'} P(e')·[pay at e']` — Omega
pays with the total probability of paying, summed over the evidence the agent might have seen.
Source: `main.tex` 305–307 (bli-paper-020)
Kind: D
Fidelity: exact -/
def U (ω : Fin 3 × Bool) (π : Policy evTables Bool) : ℚ :=
  if ω.2 then -10 * x π ω.1 else 100 * ∑ e', pE e' * x π e'

/-- The Version B prior. Source: bli-paper-020. Kind: D. Fidelity: exact -/
abbrev prior : FiniteBLIPrior witIndex 1 evTables Bool := (data U).toPrior

/-- The coefficient of `[pay at e]` in the ex-ante value: `P(e)·(50 − 10·P(h | e))`.
Source: mandate T13 ("the coefficient … is `P(e)(50 − 10 P(h | e)) > 0`")
Kind: D
Fidelity: exact -/
def coef (e : Fin 3) : ℚ := pE e * (50 - 10 * post e)

/-- **The ex-ante value of a policy in Version B is `∑_e coef e · [pay at e]`** (the average bias
is `1/2`, so `P(¬h) = 1/2`).
Source: `main.tex` 305–307; mandate T13
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exAnteValue_eq (π : Policy evTables Bool) :
    prior.exAnteValue π = ∑ e, coef e * x π e := by
  have hnum : integralOf prior.μ prior.U (fun ω => prior.pp ω = π) =
      integralOf (data U).μ₀ (fun ω₀ => U ω₀ π) (fun _ => True) *
        integralOf (data U).ν (fun _ : Policy evTables Bool => (1 : ℚ)) (fun π' => π' = π) := by
    rw [← (data U).integralOf_rect]
    change integralOf (data U).μ (fun ω => U ω.1 ω.2) (fun ω => ω.2 = π) =
      integralOf (data U).μ (fun ω => U ω.1 π * 1) (fun ω => True ∧ ω.2 = π)
    unfold integralOf
    apply Finset.sum_congr rfl
    rintro ⟨ω₀, π'⟩ _
    by_cases h : π' = π
    · subst h; simp
    · simp [h]
  have hden : massOf prior.μ (fun ω => prior.pp ω = π) =
      massOf (data U).μ₀ (fun _ => True) * massOf (data U).ν (fun π' => π' = π) := by
    rw [← (data U).massOf_rect]
    apply massOf_congr
    intro ω
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  have hν : massOf (data U).ν (fun π' => π' = π) = 1 / 8 := by simp [massOf]
  have hν' : integralOf (data U).ν (fun _ : Policy evTables Bool => (1 : ℚ)) (fun π' => π' = π) =
      1 / 8 := by
    simp [integralOf]
  have hμ : massOf (data U).μ₀ (fun _ => True) = 1 := by
    change massOf μ₀ (fun _ => True) = 1
    unfold massOf; simp [μ₀_sum_one]
  unfold FiniteBLIPrior.exAnteValue condExp
  rw [hnum, hden, hν, hν', hμ]
  change (integralOf μ₀ (fun ω₀ => U ω₀ π) (fun _ => True) * (1 / 8)) / (1 * (1 / 8)) = _
  simp only [integralOf, if_true, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool,
    μ₀, U, x, pE, post, coef, Bool.false_eq_true, if_false]
  ring

/-- The coefficients are positive. Source: mandate T13. Kind: L. Fidelity: n/a -/
lemma coef_pos (e : Fin 3) : 0 < coef e := by
  match e with
  | 0 => norm_num [coef, pE, post]
  | 1 => norm_num [coef, pE, post]
  | 2 => norm_num [coef, pE, post]

/-- The constant-pay policy. Source: `main.tex` 305–307. Kind: D. Fidelity: exact -/
def πB : Policy evTables Bool := fun _ => true

/-- **Version B: the constant-pay policy is the unique UDT 1.1 optimum** — every policy that
refuses somewhere is strictly worse (the coefficient of each `[pay at e]` is positive).
Source: `main.tex` 305–307 (bli-paper-020, Version B)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem versionB_optimal : prior.IsPriorOptimal πB ∧
    ∀ π, π ≠ πB → prior.exAnteValue π < prior.exAnteValue πB := by
  have hle : ∀ π, prior.exAnteValue π ≤ prior.exAnteValue πB := by
    intro π
    rw [exAnteValue_eq, exAnteValue_eq]
    apply Finset.sum_le_sum
    intro e _
    unfold x πB
    simp only [if_true]
    split_ifs
    · exact le_refl _
    · simp only [mul_zero, mul_one]; exact le_of_lt (coef_pos e)
  refine ⟨hle, fun π hne => ?_⟩
  rw [exAnteValue_eq, exAnteValue_eq]
  have : ∃ e, π (ev e) = false := by
    by_contra h
    push Not at h
    apply hne
    funext T
    obtain ⟨e, rfl⟩ := eq_ev T
    have he := h e
    cases hb : π (ev e)
    · exact absurd hb he
    · rfl
  obtain ⟨e₀, he₀⟩ := this
  apply Finset.sum_lt_sum
  · intro e _
    unfold x πB
    simp only [if_true]
    split_ifs
    · exact le_refl _
    · simp only [mul_zero, mul_one]; exact le_of_lt (coef_pos e)
  · refine ⟨e₀, Finset.mem_univ _, ?_⟩
    unfold x πB
    simp only [he₀, Bool.false_eq_true, if_false, if_true, mul_zero, mul_one]
    exact coef_pos e₀

/-- **Version B is not `NoCrossBranch`**: within the `lo` branch, the value depends on the
action at `hi` — `𝔼[U | state = lo ∧ pay at hi] = 2240/27 ≠ 1340/27 = 𝔼[U | state = lo ∧ refuse at hi]`,
both cells positive.
Source: `main.tex` 305–309 ("In Version B, Omega doesn't update, so we shouldn't either")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem versionB_not_noCrossBranch : ¬ prior.NoCrossBranch := by
  intro h
  have hne : ev 0 ≠ ev 2 := by simp
  have hcell : ∀ a : Bool, 0 < prior.jointMass (ev 0) (ev 2) a := by
    intro a
    rw [IndepData.jointMass_toPrior]
    show 0 < massOf μ₀ (fun ω₀ => ev ω₀.1 = ev 0) * massOf (fun _ : Policy evTables Bool => (1 / 8 : ℚ)) (fun π => π (ev 2) = a)
    rw [uniform_eq_prodLaw, IndepData.massOf_prodLaw_point _ (fun _ => by norm_num [Fintype.sum_bool])]
    simp only [massOf, ev_inj, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, μ₀]
    simp [pE, post] <;> norm_num
  have := h (ev 2) (ev 0) true false hne (hcell true) (hcell false)
  unfold FiniteBLIPrior.condEU condExp integralOf massOf at this
  revert this
  show ((∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) / (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) =
    (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) / (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _)) → False
  simp only [Fintype.sum_prod_type, sum_pol, Fintype.sum_bool, Fin.sum_univ_three, prior, data,
    IndepData.toPrior, IndepData.μ, U, x, μ₀, ev_inj, polOf_ev, pE, post]
  simp <;> norm_num

/-- **The updateful rule refuses at `hi` in Version B**: `homeEU hi refuse > homeEU hi pay`.
Source: `main.tex` 305–309; mandate T13
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem versionB_updateful_refuses_hi :
    prior.homeEU (ev 2) true < prior.homeEU (ev 2) false := by
  unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU condExp integralOf massOf
  show ((∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) / (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) <
    (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _) / (∑ ω : (Fin 3 × Bool) × Policy evTables Bool, _))
  simp only [Fintype.sum_prod_type, sum_pol, Fintype.sum_bool, Fin.sum_univ_three, prior, data,
    IndepData.toPrior, IndepData.μ, U, x, μ₀, ev_inj, polOf_ev, pE, post]
  simp <;> norm_num

end VerB

/-- **The paper's moral as one row**: Version A is `NoCrossBranch` and Version B is not, and in
Version A the one-step rule coincides with the updateful rule at every evidence class
(`udt-bli-core`'s `oneStep_iff_updateful`) — "UDT 1.1 behaves updatefully exactly when Omega's
counterfactual does".
Source: `main.tex` 309 (bli-paper-020, 021)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem moral : VerA.prior.NoCrossBranch ∧ ¬ VerB.prior.NoCrossBranch ∧
    ∀ (T : ↥evTables) (a : Bool), VerA.prior.IsOneStepChoice T a ↔ VerA.prior.IsUpdatefulChoice T a := by
  obtain ⟨_, hndpol, hR, _, _⟩ := structure_all VerA.U
  exact ⟨VerA.noCrossBranch, VerB.versionB_not_noCrossBranch, fun T a =>
    VerA.prior.oneStep_iff_updateful hndpol hR VerA.noCrossBranch T (stateMass_pos VerA.U T) a⟩

end MugEv

end Cleanroom.Udt.UdtPaperTiling
