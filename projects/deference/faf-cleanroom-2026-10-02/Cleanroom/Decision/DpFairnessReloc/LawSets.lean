import Cleanroom.Decision.DpFairnessReloc.RelocateThms
import Cleanroom.Decision.DpFairnessReloc.Witnesses

/-!
# Law-set grades, `∼`, and the certificate `⊑` (T7, T9, T10)

Package `dp-fairness-reloc`, file 9. The realizable-law sets of a problem, read on a shared world
type through a projection `f` (the identity for an input, `Prod.fst` for a relocated output):

* `lawOfW f C B`: the `(λ, r)`-law of `C` on `B` marginalised along `f` (Definition 6);
  `lawOfW' f C B` the same under Definition 6′.
* `LPure` (pure profiles), `LMixed` (Definition 6), `LSeed` (Definition 6′), `LCorr` (finite
  mixtures of pure laws — `conv L_pure`, explicit).
* `Sim f f' B B' := LPure f B = LPure f' B'` — FR-9's reduced-profile relation `∼` *is* equality
  of the pure-law images.
* `Cert f f' B B'` — EQ-12's certificate `⊑`; `HullClosed f B` — the class `𝓗`.

Theorems: **UN-2 / FR-9(i) at the pure grade** — `B ∼ Rel_U B` for **every** `B` and `U`
(`LPure_reloc`); **C.1** — `T_opt` is not `∼`-invariant: `amd ∼ Rel amd` while every procedure on
the relocated AMD is worth at most `1 < 4/3` (`amd_sim_reloc`, `value_reloc_amd_le_one`); the
surviving neighbour — on almost-fair trees the optimum is a function of `L_pure`
(`sim_value_le_of_almostFair`); **FR-10** — `T_{d,e} ∼ T_{e,d}`, both strongly fair and almost
fair, while the root point differs and the queried sets are disjoint (`tde_sim_ted`); **EQ-11's inclusions** and `L_mixed = L_seed`
on almost-fair trees (function level); **the AMD leaves the hull** (mass `2/9` on the exit-2 leaf
no pure law reaches: `amd_not_hullClosed`), so `⊑` is not reflexive on the AMD (Dead 2
refuted); **EQ-12** — optimum preservation under `⊑`, transitivity, `⊑` relates only
hull-closed trees, reflexive exactly on `𝓗`, and `B ⊑ Rel_U B` for almost-fair `B` and any
`U`; **E5 is licensed** by `⊑` although its function-level law changes (Dead 1 refuted).
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {Ω : Type} {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Laws marginalised to a shared world type -/

section laws

variable {Ω' ι' : Type} {acts' : ι' → Type} [∀ d, Fintype (acts' d)]

/-- The `(λ, r)`-law of `C` on `B` read on the world type `Ω` through `f` (Definition 6).
Source: `fair-repair.md` §2.1 ("`law_B(π) ∈ Δ(Ω_𝓔 × ℝ)` … marginalized to the common
algebra — enrichment coordinates dropped"); `equiv.md` Definitions carried
Kind: D -/
noncomputable def lawOfW (f : Ω' → Ω) (C : Proc ι' acts' K) (B : Tree Ω' ι' acts' K) :
    Ω × K →₀ K :=
  ∑ ℓ, Finsupp.single (f (world B ℓ), payoff B ℓ) (leafLaw C B ℓ)

/-- The same under Definition 6′.
Source: `equiv.md` Definitions carried (`𝓛_seed`)
Kind: D -/
noncomputable def lawOfW' [DecidableEq ι'] [∀ d, DecidableEq (acts' d)] (f : Ω' → Ω)
    (C : Proc ι' acts' K) (B : Tree Ω' ι' acts' K) : Ω × K →₀ K :=
  ∑ ℓ, Finsupp.single (f (world B ℓ), payoff B ℓ) (leafLaw' C B ℓ)

theorem lawOfW_id (C : Proc ι' acts' K) (B : Tree Ω' ι' acts' K) :
    lawOfW id C B = contLaw C B := rfl

/-- The value is the payoff integral of the marginalised law, for any projection `f`.
Source: `fair-repair.md` FR-9(iii) ("`V` is a function of the law")
Kind: L -/
theorem value_eq_lawOfW_sum (f : Ω' → Ω) (C : Proc ι' acts' K) (B : Tree Ω' ι' acts' K) :
    value C B = (lawOfW f C B).sum fun p v => v * p.2 := by
  unfold lawOfW value
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

/-- The payoff integral `∫ r dL`.
Source: none: infrastructure
Kind: D -/
noncomputable def valInt (L : Ω × K →₀ K) : K := L.sum fun p v => v * p.2

theorem valInt_finset_sum {α : Type} (s : Finset α) (L : α → Ω × K →₀ K) :
    valInt (∑ a ∈ s, L a) = ∑ a ∈ s, valInt (L a) := by
  unfold valInt
  rw [Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem valInt_smul (c : K) (L : Ω × K →₀ K) : valInt (c • L) = c * valInt L := by
  unfold valInt
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun p _ => ?_
  simp [mul_assoc]

theorem value_eq_valInt (f : Ω' → Ω) (C : Proc ι' acts' K) (B : Tree Ω' ι' acts' K) :
    value C B = valInt (lawOfW f C B) :=
  value_eq_lawOfW_sum f C B

/-- Two procedures agreeing on the queried points have the same marginalised law.
Source: none: infrastructure
Kind: L -/
theorem lawOfW_congr_queried [DecidableEq ι'] (f : Ω' → Ω) {C C' : Proc ι' acts' K}
    (B : Tree Ω' ι' acts' K) (h : ∀ d ∈ queried B, C d = C' d) : lawOfW f C B = lawOfW f C' B := by
  unfold lawOfW
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [leafLaw_congr_queried B h ℓ]

/-- Regrouping a sum of singles along a map of leaves.
Source: none: infrastructure
Kind: L -/
theorem sum_single_regroup {A A' : Type} [Fintype A] [Fintype A'] [DecidableEq A']
    (e : A → A') (g : A' → Ω × K) (w : A → K) :
    (∑ a, Finsupp.single (g (e a)) (w a)) =
      ∑ b, Finsupp.single (g b) (∑ a, if e a = b then w a else 0) := by
  classical
  ext p
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  symm
  calc (∑ x, if g x = p then ∑ a, (if e a = x then w a else 0) else 0)
      = ∑ x, ∑ a, (if g x = p then (if e a = x then w a else 0) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
    _ = ∑ a, ∑ x, (if g x = p then (if e a = x then w a else 0) else 0) := Finset.sum_comm
    _ = ∑ a, (if g (e a) = p then w a else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single (e a)]
        · simp
        · intro x _ hx; simp [Ne.symm hx]
        · intro h; exact absurd (Finset.mem_univ _) h

end laws

/-! ### The law-set grades and `∼` -/

section sets

variable {Ω' ι' : Type} {acts' : ι' → Type} [∀ d, Fintype (acts' d)] [DecidableEq ι']
  [∀ d, DecidableEq (acts' d)]

/-- `𝓛_pure(B)`: the laws of the pure profiles.
Source: `equiv.md` Definitions carried (`𝓛_pure`); `fair-repair.md` §2.1
Kind: D -/
def LPure (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : Set (Ω × K →₀ K) :=
  Set.range fun π : (d : ι') → acts' d => lawOfW f (Proc.ofFun π) B

/-- `𝓛_mixed(B)`: the laws of all procedures under Definition 6.
Source: `equiv.md` Definitions carried (`𝓛_mixed`)
Kind: D -/
def LMixed (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : Set (Ω × K →₀ K) :=
  Set.range fun C : Proc ι' acts' K => lawOfW f C B

/-- `𝓛_seed(B)`: the laws of all procedures under Definition 6′.
Source: `equiv.md` Definitions carried (`𝓛_seed`)
Kind: D -/
def LSeed (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : Set (Ω × K →₀ K) :=
  Set.range fun C : Proc ι' acts' K => lawOfW' f C B

/-- `𝓛_corr(B) = conv 𝓛_pure(B)`: explicit finite mixtures of pure laws.
Source: `equiv.md` Definitions carried (`𝓛_corr := conv 𝓛_pure`); mandate §3 ("explicit finite
mixtures — this *is* `conv L_pure`")
Kind: D -/
def LCorr (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : Set (Ω × K →₀ K) :=
  {L | ∃ (α : Type) (_ : Fintype α) (m : FinDistr K α) (π : α → (d : ι') → acts' d),
    L = ∑ a, m.w a • lawOfW f (Proc.ofFun (π a)) B}

/-- **`B ∼ B'` (FR-9's reduced-profile equivalence)**: equal images of the pure-law map on the
shared world type. (Reduction by equal laws makes the reduced map injective, so "a bijection of
reduced profile spaces commuting with `law`" is exactly image equality.)
Source: `fair-repair.md` §2.1 ("`B ∼ B'` iff `law` has the same image set")
Kind: D
Fidelity: exact -/
def Sim {Ω₁ ι₁ : Type} {acts₁ : ι₁ → Type} [∀ d, Fintype (acts₁ d)] [DecidableEq ι₁]
    [∀ d, DecidableEq (acts₁ d)] (f : Ω' → Ω) (f' : Ω₁ → Ω) (B : Tree Ω' ι' acts' K)
    (B' : Tree Ω₁ ι₁ acts₁ K) : Prop :=
  LPure f B = LPure f' B'

/-- **The certificate `B ⊑ B'`** (EQ-12): equal pure images, `𝓛_mixed(B) ⊆ 𝓛_mixed(B') ⊆
conv 𝓛_pure(B)`.
Source: `equiv.md` Definitions carried ("Certificate `B ⊑ B'`")
Kind: D -/
def Cert {Ω₁ ι₁ : Type} {acts₁ : ι₁ → Type} [∀ d, Fintype (acts₁ d)] [DecidableEq ι₁]
    [∀ d, DecidableEq (acts₁ d)] (f : Ω' → Ω) (f' : Ω₁ → Ω) (B : Tree Ω' ι' acts' K)
    (B' : Tree Ω₁ ι₁ acts₁ K) : Prop :=
  LPure f B = LPure f' B' ∧ LMixed f B ⊆ LMixed f' B' ∧ LMixed f' B' ⊆ LCorr f B

/-- **The hull-closed class `𝓗`**: `𝓛_mixed(B) ⊆ conv 𝓛_pure(B)`.
Source: `equiv.md` Definitions carried ("Hull-closed class `𝓗`")
Kind: D -/
def HullClosed (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : Prop := LMixed f B ⊆ LCorr f B

/-! ### T9: the inclusions -/

theorem LPure_subset_LMixed (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : LPure f B ⊆ LMixed f B := by
  rintro _ ⟨π, rfl⟩; exact ⟨Proc.ofFun π, rfl⟩

theorem LPure_subset_LSeed [∀ d, Nonempty (acts' d)] (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) :
    LPure f B ⊆ LSeed f B := by
  rintro _ ⟨π, rfl⟩
  refine ⟨Proc.ofFun π, ?_⟩
  unfold lawOfW lawOfW'
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [leafLaw'_ofFun]

theorem LPure_subset_LCorr (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : LPure f B ⊆ LCorr f B := by
  rintro _ ⟨π, rfl⟩
  refine ⟨Unit, inferInstance, FinDistr.pure (), fun _ => π, ?_⟩
  simp

/-- **`𝓛_seed ⊆ 𝓛_corr`**: the shared-seed law is the product mixture of the pure laws
(SE-1(a), `dp-core-tree`).
Source: `equiv.md` EQ-11 ("`𝓛_pure ⊆ 𝓛_seed ⊆ 𝓛_corr`")
Kind: C -/
theorem LSeed_subset_LCorr [∀ d, Nonempty (acts' d)] (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) :
    LSeed f B ⊆ LCorr f B := by
  rintro _ ⟨C, rfl⟩
  refine ⟨(d : ↥(queried B)) → acts' d, inferInstance, FinDistr.pi (queried B) fun d => C d,
    fun π => extendAssign B π, ?_⟩
  unfold lawOfW'
  simp only [leafLaw'_eq_product_mixture C B, Finsupp.single_finsetSum, Finset.smul_sum,
    FinDistr.pi_w]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold lawOfW
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul]
  congr 2
  apply leafLaw_congr_queried
  intro d hd
  rw [Proc.pureOn_of_mem C (queried B) π hd]
  simp [Proc.ofFun, extendAssign, hd]

/-- **On almost-fair trees `𝓛_mixed = 𝓛_seed`** — a function-level identity (the two laws agree
procedure by procedure), hence equal images.
Source: `equiv.md` EQ-11 ("on non-nested trees `𝓛_mixed = 𝓛_seed` (function-level identity by
multiaffinity, hence equal images)")
Kind: C -/
theorem lawOfW_eq_lawOfW'_of_almostFair (f : Ω' → Ω) {B : Tree Ω' ι' acts' K} (h : AlmostFair B)
    (C : Proc ι' acts' K) : lawOfW f C B = lawOfW' f C B := by
  unfold lawOfW lawOfW'
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [h.leafLaw_eq_leafLaw' C ℓ]

theorem LMixed_eq_LSeed_of_almostFair (f : Ω' → Ω) {B : Tree Ω' ι' acts' K} (h : AlmostFair B) :
    LMixed f B = LSeed f B := by
  ext L
  constructor
  · rintro ⟨C, rfl⟩; exact ⟨C, (lawOfW_eq_lawOfW'_of_almostFair f h C).symm⟩
  · rintro ⟨C, rfl⟩; exact ⟨C, lawOfW_eq_lawOfW'_of_almostFair f h C⟩

/-- Almost-fair trees are hull-closed (EQ-12(b): "non-nested trees lie in `𝓗`").
Source: `equiv.md` EQ-12(b)
Kind: C -/
theorem AlmostFair.hullClosed [∀ d, Nonempty (acts' d)] (f : Ω' → Ω) {B : Tree Ω' ι' acts' K}
    (h : AlmostFair B) : HullClosed f B := by
  intro L hL
  rw [LMixed_eq_LSeed_of_almostFair f h] at hL
  exact LSeed_subset_LCorr f B hL

end sets

/-! ### T7(a): `B ∼ Rel_U B` for every `B` and `U` -/

section reloc

variable {ι : Type} {acts : ι → Type} [DecidableEq ι] [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)] (U : Finset ι) (B : Tree Ω ι acts K)

/-- The marginalised law of the output regroups along the leaf map.
Source: none: infrastructure
Kind: L -/
theorem lawOfW_relocRoot (C' : Proc (ι ⊕ Unit) (actsR acts U) K) :
    lawOfW Prod.fst C' (relocRoot U B) =
      ∑ ℓ, Finsupp.single (world B ℓ, payoff B ℓ)
        (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then leafLaw C' (relocRoot U B) ℓ' else 0) := by
  unfold lawOfW
  have hw : ∀ ℓ' : (relocRoot U B).Leaves,
      ((world (relocRoot U B) ℓ').1, payoff (relocRoot U B) ℓ') =
        (world B (leafMap U B ℓ'), payoff B (leafMap U B ℓ')) := by
    rintro ⟨σ, ℓ'⟩
    rw [world_relocRoot, payoff_relocRoot]
  simp only [hw]
  exact sum_single_regroup (leafMap U B) (fun ℓ => (world B ℓ, payoff B ℓ)) _

/-- The projected pure law of a lifted assignment is the input's pure law (FR-7(a) at the
law level).
Source: `fair-repair.md` FR-7(a)
Kind: C -/
theorem lawOfW_reloc_ofFun (π : (d : ι) → acts d) :
    lawOfW Prod.fst (Proc.ofFun (liftFun U π)) (relocRoot U B) = lawOfW id (Proc.ofFun π) B := by
  rw [lawOfW_relocRoot]
  unfold lawOfW
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [push_leafLaw_ofFun U B π ℓ]
  rfl

/-- The assignment of `B` induced by an assignment of the relocated tree.
Source: none: infrastructure
Kind: D -/
def restrictAssign (π' : (p : ι ⊕ Unit) → actsR acts U p) : (d : ι) → acts d :=
  fun d => if h : d ∈ U then π' (.inr ()) ⟨d, h⟩ else π' (.inl d)

/-- An assignment of the output and the lift of its induced assignment agree on the queried
points of the output.
Source: none: infrastructure (`queried_reloc` at work)
Kind: L -/
theorem ofFun_agree_liftFun (π' : (p : ι ⊕ Unit) → actsR acts U p) :
    ∀ p ∈ queried (relocRoot U B),
      (Proc.ofFun π' : Proc (ι ⊕ Unit) (actsR acts U) K) p =
        Proc.ofFun (liftFun U (restrictAssign U π')) p := by
  intro p hp
  cases p with
  | inl d =>
      have hd := not_mem_U_of_mem_queried_relocRoot U B hp
      simp [Proc.ofFun, liftFun, restrictAssign, hd]
  | inr u =>
      cases u
      simp only [Proc.ofFun, liftFun, restrictAssign]
      congr 1
      funext d
      simp [d.2]

/-- **UN-2 / FR-9(i) at the pure grade: `B ∼ Rel_U B` for every `B` and every `U`** — the
pure-law images agree, nested fibers included.
Source: `universal.md` UN-2; `fair-repair.md` FR-9(i) (as repaired by `adversary-repair.md`
C.1: "relocation is `∼`-preserving on *every* problem")
Kind: P
Fidelity: exact (root site; `∼` read on the input's world type through `Prod.fst`)
Hyps: none -/
theorem LPure_reloc : LPure Prod.fst (relocRoot U B) = LPure id B := by
  ext L
  constructor
  · rintro ⟨π', rfl⟩
    refine ⟨restrictAssign U π', ?_⟩
    dsimp only
    rw [← lawOfW_reloc_ofFun U B, lawOfW_congr_queried Prod.fst (relocRoot U B)
      (ofFun_agree_liftFun U B π')]
  · rintro ⟨π, rfl⟩
    exact ⟨liftFun U π, lawOfW_reloc_ofFun U B π⟩

theorem sim_reloc : Sim id Prod.fst B (relocRoot U B) := (LPure_reloc U B).symm

/-- Every value on the output is bounded by a pure value of the input, when the output is
positively nested nowhere.
Source: `adversary-repair.md` C.1 ("no strongly fair tree matches the AMD's mixed value")
Kind: C -/
theorem value_reloc_le_pure (hU : ∀ d, Nested B d → d ∈ U) (C' : Proc (ι ⊕ Unit) (actsR acts U) K) :
    ∃ π : (d : ι) → acts d, value C' (relocRoot U B) ≤ value (Proc.ofFun π) B := by
  obtain ⟨π', hπ', -, -⟩ := exists_pure_max_value' (relocRoot U B)
  refine ⟨restrictAssign U π', ?_⟩
  have h1 : value C' (relocRoot U B) = value' C' (relocRoot U B) :=
    Finset.sum_congr rfl fun ℓ' _ => by
      rw [leafLaw_eq_leafLaw'_of_not_nested (not_nested_relocRoot U B hU) C' ℓ']
  rw [h1]
  refine (hπ' C').trans (le_of_eq ?_)
  rw [value_eq_valInt Prod.fst, value_eq_valInt id,
    lawOfW_congr_queried Prod.fst (relocRoot U B) (ofFun_agree_liftFun U B π'),
    lawOfW_reloc_ofFun]

/-- **`𝓛_mixed(Rel_U B) ⊆ conv 𝓛_pure(B)`** when the output is positively nested nowhere: every
output law is the product mixture of output pure laws, which are input pure laws.
Source: `equiv.md` EQ-12(c) ("the output is non-nested, hence multiaffine, hence inside
`conv 𝓛_pure(output) = conv 𝓛_pure(B)` (FR-7(a))")
Kind: C -/
theorem LMixed_reloc_subset_LCorr (hU : ∀ d, Nested B d → d ∈ U) :
    LMixed Prod.fst (relocRoot U B) ⊆ LCorr id B := by
  rintro _ ⟨C', rfl⟩
  dsimp only
  have h1 : lawOfW Prod.fst C' (relocRoot U B) = lawOfW' Prod.fst C' (relocRoot U B) := by
    unfold lawOfW lawOfW'
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [leafLaw_eq_leafLaw'_of_not_nested (not_nested_relocRoot U B hU) C' ℓ']
  rw [h1]
  obtain ⟨α, hα, m, π, hmix⟩ := LSeed_subset_LCorr Prod.fst (relocRoot U B) ⟨C', rfl⟩
  dsimp only at hmix
  refine ⟨α, hα, m, fun a => restrictAssign U (π a), ?_⟩
  rw [hmix]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lawOfW_congr_queried Prod.fst (relocRoot U B) (ofFun_agree_liftFun U B (π a)),
    lawOfW_reloc_ofFun]

/-- **EQ-12(c): for almost-fair `B` and every `U`, `B ⊑ Rel_U B`** — pure images equal (T7(a)),
every input law is an output law (FR-6 through the lift), every output law is a mixture of
input pure laws.
Source: `equiv.md` EQ-12(c) ("For almost-fair `B` and closed `U`, `B ⊑ Rel_U(B)`")
Kind: C
Fidelity: stronger (every `U`, not only closed ones — closure is not needed for the law sets)
Hyps: none -/
theorem AlmostFair.cert_reloc (h : AlmostFair B) : Cert id Prod.fst B (relocRoot U B) := by
  refine ⟨(LPure_reloc U B).symm, ?_, ?_⟩
  · rintro _ ⟨C, rfl⟩
    refine ⟨lift U C, ?_⟩
    dsimp only
    rw [lawOfW_relocRoot]
    unfold lawOfW
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [AlmostFair.pushLaw_reloc h U C ℓ]
    rfl
  · exact LMixed_reloc_subset_LCorr U B fun d hd => absurd hd (h.not_nested d)

end reloc

/-! ### T10: the certificate -/

section cert

variable {Ω' ι' : Type} {acts' : ι' → Type} [∀ d, Fintype (acts' d)] [DecidableEq ι']
  [∀ d, DecidableEq (acts' d)]
variable {Ω₁ ι₁ : Type} {acts₁ : ι₁ → Type} [∀ d, Fintype (acts₁ d)] [DecidableEq ι₁]
  [∀ d, DecidableEq (acts₁ d)]
variable {Ω₂ ι₂ : Type} {acts₂ : ι₂ → Type} [∀ d, Fintype (acts₂ d)] [DecidableEq ι₂]
  [∀ d, DecidableEq (acts₂ d)]

/-- A law in `conv 𝓛_pure(B)` is worth at most some pure profile of `B`.
Source: `equiv.md` EQ-12(a) ("`max conv 𝓛_pure(B) = max 𝓛_pure(B)`")
Kind: L -/
theorem valInt_le_of_mem_LCorr [∀ d, Nonempty (acts' d)] (f : Ω' → Ω) (B : Tree Ω' ι' acts' K)
    {L : Ω × K →₀ K} (hL : L ∈ LCorr f B) : ∃ π, valInt L ≤ value (Proc.ofFun π) B := by
  obtain ⟨α, hα, m, π, rfl⟩ := hL
  haveI : Nonempty α := FinDistr.nonempty_of_finDistr m
  rw [valInt_finset_sum]
  simp only [valInt_smul]
  obtain ⟨a, ha⟩ := exists_le_of_convex m fun a => valInt (lawOfW f (Proc.ofFun (π a)) B)
  exact ⟨π a, ha.trans (le_of_eq (value_eq_valInt f _ B).symm)⟩

/-- **EQ-12(a), optimum preservation**: `B ⊑ B'` ⟹ every value on `B` is matched or beaten on
`B'`, and every value on `B'` is at most a pure value of `B` (so the optima coincide: both are
attained, by `dp-core-tree`'s `exists_pure_max_value'` on almost-fair trees and here as the
two-sided bound).
Source: `equiv.md` EQ-12(a) ("`B ⊑ B' ⟹ max_C V_B(C) = max_{C'} V_{B'}(C')`")
Kind: P
Fidelity: exact (stated as the two inequalities; `V` linear in the law)
Hyps: none -/
theorem Cert.value_bounds [∀ d, Nonempty (acts' d)] {f : Ω' → Ω} {f' : Ω₁ → Ω}
    {B : Tree Ω' ι' acts' K} {B' : Tree Ω₁ ι₁ acts₁ K} (h : Cert f f' B B') :
    (∀ C : Proc ι' acts' K, ∃ C' : Proc ι₁ acts₁ K, value C B ≤ value C' B') ∧
      (∀ C' : Proc ι₁ acts₁ K, ∃ π : (d : ι') → acts' d, value C' B' ≤ value (Proc.ofFun π) B) := by
  obtain ⟨-, h1, h2⟩ := h
  refine ⟨fun C => ?_, fun C' => ?_⟩
  · obtain ⟨C', hC'⟩ := h1 ⟨C, rfl⟩
    dsimp only at hC'
    refine ⟨C', le_of_eq ?_⟩
    rw [value_eq_valInt f, value_eq_valInt f', hC']
  · obtain ⟨π, hπ⟩ := valInt_le_of_mem_LCorr f B (h2 ⟨C', rfl⟩)
    exact ⟨π, (value_eq_valInt f' C' B').trans_le hπ⟩

/-- `⊑` is transitive on all trees.
Source: `equiv.md` EQ-12(b)
Kind: L -/
theorem Cert.trans {f : Ω' → Ω} {f₁ : Ω₁ → Ω} {f₂ : Ω₂ → Ω} {B : Tree Ω' ι' acts' K}
    {B₁ : Tree Ω₁ ι₁ acts₁ K} {B₂ : Tree Ω₂ ι₂ acts₂ K} (h : Cert f f₁ B B₁) (h' : Cert f₁ f₂ B₁ B₂) :
    Cert f f₂ B B₂ := by
  obtain ⟨e1, i1, j1⟩ := h
  obtain ⟨e2, i2, j2⟩ := h'
  refine ⟨e1.trans e2, i1.trans i2, ?_⟩
  intro L hL
  obtain ⟨α, hα, m, π, rfl⟩ := j2 hL
  -- a mixture of `B₁`'s pure laws is a mixture of `B`'s pure laws, since the pure images agree
  have hpick : ∀ a, ∃ π₀ : (d : ι') → acts' d,
      lawOfW f₁ (Proc.ofFun (π a)) B₁ = lawOfW f (Proc.ofFun π₀) B := by
    intro a
    have : lawOfW f₁ (Proc.ofFun (π a)) B₁ ∈ LPure f B := by rw [e1]; exact ⟨π a, rfl⟩
    obtain ⟨π₀, hπ₀⟩ := this
    exact ⟨π₀, hπ₀.symm⟩
  choose π₀ hπ₀ using hpick
  refine ⟨α, hα, m, π₀, ?_⟩
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hπ₀ a]

/-- `⊑` relates only hull-closed trees.
Source: `equiv.md` EQ-12(b) ("`B ⊑ B'` forces both `B` and `B'` into `𝓗`")
Kind: L -/
theorem Cert.hullClosed {f : Ω' → Ω} {f' : Ω₁ → Ω} {B : Tree Ω' ι' acts' K}
    {B' : Tree Ω₁ ι₁ acts₁ K} (h : Cert f f' B B') : HullClosed f B ∧ HullClosed f' B' := by
  obtain ⟨e, i, j⟩ := h
  refine ⟨i.trans j, fun L hL => ?_⟩
  obtain ⟨α, hα, m, π, rfl⟩ := j hL
  have hpick : ∀ a, ∃ π₀ : (d : ι₁) → acts₁ d,
      lawOfW f (Proc.ofFun (π a)) B = lawOfW f' (Proc.ofFun π₀) B' := by
    intro a
    have : lawOfW f (Proc.ofFun (π a)) B ∈ LPure f' B' := by rw [← e]; exact ⟨π a, rfl⟩
    obtain ⟨π₀, hπ₀⟩ := this
    exact ⟨π₀, hπ₀.symm⟩
  choose π₀ hπ₀ using hpick
  refine ⟨α, hα, m, π₀, ?_⟩
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hπ₀ a]

/-- `⊑` is reflexive exactly on `𝓗`.
Source: `equiv.md` EQ-12(b) ("reflexive exactly on `𝓗`")
Kind: L -/
theorem cert_self_iff (f : Ω' → Ω) (B : Tree Ω' ι' acts' K) : Cert f f B B ↔ HullClosed f B :=
  ⟨fun h => h.hullClosed.1, fun h => ⟨rfl, subset_rfl, h⟩⟩

end cert

/-! ### The AMD leaves the hull; C.1 -/

/-- Every pure law of the AMD puts no mass on the exit-2 leaf `(sba, 4)`.
Source: `equiv.md` EQ-9 ("`𝓛_pure(AMD) = {δ_(exit1,0), δ_(exit0,1)}`")
Kind: L -/
theorem amd_pure_law_exit2 (π : Unit → Act2) : lawOfW id (Proc.ofFun π) amd (.sba, 4) = 0 := by
  unfold lawOfW amd
  rw [Finsupp.finsetSum_apply]
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  cases hπ : π () <;> simp [Proc.ofFun, Finsupp.single_apply, hπ]

/-- **The AMD leaves the hull (EQ-12(d), Dead 2)**: its Definition-6 law at `q = 1/3` puts mass
`2/9` on the exit-2 leaf that no pure law reaches, so it is not a mixture of pure laws.
Source: `equiv.md` EQ-12(d) ("at `q = 1/3` the Definition-6 law has mass `2/9` on the exit-2
leaf"), Dead 2
Kind: P
Fidelity: exact -/
theorem amd_law_third_not_mem_LCorr :
    lawOfW id (procQ (1/3) (by norm_num) (by norm_num)) amd ∉ LCorr id amd := by
  rintro ⟨α, hα, m, π, hmix⟩
  have h1 : lawOfW id (procQ (1/3) (by norm_num) (by norm_num)) amd (.sba, 4) = 2/9 := by
    unfold lawOfW amd
    rw [Finsupp.finsetSum_apply]
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [procQ, Finsupp.single_apply]
    norm_num
  have h2 : (∑ a, m.w a • lawOfW id (Proc.ofFun (π a)) amd) (.sba, 4) = 0 := by
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro a _
    rw [Finsupp.smul_apply, amd_pure_law_exit2, smul_zero]
  rw [hmix] at h1
  rw [h1] at h2
  norm_num at h2

/-- The AMD is not hull-closed, so `⊑` is not reflexive on it: "`⊑` is a pre-order" (on all
trees) is **refuted**; the surviving neighbour is `cert_self_iff` (a pre-order on `𝓗`).
Source: `equiv.md` Dead 2 ("`AMD ⋢ AMD`")
Kind: N− -/
theorem amd_not_hullClosed : ¬ HullClosed id amd := fun h =>
  amd_law_third_not_mem_LCorr (h ⟨_, rfl⟩)

theorem amd_not_cert_self : ¬ Cert id id amd amd := fun h => amd_not_hullClosed h.hullClosed.1

/-- **C.1: `amd ∼ Rel amd`** (every `B` is `∼` its relocation).
Source: `adversary-repair.md` C.1 ("`AMD ∼ Rel(AMD)`")
Kind: N+ -/
theorem amd_sim_reloc : Sim id Prod.fst amd (relocRoot {()} amd) := sim_reloc {()} amd

/-- **C.1: `T_opt` is not `∼`-invariant** — every procedure on the relocated AMD is worth at most
`1`, while the AMD attains `4/3`: "`T_opt` is `∼`-invariant" (FR-9(iii)) is **refuted** on the
general class.
Source: `adversary-repair.md` C.1 ("`AMD ∼ Rel(AMD)`, while `max_C V = 4/3` vs `1`");
`fair-repair.md` FR-9(iii) (refuted claim)
Kind: N+ -/
theorem value_reloc_amd_le_one (C' : Proc (Unit ⊕ Unit) (actsR (fun _ => Act2) {()}) ℚ) :
    value C' (relocRoot {()} amd) ≤ 1 := by
  obtain ⟨π, hπ⟩ := value_reloc_le_pure {()} amd (fun d _ => by simp) C'
  refine hπ.trans ?_
  cases hπa : π () with
  | a =>
      have : Proc.ofFun π = procQ 1 zero_le_one le_rfl := by
        funext u; cases u; apply FinDistr.ext'; intro x
        cases x <;> simp [Proc.ofFun, procQ, hπa, FinDistr.act2]
      rw [this, amd_value]; norm_num
  | b =>
      have : Proc.ofFun π = procQ 0 le_rfl zero_le_one := by
        funext u; cases u; apply FinDistr.ext'; intro x
        cases x <;> simp [Proc.ofFun, procQ, hπa, FinDistr.act2]
      rw [this, amd_value]; norm_num

theorem c1_refuted :
    Sim id Prod.fst amd (relocRoot {()} amd) ∧
      (∀ C' : Proc (Unit ⊕ Unit) (actsR (fun _ => Act2) {()}) ℚ, value C' (relocRoot {()} amd) ≤ 1) ∧
      value (procQ (1/3) (by norm_num) (by norm_num)) amd = 4/3 :=
  ⟨amd_sim_reloc, value_reloc_amd_le_one, amd_at_third.1⟩

/-- **The surviving neighbour of C.1**: on almost-fair trees the optimum is a function of the
pure-law image — if `B ∼ B'` with both almost fair, every value on `B` is at most a pure value of
`B'` (and symmetrically).
Source: `adversary-repair.md` C.1 ("It holds restricted to almost-fair problems, where … the mixed
sup is a function of the pure-law set")
Kind: P
Fidelity: exact
Hyps: none -/
theorem sim_value_le_of_almostFair {Ω' ι' : Type} {acts' : ι' → Type} [∀ d, Fintype (acts' d)]
    [DecidableEq ι'] [∀ d, DecidableEq (acts' d)] [∀ d, Nonempty (acts' d)]
    {Ω₁ ι₁ : Type} {acts₁ : ι₁ → Type} [∀ d, Fintype (acts₁ d)] [DecidableEq ι₁]
    [∀ d, DecidableEq (acts₁ d)] {f : Ω' → Ω} {f' : Ω₁ → Ω}
    {B : Tree Ω' ι' acts' K} {B' : Tree Ω₁ ι₁ acts₁ K} (h : AlmostFair B) (hs : Sim f f' B B')
    (C : Proc ι' acts' K) : ∃ π' : (d : ι₁) → acts₁ d, value C B ≤ value (Proc.ofFun π') B' := by
  obtain ⟨π, hπ, -, -⟩ := exists_pure_max_value' B
  have hmem : lawOfW f (Proc.ofFun π) B ∈ LPure f' B' := by rw [← hs]; exact ⟨π, rfl⟩
  obtain ⟨π', hπ'⟩ := hmem
  dsimp only at hπ'
  refine ⟨π', ?_⟩
  rw [h.value_eq_value' C]
  refine (hπ C).trans (le_of_eq ?_)
  rw [value_eq_valInt f, value_eq_valInt f', hπ']

/-! ### FR-10: `T_{d,e} ∼ T_{e,d}` -/

/-- The points of FR-10's sequenced trees, with distinct labels for the two orders: `T_{d,e}`
uses `d` first and then one point `eAfter a` per first-stage answer; `T_{e,d}` uses `e` first and
then `dAfter b` (the later point *observes* the earlier one).
Source: `fair-repair.md` FR-10 ("then a per-`a` point chooses `b` knowing `pol_d = a`"); mandate
T7(c) ("while the root point differs")
Kind: D -/
inductive FR10Pt : Type
  | d
  | eAfter (a : Act2)
  | e
  | dAfter (b : Act2)
  deriving DecidableEq, Fintype

/-- `T_{d,e}`: `d` chooses `a` first, then the per-`a` point `eAfter a` chooses `b`; worlds
`(a, b)`, payoff `v a b`.
Source: `fair-repair.md` FR-10
Kind: D -/
def tde (v : Act2 → Act2 → ℚ) : Tree SeqW FR10Pt (fun _ => Act2) ℚ :=
  .decision .d fun a => .decision (.eAfter a) fun b => .leaf (a, b) (v a b)

/-- `T_{e,d}`: the mirror — `e` chooses `b` first, then the per-`b` point `dAfter b` chooses `a`.
Source: `fair-repair.md` FR-10
Kind: D -/
def ted (v : Act2 → Act2 → ℚ) : Tree SeqW FR10Pt (fun _ => Act2) ℚ :=
  .decision .e fun b => .decision (.dAfter b) fun a => .leaf (a, b) (v a b)

theorem lawOfW_tde (v : Act2 → Act2 → ℚ) (π : FR10Pt → Act2) :
    lawOfW id (Proc.ofFun π) (tde v) =
      Finsupp.single ((π .d, π (.eAfter (π .d))), v (π .d) (π (.eAfter (π .d)))) 1 := by
  rw [lawOfW_id]
  unfold tde
  simp only [contLaw_decision, contLaw_leaf, Proc.ofFun_w, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem lawOfW_ted (v : Act2 → Act2 → ℚ) (π : FR10Pt → Act2) :
    lawOfW id (Proc.ofFun π) (ted v) =
      Finsupp.single ((π (.dAfter (π .e)), π .e), v (π (.dAfter (π .e))) (π .e)) 1 := by
  rw [lawOfW_id]
  unfold ted
  simp only [contLaw_decision, contLaw_leaf, Proc.ofFun_w, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The pure laws of both sequenced trees: `{δ_{((a,b), v(a,b))} : a, b}`.
Source: `fair-repair.md` FR-10 ("laws `δ_(a,b) ⊗ δ_v(a,b)` — the same set")
Kind: L -/
theorem LPure_tde (v : Act2 → Act2 → ℚ) :
    LPure id (tde v) = Set.range fun ab : Act2 × Act2 => Finsupp.single ((ab.1, ab.2), v ab.1 ab.2) 1 := by
  ext L
  constructor
  · rintro ⟨π, rfl⟩
    exact ⟨(π .d, π (.eAfter (π .d))), (lawOfW_tde v π).symm⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨fun p => match p with | .d => a | .eAfter _ => b | .e => b | .dAfter _ => a, ?_⟩
    dsimp only
    rw [lawOfW_tde]

theorem LPure_ted (v : Act2 → Act2 → ℚ) :
    LPure id (ted v) = Set.range fun ab : Act2 × Act2 => Finsupp.single ((ab.1, ab.2), v ab.1 ab.2) 1 := by
  ext L
  constructor
  · rintro ⟨π, rfl⟩
    exact ⟨(π (.dAfter (π .e)), π .e), (lawOfW_ted v π).symm⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨fun p => match p with | .d => a | .eAfter _ => b | .e => b | .dAfter _ => a, ?_⟩
    dsimp only
    rw [lawOfW_ted]

/-- The queried points of the two sequenced trees are disjoint: `T_{d,e}` queries `d` and the
`eAfter` points, `T_{e,d}` queries `e` and the `dAfter` points ("which observes which").
Source: `fair-repair.md` FR-10
Kind: L -/
theorem tde_ted_queried_disjoint (v : Act2 → Act2 → ℚ) :
    Disjoint (queried (tde v)) (queried (ted v)) := by
  -- `queried` never reads the payoffs, so the sets are those of the payoff-`0` trees
  have h1 : queried (tde v) = queried (tde fun _ _ => 0) := rfl
  have h2 : queried (ted v) = queried (ted fun _ _ => 0) := rfl
  rw [h1, h2]
  decide

theorem tde_fibers_singleton (v : Act2 → Act2 → ℚ) :
    ∀ d, ∀ q ∈ fiber (tde v) d, ∀ q' ∈ fiber (tde v) d, q = q' := by
  intro d q hq q' hq'
  rw [mem_fiber] at hq hq'
  change Option (Σ _ : Act2, Option (Σ _ : Act2, Empty)) at q q'
  rcases q with _ | ⟨a, _ | ⟨b, e⟩⟩ <;> rcases q' with _ | ⟨a', _ | ⟨b', e'⟩⟩ <;>
    first
    | exact e.elim
    | exact e'.elim
    | rfl
    | (simp [tde] at hq hq'; subst hq; cases hq' <;> rfl)

theorem ted_fibers_singleton (v : Act2 → Act2 → ℚ) :
    ∀ d, ∀ q ∈ fiber (ted v) d, ∀ q' ∈ fiber (ted v) d, q = q' := by
  intro d q hq q' hq'
  rw [mem_fiber] at hq hq'
  change Option (Σ _ : Act2, Option (Σ _ : Act2, Empty)) at q q'
  rcases q with _ | ⟨a, _ | ⟨b, e⟩⟩ <;> rcases q' with _ | ⟨a', _ | ⟨b', e'⟩⟩ <;>
    first
    | exact e.elim
    | exact e'.elim
    | rfl
    | (simp [ted] at hq hq'; subst hq; cases hq' <;> rfl)

/-- **FR-10**: `T_{d,e} ∼ T_{e,d}` — the same pure-law set `{δ_{((a,b), v(a,b))}}` — while the
root points differ (`d` vs `e`) and the two trees' queried point sets are disjoint (which point
observes which); both are strongly fair and almost fair. The dichotomy sentence (no relation both
makes relocation an equivalence and pins the location) is prose, recorded in the findings.
Source: `fair-repair.md` FR-10 ("`T_{d,e} ∼ T_{e,d}` … while they disagree about which choice
is made first"); mandate T7(c)
Kind: N+
Fidelity: exact (the location conjuncts are in the statement, audit r1 B2) -/
theorem tde_sim_ted (v : Act2 → Act2 → ℚ) :
    Sim id id (tde v) (ted v) ∧ StronglyFair (tde v) ∧ StronglyFair (ted v) ∧
      AlmostFair (tde v) ∧ AlmostFair (ted v) ∧
      pt (tde v) none ≠ pt (ted v) none ∧ Disjoint (queried (tde v)) (queried (ted v)) := by
  have h1 : StronglyFair (tde v) := fun d q hq q' hq' => by
    rw [tde_fibers_singleton v d q hq q' hq']; exact LabIso.refl _
  have h2 : StronglyFair (ted v) := fun d q hq q' hq' => by
    rw [ted_fibers_singleton v d q hq q' hq']; exact LabIso.refl _
  refine ⟨(LPure_tde v).trans (LPure_ted v).symm, h1, h2, h1.almostFair, h2.almostFair,
    fun h => ?_, tde_ted_queried_disjoint v⟩
  have : FR10Pt.d = FR10Pt.e := h
  cases this

/-! ### E5 is licensed by `⊑` although its function-level law changes -/

/-- E5's worlds `o1`, `o2`.
Source: `equiv.md` Definitions carried (E5 `degenerate_amd`)
Kind: D -/
inductive E5W : Type
  | o1
  | o2
  deriving DecidableEq, Fintype

/-- **E5 (`degenerate_amd`)**: one point at two nested nodes; top `a → (o1, 0)`, `b →` bottom;
bottom `a → (o1, 0)`, `b → (o2, 1)`.
Source: `equiv.md` Definitions carried
Kind: D -/
def e5 : Tree E5W Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .o1 0
    | .b => .decision () fun
      | .a => .leaf .o1 0
      | .b => .leaf .o2 1

theorem e5_nested : Nested e5 () := by
  refine ⟨by decide, ⟨.b, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive e5; simp
  · unfold e5; simp

/-- E5's Definition-6 law at `q`: `(2q − q²) δ_{(o1,0)} + (1−q)² δ_{(o2,1)}`.
Source: `equiv.md` D2 (R1)
Kind: L -/
theorem lawOfW_e5 (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    lawOfW id (procQ q h0 h1) e5 =
      (2*q - q^2) • Finsupp.single (E5W.o1, (0 : ℚ)) (1 : ℚ) +
        (1 - q)^2 • Finsupp.single (E5W.o2, (1 : ℚ)) (1 : ℚ) := by
  rw [lawOfW_id]
  unfold e5
  simp only [contLaw_decision, contLaw_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
    FinDistr.act2_b]
  ext p
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> ring

/-- E5's Definition-6′ law at `w`: `w δ_{(o1,0)} + (1−w) δ_{(o2,1)}` (one seed: the second node
repeats the first draw).
Source: `equiv.md` D2 (`Rel(E5)` at root weight `w`)
Kind: L -/
theorem lawOfW'_e5 (w : ℚ) (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    lawOfW' id (procQ w h0 h1) e5 =
      w • Finsupp.single (E5W.o1, (0 : ℚ)) (1 : ℚ) + (1 - w) • Finsupp.single (E5W.o2, (1 : ℚ)) (1 : ℚ) := by
  unfold lawOfW' e5
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp only [leafLaw'_eq, draws_decision, draws_leaf, chanceWeight_decision, chanceWeight_leaf,
    world_decision, world_leaf, payoff_decision, payoff_leaf, seedFold, Function.update_self, procQ,
    FinDistr.act2_a, FinDistr.act2_b, id]
  ext p
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> (try simp_all) <;> (try ring)

/-- The relocated E5's projected law under `lift (procQ w)` is E5's shared-seed law at `w`.
Source: `seeds.md` SE-5(2); `equiv.md` D2
Kind: C -/
theorem lawOfW_reloc_e5 (w : ℚ) (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    lawOfW Prod.fst (lift {()} (procQ w h0 h1)) (relocRoot {()} e5) = lawOfW' id (procQ w h0 h1) e5 := by
  rw [lawOfW_relocRoot {()} e5 (lift {()} (procQ w h0 h1))]
  unfold lawOfW'
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [push_leafLaw {()} (procQ w h0 h1) e5 (fun d _ => by simp) ℓ]
  rfl

/-- Every one-point procedure is a `procQ`.
Source: none: infrastructure
Kind: L -/
theorem proc_eq_procQ (C : Proc Unit (fun _ => Act2) ℚ) :
    ∃ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1), C = procQ q h0 h1 := by
  refine ⟨(C ()).w .a, (C ()).nonneg .a, (C ()).w_le_one .a, ?_⟩
  funext u; cases u
  apply FinDistr.ext'
  intro x
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  cases x
  · simp [procQ]
  · simp [procQ]; linarith

/-- **E5 is licensed (EQ-12(e), Dead 1 refuted)**: `E5 ⊑ Rel(E5)` — every Definition-6 law of E5
at `q` is the relocated law at root weight `w = 2q − q² ∈ [0, 1]`.
Source: `equiv.md` EQ-12(e), D2 ("`E5 ⊑ Rel(E5)` holds")
Kind: N+
Fidelity: exact -/
theorem e5_cert_reloc : Cert id Prod.fst e5 (relocRoot {()} e5) := by
  refine ⟨(LPure_reloc {()} e5).symm, ?_, LMixed_reloc_subset_LCorr {()} e5 (fun d _ => by simp)⟩
  rintro _ ⟨C, rfl⟩
  obtain ⟨q, h0, h1, rfl⟩ := proc_eq_procQ C
  have hw0 : 0 ≤ 2*q - q^2 := by nlinarith
  have hw1 : 2*q - q^2 ≤ 1 := by nlinarith [sq_nonneg (1 - q)]
  refine ⟨lift {()} (procQ (2*q - q^2) hw0 hw1), ?_⟩
  dsimp only
  rw [lawOfW_reloc_e5, lawOfW'_e5, lawOfW_e5]
  congr 2
  ring

/-- **The function-level law of E5 changes under relocation** (image-level vs function-level): at
`q = 1/2` the input law puts `3/4` on `(o1, 0)`, the output under `lift (procQ 1/2)` puts `1/2`.
Source: `equiv.md` EQ-12(e) ("the *function-level* law changes at the same `q` (`(¾, ¼) ↦ (½, ½)`
at `q = ½`)")
Kind: N+ -/
theorem e5_function_level_changes :
    lawOfW Prod.fst (lift {()} (procQ (1/2) (by norm_num) (by norm_num))) (relocRoot {()} e5) ≠
      lawOfW id (procQ (1/2) (by norm_num) (by norm_num)) e5 := by
  intro h
  have := congrArg (fun L => L (E5W.o1, 0)) h
  rw [lawOfW_reloc_e5, lawOfW'_e5, lawOfW_e5] at this
  simp at this
  norm_num at this

end Cleanroom.Decision.DpFairnessReloc
