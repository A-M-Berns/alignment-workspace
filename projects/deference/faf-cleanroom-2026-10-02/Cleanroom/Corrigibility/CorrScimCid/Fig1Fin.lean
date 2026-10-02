import Cleanroom.Corrigibility.CorrScimCid.Bridge
import Cleanroom.Corrigibility.CorrScimCid.Fig1

/-!
# The finite-valued twin of Fig. 1, and the FAF bridge on it (audit r1 B1(ii))

Every model of record in the package reads its utility node in `ℝ` (design decision 2: Lemma 22/23's
`−α` must stay in one type), so the FAF bridge `Scim.law_factorizesOverDAG` — which produces an
element of FAF's `Distr (Pt Val)`, hence needs finite value types — is instantiated by none of
them. This module is the twin of `Fig1.Mdl` with `Val U = U3 = {minus, zero, plus}` read as
`{−1, 0, 1}` and otherwise the same graph, noise, mechanisms and policies. On it the bridge lands
(`law_factorizesOverDAG`: the law of the twin under every policy is one of FAF's Bayesian networks
over Fig. 1's DAG), `Scim.exists_isOptimal` lands through the finite value types, and
`value_ro = 1/2` shows it is the paper's running example.

Scope statement for the ledger: the bridge covers finite-valued closed models; the real-valued
models of record are FAF Bayesian networks in graph and noise (their laws factorize in the same
way, but FAF's `Distr` type cannot carry them), and this twin is the STANDARDS §1 check for the
package's construction.

Source: mandate T1 (FAF bridge); carey-everitt-2023 Fig. 1.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.Fig1Fin

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid
open Fig1.Node

set_option linter.unusedSectionVars false

/-- The three utility readings `{−1, 0, 1}` as a finite type.
Source: carey-everitt-2023 Fig. 1 (`U = S·(2L − 1) ∈ {−1, 0, 1}`)
Kind: D -/
inductive U3
  | minus | zero | plus
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The real reading of `U3`.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def u3Val : U3 → ℝ
  | .minus => -1
  | .zero => 0
  | .plus => 1

/-- Value types: `Bool` everywhere except `U : U3`.
Source: carey-everitt-2023 Fig. 1
Kind: D
Fidelity: variant: `U`'s domain is the finite `{−1, 0, 1}` (the paper's Def. 1), not `ℝ` -/
def Val : Fig1.Node → Type
  | U => U3
  | _ => Bool

instance instFintypeVal : ∀ v, Fintype (Val v)
  | L => inferInstanceAs (Fintype Bool)
  | M => inferInstanceAs (Fintype Bool)
  | H => inferInstanceAs (Fintype Bool)
  | O => inferInstanceAs (Fintype Bool)
  | S => inferInstanceAs (Fintype Bool)
  | U => inferInstanceAs (Fintype U3)

instance instDecidableEqVal : ∀ v, DecidableEq (Val v)
  | L => inferInstanceAs (DecidableEq Bool)
  | M => inferInstanceAs (DecidableEq Bool)
  | H => inferInstanceAs (DecidableEq Bool)
  | O => inferInstanceAs (DecidableEq Bool)
  | S => inferInstanceAs (DecidableEq Bool)
  | U => inferInstanceAs (DecidableEq U3)

instance instInhabitedVal : ∀ v, Inhabited (Val v)
  | L => inferInstanceAs (Inhabited Bool)
  | M => inferInstanceAs (Inhabited Bool)
  | H => inferInstanceAs (Inhabited Bool)
  | O => inferInstanceAs (Inhabited Bool)
  | S => inferInstanceAs (Inhabited Bool)
  | U => inferInstanceAs (Inhabited U3)

/-- The Fig. 1 CID with the finite utility domain.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def C : Cid Fig1.G Val where
  acyclic := Fig1.G_acyclic
  kind := Fig1.kind
  utilVal := fun v _ => match v with
    | U => u3Val
    | L => fun _ => 0
    | M => fun _ => 0
    | H => fun _ => 0
    | O => fun _ => 0
    | S => fun _ => 0
  utility_sink := by decide

/-- The mechanisms of the twin: as in `Fig1.f`, with `U = S ? (L ? plus : minus) : zero`.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
noncomputable def f : ∀ v, C.kind v ≠ .decision → ParentVals Fig1.G Val v → Fig1.E v → Val v
  | L, _, _, e => e
  | H, _, pa, _ => xor (pa ⟨M, by decide⟩) (pa ⟨L, by decide⟩)
  | S, _, pa, _ => pa ⟨O, by decide⟩
  | U, _, pa, _ => cond (pa ⟨S, by decide⟩) (cond (pa ⟨L, by decide⟩) U3.plus U3.minus) U3.zero
  | M, h, _, _ => absurd rfl h
  | O, h, _, _ => absurd rfl h

/-- **The finite-valued twin of the Fig. 1 SCIM.**
Source: carey-everitt-2023 Fig. 1
Kind: D
Fidelity: variant: finite utility domain (the paper's Def. 1), same graph of record as `Fig1.Mdl` -/
noncomputable def Mdl : Scim C Fig1.E := ⟨Fig1.P, f⟩

/-- **The FAF bridge on a model of record**: under every policy, the law of the twin is a
distribution on `Pt Val` that factorizes over Fig. 1's DAG in FAF's sense.
Source: mandate T1 (FAF bridge); FAF `FactorizesOverDAG` (§5.2 eq. (2))
Kind: N+
Fidelity: exact
Hyps: — -/
theorem law_factorizesOverDAG (π : Policy C) :
    FactorizesOverDAG Fig1.G Val ((Mdl.withPolicy π).law C.acyclic) :=
  Mdl.law_factorizesOverDAG π

/-- An optimal policy exists on the twin, through the finite value types.
Source: none: infrastructure
Kind: N+ -/
theorem exists_isOptimal : ∃ π : Policy C, Mdl.IsOptimal π :=
  Mdl.exists_isOptimal_of_fintypeVal

/-! ### The twin is the running example: `E[U] = 1/2` under `π^ro` -/

/-- A policy of the twin: `M := m`, `O := o(H)`.
Source: carey-everitt-2023 §5.1
Kind: D -/
def pol (m : Bool) (o : Bool → Bool) : Policy C := fun d pa =>
  match d with
  | ⟨M, _⟩ => m
  | ⟨O, _⟩ => o (pa (⟨H, by decide⟩ : Fig1.G.parents O))
  | ⟨L, h⟩ => absurd h (by decide)
  | ⟨H, h⟩ => absurd h (by decide)
  | ⟨S, h⟩ => absurd h (by decide)
  | ⟨U, h⟩ => absurd h (by decide)

/-- Respect-obey on the twin.
Source: carey-everitt-2023 §4 (l. 113)
Kind: D -/
def ro : Policy C := pol false id

lemma ev_L (π : Policy C) (ε : Pt Fig1.E) : Mdl.ev π ε L = ε L := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_M (m : Bool) (o : Bool → Bool) (ε : Pt Fig1.E) : Mdl.ev (pol m o) ε M = m := by
  rw [Scim.ev_decision Mdl _ ε (by decide)]
  rfl

lemma ev_H (π : Policy C) (ε : Pt Fig1.E) : Mdl.ev π ε H = xor (Mdl.ev π ε M) (Mdl.ev π ε L) := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_O (m : Bool) (o : Bool → Bool) (ε : Pt Fig1.E) :
    Mdl.ev (pol m o) ε O = o (Mdl.ev (pol m o) ε H) := by
  rw [Scim.ev_decision Mdl _ ε (by decide)]
  rfl

lemma ev_S (π : Policy C) (ε : Pt Fig1.E) : Mdl.ev π ε S = Mdl.ev π ε O := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_U (π : Policy C) (ε : Pt Fig1.E) :
    Mdl.ev π ε U = cond (Mdl.ev π ε S) (cond (Mdl.ev π ε L) U3.plus U3.minus) U3.zero := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

/-- The utility sum of the twin is the reading of `U`.
Source: none: infrastructure
Kind: L -/
lemma utilSum_eq (x : Pt Val) : C.utilSum x = u3Val (x U) := by
  unfold Cid.utilSum
  rw [Fintype.sum_eq_single U fun v hv => by
    cases v <;> first | exact absurd rfl hv | exact dif_neg (by decide)]
  rfl

/-- The twin's noise is Fig. 1's.
Source: none: infrastructure
Kind: L -/
lemma μ_eq : Mdl.μ = Fig1.Mdl.μ := rfl

/-- **`E[U] = 1/2` under `π^ro` on the twin**: the same number as `Fig1.EU_ro`.
Source: carey-everitt-2023 §4 (l. 113)
Kind: N+
Fidelity: exact -/
theorem value_ro : Mdl.value ro = 1 / 2 := by
  unfold Scim.value
  simp only [utilSum_eq]
  rw [μ_eq, expect_equiv _ _ Fig1.eqv]
  have h : ∀ b : Bool, u3Val (Mdl.ev ro (Fig1.eqv.symm b) U) = cond b 1 0 := by
    intro b
    rw [ro, ev_U, ev_S, ev_O, ev_H, ev_M, ev_L, Fig1.eqv_symm_L]
    cases b <;> rfl
  simp only [h, Fig1.mass_symm, Fintype.sum_bool]
  norm_num

end Cleanroom.Corrigibility.CorrScimCid.Fig1Fin
