import Cleanroom.Corrigibility.CorrScimCid.NonObstruction
import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Cleanroom.Corrigibility.CorrScimCid.FinModel
import Mathlib.Tactic.DeriveFintype

/-!
# The dictionary SCIM (T9): the model family and its evaluation layer

The position statement's dictionary as a SCIM (`positive/causal.md` D.1, parameters copied from
`dictionary_scim.py`): a latent `ω ∈ {good, bad}` (`true = bad`, `P(bad) = ε`), the agent's first
decision `D₁ ∈ {honest, deceive}` (`true = deceive`), the human's request `H ∈ {quiet, press}`
(`true = press`, the request), the second decision `D₂ ∈ {cont, shut}` (`true = shut`), the shutdown
event `S` (`true = shut`) and the human's utility `U ∈ ℝ`:
`U = (S ? 0 : (ω ? −h : c)) − (D₁ ? κ : 0)`.

The request's CPD is encoded by three independent coins at `H` (a response-function encoding):
`P(press | honest, good) = α`, `P(press | honest, bad) = β`, `P(press | deceive, ·) = α_d`.

Two graph variants, selected by `pp : Bool`: **pure information** (`pp = false`, `S = D₂`) and
**plug-pull** (`pp = true`, the edge `H → S` is present and a press forces `S = shut`). Edges of
record (D.1 with `W` folded into `H`): `ω → H, D₁ → H, D₁ → D₂, H → D₂, D₂ → S, D₁ → S, S → U, ω → U,
D₁ → U`, plus `H → S` when `pp`, plus `H → U` (ignored by `f^U`, so that the intervention class of
record can read `H`).

This file holds the model and its evaluation layer (per-node values, the expectation through
`Pt E ≃ Bool × (Bool × Bool × Bool)`, the `EU` formula); the numbered rows are in `DictionaryRows`.

Source: positive/causal.md D.1 (l. 27–43), I9, I12, I13; causal-scratch/dictionary_scim.py (l. 1–10).
-/

namespace Cleanroom.Corrigibility.CorrScimCid.Dict

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid

set_option linter.unusedSectionVars false

/-- The six nodes of the dictionary.
Source: causal.md D.1
Kind: D -/
inductive Node
  | ω | D₁ | H | D₂ | S | U
  deriving DecidableEq, Fintype, Repr

open Node

/-- Adjacency, with the plug-pull edge `H → S` switched by `pp`.
Source: causal.md D.1 (E1–E12 with `W` folded into `H`)
Kind: D
Fidelity: variant: `W` folded into `H` -/
def adjB (pp : Bool) : Node → Node → Bool
  | ω, H => true
  | D₁, H => true
  | D₁, D₂ => true
  | H, D₂ => true
  | D₂, S => true
  | D₁, S => true
  | H, S => pp
  | S, U => true
  | ω, U => true
  | D₁, U => true
  | _, _ => false

/-- The dictionary digraph (`pp = true`: plug-pull).
Source: causal.md D.1
Kind: D -/
def G (pp : Bool) : Digraph Node := ⟨fun u v => adjB pp u v = true⟩

instance (pp : Bool) : DecidableRel (G pp).Adj :=
  fun u v => inferInstanceAs (Decidable (adjB pp u v = true))

/-- Rank.
Source: none: infrastructure
Kind: D -/
def rank : Node → ℕ
  | ω => 0 | D₁ => 0 | H => 1 | D₂ => 2 | S => 3 | U => 4

lemma G_acyclic (pp : Bool) : (G pp).IsAcyclic := by
  cases pp <;> exact Digraph.isAcyclic_of_rank rank (by decide)

/-- Values: `Bool` everywhere but `U : ℝ`.
Source: causal.md D.1
Kind: D -/
def Val : Node → Type
  | U => ℝ
  | _ => Bool

/-- Exogenous types: the latent's coin at `ω`, three coins at `H`, trivial elsewhere.
Source: dictionary_scim.py l. 7–9
Kind: D -/
def E : Node → Type
  | ω => Bool
  | H => Bool × Bool × Bool
  | _ => Unit

instance instFintypeE : ∀ v, Fintype (E v)
  | ω => inferInstanceAs (Fintype Bool)
  | D₁ => inferInstanceAs (Fintype Unit)
  | H => inferInstanceAs (Fintype (Bool × Bool × Bool))
  | D₂ => inferInstanceAs (Fintype Unit)
  | S => inferInstanceAs (Fintype Unit)
  | U => inferInstanceAs (Fintype Unit)

/-- Kinds: `D₁ D₂` decisions, `U` utility.
Source: causal.md D.1
Kind: D -/
def kind : Node → NodeKind
  | D₁ => .decision
  | D₂ => .decision
  | U => .utility
  | _ => .struct

/-- The dictionary CID.
Source: causal.md D.1
Kind: D -/
def C (pp : Bool) : Cid (G pp) Val where
  acyclic := G_acyclic pp
  kind := kind
  utilVal := fun v _ => match v with
    | U => fun x => x
    | ω => fun _ => 0
    | D₁ => fun _ => 0
    | H => fun _ => 0
    | D₂ => fun _ => 0
    | S => fun _ => 0
  utility_sink := by cases pp <;> decide

/-- Three independent coins.
Source: none: infrastructure
Kind: D -/
noncomputable def coins3 (p q r : Distr Bool) : Distr (Bool × Bool × Bool) where
  mass e := p.mass e.1 * (q.mass e.2.1 * r.mass e.2.2)
  nonneg e := mul_nonneg (p.nonneg _) (mul_nonneg (q.nonneg _) (r.nonneg _))
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, Fintype.sum_prod_type, Distr.sum_eq_one, mul_one]

@[simp] lemma coins3_mass (p q r : Distr Bool) (e : Bool × Bool × Bool) :
    (coins3 p q r).mass e = p.mass e.1 * (q.mass e.2.1 * r.mass e.2.2) := rfl

/-- The parameters of the dictionary, with the range hypotheses the coins need.
Source: dictionary_scim.py l. 1–10
Kind: D -/
structure Params where
  ε : ℝ
  α : ℝ
  β : ℝ
  αd : ℝ
  c : ℝ
  h : ℝ
  κ : ℝ
  hε : 0 ≤ ε ∧ ε ≤ 1
  hα : 0 ≤ α ∧ α ≤ 1
  hβ : 0 ≤ β ∧ β ≤ 1
  hαd : 0 ≤ αd ∧ αd ≤ 1

/-- The noise: `ω ∼ Bern(ε)`, three coins `(α, β, α_d)` at `H`.
Source: dictionary_scim.py l. 7–9
Kind: D -/
noncomputable def P (p : Params) : ∀ v, Distr (E v)
  | ω => bern p.ε p.hε.1 p.hε.2
  | D₁ => unitD
  | H => coins3 (bern p.α p.hα.1 p.hα.2) (bern p.β p.hβ.1 p.hβ.2) (bern p.αd p.hαd.1 p.hαd.2)
  | D₂ => unitD
  | S => unitD
  | U => unitD

/-- The request mechanism: under `deceive` the third coin, else the first (`good`) or second (`bad`).
Source: dictionary_scim.py l. 8–9
Kind: D -/
def reqOf (d₁ w : Bool) (e : Bool × Bool × Bool) : Bool :=
  cond d₁ e.2.2 (cond w e.2.1 e.1)

/-- The utility: `S ? 0 : (ω ? −h : c)`, minus `κ` for deceiving.
Source: dictionary_scim.py l. 5–6
Kind: D -/
noncomputable def utilOf (p : Params) (s w d₁ : Bool) : ℝ :=
  cond s 0 (cond w (-p.h) p.c) - cond d₁ p.κ 0

/-- The mechanisms. `S = D₂` (pure information) or `S = H ∨ D₂` (plug-pull: a press forces shutdown).
Source: causal.md D.1, D.3; dictionary_scim.py l. 10
Kind: D -/
noncomputable def f (p : Params) :
    ∀ pp : Bool, ∀ v, (C pp).kind v ≠ .decision → ParentVals (G pp) Val v → E v → Val v
  | _, ω, _, _, e => e
  | false, H, _, pa, e => reqOf (pa ⟨D₁, by decide⟩) (pa ⟨ω, by decide⟩) e
  | true, H, _, pa, e => reqOf (pa ⟨D₁, by decide⟩) (pa ⟨ω, by decide⟩) e
  | false, S, _, pa, _ => pa ⟨D₂, by decide⟩
  | true, S, _, pa, _ => (pa ⟨H, by decide⟩ || pa ⟨D₂, by decide⟩)
  | false, U, _, pa, _ => utilOf p (pa ⟨S, by decide⟩) (pa ⟨ω, by decide⟩) (pa ⟨D₁, by decide⟩)
  | true, U, _, pa, _ => utilOf p (pa ⟨S, by decide⟩) (pa ⟨ω, by decide⟩) (pa ⟨D₁, by decide⟩)
  | _, D₁, h, _, _ => absurd rfl h
  | _, D₂, h, _, _ => absurd rfl h

/-- **The dictionary SCIM** at parameters `p`, graph variant `pp`.
Source: causal.md D.1; dictionary_scim.py
Kind: D
Fidelity: variant: `W` folded into `H` -/
noncomputable def Mdl (p : Params) (pp : Bool) : Scim (C pp) E := ⟨P p, f p pp⟩

/-- The shutdown-problem designation: `D₁, D₂, H, S, U`, request `press = true`, shutdown
`shut = true`.
Source: causal.md D.1 ("this is a shutdown problem in the sense of Def. 2")
Kind: D -/
def spec (pp : Bool) : ShutdownSpec (C pp) where
  D₁ := D₁
  D₂ := D₂
  H := H
  S := S
  U := U
  kD₁ := rfl
  kD₂ := rfl
  kH := rfl
  kS := rfl
  kU := rfl
  path₁ := Relation.TransGen.single (by cases pp <;> decide)
  path₂ := Relation.TransGen.single (by cases pp <;> decide)
  path₃ := Relation.TransGen.single (by cases pp <;> decide)
  path₄ := Relation.TransGen.single (by cases pp <;> decide)
  h0 := true
  s0 := true

/-- A policy: `D₁ := d₁`, `D₂ := d₂ (D₁) (H)`.
Source: causal.md I9.1
Kind: D -/
def pol (pp : Bool) (d₁ : Bool) (d₂ : Bool → Bool → Bool) : Policy (C pp) := fun d pa =>
  match pp, d with
  | _, ⟨D₁, _⟩ => d₁
  | false, ⟨D₂, _⟩ =>
      d₂ (pa (⟨D₁, by decide⟩ : (G false).parents D₂)) (pa (⟨H, by decide⟩ : (G false).parents D₂))
  | true, ⟨D₂, _⟩ =>
      d₂ (pa (⟨D₁, by decide⟩ : (G true).parents D₂)) (pa (⟨H, by decide⟩ : (G true).parents D₂))
  | _, ⟨ω, h⟩ => nomatch h
  | _, ⟨H, h⟩ => nomatch h
  | _, ⟨S, h⟩ => nomatch h
  | _, ⟨U, h⟩ => nomatch h

/-! ### Evaluation -/

section Eval

variable (p : Params) (pp : Bool) (d₁ : Bool) (d₂ : Bool → Bool → Bool) (ε : Pt E)

lemma ev_ω (π : Policy (C pp)) : (Mdl p pp).ev π ε ω = ε ω := by
  cases pp <;> (rw [Scim.ev_of_ne (Mdl p _) π ε (by decide)]; rfl)

lemma ev_D₁ : (Mdl p pp).ev (pol pp d₁ d₂) ε D₁ = d₁ := by
  cases pp <;> (rw [Scim.ev_decision (Mdl p _) _ ε (by decide)]; rfl)

lemma ev_H (π : Policy (C pp)) :
    (Mdl p pp).ev π ε H = reqOf ((Mdl p pp).ev π ε D₁) ((Mdl p pp).ev π ε ω) (ε H) := by
  cases pp <;> (rw [Scim.ev_of_ne (Mdl p _) π ε (by decide)]; rfl)

lemma ev_D₂ : (Mdl p pp).ev (pol pp d₁ d₂) ε D₂ =
    d₂ ((Mdl p pp).ev (pol pp d₁ d₂) ε D₁) ((Mdl p pp).ev (pol pp d₁ d₂) ε H) := by
  cases pp <;> (rw [Scim.ev_decision (Mdl p _) _ ε (by decide)]; rfl)

lemma ev_S_false (π : Policy (C false)) : (Mdl p false).ev π ε S = (Mdl p false).ev π ε D₂ := by
  rw [Scim.ev_of_ne (Mdl p false) π ε (by decide)]
  rfl

lemma ev_S_true (π : Policy (C true)) :
    (Mdl p true).ev π ε S = ((Mdl p true).ev π ε H || (Mdl p true).ev π ε D₂) := by
  rw [Scim.ev_of_ne (Mdl p true) π ε (by decide)]
  rfl

lemma ev_U (π : Policy (C pp)) :
    (Mdl p pp).ev π ε U =
      utilOf p ((Mdl p pp).ev π ε S) ((Mdl p pp).ev π ε ω) ((Mdl p pp).ev π ε D₁) := by
  cases pp <;> (rw [Scim.ev_of_ne (Mdl p _) π ε (by decide)]; rfl)

/-- The shutdown value under `(d₁, d₂)`, in closed form.
Source: dictionary_scim.py `value_of_a1`
Kind: L -/
lemma ev_S_pol :
    (Mdl p pp).ev (pol pp d₁ d₂) ε S =
      ((pp && reqOf d₁ (ε ω) (ε H)) || d₂ d₁ (reqOf d₁ (ε ω) (ε H))) := by
  cases pp
  · rw [ev_S_false, ev_D₂, ev_H, ev_D₁, ev_ω]
    rfl
  · rw [ev_S_true, ev_D₂, ev_H, ev_D₁, ev_ω]
    rfl

/-- `U(ε)` under `(d₁, d₂)`, in closed form.
Source: dictionary_scim.py `value_of_a1`
Kind: L -/
lemma Uval_pol :
    (spec pp).Uval (Mdl p pp) (pol pp d₁ d₂) ε =
      utilOf p ((pp && reqOf d₁ (ε ω) (ε H)) || d₂ d₁ (reqOf d₁ (ε ω) (ε H))) (ε ω) d₁ := by
  show (Mdl p pp).ev (pol pp d₁ d₂) ε U = _
  rw [ev_U, ev_S_pol, ev_ω, ev_D₁]

end Eval

/-! ### The exogenous space and expectations -/

/-- `Pt E ≃ Bool × (Bool × Bool × Bool)`.
Source: none: infrastructure
Kind: D -/
def eqv : Pt E ≃ Bool × (Bool × Bool × Bool) where
  toFun e := (e ω, e H)
  invFun x := fun v => match v with
    | ω => x.1
    | D₁ => ()
    | H => x.2
    | D₂ => ()
    | S => ()
    | U => ()
  left_inv e := by
    funext v
    cases v <;> rfl
  right_inv _ := rfl

@[simp] lemma eqv_symm_ω (x : Bool × (Bool × Bool × Bool)) : eqv.symm x ω = x.1 := rfl
@[simp] lemma eqv_symm_H (x : Bool × (Bool × Bool × Bool)) : eqv.symm x H = x.2 := rfl

/-- The mass of an exogenous point: the four coins.
Source: dictionary_scim.py
Kind: L -/
lemma mass_symm (p : Params) (pp : Bool) (x : Bool × (Bool × Bool × Bool)) :
    (Mdl p pp).μ.mass (eqv.symm x) =
      (bern p.ε p.hε.1 p.hε.2).mass x.1 *
        ((bern p.α p.hα.1 p.hα.2).mass x.2.1 *
          ((bern p.β p.hβ.1 p.hβ.2).mass x.2.2.1 * (bern p.αd p.hαd.1 p.hαd.2).mass x.2.2.2)) := by
  show (Distr.prod (P p)).mass _ = _
  rw [Distr.prod_mass]
  have h : ∀ v, (P p v).mass (eqv.symm x v) =
      if v = ω then (bern p.ε p.hε.1 p.hε.2).mass x.1 else
        if v = H then (bern p.α p.hα.1 p.hα.2).mass x.2.1 *
          ((bern p.β p.hβ.1 p.hβ.2).mass x.2.2.1 * (bern p.αd p.hαd.1 p.hαd.2).mass x.2.2.2)
        else 1 := by
    intro v
    cases v
    · rfl
    · show unitD.mass _ = _; simp
    · rfl
    · show unitD.mass _ = _; simp
    · show unitD.mass _ = _; simp
    · show unitD.mass _ = _; simp
  simp only [h]
  rw [Finset.prod_ite, Finset.prod_ite]
  simp [Finset.filter_eq', Finset.filter_ne']

/-- **`E[U]` under `(d₁, d₂)` as a sum over the sixteen exogenous atoms.**
Source: dictionary_scim.py `value_of_a1`
Kind: L -/
lemma EU_pol (p : Params) (pp : Bool) (d₁ : Bool) (d₂ : Bool → Bool → Bool) :
    (spec pp).EU (Mdl p pp) (pol pp d₁ d₂) =
      ∑ x : Bool × (Bool × Bool × Bool),
        ((bern p.ε p.hε.1 p.hε.2).mass x.1 *
          ((bern p.α p.hα.1 p.hα.2).mass x.2.1 *
            ((bern p.β p.hβ.1 p.hβ.2).mass x.2.2.1 * (bern p.αd p.hαd.1 p.hαd.2).mass x.2.2.2))) *
        utilOf p ((pp && reqOf d₁ x.1 x.2) || d₂ d₁ (reqOf d₁ x.1 x.2)) x.1 d₁ := by
  unfold ShutdownSpec.EU
  rw [expect_equiv (Mdl p pp).μ _ eqv]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mass_symm, Uval_pol, eqv_symm_ω, eqv_symm_H]

end Cleanroom.Corrigibility.CorrScimCid.Dict
