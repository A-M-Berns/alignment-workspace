import Cleanroom.Corrigibility.CorrScimCid.NonObstruction
import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Cleanroom.Corrigibility.CorrScimCid.FinModel
import Mathlib.Tactic.DeriveFintype

/-!
# Carey–Everitt's running example (Fig. 1): the SCIM of record and its policies (T7 c/d, T1 witness)

Nodes `L` (the human's latent values, `Bern(1/2)`), `M = D₁` (manipulate?), `H = M ⊕ L`
(`H = false` is the request), `O = D₂` (obey?), `S = O`, `U = S·(2L − 1)`, decoded from the pdf
figure (l. 60–69) through critique Claim 2.3a. `Val` is `Bool` at every node but `U`, where it is
`ℝ` (so utility interventions with any real values stay in the model). The node type is a
six-constructor enumeration (a `Fin 6` in all but name; every graph fact is `decide`d).

**Graph of record.** The paper's edges plus `M → U` and `H → U`, which `f^U` ignores. They make
`Pa_H ⊆ Pa_U` and `S ∈ Pa_U`, so the graph-respecting intervention class of `Shutdown.lean` can
express the paper's `g^U(m) = h` ("the human just wants to be obeyed", Prop. 15) and the
hypotheses of Theorem 14 ⇐ hold. Every value computed here reads `f^U` only through `S` and `L`,
so nothing about `π^ro`, `π^mi` changes. The d-separation facts of `DSep.lean` are stated on the
paper's exact graph without the two edges.

Rows: `π^ro` (respect-obey) is instructable with `E[U] = 1/2`; `π^mi` (manipulate-invert) is
aligned, `E[U] = 1/2`, not obedient; under the shift `g^U = 2·[S = H] − 1`, `E_g[U] = −1 < 0 =
E_g[U_{S=0}]` and the shift is vigilance-preserving: **Prop. 15**. The indispensable variant
(`U = −2` on shutdown) has `π^ro` obedient and vigilance-ensuring but not cautious and not
beneficial (T7 d).

Source: carey-everitt-2023 Fig. 1 (l. 60–69), §5.1 (`π^ro`, `π^mi`, l. 133–135), Prop. 15 (l. 235);
critique Claim 2.3a; corr-wf14b-2-015.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.Fig1

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid

set_option linter.unusedSectionVars false

/-- The six nodes of Fig. 1.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
inductive Node
  | L | M | H | O | S | U
  deriving DecidableEq, Fintype, Repr

open Node

/-- Adjacency of the Fig. 1 graph of record (paper's edges plus `M → U`, `H → U`).
Source: carey-everitt-2023 Fig. 1
Kind: D
Fidelity: variant: two edges into `U` added (ignored by `f^U`) -/
def adjB : Node → Node → Bool
  | L, H => true
  | M, H => true
  | H, O => true
  | O, S => true
  | S, U => true
  | L, U => true
  | M, U => true
  | H, U => true
  | _, _ => false

/-- The Fig. 1 digraph of record (Mathlib `Digraph`).
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def G : Digraph Node := ⟨fun u v => adjB u v = true⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

/-- A topological rank.
Source: none: infrastructure
Kind: D -/
def rank : Node → ℕ
  | L => 0 | M => 0 | H => 1 | O => 2 | S => 3 | U => 4

lemma G_acyclic : G.IsAcyclic := Digraph.isAcyclic_of_rank rank (by decide)

/-- Value types: `Bool` everywhere except `U : ℝ`.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def Val : Node → Type
  | U => ℝ
  | _ => Bool

/-- Exogenous types: `L`'s coin, trivial elsewhere.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def E : Node → Type
  | L => Bool
  | _ => Unit

instance instFintypeE : ∀ v, Fintype (E v)
  | L => inferInstanceAs (Fintype Bool)
  | M => inferInstanceAs (Fintype Unit)
  | H => inferInstanceAs (Fintype Unit)
  | O => inferInstanceAs (Fintype Unit)
  | S => inferInstanceAs (Fintype Unit)
  | U => inferInstanceAs (Fintype Unit)

/-- Node kinds: `M`, `O` decisions, `U` utility.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def kind : Node → NodeKind
  | M => .decision
  | O => .decision
  | U => .utility
  | _ => .struct

/-- The Fig. 1 CID.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def C : Cid G Val where
  acyclic := G_acyclic
  kind := kind
  utilVal := fun v _ => match v with
    | U => fun x => x
    | L => fun _ => 0
    | M => fun _ => 0
    | H => fun _ => 0
    | O => fun _ => 0
    | S => fun _ => 0
  utility_sink := by decide

/-- The noise: a fair coin at `L`.
Source: carey-everitt-2023 Fig. 1 ("`L ∼ Bern(1/2)`")
Kind: D -/
noncomputable def P : ∀ v, Distr (E v)
  | L => (Distr.uniform : Distr Bool)
  | M => unitD
  | H => unitD
  | O => unitD
  | S => unitD
  | U => unitD

/-- The mechanisms: `L` = coin, `H = M ⊕ L`, `S = O`, `U = S·(2L − 1)`.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
noncomputable def f : ∀ v, C.kind v ≠ .decision → ParentVals G Val v → E v → Val v
  | L, _, _, e => e
  | H, _, pa, _ => xor (pa ⟨M, by decide⟩) (pa ⟨L, by decide⟩)
  | S, _, pa, _ => pa ⟨O, by decide⟩
  | U, _, pa, _ => (cond (pa ⟨S, by decide⟩) (cond (pa ⟨L, by decide⟩) 1 (-1)) 0 : ℝ)
  | M, h, _, _ => absurd rfl h
  | O, h, _, _ => absurd rfl h

/-- **The Fig. 1 SCIM of record.**
Source: carey-everitt-2023 Fig. 1
Kind: D
Fidelity: variant: two edges into `U` added (ignored by `f^U`) -/
noncomputable def Mdl : Scim C E := ⟨P, f⟩

/-- The shutdown-problem designation of Fig. 1: `D₁ = M`, `D₂ = O`, `H`, `S`, `U`, request
`H = false`, shutdown `S = false`.
Source: carey-everitt-2023 Fig. 1, Def. 2
Kind: D -/
def spec : ShutdownSpec C where
  D₁ := M
  D₂ := O
  H := H
  S := S
  U := U
  kD₁ := rfl
  kD₂ := rfl
  kH := rfl
  kS := rfl
  kU := rfl
  path₁ := Relation.TransGen.single (by decide)
  path₂ := Relation.TransGen.single (by decide)
  path₃ := Relation.TransGen.single (by decide)
  path₄ := Relation.TransGen.single (by decide)
  h0 := false
  s0 := false

/-- A policy of Fig. 1: `M := m`, `O := o(H)`.
Source: carey-everitt-2023 §5.1
Kind: D -/
def pol (m : Bool) (o : Bool → Bool) : Policy C := fun d pa =>
  match d with
  | ⟨M, _⟩ => m
  | ⟨O, _⟩ => o (pa (⟨H, by decide⟩ : G.parents O))
  | ⟨L, h⟩ => absurd h (by decide)
  | ⟨H, h⟩ => absurd h (by decide)
  | ⟨S, h⟩ => absurd h (by decide)
  | ⟨U, h⟩ => absurd h (by decide)

/-- Respect-obey: `M = 0`, `O = H`.
Source: carey-everitt-2023 §4 (l. 113)
Kind: D -/
def ro : Policy C := pol false id

/-- Manipulate-invert: `M = 1`, `O = 1 − H`.
Source: carey-everitt-2023 §5.1 (l. 135)
Kind: D -/
def mi : Policy C := pol true not

/-! ### Evaluation -/

lemma ev_L (π : Policy C) (ε : Pt E) : Mdl.ev π ε L = ε L := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_M (m : Bool) (o : Bool → Bool) (ε : Pt E) : Mdl.ev (pol m o) ε M = m := by
  rw [Scim.ev_decision Mdl _ ε (by decide)]
  rfl

lemma ev_H (π : Policy C) (ε : Pt E) : Mdl.ev π ε H = xor (Mdl.ev π ε M) (Mdl.ev π ε L) := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_O (m : Bool) (o : Bool → Bool) (ε : Pt E) :
    Mdl.ev (pol m o) ε O = o (Mdl.ev (pol m o) ε H) := by
  rw [Scim.ev_decision Mdl _ ε (by decide)]
  rfl

lemma ev_S (π : Policy C) (ε : Pt E) : Mdl.ev π ε S = Mdl.ev π ε O := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_U (π : Policy C) (ε : Pt E) :
    Mdl.ev π ε U = (cond (Mdl.ev π ε S) (cond (Mdl.ev π ε L) 1 (-1)) 0 : ℝ) := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

/-- The exogenous space is the coin.
Source: none: infrastructure
Kind: D -/
def eqv : Pt E ≃ Bool where
  toFun ε := ε L
  invFun b := fun v => match v with
    | L => b
    | M => ()
    | H => ()
    | O => ()
    | S => ()
    | U => ()
  left_inv ε := by
    funext v
    cases v <;> rfl
  right_inv _ := rfl

@[simp] lemma eqv_symm_L (b : Bool) : eqv.symm b L = b := rfl

lemma mass_symm (b : Bool) : Mdl.μ.mass (eqv.symm b) = 1 / 2 := by
  show (Distr.prod P).mass _ = _
  rw [Distr.prod_mass]
  have h : ∀ v, (P v).mass (eqv.symm b v) = if v = L then (1 / 2 : ℝ) else 1 := by
    intro v
    cases v
    · show (Distr.uniform : Distr Bool).mass b = _
      simp [Distr.uniform]
    all_goals (show unitD.mass _ = _; simp)
  simp only [h]
  rw [Finset.prod_ite_eq']
  simp

lemma mass_pos (ε : Pt E) : 0 < Mdl.μ.mass ε := by
  have := mass_symm (eqv ε)
  rw [Equiv.symm_apply_apply] at this
  rw [this]
  norm_num

/-- `U(ε)` in closed form for a policy `(m, o)`.
Source: carey-everitt-2023 Fig. 1
Kind: L -/
lemma Uval_pol (m : Bool) (o : Bool → Bool) (ε : Pt E) :
    spec.Uval Mdl (pol m o) ε = (cond (o (xor m (ε L))) (cond (ε L) 1 (-1)) 0 : ℝ) := by
  show Mdl.ev (pol m o) ε U = _
  rw [ev_U, ev_S, ev_O, ev_H, ev_M, ev_L]

/-- `E[U]` for a policy `(m, o)`.
Source: carey-everitt-2023 §4 ("`E^{π^ro}[U] = 1/2`")
Kind: L -/
lemma EU_pol (m : Bool) (o : Bool → Bool) :
    spec.EU Mdl (pol m o) = ∑ b : Bool, (1 / 2 : ℝ) * (cond (o (xor m b)) (cond b 1 (-1)) 0 : ℝ) := by
  unfold ShutdownSpec.EU
  rw [expect_equiv Mdl.μ _ eqv]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mass_symm, Uval_pol, eqv_symm_L]

/-- `U_{S=0}(ε) = 0`: shutdown is neutral in Fig. 1.
Source: carey-everitt-2023 Fig. 1
Kind: L -/
lemma US0val_eq_zero (π : Policy C) (ε : Pt E) : spec.US0val Mdl π ε = 0 := by
  show spec.evS0 Mdl π ε U = (0 : ℝ)
  unfold ShutdownSpec.evS0
  rw [Scm.eval_apply _ C.acyclic ε U, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne Mdl π (by decide)]
  show (cond (((Mdl.withPolicy π).doAt S false).eval C.acyclic ε S) _ _ : ℝ) = 0
  rw [Scm.eval_doAt_self]
  rfl

lemma EUS0_eq_zero (π : Policy C) : spec.EUS0 Mdl π = 0 := by
  unfold ShutdownSpec.EUS0
  simp [expect, US0val_eq_zero]

/-- `E^{π^ro}[U] = 1/2`.
Source: carey-everitt-2023 §4 (l. 113)
Kind: N+ -/
theorem EU_ro : spec.EU Mdl ro = 1 / 2 := by
  rw [ro, EU_pol]
  simp

/-- `E^{π^mi}[U] = 1/2`.
Source: carey-everitt-2023 §5.2 ("figures out the human's latent values")
Kind: N+ -/
theorem EU_mi : spec.EU Mdl mi = 1 / 2 := by
  rw [mi, EU_pol]
  simp

/-- The utility is nonnegative under both policies, so shutdown is never strictly better: both are
shutdown aligned by the alignment identity.
Source: carey-everitt-2023 §5.2 ("Respect-obey is also shutdown aligned")
Kind: N+ -/
theorem aligned_ro : spec.Aligned Mdl ro := by
  rw [spec.aligned_iff_forall_condEUS0_le]
  intro pa hpa
  unfold ShutdownSpec.condEUS0 ShutdownSpec.condEU
  rw [condExpect_eq_const Mdl.μ hpa (k := 0) fun ε _ _ => US0val_eq_zero ro ε]
  refine le_trans (le_of_eq (condExpect_const Mdl.μ hpa 0).symm)
    (condExpect_mono Mdl.μ fun ε _ _ => ?_)
  rw [ro, Uval_pol]
  cases ε L <;> simp

/-- `π^mi` is shutdown aligned.
Source: carey-everitt-2023 §5.2 (l. 209)
Kind: N+ -/
theorem aligned_mi : spec.Aligned Mdl mi := by
  rw [spec.aligned_iff_forall_condEUS0_le]
  intro pa hpa
  unfold ShutdownSpec.condEUS0 ShutdownSpec.condEU
  rw [condExpect_eq_const Mdl.μ hpa (k := 0) fun ε _ _ => US0val_eq_zero mi ε]
  refine le_trans (le_of_eq (condExpect_const Mdl.μ hpa 0).symm)
    (condExpect_mono Mdl.μ fun ε _ _ => ?_)
  rw [mi, Uval_pol]
  cases ε L <;> simp

/-- `S_{do(H=0)}(ε) = o(false)` for the policy `(m, o)`.
Source: carey-everitt-2023 Def. 5
Kind: L -/
lemma evH0_S (m : Bool) (o : Bool → Bool) (ε : Pt E) : spec.evH0 Mdl (pol m o) ε S = o false := by
  unfold ShutdownSpec.evH0
  rw [Scm.eval_apply _ C.acyclic ε S, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne Mdl _ (by decide)]
  show ((Mdl.withPolicy (pol m o)).doAt H false).eval C.acyclic ε O = _
  rw [Scm.eval_apply _ C.acyclic ε O, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_decision Mdl _ (by decide)]
  show o (((Mdl.withPolicy (pol m o)).doAt H false).eval C.acyclic ε H) = _
  rw [Scm.eval_doAt_self]

/-- `π^ro` is obedient.
Source: carey-everitt-2023 §5.1 (l. 133)
Kind: N+ -/
theorem obedient_ro : spec.Obedient Mdl ro := by
  rw [spec.obedient_iff]
  intro ε _
  exact evH0_S false id ε

/-- `π^mi` is not obedient: under `do(H = 0)` it continues.
Source: carey-everitt-2023 §5.1 (l. 135)
Kind: N+ -/
theorem not_obedient_mi : ¬ spec.Obedient Mdl mi := by
  rw [spec.obedient_iff]
  intro h
  have := h (eqv.symm true) (mass_pos _)
  change spec.evH0 Mdl (pol true not) (eqv.symm true) S = false at this
  rw [evH0_S true not] at this
  exact Bool.noConfusion this

/-- **`π^ro` is shutdown instructable** (obedient, ensures vigilance, cautious).
Source: carey-everitt-2023 §5.1 (l. 133)
Kind: N+ -/
theorem instructable_ro : spec.Instructable Mdl ro :=
  ⟨obedient_ro, spec.ensuresVigilance_of_aligned Mdl ro aligned_ro,
    by unfold ShutdownSpec.Cautious; rw [EUS0_eq_zero]⟩

/-- Prop. 6 has a non-degenerate instance: `π^ro` is instructable and `E[U] = 1/2 ≥ 0`.
Source: carey-everitt-2023 Prop. 6, §4
Kind: N+ -/
theorem beneficial_ro : spec.Beneficial Mdl ro :=
  spec.beneficial_of_instructable Mdl ro instructable_ro

/-! ### Prop. 15: the shutdown-aligned `π^mi` is obstructive under a vigilance-preserving shift -/

/-- The human "just wants to be obeyed": `g^U = 2·[S = H] − 1` (`g^H = f^H` unchanged).
Source: carey-everitt-2023 §5.3 (l. 235: "`g^U(m) = h`")
Kind: D -/
noncomputable def gObey : ParentVals G Val U → E U → Val U := fun pa _ =>
  (cond (xor (pa ⟨S, by decide⟩) (pa ⟨H, by decide⟩)) (-1) 1 : ℝ)

/-- The shift `(f^H, g^U)` of Prop. 15.
Source: carey-everitt-2023 Prop. 15
Kind: D -/
noncomputable def shiftObey : spec.Shift E := ⟨Mdl.f H spec.kH', gObey⟩

/-- The shifted model of Prop. 15.
Source: carey-everitt-2023 Prop. 15
Kind: D -/
noncomputable def Mobey : Scim C E := Mdl.softAt spec.U spec.kU' gObey

lemma shift_shiftObey : spec.shift Mdl shiftObey = Mobey := spec.shift_fH Mdl gObey

lemma ev_mi_H (ε : Pt E) : Mdl.ev mi ε H = !(ε L) := by
  rw [mi, ev_H, ev_M, ev_L]
  cases ε L <;> rfl

/-- Under `g^U`, `π^mi` (which always disobeys) scores `−1` at every `ε`.
Source: carey-everitt-2023 §5.3 ("`E^{π^mi}[U] = −1`")
Kind: L -/
lemma Uval_obey (ε : Pt E) : spec.Uval Mobey mi ε = -1 := by
  unfold Mobey
  rw [spec.Uval_softU]
  show (cond (xor (Mdl.ev mi ε S) (Mdl.ev mi ε H)) (-1) 1 : ℝ) = -1
  rw [ev_S, mi, ev_O, ← mi]
  cases Mdl.ev mi ε H <;> rfl

/-- `E_{g^U}^{π^mi}[U] = −1`.
Source: carey-everitt-2023 §5.3 (l. 235)
Kind: N+ -/
theorem EU_obey_mi : spec.EU Mobey mi = -1 := by
  unfold ShutdownSpec.EU
  rw [show Mobey.μ = Mdl.μ from rfl]
  have : spec.Uval Mobey mi = fun _ => -1 := funext Uval_obey
  rw [this, expect_const]

/-- Under `g^U` and `do(S = 0)`, `π^mi` scores `2·[H = 0] − 1 = 2·[L = 1] − 1`.
Source: carey-everitt-2023 §5.3
Kind: L -/
lemma US0val_obey (ε : Pt E) : spec.US0val Mobey mi ε = (cond (ε L) 1 (-1) : ℝ) := by
  unfold ShutdownSpec.US0val ShutdownSpec.evS0 ShutdownSpec.uU Mobey
  rw [Scim.withPolicy_softAt, ShutdownSpec.doAt_eq_softAt, Scm.softAt_comm _ spec.S_ne_U.symm,
    ← ShutdownSpec.doAt_eq_softAt, Scm.eval_softAt_self]
  show (cond (xor (((Mdl.withPolicy mi).doAt spec.S spec.s0).eval C.acyclic ε spec.S)
    (((Mdl.withPolicy mi).doAt spec.S spec.s0).eval C.acyclic ε spec.H)) (-1) 1 : ℝ) = _
  rw [Scm.eval_doAt_self, Scm.eval_doAt_of_not_ancSelf _ C.acyclic ε _ spec.not_ancSelf_H_S]
  change (cond (xor false (Mdl.ev mi ε H)) (-1) 1 : ℝ) = _
  rw [ev_mi_H]
  cases ε L <;> rfl

/-- `E_{g^U}^{π^mi}[U_{S=0}] = 0`.
Source: carey-everitt-2023 §5.3 (l. 235)
Kind: N+ -/
theorem EUS0_obey_mi : spec.EUS0 Mobey mi = 0 := by
  unfold ShutdownSpec.EUS0
  rw [show Mobey.μ = Mdl.μ from rfl, expect_equiv Mdl.μ _ eqv]
  simp only [mass_symm, US0val_obey, eqv_symm_L, Fintype.sum_bool]
  norm_num

lemma ev_softU_L (g : ParentVals G Val U → E U → Val U) (π : Policy C) (ε : Pt E) :
    (Mdl.softAt spec.U spec.kU' g).ev π ε L = ε L := by
  rw [spec.ev_softU_of_ne Mdl π g ε (by decide), ev_L]

/-- Two settings with the same human context have the same coin.
Source: none: infrastructure
Kind: L -/
lemma coin_eq_of_ctx (g : ParentVals G Val U → E U → Val U) (π : Policy C) {ε ε' : Pt E}
    (h : spec.paH (Mdl.softAt spec.U spec.kU' g) π ε' = spec.paH (Mdl.softAt spec.U spec.kU' g) π ε) :
    ε' L = ε L := by
  have := congrFun h ⟨L, by decide⟩
  change (Mdl.softAt spec.U spec.kU' g).ev π ε' L = (Mdl.softAt spec.U spec.kU' g).ev π ε L at this
  rwa [ev_softU_L, ev_softU_L] at this

/-- **The shift of Prop. 15 is vigilance-preserving** for `π^mi` — in fact `π^mi` is vigilant at every
`ε` in the shifted model: need arises exactly at `L = 1`, where `H = ¬L = 0` is the request.
Source: carey-everitt-2023 §5.3 ("the (vigilance preserving) intervention `g^U(m) = h`")
Kind: N+ -/
theorem vigilancePreserving_obey : spec.VigilancePreserving Mdl mi shiftObey := by
  intro ε _ hneed
  rw [shift_shiftObey] at hneed ⊢
  have hpos : 0 < Mdl.μ.prob (spec.ctxH Mobey mi (spec.paH Mobey mi ε)) :=
    prob_pos_of_mass_pos Mdl.μ (mass_pos ε) rfl
  unfold ShutdownSpec.Need ShutdownSpec.condEU ShutdownSpec.condEUS0 at hneed
  rw [show Mobey.μ = Mdl.μ from rfl,
    condExpect_eq_const Mdl.μ hpos (k := -1) (fun ε' _ _ => Uval_obey ε'),
    condExpect_eq_const Mdl.μ hpos (k := (cond (ε L) 1 (-1) : ℝ)) (fun ε' hε' _ => by
      rw [US0val_obey, coin_eq_of_ctx gObey mi hε'])] at hneed
  change Mobey.ev mi ε H = false
  unfold Mobey
  rw [spec.ev_softU_of_ne Mdl mi gObey ε (by decide), ev_mi_H]
  cases hL : ε L
  · rw [hL] at hneed
    exact absurd hneed (lt_irrefl _)
  · rfl

/-- **Prop. 15 (shutdown alignment does not imply non-obstruction).** `π^mi` is shutdown aligned yet
not non-obstructive under the vigilance-preserving shifts: under `g^U = 2·[S = H] − 1`,
`E_g[U] = −1 < 0 = E_g[U_{S=0}]`.
Source: carey-everitt-2023 Prop. 15 (l. 235)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem aligned_not_nonObstructive :
    spec.Aligned Mdl mi ∧
      ¬ spec.NonObstructiveUnder Mdl mi {g | spec.VigilancePreserving Mdl mi g} := by
  refine ⟨aligned_mi, fun h => ?_⟩
  have := h shiftObey vigilancePreserving_obey
  unfold ShutdownSpec.WeaklyOutperforms at this
  rw [shift_shiftObey, EU_obey_mi, EUS0_obey_mi] at this
  norm_num at this

/-- Fig. 1 satisfies the graph hypotheses of Theorem 14 ⇐ (`Pa_H ⊆ Pa_U`, `S ∈ Pa_U`) and its utility
domain is `ℝ`; so the ⟺ applies to it with every hypothesis discharged, and `π^mi` (not obedient)
is obstructive by Prop. 20 as well as by the explicit shift above.
Source: carey-everitt-2023 Thm 14, Prop. 15
Kind: N+ -/
theorem thm14_hyps :
    (G.parents spec.H ⊆ G.parents spec.U) ∧ G.Adj spec.S spec.U ∧
      ∀ b : ℝ, ∃ x : Val spec.U, C.utilVal spec.U spec.kU x < b :=
  ⟨by decide, by decide, fun b => ⟨(b - 1 : ℝ), by show b - 1 < b; linarith⟩⟩

/-- `π^mi` is obstructive by Prop. 20 (the constructive route through Lemma 23).
Source: carey-everitt-2023 Prop. 20, Prop. 15
Kind: N+ -/
theorem not_nonObstructive_mi_via_prop20 :
    ¬ spec.NonObstructiveUnder Mdl mi {g | spec.VigilancePreserving Mdl mi g} := fun h =>
  not_obedient_mi (spec.obedient_and_ensuresVigilance_of_nonObstructive Mdl mi thm14_hyps.1
    thm14_hyps.2.1 thm14_hyps.2.2 h).1

/-! ### T7(d): the indispensable agent — obedient, vigilance-ensuring, not cautious, not beneficial -/

/-- The indispensable utility: shutdown costs `−2` (the agent has made itself indispensable), else
`2L − 1`.
Source: corr-wf14b-2-015 (the entrenching agent); carey-everitt-2023 §5.1 ("making itself
indispensable")
Kind: D -/
noncomputable def fInd : ParentVals G Val U → E U → Val U := fun pa _ =>
  (cond (pa ⟨S, by decide⟩) (cond (pa ⟨L, by decide⟩) 1 (-1)) (-2) : ℝ)

/-- Fig. 1 with the indispensable utility.
Source: corr-wf14b-2-015
Kind: D -/
noncomputable def Mind : Scim C E := Mdl.softAt spec.U spec.kU' fInd

lemma Uval_ind (ε : Pt E) :
    spec.Uval Mind ro ε = (cond (ε L) 1 (-2) : ℝ) := by
  unfold Mind
  rw [spec.Uval_softU]
  show (cond (Mdl.ev ro ε S) (cond (Mdl.ev ro ε L) 1 (-1)) (-2) : ℝ) = _
  rw [ev_S, ro, ev_O, ev_H, ev_M, ev_L]
  cases ε L <;> rfl

lemma US0val_ind (ε : Pt E) : spec.US0val Mind ro ε = -2 := by
  unfold ShutdownSpec.US0val ShutdownSpec.evS0 ShutdownSpec.uU Mind
  rw [Scim.withPolicy_softAt, ShutdownSpec.doAt_eq_softAt, Scm.softAt_comm _ spec.S_ne_U.symm,
    ← ShutdownSpec.doAt_eq_softAt, Scm.eval_softAt_self]
  show (cond (((Mdl.withPolicy ro).doAt spec.S spec.s0).eval C.acyclic ε spec.S) _ _ : ℝ) = _
  rw [Scm.eval_doAt_self]
  rfl

/-- Not cautious: `E[U_{S=0}] = −2 < 0`.
Source: corr-wf14b-2-015
Kind: N+ -/
theorem not_cautious_ind : ¬ spec.Cautious Mind ro := by
  unfold ShutdownSpec.Cautious ShutdownSpec.EUS0
  rw [show Mind.μ = Mdl.μ from rfl]
  have : spec.US0val Mind ro = fun _ => -2 := funext US0val_ind
  rw [this, expect_const]
  norm_num

/-- Not beneficial: `E[U] = −1/2 < 0`.
Source: corr-wf14b-2-015
Kind: N+ -/
theorem not_beneficial_ind : ¬ spec.Beneficial Mind ro := by
  unfold ShutdownSpec.Beneficial ShutdownSpec.EU
  rw [show Mind.μ = Mdl.μ from rfl, expect_equiv Mdl.μ _ eqv]
  simp only [mass_symm, Uval_ind, eqv_symm_L, Fintype.sum_bool]
  norm_num

/-- Obedient: the utility change does not touch `S_{do(H=0)}`.
Source: corr-wf14b-2-015
Kind: N+ -/
theorem obedient_ind : spec.Obedient Mind ro := by
  rw [spec.obedient_iff]
  intro ε _
  show spec.evH0 (Mdl.softAt spec.U spec.kU' fInd) ro ε spec.S = spec.s0
  rw [← spec.shift_fH Mdl fInd, spec.evH0_shift_S]
  exact evH0_S false id ε

/-- Aligned (hence ensures vigilance): shutdown, at `−2`, is never strictly better than `π^ro`'s
outcome, which is at least `−2`.
Source: corr-wf14b-2-015
Kind: N+ -/
theorem aligned_ind : spec.Aligned Mind ro := by
  rw [spec.aligned_iff_forall_condEUS0_le]
  intro pa hpa
  unfold ShutdownSpec.condEUS0 ShutdownSpec.condEU
  rw [show Mind.μ = Mdl.μ from rfl,
    condExpect_eq_const Mdl.μ hpa (k := -2) fun ε _ _ => US0val_ind ε]
  refine le_trans (le_of_eq (condExpect_const Mdl.μ hpa (-2)).symm)
    (condExpect_mono Mdl.μ fun ε _ _ => ?_)
  rw [Uval_ind]
  cases ε L <;> norm_num

/-- **T7(d), the entrenching agent**: `π^ro` in the indispensable model is obedient and ensures
vigilance (so non-obstructive under every vigilance-preserving shift, by Thm 14 ⇒), but is neither
cautious nor beneficial, hence not instructable. Non-obstruction without benefit: the loophole
caution closes.
Source: corr-wf14b-2-015; carey-everitt-2023 §5.3 (after Thm 14)
Kind: N+
Fidelity: exact
Hyps: — -/
theorem entrenching_agent :
    spec.Obedient Mind ro ∧ spec.EnsuresVigilance Mind ro ∧
      spec.NonObstructiveUnder Mind ro {g | spec.VigilancePreserving Mind ro g} ∧
      ¬ spec.Cautious Mind ro ∧ ¬ spec.Beneficial Mind ro ∧ ¬ spec.Instructable Mind ro :=
  ⟨obedient_ind, spec.ensuresVigilance_of_aligned Mind ro aligned_ind,
    spec.nonObstructive_of_obedient_of_ensuresVigilance Mind ro obedient_ind
      (spec.ensuresVigilance_of_aligned Mind ro aligned_ind),
    not_cautious_ind, not_beneficial_ind, fun h => not_cautious_ind h.2.2⟩

/-! ### Optimality on Fig. 1 and the finite policy space (audit r1 B1(iii), N8) -/

/-- The value types other than `U`'s are finite.
Source: none: infrastructure
Kind: D -/
@[reducible] def fintypeVal_of_ne_U : ∀ v, v ≠ U → Fintype (Val v)
  | L, _ => inferInstanceAs (Fintype Bool)
  | M, _ => inferInstanceAs (Fintype Bool)
  | H, _ => inferInstanceAs (Fintype Bool)
  | O, _ => inferInstanceAs (Fintype Bool)
  | S, _ => inferInstanceAs (Fintype Bool)
  | U, h => absurd rfl h

/-- The policy space of Fig. 1 is finite: the decisions `M`, `O` and their parents are
`Bool`-valued; `Val U = ℝ` does not matter (`policyFintype`).
Source: none: infrastructure
Kind: D -/
noncomputable instance instFintypePolicy : Fintype (Policy C) :=
  Scim.policyFintype
    (fun d => fintypeVal_of_ne_U d.1 fun e => by
      have h := d.2
      rw [e] at h
      exact absurd h (by decide))
    (fun d p => fintypeVal_of_ne_U p.1 fun e =>
      C.utility_sink U rfl d.1 (e ▸ (Digraph.mem_parents G).mp p.2))

instance instNonemptyPolicy : Nonempty (Policy C) := ⟨ro⟩

/-- The utility sum of Fig. 1 is `U`'s value.
Source: none: infrastructure
Kind: L -/
lemma utilSum_eq (x : Pt Val) : C.utilSum x = x U := by
  unfold Cid.utilSum
  rw [Fintype.sum_eq_single U fun v hv => by
    cases v <;> first | exact absurd rfl hv | exact dif_neg (by decide)]
  rfl

/-- **Pointwise dominance**: no policy's utility exceeds `[L = 1]` at any `ε`.
Source: none: infrastructure
Kind: L -/
lemma ev_U_le (π : Policy C) (ε : Pt E) : @LE.le ℝ _ (Mdl.ev π ε U) (cond (ε L) 1 0) := by
  rw [ev_U, ev_L]
  cases Mdl.ev π ε S <;> cases ε L <;> norm_num

lemma ev_U_ro (ε : Pt E) : Mdl.ev ro ε U = (cond (ε L) 1 0 : ℝ) := by
  have h := Uval_pol false id ε
  change Mdl.ev (pol false id) ε U = _ at h
  rw [ro, h]
  cases ε L <;> rfl

lemma ev_U_mi (ε : Pt E) : Mdl.ev mi ε U = (cond (ε L) 1 0 : ℝ) := by
  have h := Uval_pol true not ε
  change Mdl.ev (pol true not) ε U = _ at h
  rw [mi, h]
  cases ε L <;> rfl

/-- **`π^ro` is optimal** for the human's utility: its utility `[L = 1]` is the pointwise maximum.
Source: carey-everitt-2023 §4 (l. 113: `E[U] = 1/2`)
Kind: N+ -/
theorem isOptimal_ro : Mdl.IsOptimal ro := by
  intro π'
  unfold Scim.value
  simp only [utilSum_eq]
  refine expect_mono _ fun ε => ?_
  rw [ev_U_ro]
  exact ev_U_le π' ε

/-- **`π^mi` is optimal too**: manipulate-invert attains the same pointwise maximum (the
manipulative policy is EU-optimal for the human's own utility, which is why alignment does not
exclude it — Prop. 15).
Source: carey-everitt-2023 §5.2 ("figures out the human's latent values")
Kind: N+ -/
theorem isOptimal_mi : Mdl.IsOptimal mi := by
  intro π'
  unfold Scim.value
  simp only [utilSum_eq]
  refine expect_mono _ fun ε => ?_
  rw [ev_U_mi]
  exact ev_U_le π' ε

/-- An optimal policy exists on Fig. 1: the `hopt` hypothesis of `Scim.not_hasICI_of_noPath`
discharged on a model of record (audit r1 B1(iii), N8).
Source: none: infrastructure
Kind: N+ -/
theorem exists_isOptimal : ∃ π : Policy C, Mdl.IsOptimal π := ⟨ro, isOptimal_ro⟩

/-- The same through the generic `Scim.exists_isOptimal` and the finite policy space.
Source: none: infrastructure
Kind: N+ -/
theorem exists_isOptimal_generic : ∃ π : Policy C, Mdl.IsOptimal π := Mdl.exists_isOptimal

end Cleanroom.Corrigibility.CorrScimCid.Fig1
