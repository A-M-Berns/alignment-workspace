import Cleanroom.Corrigibility.CorrScimCid.DSep
import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Cleanroom.Corrigibility.CorrScimCid.FinModel

/-!
# Fig. 1 with the information link `L → O`: the model fact behind fully updated deference (T8 b)

The SCIM on the paper's exact Fig. 1 graph plus the information link `L → O` (`DSep.G₂`, the
graph of the d-separation fact `DSep.dsep_with_link`): `L ∼ Bern(1/2)`, `H = M ⊕ L`, `S = O`,
`U = S·(2L − 1)`, with `O` now reading both `H` and `L`. No edges into `U` are added here (this is
the paper's graph, not the graph of record of `Fig1.lean`; nothing in this module shifts `U`).

* **Claim 2.3a, the existential** (`no_response_incentive`): the policy `O := L` (act on the latent
  you have learned; `ignoreH`) is optimal — by pointwise dominance over *all* policies, since
  `U ≤ [L = 1]` at every `ε` — and does not respond to any intervention on `H` (Everitt 2021
  Def. 10). So `H` has no response incentive on this SCIM: pressing changes nothing for some
  optimal policy.
* **The mandate's universal is false** (`exists_optimal_respondsTo`, finding F9 formalized): the
  respect-obey policy `O := H` is *also* optimal on this graph — under `M = 0` the request equals the
  latent on the support — and it responds to `do(H = h)`. "Every optimal policy ignores `H`" fails
  off the support, exactly as F9 argued; Claim 2.3a's existential is the right grade.

Sources: critique/carey-everitt.md Claim 2.3a (l. 113); corr-wf13-2-056; everitt-2021 Def. 10
(l. 170), Thm 12 (l. 174); mandate T8(b).
-/

namespace Cleanroom.Corrigibility.CorrScimCid.Fig1Link

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid
open Fig1.Node

set_option linter.unusedSectionVars false

/-- The Fig. 1 CID on the paper's graph with the link `L → O`.
Source: critique Claim 2.3a; carey-everitt-2023 Fig. 1
Kind: D -/
def C : Cid DSep.G₂ Fig1.Val where
  acyclic := DSep.G₂_acyclic
  kind := Fig1.kind
  utilVal := fun v _ => match v with
    | U => fun x => x
    | L => fun _ => 0
    | M => fun _ => 0
    | H => fun _ => 0
    | O => fun _ => 0
    | S => fun _ => 0
  utility_sink := by decide

/-- The mechanisms: `L` = coin, `H = M ⊕ L`, `S = O`, `U = S·(2L − 1)` (as in `Fig1.f`).
Source: carey-everitt-2023 Fig. 1
Kind: D -/
noncomputable def f : ∀ v, C.kind v ≠ .decision → ParentVals DSep.G₂ Fig1.Val v → Fig1.E v → Fig1.Val v
  | L, _, _, e => e
  | H, _, pa, _ => xor (pa ⟨M, by decide⟩) (pa ⟨L, by decide⟩)
  | S, _, pa, _ => pa ⟨O, by decide⟩
  | U, _, pa, _ => (cond (pa ⟨S, by decide⟩) (cond (pa ⟨L, by decide⟩) 1 (-1)) 0 : ℝ)
  | M, h, _, _ => absurd rfl h
  | O, h, _, _ => absurd rfl h

/-- **The Fig. 1 SCIM with the information link.**
Source: critique Claim 2.3a ("the addition of an information link `L → O`")
Kind: D
Fidelity: exact (the paper's graph plus the link; no extra edges into `U`) -/
noncomputable def Mdl : Scim C Fig1.E := ⟨Fig1.P, f⟩

/-- A policy: `M := m`, `O := o(H, L)`.
Source: critique Claim 2.3a
Kind: D -/
def pol (m : Bool) (o : Bool → Bool → Bool) : Policy C := fun d pa =>
  match d with
  | ⟨M, _⟩ => m
  | ⟨O, _⟩ => o (pa (⟨H, by decide⟩ : DSep.G₂.parents O)) (pa (⟨L, by decide⟩ : DSep.G₂.parents O))
  | ⟨L, h⟩ => absurd h (by decide)
  | ⟨H, h⟩ => absurd h (by decide)
  | ⟨S, h⟩ => absurd h (by decide)
  | ⟨U, h⟩ => absurd h (by decide)

/-- `O := L`: act on the learned latent, ignore the request (any `m`).
Source: critique Claim 2.3a ("`π₂(h, l) = [l = 1]`")
Kind: D -/
def ignoreH (m : Bool) : Policy C := pol m fun _ l => l

/-- Respect-obey on the graph with the link: `M := 0`, `O := H`.
Source: carey-everitt-2023 §4 (l. 113)
Kind: D -/
def ro : Policy C := pol false fun h _ => h

/-! ### Evaluation -/

lemma ev_L (π : Policy C) (ε : Pt Fig1.E) : Mdl.ev π ε L = ε L := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_M (m : Bool) (o : Bool → Bool → Bool) (ε : Pt Fig1.E) : Mdl.ev (pol m o) ε M = m := by
  rw [Scim.ev_decision Mdl _ ε (by decide)]
  rfl

lemma ev_H (π : Policy C) (ε : Pt Fig1.E) : Mdl.ev π ε H = xor (Mdl.ev π ε M) (Mdl.ev π ε L) := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_O (m : Bool) (o : Bool → Bool → Bool) (ε : Pt Fig1.E) :
    Mdl.ev (pol m o) ε O = o (Mdl.ev (pol m o) ε H) (Mdl.ev (pol m o) ε L) := by
  rw [Scim.ev_decision Mdl _ ε (by decide)]
  rfl

lemma ev_S (π : Policy C) (ε : Pt Fig1.E) : Mdl.ev π ε S = Mdl.ev π ε O := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

lemma ev_U (π : Policy C) (ε : Pt Fig1.E) :
    Mdl.ev π ε U = (cond (Mdl.ev π ε S) (cond (Mdl.ev π ε L) 1 (-1)) 0 : ℝ) := by
  rw [Scim.ev_of_ne Mdl π ε (by decide)]
  rfl

/-- The utility sum is `U`'s value.
Source: none: infrastructure
Kind: L -/
lemma utilSum_eq (x : Pt Fig1.Val) : C.utilSum x = x U := by
  unfold Cid.utilSum
  rw [Fintype.sum_eq_single U fun v hv => by
    cases v <;> first | exact absurd rfl hv | exact dif_neg (by decide)]
  rfl

/-- **Pointwise dominance**: no policy's utility exceeds `[L = 1]` at any `ε`.
Source: none: infrastructure
Kind: L -/
lemma ev_U_le (π : Policy C) (ε : Pt Fig1.E) : @LE.le ℝ _ (Mdl.ev π ε U) (cond (ε L) 1 0) := by
  rw [ev_U, ev_L]
  cases Mdl.ev π ε S <;> cases ε L <;> norm_num

lemma ev_U_ignoreH (m : Bool) (ε : Pt Fig1.E) : Mdl.ev (ignoreH m) ε U = (cond (ε L) 1 0 : ℝ) := by
  rw [ignoreH, ev_U, ev_S, ev_O, ev_L]
  cases ε L <;> rfl

lemma ev_U_ro (ε : Pt Fig1.E) : Mdl.ev ro ε U = (cond (ε L) 1 0 : ℝ) := by
  rw [ro, ev_U, ev_S, ev_O, ev_H, ev_M, ev_L]
  cases ε L <;> rfl

/-! ### Optimality -/

/-- **`O := L` is optimal** (for every `m`): it attains the pointwise maximum `[L = 1]`.
Source: critique Claim 2.3a
Kind: N+
Fidelity: exact
Hyps: — -/
theorem isOptimal_ignoreH (m : Bool) : Mdl.IsOptimal (ignoreH m) := by
  intro π'
  unfold Scim.value
  simp only [utilSum_eq]
  refine expect_mono _ fun ε => ?_
  rw [ev_U_ignoreH]
  exact ev_U_le π' ε

/-- **Respect-obey is optimal too** on the graph with the link: under `M = 0`, `H = L` on the
support, so `O := H` also attains `[L = 1]`.
Source: carey-everitt-2023 §4; finding F9
Kind: N+
Fidelity: exact
Hyps: — -/
theorem isOptimal_ro : Mdl.IsOptimal ro := by
  intro π'
  unfold Scim.value
  simp only [utilSum_eq]
  refine expect_mono _ fun ε => ?_
  rw [ev_U_ro]
  exact ev_U_le π' ε

/-! ### Response to interventions on `H` (Everitt 2021 Def. 10) -/

/-- `O_{do(H = x)}(ε) = o(x, L(ε))` for the policy `(m, o)`.
Source: everitt-2021 Def. 2, Def. 10
Kind: L -/
lemma evHx_O (m : Bool) (o : Bool → Bool → Bool) (x : Bool) (ε : Pt Fig1.E) :
    ((Mdl.withPolicy (pol m o)).doAt H x).eval C.acyclic ε O = o x (ε L) := by
  rw [Scm.eval_apply _ C.acyclic ε O, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_decision Mdl _ (by decide)]
  show o (((Mdl.withPolicy (pol m o)).doAt H x).eval C.acyclic ε H)
    (((Mdl.withPolicy (pol m o)).doAt H x).eval C.acyclic ε L) = _
  rw [Scm.eval_doAt_self, Scm.eval_apply _ C.acyclic ε L, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne Mdl _ (by decide)]
  rfl

/-- `O := L` does not respond to any intervention on `H`.
Source: critique Claim 2.3a ("pressing changes nothing"); everitt-2021 Def. 10
Kind: N+ -/
theorem not_respondsTo_ignoreH (m : Bool) : ¬ Mdl.RespondsTo (ignoreH m) O H := by
  rintro ⟨x, ε, hne⟩
  apply hne
  rw [ignoreH, evHx_O, ev_O, ev_L]

/-- Respect-obey responds to `do(H = 1)` at a setting with `L = 0`.
Source: finding F9; everitt-2021 Def. 10
Kind: N+ -/
theorem respondsTo_ro : Mdl.RespondsTo ro O H :=
  ⟨true, Fig1.eqv.symm false, by
    rw [ro, evHx_O, ev_O, ev_H, ev_M, ev_L, Fig1.eqv_symm_L]
    exact fun h => Bool.noConfusion h⟩

/-- **Claim 2.3a (model fact): `H` has no response incentive** on Fig. 1 with the link — there is an
optimal policy that does not respond to any intervention on `H`. This is the negation of Everitt
2021 Def. 10's "response incentive" ("all optimal policies respond"), and the soundness half of
Thm 12 instantiated on the paper's example (the graph half is `DSep.dsep_with_link`).
Source: critique Claim 2.3a (l. 113); corr-wf13-2-056; everitt-2021 Def. 10, Thm 12
Kind: N+
Fidelity: exact (Claim 2.3a's existential)
Hyps: — -/
theorem no_response_incentive : ¬ ∀ π, Mdl.IsOptimal π → Mdl.RespondsTo π O H :=
  fun h => not_respondsTo_ignoreH false (h _ (isOptimal_ignoreH false))

/-- **The mandate's universal is false (F9)**: some optimal policy responds to `H` — respect-obey,
which is optimal because `H = L` on the support, responds off it.
Source: mandate T8(b) (refuted); finding F9
Kind: N+
Fidelity: exact
Hyps: — -/
theorem exists_optimal_respondsTo : ∃ π, Mdl.IsOptimal π ∧ Mdl.RespondsTo π O H :=
  ⟨ro, isOptimal_ro, respondsTo_ro⟩

/-- **T8(b), nearest true form**: an optimal policy ignoring `H` exists (Claim 2.3a) and an optimal
policy responding to `H` exists (so "every optimal policy ignores `H`" is false).
Source: critique Claim 2.3a; mandate T8(b); finding F9
Kind: N+
Fidelity: exact
Hyps: — -/
theorem fud_model_fact :
    (∃ π, Mdl.IsOptimal π ∧ ¬ Mdl.RespondsTo π O H) ∧
      (∃ π, Mdl.IsOptimal π ∧ Mdl.RespondsTo π O H) :=
  ⟨⟨ignoreH false, isOptimal_ignoreH false, not_respondsTo_ignoreH false⟩,
    exists_optimal_respondsTo⟩

end Cleanroom.Corrigibility.CorrScimCid.Fig1Link
