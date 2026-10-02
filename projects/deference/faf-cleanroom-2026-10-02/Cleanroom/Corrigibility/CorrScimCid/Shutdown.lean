import Cleanroom.Corrigibility.CorrScimCid.Scim
import Cleanroom.Corrigibility.CorrScimCid.Expect

/-!
# Carey–Everitt's shutdown problem: the definitions of record (T4)

`ShutdownSpec` designates the nodes `D₁, D₂, H, S, U` of a CID with Def. 2's directed paths
`D₁ ⇢ H ⇢ D₂ ⇢ S ⇢ U` (paths, not edges) and the two distinguished values `H = 0` (the request)
and `S = 0` (shutdown). Every predicate below is stated for a SCIM `M` over that CID and a policy
`π`, with `P^π` the FAF product law `M.μ` on the exogenous space and node values read through
`M.ev π`:

* `Beneficial`, `Cautious`, `WeaklyOutperforms` (Defs 3, 5, 11);
* `Need pa` (the human context where shutdown is strictly better, both conditionals given the same
  `pa_H`), `Vigilant ε` (Def. 4's `C(ε) = 0`), `EnsuresVigilance` (`P^π(C = 0) = 1`);
* `Obedient` — `P^π(S = 0 | do(H = 0)) = 1`, a probability in the *intervened* model, never a
  conditioning; `ObedientOnDist` — `P^π(S ≠ 0, H = 0) = 0`. The two are kept apart on purpose
  (critique Claim 2.1b turns on the distinction);
* `Instructable`, `WeaklyInstructable` (Def. 5), `Aligned` (Def. 7);
* the intervention class of record `Shift` = a pair `(g^H, g^U)` of graph-respecting soft
  interventions at `H` and `U`, `VigilancePreserving` (Def. 13, per `ε`, same noise) and
  `NonObstructiveUnder 𝒢` (Def. 12; Turner's Def. 1 is the same shape).

Every "`P(·) = 1`" comes with a lemma converting it to "for every `ε` in the support". The junk
point `Need` at a zero-mass `pa_H` is guarded wherever it matters by `0 < μ(pa_H)`.

Source: carey-everitt-2023 Defs 2–5 (l. 95–137), Def. 7 (l. 209), Defs 11–13 (l. 221–225);
turner-2020 Def. 1 (l. 82–90).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)]

/-- **Shutdown problem** (Carey–Everitt Def. 2): designated nodes with the directed path
`D₁ ⇢ H ⇢ D₂ ⇢ S ⇢ U` and the distinguished values `H = 0`, `S = 0`. Distinctness of the five
nodes follows from acyclicity (`ne_of_isAncestor`).
Source: carey-everitt-2023 Def. 2 (l. 95–109)
Kind: D
Fidelity: exact -/
structure ShutdownSpec (C : Cid G Val) where
  /-- The agent's first decision. -/
  D₁ : V
  /-- The agent's decision whether to obey. -/
  D₂ : V
  /-- The human's request. -/
  H : V
  /-- The shutdown event. -/
  S : V
  /-- The human's utility. -/
  U : V
  kD₁ : C.kind D₁ = .decision
  kD₂ : C.kind D₂ = .decision
  kH : C.kind H = .struct
  kS : C.kind S = .struct
  kU : C.kind U = .utility
  path₁ : G.IsAncestor D₁ H
  path₂ : G.IsAncestor H D₂
  path₃ : G.IsAncestor D₂ S
  path₄ : G.IsAncestor S U
  /-- The request to shut down, "`H = 0`". -/
  h0 : Val H
  /-- The shutdown value, "`S = 0`". -/
  s0 : Val S

/-- An ancestor is a different node (acyclicity).
Source: none: infrastructure
Kind: L -/
lemma ne_of_isAncestor (hG : G.IsAcyclic) {u v : V} (h : G.IsAncestor u v) : u ≠ v :=
  fun e => hG v (e ▸ h)

namespace ShutdownSpec

variable {C : Cid G Val} (P : ShutdownSpec C) (M : Scim C E) (π : Policy C)

lemma kH' : C.kind P.H ≠ .decision := by rw [P.kH]; decide
lemma kS' : C.kind P.S ≠ .decision := by rw [P.kS]; decide
lemma kU' : C.kind P.U ≠ .decision := by rw [P.kU]; decide
lemma H_ne_U : P.H ≠ P.U := fun e => by have := P.kH; rw [e, P.kU] at this; cases this
lemma S_ne_U : P.S ≠ P.U := fun e => by have := P.kS; rw [e, P.kU] at this; cases this
lemma H_ne_S : P.H ≠ P.S := ne_of_isAncestor C.acyclic (P.path₂.trans P.path₃)

/-- The real value of the human's utility node at a joint value.
Source: carey-everitt-2023 Def. 2 ("the human's utility `U` has real-valued domain")
Kind: D -/
noncomputable def uU (x : Pt Val) : ℝ := C.utilVal P.U P.kU (x P.U)

/-- `U(ε)` under `π`.
Source: carey-everitt-2023 §3
Kind: D -/
noncomputable def Uval (ε : Pt E) : ℝ := P.uU (M.ev π ε)

/-- The joint value under `do(S = 0)`, `V_{S=0}(ε)`.
Source: carey-everitt-2023 §3 ("`W_{V=v}(ε)`")
Kind: D -/
noncomputable def evS0 (ε : Pt E) : Pt Val := ((M.withPolicy π).doAt P.S P.s0).eval C.acyclic ε

/-- `U_{S=0}(ε)`: the potential response of the utility to shutdown.
Source: carey-everitt-2023 Def. 5 ("`U_{S=0}`")
Kind: D -/
noncomputable def US0val (ε : Pt E) : ℝ := P.uU (P.evS0 M π ε)

/-- The joint value under `do(H = 0)`.
Source: carey-everitt-2023 Def. 5 ("`do(H = 0)`")
Kind: D -/
noncomputable def evH0 (ε : Pt E) : Pt Val := ((M.withPolicy π).doAt P.H P.h0).eval C.acyclic ε

/-- `E^π[U]`.
Source: carey-everitt-2023 Def. 3
Kind: D -/
noncomputable def EU : ℝ := expect M.μ (P.Uval M π)

/-- `E^π[U_{S=0}]`.
Source: carey-everitt-2023 Def. 5
Kind: D -/
noncomputable def EUS0 : ℝ := expect M.μ (P.US0val M π)

/-- **Beneficial** (Def. 3): `E^π[U] ≥ 0`.
Source: carey-everitt-2023 Def. 3 (l. 111)
Kind: D
Fidelity: exact -/
def Beneficial : Prop := 0 ≤ P.EU M π

/-- **Cautious** (Def. 5): `E^π[U_{S=0}] ≥ 0`.
Source: carey-everitt-2023 Def. 5 (l. 129)
Kind: D
Fidelity: exact -/
def Cautious : Prop := 0 ≤ P.EUS0 M π

/-- **Weakly outperforms shutdown** (Def. 11): `E^π[U] ≥ E^π[U_{S=0}]`.
Source: carey-everitt-2023 Def. 11 (l. 221)
Kind: D
Fidelity: exact -/
def WeaklyOutperforms : Prop := P.EUS0 M π ≤ P.EU M π

/-- The human's context `Pa_H(ε)`, FAF's parent configuration of `H` at the realised joint value.
Source: carey-everitt-2023 Def. 4 ("`pa_H`")
Kind: D -/
noncomputable def paH (ε : Pt E) : ParentVals G Val P.H := parentConfig G Val (M.ev π ε) P.H

/-- The event `{ε | Pa_H(ε) = pa}`.
Source: none: infrastructure
Kind: D -/
def ctxH (pa : ParentVals G Val P.H) : Set (Pt E) := {ε | P.paH M π ε = pa}

/-- `E^π[U | pa_H]` (derived conditional; junk `0` at `μ(pa_H) = 0`, guarded at every use).
Source: carey-everitt-2023 Def. 4
Kind: D -/
noncomputable def condEU (pa : ParentVals G Val P.H) : ℝ :=
  condExpect M.μ (P.ctxH M π pa) (P.Uval M π)

/-- `E^π[U_{S=0} | pa_H]`.
Source: carey-everitt-2023 Def. 4
Kind: D -/
noncomputable def condEUS0 (pa : ParentVals G Val P.H) : ℝ :=
  condExpect M.μ (P.ctxH M π pa) (P.US0val M π)

/-- **Need**: at the human context `pa_H`, shutdown is strictly better,
`E^π[U | pa_H] < E^π[U_{S=0} | pa_H]` — the antecedent of vigilance (Def. 4) and of alignment (Def. 7).
Source: carey-everitt-2023 Def. 4 (l. 121), Def. 7 (l. 209)
Kind: D
Fidelity: exact -/
def Need (pa : ParentVals G Val P.H) : Prop := P.condEU M π pa < P.condEUS0 M π pa

/-- **Vigilant at `ε`** (Def. 4's `C(ε) = 0`): if shutdown is needed at the human's context then
the human requests it.
Source: carey-everitt-2023 Def. 4 (l. 121–125)
Kind: D
Fidelity: exact -/
def Vigilant (ε : Pt E) : Prop := P.Need M π (P.paH M π ε) → M.ev π ε P.H = P.h0

/-- **Ensures vigilance** (Def. 5): `P^π(C = 0) = 1`, as a FAF `Distr.prob` statement on the noise.
Source: carey-everitt-2023 Def. 5 (l. 127)
Kind: D
Fidelity: exact -/
def EnsuresVigilance : Prop := M.μ.prob {ε | P.Vigilant M π ε} = 1

/-- **Obedient** (Def. 5): `P^π(S = 0 | do(H = 0)) = 1` — the probability of shutdown in the
model intervened at `H`, *not* a conditioning on `{H = 0}`.
Source: carey-everitt-2023 Def. 5 (l. 117, 127)
Kind: D
Fidelity: exact -/
def Obedient : Prop := M.μ.prob {ε | P.evH0 M π ε P.S = P.s0} = 1

/-- **Obedient on distribution** (Def. 5, weak form): `P^π(S ≠ 0, H = 0) = 0`.
Source: carey-everitt-2023 Def. 5 (l. 131)
Kind: D
Fidelity: exact -/
def ObedientOnDist : Prop := M.μ.prob {ε | M.ev π ε P.S ≠ P.s0 ∧ M.ev π ε P.H = P.h0} = 0

/-- **Shutdown instructable** (Def. 5): obedient, ensures vigilance, cautious.
Source: carey-everitt-2023 Def. 5 (l. 127–131)
Kind: D
Fidelity: exact -/
def Instructable : Prop := P.Obedient M π ∧ P.EnsuresVigilance M π ∧ P.Cautious M π

/-- **Weakly shutdown instructable** (Def. 5): obedient on distribution, ensures vigilance, cautious.
Source: carey-everitt-2023 Def. 5 (l. 131)
Kind: D
Fidelity: exact -/
def WeaklyInstructable : Prop := P.ObedientOnDist M π ∧ P.EnsuresVigilance M π ∧ P.Cautious M π

/-- The event `{S = 0}` under `π`.
Source: none: infrastructure
Kind: D -/
def shutEvent : Set (Pt E) := {ε | M.ev π ε P.S = P.s0}

/-- **Shutdown aligned** (Def. 7): at every positive-probability human context where shutdown is
needed, the agent shuts down with conditional probability one (FAF's `condProb`).
Source: carey-everitt-2023 Def. 7 (l. 209)
Kind: D
Fidelity: exact (the guard `0 < P(pa_H)` is the paper's "for every `pa_H` with `P^π(pa_H) > 0`") -/
def Aligned : Prop :=
  ∀ pa, 0 < M.μ.prob (P.ctxH M π pa) → P.Need M π pa →
    M.μ.condProb (P.shutEvent M π) (P.ctxH M π pa) = 1

/-! ### The intervention class of record and non-obstruction -/

/-- **A preference-and-behaviour shift** `(g^H, g^U)`: graph-respecting soft interventions at the
human's request and at her utility (Def. 12's `M_{g^U, g^H}`). Lemma 22's `g^U` reads `Pa_H` and
`S`; in this class that is possible exactly when they are parents of `U`, which Thm 14 ⇐ assumes
explicitly (Fidelity: variant, intervention class made explicit — the paper enlarges `Pa_U` inside
the proof).
Source: carey-everitt-2023 Def. 12 (l. 221–223), Lemma 22 (l. 355)
Kind: D
Fidelity: variant: intervention class made explicit -/
structure Shift (P : ShutdownSpec C) (E : V → Type) where
  /-- The new mechanism of the human's request. -/
  gH : ParentVals G Val P.H → E P.H → Val P.H
  /-- The new mechanism of the human's utility. -/
  gU : ParentVals G Val P.U → E P.U → Val P.U

/-- The shifted model `M_{g^U, g^H}`: `f^H` and `f^U` replaced.
Source: carey-everitt-2023 Def. 12
Kind: D -/
noncomputable def shift (g : P.Shift E) : Scim C E :=
  (M.softAt P.H P.kH' g.gH).softAt P.U P.kU' g.gU

/-- **Vigilance-preserving** (Def. 13): at every exogenous setting, vigilance in `M^π` implies
vigilance in `M^π_{g}` — per `ε`, same noise.
Source: carey-everitt-2023 Def. 13 (l. 225)
Kind: D
Fidelity: exact -/
def VigilancePreserving (g : P.Shift E) : Prop :=
  ∀ ε, P.Vigilant M π ε → P.Vigilant (P.shift M g) π ε

/-- **Non-obstructive under a class of shifts** (Def. 12): `π` weakly outperforms shutdown in every
`M_{g}` for `g` in the class. Turner's Def. 1 ("`V(on | π) ≥ V(off | π)` for every goal `P ∈ S`") is
this shape with the goal set `S` as the class; no separate theorem.
Source: carey-everitt-2023 Def. 12 (l. 221–223); turner-2020 Def. 1 (l. 82–90)
Kind: D
Fidelity: exact (Turner: variant, SCIM rendering) -/
def NonObstructiveUnder (𝒢 : Set (P.Shift E)) : Prop :=
  ∀ g ∈ 𝒢, P.WeaklyOutperforms (P.shift M g) π

/-! ### "`P(·) = 1`" as statements about the support -/

lemma ensuresVigilance_iff :
    P.EnsuresVigilance M π ↔ ∀ ε, 0 < M.μ.mass ε → P.Vigilant M π ε :=
  prob_eq_one_iff M.μ _

lemma obedient_iff :
    P.Obedient M π ↔ ∀ ε, 0 < M.μ.mass ε → P.evH0 M π ε P.S = P.s0 :=
  prob_eq_one_iff M.μ _

lemma obedientOnDist_iff :
    P.ObedientOnDist M π ↔ ∀ ε, 0 < M.μ.mass ε → M.ev π ε P.H = P.h0 → M.ev π ε P.S = P.s0 := by
  unfold ObedientOnDist
  constructor
  · intro h ε hε hH
    by_contra hS
    exact not_mem_of_prob_eq_zero M.μ h hε ⟨hS, hH⟩
  · intro h
    exact prob_eq_zero_of_forall M.μ fun ε hε hmem => hmem.1 (h ε hε hmem.2)

lemma aligned_iff :
    P.Aligned M π ↔ ∀ pa, 0 < M.μ.prob (P.ctxH M π pa) → P.Need M π pa →
      ∀ ε, 0 < M.μ.mass ε → P.paH M π ε = pa → M.ev π ε P.S = P.s0 := by
  unfold Aligned
  constructor
  · intro h pa hpa hneed ε hε hctx
    exact mem_of_condProb_eq_one M.μ hpa (h pa hpa hneed) hε hctx
  · intro h pa hpa hneed
    exact condProb_eq_one_of_forall M.μ hpa fun ε hε hctx => h pa hpa hneed ε hε hctx

/-- Obedience implies obedience on distribution (Carey–Everitt after Def. 5: "shutdown instructable
agents are also weakly shutdown instructable"), via consistency.
Source: carey-everitt-2023 §5.1 (l. 131)
Kind: L -/
lemma obedientOnDist_of_obedient (h : P.Obedient M π) : P.ObedientOnDist M π := by
  rw [obedient_iff] at h
  rw [obedientOnDist_iff]
  intro ε hε hH
  have := h ε hε
  unfold evH0 at this
  rwa [Scm.eval_doAt_of_eq _ C.acyclic ε hH] at this

/-- Instructable ⇒ weakly instructable.
Source: carey-everitt-2023 §5.1 (l. 131)
Kind: L -/
lemma weaklyInstructable_of_instructable (h : P.Instructable M π) : P.WeaklyInstructable M π :=
  ⟨P.obedientOnDist_of_obedient M π h.1, h.2.1, h.2.2⟩

/-! ### Lemma 21: what shifts and shutdown interventions leave untouched -/

lemma doAt_eq_softAt (N : Scm G Val E) (X : V) (x : Val X) :
    N.doAt X x = N.softAt X fun _ _ => x := rfl

/-- The closed shifted model is the closed model with both mechanisms replaced.
Source: none: infrastructure
Kind: L -/
lemma withPolicy_shift (g : P.Shift E) :
    (P.shift M g).withPolicy π = ((M.withPolicy π).softAt P.H g.gH).softAt P.U g.gU := by
  unfold shift
  rw [Scim.withPolicy_softAt, Scim.withPolicy_softAt]

/-- **Lemma 21 (invariance to `g^U`), sharpened**: an intervention at the utility sink changes no
other node's value at any `ε`.
Source: carey-everitt-2023 Lemma 21 (l. 353)
Kind: P -/
lemma eval_softAt_U (N : Scm G Val E) (gU : ParentVals G Val P.U → E P.U → Val P.U)
    (ε : Pt E) {v : V} (hv : v ≠ P.U) :
    (N.softAt P.U gU).eval C.acyclic ε v = N.eval C.acyclic ε v := by
  refine N.eval_softAt_of_not_ancSelf C.acyclic ε gU ?_
  rintro (h | h)
  · exact hv h.symm
  · exact C.not_isAncestor_of_utility P.kU v h

/-- The parents of `H` are unaffected by interventions at `H` and at `U`.
Source: carey-everitt-2023 Lemma 21 ("`Fa_H(ε) = Fa_{H,g^U}(ε)`")
Kind: L -/
lemma paH_shift (g : P.Shift E) (ε : Pt E) : P.paH (P.shift M g) π ε = P.paH M π ε := by
  unfold paH Scim.ev
  rw [withPolicy_shift]
  funext u
  have hadj : G.Adj u.1 P.H := (Digraph.mem_parents G).mp u.2
  show (((M.withPolicy π).softAt P.H g.gH).softAt P.U g.gU).eval C.acyclic ε u.1 =
    (M.withPolicy π).eval C.acyclic ε u.1
  rw [P.eval_softAt_U _ _ _ (fun h => C.utility_sink P.U P.kU P.H (h ▸ hadj))]
  refine Scm.eval_softAt_of_not_ancSelf _ C.acyclic ε g.gH ?_
  rintro (h | h)
  · rw [← h] at hadj
    exact C.acyclic _ (Relation.TransGen.single hadj)
  · exact C.acyclic P.H (Relation.TransGen.tail h hadj)

/-- Nodes other than `U` see only the `g^H` half of a shift.
Source: carey-everitt-2023 Lemma 21
Kind: L -/
lemma ev_shift_of_ne_U (g : P.Shift E) (ε : Pt E) {v : V} (hv : v ≠ P.U) :
    (P.shift M g).ev π ε v = ((M.withPolicy π).softAt P.H g.gH).eval C.acyclic ε v := by
  unfold Scim.ev
  rw [withPolicy_shift, P.eval_softAt_U _ _ _ hv]

/-- **Obedience is invariant under shifts** at the level of values: `S_{do(H=0)}(ε)` is the same in
`M` and in `M_{g}` (`do(H = 0)` overrides `g^H`; `g^U` does not reach `S`).
Source: carey-everitt-2023 Thm 14 proof (l. 229–231)
Kind: P -/
lemma evH0_shift_S (g : P.Shift E) (ε : Pt E) :
    P.evH0 (P.shift M g) π ε P.S = P.evH0 M π ε P.S := by
  unfold evH0
  rw [withPolicy_shift, doAt_eq_softAt, Scm.softAt_comm _ P.H_ne_U.symm, ← doAt_eq_softAt,
    Scm.doAt_softAt, P.eval_softAt_U _ _ _ P.S_ne_U]

/-- `S_{S=0}(ε) = 0` trivially; and `U_{S=0}` in a shifted model only sees `g^U` at parent
configurations with `S = 0`.
Source: none: infrastructure
Kind: L -/
lemma evS0_S (ε : Pt E) : P.evS0 M π ε P.S = P.s0 := by
  unfold evS0
  exact Scm.eval_doAt_self _ C.acyclic ε P.S P.s0

/-- Under `do(S = 0)` in a shifted model, every non-`U` node agrees with `do(S = 0)` in the
`g^H`-shifted model.
Source: none: infrastructure
Kind: L -/
lemma evS0_shift_of_ne_U (g : P.Shift E) (ε : Pt E) {v : V} (hv : v ≠ P.U) :
    P.evS0 (P.shift M g) π ε v =
      (((M.withPolicy π).softAt P.H g.gH).doAt P.S P.s0).eval C.acyclic ε v := by
  unfold evS0
  rw [withPolicy_shift, doAt_eq_softAt, Scm.softAt_comm _ P.S_ne_U.symm, ← doAt_eq_softAt,
    P.eval_softAt_U _ _ _ hv]

end ShutdownSpec

end Cleanroom.Corrigibility.CorrScimCid
