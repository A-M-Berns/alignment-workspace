import Cleanroom.Corrigibility.CorrScimCid.Benefit

/-!
# Theorem 14: non-obstruction ⟺ obedience ∧ ensured vigilance (T7)

* **⇒** (`nonObstructive_of_obedient_of_ensuresVigilance`, C): obedience transfers to every shift
  at the level of values (`evH0_shift_S`: `do(H = 0)` overrides `g^H`, `g^U` never reaches `S`),
  vigilance transfers by the vigilance-preservation hypothesis, and T5's key lemma gives weak
  outperformance — no caution needed (the indispensability loophole, Carey–Everitt §5.3).
* **⇐** (`obedient_and_ensuresVigilance_of_nonObstructive`, P) through **Lemma 22**
  (`lemma22_vigilance_only_if`: a non-vigilance-ensuring policy is punished by a utility
  intervention that keeps vigilance *unchanged* at every `ε`) and **Lemma 23**
  (`lemma23_obedience_only_if`: a disobedient policy is punished by forcing the request at one
  human context and punishing disobedience *there*).

  **Repair of Lemma 23 (finding F4).** The paper's `g^U` punishes `H = 0 ∧ S ≠ 0` at *every*
  human context, and its case (iii) asserts `E[U | Pa_H(ε)] = E_{g^U}[U | Pa_H(ε)]` at contexts
  `≠ pa'_H`; that equality fails when the policy also disobeys at a second context (the human may
  over-press there while vigilant, and the punishment then creates a need the human does not
  answer), so the paper's pair need not be vigilance-preserving. The construction here restricts the
  punishment to `Pa_H = pa'_H`, and the proof of vigilance preservation goes through verbatim.

The intervention class is the graph-respecting one of `Shutdown.lean`; Lemma 22/23 need `U` to
read `Pa_H` and `S` (`hPaH`, `hSU`), and a utility domain with arbitrarily negative values
(`hrich`, automatic for `Val U = ℝ`), which is where the paper enlarges the domain by `−α`.

Source: carey-everitt-2023 Thm 14 (l. 225–233), Appendix B Prop. 20, Lemmas 21–23 (l. 347–397).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {Val E : V → Type} [∀ v, Fintype (E v)]

namespace ShutdownSpec

variable {C : Cid G Val} (P : ShutdownSpec C) (M : Scim C E) (π : Policy C)

@[simp] lemma shift_μ (g : P.Shift E) : (P.shift M g).μ = M.μ := rfl

/-- **Theorem 14, ⇒**: an obedient policy that ensures vigilance is non-obstructive under every
vigilance-preserving shift. Obedience transfers by `evH0_shift_S`, vigilance by hypothesis, and
T5's key lemma gives `E_g[U_{S=0}] ≤ E_g[U]`. No caution is used.
Source: carey-everitt-2023 Thm 14 (l. 225), proof (l. 227–233)
Kind: C
Fidelity: exact
Hyps: — -/
theorem nonObstructive_of_obedient_of_ensuresVigilance (ho : P.Obedient M π)
    (hv : P.EnsuresVigilance M π) :
    P.NonObstructiveUnder M π {g | P.VigilancePreserving M π g} := by
  intro g hg
  have ho' : P.Obedient (P.shift M g) π := by
    rw [obedient_iff] at ho ⊢
    intro ε hε
    rw [P.evH0_shift_S M π g ε]
    exact ho ε hε
  have hv' : P.EnsuresVigilance (P.shift M g) π := by
    rw [ensuresVigilance_iff] at hv ⊢
    intro ε hε
    exact hg ε (hv ε hε)
  exact P.weaklyOutperforms_of_obedient_of_ensuresVigilance _ π ho' hv'

/-! ### Reading `Pa_H` and `S` off a parent configuration of `U` -/

section Read

variable (hPaH : G.parents P.H ⊆ G.parents P.U) (hSU : G.Adj P.S P.U)

/-- The human's context read off a parent configuration of `U` (when `Pa_H ⊆ Pa_U`).
Source: carey-everitt-2023 Lemma 22 ("the new parents `P̂a_U = Pa_U ∪ Pa_H ∪ S`")
Kind: D -/
def restrictH (paU : ParentVals G Val P.U) : ParentVals G Val P.H := fun i => paU ⟨i.1, hPaH i.2⟩

/-- The shutdown value read off a parent configuration of `U` (when `S ∈ Pa_U`).
Source: carey-everitt-2023 Lemma 22
Kind: D -/
def readS (paU : ParentVals G Val P.U) : Val P.S := paU ⟨P.S, (Digraph.mem_parents G).mpr hSU⟩

lemma restrictH_parentConfig (x : Pt Val) :
    P.restrictH hPaH (parentConfig G Val x P.U) = parentConfig G Val x P.H := rfl

lemma readS_parentConfig (x : Pt Val) : P.readS hSU (parentConfig G Val x P.U) = x P.S := rfl

end Read

/-! ### A soft intervention at `U` seen from the shutdown vocabulary -/

section SoftU

variable (gU : ParentVals G Val P.U → E P.U → Val P.U) (ε : Pt E)

lemma ev_softU_of_ne {v : V} (hv : v ≠ P.U) :
    (M.softAt P.U P.kU' gU).ev π ε v = M.ev π ε v := by
  unfold Scim.ev
  rw [Scim.withPolicy_softAt]
  exact P.eval_softAt_U _ gU ε hv

lemma paH_softU : P.paH (M.softAt P.U P.kU' gU) π ε = P.paH M π ε := by
  unfold paH
  funext u
  exact P.ev_softU_of_ne M π gU ε fun h =>
    C.utility_sink P.U P.kU P.H (h ▸ (Digraph.mem_parents G).mp u.2)

lemma ctxH_softU (pa : ParentVals G Val P.H) :
    P.ctxH (M.softAt P.U P.kU' gU) π pa = P.ctxH M π pa := by
  ext ε
  simp [ctxH, paH_softU]

lemma parentConfig_U_softU :
    parentConfig G Val ((M.softAt P.U P.kU' gU).ev π ε) P.U = parentConfig G Val (M.ev π ε) P.U := by
  funext u
  have hadj : G.Adj u.1 P.U := (Digraph.mem_parents G).mp u.2
  refine P.ev_softU_of_ne M π gU ε fun h => ?_
  rw [h] at hadj
  exact C.acyclic P.U (Relation.TransGen.single hadj)

/-- The utility under a soft intervention at `U`: `g^U` at the unchanged parent configuration.
Source: none: infrastructure
Kind: L -/
lemma Uval_softU :
    P.Uval (M.softAt P.U P.kU' gU) π ε =
      C.utilVal P.U P.kU (gU (parentConfig G Val (M.ev π ε) P.U) (ε P.U)) := by
  unfold Uval uU Scim.ev
  rw [Scim.withPolicy_softAt, Scm.eval_softAt_self]

/-- `U_{S=0}` is unchanged by a utility intervention that agrees with `f^U` wherever `S = 0`.
Source: carey-everitt-2023 Lemma 22 proof ("cannot change `E[U_{S=0} | pa_H]`")
Kind: L -/
lemma US0val_softU (hSU : G.Adj P.S P.U)
    (hg : ∀ paU e, P.readS hSU paU = P.s0 → gU paU e = M.f P.U P.kU' paU e) :
    P.US0val (M.softAt P.U P.kU' gU) π ε = P.US0val M π ε := by
  unfold US0val evS0 uU
  rw [Scim.withPolicy_softAt, doAt_eq_softAt, Scm.softAt_comm _ P.S_ne_U.symm, ← doAt_eq_softAt,
    Scm.eval_softAt_self]
  have hS : P.readS hSU (parentConfig G Val (((M.withPolicy π).doAt P.S P.s0).eval C.acyclic ε) P.U)
      = P.s0 := by
    rw [readS_parentConfig]
    exact Scm.eval_doAt_self _ C.acyclic ε P.S P.s0
  rw [hg _ _ hS]
  congr 1
  rw [Scm.eval_apply _ C.acyclic ε P.U, Scm.doAt_f_of_ne _ P.S_ne_U.symm,
    Scim.withPolicy_f_of_ne M π P.kU']

/-- The utility value under the *original* mechanism, at the realised parent configuration.
Source: none: infrastructure
Kind: L -/
lemma Uval_eq_f : P.Uval M π ε =
    C.utilVal P.U P.kU (M.f P.U P.kU' (parentConfig G Val (M.ev π ε) P.U) (ε P.U)) := by
  unfold Uval uU
  rw [Scim.ev_of_ne M π ε P.kU']

end SoftU

/-! ### Lemma 22: vigilance only-if -/

section Lemma22

variable (hPaH : G.parents P.H ⊆ G.parents P.U) (hSU : G.Adj P.S P.U)

open Classical in
/-- **Lemma 22's punishment** `g^U(p̂a_U) = x₀` if `pa_H ∈ A ∧ S ≠ 0`, else `f^U(pa_U)`, with `A` the
need set of `π` in `M`.
Source: carey-everitt-2023 Lemma 22 proof (l. 357)
Kind: D -/
noncomputable def punishU22 (x₀ : Val P.U) : ParentVals G Val P.U → E P.U → Val P.U :=
  fun paU e =>
    if P.Need M π (P.restrictH hPaH paU) ∧ P.readS hSU paU ≠ P.s0 then x₀
    else M.f P.U P.kU' paU e

/-- The bad event of Lemma 22: `{Pa_H ∈ A ∧ S ≠ 0}`.
Source: carey-everitt-2023 Lemma 22 proof
Kind: D -/
def bad22 : Set (Pt E) := {ε | P.Need M π (P.paH M π ε) ∧ M.ev π ε P.S ≠ P.s0}

variable (x₀ : Val P.U)

/-- The punished model `M_{g^U}` of Lemma 22 (with `g^H = f^H`).
Source: carey-everitt-2023 Lemma 22
Kind: D -/
noncomputable def M22 : Scim C E := M.softAt P.U P.kU' (P.punishU22 M π hPaH hSU x₀)

open Classical in
lemma Uval_M22 (ε : Pt E) :
    P.Uval (P.M22 M π hPaH hSU x₀) π ε =
      if ε ∈ P.bad22 M π then C.utilVal P.U P.kU x₀ else P.Uval M π ε := by
  classical
  unfold M22
  rw [Uval_softU, punishU22, restrictH_parentConfig, readS_parentConfig]
  by_cases h : ε ∈ P.bad22 M π
  · have h' : P.Need M π (parentConfig G Val (M.ev π ε) P.H) ∧ M.ev π ε P.S ≠ P.s0 := h
    rw [if_pos h', if_pos h]
  · have h' : ¬ (P.Need M π (parentConfig G Val (M.ev π ε) P.H) ∧ M.ev π ε P.S ≠ P.s0) := h
    rw [if_neg h', if_neg h, Uval_eq_f]

lemma US0val_M22 (ε : Pt E) : P.US0val (P.M22 M π hPaH hSU x₀) π ε = P.US0val M π ε := by
  classical
  unfold M22
  refine P.US0val_softU M π _ ε hSU fun paU e hS => ?_
  unfold punishU22
  rw [if_neg]
  rintro ⟨-, hne⟩
  exact hne hS

lemma paH_M22 (ε : Pt E) : P.paH (P.M22 M π hPaH hSU x₀) π ε = P.paH M π ε :=
  P.paH_softU M π _ ε

lemma ctxH_M22 (pa : ParentVals G Val P.H) :
    P.ctxH (P.M22 M π hPaH hSU x₀) π pa = P.ctxH M π pa :=
  P.ctxH_softU M π _ pa

lemma ev_M22_H (ε : Pt E) : (P.M22 M π hPaH hSU x₀).ev π ε P.H = M.ev π ε P.H :=
  P.ev_softU_of_ne M π _ ε P.H_ne_U

lemma condEUS0_M22 (pa : ParentVals G Val P.H) :
    P.condEUS0 (P.M22 M π hPaH hSU x₀) π pa = P.condEUS0 M π pa := by
  unfold condEUS0
  rw [ctxH_M22]
  exact condExpect_congr M.μ fun ε _ _ => P.US0val_M22 M π hPaH hSU x₀ ε

/-- With `x₀` below every realised utility, the punished utility is pointwise at most the original.
Source: carey-everitt-2023 Lemma 22 proof, eq. (4) ("can only decrease `E[U | pa_H]`")
Kind: L -/
lemma condEU_M22_le (hx : ∀ ε, C.utilVal P.U P.kU x₀ ≤ P.Uval M π ε) (pa : ParentVals G Val P.H) :
    P.condEU (P.M22 M π hPaH hSU x₀) π pa ≤ P.condEU M π pa := by
  unfold condEU
  rw [ctxH_M22]
  refine condExpect_mono M.μ fun ε _ _ => ?_
  rw [Uval_M22]
  split_ifs with h
  · exact hx ε
  · exact le_rfl

/-- Where need is absent, the punishment is inert and the conditional utility is unchanged.
Source: carey-everitt-2023 Lemma 22 proof, case (iii)
Kind: L -/
lemma condEU_M22_of_not_need {pa : ParentVals G Val P.H} (hpa : ¬ P.Need M π pa) :
    P.condEU (P.M22 M π hPaH hSU x₀) π pa = P.condEU M π pa := by
  unfold condEU
  rw [ctxH_M22]
  refine condExpect_congr M.μ fun ε hε _ => ?_
  rw [Uval_M22, if_neg]
  rintro ⟨hneed, -⟩
  exact hpa (hε ▸ hneed)

/-- Under the bound, need is the same in `M` and in `M_{g^U}` at every context.
Source: carey-everitt-2023 Lemma 22 proof, cases (i)–(iii)
Kind: P -/
lemma need_M22_iff (hx : ∀ ε, C.utilVal P.U P.kU x₀ ≤ P.Uval M π ε) (pa : ParentVals G Val P.H) :
    P.Need (P.M22 M π hPaH hSU x₀) π pa ↔ P.Need M π pa := by
  unfold Need
  rw [condEUS0_M22]
  constructor
  · intro h
    by_contra hn
    rw [condEU_M22_of_not_need P M π hPaH hSU x₀ hn] at h
    exact hn h
  · intro h
    exact lt_of_le_of_lt (P.condEU_M22_le M π hPaH hSU x₀ hx pa) h

/-- **Strong vigilance preservation** (Lemma 22 (1)): `C(ε)` is the same in `M^π` and `M^π_{g^U}`.
Source: carey-everitt-2023 Lemma 22 (1) (l. 355)
Kind: P -/
lemma vigilant_M22_iff (hx : ∀ ε, C.utilVal P.U P.kU x₀ ≤ P.Uval M π ε) (ε : Pt E) :
    P.Vigilant M π ε ↔ P.Vigilant (P.M22 M π hPaH hSU x₀) π ε := by
  unfold Vigilant
  rw [paH_M22, ev_M22_H, need_M22_iff P M π hPaH hSU x₀ hx]

/-- The bad event has positive probability when vigilance is not ensured (the consistency step of
Lemma 22's proof of (2)).
Source: carey-everitt-2023 Lemma 22 proof (2) ("it follows from consistency that `P(S = 0 | pa_H) < 1`")
Kind: P -/
lemma prob_bad22_pos (hnv : ¬ P.EnsuresVigilance M π) : 0 < M.μ.prob (P.bad22 M π) := by
  rw [ensuresVigilance_iff] at hnv
  push Not at hnv
  obtain ⟨ε₁, hε₁, hnvig⟩ := hnv
  unfold Vigilant at hnvig
  push Not at hnvig
  obtain ⟨hneed, -⟩ := hnvig
  by_contra hz
  push Not at hz
  have hz' : M.μ.prob (P.bad22 M π) = 0 := le_antisymm hz (M.μ.prob_nonneg _)
  refine absurd (P.condEU_eq_condEUS0_of_shut M π (P.paH M π ε₁) fun ε hε hctx => ?_)
    (ne_of_lt hneed)
  by_contra hS
  exact not_mem_of_prob_eq_zero M.μ hz' hε ⟨hctx ▸ hneed, hS⟩

/-- `E_{g^U}[U] = u(x₀) · P(bad) + K` with `K` independent of `x₀`.
Source: carey-everitt-2023 Lemma 22 proof (2)
Kind: L -/
lemma EU_M22 : P.EU (P.M22 M π hPaH hSU x₀) π =
    C.utilVal P.U P.kU x₀ * M.μ.prob (P.bad22 M π) + expectOn M.μ (P.bad22 M π)ᶜ (P.Uval M π) := by
  unfold EU
  rw [show (P.M22 M π hPaH hSU x₀).μ = M.μ from rfl,
    expect_eq_expectOn_add_expectOn_compl M.μ (P.bad22 M π), ← expectOn_const]
  congr 1
  · exact expectOn_congr M.μ fun ε hε _ => by rw [Uval_M22, if_pos hε]
  · exact expectOn_congr M.μ fun ε hε _ => by rw [Uval_M22, if_neg hε]

lemma EUS0_M22 : P.EUS0 (P.M22 M π hPaH hSU x₀) π = P.EUS0 M π := by
  unfold EUS0
  rw [show (P.M22 M π hPaH hSU x₀).μ = M.μ from rfl]
  simp only [expect]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [US0val_M22]

include hPaH hSU in
/-- **Lemma 22 (vigilance only-if).** If `π` does not ensure vigilance in `M`, then for every `δ`
there is a utility intervention `g^U` (reading `Pa_H` and `S`) such that (1) vigilance is *equal*
in `M^π` and `M^π_{g^U}` at every `ε`, and (2) `π` neither weakly outperforms shutdown nor is
beneficial in `M_{g^U}`: `E_{g^U}[U] < E_{g^U}[U_{S=0}]` and `E_{g^U}[U] < δ`.
Source: carey-everitt-2023 Lemma 22 (l. 355–375)
Kind: P
Fidelity: exact
Hyps: (c) `hPaH`, `hSU` — the paper enlarges `Pa_U` to `Pa_U ∪ Pa_H ∪ {S}` inside the proof; here `U` must already read them. (c) `hrich` — the paper enlarges the utility domain by `−α`; here the domain must contain arbitrarily negative values (automatic for `Val U = ℝ`). -/
theorem lemma22_vigilance_only_if (hrich : ∀ b : ℝ, ∃ x : Val P.U, C.utilVal P.U P.kU x < b)
    (hnv : ¬ P.EnsuresVigilance M π) (δ : ℝ) :
    ∃ gU : ParentVals G Val P.U → E P.U → Val P.U,
      (∀ ε, P.Vigilant M π ε ↔ P.Vigilant (M.softAt P.U P.kU' gU) π ε) ∧
      P.EU (M.softAt P.U P.kU' gU) π < P.EUS0 (M.softAt P.U P.kU' gU) π ∧
      P.EU (M.softAt P.U P.kU' gU) π < δ := by
  classical
  have hp : 0 < M.μ.prob (P.bad22 M π) := P.prob_bad22_pos M π hnv
  haveI : Nonempty (Pt E) := M.μ.nonempty_carrier
  obtain ⟨ε₀, -, hε₀⟩ := Finset.exists_min_image Finset.univ (P.Uval M π) Finset.univ_nonempty
  set m := P.Uval M π ε₀ with hm
  set K := expectOn M.μ (P.bad22 M π)ᶜ (P.Uval M π) with hK
  set L := P.EUS0 M π with hL
  obtain ⟨x₀, hx₀⟩ := hrich (min m ((min L δ - K) / M.μ.prob (P.bad22 M π)))
  have hxm : ∀ ε, C.utilVal P.U P.kU x₀ ≤ P.Uval M π ε := fun ε =>
    le_trans (le_of_lt (lt_of_lt_of_le hx₀ (min_le_left _ _))) (hε₀ ε (Finset.mem_univ _))
  have hxb : C.utilVal P.U P.kU x₀ * M.μ.prob (P.bad22 M π) < min L δ - K := by
    have := lt_of_lt_of_le hx₀ (min_le_right _ _)
    rwa [lt_div_iff₀ hp] at this
  refine ⟨P.punishU22 M π hPaH hSU x₀, P.vigilant_M22_iff M π hPaH hSU x₀ hxm, ?_, ?_⟩
  · show P.EU (P.M22 M π hPaH hSU x₀) π < P.EUS0 (P.M22 M π hPaH hSU x₀) π
    rw [EU_M22, EUS0_M22]
    have := min_le_left L δ
    linarith
  · show P.EU (P.M22 M π hPaH hSU x₀) π < δ
    rw [EU_M22]
    have := min_le_right L δ
    linarith

/-- A shift with `g^H = f^H` is the soft intervention at `U` alone.
Source: none: infrastructure
Kind: L -/
lemma shift_fH (gU : ParentVals G Val P.U → E P.U → Val P.U) :
    P.shift M ⟨M.f P.H P.kH', gU⟩ = M.softAt P.U P.kU' gU := by
  unfold shift
  congr 1
  unfold Scim.softAt
  cases M with
  | mk P' f =>
    simp only
    congr 1
    exact Function.update_eq_self P.H f

end Lemma22

/-! ### Lemma 23: obedience only-if (repaired construction) -/

section Lemma23

variable (hPaH : G.parents P.H ⊆ G.parents P.U) (hSU : G.Adj P.S P.U)
variable (pa' : ParentVals G Val P.H) (x₀ : Val P.U)

open Classical in
/-- **Lemma 23's `g^H`**: force the request at the human context `pa'_H`, keep `f^H` elsewhere.
Source: carey-everitt-2023 Lemma 23 proof (l. 383)
Kind: D -/
noncomputable def forceH : ParentVals G Val P.H → E P.H → Val P.H :=
  fun pa e => if pa = pa' then P.h0 else M.f P.H P.kH' pa e

open Classical in
/-- **Lemma 23's `g^U`, repaired**: punish disobedience (`S ≠ 0`) *at the context `pa'_H`* only
(the paper punishes `H = 0 ∧ S ≠ 0` at every context, which breaks its case (iii); finding F4).
Source: carey-everitt-2023 Lemma 23 proof (l. 383), repaired
Kind: D
Fidelity: variant: punishment restricted to `pa'_H` -/
noncomputable def punishU23 : ParentVals G Val P.U → E P.U → Val P.U :=
  fun paU e =>
    if P.restrictH hPaH paU = pa' ∧ P.readS hSU paU ≠ P.s0 then x₀ else M.f P.U P.kU' paU e

/-- The model with only `g^H` applied.
Source: carey-everitt-2023 Lemma 23
Kind: D -/
noncomputable def M23H : Scim C E := M.softAt P.H P.kH' (P.forceH M pa')

/-- Lemma 23's shift `(g^H, g^U)`.
Source: carey-everitt-2023 Lemma 23
Kind: D -/
noncomputable def shift23 : P.Shift E := ⟨P.forceH M pa', P.punishU23 M hPaH hSU pa' x₀⟩

/-- The bad event of Lemma 23: `{Pa_H = pa'_H ∧ S_{g^H} ≠ 0}`.
Source: carey-everitt-2023 Lemma 23 proof (2)
Kind: D -/
def bad23 : Set (Pt E) := {ε | P.paH M π ε = pa' ∧ (P.M23H M pa').ev π ε P.S ≠ P.s0}

lemma shift_shift23 :
    P.shift M (P.shift23 M hPaH hSU pa' x₀) =
      (P.M23H M pa').softAt P.U P.kU' (P.punishU23 M hPaH hSU pa' x₀) := rfl

lemma paH_M23H (ε : Pt E) : P.paH (P.M23H M pa') π ε = P.paH M π ε := by
  unfold paH Scim.ev M23H
  rw [Scim.withPolicy_softAt]
  exact Scm.parentConfig_softAt _ C.acyclic ε P.H _

lemma ctxH_M23H (pa : ParentVals G Val P.H) : P.ctxH (P.M23H M pa') π pa = P.ctxH M π pa := by
  ext ε
  simp [ctxH, paH_M23H]

open Classical in
/-- Under `g^H`, the request is forced at `pa'_H` and unchanged elsewhere.
Source: carey-everitt-2023 Lemma 23 proof (1), cases (i)–(iii)
Kind: L -/
lemma ev_M23H_H (ε : Pt E) :
    (P.M23H M pa').ev π ε P.H = if P.paH M π ε = pa' then P.h0 else M.ev π ε P.H := by
  classical
  unfold Scim.ev M23H
  rw [Scim.withPolicy_softAt, Scm.eval_softAt_self]
  show (if P.paH M π ε = pa' then P.h0 else M.f P.H P.kH' (P.paH M π ε) (ε P.H)) = _
  by_cases h : P.paH M π ε = pa'
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact (Scim.ev_of_ne M π ε P.kH').symm

/-- Off `pa'_H`, `g^H` has no effect on any node.
Source: carey-everitt-2023 Lemma 23 proof (1), case (iii) ("it has no effect")
Kind: L -/
lemma ev_M23H_of_ne (ε : Pt E) (hpa : P.paH M π ε ≠ pa') (v : V) :
    (P.M23H M pa').ev π ε v = M.ev π ε v := by
  classical
  unfold Scim.ev M23H
  rw [Scim.withPolicy_softAt]
  refine Scm.eval_congr C.acyclic ε v fun w _ => ?_
  by_cases hw : w = P.H
  · subst hw
    rw [Scm.softAt_f_self]
    unfold forceH
    have hpa' : parentConfig G Val ((M.withPolicy π).eval C.acyclic ε) P.H ≠ pa' := hpa
    rw [if_neg hpa', Scim.withPolicy_f_of_ne M π P.kH']
  · rw [Scm.softAt_f_of_ne _ hw]

/-- At `pa'_H`, `g^H` acts as `do(H = 0)` on every node.
Source: carey-everitt-2023 Lemma 23 proof (2)
Kind: L -/
lemma ev_M23H_of_eq (ε : Pt E) (hpa : P.paH M π ε = pa') (v : V) :
    (P.M23H M pa').ev π ε v = P.evH0 M π ε v := by
  classical
  unfold Scim.ev M23H evH0
  rw [Scim.withPolicy_softAt]
  refine Scm.eval_congr C.acyclic ε v fun w _ => ?_
  by_cases hw : w = P.H
  · subst hw
    rw [Scm.softAt_f_self, Scm.doAt_f_self]
    unfold forceH
    have hpa' : parentConfig G Val (((M.withPolicy π).doAt P.H P.h0).eval C.acyclic ε) P.H = pa' := by
      rw [doAt_eq_softAt, Scm.parentConfig_softAt]
      exact hpa
    rw [if_pos hpa']
  · rw [Scm.softAt_f_of_ne _ hw, Scm.doAt_f_of_ne _ hw]

/-- `S` is no ancestor-or-self of `H`.
Source: none: infrastructure
Kind: L -/
lemma not_ancSelf_H_S : ¬ Scm.AncSelf G P.H P.S := by
  rintro (h | h)
  · exact P.H_ne_S h.symm
  · exact C.acyclic P.H (Relation.TransGen.trans (P.path₂.trans P.path₃) h)

/-- Off `pa'_H`, `U_{S=0}` is unchanged by `g^H`.
Source: carey-everitt-2023 Lemma 23 proof (1), case (iii)
Kind: L -/
lemma evS0_M23H_of_ne (ε : Pt E) (hpa : P.paH M π ε ≠ pa') (v : V) :
    P.evS0 (P.M23H M pa') π ε v = P.evS0 M π ε v := by
  classical
  unfold evS0 M23H
  rw [Scim.withPolicy_softAt]
  refine Scm.eval_congr C.acyclic ε v fun w _ => ?_
  by_cases hw : w = P.H
  · subst hw
    rw [Scm.doAt_f_of_ne _ P.H_ne_S, Scm.doAt_f_of_ne _ P.H_ne_S, Scm.softAt_f_self]
    unfold forceH
    have hpc : parentConfig G Val (((M.withPolicy π).doAt P.S P.s0).eval C.acyclic ε) P.H =
        P.paH M π ε := by
      rw [doAt_eq_softAt]
      exact Scm.parentConfig_softAt_of_not_ancSelf _ C.acyclic ε _ (P.not_ancSelf_H_S)
    rw [hpc, if_neg hpa, Scim.withPolicy_f_of_ne M π P.kH']
  · by_cases hwS : w = P.S
    · subst hwS
      rw [Scm.doAt_f_self, Scm.doAt_f_self]
    · rw [Scm.doAt_f_of_ne _ hwS, Scm.doAt_f_of_ne _ hwS, Scm.softAt_f_of_ne _ hw]

lemma M23H_f_U (h : C.kind P.U ≠ .decision) (paU : ParentVals G Val P.U) (e : E P.U) :
    (P.M23H M pa').f P.U h paU e = M.f P.U h paU e := by
  show Function.update M.f P.H _ P.U h paU e = _
  rw [Function.update_of_ne P.H_ne_U.symm]

open Classical in
lemma Uval_M23 (ε : Pt E) :
    P.Uval (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π ε =
      if ε ∈ P.bad23 M π pa' then C.utilVal P.U P.kU x₀ else P.Uval (P.M23H M pa') π ε := by
  rw [shift_shift23, Uval_softU]
  unfold punishU23
  rw [restrictH_parentConfig, readS_parentConfig]
  have hpc : parentConfig G Val ((P.M23H M pa').ev π ε) P.H = P.paH M π ε := P.paH_M23H M π pa' ε
  rw [hpc]
  by_cases h : ε ∈ P.bad23 M π pa'
  · have h' : P.paH M π ε = pa' ∧ (P.M23H M pa').ev π ε P.S ≠ P.s0 := h
    rw [if_pos h', if_pos h]
  · have h' : ¬ (P.paH M π ε = pa' ∧ (P.M23H M pa').ev π ε P.S ≠ P.s0) := h
    rw [if_neg h', if_neg h, Uval_eq_f, M23H_f_U]

lemma US0val_M23 (ε : Pt E) :
    P.US0val (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π ε = P.US0val (P.M23H M pa') π ε := by
  classical
  rw [shift_shift23]
  refine P.US0val_softU _ π _ ε hSU fun paU e hS => ?_
  unfold punishU23
  rw [if_neg]
  · exact (P.M23H_f_U M pa' _ paU e).symm
  · rintro ⟨-, hne⟩
    exact hne hS

lemma paH_M23 (ε : Pt E) : P.paH (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π ε = P.paH M π ε := by
  rw [shift_shift23, paH_softU, paH_M23H]

lemma ctxH_M23 (pa : ParentVals G Val P.H) :
    P.ctxH (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π pa = P.ctxH M π pa := by
  ext ε
  simp [ctxH, paH_M23]

lemma ev_M23_H (ε : Pt E) :
    (P.shift M (P.shift23 M hPaH hSU pa' x₀)).ev π ε P.H = (P.M23H M pa').ev π ε P.H := by
  rw [shift_shift23]
  exact P.ev_softU_of_ne _ π _ ε P.H_ne_U

/-- Off `pa'_H`, need is the same in `M` and in `M_{g^H, g^U}` (the repaired case (iii)).
Source: carey-everitt-2023 Lemma 23 proof (1), case (iii), repaired
Kind: P -/
lemma need_M23_iff_of_ne {pa : ParentVals G Val P.H} (hpa : pa ≠ pa') :
    P.Need (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π pa ↔ P.Need M π pa := by
  classical
  unfold Need condEU condEUS0
  rw [ctxH_M23]
  have h1 : condExpect M.μ (P.ctxH M π pa) (P.Uval (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π) =
      condExpect M.μ (P.ctxH M π pa) (P.Uval M π) := by
    refine condExpect_congr M.μ fun ε hε _ => ?_
    have hε' : P.paH M π ε = pa := hε
    rw [Uval_M23, if_neg (fun h => hpa (hε'.symm.trans h.1))]
    unfold Uval uU
    rw [P.ev_M23H_of_ne M π pa' ε (fun h => hpa (hε'.symm.trans h))]
  have h2 : condExpect M.μ (P.ctxH M π pa) (P.US0val (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π) =
      condExpect M.μ (P.ctxH M π pa) (P.US0val M π) := by
    refine condExpect_congr M.μ fun ε hε _ => ?_
    have hε' : P.paH M π ε = pa := hε
    rw [US0val_M23]
    unfold US0val uU
    rw [P.evS0_M23H_of_ne M π pa' ε (fun h => hpa (hε'.symm.trans h))]
  rw [show (P.shift M (P.shift23 M hPaH hSU pa' x₀)).μ = M.μ from rfl, h1, h2]

/-- **Vigilance preservation of the repaired Lemma 23 pair.** Cases: the human already requests
(`H = 0` stays), the context is `pa'_H` (the request is forced), or neither (nothing changes,
including need).
Source: carey-everitt-2023 Lemma 23 proof (1), repaired
Kind: P -/
lemma vigilancePreserving_shift23 : P.VigilancePreserving M π (P.shift23 M hPaH hSU pa' x₀) := by
  classical
  intro ε hvig hneed
  rw [ev_M23_H, ev_M23H_H]
  by_cases hpa : P.paH M π ε = pa'
  · rw [if_pos hpa]
  · rw [if_neg hpa]
    apply hvig
    rw [paH_M23] at hneed
    exact (P.need_M23_iff_of_ne M π hPaH hSU pa' x₀ hpa).mp hneed

lemma EU_M23 : P.EU (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π =
    C.utilVal P.U P.kU x₀ * M.μ.prob (P.bad23 M π pa') +
      expectOn M.μ (P.bad23 M π pa')ᶜ (P.Uval (P.M23H M pa') π) := by
  classical
  unfold EU
  rw [show (P.shift M (P.shift23 M hPaH hSU pa' x₀)).μ = M.μ from rfl,
    expect_eq_expectOn_add_expectOn_compl M.μ (P.bad23 M π pa'), ← expectOn_const]
  congr 1
  · exact expectOn_congr M.μ fun ε hε _ => by rw [Uval_M23, if_pos hε]
  · exact expectOn_congr M.μ fun ε hε _ => by rw [Uval_M23, if_neg hε]

lemma EUS0_M23 : P.EUS0 (P.shift M (P.shift23 M hPaH hSU pa' x₀)) π = P.EUS0 (P.M23H M pa') π := by
  unfold EUS0
  rw [show (P.shift M (P.shift23 M hPaH hSU pa' x₀)).μ = M.μ from rfl,
    show (P.M23H M pa').μ = M.μ from rfl]
  simp only [expect]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [US0val_M23]

include hPaH hSU in
/-- **Lemma 23 (obedience only-if), with the repaired construction.** If `π` is not obedient in
`M`, then for every `δ` there is a vigilance-preserving shift `(g^H, g^U)` under which `π` neither
weakly outperforms shutdown nor is beneficial: `E_g[U] < E_g[U_{S=0}]` and `E_g[U] < δ`. `g^H`
forces the request at a context `pa'_H` where disobedience under `do(H = 0)` has positive
probability; `g^U` punishes `S ≠ 0` at that context.
Source: carey-everitt-2023 Lemma 23 (l. 379–397), construction repaired (finding F4)
Kind: P
Fidelity: exact (statement); variant: construction
Hyps: (c) `hPaH`, `hSU`, `hrich` as in Lemma 22. -/
theorem lemma23_obedience_only_if (hrich : ∀ b : ℝ, ∃ x : Val P.U, C.utilVal P.U P.kU x < b)
    (hno : ¬ P.Obedient M π) (δ : ℝ) :
    ∃ g : P.Shift E, P.VigilancePreserving M π g ∧
      P.EU (P.shift M g) π < P.EUS0 (P.shift M g) π ∧ P.EU (P.shift M g) π < δ := by
  classical
  rw [obedient_iff] at hno
  push Not at hno
  obtain ⟨ε₁, hε₁, hS⟩ := hno
  have hp : 0 < M.μ.prob (P.bad23 M π (P.paH M π ε₁)) :=
    prob_pos_of_mass_pos M.μ hε₁ ⟨rfl, by rw [P.ev_M23H_of_eq M π _ ε₁ rfl]; exact hS⟩
  set K := expectOn M.μ (P.bad23 M π (P.paH M π ε₁))ᶜ (P.Uval (P.M23H M (P.paH M π ε₁)) π) with hK
  set L := P.EUS0 (P.M23H M (P.paH M π ε₁)) π with hL
  obtain ⟨x₀, hx₀⟩ := hrich ((min L δ - K) / M.μ.prob (P.bad23 M π (P.paH M π ε₁)))
  have hxb : C.utilVal P.U P.kU x₀ * M.μ.prob (P.bad23 M π (P.paH M π ε₁)) < min L δ - K := by
    rwa [lt_div_iff₀ hp] at hx₀
  refine ⟨P.shift23 M hPaH hSU (P.paH M π ε₁) x₀,
    P.vigilancePreserving_shift23 M π hPaH hSU _ x₀, ?_, ?_⟩
  · rw [EU_M23, EUS0_M23]
    have := min_le_left L δ
    linarith
  · rw [EU_M23]
    have := min_le_right L δ
    linarith

end Lemma23

/-! ### Prop. 20 and Theorem 14 -/

/-- **Prop. 20 (non-obstruction ⇒ vigilance and obedience).** If `π` is non-obstructive under every
vigilance-preserving shift, it ensures vigilance (else Lemma 22's `g^U` with `g^H = f^H` obstructs)
and is obedient (else Lemma 23's pair obstructs).
Source: carey-everitt-2023 Prop. 20 (l. 349), Appendix B
Kind: P
Fidelity: exact
Hyps: (c) `hPaH`, `hSU` — `U` reads `Pa_H` and `S` (the paper enlarges `Pa_U` in the proof); (c) `hrich` — arbitrarily negative utility values available (the paper enlarges the domain). -/
theorem obedient_and_ensuresVigilance_of_nonObstructive
    (hPaH : G.parents P.H ⊆ G.parents P.U) (hSU : G.Adj P.S P.U)
    (hrich : ∀ b : ℝ, ∃ x : Val P.U, C.utilVal P.U P.kU x < b)
    (h : P.NonObstructiveUnder M π {g | P.VigilancePreserving M π g}) :
    P.Obedient M π ∧ P.EnsuresVigilance M π := by
  by_cases hv : P.EnsuresVigilance M π
  · refine ⟨?_, hv⟩
    by_contra ho
    obtain ⟨g, hvp, hlt, -⟩ := P.lemma23_obedience_only_if M π hPaH hSU hrich ho 0
    exact absurd (h g hvp) (not_le.mpr hlt)
  · exfalso
    obtain ⟨gU, hiff, hlt, -⟩ := P.lemma22_vigilance_only_if M π hPaH hSU hrich hv 0
    have hvp : P.VigilancePreserving M π ⟨M.f P.H P.kH', gU⟩ := fun ε hε => by
      rw [shift_fH]
      exact (hiff ε).mp hε
    have := h _ hvp
    rw [shift_fH] at this
    exact absurd this (not_le.mpr hlt)

/-- **Theorem 14 (non-obstruction is equivalent to obedience and vigilance).** `π` is obedient and
ensures vigilance iff it is non-obstructive under every vigilance-preserving shift. ⇒ needs
nothing; ⇐ needs `U` to read `Pa_H` and `S` and a utility domain unbounded below.
Source: carey-everitt-2023 Thm 14 (l. 225)
Kind: P
Fidelity: exact (⇒); variant: intervention class made explicit (⇐)
Hyps: (c) `hPaH`, `hSU`, `hrich` (used by ⇐ only). -/
theorem obedient_and_ensuresVigilance_iff_nonObstructive
    (hPaH : G.parents P.H ⊆ G.parents P.U) (hSU : G.Adj P.S P.U)
    (hrich : ∀ b : ℝ, ∃ x : Val P.U, C.utilVal P.U P.kU x < b) :
    (P.Obedient M π ∧ P.EnsuresVigilance M π) ↔
      P.NonObstructiveUnder M π {g | P.VigilancePreserving M π g} :=
  ⟨fun h => P.nonObstructive_of_obedient_of_ensuresVigilance M π h.1 h.2,
    P.obedient_and_ensuresVigilance_of_nonObstructive M π hPaH hSU hrich⟩

end ShutdownSpec

end Cleanroom.Corrigibility.CorrScimCid
