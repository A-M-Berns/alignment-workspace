import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpFairnessReloc.Output
import Cleanroom.Decision.DpLocalOpt.Sia

/-!
# `dp-faithful-udt` — definitions of record (T1)

Package `dp-faithful-udt` (area `decision`), namespace `Cleanroom.Decision.DpFaithfulUdt`. This
file holds the definitions of record for [[decision-problems-v2]] §4 Definition 17 (the four
procedures), Definition 18 (the advocacy theories), the counterfactual slot `cf` with v2
Definition 2's success axiom, the *masked* form of Definition 11 (prior calibration under a
full-support self-model), the **disposition coordinate of record** `polEv` (the relocated tree's
`pol_d = a` event, [[dp-fairness-reloc]]'s `nu_pol_eq`), Theorem 2's point-game best reply `BR`
and the Nash predicate. Every later file imports this one.

## Modelling choices, disclosed once here

* **`UDT_{s°,ρ}` is `EDT` with the constant state assignment `s°` and act events `ρ`.** v2's two
  displays are literally the same formula with `s_d := s°` and `a := ρ_d(a)`, so `udtDomain`,
  `udtArgmax`, `udtProc` and `TUdt` are *defined* through `dp-calibration`'s `APlus`,
  `argmaxPlus`, `edtProc` and `TEdt` (equation lemmas are `rfl`). This is the mandate's "build it
  exactly as `edtProc` is built", taken literally; the tie convention (uniform over the argmax,
  `Unif(A_d)` at an empty domain) and Definition 18's escape clause are therefore inherited
  unchanged, which the `(⅓,⅔)` refutation in `SelfConfirming.lean` depends on.
* **`ρ : (d : ι) → acts d → Finset Ω`** has the type of `actEv`; v2's `ρ_d(a) ∈ 𝓔 ∖ {⊥}` is not
  enforced — the domain guard `0 < P_{s°}(ρ_d(a))` does the work. An enrichment `𝓔′ ⊇ 𝓔` is a
  change of world type (`RW Ω acts U`), never a new algebra structure.
* **`cf` is a total function `Finset Ω → State Ω K`** (`Cf`), outside `State` (which has no `cf`
  slot by `dp-calibration`'s decision); v2 Definition 2's success axiom is the predicate
  `Success`, carried as a hypothesis where a theorem needs it. `cdtProc`/`cudtProc` consume a
  `Cf`; the state `s` whose slot it is does not enter their definition and is not a parameter.
* **`polEv U d a`** is the event `{w : w.2 d = a}` of `RW Ω acts U` when `d ∈ U`, and `∅` (junk:
  prior probability `0`, so the point falls to the uniform fallback) when `d ∉ U`; every theorem
  quantifies over `d ∈ U`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Total argmax and its uniform mixture -/

section argmax

variable {α : Type} [Fintype α]

/-- `argmax_{a ∈ A} f(a)`, over the whole finite type.
Source: [[decision-problems-v2]] §4 Definition 17 (`CDT(d) := Unif argmax_{a ∈ A_d} …`)
Kind: D -/
def argmaxFull (f : α → K) : Finset α := Finset.univ.filter fun a => ∀ b, f b ≤ f a

/-- Membership in the total argmax. Source: none: infrastructure. Kind: L -/
theorem mem_argmaxFull (f : α → K) (a : α) : a ∈ argmaxFull f ↔ ∀ b, f b ≤ f a := by
  simp [argmaxFull]

/-- The total argmax over a nonempty finite type is nonempty.
Source: none: infrastructure
Kind: L -/
theorem argmaxFull_nonempty [Nonempty α] (f : α → K) : (argmaxFull f).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  exact ⟨a, (mem_argmaxFull f a).mpr fun b => ha b (Finset.mem_univ b)⟩

/-- `Unif(argmax_{a ∈ A} f(a))`: Definition 17's uniform tie convention over a total argmax.
Source: [[decision-problems-v2]] §4 Definition 17 ("an argmax set becomes a mixed action by
uniform mixture")
Kind: D -/
def uniformArgmax [Nonempty α] [DecidableEq α] (f : α → K) : FinDistr K α :=
  uniformOn (argmaxFull f) (argmaxFull_nonempty f)

/-- The support of `Unif(argmax f)` is the argmax. Source: none: infrastructure. Kind: L -/
theorem uniformArgmax_w_pos_iff [Nonempty α] [DecidableEq α] (f : α → K) (a : α) :
    0 < (uniformArgmax (K := K) f).w a ↔ ∀ b, f b ≤ f a := by
  unfold uniformArgmax
  rw [uniformOn_w, ← mem_argmaxFull]
  split_ifs with h
  · simp only [h, iff_true]
    have : (0 : K) < (argmaxFull f).card := by
      exact_mod_cast Finset.card_pos.mpr (argmaxFull_nonempty f)
    exact inv_pos.mpr this
  · simp [h]

/-- `Unif(argmax f)` with a unique maximiser `a₀` is the point mass `δ_{a₀}`.
Source: none: infrastructure
Kind: L -/
theorem uniformArgmax_eq_pure [Nonempty α] [DecidableEq α] (f : α → K) (a₀ : α)
    (h : argmaxFull f = {a₀}) : uniformArgmax (K := K) f = FinDistr.pure a₀ := by
  apply FinDistr.ext'
  intro a
  simp only [uniformArgmax, uniformOn_w, FinDistr.pure_w, h, Finset.mem_singleton,
    Finset.card_singleton, Nat.cast_one, inv_one]

/-- `Unif(argmax f)` when every value ties is the uniform distribution.
Source: none: infrastructure
Kind: L -/
theorem uniformArgmax_eq_uniform [Nonempty α] [DecidableEq α] (f : α → K)
    (h : ∀ a b, f a = f b) : uniformArgmax (K := K) f = FinDistr.uniform := by
  apply FinDistr.ext'
  intro a
  have hall : argmaxFull f = Finset.univ := by
    ext b; simp only [mem_argmaxFull, Finset.mem_univ, iff_true]
    intro c; rw [h c b]
  simp only [uniformArgmax, uniformOn_w, hall, Finset.mem_univ, if_true, Finset.card_univ,
    FinDistr.uniform_w]

end argmax

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### Definition 17: the updateless pair `UDT_{s°,ρ}`, and Definition 18's `T_UDT` -/

section udt

variable (s₀ : State Ω K) (ρ : (d : ι) → acts d → Finset Ω)

/-- **Definition 17's maximisation domain for `UDT_{s°,ρ}`**: `{a : P_{s°}(ρ_d(a)) > 0}` — which
is `A_d^+` of `dp-calibration` with the constant state `s°` and the events `ρ_d(·)`.
Source: [[decision-problems-v2]] §4 Definition 17 (`a : P_{s°}(ρ_d(a)) > 0`)
Kind: D
Fidelity: exact -/
def udtDomain (d : ι) : Finset (acts d) := APlus (fun _ => s₀) ρ d

/-- Membership in the domain. Source: none: infrastructure. Kind: L -/
theorem mem_udtDomain (d : ι) (a : acts d) : a ∈ udtDomain s₀ ρ d ↔ 0 < s₀.pr (ρ d a) := by
  simp [udtDomain, APlus]

/-- **Definition 17's argmax for `UDT_{s°,ρ}`**: `argmax_{a : P_{s°}(ρ_d(a)) > 0} V_{s°}(ρ_d(a))`.
Source: [[decision-problems-v2]] §4 Definition 17
Kind: D
Fidelity: exact -/
def udtArgmax (d : ι) : Finset (acts d) := argmaxPlus (fun _ => s₀) ρ d

/-- Membership in the argmax. Source: none: infrastructure. Kind: L -/
theorem mem_udtArgmax (d : ι) (a : acts d) :
    a ∈ udtArgmax s₀ ρ d ↔
      0 < s₀.pr (ρ d a) ∧ ∀ b, 0 < s₀.pr (ρ d b) → s₀.V (ρ d b) ≤ s₀.V (ρ d a) := by
  unfold udtArgmax
  rw [mem_argmaxPlus]
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Definition 17's `UDT_{s°,ρ}`**:
`UDT_{s°,ρ}(d) := Unif argmax_{a : P_{s°}(ρ_d(a)) > 0} V_{s°}(ρ_d(a))`, `Unif(A_d)` when the
domain is empty. Literally `dp-calibration`'s `edtProc` with the constant state assignment
`fun _ => s°` and the act events `ρ` (`udtProc_eq_edtProc` is `rfl`): the updateless pair
evaluates the *disposition* `ρ_d(a)` at the *prior* `s°` by the same formula EDT applies to the
act at the current state.
Source: [[decision-problems-v2]] §4 Definition 17 (`UDT_{s°,ρ}`); Remark 4.1
Kind: D
Fidelity: exact (uniform tie convention and empty-domain fallback as v2 states them) -/
def udtProc : Proc ι acts K := edtProc (fun _ => s₀) ρ

/-- `UDT_{s°,ρ} = EDT[s_d := s°, a := ρ_d(a)]`. Source: [[decision-problems-v2]] Definition 17.
Kind: L -/
theorem udtProc_eq_edtProc : udtProc s₀ ρ = edtProc (fun _ => s₀) ρ := rfl

/-- The point value of `udtProc`: `Unif(udtArgmax)` when nonempty, else uniform.
Source: none: infrastructure
Kind: L -/
theorem udtProc_apply (d : ι) :
    udtProc s₀ ρ d =
      if h : (udtArgmax s₀ ρ d).Nonempty then uniformOn (udtArgmax s₀ ρ d) h
      else FinDistr.uniform := rfl

/-- **Definition 18's `T_{UDT_{s°,ρ}}` (advocacy)**: at every queried point whose domain is
nonempty, `supp C(d) ⊆ argmax_{a : P_{s°}(ρ_d(a)) > 0} V_{s°}(ρ_d(a))`; no constraint where the
domain is empty. `dp-calibration`'s `TEdt` at the constant state `s°` with events `ρ`
(`tUdt_iff_tEdt`), stated for a problem over any world type `Ω'` (the prior lives on an
enrichment of the problem's algebra; the theory reads only `queried B`).
Source: [[decision-problems-v2]] §4 Definition 18 ("`T_UDT_{s°,ρ}` … analogously, each with its
own act value and maximization domain")
Kind: D
Fidelity: exact -/
def TUdt {Ω' : Type} (C : Proc ι acts K) (B : Tree Ω' ι acts K) : Prop :=
  ∀ d ∈ queried B, (udtDomain s₀ ρ d).Nonempty → ∀ a, 0 < (C d).w a → a ∈ udtArgmax s₀ ρ d

/-- `T_UDT` unfolded. Source: none: infrastructure. Kind: L -/
theorem tUdt_iff {Ω' : Type} (C : Proc ι acts K) (B : Tree Ω' ι acts K) :
    TUdt s₀ ρ C B ↔
      ∀ d ∈ queried B, (udtDomain s₀ ρ d).Nonempty → ∀ a, 0 < (C d).w a → a ∈ udtArgmax s₀ ρ d :=
  Iff.rfl

/-- On the prior's own carrier, `T_UDT` is `T_EDT` at the constant state `s°`.
Source: [[decision-problems-v2]] §4 Definition 18
Kind: L -/
theorem tUdt_iff_tEdt (C : Proc ι acts K) (B : Tree Ω ι acts K) :
    TUdt s₀ ρ C B ↔ TEdt (fun _ => s₀) ρ C B := Iff.rfl

/-- **`T_UDT(UDT_{s°,ρ}, B)` for every `B`** (the `∃C ∀B` shape survives for the updateless pair
once the parameters are fixed).
Source: [[decision-problems-v2]] §4 Definition 18 ("the uniform-tie procedures of Definition 17
are canonical witnesses")
Kind: L
Fidelity: exact -/
theorem tUdt_udtProc {Ω' : Type} (B : Tree Ω' ι acts K) : TUdt s₀ ρ (udtProc s₀ ρ) B := by
  intro d _ hne a ha
  have hne' : (udtArgmax s₀ ρ d).Nonempty := argmaxPlus_nonempty (fun _ => s₀) ρ d hne
  rw [udtProc_apply, dif_pos hne', uniformOn_w] at ha
  by_contra hc
  rw [if_neg hc] at ha
  exact lt_irrefl 0 ha

/-- `UDT_{s°,ρ}` is zero-respecting for its own domain (Definition 12 transposed to `ρ`).
Source: [[decision-problems-v2]] §4 Definition 17 ("EDT is zero-respecting by construction"),
transposed
Kind: L -/
theorem udtProc_zeroRespecting : ZeroRespecting (fun _ => s₀) ρ (udtProc s₀ ρ) :=
  edtProc_zeroRespecting (fun _ => s₀) ρ

/-- When the domain is all of `A_d`, the argmax is the total argmax of `V_{s°} ∘ ρ_d`.
Source: none: infrastructure
Kind: L -/
theorem udtArgmax_eq_argmaxFull (d : ι) (h : ∀ a, 0 < s₀.pr (ρ d a)) :
    udtArgmax s₀ ρ d = argmaxFull fun a => s₀.V (ρ d a) := by
  ext a
  rw [mem_udtArgmax, mem_argmaxFull]
  exact ⟨fun ⟨_, hmax⟩ b => hmax b (h b), fun hmax => ⟨h a, fun b _ => hmax b⟩⟩

/-- When the domain is all of `A_d`, `UDT_{s°,ρ}(d) = Unif argmax_a V_{s°}(ρ_d(a))`.
Source: `faithful.md` FA-5 ("the Definition 17 domain is all of `A_d`")
Kind: L -/
theorem udtProc_eq_uniformArgmax (d : ι) (h : ∀ a, 0 < s₀.pr (ρ d a)) :
    udtProc s₀ ρ d = uniformArgmax fun a => s₀.V (ρ d a) := by
  rw [udtProc_apply, udtArgmax_eq_argmaxFull s₀ ρ d h, dif_pos (argmaxFull_nonempty _)]
  rfl

end udt

/-! ### The counterfactual slot, Definition 2's success axiom, and the causal pair -/

section cf

/-- **The counterfactual structure** `cf : 𝓔 → states`, total on events (v2's `cf_s` returns a
probability–desirability pair at every non-`⊥` event). Kept outside `State` (which has no `cf`
slot by `dp-calibration`'s decision, Remark 3.11: `cf` is uncalibrated unless a calibration sense
says so).
Source: [[decision-problems-v2]] §1 Definition 2 (`cf_s : 𝓔 ∖ {⊥} → Δ × 𝓥`); Remark 3.11
Kind: D
Fidelity: variant: total on all events including `∅` (v2 excludes `⊥` by type; here `Success`
is required on nonempty events only) -/
abbrev Cf (Ω : Type) [Fintype Ω] [DecidableEq Ω] (K : Type) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : Type := Finset Ω → State Ω K

/-- **v2 Definition 2's success axiom**: `P^X(X) = 1` for every nonempty event `X`.
Source: [[decision-problems-v2]] §1 Definition 2 ("*success*: … `P^a_s(a) = 1`")
Kind: D
Fidelity: exact (on nonempty events; `⊥` is excluded by v2's type) -/
def Success (cf : Cf Ω K) : Prop := ∀ X : Finset Ω, X.Nonempty → (cf X).pr X = 1

variable (cf : Cf Ω K) (actEv : (d : ι) → acts d → Finset Ω) (ρ : (d : ι) → acts d → Finset Ω)

/-- **Definition 17's `CDT`**: `CDT(d) := Unif argmax_{a ∈ A_d} V^a_s(a)`, the supposed value of
the act under the state's counterfactual slot `cf`; total (the domain is all of `A_d`). The
state `s` whose slot `cf` is does not enter the formula and is not a parameter here.
Source: [[decision-problems-v2]] §4 Definition 17 (`CDT(d)`)
Kind: D
Fidelity: exact -/
def cdtProc : Proc ι acts K := fun d => uniformArgmax fun a => (cf (actEv d a)).V (actEv d a)

/-- **Definition 17's `cUDT_{s°,ρ}`**: `cUDT(d) := Unif argmax_{a ∈ A_d} V^{ρ_d(a)}_{s°}(ρ_d(a))`,
the supposed value of the *disposition* under the prior's counterfactual slot; total.
Source: [[decision-problems-v2]] §4 Definition 17 (`cUDT_{s°,ρ}`)
Kind: D
Fidelity: exact -/
def cudtProc : Proc ι acts K := fun d => uniformArgmax fun a => (cf (ρ d a)).V (ρ d a)

/-- CDT is total: its support at `d` is the (nonempty) argmax over all of `A_d`.
Source: [[decision-problems-v2]] §4 Definition 17 ("causal choice … is total, because `cf` is")
Kind: L -/
theorem cdtProc_w_pos_iff (d : ι) (a : acts d) :
    0 < (cdtProc cf actEv d).w a ↔
      ∀ b, (cf (actEv d b)).V (actEv d b) ≤ (cf (actEv d a)).V (actEv d a) :=
  uniformArgmax_w_pos_iff _ a

/-- cUDT is total likewise. Source: [[decision-problems-v2]] Definition 17. Kind: L -/
theorem cudtProc_w_pos_iff (d : ι) (a : acts d) :
    0 < (cudtProc cf ρ d).w a ↔ ∀ b, (cf (ρ d b)).V (ρ d b) ≤ (cf (ρ d a)).V (ρ d a) :=
  uniformArgmax_w_pos_iff _ a

/-- **Definition 18's `T_CDT`**: at every queried point, `supp C(d) ⊆ argmax_{a ∈ A_d} V^a(a)`.
Source: [[decision-problems-v2]] §4 Definition 18
Kind: D
Fidelity: exact -/
def TCdt {Ω' : Type} (C : Proc ι acts K) (B : Tree Ω' ι acts K) : Prop :=
  ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → a ∈ argmaxFull fun a => (cf (actEv d a)).V (actEv d a)

/-- **Definition 18's `T_{cUDT_{s°,ρ}}` at one point**: `supp C(d) ⊆ argmax_{a ∈ A_d}
V^{ρ_d(a)}(ρ_d(a))`.
Source: [[decision-problems-v2]] §4 Definition 18
Kind: D
Fidelity: exact -/
def TCudtAt (C : Proc ι acts K) (d : ι) : Prop :=
  ∀ a, 0 < (C d).w a → a ∈ argmaxFull fun a => (cf (ρ d a)).V (ρ d a)

/-- **Definition 18's `T_{cUDT_{s°,ρ}}`**: the clause at every queried point.
Source: [[decision-problems-v2]] §4 Definition 18
Kind: D
Fidelity: exact -/
def TCudt {Ω' : Type} (C : Proc ι acts K) (B : Tree Ω' ι acts K) : Prop :=
  ∀ d ∈ queried B, TCudtAt cf ρ C d

/-- `T_CDT(CDT, B)` for every `B`. Source: [[decision-problems-v2]] Definition 18 ("likewise CDT").
Kind: L -/
theorem tCdt_cdtProc {Ω' : Type} (B : Tree Ω' ι acts K) : TCdt cf actEv (cdtProc cf actEv) B := by
  intro d _ a ha
  rw [mem_argmaxFull]
  exact (cdtProc_w_pos_iff cf actEv d a).mp ha

/-- `T_cUDT(cUDT, B)` for every `B`. Source: [[decision-problems-v2]] Definition 18. Kind: L -/
theorem tCudt_cudtProc {Ω' : Type} (B : Tree Ω' ι acts K) : TCudt cf ρ (cudtProc cf ρ) B := by
  intro d _ a ha
  rw [mem_argmaxFull]
  exact (cudtProc_w_pos_iff cf ρ d a).mp ha

/-- A counterfactual structure built from one state per action at `d`, read back on the
`ρ`-events (`Cf.ofEvents_apply`); junk (`State.trivial`) elsewhere. This is how a per-disposition
family `a ↦ (P^a, V^a)` (D4's PDC, FA-7′(iv)'s R1 states) is packaged as v2's event-indexed `cf`.
Source: `firstperson.md` D4 ("`cf_{s_d}(ρ_d(a)) = (P^a, V^a)`"); `faithful.md` FA-7′(iv)
Kind: D -/
noncomputable def Cf.ofEvents [Nonempty Ω] (d : ι) (st : acts d → State Ω K) : Cf Ω K :=
  fun X => if h : ∃ a, ρ d a = X then st (Classical.choose h) else State.trivial

/-- When `ρ_d` is injective, `Cf.ofEvents` reads back the intended state on each `ρ_d(a)`.
Source: none: infrastructure
Kind: L -/
theorem Cf.ofEvents_apply [Nonempty Ω] (d : ι) (st : acts d → State Ω K)
    (hinj : Function.Injective (ρ d)) (a : acts d) :
    Cf.ofEvents ρ d st (ρ d a) = st a := by
  unfold Cf.ofEvents
  have h : ∃ a', ρ d a' = ρ d a := ⟨a, rfl⟩
  rw [dif_pos h]
  congr 1
  exact hinj (Classical.choose_spec h)

end cf

/-! ### The prior state and the masked form of Definition 11 -/

section prior

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **The prior-calibrated state of `C` on `B`**: `dp-calibration`'s calibrated state at the
trivial observation `⊤` — `P := ν_{B,C}`, `V(X) := 𝔼_μ[r ∣ λ ⊨ X]`.
Source: [[decision-problems-v2]] §3.1 Definition 11 (the state it pins); `verify-prior-notes.md`
F1 ("at a root point with `O = ⊤` … literally Def 11's clause")
Kind: D -/
noncomputable def priorState : State Ω K :=
  calibratedState C B Finset.univ (by rw [nu_univ]; exact one_pos)

/-- `P` of the prior state is `ν`. Source: none: infrastructure. Kind: L -/
theorem priorState_pr (X : Finset Ω) : (priorState C B).pr X = nu C B X := by
  unfold priorState
  rw [calibratedState_pr, Finset.inter_univ, nu_univ, div_one]

/-- `V` of the prior state is `𝔼[r ∣ X]` (Lean's `x / 0 = 0` off the support).
Source: none: infrastructure. Kind: L -/
theorem priorState_V (X : Finset Ω) : (priorState C B).V X = paySum C B X / nu C B X := by
  unfold priorState
  rw [calibratedState_V, Finset.inter_univ]

/-- **The prior state is prior-calibrated (Definition 11, strict form) for every `C`, `B`**: the
hypothesis package of every headline below is inhabited by the real construction.
Source: [[decision-problems-v2]] §3.1 Definition 11
Kind: N+
Fidelity: exact
Hyps: none -/
theorem priorState_priorCalibrated : PriorCalibrated C B (priorState C B) := by
  refine ⟨fun X => priorState_pr C B X, fun X hX => ?_⟩
  rw [priorState_V, div_mul_cancel₀ _ hX.ne']

/-- **Definition 11, masked variant, with self-model `C'`**: `C'` has full support and `s°` is
strictly prior-calibrated for `C'`. The plan's "masked prior calibration under a full-support
self-model" is literally this: the mask is the replacement of the actual procedure by the
full-support `C'` in Definition 11's strict rule (`faithful.md` FA-6′ is why the mask is
mandatory: the strict rule under a deterministic `C` collapses the domain).
Source: `faithful.md` Definition F1 ("Under Definition 11's masked variant with self-model
`C'`"), FA-6′; [[decision-problems-v2]] §3.1 Definition 11
Kind: D
Fidelity: exact -/
def MaskedPriorCalibrated (s₀ : State Ω K) : Prop := C.FullSupport ∧ PriorCalibrated C B s₀

/-- The prior state of a full-support `C'` is masked-prior-calibrated: the hypothesis package is
inhabited (N+ for every full-support self-model).
Source: `faithful.md` Definition F1
Kind: N+ -/
theorem maskedPriorCalibrated_priorState (h : C.FullSupport) :
    MaskedPriorCalibrated C B (priorState C B) :=
  ⟨h, priorState_priorCalibrated C B⟩

/-- The lift of a full-support procedure has full support (the product of positive weights).
Source: none: infrastructure
Kind: L -/
theorem lift_fullSupport (U : Finset ι) {C : Proc ι acts K} (h : C.FullSupport) :
    (lift U C).FullSupport := by
  intro p a
  cases p with
  | inl d => exact h d a
  | inr u =>
      cases u
      simp only [lift_inr, FinDistr.pi_w]
      exact Finset.prod_pos fun d _ => h d (a d)

end prior

/-! ### The disposition coordinate of record: `pol_d = a` on the relocated tree -/

section pol

variable (U : Finset ι)

/-- **The disposition event of record** `ρ_d(a) := {pol_d = a}` on the relocated world type
`RW Ω acts U = Ω × ∏_{d ∈ U} A_d` (D3; `dp-fairness-reloc`'s `nu_pol_eq` event). For `d ∉ U` the
event is `∅` (junk: the point then has prior probability `0` at every action and falls to
Definition 17's uniform fallback); every theorem quantifies over `d ∈ U`.
Source: `firstperson.md` D3 ("`ρ_d(a) := {pol_d = a}` — Remark 4.2's would-pay coordinate; the
canonical `ρ` of Def 17 once the algebra is enriched"); `fair-repair.md` FR-2; mandate decision 3
Kind: D
Fidelity: exact (for `d ∈ U`) -/
def polEv (d : ι) (a : acts d) : Finset (RW Ω acts U) :=
  if h : d ∈ U then Finset.univ.filter fun w => w.2 ⟨d, h⟩ = a else ∅

/-- `polEv` on a relocated point. Source: none: infrastructure. Kind: L -/
theorem polEv_of_mem {d : ι} (h : d ∈ U) (a : acts d) :
    polEv U d a = (Finset.univ : Finset (RW Ω acts U)).filter fun w => w.2 ⟨d, h⟩ = a := by
  simp [polEv, h]

/-- `polEv` off `U` is empty (junk). Source: none: infrastructure. Kind: L -/
theorem polEv_of_not_mem {d : ι} (h : d ∉ U) (a : acts d) :
    polEv (Ω := Ω) (acts := acts) U d a = ∅ := by
  simp [polEv, h]

/-- **`ρ` derived: `ν_{Rel_U B, lift C}(pol_d = a) = C(d)(a)`** — `dp-fairness-reloc`'s `nu_pol_eq`
restated on `polEv`.
Source: `fair-repair.md` FR-2; `dp-fairness-reloc` `nu_pol_eq`
Kind: L -/
theorem nu_polEv {d : ι} (h : d ∈ U) (C : Proc ι acts K) (B : Tree Ω ι acts K) (a : acts d) :
    nu (lift U C) (relocRoot U B) (polEv U d a) = (C d).w a := by
  rw [polEv_of_mem U h]
  exact nu_pol_eq U C B ⟨d, h⟩ a

/-- The disposition events of one relocated point are pairwise distinct (the carrier has a world
with every value of the `pol_d` coordinate).
Source: none: infrastructure
Kind: L -/
theorem polEv_injective [Nonempty Ω] {d : ι} (h : d ∈ U) :
    Function.Injective (polEv (Ω := Ω) (acts := acts) U d) := by
  intro a a' haa'
  by_contra hne
  obtain ⟨ω⟩ := (inferInstance : Nonempty Ω)
  let τ : (e : ↥U) → acts e := Function.update (fun e => Classical.arbitrary (acts e)) ⟨d, h⟩ a
  have hτ : τ ⟨d, h⟩ = a := Function.update_self _ _ _
  have hw : ((ω, τ) : RW Ω acts U) ∈ polEv U d a := by
    rw [polEv_of_mem U h]
    simp [hτ]
  rw [haa', polEv_of_mem U h] at hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hτ] at hw
  exact hne hw

end pol

/-! ### Theorem 2's point game: best replies and Nash -/

section br

variable (C' : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **The best replies at `d` to the self-model `C'`**: `BR_d(C') := argmax_a V_B(C'[d ↦ a])`,
the point game whose payoff at `d` is Theorem 2's evaluator with `C'` in place of `C`. The three
intrinsic referents of Definition F2 (R1 prior/per-run/`O_d`-conditioned, R2 single-instance,
R3 tremble) are `dp-referents-cdt`'s; `BR` is R1 at the prior weighting (the deviation
`C'[d ↦ a]`, unconditioned).
Source: `faithful.md` FA-9 ("`Unif argmax_a V_B(C'[d↦a]) =: BR_d(C')` — Theorem 2's evaluator
with `C'` for `C`"), Definition F2 (R1, prior weighting)
Kind: D
Fidelity: exact -/
def BR (d : ι) : Finset (acts d) := argmaxFull fun a => value (C'.deviatePure d a) B

/-- Membership in `BR`. Source: none: infrastructure. Kind: L -/
theorem mem_BR (d : ι) (a : acts d) :
    a ∈ BR C' B d ↔ ∀ b, value (C'.deviatePure d b) B ≤ value (C'.deviatePure d a) B :=
  mem_argmaxFull _ a

/-- `BR` is nonempty. Source: none: infrastructure. Kind: L -/
theorem BR_nonempty (d : ι) : (BR C' B d).Nonempty := argmaxFull_nonempty _

/-- **Mixed Nash of the point game**: at every queried point every supported action of `C'` is
a best reply to `C'` (the "self-model is a fixed point of componentwise best reply").
Source: `faithful.md` FA-12′ ("`C'` is a mixed Nash equilibrium of the point game")
Kind: D
Fidelity: exact -/
def Nash : Prop := ∀ d ∈ queried B, ∀ a, 0 < (C' d).w a → a ∈ BR C' B d

end br

end Cleanroom.Decision.DpFaithfulUdt
