import CartesianFrames.API
import Mathlib.Data.Set.Basic

/-!
# Observability and its relatives over FAF's `Frame`

Package `dp-cartesian-frames`, file 1. Everything here is stated over an arbitrary
`C : CartesianFrames.Frame W`; nothing mentions trees. FAF's `CartesianFrames` carries the
paper (arXiv:2109.10996) only, and the paper has no notion of observability, so the
definitions of the LessWrong sequence's post 11 ("Eight Definitions of Observability") are
defined here (an FAF API request), with the conditional-policies definition as the definition
of record and the others as theorems about it.

* `Observable C v` (post 11 §2, conditional policies), `Observable2 C S` (the two-cell form,
  written with the two values of `f`), `PowerlessOutside`, `ColumnDetermined`, `Ensurable`,
  `Preventable`, `Controllable`; the partition convention is CF-2's: a partition is any
  `v : W → V`, so unreachable cells add no constraint and `W` is **not** restricted to the image.
* The sum `&` (`Frame.sum`, `sumI`) and tensor `⊗` (`Frame.tensor`) of post 11 §3/§4.
* **CF-8**: observable ⟹ column-determined, and Obs ∩ Ctrl = ∅. **CF-9**: powerless outside ⟹
  observable. Post 11 §4.1's two powerlessness lemmas.
* **T8(a)**: every predicate is monotone under `assume` (identification only adds observability).
* **T9(a)**: every predicate is invariant under biextensional equivalence (through FAF's
  `biextEquiv_iff_homotopyEquiv`).
* **T10(b)**: for two cells `Observable2 C S ↔ Observable2 C Sᶜ`; and the *assuming*
  definition — `Observable C v ↔ C ≃ᵇ sumI (fun c => C.assume (colCell C v c))` for
  column-determined `v` on a frame with a nonempty agent (post 11 elides both side
  conditions; its own proof assumes the agent nonempty).
* **T12(a)**: `C.external s ≅ sumI (fun c => C.commit {a | ⟦a⟧ = c})` in `Chu(W)`.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame

universe u v

variable {W : Type u}

/-! ### The predicates (post 11) -/

/-- **Conditional-policies observability** (definition of record): `C`'s agent can observe the
partition `v : W → V` if for every conditional policy `f : V → A` some `a_f ∈ A` realizes it —
`f (v (a_f ⋆ e)) ⋆ e = a_f ⋆ e` for every `e`. A partition is any function on `W`, and `W` is
not restricted to the image (the mandate's §3 convention; CF-2 takes `W = Image` — immaterial
here, since every predicate quantifies over `Env`, so cells with no reachable world add no
constraint). FAF lacks this notion (the paper predates the sequence). On a frame with an
**empty agent** every predicate of this file holds vacuously (there is no conditional policy to
realize); tree headlines stated without `[∀ d, Nonempty (acts d)]` cover that case vacuously, and
every witness tree of the package has inhabited action types (audit r2, N8).
Source: post 11 §2 (`11-eight-definitions-observability-full.md` line 53); cf-correspondence
CF-2 (line 19)
Kind: D
Fidelity: exact (the post's `V` is a finite partition of `W`; here any map `W → V`) -/
def Observable {V : Sort v} (C : CartesianFrames.Frame W) (v : W → V) : Prop :=
  ∀ f : V → C.Agent, ∃ a : C.Agent, ∀ e : C.Env,
    C.outcome (f (v (C.outcome a e))) e = C.outcome a e

/-- **Two-cell observability** `{S, Sᶜ}`, with the conditional policy given by its two values
`a₀` (on `S`) and `a₁` (off `S`): some `a` agrees with `a₀` wherever its outcome lies in `S`
and with `a₁` wherever it does not. Proved equal to `Observable C (fun w => w ∈ S)` in
`observable2_iff_observable`.
Source: post 11 §2 (line 53), two-cell instance; cf-frontier CFF-24 (line 108)
Kind: D
Fidelity: exact -/
def Observable2 (C : CartesianFrames.Frame W) (S : Set W) : Prop :=
  ∀ a₀ a₁ : C.Agent, ∃ a : C.Agent, ∀ e : C.Env,
    (C.outcome a e ∈ S → C.outcome a e = C.outcome a₀ e) ∧
    (C.outcome a e ∉ S → C.outcome a e = C.outcome a₁ e)

/-- **Powerless outside `S`**: whenever some row's outcome at `e` lies outside `S`, every row
has that outcome at `e`.
Source: post 11 §4.1 (line 163)
Kind: D
Fidelity: exact -/
def PowerlessOutside (C : CartesianFrames.Frame W) (S : Set W) : Prop :=
  ∀ (e : C.Env) (a₀ a₁ : C.Agent), C.outcome a₀ e ∉ S → C.outcome a₀ e = C.outcome a₁ e

/-- **Column-determined membership**: whether the outcome at `e` lies in `S` does not depend on
the row. Kept separate from observability (it is CF-8's *conclusion*, not part of the
definition).
Source: cf-correspondence CF-8 (line 37) ("membership is column-determined")
Kind: D
Fidelity: exact -/
def ColumnDetermined (C : CartesianFrames.Frame W) (S : Set W) : Prop :=
  ∀ (e : C.Env) (a₀ a₁ : C.Agent), (C.outcome a₀ e ∈ S ↔ C.outcome a₁ e ∈ S)

/-- **Column-determined cells** for a general partition `v`: the cell of the outcome at `e`
does not depend on the row.
Source: cf-correspondence CF-8 (line 37), cellwise; zoo ZO-12 ("chance-determined")
Kind: D
Fidelity: exact -/
def ColumnDeterminedV {V : Sort v} (C : CartesianFrames.Frame W) (v : W → V) : Prop :=
  ∀ (e : C.Env) (a₀ a₁ : C.Agent), v (C.outcome a₀ e) = v (C.outcome a₁ e)

/-- **Ensurable**: some row lies in `S` at every column.
Source: post 11 §1 (the sequence's `Ensure`); cf-correspondence CF-8 (line 37)
Kind: D
Fidelity: exact -/
def Ensurable (C : CartesianFrames.Frame W) (S : Set W) : Prop :=
  ∃ a : C.Agent, ∀ e : C.Env, C.outcome a e ∈ S

/-- **Preventable**: `Sᶜ` is ensurable.
Source: cf-correspondence CF-8 (line 37)
Kind: D
Fidelity: exact -/
def Preventable (C : CartesianFrames.Frame W) (S : Set W) : Prop := Ensurable C Sᶜ

/-- **Controllable**: ensurable and preventable.
Source: cf-correspondence CF-8 (line 37) ("Ctrl = Ensure ∩ Prevent")
Kind: D
Fidelity: exact -/
def Controllable (C : CartesianFrames.Frame W) (S : Set W) : Prop :=
  Ensurable C S ∧ Preventable C S

/-- The column set of the cell `c`: the environments all of whose outcomes lie in cell `c`
(post 11 §3's `E_i`, the environment of `Assume_{S_i}(C)`).
Source: post 11 §3 (line 123: `C_i = (A, E_i, ·_i)`)
Kind: D
Fidelity: exact -/
def colCell {V : Sort v} (C : CartesianFrames.Frame W) (v : W → V) (c : V) : Set C.Env :=
  {e | ∀ a : C.Agent, v (C.outcome a e) = c}

/-- The two-cell column sets: `E_S := {e | ∀ a, a ⋆ e ∈ S}` (CF-20's `E^∀_S`).
Source: cf-correspondence CF-20 (line 104: `Assume^{E^∀_S}`)
Kind: D
Fidelity: exact -/
def colIn (C : CartesianFrames.Frame W) (S : Set W) : Set C.Env :=
  {e | ∀ a : C.Agent, C.outcome a e ∈ S}

/-! ### The sum and tensor of frames (post 11 §3, §4) -/

/-- The indexed sum `&ᵢ Cᵢ` of frames over `W`: the agent chooses one row per summand, the
environment chooses a summand and a column of it.
Source: post 11 §3 (line 123: `C₁ & ⋯ & Cₙ = (Aⁿ, E₁ ⊔ ⋯ ⊔ Eₙ, ⋆)`)
Kind: D
Fidelity: exact -/
def sumI {ι : Type u} (C : ι → CartesianFrames.Frame W) : CartesianFrames.Frame W where
  Agent := (i : ι) → (C i).Agent
  Env := Σ i : ι, (C i).Env
  outcome a e := (C e.1).outcome (a e.1) e.2

/-- The binary sum `C & D`.
Source: post 11 §3 (line 123)
Kind: D
Fidelity: exact -/
def Frame.sum (C D : CartesianFrames.Frame W) : CartesianFrames.Frame W where
  Agent := C.Agent × D.Agent
  Env := C.Env ⊕ D.Env
  outcome a e := match e with
    | .inl e => C.outcome a.1 e
    | .inr f => D.outcome a.2 f

/-- The tensor `C ⊗ D`: agent `A × B`, environment the Chu morphisms `C ⟶ D*` (FAF's `Hom`
into FAF's `dual`), outcome `a ⋆ h(b)` (`= b ⋆' g(a)` by adjointness).
Source: post 11 §4.1 (line 177: `C ⊗ D = (A × B, hom(C, D*), ⋄)`)
Kind: D
Fidelity: exact -/
def Frame.tensor (C D : CartesianFrames.Frame W) : CartesianFrames.Frame W where
  Agent := C.Agent × D.Agent
  Env := C ⟶ D.dual
  outcome a φ := C.outcome a.1 (φ.env a.2)

/-- In the tensor the two readings of the outcome agree (post 11's `a₀ · h(b₀) = b₀ ⋆ g(a₀)`).
Source: post 11 §4.1 (line 177)
Kind: L -/
theorem tensor_outcome_eq (C D : CartesianFrames.Frame W) (a : (Frame.tensor C D).Agent)
    (φ : (Frame.tensor C D).Env) :
    (Frame.tensor C D).outcome a φ = D.outcome a.2 (φ.agent a.1) :=
  φ.adjoint a.1 a.2

/-! ### CF-8, CF-9 and the two powerlessness lemmas -/

/-- The two-cell form is the conditional-policies definition at the partition `w ↦ (w ∈ S)`
(cells `True`/`False`): the two definitions are the same predicate.
Source: post 11 §2 (line 53) vs. cf-frontier CFF-24 (line 108)
Kind: L
Fidelity: exact
Hyps: none -/
theorem observable2_iff_observable (C : CartesianFrames.Frame W) (S : Set W) :
    Observable2 C S ↔ Observable C (fun w => w ∈ S) := by
  constructor
  · intro h f
    obtain ⟨a, ha⟩ := h (f True) (f False)
    refine ⟨a, fun e => ?_⟩
    show C.outcome (f (C.outcome a e ∈ S)) e = C.outcome a e
    by_cases hm : C.outcome a e ∈ S
    · rw [eq_true hm]; exact ((ha e).1 hm).symm
    · rw [eq_false hm]; exact ((ha e).2 hm).symm
  · intro h a₀ a₁
    classical
    obtain ⟨a, ha⟩ := h (fun p => if p then a₀ else a₁)
    refine ⟨a, fun e => ⟨fun hm => ?_, fun hm => ?_⟩⟩
    · have := ha e; rw [if_pos hm] at this; exact this.symm
    · have := ha e; rw [if_neg hm] at this; exact this.symm

/-- **CF-8, first half: an observable two-cell partition has column-determined membership.**
Were `a₀ ⋆ e ∈ S` and `a₁ ⋆ e ∉ S`, the conditional policy "`a₁` on `S`, `a₀` off `S`" would be
realized by some `a` whose outcome at `e` can lie neither in `S` nor outside it.
Source: cf-correspondence CF-8 (line 37)
Kind: P
Fidelity: exact
Hyps: none -/
theorem Observable2.columnDetermined {C : CartesianFrames.Frame W} {S : Set W}
    (h : Observable2 C S) : ColumnDetermined C S := by
  have key : ∀ (e : C.Env) (a₀ a₁ : C.Agent), C.outcome a₀ e ∈ S → C.outcome a₁ e ∈ S := by
    intro e a₀ a₁ h₀
    by_contra h₁
    obtain ⟨a, ha⟩ := h a₁ a₀
    by_cases hm : C.outcome a e ∈ S
    · exact h₁ (((ha e).1 hm) ▸ hm)
    · exact hm (((ha e).2 hm) ▸ h₀)
  exact fun e a₀ a₁ => ⟨key e a₀ a₁, key e a₁ a₀⟩

/-- A column-determined partition with both cells realized is neither ensurable nor
preventable: the second cell's realizing column has every row outside `S`, the first's every
row inside.
Source: cf-correspondence CF-8 (line 37) ("no agent-controlled event is observable")
Kind: P
Fidelity: exact
Hyps: none -/
theorem ColumnDetermined.not_ensurable_not_preventable {C : CartesianFrames.Frame W} {S : Set W}
    (h : ColumnDetermined C S) (hin : ∃ e a, C.outcome a e ∈ S)
    (hout : ∃ e a, C.outcome a e ∉ S) : ¬ Ensurable C S ∧ ¬ Preventable C S := by
  obtain ⟨e₁, a₁, h₁⟩ := hin
  obtain ⟨e₀, a₀, h₀⟩ := hout
  refine ⟨fun ⟨a, ha⟩ => h₀ ((h e₀ a a₀).mp (ha e₀)), fun ⟨a, ha⟩ => ?_⟩
  exact (ha e₁) ((h e₁ a₁ a).mp h₁)

/-- **CF-8, second half (Obs ∩ Ctrl = ∅)**: an observable two-cell partition with both cells
realized is neither ensurable nor preventable.
Source: cf-correspondence CF-8 (line 37)
Kind: C
Fidelity: exact
Hyps: none -/
theorem Observable2.not_ensurable_not_preventable {C : CartesianFrames.Frame W} {S : Set W}
    (h : Observable2 C S) (hin : ∃ e a, C.outcome a e ∈ S) (hout : ∃ e a, C.outcome a e ∉ S) :
    ¬ Ensurable C S ∧ ¬ Preventable C S :=
  h.columnDetermined.not_ensurable_not_preventable hin hout

/-- Powerless outside `S` ⟹ column-determined membership.
Source: cf-correspondence CF-9 (line 41) (first step of the proof)
Kind: P
Fidelity: exact
Hyps: none -/
theorem PowerlessOutside.columnDetermined {C : CartesianFrames.Frame W} {S : Set W}
    (h : PowerlessOutside C S) : ColumnDetermined C S := by
  intro e a₀ a₁
  constructor
  · intro h₀; by_contra h₁; exact h₁ (by rw [h e a₁ a₀ h₁]; exact h₀)
  · intro h₁; by_contra h₀; exact h₀ (by rw [h e a₀ a₁ h₀]; exact h₁)

/-- **CF-9: powerless outside `S` ⟹ `{S, Sᶜ}` observable.** The policy `a₀` (the `S`-value)
realizes every conditional policy: on `S`-columns trivially, off `S` by powerlessness.
Source: cf-correspondence CF-9 (line 41); post 11 §4
Kind: P
Fidelity: exact
Hyps: none -/
theorem PowerlessOutside.observable2 {C : CartesianFrames.Frame W} {S : Set W}
    (h : PowerlessOutside C S) : Observable2 C S :=
  fun a₀ a₁ => ⟨a₀, fun e => ⟨fun _ => rfl, fun hm => h e a₀ a₁ hm⟩⟩

/-- Powerlessness is monotone in the subset (post 11 §4.1, first lemma).
Source: post 11 §4.1 (line 167)
Kind: P
Fidelity: exact
Hyps: none -/
theorem PowerlessOutside.mono {C : CartesianFrames.Frame W} {S T : Set W}
    (h : PowerlessOutside C S) (hST : S ⊆ T) : PowerlessOutside C T :=
  fun e a₀ a₁ hT => h e a₀ a₁ (fun hS => hT (hST hS))

/-- Powerlessness outside `S` passes to the tensor (post 11 §4.1, second lemma): with
`(g, h) : C ⟶ D*`, `a₀ ⋆ h(b₀) = a₁ ⋆ h(b₀) = b₀ ⋆' g(a₁) = b₁ ⋆' g(a₁)`.
Source: post 11 §4.1 (line 171)
Kind: P
Fidelity: exact
Hyps: none -/
theorem PowerlessOutside.tensor {C D : CartesianFrames.Frame W} {S : Set W}
    (hC : PowerlessOutside C S) (hD : PowerlessOutside D S) :
    PowerlessOutside (Frame.tensor C D) S := by
  rintro φ ⟨a₀, b₀⟩ ⟨a₁, b₁⟩ hout
  change C.outcome a₀ (φ.env b₀) ∉ S at hout
  change C.outcome a₀ (φ.env b₀) = C.outcome a₁ (φ.env b₁)
  have h1 : C.outcome a₀ (φ.env b₀) = C.outcome a₁ (φ.env b₀) := hC _ a₀ a₁ hout
  have h2 : C.outcome a₁ (φ.env b₀) = D.outcome b₀ (φ.agent a₁) := φ.adjoint a₁ b₀
  have h3 : D.outcome b₀ (φ.agent a₁) = D.outcome b₁ (φ.agent a₁) :=
    hD _ b₀ b₁ (by rw [← h2, ← h1]; exact hout)
  have h4 : D.outcome b₁ (φ.agent a₁) = C.outcome a₁ (φ.env b₁) := (φ.adjoint a₁ b₁).symm
  rw [h1, h2, h3, h4]

/-- Two-cell observability is symmetric in the cells.
Source: post 11 §2 ("definition from subsets": `S` observable iff `Sᶜ` observable)
Kind: L
Fidelity: exact
Hyps: none -/
theorem observable2_compl_iff (C : CartesianFrames.Frame W) (S : Set W) :
    Observable2 C Sᶜ ↔ Observable2 C S := by
  constructor <;>
  · intro h a₀ a₁
    obtain ⟨a, ha⟩ := h a₁ a₀
    refine ⟨a, fun e => ⟨fun hm => (ha e).2 ?_, fun hm => (ha e).1 ?_⟩⟩ <;>
      simpa using hm

/-! ### T8(a): monotonicity under `assume` -/

/-- Observability is monotone under `assume`: a conditional policy realized on every column is
realized on the columns of `F`.
Source: cf-frontier CFF-1 (line 60) ("∀e-statements, hence monotone lazy → identified")
Kind: P
Fidelity: exact
Hyps: none -/
theorem Observable.assume {V : Sort v} {C : CartesianFrames.Frame W} {v : W → V}
    (h : Observable C v) (F : Set C.Env) : Observable (C.assume F) v := by
  intro f
  obtain ⟨a, ha⟩ := h f
  exact ⟨a, fun e => ha e.val⟩

/-- Two-cell observability is monotone under `assume`.
Source: cf-frontier CFF-1 (line 60)
Kind: P
Fidelity: exact
Hyps: none -/
theorem Observable2.assume {C : CartesianFrames.Frame W} {S : Set W}
    (h : Observable2 C S) (F : Set C.Env) : Observable2 (C.assume F) S := by
  intro a₀ a₁
  obtain ⟨a, ha⟩ := h a₀ a₁
  exact ⟨a, fun e => ha e.val⟩

/-- Column-determinedness is monotone under `assume`.
Source: cf-frontier CFF-1 (line 60)
Kind: P
Fidelity: exact
Hyps: none -/
theorem ColumnDetermined.assume {C : CartesianFrames.Frame W} {S : Set W}
    (h : ColumnDetermined C S) (F : Set C.Env) : ColumnDetermined (C.assume F) S :=
  fun e a₀ a₁ => h e.val a₀ a₁

/-- Powerlessness outside `S` is monotone under `assume`.
Source: cf-frontier CFF-1 (line 60)
Kind: P
Fidelity: exact
Hyps: none -/
theorem PowerlessOutside.assume {C : CartesianFrames.Frame W} {S : Set W}
    (h : PowerlessOutside C S) (F : Set C.Env) : PowerlessOutside (C.assume F) S :=
  fun e a₀ a₁ hm => h e.val a₀ a₁ hm

/-! ### T9(a): biextensional invariance -/

/-- In a homotopy equivalence `(φ, ψ)` every outcome of `D` is an outcome of `C`:
`D.outcome b y = C.outcome (ψ.agent b) (φ.env y)`. (From `Homotopic (ψ ≫ φ) (𝟙 D)` and `φ`'s
adjointness.)
Source: none: infrastructure (FAF Definitions 36–37)
Kind: L -/
theorem outcome_eq_of_homotopyEquiv {C D : CartesianFrames.Frame W} (φ : C ⟶ D) (ψ : D ⟶ C)
    (hψφ : Frame.Homotopic (ψ ≫ φ) (𝟙 D)) (b : D.Agent) (y : D.Env) :
    D.outcome b y = C.outcome (ψ.agent b) (φ.env y) := by
  have h := hψφ b y
  simp only [Frame.id_env, Frame.comp_agent, Function.comp, id] at h
  rw [h]
  exact (φ.adjoint (ψ.agent b) y).symm

/-- One direction of the transport of observability along a homotopy equivalence: the
conditional policy `f` for `D` is realized by `φ.agent a_{ψ ∘ f}`.
Source: cf-correspondence CF-21 (line 113) ("observability is biextensional-invariant")
Kind: P
Fidelity: exact
Hyps: none -/
theorem Observable.of_homotopyEquiv {V : Sort v} {C D : CartesianFrames.Frame W}
    (φ : C ⟶ D) (ψ : D ⟶ C) (hψφ : Frame.Homotopic (ψ ≫ φ) (𝟙 D)) {v : W → V}
    (h : Observable C v) : Observable D v := by
  intro g
  obtain ⟨a, ha⟩ := h (fun c => ψ.agent (g c))
  refine ⟨φ.agent a, fun y => ?_⟩
  have hb : D.outcome (φ.agent a) y = C.outcome a (φ.env y) := (φ.adjoint a y).symm
  rw [hb, outcome_eq_of_homotopyEquiv φ ψ hψφ]
  exact ha (φ.env y)

/-- **Observability is invariant under biextensional equivalence** (the lemma CF-21 rests on):
through FAF's `biextEquiv_iff_homotopyEquiv`, a homotopy equivalence transports conditional
policies both ways.
Source: cf-correspondence CF-21 (line 113); mandate T9(a)
Kind: P
Fidelity: exact
Hyps: none -/
theorem observable_iff_of_biextEquiv {V : Sort v} {C D : CartesianFrames.Frame W}
    (h : C ≃ᵇ D) (v : W → V) : Observable C v ↔ Observable D v := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp h
  exact ⟨Observable.of_homotopyEquiv φ ψ hψφ, Observable.of_homotopyEquiv ψ φ hφψ⟩

/-- Two-cell observability is invariant under biextensional equivalence.
Source: cf-correspondence CF-21 (line 113)
Kind: C
Fidelity: exact
Hyps: none -/
theorem observable2_iff_of_biextEquiv {C D : CartesianFrames.Frame W} (h : C ≃ᵇ D)
    (S : Set W) : Observable2 C S ↔ Observable2 D S := by
  rw [observable2_iff_observable, observable2_iff_observable]
  exact observable_iff_of_biextEquiv h _

/-- Column-determinedness is invariant under biextensional equivalence.
Source: mandate T9(a)
Kind: P
Fidelity: exact
Hyps: none -/
theorem columnDetermined_iff_of_biextEquiv {C D : CartesianFrames.Frame W} (h : C ≃ᵇ D)
    (S : Set W) : ColumnDetermined C S ↔ ColumnDetermined D S := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp h
  constructor
  · intro hC y b₀ b₁
    rw [outcome_eq_of_homotopyEquiv φ ψ hψφ b₀, outcome_eq_of_homotopyEquiv φ ψ hψφ b₁]
    exact hC _ _ _
  · intro hD e a₀ a₁
    rw [outcome_eq_of_homotopyEquiv ψ φ hφψ a₀, outcome_eq_of_homotopyEquiv ψ φ hφψ a₁]
    exact hD _ _ _

/-- Powerlessness outside `S` is invariant under biextensional equivalence.
Source: mandate T9(a)
Kind: P
Fidelity: exact
Hyps: none -/
theorem powerlessOutside_iff_of_biextEquiv {C D : CartesianFrames.Frame W} (h : C ≃ᵇ D)
    (S : Set W) : PowerlessOutside C S ↔ PowerlessOutside D S := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp h
  constructor
  · intro hC y b₀ b₁
    rw [outcome_eq_of_homotopyEquiv φ ψ hψφ b₀, outcome_eq_of_homotopyEquiv φ ψ hψφ b₁]
    exact hC _ _ _
  · intro hD e a₀ a₁
    rw [outcome_eq_of_homotopyEquiv ψ φ hφψ a₀, outcome_eq_of_homotopyEquiv ψ φ hφψ a₁]
    exact hD _ _ _

/-- Ensurability is invariant under biextensional equivalence.
Source: mandate T9(a)
Kind: P
Fidelity: exact
Hyps: none -/
theorem ensurable_iff_of_biextEquiv {C D : CartesianFrames.Frame W} (h : C ≃ᵇ D)
    (S : Set W) : Ensurable C S ↔ Ensurable D S := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := Frame.biextEquiv_iff_homotopyEquiv.mp h
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨φ.agent a, fun y => (φ.adjoint a y) ▸ ha (φ.env y)⟩
  · rintro ⟨b, hb⟩
    exact ⟨ψ.agent b, fun e => (ψ.adjoint b e) ▸ hb (ψ.env e)⟩

/-! ### T10(b): the assuming definition -/

/-- The indexed sum of the assumed cells observes the partition: the cell-indexed tuple
`c ↦ f c c` realizes every conditional policy `f`, since a column of the `c`-summand has all
its outcomes in cell `c`.
Source: post 11 §3 (line 123, the assuming definition ⟹ conditional policies)
Kind: P
Fidelity: exact
Hyps: none -/
theorem observable_sumI_assume_colCell {V : Type u} (C : CartesianFrames.Frame W) (v : W → V) :
    Observable (sumI fun c => C.assume (colCell C v c)) v := by
  intro f
  refine ⟨fun c => f c c, ?_⟩
  rintro ⟨c, e, he⟩
  change C.outcome (f (v (C.outcome (f c c) e)) c) e = C.outcome (f c c) e
  rw [he (f c c)]

/-- **Conditional policies ⟹ assuming** (post 11 §3, the substantive direction): if `C`'s
agent, nonempty, observes the column-determined partition `v`, then `C` is biextensionally
equivalent to the sum over cells of `Assume` on that cell's columns. The homotopy equivalence
is `a ↦ (c ↦ a)` forward and `x ↦ a_x` (the realizing policy of `x` read as a conditional
policy) backward.
Source: post 11 §3 (line 123)
Kind: P
Fidelity: exact (the post elides the nonempty-agent and column-determinedness side
conditions; its proof assumes `A` nonempty)
Hyps: none -/
theorem Observable.biextEquiv_sumI_assume {V : Type u} {C : CartesianFrames.Frame W}
    {v : W → V} (hcd : ColumnDeterminedV C v) (hA : Nonempty C.Agent)
    (h : Observable C v) : C ≃ᵇ sumI fun c => C.assume (colCell C v c) := by
  classical
  obtain ⟨a₀⟩ := hA
  have hcell : ∀ e : C.Env, e ∈ colCell C v (v (C.outcome a₀ e)) := fun e a => hcd e a a₀
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact
      { agent := fun a _ => a
        env := fun y => y.2.val
        adjoint := fun a y => rfl }
  · exact
      { agent := fun x => Classical.choose (h x)
        env := fun e => ⟨v (C.outcome a₀ e), ⟨e, hcell e⟩⟩
        adjoint := fun x e => by
          change C.outcome (x (v (C.outcome a₀ e))) e = C.outcome (Classical.choose (h x)) e
          have hx := Classical.choose_spec (h x) e
          rw [← hx, hcd e a₀ (Classical.choose (h x))] }
  · intro a e
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    exact Classical.choose_spec (h fun _ => a) e
  · rintro x ⟨c, e, he⟩
    simp only [Frame.id_env, Frame.comp_agent, Function.comp, id]
    change C.outcome (x c) e = C.outcome (Classical.choose (h x)) e
    have hx := Classical.choose_spec (h x) e
    rw [← hx, he]

/-- **The assuming definition of observability** (post 11 §3, both directions): for a
column-determined partition on a frame with a nonempty agent, `C` observes `v` iff
`C ≃ᵇ &_c Assume_{E_c}(C)`. (⟸) is `observable_sumI_assume_colCell` transported along the
equivalence; (⟹) is `Observable.biextEquiv_sumI_assume`.
Source: post 11 §3 (line 123); mandate T10(b)
Kind: P
Fidelity: exact (side conditions made explicit; post 11 elides them)
Hyps: none -/
theorem observable_iff_biextEquiv_sumI_assume {V : Type u} {C : CartesianFrames.Frame W}
    {v : W → V} (hcd : ColumnDeterminedV C v) (hA : Nonempty C.Agent) :
    Observable C v ↔ (C ≃ᵇ sumI fun c => C.assume (colCell C v c)) :=
  ⟨Observable.biextEquiv_sumI_assume hcd hA,
    fun h => (observable_iff_of_biextEquiv h v).mpr (observable_sumI_assume_colCell C v)⟩

/-! ### T12(a): `External` is the sum of the committed frames -/

/-- **`External_s(C) ≅ &_c Commit^{[a] = c}(C)`** in `Chu(W)`, for any frame and any
partition `s` of its agent: a section of the partition is exactly a tuple of representatives,
and `Quotient s × Env ≃ Σ c, Env`. FAF's Definition 32 unpacked; CFF-19(i) is the instance
`s` = "same stage-1 profile".
Source: cf-frontier CFF-19(i) (line 94); mandate T12(a)
Kind: P
Fidelity: exact
Hyps: none -/
def externalIsoSumICommit (C : CartesianFrames.Frame W) (s : Setoid C.Agent) :
    C.external s ≅ sumI fun c : Quotient s => C.commit {a | Quotient.mk s a = c} where
  hom :=
    { agent := fun q c => ⟨q.val c, q.property c⟩
      env := fun y => (y.1, y.2)
      adjoint := fun _ _ => rfl }
  inv :=
    { agent := fun x => ⟨fun c => (x c).val, fun c => (x c).property⟩
      env := fun p => ⟨p.1, p.2⟩
      adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

end Cleanroom.Decision.DpCartesianFrames
