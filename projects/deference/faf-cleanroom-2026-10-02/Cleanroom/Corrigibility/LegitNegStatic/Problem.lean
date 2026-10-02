import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# The finite legitimacy decision problem of record

Package `legit-neg-static` (faf-cleanroom run, 2026-09-29). Source: the legitimacy-negatives
run of 2026-09-25 (`research/corrigibility/legitimacy-negatives-2026-09-25/`), pinned by
[[corr-legit-neg-inventory]] item 001 and [[corr-legit-neg-2-inventory]] item 2-001, from
`clusters/B/fixtures/model.py:34-67`.

This file is API for `legit-neg-pricing` and `legit-neg-dynamic`: definitions and the
identities they need, no cluster-A theorems. Everything is a `Finset.sum` over a `Fintype`
of starting states with rational weights; no FAF object is involved (the inventory's "FAF fit"
section: nothing in FAF covers the finite decision layer).
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

/-- The rational indicator of a `Bool`: `1` if true, `0` if false.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ind (b : Bool) : ℚ := if b then 1 else 0

/-- `ind_true`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ind_true : ind true = 1 := rfl
/-- `ind_false`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ind_false : ind false = 0 := rfl
/-- `ind_nonneg`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]
/-- `ind_le_one`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_le_one (b : Bool) : ind b ≤ 1 := by cases b <;> simp [ind]
/-- `ind_not`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_not (b : Bool) : ind (!b) = 1 - ind b := by cases b <;> simp [ind]
/-- `ind_mul_self`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_mul_self (b : Bool) : ind b * ind b = ind b := by cases b <;> simp [ind]
/-- `ind_mul_not`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_mul_not (b : Bool) : ind b * ind (!b) = 0 := by cases b <;> simp [ind]
/-- `ind_decide`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ind_decide (p : Prop) [Decidable p] : ind (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [ind, h]

/-- Expected utility of a standard `Q` under an arbitrary weight `μ` (not necessarily the
problem's prior): `∑ s, μ s · Q s a`. The yardstick `W_μ` of VERIFY A V5 is this with the
humans' ex-ante prior `μ`.
Source: [[corr-legit-neg-inventory]] item 004; VERIFY A "A6, narrowing (i)"
Kind: D
Fidelity: exact -/
def EU {S A : Type} [Fintype S] (μ : S → ℚ) (Q : S → A → ℚ) (a : A) : ℚ := ∑ s, μ s * Q s a

/-- The finite legitimacy decision problem of record (cluster B's `Problem`, `model.py:34-46`):
finite starting states `S` with the agent's issuance-time prior, a finite menu `A`, a total
legitimacy bit `leg s a` on every terminal `(s, a)`, and a total standard `u s a` on every
terminal, void ones included and possibly negative (B's `random_problem(…, wlo=-1)` draws
`u ∈ [-1, 1]` on void terminals: the floor `0` is a property of the proposals, not of `u`).
Optional data — void grades `W`, cross-branch assessments `K`, a bounded standard `Q` — are
function arguments of the proposals, never fields, so nothing carries a junk default.
Source: [[corr-legit-neg-inventory]] item 001; [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
structure Problem (S A : Type) [Fintype S] [Fintype A] where
  /-- the agent's day-`n` prior over starting states -/
  prior : S → ℚ
  prior_nonneg : ∀ s, 0 ≤ prior s
  prior_sum : ∑ s, prior s = 1
  /-- legitimacy bit of the terminal `(s, a)` -/
  leg : S → A → Bool
  /-- the standard's value on every terminal (cluster B's `u`; cluster A's `Q` when bounded) -/
  u : S → A → ℚ

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- The prior mass of an event `E : S → Bool`: `∑ s, π s · [E s]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def mass (E : S → Bool) : ℚ := ∑ s, P.prior s * ind (E s)

/-- `P(L | a) = ∑ s, π s · [leg s a]` (`model.py:49-52` without a cell).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def PL (a : A) : ℚ := P.mass (fun s => P.leg s a)

/-- The standard `W Q a = ∑ s, π s · Q s a` (cluster A): the humans' full-view quality on every
terminal, void ones included, weighted by the *agent's* prior. This is expected-utility
maximization with correctly learned values, the `E^A_n(U | a)` benchmark that Abram's
correction (`RUN.md` §2.4 item 3) says gives up the floor; a distortion relative to `W` is not
a failure by Abram's concerns (VERIFY A, cross-cutting caveat; SYNTHESIS). No theorem here may
be named as if it were.
Source: [[corr-legit-neg-inventory]] item 004
Kind: D
Fidelity: exact -/
def W (Q : S → A → ℚ) (a : A) : ℚ := EU P.prior Q a

/-- The standard `H a = ∑ s, π s · u s a` (cluster B, `model.py:54-57` without a cell):
`W` with `Q = u`. Same register as `W`: unconstrained expected utility.
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def H (a : A) : ℚ := P.W P.u a

/-- The renormalised prior on a cell `C` (`model.py:59-64`); zero outside `C`. Meaningful
only when `0 < ∑ s ∈ C, π s`, which every use below carries as a hypothesis (the fixture
`assert`s it): a measure-zero cell is excluded, not given a junk value.
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def cellprior (C : Finset S) [DecidableEq S] (s : S) : ℚ :=
  if s ∈ C then P.prior s / (∑ t ∈ C, P.prior t) else 0

/-- `P(L | a)` within a cell (`model.py:49-52`, T2).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def PLc [DecidableEq S] (a : A) (C : Finset S) : ℚ :=
  ∑ s, P.cellprior C s * ind (P.leg s a)

/-- `H` within a cell (`model.py:54-57`, T2).
Source: [[corr-legit-neg-2-inventory]] item 2-001
Kind: D
Fidelity: exact -/
def Hc [DecidableEq S] (a : A) (C : Finset S) : ℚ :=
  ∑ s, P.cellprior C s * P.u s a

/-- `Sealed P`: legitimacy is independent of the option (readout R3, `RUN.md` §3; the
workspace's common activation event). The predicate of record for cluster A.
Source: [[corr-legit-neg-inventory]] item 003
Kind: D
Fidelity: exact -/
def Sealed : Prop := ∀ s a a', P.leg s a = P.leg s a'

/-- `SealedBy P ℓ`: the legitimacy bit is the state-only event `ℓ`. The working form of
`Sealed` (it names the event `L`, so `π(L)` is `P.mass ℓ`).
Source: [[corr-legit-neg-inventory]] item 003
Kind: D
Fidelity: exact -/
def SealedBy (ℓ : S → Bool) : Prop := ∀ s a, P.leg s a = ℓ s

/-- `Sealed_of_SealedBy`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Sealed_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) : P.Sealed :=
  fun s a a' => by rw [h s a, h s a']

/-- `SealedBy_of_Sealed`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma SealedBy_of_Sealed [Nonempty A] (h : P.Sealed) : ∃ ℓ, P.SealedBy ℓ :=
  ⟨fun s => P.leg s (Classical.arbitrary A), fun s a => h s a _⟩

/-- Under `SealedBy ℓ`, `P(L | a)` is the constant `π(L)`: no option moves legitimacy.
This is the whole content of NEGATIVES A4a ("protection of `C_n` is inexpressible") and of
its dual A4a′ ("no steering toward `¬C_n`"), by the type of the sealed problem.
Source: [[corr-legit-neg-inventory]] item 011 (A4a, A4a′)
Kind: L
Fidelity: exact -/
theorem PL_eq_mass_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) (a : A) :
    P.PL a = P.mass ℓ := by
  unfold PL mass
  exact Finset.sum_congr rfl fun s _ => by simp only [h s a]

/-! ### Mass lemmas -/

/-- `mass_nonneg`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_nonneg (E : S → Bool) : 0 ≤ P.mass E :=
  Finset.sum_nonneg fun s _ => mul_nonneg (P.prior_nonneg s) (ind_nonneg _)

/-- `mass_not`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_not (E : S → Bool) : P.mass (fun s => !E s) = 1 - P.mass E := by
  unfold mass
  simp only [ind_not, mul_sub, mul_one, Finset.sum_sub_distrib, P.prior_sum]

/-- `mass_le_one`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_le_one (E : S → Bool) : P.mass E ≤ 1 := by
  have := P.mass_nonneg (fun s => !E s)
  rw [mass_not] at this; linarith

/-- Zero mass means zero prior on every state of the event (no junk: a `0 · x` term).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prior_eq_zero_of_mass_eq_zero {E : S → Bool} (h : P.mass E = 0) (s : S)
    (hs : E s = true) : P.prior s = 0 := by
  unfold mass at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun t _ => mul_nonneg (P.prior_nonneg t) (ind_nonneg (E t)))).1 h s (Finset.mem_univ s)
  simpa [hs] using h0

/-- `mass_pos_of_prior_pos`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_pos_of_prior_pos {E : S → Bool} (s : S) (hs : E s = true) (hp : 0 < P.prior s) :
    0 < P.mass E := by
  by_contra hle
  have h0 : P.mass E = 0 := le_antisymm (not_lt.1 hle) (P.mass_nonneg E)
  exact absurd (P.prior_eq_zero_of_mass_eq_zero h0 s hs) hp.ne'

/-- The standard splits over an event and its complement.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma W_split (Q : S → A → ℚ) (E : S → Bool) (a : A) :
    P.W Q a = (∑ s, P.prior s * ind (E s) * Q s a) + ∑ s, P.prior s * ind (!E s) * Q s a := by
  unfold W EU
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  cases E s <;> simp [ind]

/-! ### Cells and the restricted problem -/

/-- `cellprior_nonneg`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellprior_nonneg [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) (s : S) :
    0 ≤ P.cellprior C s := by
  unfold cellprior
  split_ifs
  · exact div_nonneg (P.prior_nonneg s) hC.le
  · exact le_rfl

/-- `cellprior_sum`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellprior_sum [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) :
    ∑ s, P.cellprior C s = 1 := by
  unfold cellprior
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div]
  exact div_self hC.ne'

/-- The T2 problem: the same terminals under the prior renormalised to the cell `C`
(`model.py:59-64`); stretch S1 of the mandate. Every T1 theorem over `Problem` is a T2
theorem over `P.restrict C hC`.
Source: [[corr-legit-neg-2-inventory]] item 2-001 (`cellprior`)
Kind: D
Fidelity: exact -/
def restrict [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) : Problem S A where
  prior := P.cellprior C
  prior_nonneg := P.cellprior_nonneg C hC
  prior_sum := P.cellprior_sum C hC
  leg := P.leg
  u := P.u

/-- `restrict_prior`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrict_prior [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) :
    (P.restrict C hC).prior = P.cellprior C := rfl
/-- `restrict_leg`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrict_leg [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) :
    (P.restrict C hC).leg = P.leg := rfl
/-- `restrict_u`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrict_u [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) :
    (P.restrict C hC).u = P.u := rfl

/-- `restrict_PL`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_PL [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) (a : A) :
    (P.restrict C hC).PL a = P.PLc a C := rfl

/-- `restrict_H`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_H [DecidableEq S] (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) (a : A) :
    (P.restrict C hC).H a = P.Hc a C := rfl

/-- The cellprior of a singleton `{s}` with positive mass is the point mass at `s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellprior_singleton [DecidableEq S] (s : S) (hs : 0 < P.prior s) (t : S) :
    P.cellprior {s} t = if t = s then 1 else 0 := by
  unfold cellprior
  simp only [Finset.mem_singleton, Finset.sum_singleton]
  split_ifs with h
  · subst h; exact div_self hs.ne'
  · rfl

end Problem

/-! ### `argmax` over a finite menu -/

section Argmax

variable {A : Type} [Fintype A]

open Classical in
/-- The set of maximisers of `f : A → ℚ` over the whole menu (non-empty when `A` is).
Source: `clusters/A/fixtures/run.py:35-37` (`argmax_set`)
Kind: D
Fidelity: exact -/
noncomputable def argmax (f : A → ℚ) : Finset A := univ.filter fun a => ∀ b, f b ≤ f a

/-- `mem_argmax`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_argmax {f : A → ℚ} {a : A} : a ∈ argmax f ↔ ∀ b, f b ≤ f a := by
  simp [argmax]

open Classical in
/-- Maximisers among the *defined* values of `f : A → Option ℚ`; empty if none is defined
(`model.py:70-76`, `argmax`). This is the **exclusion convention of record** for `P2` and
`P5` at `P(L | a) = 0`: an undefined option is not a candidate.
Source: [[corr-legit-neg-2-inventory]] item 2-003
Kind: D
Fidelity: exact -/
noncomputable def argmaxOpt (f : A → Option ℚ) : Finset A :=
  univ.filter fun a => ∃ x, f a = some x ∧ ∀ b y, f b = some y → y ≤ x

/-- `mem_argmaxOpt`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_argmaxOpt {f : A → Option ℚ} {a : A} :
    a ∈ argmaxOpt f ↔ ∃ x, f a = some x ∧ ∀ b y, f b = some y → y ≤ x := by
  simp [argmaxOpt]

/-- `argmaxOpt` of an everywhere-defined function is `argmax`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmaxOpt_some (f : A → ℚ) : argmaxOpt (fun a => some (f a)) = argmax f := by
  ext a
  simp only [mem_argmaxOpt, mem_argmax, Option.some.injEq]
  constructor
  · rintro ⟨x, rfl, h⟩ b; exact h b (f b) rfl
  · intro h; exact ⟨f a, rfl, fun b y hy => hy ▸ h b⟩

/-- `argmaxOpt` of a nowhere-defined function is empty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmaxOpt_none (f : A → Option ℚ) (h : ∀ a, f a = none) : argmaxOpt f = ∅ := by
  ext a; simp [mem_argmaxOpt, h]

/-- Scaling by a positive constant leaves the argmax unchanged.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_mul_pos (f : A → ℚ) {c : ℚ} (hc : 0 < c) :
    argmax (fun a => f a * c) = argmax f := by
  ext a; simp only [mem_argmax]
  constructor
  · intro h b; exact le_of_mul_le_mul_right (h b) hc
  · intro h b; exact mul_le_mul_of_nonneg_right (h b) hc.le

/-- `argmax_div_pos`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_div_pos (f : A → ℚ) {c : ℚ} (hc : 0 < c) :
    argmax (fun a => f a / c) = argmax f := by
  ext a; simp only [mem_argmax]
  constructor
  · intro h b; exact (div_le_div_iff_of_pos_right hc).1 (h b)
  · intro h b; exact (div_le_div_iff_of_pos_right hc).2 (h b)

/-- Adding a constant leaves the argmax unchanged.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_add_const (f : A → ℚ) (c : ℚ) : argmax (fun a => f a + c) = argmax f := by
  ext a; simp [mem_argmax]

/-- `argmax_congr`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_congr {f g : A → ℚ} (h : ∀ a, f a = g a) : argmax f = argmax g := by
  ext a; simp only [mem_argmax, h]

/-- A constant function has the whole menu as argmax.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_const (c : ℚ) : argmax (fun _ : A => c) = univ := by
  ext a; simp [mem_argmax]

/-- Over a non-empty finite menu the argmax is non-empty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_nonempty [Nonempty A] (f : A → ℚ) : (argmax f).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image univ f univ_nonempty
  exact ⟨a, mem_argmax.2 fun b => ha b (mem_univ b)⟩

end Argmax

end Cleanroom.Corrigibility.LegitNegStatic
