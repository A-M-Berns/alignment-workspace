import Cleanroom.Udt.UdtPolicyCalc.Simplification

/-!
# `Cleanroom.Udt.UdtCtExamples.Bridge`: the bridge `argmax_a E[U ∣ Π*(o) = a] = argmax_a U'(π[o ↦ a])`
(T5(c))

Work package `udt-ct-examples`, target T5(c) (udt-rep-090; the comment in the corpus's
`UDTConnection.lean` identifying the C&T rule with the policy-utility rule). Objects from
`udt-policy-calc`'s `Simplification.lean`: `rhs μ V s a = E_μ[V ∣ π s = a]` (junk `−1`) under a
prior `μ` over policies, `lhs V π s a = V (π[s ↦ a])`, and the point-mass results `rhs_delta_eq`
(`rhs (δ π₀) V s (π₀ s) = V π₀`) and `rhs_delta_junk` (`rhs (δ π₀) V s a = −1` for `a ≠ π₀ s`).

* (i) For a full-support prior, `rhs μ V s a = V (π₀[s ↦ a])` for every `π₀` and `a` **iff** `V`
  depends on the policy only through its value at `s` (`LocalAt V s`). Both directions.
* (ii) The point-mass case is `rhs_delta_eq`/`rhs_delta_junk`: cited, not restated.
* (iii) So the identification is a modelling substitution `(c)` except under `LocalAt`, which
  no coordination problem meets: Coordinated Buttons' policy value over `Policy (Fin 2) (Fin 2)`
  (`Vcb`) is not local at either room.
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Simplification Finset

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- **`V` is local at `s`**: it depends on a policy only through the policy's value at `s`.
Source: mandate T5(c)(i)
Kind: D
Fidelity: n/a (the condition the bridge needs)
Hyps: n/a -/
def LocalAt (V : Policy S A → ℝ) (s : S) : Prop := ∀ π π', π s = π' s → V π = V π'

/-- **(i) ⟸: under a full-support prior and locality at `s`, the C&T conditional expectation is
the policy value of the updated policy**, for every base policy: `rhs μ V s a = V (π₀[s ↦ a])`.
Source: udt-rep-090 (`UDTConnection.lean`'s bridge); mandate T5(c)(i)
Kind: P
Fidelity: exact
Hyps: (a) full support and `LocalAt` explicit -/
theorem rhs_eq_update_of_localAt (μ : FinDist (Policy S A)) (hμ : ∀ π, 0 < μ.w π)
    (V : Policy S A → ℝ) (s : S) (h : LocalAt V s) (π₀ : Policy S A) (a : A) :
    rhs μ V s a = V (Function.update π₀ s a) := by
  unfold rhs
  have hmem : Function.update π₀ s a ∈ (event fun π : Policy S A => π s = a) := by
    rw [mem_event]; simp
  have hpos : 0 < mass μ.w (event fun π : Policy S A => π s = a) :=
    mass_pos_of_mem (fun π => (hμ π).le) hmem (hμ _)
  refine condExpJunk_const_on (fun π hπ => ?_) hpos
  rw [mem_event] at hπ
  exact h π _ (by rw [hπ]; simp)

/-- **(i) ⟹: if the bridge identity holds for every base policy, `V` is local at `s`**:
specialize `π₀ := π` with `a := π s`, and `π₀ := π'` with `a := π' s = π s`.
Source: mandate T5(c)(i)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem localAt_of_rhs_eq_update (μ : FinDist (Policy S A)) (V : Policy S A → ℝ) (s : S)
    (h : ∀ π₀ a, rhs μ V s a = V (Function.update π₀ s a)) : LocalAt V s := by
  intro π π' hs
  have h1 := h π (π s)
  have h2 := h π' (π' s)
  rw [Function.update_eq_self] at h1 h2
  rw [← h1, ← h2, hs]

/-- **(i) The bridge holds for every base policy iff `V` is local at `s`** (full-support prior).
This is the *value* identity `rhs μ V s a = V (π₀[s ↦ a])` for every base policy `π₀`; the
corpus's `UDTConnection.lean` comment is the *argmax* identity for the current policy `π`. The
argmax form fails on coordination problems for a one-line reason not in Lean (audit r1 N3): the
left side does not depend on `π`, the right side's argmax does, so it cannot hold for two
policies whose off-`s` values differ — the "(c) for every coordination problem" conclusion
(`not_localAt_Vcb`, F-14) stands for both forms.
Source: udt-rep-090; mandate T5(c)(i)
Kind: P
Fidelity: exact (value form); the argmax form is argued in prose
Hyps: (a) full support explicit -/
theorem bridge_iff_localAt (μ : FinDist (Policy S A)) (hμ : ∀ π, 0 < μ.w π) (V : Policy S A → ℝ)
    (s : S) : (∀ π₀ a, rhs μ V s a = V (Function.update π₀ s a)) ↔ LocalAt V s :=
  ⟨localAt_of_rhs_eq_update μ V s, fun h π₀ a => rhs_eq_update_of_localAt μ hμ V s h π₀ a⟩

/-- Coordinated Buttons' policy value over room policies `Fin 2 → Fin 2`: `1/2` if both press
`$5`, `1` if both `$10`, `0` otherwise.
Source: [[communication-trust-translated]] line 149; mandate T5(c)(iii)
Kind: D
Fidelity: exact (scaled)
Hyps: n/a -/
noncomputable def Vcb : Policy (Fin 2) (Fin 2) → ℝ := fun π =>
  if π 0 = π 1 then (if π 0 = 1 then 1 else 1 / 2) else 0

/-- **(iii) Coordinated Buttons' value is not local at either room**: the bridge is a
modelling substitution `(c)` for every coordination problem (the constant-`$5` and the
`$5`-then-`$10` policies agree at the red room and have values `1/2` and `0`).
Source: mandate T5(c)(iii)
Kind: N−
Fidelity: n/a (one-line witness)
Hyps: none -/
theorem not_localAt_Vcb : ¬ LocalAt Vcb 0 ∧ ¬ LocalAt Vcb 1 := by
  constructor
  · intro h
    have := h (fun _ => 0) (fun i => i) rfl
    norm_num [Vcb] at this
  · intro h
    have := h (fun _ => 1) (fun i => i) rfl
    norm_num [Vcb] at this

end Cleanroom.Udt.UdtCtExamples
