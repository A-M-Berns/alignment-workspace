import Cleanroom.Bli.BliTrajectory.Defs

/-!
# `bli-trajectory` · JournalResponse: response-conditioning vs Eisenstat's BLI (M8, T7)

(Named after notes in the author's 2023 journal; it is not Scott Garrabrant's or Benja Fallenstein's proposal — theirs were specific and technical, and the author's notes do not record them accurately.)

Abram's email ([[bli-journal-2023-09-11-soto-emails-and-pdf-notes]] ll. 852–870, paraphrased):
if the market's beliefs about a large sentence are a *reflection* of what the later traders will
decide, then whenever the response settles `φ` on every observed state, no uncertainty about `φ`
survives at `n` — "my current 'small' expectations about those beliefs cannot possibly be
marginals of that 'large' distribution over beliefs". Formally: a `Reflection` identity
`𝐏_n(φ) = ∑_q 𝐏_n(σ_q) · resp q φ` with a response `resp` **constant in `q`** forces
`𝐏_n(φ)` (`journalResponse_forced`); with Eisenstat's response `resp q := Q̂_q[φ]` (the state's own
table) the same identity leaves `𝐏_n(φ) = ½` over two certain-but-opposite states
(`eisenstat_form_consistent`): a *state* can be wrong about `φ`, and the market's uncertainty
about the state is genuine uncertainty about `φ`. **The content is the contrast.** The forcing
lemmas are the *tautological* half of the email's argument (one `Finset.sum_congr`; graded `L`
after audit r1); the email's contradiction — a market that does not yet know the digits cannot
already equal them — is not formalized here.

"Traders can compute the digits" is the hypothesis `∀ q, resp q φ = truth φ`, graded **(c)** on
the *interpretation* that this is what the market response does; the theorem is (a).
**ATTRIBUTION-UNVETTED** that this is the argument the email intended.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

open Classical

/-- **Reflection** of `𝐏_n(φ)` through a response map over the day-`m` states:
`𝐏_n(φ) = ∑_{q ∈ states m} 𝐏_n(⌜𝐐_m = q⌝) · resp q φ`. The journal response argument: `resp` is the traders'
response to the observed table; Eisenstat: `resp q := S.val m q`.
Source: [[bli-journal-2023-09-11-soto-emails-and-pdf-notes]] ll. 852–870; mandate M8
Kind: D
Fidelity: variant: the response is an abstract map (disclosed) -/
def Reflection (resp : ℕ → Sentence → ℝ) (S : StateSystem) (P : History) (n m : ℕ)
    (φ : Sentence) : Prop :=
  P n φ = ∑ q ∈ S.states m, P n (stateAtom m q) * resp q φ

/-- **`journalResponse_forced`**: if the day-`m` masses sum to one and the response settles `φ` at the
same value `t` on every state, reflection forces `𝐏_n(φ) = t` — no uncertainty about anything
the later traders decide survives at `n`. **This is the tautological half of the email's
argument** (substitute the constant response into the reflection identity and use mass one:
one `Finset.sum_congr`); the other half — that a market which "should not yet know those
digits" cannot have its small expectations equal what the traders will later compute — is not
formalized. Graded `L` (audit r1 adversarial B1); the content of M8 is the contrast with
`eisenstat_form_consistent`.
Source: [[bli-journal-2023-09-11-soto-emails-and-pdf-notes]] ll. 866–869; mandate M8
Kind: L
Fidelity: weaker: the tautological half only (abstract response)
Hyps: (a) reflection, mass one, settled response (all explicit) -/
theorem journalResponse_forced {resp : ℕ → Sentence → ℝ} {S : StateSystem} {P : History} {n m : ℕ}
    {φ : Sentence} {t : ℝ} (hrefl : Reflection resp S P n m φ)
    (hsum : ∑ q ∈ S.states m, P n (stateAtom m q) = 1)
    (hresp : ∀ q ∈ S.states m, resp q φ = t) : P n φ = t := by
  rw [hrefl, Finset.sum_congr rfl (fun q hq => by rw [hresp q hq]), ← Finset.sum_mul, hsum, one_mul]

/-- "The traders compute the truth": the response is the truth value, whatever the state.
Source: mandate M8 ("traders can compute the digits")
Kind: D
Fidelity: variant: (c) on the interpretation that this is what the market response does -/
def TruthResponse (truth : Sentence → ℝ) (resp : ℕ → Sentence → ℝ) : Prop :=
  ∀ q φ, resp q φ = truth φ

/-- **Response-conditioning on the truth collapses the market to the truth**: under a truth
response, reflection with mass one gives `𝐏_n(φ) = truth φ`. The same tautological half as
`journalResponse_forced` with `t := truth φ` (graded `L`, audit r1 adversarial B1); the
incompatibility with an inductor that does not yet know the digits is not formalized.
Source: [[bli-journal-2023-09-11-soto-emails-and-pdf-notes]] ll. 866–869; mandate M8
Kind: L
Fidelity: weaker: the tautological half only
Hyps: (c) `TruthResponse` (the interpretation); (a) the rest -/
theorem journalResponse_truth {truth : Sentence → ℝ} {resp : ℕ → Sentence → ℝ} {S : StateSystem}
    {P : History} {n m : ℕ} {φ : Sentence} (htruth : TruthResponse truth resp)
    (hrefl : Reflection resp S P n m φ) (hsum : ∑ q ∈ S.states m, P n (stateAtom m q) = 1) :
    P n φ = truth φ :=
  journalResponse_forced hrefl hsum (fun q _ => htruth q φ)

/-- The two-state system of the contrast: on every day, states `{0, 1}`; state `0` prices `φ₀`
at `1`, state `1` at `0`, everything else at `½`.
Source: mandate M8 (`eisenstat_form_consistent`)
Kind: D
Fidelity: n/a -/
noncomputable def sbSystem (φ₀ : Sentence) : StateSystem where
  states _ := {0, 1}
  val _ q φ := if φ = φ₀ then (if q = 0 then 1 else 0) else 1 / 2
  actual _ := 0
  actual_mem _ := by simp

/-- **`eisenstat_form_consistent`**: on `sbSystem φ₀`, the constant-`½` market reflects `φ₀`
through Eisenstat's response (each state's own table): `½ = ½ · 1 + ½ · 0`. Two states, each
certain about `φ₀` and opposite, both with positive mass; the market's `½` is genuine
uncertainty about which state obtains. The journal response argument (constant in `q`) cannot
produce this (`journalResponse_forced`): with the same masses it forces `𝐏_n(φ₀)` to the response.
Source: [[bli-journal-2023-09-11-soto-emails-and-pdf-notes]] ll. 852–870; mandate M8
Kind: N+
Fidelity: n/a (two distinct certain states, both charged)
Hyps: (a) -/
theorem eisenstat_form_consistent (φ₀ : Sentence) (n m : ℕ) :
    Reflection (fun q => (sbSystem φ₀).val m q) (sbSystem φ₀) (fun _ _ => (1 / 2 : ℝ)) n m φ₀ ∧
      (sbSystem φ₀).val m 0 φ₀ = 1 ∧ (sbSystem φ₀).val m 1 φ₀ = 0 ∧
      (∑ q ∈ (sbSystem φ₀).states m, (fun _ _ => (1 / 2 : ℝ)) n (stateAtom m q)) = 1 := by
  refine ⟨?_, by simp [sbSystem], by simp [sbSystem], by simp [sbSystem]⟩
  unfold Reflection
  simp [sbSystem]

/-- **The Eisenstat response does not settle `φ₀`** on `sbSystem φ₀`: no single value `t` is the
response on both states — so `journalResponse_forced` does not apply, and `½` survives.
Source: mandate M8 (the contrast)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem eisenstat_response_unsettled (φ₀ : Sentence) (m : ℕ) :
    ¬ ∃ t : ℝ, ∀ q ∈ (sbSystem φ₀).states m, (sbSystem φ₀).val m q φ₀ = t := by
  rintro ⟨t, ht⟩
  have h0 := ht 0 (by simp [sbSystem])
  have h1 := ht 1 (by simp [sbSystem])
  simp [sbSystem] at h0 h1
  linarith

end Cleanroom.Bli.BliTrajectory
