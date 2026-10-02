import Cleanroom.Bli.BliWitnessLia.Verdict

/-!
# `bli-witness-lia` · Checks: the risk-9 and degeneracy checks on the witness (T5)

[[bli-program]] §7 item 9 asks every decision-theoretic witness to show *why* the two rules
separate and that the verdict is not built into the shape. On `segmentSist`:

- **(a) `NoCrossBranch` fails** (`not_noCrossBranch`, `V ≠ 0`): the Rec branch's value of the Ask
  point moves by `V` with the action (`condEU_rec_sistSkel`), so `udt-bli-core`'s U3 lemma (which
  makes one-step and updateful choices agree under `Reflective ∧ NoCrossBranch`) does not apply —
  and the rules do separate (`isOneStepChoice_pay` versus `isUpdatefulChoice_refuse`).
- **(b) `Reflective` holds** (`reflective`): the prior is an `IndepData.toPrior` (the policy law
  is drawn independently of the state), so no policy point moves any branch probability
  (`IndepData.reflective_toPrior`). Hence U3's lemma fails **only** through `NoCrossBranch`.
- **(c) The auditor's contrast** (`instance_refuse`, `V < c`): same prior, same hypotheses, stakes
  reversed — one-step UDT refuses. The verdict is `(V − c)/2`, a function of the parameters, not of
  the shape.
- **(d) The days**: the witness is planted on `2 ≤ n < H`. `freshCoord` is small from day `2`
  only (`freshCoord_not_small_one`: `sizeBound 1 = 4` and the atom has five base-4 digits plus one
  token), so on day `n = 1` the base table has no coin coordinate at all — `coin_price`'s first
  conjunct cannot be stated — and `linked_fresh_half` is proved on `[2, H)` only. At `n = 1` the two
  slice tables are still distinct (`sliceT_ne_sliceF` needs `1 ≤ n`) but nothing controls the base's
  coin price; at `n = 0` even that fails. This is the N− recorded in the report; it is not hidden.
- **(e) The § 7 item-11 guard** (`charged_distinct`): the two charged tables are distinct and both
  have positive mass on every `2 ≤ n < H` — a face with at least two points and positive mass on
  every branch the mugging needs. (`NonDegenerate` in `bli-finite`'s product-face form fails at the
  two-point law, `Check.not_nonDegenerate_twoPointLaw`; the non-degeneracy of record is this one,
  as `bli-exact-base` § 4 declares.)

Sources: mandate T5; [[bli-program]] §7 items 9, 11; udt-bli-core U3; udt-bli-sist T8.
-/

namespace Cleanroom.Bli.BliWitnessLia

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist

noncomputable section

section Checks

variable {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
variable (c V : ℚ) (r₀ : Bool → ℚ)

/-- **(a) `NoCrossBranch` fails over the inductor** whenever `V ≠ 0`: it would give
`ClassInert {Ask} Ask` (`classInert_singleton_of_noCrossBranch`), which `not_classInert` refutes
— the Rec branch (mass `1/2`) values the Ask point at `V·[give]`. So U3's agreement lemma does not
apply, and the two rules separate for this reason.
Source: [[bli-program]] §7 item 9; §3.9 (U5: "`NoCrossBranch` fails"); mandate T5 (a)
Kind: P
Fidelity: exact
Hyps: (a) `V ≠ 0` -/
theorem not_noCrossBranch (hV : V ≠ 0) : ¬ (segmentSist H K hK n hn h2 c V r₀).NoCrossBranch :=
  fun hN => not_classInert hK hn h2 c V r₀ hV (classInert_singleton_of_noCrossBranch _ hN _)

/-- **(b) `Reflective` holds over the inductor**: the prior is `IndepData.toPrior` (state and
policy law independent), so every policy point of positive mass leaves every branch probability
at its state mass. U3's lemma therefore fails *only* through `NoCrossBranch`.
Source: mandate T5 (b) ("compute which"); udt-bli-core `IndepData.reflective_toPrior`
Kind: C (instance of `reflective_toPrior`)
Fidelity: exact
Hyps: (a) -/
theorem reflective : (segmentSist H K hK n hn h2 c V r₀).Reflective :=
  (sistSkelData (segmentSkeleton H K hK) n 0 (linkedTable n) (coinAt n (by omega)) c V r₀
    (askTable K hK hn)).reflective_toPrior

/-- **(c) The auditor's contrast**: with the stakes reversed (`V < c`), on the same prior under the
same hypotheses, one-step UDT *refuses* (strictly). The verdict `(V − c)/2` is not built into the
shape.
Source: mandate T5 (c) (`instance_refuse`); [[bli-program]] §7 item 9
Kind: C (from `verdict`)
Fidelity: exact
Hyps: (a) `V < c` -/
theorem instance_refuse (hcV : V < c) :
    (segmentSist H K hK n hn h2 c V r₀).IsOneStepChoice (askTable K hK hn) false ∧
      (segmentSist H K hK n hn h2 c V r₀).EU (askTable K hK hn) true <
        (segmentSist H K hK n hn h2 c V r₀).EU (askTable K hK hn) false := by
  have hd := verdict hK hn h2 c V r₀
  refine ⟨fun b => ?_, by linarith⟩
  cases b
  · exact le_rfl
  · linarith

/-- **(e) The § 7 item-11 guard**: the two charged tables are distinct and both positive at every
`2 ≤ n < H` — the non-degeneracy of record (two charged candidates on the coherent carrier).
Source: [[bli-program]] §7 item 11; mandate T5 (e); [[bli-exact-base-report]] § 4
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem charged_distinct :
    askTable K hK hn ≠ recTable K hK hn ∧
    0 < (segmentSist H K hK n hn h2 c V r₀).stateMass (askTable K hK hn) ∧
    0 < (segmentSist H K hK n hn h2 c V r₀).stateMass (recTable K hK hn) :=
  ⟨askTable_ne_recTable hK hn (by omega), stateMass_ask_pos hK hn h2 c V r₀,
    stateMass_rec_pos hK hn h2 c V r₀⟩

end Checks

/-- **(d) `freshCoord` is not small on day `1`**: `sizeBound 1 = 4`, while the coin's atom has
token size `(natDigits4 (code + 5)).length + 1 ≥ 6` (its code exceeds `64`, so at least four
base-4 digits — in fact five). So the witness cannot be planted on `n = 1`: the day-`1` base table
has no coin coordinate (the mandate's "`freshCoord ∉ smallSet 1`").
Source: mandate T5 (d); `Tables.freshCoord_mem_smallSet`'s docstring ("from day `2`")
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem freshCoord_not_small_one : freshCoord ∉ smallSet 1 := by
  rw [mem_smallSet]
  unfold SmallOn
  rw [show freshCoord = Formula.atom (freshAtomCode freshFamily (Nat.pair 0 0)) from rfl,
    tokenSize_atom]
  intro h
  have h1 := lt_pow_length_natDigits4 (freshAtomCode freshFamily (Nat.pair 0 0) + 5)
  have h64 : 64 < freshAtomCode freshFamily (Nat.pair 0 0) + 5 := by decide
  have h3 : (natDigits4 (freshAtomCode freshFamily (Nat.pair 0 0) + 5)).length ≤ 3 := by
    have : sizeBound 1 = 4 := by norm_num [sizeBound]
    omega
  have h4 : 4 ^ (natDigits4 (freshAtomCode freshFamily (Nat.pair 0 0) + 5)).length ≤ 4 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) h3
  norm_num at h4
  omega

/-- **(d) The days of record, in one line**: the coin is a day-`2` small sentence and not a day-`1`
one. Day `n = 2` is the first day on which the base table has a coin coordinate; the witness is
planted on `2 ≤ n < H` (smallest instance `H = 4`, `n = 2`; `n = 3` also for T1–T3).
Source: mandate T5 (d), § 3.2
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem day_two_first : freshCoord ∈ smallSet 2 ∧ freshCoord ∉ smallSet 1 :=
  ⟨freshCoord_mem_smallSet le_rfl, freshCoord_not_small_one⟩

end

end Cleanroom.Bli.BliWitnessLia
