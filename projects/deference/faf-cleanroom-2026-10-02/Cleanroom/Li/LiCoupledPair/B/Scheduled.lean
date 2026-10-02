import Cleanroom.Li.LiCoupledPair.B.Clocked
import Cleanroom.Found.LiQuoteLane.Conditioning

/-!
# `li-coupled-pair` · B · Scheduled: when the *scheduled* sequence's certificate holds

`Clocked.lean` discharges the conditioning route's certificate for a sequence whose positions
pay the fuel. This file asks the mandate's question for `li-quote-lane`'s **original**
schedule-indexed sequence `ledgerSeq a e` (position `t = ⟨⟨n, ⟨j, c⟩⟩, d⟩` carries the literal as
soon as `(e j).e n ≤ t`, whatever the cost): under what condition does its certificate
`MachineSentenceCodes (ledgerSeq a e)` — the `(c)` `hψ` of `conditioningRoute_inductor` — hold?
The condition offered is the chat's `e ≥ Λ` (anson-2-007: "publish a quote no earlier than the
stage by which its full computation has finished"), rendered in FAF's cost model:

`FuelDominated c₁ a e` — for every literal `(j, n, c)` the polarity program `c₁` halts on the
payload `p = ⟨n, ⟨j, c⟩⟩` within the route's clock at the scheduled position,
`clock (max ((e j).e n) p) = (max ((e j).e n) p + 1)² + 1`.

Under it the scheduled and the clocked sequences coincide position by position
(`ledgerSeq_eq_clockedSeq`), so the certificate transfers (`ledgerSeq_codes_of_dominated`) and
li-quote-lane's `conditioningRoute_inductor` runs with its `(c)` replaced by this hypothesis
(`conditioningRoute_inductor_of_dominated`).

**Repair round 2 (audit r2 adversarial B1).** The definition shipped before this round bounded
the fuel by `max ((e j).e n) p` *itself* (`∃ k ≤ max ((e j).e n) p, … ∈ evaln k c₁ p`). That is
unsatisfiable for every program, table and schedule: Mathlib's `evaln_bound` needs fuel strictly
*exceeding* the input `p`, and `p ≥ c` is unbounded in the rational code `c` for fixed `(j, n)` —
the argument of `not_perDay_dominated`, which the `max` was meant to escape and did not. The
refutation of that form is now the theorem `not_fuelDominated_le` (the auditor's probe,
`run/wp/li-coupled-pair/audit-r2-probes/FuelDominatedVacuous.lean`, made part of the package), and
the definition takes the clock at the scheduled position, which exceeds the payload
(`lt_clock`). Nothing downstream of `FuelDominated` changed shape: `ledgerSeq_eq_clockedSeq`,
`ledgerSeq_codes_of_dominated` and `conditioningRoute_inductor_of_dominated` have the same
statements with the repaired hypothesis.

**What the schedule can and cannot pay for** (findings R-13, sharpening F-B7 / R-8). The bound
`clock (max ((e j).e n) p)` is `clock p` as soon as `p ≥ (e j).e n`, i.e. for all but finitely
many rational codes `c` per `(j, n)`. So `FuelDominated c₁ a e` sits between the schedule-free
`PayloadClocked c₁ a` — the program halts within the route's clock on its own payload
(`fuelDominated_of_payloadClocked`) — and the restriction of that to payloads at or above the
publication stage (`payloadClocked_of_fuelDominated_above`). In FAF's fuel model the schedule can
pay for the *value* (the finitely many small codes per day) and never for the *threshold
comparison*: the position must pay for that, as `not_perDay_dominated` already showed for a
per-day bound. The chat's `e ≥ Λ` therefore degenerates, over li-quote-lane's per-threshold
rendering, into a property of the polarity program alone.

**Grade and non-vacuity.** `(c)` by the standards' letter (a fuel bound FAF does not supply for an
opaque program). **No instance is known**, and none is shipped. A degenerate (N−) one is not
available either: `gateVal a` is never constant (both polarities occur under every table, `ℚ`
being unbounded both ways), and Mathlib's `decode : ℕ → Option ℚ` runs a coprimality test, so any
polarity program computes a gcd; certifying one within the quadratic clock `(p + 1)² + 1` in
`evaln`'s fuel (every sub-evaluation's input below the fuel, every loop iteration costing one) is
a fuel-calculus project. FAF's `PolyFueled` combinators certify at *some* `clockOf a k`, not at
the route's fixed `clockOf 1 2`, and the schedule cannot absorb the difference (above). Whether
`FuelDominated` has any instance at all is stated OPEN (`exists_fuelDominated`, listed in
`li-coupled-pair-open.txt`); the honest status of the two theorems resting on it is
`partial: FuelDominated (c); no instance known`. The clocked route (`Clocked.lean`) needs no such
clause and is the answer to the mandate's angle-B question. Scope: one-way.
-/

namespace Cleanroom.Li.LiCoupledPair.B

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Nat.Partrec (Code)

attribute [local irreducible] Nat.sqrt

/-- The route's clock is monotone in the position.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clock_mono {s t : ℕ} (h : s ≤ t) : clock s ≤ clock t := by
  rw [clock_eq, clock_eq]
  exact Nat.add_le_add_right (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2) 1

/-- The payload is at least the threshold code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma code_le_ledgerPayload (j n c : ℕ) : c ≤ ledgerPayload j n c := by
  unfold ledgerPayload
  exact le_trans (Nat.right_le_pair j c) (Nat.right_le_pair n _)

/-- **The schedule dominates the fuel** (anson-2-007's `e(n) ≥ Λ(n)`, per literal): for every
item `j`, day `n` and rational code `c`, the polarity program halts on the literal's payload
`p = ⟨n, ⟨j, c⟩⟩` within the route's clock at the scheduled position, `clock (max ((e j).e n) p)`
— the schedule pays for the value, the payload for the threshold comparison (module docstring).
Repaired in repair round 2 (audit r2 adversarial B1): the earlier bound `k ≤ max ((e j).e n) p`
was refutable outright (`not_fuelDominated_le`). No instance is known (`exists_fuelDominated`).
Source: anson-2-007 (chat 04 L686–703, "require `e(n) ≥ Λ(n)`"); mandate angle B ("using the delay to pay for the value")
Kind: D
Fidelity: variant: the cost is `evaln` fuel at the route's clock; the threshold's own payload is in the bound (unavoidable over FAF, `evaln_bound`); no instance known
Hyps: n/a -/
def FuelDominated (c₁ : Code) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) : Prop :=
  ∀ j n c, (Encodable.decode (α := ℚ) c).isSome = true →
    gateVal a (ledgerPayload j n c) ∈
      Code.evaln (clock (max ((e j).e n) (ledgerPayload j n c))) c₁ (ledgerPayload j n c)

/-- **The schedule-free sufficient condition**: the polarity program halts within the route's
clock on the literal's own payload, for every literal. No schedule enters; `FuelDominated c₁ a e`
follows for every `e` (`fuelDominated_of_payloadClocked`), and is implied back for every literal
whose payload is at or above its publication stage (`payloadClocked_of_fuelDominated_above`).
Source: mandate angle B; findings R-13 (the schedule cannot pay for the threshold comparison)
Kind: D
Fidelity: n/a (a condition on the program alone)
Hyps: n/a -/
def PayloadClocked (c₁ : Code) (a : ℕ → ℕ → ℚ) : Prop :=
  ∀ j n c, (Encodable.decode (α := ℚ) c).isSome = true →
    gateVal a (ledgerPayload j n c) ∈
      Code.evaln (clock (ledgerPayload j n c)) c₁ (ledgerPayload j n c)

/-- **The schedule is not needed**: a program clocked on its own payload dominates every schedule.
Source: findings R-13
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem fuelDominated_of_payloadClocked {c₁ : Code} {a : ℕ → ℕ → ℚ} (h : PayloadClocked c₁ a)
    (e : ℕ → PublicationSchedule) : FuelDominated c₁ a e :=
  fun j n c hd => Code.evaln_mono (clock_mono (le_max_right _ _)) (h j n c hd)

/-- **The schedule cannot pay for the threshold comparison**: under `FuelDominated`, every literal
whose payload is at or above its publication stage — all but finitely many rational codes per
`(j, n)` — is decided by the program within the clock of its own payload.
Source: findings R-13
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem payloadClocked_of_fuelDominated_above {c₁ : Code} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hdom : FuelDominated c₁ a e) (j n c : ℕ)
    (hd : (Encodable.decode (α := ℚ) c).isSome = true)
    (hp : (e j).e n ≤ ledgerPayload j n c) :
    gateVal a (ledgerPayload j n c) ∈
      Code.evaln (clock (ledgerPayload j n c)) c₁ (ledgerPayload j n c) := by
  have h := hdom j n c hd
  rwa [max_eq_right hp] at h

/-- `ledgerIndex` reads the same three coordinates as `posDay`/`posItem`/`posCode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ledgerIndex_eq (t : ℕ) : ledgerIndex t = (posDay t, posItem t, posCode t) := rfl

/-- Under domination the clocked digit at a published position is the gate value: the position
is at least the payload and at least the publication stage, so its clock is at least the clock
the domination promises (`clock_mono`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clockDigit_eq_gateVal_of_dominated {a : ℕ → ℕ → ℚ} (c₁ : Code)
    (e : ℕ → PublicationSchedule) (hdom : FuelDominated c₁ a e) (t : ℕ)
    (hd : (Encodable.decode (α := ℚ) (posCode t)).isSome = true)
    (hs : (e (posItem t)).e (posDay t) ≤ t) :
    clockDigit (tokenCode c₁) t = gateVal a (posPayload t) := by
  have hmem := hdom (posItem t) (posDay t) (posCode t) hd
  rw [← posPayload_eq] at hmem
  obtain ⟨K, hK⟩ : ∃ K, clock t = K + 1 := ⟨clock t - 1, by have := lt_clock t; omega⟩
  have hpair : Nat.pair t 0 ≤ K := by have := pair_zero_lt_clock t; omega
  have h1 : posPayload t ≤ t := Nat.unpair_left_le t
  have hkK : clock (max ((e (posItem t)).e (posDay t)) (posPayload t)) ≤ K + 1 := by
    rw [← hK]
    exact clock_mono (max_le hs h1)
  have hsucc : gateVal a (posPayload t) ∈ Code.evaln (K + 1) c₁ (posPayload t) :=
    Code.evaln_mono hkK hmem
  unfold clockDigit
  rw [hK, tokenCode_evaln_of_le c₁ t K hpair hsucc]
  simp only [Option.getD_some]
  exact min_eq_left (le_trans (gateVal_le a _) (by norm_num))

/-- **Under domination the scheduled and the clocked sequences coincide**, position by position.
Source: mandate angle B; anson-2-007
Kind: P
Fidelity: n/a
Hyps: (c) `hdom` (the fuel domination, in place of the source's `e ≥ Λ`; no instance known); `hc` says `c₁` computes the polarity -/
theorem ledgerSeq_eq_clockedSeq {a : ℕ → ℕ → ℚ} (c₁ : Code) (e : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (hdom : FuelDominated c₁ a e) (t : ℕ) :
    ledgerSeq a e t = clockedSeq c₁ e t := by
  unfold ledgerSeq clockedSeq
  rw [ledgerIndex_eq]
  simp only
  by_cases hs : (e (posItem t)).e (posDay t) ≤ t
  · by_cases hd : (Encodable.decode (α := ℚ) (posCode t)).isSome = true
    · rw [if_pos ⟨hd, hs⟩, if_pos hs, clockDigit_eq_gateVal_of_dominated c₁ e hdom t hd hs,
        posPayload_eq t, gateVal_ledgerPayload, hd, cond_true]
      by_cases hlt : ratOfCode (posCode t) < a (posItem t) (posDay t)
      · simp [hlt, ledgerEntry, literalOf]
      · simp [hlt, ledgerEntry, literalOf]
    · rw [if_neg (fun h => hd h.1), if_pos hs]
      rcases clockDigit_tokenCode c₁ hc t with h0 | hg
      · rw [h0]; simp
      · rw [hg, posPayload_eq t, gateVal_ledgerPayload]
        simp only [Bool.not_eq_true] at hd
        simp [hd]
  · rw [if_neg (fun h => hs h.2), if_neg hs]

/-- **The scheduled sequence's certificate under domination**: li-quote-lane's `(c)` `hψ`, as a
theorem from `FuelDominated`. This is the chat's argument — the delay pays for the value — with
the cost metered in FAF's fuel at the route's clock and the threshold's payload in the bound.
No instance of the hypothesis is known (`exists_fuelDominated`, OPEN): the theorem is proved,
its hypothesis package is not known to be inhabited.
Source: anson-2-007; li-quote-lane findings F8; mandate angle B
Kind: C
Fidelity: variant: fuel in place of runtime; the threshold's payload in the bound
Hyps: (c) `hdom` (no instance known); `he` is the schedule's own poly-time certificate -/
theorem ledgerSeq_codes_of_dominated {a : ℕ → ℕ → ℚ} (c₁ : Code) (e : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (hdom : FuelDominated c₁ a e)
    (he : UnaryRuler fun p => (e p.unpair.1).e p.unpair.2) :
    MachineSentenceCodes (ledgerSeq a e) :=
  (clockedSeq_codes c₁ e he).of_eq fun t => (ledgerSeq_eq_clockedSeq c₁ e hc hdom t).symm

/-- **li-quote-lane's conditioning route with its `(c)` replaced by fuel domination**:
`conditioningRoute_inductor` at `ledgerSeq_codes_of_dominated`. Not a sharper hypothesis than
li-quote-lane's `hψ` (which is satisfiable at least for cheap tables): a *different* one, with no
instance known.
Source: anson-2-002 (`Lemma [Existence]`); li-quote-lane T6.3; mandate angle B
Kind: L (li-quote-lane's `conditioningRoute_inductor` at `ledgerSeq_codes_of_dominated`)
Fidelity: variant: plain trader class; `e ≥ Λ` as `FuelDominated`
Hyps: (c) `hdom` (no instance known) -/
theorem conditioningRoute_inductor_of_dominated (P : History) (DPH : DeductiveProcess)
    [IsLogicalInductor P DPH] {a : ℕ → ℕ → ℚ} (c₁ : Code) (e : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal a p)) (hdom : FuelDominated c₁ a e)
    (he : UnaryRuler fun p => (e p.unpair.1).e p.unpair.2) :
    IsLogicalInductor (ledgerConditionedHistory P a e) (ledgerConditionedProcess DPH a e) :=
  conditioningRoute_inductor P DPH a e (ledgerSeq_codes_of_dominated c₁ e hc hdom he)

/-! ## Why the bound must *exceed* the payload: two refutations -/

/-- **A per-day fuel bound is unsatisfiable** (finding F-B7, checked): a per-`(j, n)` domination
`∃ k ≤ (e j).e n, … ∈ evaln k c₁ (ledgerPayload j n c)` for *all* rational codes `c` holds for no
program, because a run on input `p` needs fuel `> p` (`evaln_bound`) and the payload is
unbounded in `c` (`code_le_ledgerPayload`, and infinitely many `c` code rationals). So the bound
must *exceed* the payload — which `max ((e j).e n) p` does not (`not_fuelDominated_le`); the
clock at the scheduled position does.
Source: anson-2-007 (the literal reading of `e(n) ≥ Λ(n)`); Mathlib `evaln_bound`
Kind: P
Fidelity: n/a (a fact about the rendering)
Hyps: (a) none -/
theorem not_perDay_dominated (c₁ : Code) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule)
    (j n : ℕ) :
    ¬ ∀ c, (Encodable.decode (α := ℚ) c).isSome = true →
      ∃ k ≤ (e j).e n, gateVal a (ledgerPayload j n c) ∈ Code.evaln k c₁ (ledgerPayload j n c) := by
  intro h
  -- A rational code above the publication stage: the codes of `m ↦ (m : ℚ)` are injective, so
  -- among `(e j).e n + 2` of them one exceeds `(e j).e n`.
  obtain ⟨c, hd, hc⟩ : ∃ c, (Encodable.decode (α := ℚ) c).isSome = true ∧ (e j).e n < c := by
    by_contra hall
    push Not at hall
    set M := (e j).e n
    have hinj : Function.Injective fun m : ℕ => Encodable.encode ((m : ℕ) : ℚ) :=
      Encodable.encode_injective.comp Nat.cast_injective
    have hsub : (Finset.range (M + 2)).image (fun m : ℕ => Encodable.encode ((m : ℕ) : ℚ)) ⊆
        Finset.range (M + 1) := by
      intro x hx
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hall _ (by simp)))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range, Finset.card_range] at hcard
    omega
  obtain ⟨k, hk, hmem⟩ := h c hd
  have hbound := Code.evaln_bound hmem
  have hpay : c ≤ ledgerPayload j n c := code_le_ledgerPayload j n c
  omega

/-- Rational codes are unbounded: `ℚ` is infinite and `encode` is injective.
Source: none: infrastructure (audit r2 probe `FuelDominatedVacuous.lean`)
Kind: L
Fidelity: n/a -/
theorem exists_rat_code_ge (M : ℕ) : ∃ q : ℚ, M ≤ Encodable.encode q := by
  by_contra hall
  push Not at hall
  have hinj : Function.Injective (fun q : ℚ => (⟨Encodable.encode q, hall q⟩ : Fin M)) := by
    intro q₁ q₂ h
    exact Encodable.encode_injective (by simpa using congrArg Fin.val h)
  exact not_injective_infinite_finite _ hinj

/-- **The pre-repair `FuelDominated` (fuel `≤ max ((e j).e n) p`) has no instance**, for every
program, table and schedule: pick a rational code `c ≥ (e 0).e 0`; then the bound is the payload
`p = ledgerPayload 0 0 c` itself and `evaln_bound` needs `p < k ≤ p`. This is audit round 2's
adversarial B1 (probe `FuelDominatedVacuous.lean`, `not_fuelDominated`), made part of the package
so that the record of why the bound must exceed the payload is machine-checked.
Source: audit r2 adversarial B1; Mathlib `evaln_bound`
Kind: P
Fidelity: n/a (a fact about the rendering)
Hyps: (a) none -/
theorem not_fuelDominated_le (c₁ : Code) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ¬ ∀ j n c, (Encodable.decode (α := ℚ) c).isSome = true →
      ∃ k ≤ max ((e j).e n) (ledgerPayload j n c),
        gateVal a (ledgerPayload j n c) ∈ Code.evaln k c₁ (ledgerPayload j n c) := by
  intro h
  obtain ⟨q, hq⟩ := exists_rat_code_ge ((e 0).e 0)
  set c := Encodable.encode q with hc
  have hd : (Encodable.decode (α := ℚ) c).isSome = true := by simp [hc]
  obtain ⟨k, hk, hmem⟩ := h 0 0 c hd
  have hlt : ledgerPayload 0 0 c < k := Code.evaln_bound hmem
  have hcp : c ≤ ledgerPayload 0 0 c := code_le_ledgerPayload 0 0 c
  have hmax : max ((e 0).e 0) (ledgerPayload 0 0 c) = ledgerPayload 0 0 c :=
    max_eq_right (le_trans hq hcp)
  rw [hmax] at hk
  omega

/-! ## OPEN: is the repaired hypothesis inhabited at all? -/

/-- **OPEN: `FuelDominated` has an instance** — some polarity program `c₁` (computing `gateVal a`
for some table `a`) halts within the route's clock `(max ((e j).e n) p + 1)² + 1` on every
literal's payload `p`, for some schedule `e`. By `fuelDominated_of_payloadClocked` it suffices
that `c₁` halts within `clock p` on every payload `p` (`PayloadClocked`), and by
`payloadClocked_of_fuelDominated_above` little less is needed. Unknown either way: the program
must run Mathlib's rational `decode` (a coprimality test, hence a gcd) and a comparison inside
quadratic `evaln` fuel on the *value* of `p`, every sub-evaluation's input below the fuel; the
payload is at least `c²` (`Nat.pair j c ≥ c²`), which leaves room, but a certificate is a
fuel-calculus construction FAF's `PolyFueled` combinators do not give at a fixed clock. Not rested
on by anything; the status of `ledgerSeq_codes_of_dominated` is `partial: FuelDominated (c); no
instance known` until this closes either way.
Source: audit r2 adversarial B1 (what a witness of the repaired hypothesis needs); mandate angle B
Kind: OPEN
Fidelity: n/a (open)
Hyps: n/a (open) -/
theorem exists_fuelDominated :
    ∃ (c₁ : Code) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule),
      (∀ p, c₁.eval p = Part.some (gateVal a p)) ∧ FuelDominated c₁ a e := by
  sorry

end Cleanroom.Li.LiCoupledPair.B
