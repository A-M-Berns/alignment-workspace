import Cleanroom.Li.LiCoupledPair.B.Conditioned
import Cleanroom.Li.LiCoupledPair.B.Sibling
import Cleanroom.Found.LiQuoteLane.Witnesses
import Cleanroom.Found.LiQuoteLane.PaperWitness

/-!
# `li-coupled-pair` · B · ConditionedWitness: the conditioned pair and the sibling at `paperDP 𝗜𝚺₁`

The construction-facing file of angle B (imports `Construction.LIACompiler` through
`li-quote-lane`'s `OneWay`/`Witnesses`): the general constructor `ConditionedPair.ofLIA` (every
field derived from FAF's `LIA_is_logical_inductor` and this package's theorems), its instance
`paperConditionedPair` at `T := 𝗜𝚺₁` with `P := liaHistory (paperDP 𝗜𝚺₁)`, `H :=` the one-way
pair's reader `paperOneWayPair.H` (`liaHistory` over `paperDP 𝗜𝚺₁ ⊕ ledger of P's prices of the
tag-0 atoms, next-day`), `XH := cleanX`, `f := succDeferral`, `σ := payoutSchedule` (`n + 2`), and
the sibling family by conditioning at the same table.

**N+ grounds proved** (mandate T1.3 / T4.1 criteria): both polarities occur in `A`'s clocked
record and in `H`'s ledger; `XH` is outside the ledger family (its atoms carry FAF's tag `0`); the
two processes differ — `H`'s ledger decides the day-`0`, item-`0` threshold with code `c` by stage
`c`, while `A`'s clocked process cannot have written that literal by stage `c` (its position is
`≥ ⟨0, ⟨0, c⟩⟩ = c⁴ > c` for `c ≥ 2`) — a *timing* difference, which is exactly what the clocked
record changes; and the sibling family varies with `N`. As in li-quote-lane F7, nothing is claimed
about the quote *values* (that would evaluate the LIA).

Also here (T2.3, finding): anson-2-008's "theorems output in the first `n` steps of a fixed
search" is FAF's own `theoremDP`/`paperTheoryDP`, by definition (`theoremDP_is_steps_form`).
Scope: one-way timed each way, meeting at `P` (`ConditionedPair`'s docstring).
-/

namespace Cleanroom.Li.LiCoupledPair.B

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc
open Nat.Partrec (Code)

attribute [local irreducible] Nat.sqrt

/-! ## A. The general constructor -/

/-- Payout two days after the question is a poly-time schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutSchedule_ruler :
    UnaryRuler fun p : ℕ => ((fun _ : ℕ => payoutSchedule) p.unpair.1).e p.unpair.2 :=
  (UnaryRuler.unpairSnd.add (UnaryRuler.const 2)).of_eq fun _ => rfl

/-- **The conditioned pair from FAF's LIA on both bases, every field derived**: `P := liaHistory DPA0`,
`H :=` li-quote-lane's `OneWayPair.ofLIA` reader over `DPH0 ⊕ ledger of P's prices`, `MH` its
market program, `c₁` a program for the polarity of `H`'s realized expectations
(`quoteGateCode_exists`), `A := P | ψ_H` an inductor by `clocked_inductor`, the package by
`crossQuotePackage_clocked`, the worlds by `clockedProcess_hworld` and T1.5.
Source: mandate angle B (the bundle); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: C
Fidelity: variant: `A = P | ψ_H` with `H` reading `P` (not the two-way pair); plain trader class; FAF's capped conditional
Hyps: (a) none -/
noncomputable def ConditionedPair.ofLIA (DPA0 DPH0 : DeductiveProcess)
    (hA : ComputableDeductiveProcess DPA0) (hH : ComputableDeductiveProcess DPH0)
    (quotedA : ℕ → ℕ → Sentence) (hq : Computable fun p : ℕ × ℕ => quotedA p.1 p.2)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (XH : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq XH) (f : DeferralFunction)
    (σ : ℕ → PublicationSchedule) (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2)
    (hfreeA : CleanroomFreeProcess DPA0) (hworldA0 : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA0.D n))
    (hfreeH : CleanroomFreeProcess DPH0) (hworldH0 : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH0.D n)) :
    ConditionedPair :=
  let pair := OneWayPair.ofLIA DPA0 DPH0 hA hH quotedA hq e he
    (processFreeOf_ledgerSchedule_of_cleanroomFree hfreeH) hworldH0
  let MH : MarketComputation pair.H := pair.H_inductor.marketComputable.nonemptyComputation.some
  let hc₁ := quoteGateCode_exists MH XH hX f
  { DPA0 := DPA0
    DPH0 := DPH0
    quotedA := quotedA
    e := e
    XH := XH
    f := f
    σ := σ
    P := liaHistory DPA0
    H := pair.H
    MH := MH
    c₁ := Classical.choose hc₁
    hc := Classical.choose_spec hc₁
    aP := pair.a
    aP_eq := pair.a_eq
    P_inductor := LIA_is_logical_inductor DPA0 hA
    A_inductor := @clocked_inductor (liaHistory DPA0) DPA0 (LIA_is_logical_inductor DPA0 hA)
      (Classical.choose hc₁) σ hσ
    H_inductor := pair.H_inductor
    package := crossQuotePackage_clocked MH XH f DPA0 (Classical.choose hc₁)
      (Classical.choose_spec hc₁) σ
    hworldA := clockedProcess_hworld (Classical.choose_spec hc₁)
      (processFreeOf_ledgerSchedule_of_cleanroomFree hfreeA) hworldA0
    hworldH := pair.hworld
    determinedH := pair.determined }

/-! ## B. The instance at `𝗜𝚺₁` -/

/-- **The conditioned pair at `paperDP 𝗜𝚺₁`** (N+): `P` the bare paper LIA, `H` the one-way pair's
reader (`paperOneWayPair.H`), `XH := cleanX` (tag-0 indicator LUVs), `f := succDeferral`,
`σ := payoutSchedule`. Scope: `A` reads `H` timed; `H` reads `P`.
Source: mandate T1.3 (the witness, angle B's analogue of `sigmaPair_paper`)
Kind: N+
Fidelity: variant (as `ConditionedPair`)
Hyps: (a) none -/
noncomputable def paperConditionedPair : ConditionedPair :=
  ConditionedPair.ofLIA (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) witnessQuoted witnessQuoted_computable
    (fun _ => PublicationSchedule.succ) succSchedule_computable cleanX cleanX_codes succDeferral
    (fun _ => payoutSchedule) payoutSchedule_ruler (paperDP_cleanroomFree 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁) (paperDP_cleanroomFree 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)

/-- The witness's `P` is the paper LIA, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperConditionedPair_P : paperConditionedPair.P = liaHistory (paperDP 𝗜𝚺₁) := rfl

/-- The witness's `H` is the one-way pair's reader, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperConditionedPair_H : paperConditionedPair.H = paperOneWayPair.H := rfl

/-- The witness's table of `P`'s prices is the one-way pair's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperConditionedPair_aP (j n : ℕ) :
    paperConditionedPair.aP j n = liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n) := rfl

/-- **N+: both polarities occur in `A`'s clocked record** of `H`'s realized expectations (`−1`
affirmed, `2` denied), for every day.
Source: mandate T1.3 (N+ criteria)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperConditionedPair_both_polarities_A (n : ℕ) :
    (∃ t, clockedSeq paperConditionedPair.c₁ paperConditionedPair.σ t =
        freshAtom ledgerFamily (ledgerPayload 0 n (Encodable.encode (-1 : ℚ)))) ∧
      ∃ t, clockedSeq paperConditionedPair.c₁ paperConditionedPair.σ t =
        ∼freshAtom ledgerFamily (ledgerPayload 0 n (Encodable.encode (2 : ℚ))) :=
  clockedSeq_both_polarities paperConditionedPair.c₁ paperConditionedPair.σ
    paperConditionedPair.hc
    (fun _ n => paperConditionedPair.MH.expectQuoteAt_mem_Icc cleanX n (succDeferral.f n)) 0 n

/-- **N+: both polarities occur in `H`'s ledger** of `P`'s prices (li-quote-lane's
`paperOneWayPair_both_polarities`).
Source: mandate T1.3 (N+ criteria)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperConditionedPair_both_polarities_H (j n : ℕ) :
    (∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule paperConditionedPair.aP paperConditionedPair.e).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule paperConditionedPair.aP paperConditionedPair.e).lits s :=
  paperOneWayPair_both_polarities j n

/-- **N+: `XH` is outside the ledger family** — `cleanX n`'s sentence is a tag-`0` atom, never a
family-3 atom.
Source: mandate T1.3 (N+ criteria: `XH` outside the ledger family)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem witnessQuoted_ne_freshAtom (j n p : ℕ) : witnessQuoted j n ≠ freshAtom ledgerFamily p := by
  intro h
  have h' := congrArg (fun φ : Sentence => match φ with
    | Formula.atom a => (Nat.unpair a).1 | _ => 0) h
  simp [witnessQuoted, freshAtom, freshAtomCode, cleanroomBaseTag, ledgerFamily] at h'

/-- Some rational has a code `≥ 2` (three distinct codes cannot all be `< 2`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_rat_code_ge_two : ∃ q : ℚ, 2 ≤ Encodable.encode q := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hne01 : Encodable.encode (0 : ℚ) ≠ Encodable.encode (1 : ℚ) := fun e =>
    by norm_num [Encodable.encode_injective.eq_iff] at e
  have hne02 : Encodable.encode (0 : ℚ) ≠ Encodable.encode (2 : ℚ) := fun e =>
    by norm_num [Encodable.encode_injective.eq_iff] at e
  have hne12 : Encodable.encode (1 : ℚ) ≠ Encodable.encode (2 : ℚ) := fun e =>
    by norm_num [Encodable.encode_injective.eq_iff] at e
  omega

/-- A family-3 literal is in no stage of a cleanroom-free process.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma literalOf_not_mem_of_cleanroomFree {DP : DeductiveProcess} (h : CleanroomFreeProcess DP)
    (k p : ℕ) (b : Bool) : literalOf (ledgerFamily, p, b) ∉ DP.D k := by
  intro hmem
  have hfree := h k _ hmem (freshAtomCode ledgerFamily p)
  cases b
  · simp [literalOf, freshAtom, freshAtomCode_unpair, cleanroomBaseTag, ledgerFamily] at hfree
  · simp [literalOf, freshAtom, freshAtomCode_unpair, cleanroomBaseTag, ledgerFamily] at hfree

/-- **N+: the two processes differ** — a *timing* difference. For a rational code `c ≥ 2`, `H`'s
ledger (next-day publication) holds the day-`0`, item-`0`, threshold-`c` literal at stage `c`,
while `A`'s clocked process holds no literal of that payload at stage `c`: its position is at least
the payload `⟨0, ⟨0, c⟩⟩ = c⁴ > c`, and `paperDP 𝗜𝚺₁` is cleanroom-free. Nothing about the quote
values is used.
Source: mandate T1.3 (N+ criteria: the two processes differ)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperConditionedPair_processes_differ :
    ∃ s φ, φ ∈ paperConditionedPair.processH.D s ∧ φ ∉ paperConditionedPair.processA.D s := by
  obtain ⟨q, hq⟩ := exists_rat_code_ge_two
  set c := Encodable.encode q with hc
  have hd : (Encodable.decode (α := ℚ) c).isSome = true := by simp [hc]
  refine ⟨c, literalOf (ledgerEntry paperConditionedPair.aP 0 0 c), ?_, ?_⟩
  · show _ ∈ (ledgerProcess (paperDP 𝗜𝚺₁) paperConditionedPair.aP (fun _ => PublicationSchedule.succ)).D c
    rw [ledgerProcess_D, Finset.mem_union]
    refine Or.inr (Finset.mem_image.mpr ⟨ledgerEntry paperConditionedPair.aP 0 0 c, ?_, rfl⟩)
    rw [← ledgerSchedule_lits, mem_ledgerSchedule_iff]
    exact ⟨0, 0, c, Nat.zero_le _, Nat.zero_le _, le_rfl, by show 1 ≤ c; omega, hd, rfl⟩
  · intro hmem
    rw [ConditionedPair.processA, clockedProcess_D, Finset.mem_union] at hmem
    rcases hmem with hbase | hpre
    · exact literalOf_not_mem_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) c _ _ hbase
    · obtain ⟨t, hts, ht⟩ := mem_prefixProcess.mp hpre
      obtain ⟨hp, -⟩ := clockedSeq_eq_literal_imp _ _ t _ _ ht
      have hpay : ledgerPayload 0 0 c = c * c * (c * c) := by
        simp only [ledgerPayload, Nat.pair]
        have hc0 : 0 < c := by omega
        simp [hc0]
      have hle : posPayload t ≤ t := Nat.unpair_left_le t
      have h3 : c * c * (c * c) ≤ c := by rw [← hpay, hp]; omega
      have h1 : c < c * c := by nlinarith
      have h2 : c * c ≤ c * c * (c * c) := Nat.le_mul_of_pos_right _ (by positivity)
      linarith

/-! ## C. The sibling family at the same table -/

/-- A polarity program for the one-way pair's table `liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n)`
(`gateCode_exists` on `liaQuote_computable`).
Source: none: infrastructure (T4.1 witness)
Kind: L
Fidelity: n/a -/
theorem paperSiblingGateCode_exists :
    ∃ c₁ : Code, ∀ p, c₁.eval p = Part.some (gateVal paperConditionedPair.aP p) :=
  gateCode_exists (liaQuote_computable (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) witnessQuoted
    witnessQuoted_computable)

/-- The chosen polarity program of the sibling witness.
Source: none: infrastructure (T4.1 witness)
Kind: D
Fidelity: n/a -/
noncomputable def paperSiblingCode : Code := Classical.choose paperSiblingGateCode_exists

/-- `paperSiblingCode` computes the table's polarity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperSiblingCode_spec :
    ∀ p, paperSiblingCode.eval p = Part.some (gateVal paperConditionedPair.aP p) :=
  Classical.choose_spec paperSiblingGateCode_exists

/-- **T4.1 witness (angle B): the sibling family at `paperDP 𝗜𝚺₁`**, `A := liaHistory (paperDP 𝗜𝚺₁)`
reading nothing, each `H^{[N]} := liaHistory (paperDP 𝗜𝚺₁) | (frozen clocked record of `A`'s
prices of the tag-0 atoms, next-day gate)` an inductor over its frozen process, with
determinacy below `N`, freezing at and above, worlds, and the family varying with `N`.
Source: mandate T4.1 (`siblingFamily_paper`); [[frozen-deliberation-deference-v6]] §3
Kind: N+
Fidelity: variant: plain trader class; FAF's capped conditional; clocked positions
Hyps: (a) none -/
theorem paperSiblingFamily (N : ℕ) :
    IsLogicalInductor
        (siblingHistoryB (liaHistory (paperDP 𝗜𝚺₁)) paperSiblingCode
          (fun _ => PublicationSchedule.succ) N)
        (siblingProcessB (paperDP 𝗜𝚺₁) paperSiblingCode (fun _ => PublicationSchedule.succ) N) ∧
      (∀ j n, n < N → LUV.DeterminedVia (ledgerLuv j n)
        (siblingProcessB (paperDP 𝗜𝚺₁) paperSiblingCode (fun _ => PublicationSchedule.succ) N)
        (liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n))) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith
        ((siblingProcessB (paperDP 𝗜𝚺₁) paperSiblingCode (fun _ => PublicationSchedule.succ) N).D n)) ∧
      (∃ s, freshAtom ledgerFamily (ledgerPayload 0 N (Encodable.encode (-1 : ℚ))) ∈
        (prefixProcess (frozenSeq paperSiblingCode (fun _ => PublicationSchedule.succ) (N + 1))).D s) ∧
      ∀ s, freshAtom ledgerFamily (ledgerPayload 0 N (Encodable.encode (-1 : ℚ))) ∉
        (prefixProcess (frozenSeq paperSiblingCode (fun _ => PublicationSchedule.succ) N)).D s := by
  have hmem : ∀ j n, 0 ≤ paperConditionedPair.aP j n ∧ paperConditionedPair.aP j n ≤ 1 :=
    fun j n => liaQuote_mem (paperDP 𝗜𝚺₁) n (witnessQuoted j n)
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁)
  obtain ⟨h4, h5⟩ := siblingPrefix_ne_succ paperSiblingCode (fun _ => PublicationSchedule.succ)
    paperSiblingCode_spec hmem N
  exact ⟨sibling_inductor_B _ _ paperSiblingCode _ succSchedule_ruler N,
    fun j n hn => ledgerLuv_determinedVia_sibling _ paperSiblingCode _ paperSiblingCode_spec hmem
      N j n hn,
    siblingProcessB_hworld paperSiblingCode_spec N
      (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
      (paperDP_hworld 𝗜𝚺₁),
    h4, h5⟩

/-! ## D. T2.3: the "first `n` steps of a fixed search" process is FAF's own paper process -/

/-- **T2.3 (finding, cited): anson-2-008's e.c. and `Γ`-complete process** "theorems output in the
first `n` steps of a fixed proof search" **is** FAF's `theoremDP T` — the dovetail of a
semi-decider under the event naming map — by definition. The item's existence claim is realized
by FAF's own paper process; its "poly-time in unary `n`" clause has no FAF object for processes
(`ComputableDeductiveProcess` carries no efficiency clause) — findings F-B6.
Source: anson-2-008 (chat 04 L7404–7407); mandate T2.3; FAF `theoremDP`, `dovetailProcess`
Kind: L
Fidelity: exact (the existence claim); the efficiency clause has no FAF carrier
Hyps: (a) none -/
theorem theoremDP_is_steps_form (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] :
    theoremDP T = dovetailProcess eventAtom (exists_eventCode T).choose := rfl

/-- The same for the paper's theory process `paperTheoryDP T`.
Source: anson-2-008; FAF `paperTheoryDP`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem paperTheoryDP_is_steps_form (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] :
    paperTheoryDP T = dovetailProcess paperTheoremSentence (exists_paperTheoremCode T).choose :=
  rfl

end Cleanroom.Li.LiCoupledPair.B
