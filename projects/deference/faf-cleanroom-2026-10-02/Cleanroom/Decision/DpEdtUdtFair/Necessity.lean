import Cleanroom.Decision.DpEdtUdtFair.FairWitnesses
import Cleanroom.Decision.DpCalibration.ToldYouSo
import Cleanroom.Decision.DpCalibration.Witnesses
import Cleanroom.Decision.DpEdtUdtFair.Devices

/-!
# Each hypothesis of Theorem 3 is necessary (T7 (ii)–(iv)) and Claim 3.2 as stated is refuted
(T16(a))

Each row proves the *other* hypotheses of Theorem 3, the device (D2, `EventTrembleEdtConsistent`),
and `¬ IsOptimal`, on a finite tree:

* **(ii) no fairness** — `twoStag` with `(H, H)`: almost fair, `FRec` (with `stagObs = ⊤` and the
  act-recording `stagActEv`), pruned, realized, **not strongly fair** (`dp-local-opt`), D2-consistent
  (`𝔼_ε[r ∣ act₁ = S] = ε < 1 − ε/2 = 𝔼_ε[r ∣ act₁ = H]`, and symmetrically at `p2`), `V = 1 < 2`.
* **(iii) no recording** — `toldYouSo` with `C₀ = (five, ten)`: strongly fair, pruned, realized,
  **not recording at `d₅`** (the root is not subtree-veridical), D2-consistent (at `d₅` only
  `five ∧ O₅` is realized; at `d₁₀`, `ten` beats `five`), `V = 5 < 10`. ZO-4's non-selection
  clauses: `mislabelled` (`δ_a` approved, `V = 0 < 1`; action-veridicality fails) and `doppel`
  (`δ_a` approved with `𝔼_ε[r ∣ act = a] = 5/(1 − ε/4) > 1`, `V = 5 < 11/2`; coverage fails).
* **(iv) no realized observation** — `a1Node` with `δ_a`: strongly fair, `RecordsForAll`
  vacuously, pruned, D2 vacuous because the guard `nuPoly O_d ≠ 0` fails (the escape clause
  fires), `V = 0 < 1`. This is A.1's kill of FR-11 as first stated.
* **Claim 3.2 as stated (fable-slop-notes l. 65) is refuted** by `mislabelled`: its hypothesis
  "Proposition 3's hypotheses at every point" (= `H_d`: coverage and subtree-veridicality) holds
  there, the procedure is deterministic and D2-consistent, and it is not optimal.

The no-trembles row (i) is in `Threat.lean` (it needs the calibration senses).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

/-! ### (ii) No fairness: the Stag Hunt -/

section stag

/-- `ν` on `twoStag` under `proc2 p q`. Source: none: infrastructure. Kind: L -/
theorem twoStag_nu (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (X : Finset MiniW) :
    nu (proc2 p q hp0 hp1 hq0 hq1) twoStag X =
      ((if (Act2.a, Act2.a) ∈ X then p * q else 0) + (if (Act2.a, Act2.b) ∈ X then p * (1 - q) else 0)) +
      ((if (Act2.b, Act2.a) ∈ X then (1 - p) * q else 0) +
        (if (Act2.b, Act2.b) ∈ X then (1 - p) * (1 - q) else 0)) := by
  rw [nu_eq_sum, twoStag_sum]
  simp [twoStag, leafLaw_decision, world_decision, proc2, FinDistr.act2]

/-- `𝔼[r 1_X]` on `twoStag` under `proc2 p q`. Source: none: infrastructure. Kind: L -/
theorem twoStag_paySum (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (X : Finset MiniW) :
    paySum (proc2 p q hp0 hp1 hq0 hq1) twoStag X =
      (if (Act2.a, Act2.a) ∈ X then p * q * 2 else 0) +
        (if (Act2.b, Act2.b) ∈ X then (1 - p) * (1 - q) * 1 else 0) := by
  rw [paySum_eq_sum_ite, twoStag_sum]
  simp [twoStag, leafLaw_decision, world_decision, payoff_decision, proc2, FinDistr.act2]

/-- The four act-conditioned values on `twoStag` under `proc2 p q` (the source's
`𝔼[r ∣ act₁ = S] = 2q`, `𝔼[r ∣ act₁ = H] = 1 − q`, and symmetrically at `p2`), with their
denominators.
Source: `identity.md` ID-21 ("`𝔼_{C^ε}[r ∣ act₁ = S] = ε < 1 − ε/2`"); `zoo.md` ZO-7
Kind: P -/
theorem twoStag_condExp (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p1 .a ∩ stagObs .p1) = p ∧
    nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p1 .b ∩ stagObs .p1) = 1 - p ∧
    nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p2 .a ∩ stagObs .p2) = q ∧
    nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p2 .b ∩ stagObs .p2) = 1 - q ∧
    (0 < p → condExp (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p1 .a ∩ stagObs .p1) = 2 * q) ∧
    (p < 1 → condExp (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p1 .b ∩ stagObs .p1) = 1 - q) ∧
    (0 < q → condExp (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p2 .a ∩ stagObs .p2) = 2 * p) ∧
    (q < 1 → condExp (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p2 .b ∩ stagObs .p2) = 1 - p) := by
  have h1 : nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p1 .a ∩ stagObs .p1) = p := by
    rw [twoStag_nu]; simp [stagActEv, stagObs]; ring
  have h2 : nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p1 .b ∩ stagObs .p1) = 1 - p := by
    rw [twoStag_nu]; simp [stagActEv, stagObs]; ring
  have h3 : nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p2 .a ∩ stagObs .p2) = q := by
    rw [twoStag_nu]; simp [stagActEv, stagObs]; ring
  have h4 : nu (proc2 p q hp0 hp1 hq0 hq1) twoStag (stagActEv .p2 .b ∩ stagObs .p2) = 1 - q := by
    rw [twoStag_nu]; simp [stagActEv, stagObs]; ring
  refine ⟨h1, h2, h3, h4, fun hp => ?_, fun hp => ?_, fun hq => ?_, fun hq => ?_⟩
  · unfold condExp; rw [h1, twoStag_paySum]; simp [stagActEv, stagObs]; field_simp
  · unfold condExp; rw [h2, twoStag_paySum]; simp [stagActEv, stagObs]
    have : (1 - p) ≠ 0 := by linarith
    field_simp
  · unfold condExp; rw [h3, twoStag_paySum]; simp [stagActEv, stagObs]; field_simp
  · unfold condExp; rw [h4, twoStag_paySum]; simp [stagActEv, stagObs]
    have : (1 - q) ≠ 0 := by linarith
    field_simp

/-- `twoStag` records at `p1` for every procedure (`O = ⊤`, worlds record `act₁`).
Source: `identity.md` ID-21 ("recorded at both points for every procedure")
Kind: N+ -/
theorem twoStag_recordsForAll_p1 : RecordsForAll stagObs stagActEv twoStag .p1 := by
  intro C ℓ _ _
  unfold twoStag at ℓ ⊢
  rcases ℓ with ⟨a₁, ℓ⟩
  cases a₁ <;> rcases ℓ with ⟨a₂, _⟩ <;> cases a₂ <;>
  · refine ⟨by simp [count_decision, count_leaf], ?_⟩
    rintro (_ | ⟨b, q⟩) hq a ha
    · simp only [edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨fun _ _ => by simp [stagObs], by simp [stagActEv, world_decision, world_leaf], ?_⟩
      intro a' ha'
      cases a' <;> simp [stagActEv, world_decision, world_leaf] at ha' ⊢
    · cases b <;> rcases q with _ | ⟨c, q'⟩
      all_goals first
        | (cases c <;> exact q'.elim)
        | (simp [pt] at hq)

/-- `twoStag` records at `p2` for every procedure (`O = ⊤`, worlds record `act₂`; each path
passes exactly one `p2`-node).
Source: `identity.md` ID-21
Kind: N+ -/
theorem twoStag_recordsForAll_p2 : RecordsForAll stagObs stagActEv twoStag .p2 := by
  intro C ℓ _ _
  unfold twoStag at ℓ ⊢
  rcases ℓ with ⟨a₁, ℓ⟩
  cases a₁ <;> rcases ℓ with ⟨a₂, _⟩ <;> cases a₂ <;>
  · refine ⟨by simp [count_decision, count_leaf], ?_⟩
    rintro (_ | ⟨b, q⟩) hq a ha
    · simp [pt] at hq
    · cases b <;> rcases q with _ | ⟨c, q'⟩
      all_goals first
        | (cases c <;> exact q'.elim)
        | (simp only [edgeOf_decision_some, dite_true, edgeOf_decision_none,
            Option.some.injEq] at ha
           subst ha
           refine ⟨fun _ _ => by simp [stagObs],
             by simp [stagActEv, pt, world_decision, world_leaf], ?_⟩
           intro a' ha'
           cases a' <;> simp [stagActEv, pt, world_decision, world_leaf] at ha' ⊢)
        | (simp [edgeOf_decision_some] at ha)

/-- `twoStag` is pruned and both observations are realized.
Source: none: infrastructure
Kind: L -/
theorem twoStag_pruned_realized :
    Pruned twoStag ∧ ∀ d ∈ queried twoStag, Realized stagObs twoStag d := by
  refine ⟨?_, fun d _ => ?_⟩
  · rintro ⟨a₁, ℓ⟩
    cases a₁ <;> rcases ℓ with ⟨a₂, _⟩ <;> cases a₂ <;>
      simp [Positive, twoStag, chanceWeight_decision, chanceWeight_leaf]
  · exact ⟨⟨.a, .a, ()⟩, by simp [Positive, twoStag, chanceWeight_decision, chanceWeight_leaf],
      by simp [stagObs]⟩

/-- **`(H, H)` on the Stag Hunt is event-tremble-EDT-consistent** (D2): under `C^ε` at `p1`,
`𝔼_ε[r ∣ act₁ = S] = ε ≤ 1 − ε/2 = 𝔼_ε[r ∣ act₁ = H]` for `ε ≤ 2/3`, and symmetrically at `p2`.
Source: `identity.md` ID-21 ("tremble-EDT-consistent (`𝔼_{C^ε}[r ∣ act₁ = S] = ε < 1 − ε/2`)");
`zoo.md` ZO-7; `spectrum.md` SP-16
Kind: N+ -/
theorem twoStag_HH_eventTremble : EventTrembleEdtConsistent stagObs stagActEv profHH twoStag := by
  refine ⟨1 / 2, by norm_num, fun ε h0 h1 hlt d _ _ _ a ha => ?_⟩
  unfold profHH at ha ⊢
  rw [tremble_proc2]
  obtain ⟨n1, n2, n3, n4, c1, c2, c3, c4⟩ := twoStag_condExp ((1 - ε) * 0 + ε / 2) ((1 - ε) * 0 + ε / 2)
    (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).1 (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).2
    (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).1 (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).2
  cases d <;> cases a <;> simp [proc2, FinDistr.act2] at ha
  · refine ⟨by rw [n2]; linarith, fun b _ => ?_⟩
    cases b
    · rw [c1 (by linarith), c2 (by linarith)]; linarith
    · exact le_rfl
  · refine ⟨by rw [n4]; linarith, fun b _ => ?_⟩
    cases b
    · rw [c3 (by linarith), c4 (by linarith)]; linarith
    · exact le_rfl

/-- **T7(ii), no fairness**: the two-point Stag Hunt with `(H, H)` inhabits every hypothesis of
Theorem 3 except strong fairness (almost fair, `FRec`, pruned, realized), is D2-consistent, and is
not optimal (`V = 1 < 2`). Also Definition-22-coherent (pure and mixed) and Theorem-1-ratified
(`dp-local-opt`), so "even D2 approves `(H, H)` on the almost-fair class" (Proposition ID-R).
Source: `fair-repair.md` §3.2 ("Without fairness"); `identity.md` ID-21, ID-23 (Proposition ID-R);
A36 (iii); `spectrum.md` SP-16; dp-cf-068, dp-cf-2-020, dp-cf-2-060
Kind: N+
Fidelity: exact (the source's TN-V2 instance is replaced by the Stag Hunt, ID-21's honest
almost-fair witness; TN-V2 is not almost fair, `dp-fairness-reloc`'s `tnV2_not_almostFair`)
Hyps: (a) all -/
theorem twoStag_HH_eventTremble_not_optimal :
    AlmostFair twoStag ∧ FRec stagObs stagActEv twoStag ∧ Pruned twoStag ∧
    (∀ d ∈ queried twoStag, Realized stagObs twoStag d) ∧ ¬ StronglyFair twoStag ∧
    EventTrembleEdtConsistent stagObs stagActEv profHH twoStag ∧ ¬ IsOptimal profHH twoStag ∧
    value profHH twoStag = 1 ∧ Coherent profHH twoStag ∧ Thm1 profHH twoStag := by
  obtain ⟨hcoh, -, hthm1, hnot, hval, -⟩ := twoStag_HH_coherent_thm1_not_optimal
  exact ⟨twoStag_not_stronglyFair.1, fun d _ => by
      cases d
      · exact twoStag_recordsForAll_p1
      · exact twoStag_recordsForAll_p2,
    twoStag_pruned_realized.1, twoStag_pruned_realized.2, twoStag_not_stronglyFair.2,
    twoStag_HH_eventTremble, hnot, hval, hcoh, hthm1⟩

end stag

/-! ### (iii) No recording: Told-You-So, `mislabelled`, `doppel` -/

section tys

/-- `toldYouSo` has one node per point.
Source: `fair-repair.md` §3.2 ("Told-You-So `B_P` is strongly fair (both fibers singletons!)")
Kind: L -/
theorem toldYouSo_pt_injective : Function.Injective (pt toldYouSo) := by
  intro q q' h
  rcases q with _ | ⟨a, q⟩
  · rcases q' with _ | ⟨a', q'⟩
    · rfl
    · cases a'
      · exact q'.elim
      · rcases q' with _ | ⟨a'', q''⟩
        · exact absurd h (by simp [toldYouSo, pt])
        · cases a'' <;> exact q''.elim
  · cases a
    · exact q.elim
    · rcases q with _ | ⟨a'', q''⟩
      · rcases q' with _ | ⟨a', q'⟩
        · exact absurd h (by simp [toldYouSo, pt])
        · cases a'
          · exact q'.elim
          · rcases q' with _ | ⟨a''', q'''⟩
            · rfl
            · cases a''' <;> exact q'''.elim
      · cases a'' <;> exact q''.elim

/-- `toldYouSo` is strongly fair, pruned, and both observations are realized.
Source: `fair-repair.md` §3.2
Kind: L -/
theorem toldYouSo_fair_pruned_realized :
    StronglyFair toldYouSo ∧ Pruned toldYouSo ∧
    ∀ d ∈ queried toldYouSo, Realized tysObs toldYouSo d := by
  refine ⟨StronglyFair.of_injective_pt toldYouSo_pt_injective, ?_, fun d _ => ?_⟩
  · rintro ⟨a, ℓ⟩
    cases a
    · simp [Positive, toldYouSo, chanceWeight_decision, chanceWeight_leaf]
    · rcases ℓ with ⟨b, _⟩
      cases b <;> simp [Positive, toldYouSo, chanceWeight_decision, chanceWeight_leaf]
  · cases d
    · exact ⟨⟨.five, ()⟩, by simp [Positive, toldYouSo, chanceWeight_decision, chanceWeight_leaf],
        by simp [tysObs, toldYouSo, world_decision, world_leaf]⟩
    · exact ⟨⟨.ten, .ten, ()⟩,
        by simp [Positive, toldYouSo, chanceWeight_decision, chanceWeight_leaf],
        by simp [tysObs, toldYouSo, world_decision, world_leaf]⟩

/-- **`toldYouSo` does not record at `d₅` for `C₀`**: the `O₅`-run through the root has the root
as its `d₅`-node, and the root is not subtree-veridical (the leaves `(10, ·)` lie below it).
Source: `fair-repair.md` §3.2 ("`B_P` fails subtree-veridicality at the root … and fails
recording at `d₅`"); mandate T1(b)
Kind: N+ -/
theorem toldYouSo_not_recordsFor_five :
    ¬ RecordsFor tysObs tysActEv procFiveTen toldYouSo .five := by
  intro h
  have hpos : 0 < leafLaw procFiveTen toldYouSo ⟨.five, ()⟩ := by
    simp [toldYouSo, leafLaw_decision, procFiveTen]
  have hobs : world toldYouSo ⟨.five, ()⟩ ∈ tysObs .five := by
    simp [toldYouSo, world_decision, tysObs]
  have hsv := ((h _ hpos hobs).2 none rfl .five rfl).1
  have := hsv ⟨.ten, .ten, ()⟩ ((mem_leavesBelow _ _ _).mpr rfl)
  simp [toldYouSo, world_decision, tysObs] at this

/-- `Fintype.card Five10 = 2`. Source: none: infrastructure. Kind: L -/
theorem card_five10 : Fintype.card Five10 = 2 := rfl

/-- **`C₀ = (five, ten)` on Told-You-So is event-tremble-EDT-consistent** (D2): at `d₅` only
`five ∧ O₅` is realized (no leaf-world has `n = 5 ∧ m = 10`), so the argmax is `{five}`; at `d₁₀`,
`𝔼_ε[r ∣ ten ∧ O₁₀] = 10 > 5 = 𝔼_ε[r ∣ five ∧ O₁₀]`.
Source: `fair-repair.md` §3.2 ("take-5 is tremble-EDT-consistent"); `grounding.md` GR-22 (b)
Kind: N+ -/
theorem toldYouSo_fiveTen_eventTremble :
    EventTrembleEdtConsistent tysObs tysActEv procFiveTen toldYouSo := by
  refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a ha => ?_⟩
  have hc : ((Fintype.card Five10 : ℕ) : ℚ) = 2 := by rw [card_five10]; norm_num
  cases d <;> cases a <;> simp [procFiveTen, Proc.ofFun_w] at ha
  · refine ⟨?_, fun b hb => ?_⟩
    · rw [tys_nu]; simp [tysObs, tysActEv, tremble_w, procFiveTen, Proc.ofFun_w, hc]; linarith
    · cases b
      · exact le_rfl
      · rw [tys_nu] at hb
        simp [tysObs, tysActEv] at hb
  · refine ⟨?_, fun b _ => ?_⟩
    · rw [tys_nu]; simp [tysObs, tysActEv, tremble_w, procFiveTen, Proc.ofFun_w, hc]
      nlinarith
    · cases b
      · have h2 : ε * 2⁻¹ * (ε * 2⁻¹) ≠ 0 := by positivity
        have h3 : ε * 2⁻¹ * ((1 - ε) + ε * 2⁻¹) ≠ 0 := by
          have : 0 < ε * 2⁻¹ * ((1 - ε) + ε * 2⁻¹) := by nlinarith
          exact this.ne'
        have c5 : condExp (tremble procFiveTen ε h0.le h1) toldYouSo
            (tysActEv .ten .five ∩ tysObs .ten) = 5 := by
          unfold condExp
          rw [tys_nu, tys_paySum]
          simp [tysObs, tysActEv, tremble_w, procFiveTen, Proc.ofFun_w, hc]
          field_simp
        have c10 : condExp (tremble procFiveTen ε h0.le h1) toldYouSo
            (tysActEv .ten .ten ∩ tysObs .ten) = 10 := by
          unfold condExp
          rw [tys_nu, tys_paySum]
          simp [tysObs, tysActEv, tremble_w, procFiveTen, Proc.ofFun_w, hc]
          field_simp
        rw [c5, c10]; norm_num
      · exact le_rfl

/-- `V(C₀) = 5` and `V(C*) = 10` on Told-You-So.
Source: [[decision-problems-v2]] §7.1 Proposition 8
Kind: L -/
theorem toldYouSo_values :
    value procFiveTen toldYouSo = 5 ∧ value procTake10 toldYouSo = 10 := by
  constructor <;>
  · unfold value
    rw [tys_sum]
    simp [toldYouSo, leafLaw_decision, payoff_decision, procFiveTen, procTake10, Proc.ofFun_w]

/-- **T7(iii), no recording**: Told-You-So with `C₀ = (five, ten)` is strongly fair, pruned,
realized, D2-consistent, not recording at `d₅`, and not optimal (`V = 5 < 10`). The fair class
without recording contains Löb-style traps: recording is the third load-bearing hypothesis.
Source: `fair-repair.md` §3.2 ("Without veridicality/recording"); A36 (iii); `grounding.md`
GR-13, GR-22; dp-cf-2-049
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem toldYouSo_fiveTen_eventTremble_not_optimal :
    StronglyFair toldYouSo ∧ Pruned toldYouSo ∧
    (∀ d ∈ queried toldYouSo, Realized tysObs toldYouSo d) ∧
    ¬ RecordsFor tysObs tysActEv procFiveTen toldYouSo .five ∧
    EventTrembleEdtConsistent tysObs tysActEv procFiveTen toldYouSo ∧
    ¬ IsOptimal procFiveTen toldYouSo ∧ value procFiveTen toldYouSo = 5 := by
  obtain ⟨hf, hp, hr⟩ := toldYouSo_fair_pruned_realized
  refine ⟨hf, hp, hr, toldYouSo_not_recordsFor_five, toldYouSo_fiveTen_eventTremble, fun h => ?_,
    toldYouSo_values.1⟩
  have := h procTake10
  rw [toldYouSo_values.1, toldYouSo_values.2] at this
  norm_num at this

end tys

section zo4

/-- `Proc.ofFun (fun _ => a)` on a `Unit` point is `procQ 1`; `δ_b` is `procQ 0`.
Source: none: infrastructure
Kind: L -/
theorem ofFun_eq_procQ :
    (Proc.ofFun fun _ => Act2.a : Proc Unit (fun _ => Act2) ℚ) = procQ 1 zero_le_one le_rfl ∧
    (Proc.ofFun fun _ => Act2.b : Proc Unit (fun _ => Act2) ℚ) = procQ 0 le_rfl zero_le_one := by
  constructor <;>
  · funext d; apply FinDistr.ext'; intro x; cases x <;> simp [Proc.ofFun, procQ, FinDistr.act2]

/-- `mislabelled` is strongly fair (one node).
Source: `zoo.md` ZO-4 (d1) ("strongly fair")
Kind: L -/
theorem mislabelled_stronglyFair : StronglyFair mislabelled := by
  apply StronglyFair.of_injective_pt
  rintro (_ | ⟨a, q⟩) (_ | ⟨a', q'⟩) _
  · rfl
  · cases a' <;> exact q'.elim
  · cases a <;> exact q.elim
  · cases a <;> exact q.elim

/-- `ν` and `𝔼[r 1_X]` on `mislabelled` under `procQ q`. Source: none: infrastructure. Kind: L -/
theorem mislabelled_nu_paySum (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (X : Finset Act2) :
    nu (procQ q h0 h1) mislabelled X =
      (if Act2.b ∈ X then q else 0) + (if Act2.a ∈ X then 1 - q else 0) ∧
    paySum (procQ q h0 h1) mislabelled X = (if Act2.a ∈ X then 1 - q else 0) := by
  constructor
  · rw [nu_eq_sum, mislabelled_sum]
    simp [mislabelled, leafLaw_decision, world_decision, procQ, FinDistr.act2]
  · rw [paySum_eq_sum_ite, mislabelled_sum]
    simp [mislabelled, leafLaw_decision, world_decision, payoff_decision, procQ, FinDistr.act2]

/-- **ZO-4 (d1), `mislabelled`**: strongly fair, pruned, realized, **not recording** (the `a`-edge's
world is `act = b`), `δ_a` D2-consistent (`𝔼_ε[r ∣ act = a] = 1 > 0 = 𝔼_ε[r ∣ act = b]`), and not
optimal (`V(δ_a) = 0 < 1 = V(δ_b)`). Recording's action-veridicality clause is load-bearing in
Theorem 3 on its own.
Source: `zoo.md` ZO-4 (d1); mandate T7(iii)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem mislabelled_eventTremble_not_optimal :
    StronglyFair mislabelled ∧ Pruned mislabelled ∧
    (∀ d ∈ queried mislabelled, Realized actObs mislabelled d) ∧
    ¬ RecordsFor actObs actActEv (Proc.ofFun fun _ => Act2.a) mislabelled () ∧
    EventTrembleEdtConsistent actObs actActEv (Proc.ofFun fun _ => Act2.a) mislabelled ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.a) mislabelled ∧
    value (Proc.ofFun fun _ => Act2.a) mislabelled = 0 := by
  obtain ⟨hpa, hpb⟩ := ofFun_eq_procQ
  refine ⟨?_, ?_, fun d _ => ?_, fun h => ?_, ?_, fun h => ?_, ?_⟩
  · exact mislabelled_stronglyFair
  · rintro ⟨a, _⟩; cases a <;> simp [Positive, mislabelled, chanceWeight_decision, chanceWeight_leaf]
  · exact ⟨⟨.a, ()⟩, by simp [Positive, mislabelled, chanceWeight_decision, chanceWeight_leaf],
      by simp [actObs]⟩
  · have hpos : 0 < leafLaw (Proc.ofFun fun _ => Act2.a) mislabelled ⟨.a, ()⟩ := by
      simp [mislabelled, leafLaw_decision, Proc.ofFun_w]
    have := ((h _ hpos (by simp [actObs])).2 none rfl .a rfl).2.1
    simp [mislabelled, world_decision, actActEv] at this
  · refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a ha => ?_⟩
    cases d
    rw [hpa, tremble_procQ]
    have hn := fun X => (mislabelled_nu_paySum ((1 - ε) * 1 + ε / 2)
      (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).1 (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).2 X).1
    have hp := fun X => (mislabelled_nu_paySum ((1 - ε) * 1 + ε / 2)
      (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).1 (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).2 X).2
    cases a <;> simp [Proc.ofFun_w] at ha
    refine ⟨?_, fun b _ => ?_⟩
    · rw [hn]; simp [actActEv, actObs]; linarith
    · cases b
      · exact le_rfl
      · unfold condExp; rw [hn, hn, hp, hp]; simp [actActEv, actObs]
        exact div_nonneg (by linarith) (by linarith)
  · have := h (Proc.ofFun fun _ => Act2.b)
    rw [hpa, hpb, mislabelled_value, mislabelled_value] at this
    norm_num at this
  · rw [hpa, mislabelled_value]; norm_num

/-- `doppel` is strongly fair (one decision node), pruned, realized.
Source: `zoo.md` ZO-4 (d2)
Kind: L -/
theorem doppel_fair_pruned_realized :
    StronglyFair doppel ∧ Pruned doppel ∧ ∀ d ∈ queried doppel, Realized actObs doppel d := by
  refine ⟨?_, ?_, fun d _ => ?_⟩
  · apply StronglyFair.of_injective_pt
    rintro ⟨i, q⟩ ⟨i', q'⟩ _
    fin_cases i <;> fin_cases i'
    · rcases q with _ | ⟨a, q⟩ <;> rcases q' with _ | ⟨a', q'⟩
      · rfl
      · cases a' <;> exact q'.elim
      · cases a <;> exact q.elim
      · cases a <;> exact q.elim
    · exact q'.elim
    · exact q.elim
    · exact q.elim
  · rintro ⟨i, ℓ⟩
    fin_cases i
    · change 0 < FinDistr.fair.w 0 * chanceWeight doppelL ℓ
      rcases ℓ with ⟨a, _⟩
      cases a <;> simp [chanceWeight_decision, chanceWeight_leaf, doppelL, FinDistr.fair,
        FinDistr.coin]
    · change 0 < FinDistr.fair.w 1 * chanceWeight doppelR ℓ
      simp [chanceWeight_leaf, doppelR, FinDistr.fair, FinDistr.coin]; norm_num
  · refine ⟨⟨1, ()⟩, ?_, by simp [actObs]⟩
    change 0 < FinDistr.fair.w 1 * chanceWeight doppelR ()
    simp [chanceWeight_leaf, doppelR, FinDistr.fair, FinDistr.coin]; norm_num

/-- The three leaves of `doppel`: worlds, laws under `procQ q`, payoffs.
Source: none: infrastructure
Kind: L -/
theorem doppel_leaf_facts (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    world doppel ⟨0, .a, ()⟩ = .a ∧ world doppel ⟨0, .b, ()⟩ = .b ∧ world doppel ⟨1, ()⟩ = .a ∧
    leafLaw (procQ q h0 h1) doppel ⟨0, .a, ()⟩ = 1 / 2 * q ∧
    leafLaw (procQ q h0 h1) doppel ⟨0, .b, ()⟩ = 1 / 2 * (1 - q) ∧
    leafLaw (procQ q h0 h1) doppel ⟨1, ()⟩ = 1 / 2 ∧
    payoff doppel ⟨0, .a, ()⟩ = 0 ∧ payoff doppel ⟨0, .b, ()⟩ = 1 ∧ payoff doppel ⟨1, ()⟩ = 10 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · show FinDistr.fair.w 0 * ((procQ q h0 h1 ()).w Act2.a * 1) = 1 / 2 * q
    simp [FinDistr.fair, FinDistr.coin, procQ]
  · show FinDistr.fair.w 0 * ((procQ q h0 h1 ()).w Act2.b * 1) = 1 / 2 * (1 - q)
    simp [FinDistr.fair, FinDistr.coin, procQ]
  · show FinDistr.fair.w 1 * 1 = 1 / 2
    simp [FinDistr.fair, FinDistr.coin]; norm_num

/-- `ν` and `𝔼[r 1_X]` on `doppel` under `procQ q`. Source: none: infrastructure. Kind: L -/
theorem doppel_nu_paySum (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (X : Finset Act2) :
    nu (procQ q h0 h1) doppel X =
      ((if Act2.a ∈ X then 1 / 2 * q else 0) + (if Act2.b ∈ X then 1 / 2 * (1 - q) else 0)) +
        (if Act2.a ∈ X then 1 / 2 else 0) ∧
    paySum (procQ q h0 h1) doppel X =
      (if Act2.b ∈ X then 1 / 2 * (1 - q) else 0) + (if Act2.a ∈ X then 1 / 2 * 10 else 0) := by
  obtain ⟨w0a, w0b, w1, l0a, l0b, l1, p0a, p0b, p1⟩ := doppel_leaf_facts q h0 h1
  constructor
  · rw [nu_eq_sum, doppel_sum, w0a, w0b, w1, l0a, l0b, l1]
  · rw [paySum_eq_sum_ite, doppel_sum, w0a, w0b, w1, l0a, l0b, l1, p0a, p0b, p1]
    split_ifs <;> ring

/-- **ZO-4 (d2), `doppel`**: strongly fair, pruned, realized, **not recording** (the unconsulted
leaf's world `act = a` satisfies `O = ⊤` with no `d`-node on its path: coverage fails), `δ_a`
D2-consistent (`𝔼_ε[r ∣ act = a] = 5/(1 − ε/4) > 1 = 𝔼_ε[r ∣ act = b]`), and not optimal
(`V(δ_a) = 5 < 11/2 = V(δ_b)`). Recording's coverage clause is load-bearing on its own.
Source: `zoo.md` ZO-4 (d2); mandate T7(iii)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem doppel_eventTremble_not_optimal :
    StronglyFair doppel ∧ Pruned doppel ∧ (∀ d ∈ queried doppel, Realized actObs doppel d) ∧
    ¬ RecordsFor actObs actActEv (Proc.ofFun fun _ => Act2.a) doppel () ∧
    EventTrembleEdtConsistent actObs actActEv (Proc.ofFun fun _ => Act2.a) doppel ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.a) doppel ∧
    value (Proc.ofFun fun _ => Act2.a) doppel = 5 := by
  obtain ⟨hpa, hpb⟩ := ofFun_eq_procQ
  obtain ⟨hf, hp, hr⟩ := doppel_fair_pruned_realized
  refine ⟨hf, hp, hr, fun h => ?_, ?_, fun h => ?_, ?_⟩
  · have hpos : 0 < leafLaw (Proc.ofFun fun _ => Act2.a) doppel ⟨1, ()⟩ := by
      rw [hpa, (doppel_leaf_facts 1 zero_le_one le_rfl).2.2.2.2.2.1]; norm_num
    have := (h _ hpos (by simp [actObs])).1
    change count () doppelR () = 1 at this
    simp [doppelR, count_leaf] at this
  · refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a ha => ?_⟩
    cases d
    rw [hpa, tremble_procQ]
    have hn := fun X => (doppel_nu_paySum ((1 - ε) * 1 + ε / 2)
      (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).1 (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).2 X).1
    have hp := fun X => (doppel_nu_paySum ((1 - ε) * 1 + ε / 2)
      (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).1 (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).2 X).2
    cases a <;> simp [Proc.ofFun_w] at ha
    refine ⟨?_, fun b _ => ?_⟩
    · rw [hn]; simp [actActEv, actObs]; linarith
    · cases b
      · exact le_rfl
      · unfold condExp; rw [hn, hn, hp, hp]; simp [actActEv, actObs]
        have hb : (0 : ℚ) < 2⁻¹ * (1 - (1 - ε + ε / 2)) := by linarith
        have hd : (0 : ℚ) < 2⁻¹ * (1 - ε + ε / 2) + 2⁻¹ := by linarith
        rw [div_le_div_iff₀ hb hd]
        nlinarith
  · have := h (Proc.ofFun fun _ => Act2.b)
    rw [hpa, hpb, doppel_value, doppel_value] at this
    norm_num at this
  · rw [hpa, doppel_value]; norm_num

end zo4

/-! ### (iv) No realized observation: A.1's node -/

section a1

/-- `a1Node` is strongly fair (one node), pruned (no chance), records at its point for every
procedure **vacuously** (no leaf-world satisfies `O_d`), and its observation is **not** realized.
Source: `adversary-repair.md` A.1 ("`B` records at `d` for every procedure … vacuously");
`zoo.md` ZO-2 (witness off "realized")
Kind: N− (vacuous by design) -/
theorem a1Node_hyps :
    StronglyFair a1Node ∧ Pruned a1Node ∧ RecordsForAll a1Obs a1ActEv a1Node () ∧
    ¬ Realized a1Obs a1Node () := by
  refine ⟨?_, ?_, fun C ℓ _ hobs => ?_, fun ⟨ℓ, _, hobs⟩ => ?_⟩
  · apply StronglyFair.of_injective_pt
    rintro (_ | ⟨a, q⟩) (_ | ⟨a', q'⟩) _
    · rfl
    · cases a' <;> exact q'.elim
    · cases a <;> exact q.elim
    · cases a <;> exact q.elim
  · rintro ⟨a, _⟩; cases a <;> simp [Positive, a1Node, chanceWeight_decision, chanceWeight_leaf]
  · exfalso
    unfold a1Node at ℓ hobs
    rcases ℓ with ⟨a, _⟩
    simp [a1Obs, world_decision] at hobs
  · unfold a1Node at ℓ hobs
    rcases ℓ with ⟨a, _⟩
    simp [a1Obs, world_decision] at hobs

/-- Values on `a1Node`: `V(δ_a) = 0`, `V(δ_b) = 1`.
Source: `adversary-repair.md` A.1
Kind: L -/
theorem a1Node_values :
    value (Proc.ofFun fun _ => Act2.a) a1Node = 0 ∧ value (Proc.ofFun fun _ => Act2.b) a1Node = 1 := by
  constructor <;>
  · unfold value a1Node
    rw [sum_leaves_decision, Act2.sum_univ]
    simp [Tree.sum_leaves_leaf, leafLaw_decision, payoff_decision, Proc.ofFun_w]
    all_goals rfl

/-- **T7(iv), no realized observation — A.1's kill of FR-11 as first stated (refuted row)**:
`a1Node` with `δ_a` is strongly fair, records at `d` for every procedure, is pruned, and is
event-tremble-EDT-consistent **because the D2 guard `nuPoly O_d ≠ 0` fails** (equivalently the
escape clause fires: no action event is realized within `O_d` under any `C^ε`), yet `V = 0 < 1`.
Quoted (fair-repair.md l. 95): "Let `B` be strongly fair and fully recorded (FRec; EC where
observations are chance-determined), all chance edges of positive probability … Let `C` be
tremble-EDT-consistent … Then `V_B(C) = max_{C'} V_B(C')`." Reading: FR-11 with the hypothesis
list as first stated (no realized-observation clause). Surviving neighbour: A36's Theorem 3
(`eventTrembleEdt_isOptimal_of_fairClass`), whose clause (O) this tree fails.
FR-11's own device ("for every small `ε` a state assignment making `B` strictly OC for `C^ε`
with `T_EDT(C, B_ε)`", states free) approves `δ_a` for the parallel reason — the state at the
null observation is free, A.1's construction — `a1Node_fr11_device`; and D3
(`OccTrembleEdtConsistent`, no escape clause) **rejects** `δ_a` here, `a1Node_not_occTremble`:
A.1's hole is device-relative (findings F14).
Source: `adversary-repair.md` A.1 ("The theorem as stated is false; the hole is queried points
whose observation is realized by no leaf-world"); `zoo.md` ZO-2; dp-cf-034 item 1
Kind: N+ (the refutation instance; the D2 verdict itself is vacuous by design)
Fidelity: exact
Hyps: (a) all -/
theorem a1Node_eventTremble_not_optimal :
    StronglyFair a1Node ∧ Pruned a1Node ∧ RecordsForAll a1Obs a1ActEv a1Node () ∧
    ¬ Realized a1Obs a1Node () ∧
    EventTrembleEdtConsistent a1Obs a1ActEv (Proc.ofFun fun _ => Act2.a) a1Node ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.a) a1Node ∧
    value (Proc.ofFun fun _ => Act2.a) a1Node = 0 := by
  obtain ⟨hf, hp, hrec, hnr⟩ := a1Node_hyps
  refine ⟨hf, hp, hrec, hnr, ⟨1, one_pos, fun ε _ _ _ d _ hguard => ?_⟩, fun h => ?_,
    a1Node_values.1⟩
  · cases d
    exact absurd (a1_nuPoly_obs_eq_zero _) hguard
  · have := h (Proc.ofFun fun _ => Act2.b)
    rw [a1Node_values.1, a1Node_values.2] at this
    norm_num at this

/-- **FR-11's own device approves `δ_a` on `a1Node`** (A.1's construction, machine-checked): for
every `ε ∈ (0, 1]` the point mass on the world `(false, a)` with constant desirability is
strict-OC for `δ_a^ε` (vacuously: `ν_ε(O_d) = 0`, the point is unconstrained) and
`T_EDT`-approves `δ_a`. So the refutation of FR-11 as first stated does not depend on D2's
escape clause: the letter of FR-11 fails with its own device too.
Source: `adversary-repair.md` A.1 ("stipulate a state with `P` certain of `(false, a)`");
`fair-repair.md` l. 95 (the device); audit round 1 probe P4
Kind: N+ -/
theorem a1Node_fr11_device (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ∃ s : Unit → State A1W ℚ,
      StrictOC s a1Obs (tremble (Proc.ofFun fun _ => Act2.a) ε h0.le h1) a1Node ∧
      TEdt s a1ActEv (Proc.ofFun fun _ => Act2.a) a1Node := by
  refine ⟨fun _ => State.ofConst (FinDistr.pure (false, Act2.a)) 7, ?_, ?_⟩
  · intro d _ hpos
    exfalso
    cases d
    rw [← eval_nuPoly _ _ _ ε h0.le h1, a1_nuPoly_obs_eq_zero] at hpos
    simp at hpos
  · intro d _ _ a ha
    cases d
    cases a <;> simp [Proc.ofFun_w] at ha
    rw [mem_argmaxPlus]
    refine ⟨?_, fun b _ => by simp [State.ofConst]⟩
    simp [APlus, State.pr, State.ofConst, probOf_pure, a1ActEv]

/-- **D3 rejects `δ_a` on `a1Node`**: the occurrence-weighted device (`OccTrembleEdtConsistent`,
no guard and no escape clause) compares `fiberForced(b) = 1 > 0 = fiberForced(a)` at every
`ε`. So clause (O) is load-bearing for D2 and for FR-11's device, but not for D3 on this
example — A.1's hole is device-relative, and `a1Node` is where D2 and D3 part off `𝔉`
(`FairClass.eventTremble_iff_occTremble` is the on-`𝔉` identification).
Source: `calibration.md` D3; audit round 1 probe P5; findings F14
Kind: N+ -/
theorem a1Node_not_occTremble :
    ¬ OccTrembleEdtConsistent (Proc.ofFun fun _ => Act2.a) a1Node := by
  rintro ⟨ε₀, hε₀, hD3⟩
  have hq : (() : Unit) ∈ queried a1Node := pt_mem_queried a1Node none
  have := hD3 (min (ε₀ / 2) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)
    ((min_le_left _ _).trans_lt (by linarith)) () hq .a (by simp [Proc.ofFun_w]) .b
  rw [fiberForced_eq_siaSum, fiberForced_eq_siaSum] at this
  unfold a1Node at this
  rw [siaSum_decision_self, siaSum_decision_self] at this
  simp [DpLocalOpt.value_leaf] at this
  exact absurd this (by norm_num)

end a1

/-! ### Claim 3.2 as stated is refuted (T16(a)) -/

section claim32

/-- On `mislabelled` (`O = ⊤`), Proposition 3's hypothesis `H_d` (coverage and
a.s. subtree-veridicality at every `d`-node — v2 Proposition 3, l. 134: "every `d`-node is
subtree-veridical and `B` covers `d`") holds for every procedure. This is `dp-calibration`'s `H_d`
(`zo2_chain`'s hypothesis), **not** `dp-core-tree`'s recording-inclusive `HStar`, which
`mislabelled` fails (`mislabelled_eventTremble_not_optimal`'s `¬ RecordsFor`).
Source: [[decision-problems-v2]] Proposition 3 (l. 134); `fable-slop-notes.md` Claim 3.2
("Proposition 3's hypotheses at every point")
Kind: L -/
theorem mislabelled_hd (C : Proc Unit (fun _ => Act2) ℚ) :
    Covers actObs C mislabelled () ∧
    ∀ q : mislabelled.DecNode, pt mislabelled q = () → SubtreeVeridicalAS actObs C mislabelled q := by
  refine ⟨fun ℓ _ _ => ?_, fun q _ ℓ _ _ => by simp [actObs]⟩
  unfold mislabelled at ℓ ⊢
  rcases ℓ with ⟨a, _⟩
  cases a <;> simp [count_decision, count_leaf]

/-- **Claim 3.2 as stated is refuted** (rule 3). Quoted (fable-slop-notes.md l. 65): "Let `B` be
strongly fair with veridical labelling (Proposition 3's hypotheses at every point), and let `C` be
deterministic and tremble-consistent with respect to `T_EDT` (Remark 3.12). Then `C` is
`V`-optimal." Reading (ATTRIBUTION-UNVETTED — the sentence's parenthetical pins "veridical
labelling" to Proposition 3's hypotheses, and that reading is formalised; read instead as
*act-veridical leaf labels*, Definition 7's "action-veridical", the sentence excludes
`mislabelled` and is wounded only by A.1's `a1Node_eventTremble_not_optimal`): Proposition 3's
hypotheses = `H_d` (coverage + a.s. subtree-veridicality, v2 l. 134) at every queried point; the
device = D2 on the concrete tree. Witness: `mislabelled` — strongly fair, `H_d` for every
procedure (`O = ⊤`), `δ_a` deterministic and D2-consistent, `V = 0 < 1`. The hypothesis Claim 3.2
names is weaker than Definition 7 recording (it lacks the action clauses) and does not suffice;
surviving neighbour: Theorem 3 with `FRec` (and "deterministic" is unnecessary there).
Source: `fable-slop-notes.md` Claim 3.2 (l. 65); `zoo.md` ZO-4 (d1); dp-core-069; mandate
T16(a)
Kind: N+ (refutation instance)
Fidelity: exact
Hyps: (a) all -/
theorem claim32_refuted :
    StronglyFair mislabelled ∧
    (∀ C : Proc Unit (fun _ => Act2) ℚ, Covers actObs C mislabelled () ∧
      ∀ q : mislabelled.DecNode, pt mislabelled q = () → SubtreeVeridicalAS actObs C mislabelled q) ∧
    Proc.IsDeterministic (Proc.ofFun fun _ => Act2.a : Proc Unit (fun _ => Act2) ℚ) ∧
    EventTrembleEdtConsistent actObs actActEv (Proc.ofFun fun _ => Act2.a) mislabelled ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.a) mislabelled := by
  obtain ⟨hf, -, -, -, hD2, hnot, -⟩ := mislabelled_eventTremble_not_optimal
  exact ⟨hf, mislabelled_hd, fun _ => ⟨.a, rfl⟩, hD2, hnot⟩

end claim32

end Cleanroom.Decision.DpEdtUdtFair
