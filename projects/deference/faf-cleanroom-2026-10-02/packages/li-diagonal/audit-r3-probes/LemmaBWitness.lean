import Cleanroom.Li.LiDiagonal.Forcing

/-!
# `li-diagonal` · audit round 3 · adversarial lens · probe: Lemma B's certificates are inhabitable

**Not imported by the library.** Evidence for `li-diagonal-audit-r3-adversarial.md`.

The ledger rows for `lemmaB`, `lemmaB_quarter`, `lemmaB_expect` and `lemmaB_expect_quarter` are
`flagged: no inhabitant of hR/hR' exhibited`, and the handoff (item 8) asks for "a pair with a
`UnaryRuler`-computable side". The adversarial question is whether the cost-model certificates
`hR : MachineSentenceCodes (padTrueSide pair.a f)` and `hR'` could be jointly *uninhabitable* for
every `OneWayPair` — which would make Lemma B vacuous. They are not. This file builds a
`OneWayPair` whose posted table flips every day (`0` on odd days, `1` on even days), so the side
`s_n = 𝟙[a_n ≤ ½]` takes both values infinitely often, and discharges `hR`, `hR'` at
`succDeferral` from `gDiag_codes` by FAF's `MachineSentenceCodes.ifZero` on the parity ruler.
`lemmaB` and `lemmaB_expect` then apply with no remaining hypothesis.

What is degenerate and what is not. The reader `H` is FAF's genuine LIA over the ledger process
of `paperDP 𝗜𝚺₁` (every reader-side field is the package's own, as in `paperOneWayPair`), and the
side it must track is not eventually constant — Lemma B's own content ("`H` learns the posted
side by day `n+1`") is exercised, so for the one-way statement this is an **N+** inhabitant. The
fixed market `A` is a dead inductor: a constant-per-day history over a contradictory process,
where FAF's criterion holds vacuously (`isLogicalInductor_of_stage_unsatisfiable`, `thm:scon`; the
same device as li-quote-lane's audit-r2 probe `AdvR2OneWayDegenerateA.lean`). Lemma B never uses
`A_inductor`, so this costs it nothing; for anything two-way (a `DiagonalPair`) the pair would be
N−, and `DiagonalPair`'s inhabitation stays `li-coupled-pair`'s OPEN as the package says.
-/

namespace Cleanroom.Li.LiDiagonal.AuditR3Adv

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Bli.BliFound
open Filter Topology

/-! ## A contradictory computable process for the dead fixed market -/

/-- A process every stage of which holds `⊤` and `∼⊤`: no world is consistent with it. -/
def botBase : DeductiveProcess where
  D _ := {(⊤ : Sentence), ∼ (⊤ : Sentence)}
  mono _ := Finset.Subset.refl _

/-- `botBase` is a computable deductive process (a constant stage). -/
theorem botBase_computable : ComputableDeductiveProcess botBase := by
  have hc : Computable fun s : ℕ => Encodable.encode (botBase.D s) :=
    (Computable.const (Encodable.encode (botBase.D 0))).of_eq fun _ => rfl
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc.partrec)
  exact ⟨code, fun s => by rw [hcode]; simp⟩

/-- No world is consistent with stage `0` of `botBase`. -/
theorem botBase_no_world (v : PCWorld) : ¬ v.ConsistentWith (botBase.D 0) := by
  intro hv
  have h1 : v.Holds (⊤ : Sentence) := hv _ (by simp [botBase])
  have h2 : v.Holds (∼ (⊤ : Sentence)) := hv _ (by simp [botBase])
  rw [PCWorld.holds_neg] at h2
  exact h2 h1

/-! ## The posted table: a side that flips every day -/

/-- The posted table: `0` on odd days, `1` on even days (item index ignored). -/
def parityTable (_j n : ℕ) : ℚ := if (n + 1) % 2 = 0 then 0 else 1

theorem parityTable_mem (j n : ℕ) : 0 ≤ parityTable j n ∧ parityTable j n ≤ 1 := by
  unfold parityTable; split_ifs <;> norm_num

theorem parityTable_computable : Computable fun p : ℕ × ℕ => parityTable p.1 p.2 := by
  have hmod : Primrec fun p : ℕ × ℕ => (p.2 + 1) % 2 :=
    Primrec.nat_mod.comp (Primrec.succ.comp Primrec.snd) (Primrec.const 2)
  have hpred : PrimrecPred fun p : ℕ × ℕ => (p.2 + 1) % 2 = 0 :=
    Primrec.eq.comp hmod (Primrec.const 0)
  exact ((Primrec.ite hpred (Primrec.const (0 : ℚ)) (Primrec.const 1)).to_comp).of_eq fun p => by
    simp [parityTable]

/-- The dead fixed market: quotes the posted number for every sentence. -/
noncomputable def parityA : History := fun n _ => (parityTable 0 n : ℝ)

theorem parityA_computableMarket : ComputableMarket parityA := by
  refine ⟨fun n φ => ?_, fun n _ => parityTable 0 n, ?_⟩
  · show (0 : ℝ) ≤ (parityTable 0 n : ℝ) ∧ (parityTable 0 n : ℝ) ≤ 1
    exact ⟨by exact_mod_cast (parityTable_mem 0 n).1, by exact_mod_cast (parityTable_mem 0 n).2⟩
  · have hmod : Primrec fun n : ℕ => (n + 1) % 2 :=
      Primrec.nat_mod.comp Primrec.succ (Primrec.const 2)
    have hpred : PrimrecPred fun n : ℕ => (n + 1) % 2 = 0 :=
      Primrec.eq.comp hmod (Primrec.const 0)
    have h1 : Computable fun n : ℕ => parityTable 0 n :=
      ((Primrec.ite hpred (Primrec.const (0 : ℚ)) (Primrec.const 1)).to_comp).of_eq fun n => by
        simp [parityTable]
    have hc : Computable fun z : ℕ => Encodable.encode (parityTable 0 z.unpair.1) :=
      Computable.encode.comp (h1.comp (Computable.fst.comp Computable.unpair))
    obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc.partrec)
    exact ⟨code, fun _ _ => rfl, fun z => by rw [hcode]; simp⟩

/-! ## The pair -/

/-- **A `OneWayPair` with a daily-flipping posted side.** Reader side: FAF's LIA over the ledger
process of `paperDP 𝗜𝚺₁` reading `parityTable` on the `succ` schedule (every field the package's
own). Fixed market: `parityA` over the contradictory `botBase`, an inductor by `thm:scon`. -/
noncomputable def parityPair : OneWayPair where
  DPA := botBase
  DPH := paperDP 𝗜𝚺₁
  quoted := fun _ _ => ⊤
  e := fun _ => PublicationSchedule.succ
  A := parityA
  H := liaHistory (ledgerProcess (paperDP 𝗜𝚺₁) parityTable (fun _ => PublicationSchedule.succ))
  a := parityTable
  a_eq := fun _ _ => rfl
  A_inductor := isLogicalInductor_of_stage_unsatisfiable parityA botBase parityA_computableMarket
    botBase_computable (N := 0) botBase_no_world
  H_inductor := LIA_is_logical_inductor _
    (ledgerProcess_computable (paperDP_computable 𝗜𝚺₁) parityTable_computable
      succSchedule_computable)
  hworld := ledgerProcess_hworld
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁)
  determined := fun j n => ledgerLuv_determinedVia _ parityTable _ parityTable_mem j n

/-- The side flips: `1` on every odd day. -/
theorem parityPair_side_one_frequently : ∃ᶠ n in atTop, side (parityPair.a 0) n = 1 := by
  rw [Filter.frequently_atTop]
  intro a
  refine ⟨2 * a + 1, by omega, ?_⟩
  rw [side_eq_one_iff]
  show parityTable 0 (2 * a + 1) ≤ 1 / 2
  unfold parityTable
  rw [if_pos (by omega)]
  norm_num

/-- The side flips: `0` on every even day. -/
theorem parityPair_side_zero_frequently : ∃ᶠ n in atTop, side (parityPair.a 0) n = 0 := by
  rw [Filter.frequently_atTop]
  intro a
  refine ⟨2 * a, by omega, ?_⟩
  rw [side_eq_zero_iff]
  show (1 / 2 : ℚ) < parityTable 0 (2 * a)
  unfold parityTable
  rw [if_neg (by omega)]
  norm_num

/-! ## The cost-model certificates at `succDeferral` -/

/-- The padded true side along `succ`: `⊤` on day `0`, then `g_{m−1}` on even days and
`∼g_{m−1}` on odd days. -/
theorem parityPair_padTrueSide (m : ℕ) : padTrueSide parityPair.a succDeferral m =
    if m = 0 then ⊤ else if m % 2 = 0 then gDiag (m - 1) else ∼ gDiag (m - 1) := by
  cases m with
  | zero =>
    unfold padTrueSide
    rw [dif_neg, if_pos rfl]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    have h := padTrueSide_apply parityPair.a succDeferral (fun _ _ hab => Nat.succ_injective hab) k
    refine h.trans ?_
    show (if parityTable 0 k ≤ 1 / 2 then gDiag k else ∼ gDiag k) = _
    unfold parityTable
    by_cases h : (k + 1) % 2 = 0
    · rw [if_pos h, if_pos h, if_pos (by norm_num)]
    · rw [if_neg h, if_neg h, if_neg (by norm_num)]

/-- The padded false side along `succ`: `∼⊤` on day `0`, then `∼g_{m−1}` on even days and
`g_{m−1}` on odd days. -/
theorem parityPair_padFalseSide (m : ℕ) : padFalseSide parityPair.a succDeferral m =
    if m = 0 then ∼ (⊤ : Sentence) else if m % 2 = 0 then ∼ gDiag (m - 1) else gDiag (m - 1) := by
  cases m with
  | zero =>
    unfold padFalseSide
    rw [dif_neg, if_pos rfl]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    have h := padFalseSide_apply parityPair.a succDeferral
      (fun _ _ hab => Nat.succ_injective hab) k
    refine h.trans ?_
    show (if parityTable 0 k ≤ 1 / 2 then ∼ gDiag k else gDiag k) = _
    unfold parityTable
    by_cases h : (k + 1) % 2 = 0
    · rw [if_pos h, if_pos h, if_pos (by norm_num)]
    · rw [if_neg h, if_neg h, if_neg (by norm_num)]

/-- **`hR` discharged**: the padded true side is e.c. (`ifZero` on the day being `0`, then
`ifZero` on parity, from `gDiag_codes`). -/
theorem parityPair_hR : MachineSentenceCodes (padTrueSide parityPair.a succDeferral) := by
  have hpred : UnaryRuler (fun m : ℕ => m - 1) := UnaryRuler.id.sub (UnaryRuler.const 1)
  have hmod : UnaryRuler (fun m : ℕ => m % 2) :=
    (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two
  have hg : MachineSentenceCodes (fun m : ℕ => gDiag (m - 1)) :=
    MachineSentenceCodes.comp gDiag_codes hpred
  have hng : MachineSentenceCodes (fun m : ℕ => ∼ gDiag (m - 1)) :=
    MachineSentenceCodes.comp gDiag_codes.neg hpred
  have hinner : MachineSentenceCodes
      (fun m : ℕ => if m % 2 = 0 then gDiag (m - 1) else ∼ gDiag (m - 1)) :=
    MachineSentenceCodes.ifZero hg hng hmod
  have htop : MachineSentenceCodes (fun _ : ℕ => (⊤ : Sentence)) :=
    MachineSentenceCodes.const (⊤ : Sentence)
  refine MachineSentenceCodes.of_eq (MachineSentenceCodes.ifZero htop hinner UnaryRuler.id)
    fun m => ?_
  simp only [parityPair_padTrueSide]

/-- **`hR'` discharged**: the padded false side is e.c. -/
theorem parityPair_hR' : MachineSentenceCodes (padFalseSide parityPair.a succDeferral) := by
  have hpred : UnaryRuler (fun m : ℕ => m - 1) := UnaryRuler.id.sub (UnaryRuler.const 1)
  have hmod : UnaryRuler (fun m : ℕ => m % 2) :=
    (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two
  have hg : MachineSentenceCodes (fun m : ℕ => gDiag (m - 1)) :=
    MachineSentenceCodes.comp gDiag_codes hpred
  have hng : MachineSentenceCodes (fun m : ℕ => ∼ gDiag (m - 1)) :=
    MachineSentenceCodes.comp gDiag_codes.neg hpred
  have hinner : MachineSentenceCodes
      (fun m : ℕ => if m % 2 = 0 then ∼ gDiag (m - 1) else gDiag (m - 1)) :=
    MachineSentenceCodes.ifZero hng hg hmod
  have hbot : MachineSentenceCodes (fun _ : ℕ => ∼ (⊤ : Sentence)) :=
    MachineSentenceCodes.const (∼ (⊤ : Sentence))
  refine MachineSentenceCodes.of_eq (MachineSentenceCodes.ifZero hbot hinner UnaryRuler.id)
    fun m => ?_
  simp only [parityPair_padFalseSide]

/-! ## Lemma B, inhabited -/

/-- **Lemma B on the parity pair, no hypotheses**: the reader's day-`(n+1)` price of `g_n` tracks
a side that flips every day. -/
theorem lemmaB_parityPair :
    Tendsto (fun n => |parityPair.H (succDeferral n) (gDiag n) - side (parityPair.a 0) n|)
      atTop (𝓝 0) :=
  lemmaB parityPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    parityPair_hR parityPair_hR'

/-- **Lemma B's expectation form on the parity pair, no hypotheses** (`hG` is
`padG_codes_succ`). -/
theorem lemmaB_expect_parityPair :
    Tendsto (fun n => |(LUV.indicatorOf (gDiag n)).expect parityPair.H (succDeferral n) -
      side (parityPair.a 0) n|) atTop (𝓝 0) :=
  lemmaB_expect parityPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    parityPair_hR parityPair_hR' padG_codes_succ

end Cleanroom.Li.LiDiagonal.AuditR3Adv
