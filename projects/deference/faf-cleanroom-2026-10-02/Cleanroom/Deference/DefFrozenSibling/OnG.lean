import Cleanroom.Deference.DefFrozenSibling.OffG
import Cleanroom.Deference.DefFrozenSibling.Engine
import Cleanroom.Deference.DefFrozenSibling.Limits
import Cleanroom.Deference.DefFrozenSibling.Value
import Cleanroom.Deference.DefFrozenSibling.Misc

/-!
# `def-frozen-sibling` · OnG: the one-way inhabitant at a timely day (N+ for the on-`G` suite)

The counter-model of `OffG.lean` with the lag set to `0` and the diagonal set to the truth: the
contract atoms are decided in the shared process at stage `n` (before the horizon `F n = n + 1`),
alternating; every sibling is FAF's LIA on its frozen process **perturbed at `(F n, contract n)` to
the decided value** (an inductor by `thm:ifp`, `perturbAt_inductor`); the diagonal `Y n :=
truthAt n ∈ {0,1}` is non-constant; `A` and `Hplus` are FAF's LIAs over their ledger processes.
Every day is timely at tolerance `0` (`onG_timely`), so the on-`G` theorems are instantiated at
the trivial ruler `t ≡ 0`: `engineA_onG` (T3's A-side at grade (a): FAF's LIA's expectation of the
contract settled to the truth value agrees with its own price of the decided proposition),
`limit_agree_onG_onG` (T7 exact). One-way: `Y` is a given table, no joint fixed point. The
tolerance clause is exercised at `ε ≡ 0` by the perturbation (the mandate's N− "`ε ≡ 1`, the
tolerance clause idle" is improved to an exact verdict), but the perturbed sibling is *pinned* to
the truth at the horizon rather than *reaching* it — the diagonal convergence of an unperturbed
family is the OPEN `timely_cofinite_const` (findings F3). Heavy module (imports `OffG`).

**§E — the `hz` clause at the inhabitant** (repair round 1, audit r1 adversarial B3 (iii)): the
alternating table `Y0` is a `MachineRatCodes` (`Y0_machineRatCodes`: the parity flag is a
`UnaryRuler` by `UnaryRuler.ifZero` on `MachineDigits.mod_two`, the numerator code is `2·flag`),
hence `PGenerableRat onGSystem.A Y0` (`hz_onG`), and every `hz`-row of the package has its one-way
N+ at the inhabitant with `zhat := Y0`, `t ≡ 0`, `ε ≡ 0`: `tracking_onG`, `metaTrust_onG`,
`metaTrust_expect_onG`, `engineA_truth_onG`, `condTower_onG_onG`, `valueTwoOption_onG_onG`,
`thresholdAbove_onG_onG`, `valueConst_onG_onG`, `calibration_onG_degenerate_onG`. **Regime
caveat** (findings F4, audit r1 N5): at `onGSystem` the polarity pattern is even/odd, which is
e.c., so these witnesses live where `engineA_truth_ofPattern` would also reach the truth without
the quote — they inhabit the statements' full hypothesis packages (N+), not the regime where the
quote is load-bearing (a non-e.c. pattern). That the inhabitant is in the quote-redundant regime
is machine-checked in §G (`hpat₁_onG`, `hpat₀_onG`, `engineA_truth_onG_noHz`); whether an
explicit computable witness can exhibit the other regime is **open**, not excluded (audit r2
adversarial N4: `hz` is a price-reading feature, `hpat` an FP function of the day, and no theorem
turns one into the other).

**§G — the inhabitants and the pinned OPEN rows, read closely** (repair round 2): `antiSystem`'s
"timely nowhere" is tolerance-relative (`anti_timely_iff : Timely antiSystem ε n ↔ 1 ≤ ε n`); at
the pins of `timely_cofinite_const` / `timely_not_mono_open` every day is decided with decided
value `Y0` (`pinned_base0_decided`, `pinned_base0_decided'`), so the first OPEN is diagonal
convergence `S.Y − Y0 → 0` (`cofinite_const_iff`) and the second a one-day strict comparison
(`notMono_tol_iff`); and the diagonal property at those pins yields the whole on-`G` package at
`t ≡ 0` (`engineA_of_diagonal`, through `timely_all_of_diagonal`).

**§F — the anti-truth sibling** (repair round 1, audit r1 adversarial B1): the same construction
with the sibling pinned at the horizon to the *wrong* value (`antiSystem`, `Y1 := 1 − Y0`). Same
shared process, contracts and schedules as `onGSystem`, no day timely at tolerance `0`
(`anti_not_timely`). So the tolerance clause of `Timely` is not a function of the shared process,
the contracts and the horizon (`timely_not_horizon_only`): the mandate's T13 implication
`Timely S ε n → Timely S' ε n` over the free carrier is **false** even at `F' = F`, because the
sibling family is a free field. The question with content — whether FAF's *unperturbed* LIA
family can lose a timely day to a strictly later horizon — is the OPEN `timely_not_mono_open`
(`OffG.lean` §F, restated in repair round 1).
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair
open Filter Topology

/-! ## A. The lag-`0` shared process -/

/-- `mem_enum0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_enum0 {s : ℕ} {x : ℕ × ℕ × Bool} :
    x ∈ enum0 s ↔ ∃ n, n < s + 1 ∧ (contractFamily, Nat.pair n 0, decide (n % 2 = 0)) = x := by
  simp [enum0, List.mem_map, List.mem_range]

/-- The lag-`0` contract schedule (day `n` adjoined at stage `n`).
Source: mandate D2 (non-vacuity witness)
Kind: D
Fidelity: n/a -/
def contractSchedule0 : LiteralSchedule := LiteralSchedule.ofList enum0 enum0_mono

/-- `contractSchedule0_functional`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma contractSchedule0_functional : contractSchedule0.Functional := by
  rintro s f p ⟨h1, h2⟩
  rw [contractSchedule0, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum0] at h1 h2
  obtain ⟨n, -, hn⟩ := h1
  obtain ⟨m, -, hm⟩ := h2
  simp only [Prod.mk.injEq] at hn hm
  obtain ⟨-, hp1, hb1⟩ := hn
  obtain ⟨-, hp2, hb2⟩ := hm
  rw [← hp2, Nat.pair_eq_pair] at hp1
  rw [hp1.1] at hb1
  rw [hb1] at hb2
  exact Bool.noConfusion hb2

/-- `enum0_primrec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enum0_primrec : Primrec enum0 := by
  have hg : Primrec₂ fun (_ n : ℕ) => (contractFamily, Nat.pair n 0, decide (n % 2 = 0)) :=
    (Primrec.const contractFamily).pair
      ((Primrec₂.natPair.comp Primrec.snd (Primrec.const 0)).pair
        (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
          (Primrec.const 0)).decide)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.succ) hg

/-- `base0` is `extendBy (paperDP 𝗜𝚺₁) contractSchedule0`, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base0_eq : base0 = extendBy (paperDP 𝗜𝚺₁) contractSchedule0 := rfl

/-- `base0_computable`.
Source: none: infrastructure
Kind: C
Fidelity: n/a -/
theorem base0_computable : ComputableDeductiveProcess base0 :=
  extendBy_ofList_computable (paperDP_computable 𝗜𝚺₁) enum0 enum0_mono enum0_primrec

/-- `base0_hworld`.
Source: none: infrastructure
Kind: C
Fidelity: n/a -/
theorem base0_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (base0.D n) :=
  extendBy_hworld contractSchedule0_functional
    (ProcessFreeOf.of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) _) (paperDP_hworld 𝗜𝚺₁)

/-- `base0_tagFree`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base0_tagFree {t : ℕ} (h9 : cleanroomBaseTag ≤ t)
    (h16 : t ≠ cleanroomBaseTag + contractFamily) : TagFreeProcess t base0 := by
  intro k φ hφ
  rw [base0_eq, extendBy_D, Finset.mem_union] at hφ
  rcases hφ with h | h
  · exact paperDP_tagFree 𝗜𝚺₁ h9 k φ h
  · rw [Finset.mem_image] at h
    obtain ⟨x, hx, rfl⟩ := h
    rw [contractSchedule0, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum0] at hx
    obtain ⟨n, -, rfl⟩ := hx
    by_cases hn : n % 2 = 0
    · simp only [hn, decide_true, literalOf_true]
      exact freshAtom_tagFree_of_ne h16
    · simp only [hn, decide_false, literalOf_false]
      exact (freshAtom_tagFree_of_ne h16).neg

/-- `base0_freeOf_ledger`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base0_freeOf_ledger (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ProcessFreeOf (ledgerSchedule a e) base0 :=
  ProcessFreeOf.of_tagFree fun f hf => by
    rw [ledgerSchedule_families a e f hf]
    exact base0_tagFree (by simp [cleanroomBaseTag, ledgerFamily])
      (by simp [cleanroomBaseTag, ledgerFamily, contractFamily])

/-- Even days: the contract is in stage `n` (hence in stage `n + 1`, the horizon).
Source: mandate D2
Kind: L
Fidelity: n/a -/
theorem contract0_mem_of_even (n : ℕ) (hn : n % 2 = 0) : contract5 n ∈ base0.D n := by
  rw [base0_eq, extendBy_D]
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨(contractFamily, Nat.pair n 0, true), ?_, by simp [contract5]⟩
  rw [contractSchedule0, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum0]
  exact ⟨n, by omega, by simp [hn]⟩

/-- Odd days: the contract's negation is in stage `n`.
Source: mandate D2
Kind: L
Fidelity: n/a -/
theorem contract0_neg_mem_of_odd (n : ℕ) (hn : n % 2 = 1) : ∼contract5 n ∈ base0.D n := by
  rw [base0_eq, extendBy_D]
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨(contractFamily, Nat.pair n 0, false), ?_, by simp [contract5]⟩
  rw [contractSchedule0, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum0]
  exact ⟨n, by omega, by simp [hn]⟩

/-- Odd days: the contract itself is in **no** stage of `base0` (FAF's `paperDP` never mentions
it; the schedule adjoins its negation).
Source: mandate D2
Kind: L
Fidelity: n/a -/
theorem contract0_not_mem_of_odd (n : ℕ) (hn : n % 2 = 1) (k : ℕ) : contract5 n ∉ base0.D k := by
  intro h
  rw [base0_eq, extendBy_D, Finset.mem_union, Finset.mem_image] at h
  rcases h with h | ⟨x, hx, hxe⟩
  · exact (contract5_not_mem_paper n k).1 h
  · rw [contractSchedule0, LiteralSchedule.ofList_lits, List.mem_toFinset, mem_enum0] at hx
    obtain ⟨m, -, rfl⟩ := hx
    by_cases h2 : m % 2 = 0
    · simp only [h2, decide_true, literalOf_true] at hxe
      rw [contract5, freshAtom_inj, Nat.pair_eq_pair] at hxe
      omega
    · simp only [h2, decide_false, literalOf_false] at hxe
      exact atom_ne_neg _ _ hxe.symm

/-! ## B. The markets: the truth table, the predictor, the advised reasoner, the perturbed siblings -/

/-- The truth table: `1` on even days, `0` on odd days.
Source: mandate D2 ("alternating polarity")
Kind: D
Fidelity: n/a -/
def Y0 (n : ℕ) : ℚ := if n % 2 = 0 then 1 else 0

/-- `Y0_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Y0_computable : Computable Y0 := by
  have hc : Computable fun n : ℕ => decide (n % 2 = 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).decide.to_comp
  refine (Computable.cond hc (Computable.const (1 : ℚ)) (Computable.const (0 : ℚ))).of_eq
    fun n => ?_
  simp only [Y0]
  by_cases h : n % 2 = 0 <;> simp [h]

/-- `Y0_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Y0_mem (n : ℕ) : 0 ≤ Y0 n ∧ Y0 n ≤ 1 := by
  unfold Y0; split_ifs <;> norm_num

/-- The predictor's process: `base0` plus the contract ledger settled to the truth table.
Source: mandate D2 / T3 witness
Kind: D
Fidelity: n/a -/
noncomputable def DPA0' : DeductiveProcess :=
  ledgerProcess base0 (fun _ n => Y0 n) (fun _ => payoutSchedule)

/-- `DPA0'_computable`.
Source: none: infrastructure
Kind: C
Fidelity: n/a -/
theorem DPA0'_computable : ComputableDeductiveProcess DPA0' :=
  ledgerProcess_computable base0_computable (Y0_computable.comp Computable.snd)
    payoutSchedule_computable

/-- `A0_inductor`.
Source: FAF `LIA_is_logical_inductor`
Kind: L
Fidelity: n/a -/
theorem A0_inductor : IsLogicalInductor (liaHistory DPA0') DPA0' :=
  LIA_is_logical_inductor DPA0' DPA0'_computable

/-- A market program for the predictor.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def M0 : MarketComputation (liaHistory DPA0') :=
  Classical.choice A0_inductor.marketComputable.nonemptyComputation

/-- The published quote table.
Source: mandate T3 witness
Kind: D
Fidelity: n/a -/
noncomputable def a0 (n : ℕ) : ℚ := M0.expectQuoteAt (ledgerLuv 0) n n

/-- `a0_eq`.
Source: FAF `expectQuoteAt_cast`
Kind: L
Fidelity: n/a -/
theorem a0_eq (n : ℕ) : (a0 n : ℝ) = (ledgerLuv 0 n).expect (liaHistory DPA0') n :=
  (M0.expectQuoteAt_cast (ledgerLuv 0) n n).symm

/-- `a0_mem`.
Source: FAF `expectQuoteAt_mem_Icc`
Kind: L
Fidelity: n/a -/
theorem a0_mem (n : ℕ) : 0 ≤ a0 n ∧ a0 n ≤ 1 := M0.expectQuoteAt_mem_Icc _ n n

/-- `a0_computable`.
Source: FAF `expectQuoteAt_computable`
Kind: L
Fidelity: n/a -/
theorem a0_computable : Computable a0 :=
  ((M0.expectQuoteAt_computable (ledgerLuv_thresholdCodes 0)).comp
    (Computable.id.pair Computable.id)).of_eq fun _ => rfl

/-- The two-item `H`-side table: the quote and the truth value.
Source: mandate D2 / T3 witness
Kind: D
Fidelity: n/a -/
noncomputable def table0 : ℕ → ℕ → ℚ := frozenTable a0 Y0

/-- `table0_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem table0_mem (j n : ℕ) : 0 ≤ table0 j n ∧ table0 j n ≤ 1 := by
  unfold table0 frozenTable
  split_ifs
  · exact a0_mem n
  · exact Y0_mem n

/-- `table0_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem table0_computable : Computable fun p : ℕ × ℕ => table0 p.1 p.2 := by
  have hc : Computable fun p : ℕ × ℕ => decide (p.1 = 0) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide.to_comp
  refine (Computable.cond hc (a0_computable.comp Computable.snd)
    (Y0_computable.comp Computable.snd)).of_eq fun p => ?_
  simp only [table0, frozenTable]
  by_cases h : p.1 = 0 <;> simp [h]

/-- The advised reasoner's process.
Source: mandate T3 witness
Kind: D
Fidelity: n/a -/
noncomputable def DPH0' : DeductiveProcess := ledgerProcess base0 table0 sched5

/-- `DPH0'_computable`.
Source: none: infrastructure
Kind: C
Fidelity: n/a -/
theorem DPH0'_computable : ComputableDeductiveProcess DPH0' :=
  ledgerProcess_computable base0_computable table0_computable sched5_computable

/-- Sibling `N`'s process (the two-item ledger frozen at day `N`).
Source: mandate T3 witness
Kind: D
Fidelity: n/a -/
noncomputable def sibProc0 (N : ℕ) : DeductiveProcess := siblingProcess base0 table0 sched5 N

/-- `sibProc0_computable`.
Source: none: infrastructure
Kind: C
Fidelity: n/a -/
theorem sibProc0_computable (N : ℕ) : ComputableDeductiveProcess (sibProc0 N) :=
  siblingProcess_computable base0_computable table0_computable sched5_computable N

/-- **The sibling pinned to the truth at the horizon**: FAF's LIA on the frozen process with its
day-`N + 1` price of `P^{(N)}` moved to the decided value `Y0 N` (an inductor by `thm:ifp`).
Source: mandate D2 (non-vacuity witness); FAF `thm:ifp`
Kind: D
Fidelity: n/a -/
noncomputable def sib0 (N : ℕ) : History :=
  perturbAt (liaHistory (sibProc0 N)) (N + 1) (contract5 N) (Y0 N)

/-- `sib0_inductor`.
Source: FAF `thm:ifp` through `perturbAt_inductor`
Kind: C
Fidelity: n/a -/
theorem sib0_inductor (N : ℕ) : IsLogicalInductor (sib0 N) (sibProc0 N) :=
  perturbAt_inductor (LIA_is_logical_inductor _ (sibProc0_computable N)) _ _ _ (Y0_mem N).1
    (Y0_mem N).2

/-! ## C. The system, and every day timely -/

/-- **The on-`G` inhabitant** (one-way, N+): the shared process `base0`, horizon `succDeferral`,
settlement `payoutSchedule`, the predictor and the advised reasoner FAF's LIAs, every sibling the
LIA pinned to the truth at the horizon, the diagonal the (non-constant) truth table.
Source: mandate D2 (the N− witness, improved), T3 ("Witness (N+, one-way)")
Kind: N+
Fidelity: exact (one-way: `Y` is a given table; the sibling is pinned, not converged — findings F3)
Hyps: (a) none -/
noncomputable def onGSystem : FrozenSystem where
  base := base0
  DPA0 := base0
  shared := fun _ => subset_rfl
  eq := PublicationSchedule.sameDay
  eY := payoutSchedule
  F := succDeferral
  σ := payoutSchedule
  eq_lt_F := fun n => Nat.lt_succ_self n
  F_lt_σ := fun n => by show n + 1 < n + 2; omega
  σ_le_eY := fun _ => le_rfl
  contract := contract5
  contract_codes := contract5_codes
  contract_ledgerFree := fun _ =>
    freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, ledgerFamily, contractFamily])
  contract_projFree := fun _ =>
    freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, contractFamily])
  A := liaHistory DPA0'
  Hplus := liaHistory DPH0'
  sib := sib0
  a := a0
  Y := Y0
  Y_eq := fun n => (perturbAt_at _ _ _ _).symm
  a_eq := a0_eq
  A_inductor := A0_inductor
  Hplus_inductor := LIA_is_logical_inductor DPH0' DPH0'_computable
  sib_inductor := sib0_inductor
  hworldA := ledgerProcess_hworld (base0_freeOf_ledger _ _) base0_hworld
  hworldH := ledgerProcess_hworld (base0_freeOf_ledger _ _) base0_hworld
  hworldSib := fun N => sibling_hworld (base0_freeOf_ledger _ _) base0_hworld N
  determinedA := fun n => ledgerLuv_determinedVia base0 _ _ (fun _ n => Y0_mem n) 0 n
  determinedH := fun j n => ledgerLuv_determinedVia base0 _ _ table0_mem j n
  determinedSib := fun N j n hN => siblingLuv_determinedVia base0 _ _ table0_mem N j n hN

/-- Every day is decided by the horizon in the on-`G` inhabitant.
Source: mandate D2
Kind: L
Fidelity: n/a -/
theorem onG_decidedBy (n : ℕ) : DecidedBy onGSystem n := by
  show contract5 n ∈ base0.D (n + 1) ∨ ∼contract5 n ∈ base0.D (n + 1)
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact Or.inl (base0.mono_le (Nat.le_succ n) (contract0_mem_of_even n h))
  · exact Or.inr (base0.mono_le (Nat.le_succ n) (contract0_neg_mem_of_odd n h))

/-- The decided value is the truth table.
Source: mandate D2
Kind: L
Fidelity: n/a -/
theorem onG_truthAt (n : ℕ) : truthAt onGSystem n = Y0 n := by
  show (if contract5 n ∈ base0.D (n + 1) then (1 : ℚ) else 0) = Y0 n
  unfold Y0
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos (base0.mono_le (Nat.le_succ n) (contract0_mem_of_even n h)), if_pos h]
  · rw [if_neg (contract0_not_mem_of_odd n h (n + 1)), if_neg (by omega)]

/-- **Every day is timely, at every non-negative tolerance** — including `ε ≡ 0`: the sibling's
verdict is the decided value exactly.
Source: mandate D2 (non-vacuity of `G`, N+ at a fixed tolerance; the vanishing-tolerance diagonal
property of an unperturbed family is the OPEN `timely_cofinite_const`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem onG_timely (ε : ℕ → ℚ) (hε : ∀ n, 0 ≤ ε n) (n : ℕ) : Timely onGSystem ε n := by
  refine ⟨onG_decidedBy n, ?_⟩
  show |Y0 n - truthAt onGSystem n| ≤ ε n
  rw [onG_truthAt, sub_self, abs_zero]
  exact hε n

/-- The truth table is not constant (non-degeneracy of the inhabitant).
Source: mandate T1 trap ("the witness must exhibit a non-constant `Y`")
Kind: N+
Fidelity: n/a -/
theorem Y0_not_const : Y0 0 ≠ Y0 1 := by
  simp [Y0]

/-! ## D. The on-`G` suite at the inhabitant -/

/-- **T3's A-side at the inhabitant (N+, one-way, grade (a))**: FAF's LIA over the contract ledger
settled to the truth value has `𝔼^A_n(C_n) ≈ A_n(P^{(n)})` on every day (`t ≡ 0`, tolerance `0`) —
the expectation of a ledger LUV settled to the decided value of a sentence agrees with the LIA's
own price of that sentence.
Source: mandate T3 ("Witness (N+, one-way): the deferred pair … a contract family decided at stage 0 with alternating polarity, `F = succDeferral`, `t ≡ 0`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem engineA_onG :
    ∀ δ > 0, ∀ᶠ n in atTop,
      |(ledgerLuv 0 n).expect (liaHistory DPA0') n - liaHistory DPA0' n (contract5 n)| ≤ δ := by
  intro δ hδ
  have hε : Tendsto (fun _ : ℕ => (((0 : ℚ)) : ℝ)) atTop (𝓝 0) := by
    simp only [Rat.cast_zero]
    exact tendsto_const_nhds
  have h := engineA onGSystem (fun _ => 0) hε (UnaryRuler.const 0)
    (fun n _ => onG_timely (fun _ => 0) (fun _ => le_rfl) n) δ hδ
  filter_upwards [h] with n hn
  exact hn rfl

/-- **T7 at the inhabitant (N+, one-way)**: on every day the perturbed sibling's, the advised
reasoner's and the predictor's limiting beliefs on `P^{(n)}` equal the truth value.
Source: mandate T7 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem limit_agree_onG_onG (n : ℕ) :
    limitingBelief (sib0 n) (contract5 n) = (Y0 n : ℝ) ∧
      limitingBelief (liaHistory DPH0') (contract5 n) = (Y0 n : ℝ) ∧
      limitingBelief (liaHistory DPA0') (contract5 n) = (Y0 n : ℝ) := by
  have h := limit_agree_onG onGSystem (fun _ => 0) n (onG_timely (fun _ => 0) (fun _ => le_rfl) n)
  rw [onG_truthAt] at h
  exact h

/-! ## E. The `hz` clause at the inhabitant: the alternating table is generable (repair round 1) -/

/-- The parity flag `n ↦ if n % 2 = 0 then 1 else 0` is a unary ruler: `MachineDigits.mod_two` of
the identity count, dispatched by `UnaryRuler.ifZero`.
Source: audit r1 adversarial B3 (iii) (probe `AlternatingGenerable.lean`); FAF `UnaryRuler.ifZero`, `MachineDigits.mod_two`
Kind: L
Fidelity: n/a -/
theorem flip_ruler : UnaryRuler (fun n : ℕ => if n % 2 = 0 then 1 else 0) :=
  UnaryRuler.ifZero (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two (UnaryRuler.const 1)
    (UnaryRuler.const 0)

/-- **The alternating table is machine-metered**: numerator code `2·flag` (FAF encodes `(1 : ℤ)`
as `2` and `(0 : ℤ)` as `0`), magnitude `flag`, denominator `1`. This is the dispatch certificate
the first-round report said FAF lacked; it is `UnaryRuler.ifZero` on `MachineDigits.mod_two`.
Source: audit r1 adversarial B3 (iii) (probe `AlternatingGenerable.lean`); FAF `MachineRatCodes`
Kind: L
Fidelity: n/a -/
theorem Y0_machineRatCodes : MachineRatCodes Y0 where
  numCode :=
    ((MachineDigits.ofUnaryRuler flip_ruler).add (MachineDigits.ofUnaryRuler flip_ruler)).of_eq
      (fun n => by
        unfold Y0
        split_ifs <;> simp [show Encodable.encode (1 : ℤ) = 2 from rfl,
          show Encodable.encode (0 : ℤ) = 0 from rfl])
  natAbsNum :=
    (MachineDigits.ofUnaryRuler flip_ruler).of_eq (fun n => by
      unfold Y0
      split_ifs <;> simp)
  den :=
    (MachineDigits.const 1).of_eq (fun n => by
      unfold Y0
      split_ifs <;> simp)

/-- **`hz` at the inhabitant** (checklist row 6 discharged): the alternating table is generable at
the predictor — FAF's `PGenerableRat.ofMachineRatCodes`, so in fact at every market.
Source: audit r1 adversarial B3 (iii); FAF `PGenerableRat.ofMachineRatCodes`
Kind: L
Fidelity: n/a -/
theorem hz_onG : PGenerableRat onGSystem.A Y0 :=
  PGenerableRat.ofMachineRatCodes Y0_machineRatCodes _

/-- `hlim` at the inhabitant is trivial: the approximant is the table itself.
Source: none: infrastructure
Kind: T
Fidelity: n/a -/
theorem hlim_onG : Tendsto (fun n => (Y0 n : ℝ) - onGSystem.Y n) atTop (𝓝 0) := by
  show Tendsto (fun n => (Y0 n : ℝ) - (Y0 n : ℝ)) atTop (𝓝 0)
  simp only [sub_self]
  exact tendsto_const_nhds

/-- The tolerance `ε ≡ 0` vanishes.
Source: none: infrastructure
Kind: T
Fidelity: n/a -/
theorem hε_onG : Tendsto (fun _ : ℕ => (((0 : ℚ)) : ℝ)) atTop (𝓝 0) := by
  simp only [Rat.cast_zero]
  exact tendsto_const_nhds

/-- Every day is in the sub-fragment of the trivial ruler `t ≡ 0`, and timely at tolerance `0`.
Source: none: infrastructure
Kind: T
Fidelity: n/a -/
theorem hG_onG : ∀ n, (fun _ : ℕ => 0) n = 0 → Timely onGSystem (fun _ => 0) n :=
  fun n _ => onG_timely (fun _ => 0) (fun _ => le_rfl) n

/-- **T1 at the inhabitant (N+, one-way)**: FAF's LIA's expectation of the contract LUV settled to
the alternating truth table tracks it, `a0 ≈ₙ Y0`. The full hypothesis package of `tracking` is
inhabited (`hz_onG`, `hlim_onG`); in the quote-redundant regime of findings F4 (the polarity
pattern is e.c.).
Source: mandate T1 (witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way; `Y` the given truth table)
Hyps: (a) none -/
theorem tracking_onG : (fun n => (a0 n : ℝ)) ≈ₙ (fun n => (Y0 n : ℝ)) :=
  tracking onGSystem Y0 hz_onG hlim_onG

/-- **T2b at the inhabitant (N+, one-way)**: the advised reasoner's price of the calibration
sentence tends to `1` at every `ε₀ > 0`.
Source: mandate T2 (witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way)
Hyps: (a) none -/
theorem metaTrust_onG {ε₀ : ℚ} (hε₀ : 0 < ε₀) :
    (fun n => liaHistory DPH0' n (calSentence ε₀ n)) ≈ₙ fun _ => 1 :=
  metaTrust onGSystem hε₀ Y0 hz_onG hlim_onG

/-- **T2a at the inhabitant (N+, one-way)**: the advised reasoner's expectations of the quote item
and the settled-value item agree.
Source: mandate T2a (witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way)
Hyps: (a) none -/
theorem metaTrust_expect_onG :
    (fun n => (ledgerLuv 0 n).expect (liaHistory DPH0') n) ≈ₙ
      (fun n => (ledgerLuv 1 n).expect (liaHistory DPH0') n) :=
  metaTrust_expect onGSystem Y0 hz_onG hlim_onG

/-- **A-to-truth at the inhabitant (N+, one-way)**: the quote tracks the alternating truth on
every day.
Source: mandate T3 (`engineA_truth`, witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way; `t ≡ 0`)
Hyps: (a) none -/
theorem engineA_truth_onG :
    ∀ δ > 0, ∀ᶠ n in atTop, |(a0 n : ℝ) - (truthAt onGSystem n : ℝ)| ≤ δ := by
  intro δ hδ
  filter_upwards [engineA_truth onGSystem (fun _ => 0) hε_onG hG_onG Y0 hz_onG hlim_onG δ hδ]
    with n hn
  exact hn rfl

/-- **T3 H-side (the conditional tower) at the inhabitant (N+, one-way)**: FAF's LIA over the
two-item ledger has its price of the decided contract agree with its expectation of the quote item
`α_{0,n}` (settled at `a0 n`), on every day. The H-side row the first-round report said had no
witness.
Source: mandate T3 H-side (witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way; `t ≡ 0`; quote-redundant regime of F4)
Hyps: (a) none -/
theorem condTower_onG_onG :
    ∀ δ > 0, ∀ᶠ n in atTop,
      |liaHistory DPH0' n (contract5 n) - (ledgerLuv 0 n).expect (liaHistory DPH0') n| ≤ δ := by
  intro δ hδ
  filter_upwards [condTower_onG onGSystem (fun _ => 0) hε_onG (UnaryRuler.const 0) hG_onG Y0
    hz_onG hlim_onG δ hδ] with n hn
  exact hn rfl

/-- **T4a at the inhabitant (N+, one-way)**, at the threshold `s = 1/2`: the advised reasoner's
expectation of the followed two-option strategy dominates its expectation of `𝟙 P^{(n)}` and the
constant `1/2`.
Source: mandate T4a (witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way; `t ≡ 0`, `s = 1/2`)
Hyps: (a) none -/
theorem valueTwoOption_onG_onG :
    (∀ δ > 0, ∀ᶠ n in atTop,
      (LUV.indicatorOf (contract5 n)).expect (liaHistory DPH0') n - δ ≤
        (followed onGSystem (1 / 2) n).expect (liaHistory DPH0') n) ∧
    (∀ δ > 0, ∀ᶠ n in atTop,
      ((1 / 2 : ℚ) : ℝ) - δ ≤ (followed onGSystem (1 / 2) n).expect (liaHistory DPH0') n) := by
  obtain ⟨h1, h2⟩ := valueTwoOption_onG onGSystem (fun _ => 0) hε_onG (UnaryRuler.const 0) hG_onG
    Y0 hz_onG hlim_onG (1 / 2) (by norm_num) (by norm_num)
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · filter_upwards [h1 δ hδ] with n hn
    exact hn rfl
  · filter_upwards [h2 δ hδ] with n hn
    exact hn rfl

/-- **T4b (above-threshold inequality) at the inhabitant (N+, one-way)**, at `s = 1/2`.
Source: mandate T4b (witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way; `t ≡ 0`, `s = 1/2`)
Hyps: (a) none -/
theorem thresholdAbove_onG_onG :
    ∀ δ > 0, ∀ᶠ n in atTop,
      -δ ≤ (LUV.indicatorOf (contract5 n ⋏ followLiteral (1 / 2) n)).expect (liaHistory DPH0') n -
        ((1 / 2 : ℚ) : ℝ) * (LUV.indicatorOf (followLiteral (1 / 2) n)).expect (liaHistory DPH0') n := by
  intro δ hδ
  filter_upwards [thresholdAbove_onG onGSystem (fun _ => 0) hε_onG (UnaryRuler.const 0) hG_onG Y0
    hz_onG hlim_onG (1 / 2) (by norm_num) (by norm_num) δ hδ] with n hn
  exact hn rfl

/-- **T4b (Value against the constant on `def-lattice`'s `twoOptionComb`) at the inhabitant (N+,
one-way)**, at `s = 1/2`.
Source: mandate T4b (witness); audit r1 adversarial B3 (iii)
Kind: N+
Fidelity: exact (one-way; `t ≡ 0`, `s = 1/2`)
Hyps: (a) none -/
theorem valueConst_onG_onG :
    ∀ δ > 0, ∀ᶠ n in atTop, ((1 / 2 : ℚ) : ℝ) - δ ≤
      (Cleanroom.Found.DefLattice.twoOptionComb (1 / 2)
        (fun n => LUV.indicatorOf (contract5 n ⋏ followLiteral (1 / 2) n))
        (fun n => LUV.indicatorOf (followLiteral (1 / 2) n)) n).expect (liaHistory DPH0') n := by
  intro δ hδ
  filter_upwards [valueConst_onG onGSystem (fun _ => 0) hε_onG (UnaryRuler.const 0) hG_onG Y0
    hz_onG hlim_onG (1 / 2) (by norm_num) (by norm_num) δ hδ] with n hn
  exact hn rfl

/-- **T6 at the inhabitant (one-way)**: the interior bin at `v = 1/2`, `δ = 1/4`, is eventually
empty — N− by the sources' own admission (the calibration content on `G` is degenerate).
Source: mandate T6 (witness); audit r1 adversarial B3 (iii)
Kind: N-
Fidelity: exact (one-way)
Hyps: (a) none -/
theorem calibration_onG_degenerate_onG :
    ∀ᶠ n in atTop, (1 / 4 : ℝ) < |(a0 n : ℝ) - 1 / 2| := by
  filter_upwards [calibration_onG_degenerate onGSystem (fun _ => 0) hε_onG hG_onG Y0 hz_onG
    hlim_onG (1 / 2) (by norm_num) (by norm_num) (1 / 4) (by norm_num) (by norm_num)] with n hn
  exact hn rfl

/-! ## F. The anti-truth sibling: the tolerance clause is not a property of the horizon alone
(repair round 1, audit r1 adversarial B1) -/

/-- The anti-truth table `1 − Y0`: `0` on even days, `1` on odd days.
Source: audit r1 adversarial B1 (probe `NotMonoRelabel.lean`)
Kind: D
Fidelity: n/a -/
def Y1 (n : ℕ) : ℚ := if n % 2 = 0 then 0 else 1

/-- `Y1_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Y1_computable : Computable Y1 := by
  have hc : Computable fun n : ℕ => decide (n % 2 = 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).decide.to_comp
  refine (Computable.cond hc (Computable.const (0 : ℚ)) (Computable.const (1 : ℚ))).of_eq
    fun n => ?_
  simp only [Y1]
  by_cases h : n % 2 = 0 <;> simp [h]

/-- `Y1_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Y1_mem (n : ℕ) : 0 ≤ Y1 n ∧ Y1 n ≤ 1 := by
  unfold Y1; split_ifs <;> norm_num

/-- The predictor's process with the ledger settled to the anti-truth table.
Source: audit r1 adversarial B1
Kind: D
Fidelity: n/a -/
noncomputable def DPA1 : DeductiveProcess :=
  ledgerProcess base0 (fun _ n => Y1 n) (fun _ => payoutSchedule)

/-- `DPA1_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DPA1_computable : ComputableDeductiveProcess DPA1 :=
  ledgerProcess_computable base0_computable (Y1_computable.comp Computable.snd)
    payoutSchedule_computable

/-- `A1_inductor`: FAF's LIA over `DPA1`.
Source: none: infrastructure; FAF `LIA_is_logical_inductor`
Kind: L
Fidelity: n/a -/
theorem A1_inductor : IsLogicalInductor (liaHistory DPA1) DPA1 :=
  LIA_is_logical_inductor DPA1 DPA1_computable

/-- A market program for the anti-truth predictor.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def M1 : MarketComputation (liaHistory DPA1) :=
  Classical.choice A1_inductor.marketComputable.nonemptyComputation

/-- The anti-truth predictor's quote table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def a1 (n : ℕ) : ℚ := M1.expectQuoteAt (ledgerLuv 0) n n

/-- `a1_eq`: the quote is the LIA's expectation of the contract LUV.
Source: none: infrastructure; FAF `expectQuoteAt_cast`
Kind: L
Fidelity: n/a -/
theorem a1_eq (n : ℕ) : (a1 n : ℝ) = (ledgerLuv 0 n).expect (liaHistory DPA1) n :=
  (M1.expectQuoteAt_cast (ledgerLuv 0) n n).symm

/-- `a1_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem a1_mem (n : ℕ) : 0 ≤ a1 n ∧ a1 n ≤ 1 := M1.expectQuoteAt_mem_Icc _ n n

/-- `a1_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem a1_computable : Computable a1 :=
  ((M1.expectQuoteAt_computable (ledgerLuv_thresholdCodes 0)).comp
    (Computable.id.pair Computable.id)).of_eq fun _ => rfl

/-- The two-item table of the anti-truth system.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def table1 : ℕ → ℕ → ℚ := frozenTable a1 Y1

/-- `table1_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem table1_mem (j n : ℕ) : 0 ≤ table1 j n ∧ table1 j n ≤ 1 := by
  unfold table1 frozenTable
  split_ifs
  · exact a1_mem n
  · exact Y1_mem n

/-- `table1_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem table1_computable : Computable fun p : ℕ × ℕ => table1 p.1 p.2 := by
  have hc : Computable fun p : ℕ × ℕ => decide (p.1 = 0) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide.to_comp
  refine (Computable.cond hc (a1_computable.comp Computable.snd)
    (Y1_computable.comp Computable.snd)).of_eq fun p => ?_
  simp only [table1, frozenTable]
  by_cases h : p.1 = 0 <;> simp [h]

/-- The anti-truth advised reasoner's process.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def DPH1 : DeductiveProcess := ledgerProcess base0 table1 sched5

/-- `DPH1_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem DPH1_computable : ComputableDeductiveProcess DPH1 :=
  ledgerProcess_computable base0_computable table1_computable sched5_computable

/-- Sibling `N`'s process in the anti-truth system.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def sibProc1 (N : ℕ) : DeductiveProcess := siblingProcess base0 table1 sched5 N

/-- `sibProc1_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sibProc1_computable (N : ℕ) : ComputableDeductiveProcess (sibProc1 N) :=
  siblingProcess_computable base0_computable table1_computable sched5_computable N

/-- The sibling pinned at the horizon to the **wrong** value: FAF's LIA on its frozen process
with its day-`F N` price of `P^{(N)}` moved to `Y1 N = 1 − truthAt N`.
Source: audit r1 adversarial B1
Kind: D
Fidelity: n/a -/
noncomputable def sib1 (N : ℕ) : History :=
  perturbAt (liaHistory (sibProc1 N)) (N + 1) (contract5 N) (Y1 N)

/-- `sib1_inductor`: an inductor by `thm:ifp`, exactly as `sib0`.
Source: none: infrastructure; FAF `lic_iff_of_finiteSupport` through `perturbAt_inductor`
Kind: L
Fidelity: n/a -/
theorem sib1_inductor (N : ℕ) : IsLogicalInductor (sib1 N) (sibProc1 N) :=
  perturbAt_inductor (LIA_is_logical_inductor _ (sibProc1_computable N)) _ _ _ (Y1_mem N).1
    (Y1_mem N).2

/-- **The anti-truth system**: `onGSystem` with the sibling family pinned to the wrong value —
same shared process `base0`, same contracts, same horizon `succDeferral` and schedules; `A` and
`Hplus` FAF's LIAs over their (now different) ledger processes, every sibling the LIA perturbed to
`1 − truthAt n` at the horizon. One-way.
Source: audit r1 adversarial B1 (probe `NotMonoRelabel.lean`); mandate T13
Kind: N+
Fidelity: exact (one-way)
Hyps: (a) none -/
noncomputable def antiSystem : FrozenSystem where
  base := base0
  DPA0 := base0
  shared := fun _ => subset_rfl
  eq := PublicationSchedule.sameDay
  eY := payoutSchedule
  F := succDeferral
  σ := payoutSchedule
  eq_lt_F := fun n => Nat.lt_succ_self n
  F_lt_σ := fun n => by show n + 1 < n + 2; omega
  σ_le_eY := fun _ => le_rfl
  contract := contract5
  contract_codes := contract5_codes
  contract_ledgerFree := fun _ =>
    freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, ledgerFamily, contractFamily])
  contract_projFree := fun _ =>
    freshAtom_tagFree_of_ne (by simp [cleanroomBaseTag, contractFamily])
  A := liaHistory DPA1
  Hplus := liaHistory DPH1
  sib := sib1
  a := a1
  Y := Y1
  Y_eq := fun n => (perturbAt_at _ _ _ _).symm
  a_eq := a1_eq
  A_inductor := A1_inductor
  Hplus_inductor := LIA_is_logical_inductor DPH1 DPH1_computable
  sib_inductor := sib1_inductor
  hworldA := ledgerProcess_hworld (base0_freeOf_ledger _ _) base0_hworld
  hworldH := ledgerProcess_hworld (base0_freeOf_ledger _ _) base0_hworld
  hworldSib := fun N => sibling_hworld (base0_freeOf_ledger _ _) base0_hworld N
  determinedA := fun n => ledgerLuv_determinedVia base0 _ _ (fun _ n => Y1_mem n) 0 n
  determinedH := fun j n => ledgerLuv_determinedVia base0 _ _ table1_mem j n
  determinedSib := fun N j n hN => siblingLuv_determinedVia base0 _ _ table1_mem N j n hN

/-- The decided value at `antiSystem` is the truth table (same base, contracts and horizon as
`onGSystem`).
Source: audit r1 adversarial B1
Kind: L
Fidelity: n/a -/
theorem anti_truthAt (n : ℕ) : truthAt antiSystem n = Y0 n := by
  show (if contract5 n ∈ base0.D (n + 1) then (1 : ℚ) else 0) = Y0 n
  unfold Y0
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos (base0.mono_le (Nat.le_succ n) (contract0_mem_of_even n h)), if_pos h]
  · rw [if_neg (contract0_not_mem_of_odd n h (n + 1)), if_neg (by omega)]

/-- Every day is decided at `antiSystem` (the decided clause is the same as at `onGSystem`), and
**no day is timely at tolerance `0`**: the sibling's verdict is `1` away from the decided value.
Source: audit r1 adversarial B1
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem anti_not_timely (n : ℕ) : DecidedBy antiSystem n ∧ ¬ Timely antiSystem (fun _ => 0) n := by
  refine ⟨?_, fun h => ?_⟩
  · show contract5 n ∈ base0.D (n + 1) ∨ ∼contract5 n ∈ base0.D (n + 1)
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact Or.inl (base0.mono_le (Nat.le_succ n) (contract0_mem_of_even n h))
    · exact Or.inr (base0.mono_le (Nat.le_succ n) (contract0_neg_mem_of_odd n h))
  · have h2 : |Y1 n - truthAt antiSystem n| ≤ (0 : ℚ) := h.2
    rw [anti_truthAt] at h2
    unfold Y1 Y0 at h2
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [if_pos hn, if_pos hn] at h2; norm_num at h2
    · rw [if_neg (by omega), if_neg (by omega)] at h2; norm_num at h2

/-- **T13 — the tolerance clause of `Timely` is not a function of the shared process, the
contracts and the horizon** (headline, N+): two frozen-deliberation systems with the *same*
shared process, contracts, horizon and all three schedules, every day decided in both, one
timely at every day and the other at none (`onGSystem` against `antiSystem`, tolerance `0`). The
decided clause is monotone in the horizon (`decidedBy_mono`); the tolerance clause depends on the
sibling family, which is a free field of the carrier. Consequently the mandate's T13 implication
`Timely S ε n → Timely S' ε n` for `F ≤ F'` over the carrier is false (take `F' = F`) — a fact
about the carrier, not about FAF's LIA family. The question with content (the same unperturbed
LIA family at a strictly later horizon) is the OPEN `timely_not_mono_open` (`OffG.lean` §F).
Source: root-fa-2-011 (ii); [[legitimacy-theory-v1]] §7.2 ("grow `G`"); mandate T13 (F8); audit r1 adversarial B1
Kind: N+
Fidelity: stronger: the horizon and every schedule are equal, not merely `F ≤ F'`; `ε ≡ 0`
Hyps: (a) none -/
theorem timely_not_horizon_only : ∃ (S S' : FrozenSystem) (ε : ℕ → ℚ),
    S'.base = S.base ∧ S'.DPA0 = S.DPA0 ∧ S'.contract = S.contract ∧ S'.F = S.F ∧
    S'.σ = S.σ ∧ S'.eq = S.eq ∧ S'.eY = S.eY ∧
    (∀ n, DecidedBy S n) ∧ (∀ n, DecidedBy S' n) ∧
    (∀ n, Timely S ε n) ∧ (∀ n, ¬ Timely S' ε n) :=
  ⟨onGSystem, antiSystem, fun _ => 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun n => onG_decidedBy n, fun n => (anti_not_timely n).1,
    fun n => onG_timely (fun _ => 0) (fun _ => le_rfl) n, fun n => (anti_not_timely n).2⟩

/-! ## G. The inhabitants and the pinned OPEN rows, read closely (repair round 2) -/

/-- At `antiSystem` the verdict is exactly `1` from the decided value at every day.
Source: audit r2 adversarial N2 (probe `PinnedSystems.lean`)
Kind: L
Fidelity: n/a -/
theorem anti_gap (n : ℕ) : |Y1 n - truthAt antiSystem n| = 1 := by
  rw [anti_truthAt]
  unfold Y1 Y0
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg (by omega), if_neg (by omega)]; norm_num

/-- **"Timely nowhere" is tolerance-relative**: `Timely antiSystem ε n ↔ 1 ≤ ε n`. At every
tolerance below `1` no day of `antiSystem` is timely; at tolerance `1` (or any larger) every day
is — as at any system decided at every day (audit r1 N7).
Source: audit r2 adversarial N2 (probe `PinnedSystems.lean`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem anti_timely_iff (ε : ℕ → ℚ) (n : ℕ) : Timely antiSystem ε n ↔ 1 ≤ ε n := by
  constructor
  · intro h
    have h2 : |Y1 n - truthAt antiSystem n| ≤ ε n := h.2
    rwa [anti_gap] at h2
  · intro h
    refine ⟨(anti_not_timely n).1, ?_⟩
    have h2 : |Y1 n - truthAt antiSystem n| ≤ ε n := by rw [anti_gap]; exact h
    exact h2

/-- At tolerance `1` every day of `antiSystem` is timely (the instance of `anti_timely_iff`).
Source: audit r2 adversarial N2
Kind: N−
Fidelity: n/a -/
theorem anti_timely_at_one (n : ℕ) : Timely antiSystem (fun _ => 1) n :=
  (anti_timely_iff _ n).2 le_rfl

/-- At a system with the pins of `timely_cofinite_const` (and of `timely_not_mono_open`'s `S`):
shared process `base0`, contracts `contract5`, horizon `succDeferral` — every day is decided by
the horizon and the decided value is `Y0`. (The market pins are not needed for this.)
Source: audit r2 adversarial B1 (iii) (probe `PinnedSystems.lean`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem pinned_base0_decided (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral) (n : ℕ) :
    DecidedBy S n ∧ truthAt S n = Y0 n := by
  unfold DecidedBy truthAt
  rw [hb, hc, hF]
  show (contract5 n ∈ base0.D (n + 1) ∨ ∼contract5 n ∈ base0.D (n + 1)) ∧
    (if contract5 n ∈ base0.D (n + 1) then (1 : ℚ) else 0) = Y0 n
  exact ⟨onG_decidedBy n, onG_truthAt n⟩

/-- The same at the horizon `n + 2` (`timely_not_mono_open`'s `S'`).
Source: audit r2 adversarial B1 (iii) (probe `PinnedSystems.lean`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem pinned_base0_decided' (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : ∀ m, S.F.f m = m + 2) (n : ℕ) :
    DecidedBy S n ∧ truthAt S n = Y0 n := by
  unfold DecidedBy truthAt
  rw [hb, hc, hF n]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hm : contract5 n ∈ base0.D (n + 2) :=
      base0.mono_le (by omega) (contract0_mem_of_even n h)
    refine ⟨Or.inl hm, ?_⟩
    rw [if_pos hm]
    unfold Y0
    rw [if_pos h]
  · have hm : ∼contract5 n ∈ base0.D (n + 2) :=
      base0.mono_le (by omega) (contract0_neg_mem_of_odd n h)
    refine ⟨Or.inr hm, ?_⟩
    rw [if_neg (contract0_not_mem_of_odd n h (n + 2))]
    unfold Y0
    rw [if_neg (by omega)]

/-- **`timely_cofinite_const`'s last conjunct, at its pins, is diagonal convergence** read at
constant tolerances: `Timely S (fun _ => δ) n ↔ |S.Y n − Y0 n| ≤ δ`. So the OPEN row asks exactly
whether `S.Y n − Y0 n → 0` — the sibling LIA family's verdict along its diagonal against the
alternating truth table.
Source: audit r2 adversarial B1 (iii) (probe `PinnedSystems.lean`); findings F3
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem cofinite_const_iff (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral) (δ : ℚ) (n : ℕ) :
    Timely S (fun _ => δ) n ↔ |S.Y n - Y0 n| ≤ δ := by
  obtain ⟨hD, ht⟩ := pinned_base0_decided S hb hc hF n
  constructor
  · intro h
    have h2 := h.2
    rwa [ht] at h2
  · intro h
    exact ⟨hD, by rw [ht]; exact h⟩

/-- **`timely_not_mono_open`'s last three conjuncts, at its pins, are a one-day strict
comparison** `|S.Y n − Y0 n| < |S'.Y n − Y0 n|`: the tolerance schedule is a free existential
(the general reduction is `exists_tol_iff`, `Defs.lean` §F; here both systems are decided at
every day with decided value `Y0`).
Source: audit r2 adversarial N1 (probes `ToleranceFree.lean`, `PinnedSystems.lean`); findings F8
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem notMono_tol_iff (S S' : FrozenSystem) (hb : S.base = base0) (hc : S.contract = contract5)
    (hF : S.F = succDeferral) (hb' : S'.base = base0) (hc' : S'.contract = contract5)
    (hF' : ∀ m, S'.F.f m = m + 2) (n : ℕ) :
    (∃ ε : ℕ → ℚ, (∀ m, 0 ≤ ε m) ∧ Timely S ε n ∧ ¬ Timely S' ε n) ↔
      |S.Y n - Y0 n| < |S'.Y n - Y0 n| := by
  obtain ⟨hD, ht⟩ := pinned_base0_decided S hb hc hF n
  obtain ⟨hD', ht'⟩ := pinned_base0_decided' S' hb' hc' hF' n
  rw [exists_tol_iff, ht, ht']
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd hD' h
    · exact h
  · intro h
    exact ⟨hD, Or.inr h⟩

/-- **The diagonal property at the pins of `timely_cofinite_const` gives the two-way on-`G`
instance of `engineA` at `t ≡ 0`** (repair round 2, audit r2 adversarial B1 (iii)): for any
system with those three pins (shared process `base0`, contracts `contract5`, horizon
`succDeferral`) whose sibling family converges along its diagonal, there is a non-negative
tolerance schedule vanishing at infinity at which every day is timely, and along the whole
sequence the predictor's expectation of the contract LUV agrees with its own price of the
proposition. So the nine on-`G` two-way rows are partial over `timely_cofinite_const` (plus `hz`
there, for the `hz`-rows), not over the bare existence row `frozenSystem_exists`.
Source: audit r2 adversarial B1 (iii); mandate T3 (the A-side); findings F3
Kind: L (over `timely_all_of_diagonal` and `engineA`)
Fidelity: n/a
Hyps: (a) none (`hdiag` is the OPEN row's last conjunct) -/
theorem engineA_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    ∃ ε : ℕ → ℚ, Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧ (∀ n, Timely S ε n) ∧
      AgreeAlong (fun _ => 0) (fun n => (ledgerLuv 0 n).expect S.A n)
        (fun n => S.A n (S.contract n)) := by
  obtain ⟨ε, hε, -, hT⟩ :=
    timely_all_of_diagonal S (fun n => (pinned_base0_decided S hb hc hF n).1) hdiag
  exact ⟨ε, hε, hT, engineA S ε hε (UnaryRuler.const 0) (fun n _ => hT n)⟩

/-- The parity ruler that vanishes on even days (`flip_ruler` is the one vanishing on odd days).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem evenZero_ruler : UnaryRuler (fun n : ℕ => if n % 2 = 0 then 0 else 1) :=
  UnaryRuler.ifZero (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two (UnaryRuler.const 0)
    (UnaryRuler.const 1)

/-- `hpat₁` at `onGSystem`, `t ≡ 0`: the "decided true" subfamily of the contracts is e.c.
Source: audit r2 adversarial N4 (probe `PinnedSystems.lean`); findings F4
Kind: L
Fidelity: n/a -/
theorem hpat₁_onG : MachineSentenceCodes
    (fun n => if (fun _ : ℕ => 0) n = 0 ∧ truthAt onGSystem n = 1 then onGSystem.contract n
      else ⊤) :=
  (MachineSentenceCodes.ifZero contract5_codes (MachineSentenceCodes.const ⊤) evenZero_ruler).of_eq
    (fun n => by
      have hc : onGSystem.contract n = contract5 n := rfl
      rw [onG_truthAt, hc]
      unfold Y0
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h])

/-- `hpat₀` at `onGSystem`, `t ≡ 0`: the "decided false" subfamily of the contracts is e.c.
Source: audit r2 adversarial N4 (probe `PinnedSystems.lean`); findings F4
Kind: L
Fidelity: n/a -/
theorem hpat₀_onG : MachineSentenceCodes
    (fun n => if (fun _ : ℕ => 0) n = 0 ∧ truthAt onGSystem n = 0 then onGSystem.contract n
      else ∼(⊤ : Sentence)) :=
  (MachineSentenceCodes.ifZero contract5_codes (MachineSentenceCodes.const (∼(⊤ : Sentence)))
    flip_ruler).of_eq (fun n => by
      have hc : onGSystem.contract n = contract5 n := rfl
      rw [onG_truthAt, hc]
      unfold Y0
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h])

/-- **`engineA_truth_onG` without `hz`**: the pattern route (`engineA_truth_ofPattern`) reaches the
same conclusion at the inhabitant, so the quote is redundant there — the regime caveat of
findings F4, machine-checked rather than asserted (audit r2 adversarial N4).
Source: audit r2 adversarial N4 (probe `PinnedSystems.lean`); findings F4
Kind: N+ (for the regime claim about the inhabitant)
Fidelity: n/a
Hyps: (a) none -/
theorem engineA_truth_onG_noHz :
    ∀ δ > 0, ∀ᶠ n in atTop, |(a0 n : ℝ) - (truthAt onGSystem n : ℝ)| ≤ δ := by
  intro δ hδ
  filter_upwards [engineA_truth_ofPattern onGSystem (fun _ => 0) hε_onG (UnaryRuler.const 0)
    hG_onG hpat₁_onG hpat₀_onG δ hδ] with n hn
  exact hn rfl

end Cleanroom.Deference.DefFrozenSibling
