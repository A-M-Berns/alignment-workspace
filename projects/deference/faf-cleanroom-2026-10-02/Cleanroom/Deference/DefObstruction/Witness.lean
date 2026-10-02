import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Found.LiQuoteLane.PaperWitness
import Cleanroom.Deference.DefObstruction.Tracking

/-!
# `def-obstruction` · Witness: 2a non-vacuity over FAF's LIA (T3)

The N+ witness of 2a: FAF's logical-induction algorithm over the ledger process of the paper's
deductive process `paperDP 𝗜𝚺₁` recording the **alternating table** `aAlt 0 n := if n even then
0 else 1` under next-day publication. Every certificate of `tracking_fails` is discharged — the
side of the alternating table is the parity of the day, a `UnaryRuler` (`MachineDigits.mod_two`
on the day), so the padded true/false-side families are `MachineSentenceCodes.ifZero` dispatches
between `gDiag ∘ (m − 1)` and its negation — and the instance `altPair_tracking_fails` is
**hypothesis-free**. The settlement defect there is exactly `1` on every day
(`aAlt_defect_eq_one`), and the credence defect `|aAlt 0 n − Y_n| → 1` (`altPair_defect_tendsto_one`).

**Why this is N+ and not the paper pair.** The alternating table is not constant
(`aAlt_not_const`), so both polarities of `g_n` occur (`side_aAlt_zero`, `side_aAlt_one`) — that
is the day variation; `altPair_both_polarities` (li-quote-lane's `ledgerSchedule_both_polarities`
at thresholds `−1` and `2`) holds for every `[0,1]` table and is *not* evidence of it (repair
round 1, audit N4). The reader is FAF's real construction over a real base; what makes the
certificates cheap is that the side is a *computable* function of the day — exactly what
`li-diagonal`'s K1 remark said a cheap side needs, and exactly what `paperOneWayPair` (whose side
is an LIA price compared with `½`) plausibly lacks. The table-only carrier is what makes this
witness available: `OneWayPair` would demand that the table be an inductor's prices.

**The honest N+ caveat (audit r1 N1).** `altPair` inhabits the full hypothesis package of
`tracking_fails` and realizes the defect, but it discharges the cost model by the *table's own
computability*: the reader's traders compute the parity; they never read the ledger to predict
`g_n`'s side, and the ledger's only role is to make `g_n` true or false. `latePair` makes this
concrete: with publication 100 days after the deferral reads the credence, 2a still holds with
the *same* certificates (`latePair_tracking_fails`). So the hypothesis "`A`'s side is e.c. along
`F`" is not a cost model for *reading* `A`; it is the assumption that `H`'s trader class already
contains the side — which excludes the corpus's `𝒞_H ⊊ 𝒞_A` publisher by construction. No
instance with a non-computable side exists in this package (that regime is the OPEN
`tracking_bound_fails_some_table`).

**The constant best response** `aHalf ≡ ½` (anson-003's witness, N−): `s ≡ 1`, `Y_n → 1`,
`|½ − Y_n| → ½` — the exact infimum of Lemma 2.1 attained, and still a failure of tracking
(`halfPair_defect_tendsto_half`). Its padded true-side family *is* `padG succDeferral`
(`padTrueSide_aHalf_succ`), so its certificates are `padG_codes_succ` and one more `ifZero`.

**The generator** `TablePair.ofLIA`: for any computable base, computable `[0,1]`-table and
computable schedules, FAF's LIA over the ledger process is a `TablePair` with (a) throughout
(`LIA_is_logical_inductor` on `ledgerProcess_computable`; `hworld` from
`ledgerProcess_hworld`). 2a's quantifier "for every quote sequence" is instantiated by this
constructor at every computable table.

This is the only file of the package importing `Construction.LIACompiler` directly (through
`li-quote-lane`'s `OneWay`) — though `li-diagonal`'s `Family` already pulls it in transitively,
so the separation is organisational, not a memory saving. Scope: one-way.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The generator: FAF's LIA over any computable table -/

/-- **The table-only pair from FAF's LIA**: for a computable base `DPH` free of the ledger's atoms
and with satisfiable stages, a computable `[0,1]`-valued table `a` and computable schedules `e`,
FAF's constructed market over `ledgerProcess DPH a e` is a `TablePair` — `H_inductor` by
`LIA_is_logical_inductor` on `li-quote-lane`'s `ledgerProcess_computable`, `hworld` by
`ledgerProcess_hworld`. This is `OneWayPair.ofLIA` with the publisher replaced by an arbitrary
computable table: 2a's "for every quote sequence" at every computable one.
Scope: one-way.
Source: mandate T3 (the recipe of `paperOneWayPair` "with the table swapped"); [[li-quote-lane-mandate]] T6.1
Kind: C
Fidelity: variant: plain trader class (`EfficientlyComputable`), as every FAF inductor
Hyps: (a) none -/
noncomputable def TablePair.ofLIA (DPH : DeductiveProcess) (hH : ComputableDeductiveProcess DPH)
    (a : ℕ → ℕ → ℚ) (ha : Computable fun p : ℕ × ℕ => a p.1 p.2)
    (e : ℕ → PublicationSchedule) (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2)
    (hfree : ProcessFreeOf (ledgerSchedule a e) DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hrange : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) : TablePair where
  DPH := DPH
  e := e
  a := a
  H := liaHistory (ledgerProcess DPH a e)
  H_inductor := LIA_is_logical_inductor _ (ledgerProcess_computable hH ha he)
  hworld := ledgerProcess_hworld hfree hworld
  range := hrange

/-! ## B. The alternating table -/

/-- **The alternating table** `aAlt _ n := if n even then 0 else 1` (item-independent): the
published number is `0` on even days and `1` on odd days, so the side `𝟙[a ≤ ½]` is the parity
of the day. Computable, `[0,1]`-valued, not constant, both polarities realized.
Scope: one-way (the table alone).
Source: mandate T3
Kind: D
Fidelity: n/a (the witness's own object)
Hyps: n/a -/
def aAlt (_ n : ℕ) : ℚ := if n % 2 = 0 then 0 else 1

/-- The alternating table is computable (primitive recursive in `(j, n)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aAlt_computable : Computable fun p : ℕ × ℕ => aAlt p.1 p.2 := by
  have h : Primrec fun p : ℕ × ℕ => aAlt p.1 p.2 := by
    unfold aAlt
    exact Primrec.ite
      (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
        (Primrec.const 0))
      (Primrec.const 0) (Primrec.const 1)
  exact h.to_comp

/-- The alternating table is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aAlt_range (j n : ℕ) : 0 ≤ aAlt j n ∧ aAlt j n ≤ 1 := by
  unfold aAlt; split_ifs <;> norm_num

/-- The alternating table is at or below `½` exactly on even days.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aAlt_le_half_iff (n : ℕ) : aAlt 0 n ≤ 1 / 2 ↔ n % 2 = 0 := by
  unfold aAlt
  split_ifs with h <;> norm_num [h]

/-- **The side of the alternating table is the parity of the day.**
Source: mandate T3 ("`side (aAlt 0) n = 𝟙[Even n]`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem side_aAlt (n : ℕ) : side (aAlt 0) n = if n % 2 = 0 then 1 else 0 := by
  unfold side
  by_cases h : n % 2 = 0
  · rw [if_pos ((aAlt_le_half_iff n).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((aAlt_le_half_iff n).1 h')), if_neg h]

/-- Both polarities of `g_n` are realized on the alternating table: `g_0` true, `g_1` false. (A
fact about the table supporting `altPair`'s N+ grade, not itself a witness — audit r2 N5.)
Source: mandate T3 (non-degeneracy)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem side_aAlt_zero : side (aAlt 0) 0 = 1 := by rw [side_aAlt]; rfl

/-- `side_aAlt_one`.
Source: mandate T3 (non-degeneracy)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem side_aAlt_one : side (aAlt 0) 1 = 0 := by rw [side_aAlt]; rfl

/-- The alternating table is not constant.
Source: mandate T3 (non-degeneracy)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem aAlt_not_const : aAlt 0 0 ≠ aAlt 0 1 := by unfold aAlt; norm_num

/-- **The settlement defect of the alternating table is exactly `1` on every day**: the quote is
`0` where the side is `1` and `1` where the side is `0`.
Source: mandate T3 ("in fact the pointwise defect is `|aAlt 0 n − s_n| = 1`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem aAlt_defect_eq_one (n : ℕ) : |(aAlt 0 n : ℝ) - side (aAlt 0) n| = 1 := by
  rw [side_aAlt]
  unfold aAlt
  by_cases h : n % 2 = 0 <;> simp [h]

/-! ### The certificates at `succDeferral` -/

/-- The padded true-side family of the alternating table at `succDeferral`, in closed form:
`⊤` on day `0`, then `g_{m−1}` on days with `m − 1` even and `∼g_{m−1}` otherwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem padTrueSide_aAlt_succ (m : ℕ) : padTrueSide aAlt succDeferral m =
    if m = 0 then ⊤ else if (m - 1) % 2 = 0 then gDiag (m - 1) else ∼ gDiag (m - 1) := by
  cases m with
  | zero =>
    unfold padTrueSide
    rw [dif_neg, if_pos rfl]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    have h := padTrueSide_apply aAlt succDeferral (fun _ _ hab => Nat.succ_injective hab) k
    have h2 : trueSide aAlt k = if k % 2 = 0 then gDiag k else ∼ gDiag k := by
      unfold trueSide
      by_cases hk : k % 2 = 0
      · rw [if_pos ((aAlt_le_half_iff k).2 hk), if_pos hk]
      · rw [if_neg (fun h' => hk ((aAlt_le_half_iff k).1 h')), if_neg hk]
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, ← h2]
    exact h

/-- The padded false-side family of the alternating table at `succDeferral`, in closed form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem padFalseSide_aAlt_succ (m : ℕ) : padFalseSide aAlt succDeferral m =
    if m = 0 then ∼ (⊤ : Sentence)
    else if (m - 1) % 2 = 0 then ∼ gDiag (m - 1) else gDiag (m - 1) := by
  cases m with
  | zero =>
    unfold padFalseSide
    rw [dif_neg, if_pos rfl]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    have h := padFalseSide_apply aAlt succDeferral (fun _ _ hab => Nat.succ_injective hab) k
    have h2 : falseSide aAlt k = if k % 2 = 0 then ∼ gDiag k else gDiag k := by
      unfold falseSide
      by_cases hk : k % 2 = 0
      · rw [if_pos ((aAlt_le_half_iff k).2 hk), if_pos hk]
      · rw [if_neg (fun h' => hk ((aAlt_le_half_iff k).1 h')), if_neg hk]
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, ← h2]
    exact h

/-- The parity of `m − 1` is a unary ruler (FAF's `MachineDigits.mod_two` on the ruler `m ↦ m − 1`).
Source: none: infrastructure (FAF `MachineDigits.mod_two`; `li-diagonal` `evenIndicator_pgenerable`'s recipe)
Kind: L
Fidelity: n/a -/
theorem predParity_ruler : UnaryRuler (fun m : ℕ => (m - 1) % 2) :=
  (MachineDigits.ofUnaryRuler (UnaryRuler.id.sub (UnaryRuler.const 1))).mod_two

/-- `gDiag` shifted by one day is e.c.
Source: none: infrastructure (`li-diagonal` `gDiag_codes` composed with the ruler `m ↦ m − 1`)
Kind: L
Fidelity: n/a -/
theorem gDiag_pred_codes : MachineSentenceCodes (fun m : ℕ => gDiag (m - 1)) :=
  MachineSentenceCodes.comp gDiag_codes (UnaryRuler.id.sub (UnaryRuler.const 1))

/-- **The cost model is discharged for the alternating table (true side)**: `hR` at
`succDeferral`, by FAF's `ifZero` on the day ruler (day `0` → `⊤`) and on the parity ruler
(`gDiag ∘ pred` vs its negation).
Source: mandate T3 (certificates)
Kind: C
Fidelity: n/a (a certificate)
Hyps: (a) none -/
theorem padTrueSide_aAlt_codes : MachineSentenceCodes (padTrueSide aAlt succDeferral) := by
  have htop : MachineSentenceCodes (fun _ : ℕ => (⊤ : Sentence)) :=
    MachineSentenceCodes.const (⊤ : Sentence)
  have hinner : MachineSentenceCodes
      (fun m : ℕ => if (m - 1) % 2 = 0 then gDiag (m - 1) else ∼ gDiag (m - 1)) :=
    MachineSentenceCodes.ifZero gDiag_pred_codes gDiag_pred_codes.neg predParity_ruler
  have h := MachineSentenceCodes.ifZero htop hinner UnaryRuler.id
  refine MachineSentenceCodes.of_eq h fun m => ?_
  simp only [padTrueSide_aAlt_succ]

/-- **The cost model is discharged for the alternating table (false side)**: `hR'` at
`succDeferral`.
Source: mandate T3 (certificates)
Kind: C
Fidelity: n/a (a certificate)
Hyps: (a) none -/
theorem padFalseSide_aAlt_codes : MachineSentenceCodes (padFalseSide aAlt succDeferral) := by
  have hbot : MachineSentenceCodes (fun _ : ℕ => (∼ (⊤ : Sentence) : Sentence)) :=
    MachineSentenceCodes.const _
  have hinner : MachineSentenceCodes
      (fun m : ℕ => if (m - 1) % 2 = 0 then ∼ gDiag (m - 1) else gDiag (m - 1)) :=
    MachineSentenceCodes.ifZero gDiag_pred_codes.neg gDiag_pred_codes predParity_ruler
  have h := MachineSentenceCodes.ifZero hbot hinner UnaryRuler.id
  refine MachineSentenceCodes.of_eq h fun m => ?_
  simp only [padFalseSide_aAlt_succ]

/-! ### The pair -/

/-- **The alternating pair** (headline 2, N+): FAF's LIA over `ledgerProcess (paperDP 𝗜𝚺₁) aAlt
succ` — the paper's own deductive process over `IΣ₁`, the alternating table, next-day
publication. Every field from FAF's facts (`paperDP_computable`, `paperDP_cleanroomFree`,
`paperDP_hworld`, `LIA_is_logical_inductor`).
Scope: one-way.
Source: mandate T3 (anson-003's witness, made N+)
Kind: N+
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable def altPair : TablePair :=
  TablePair.ofLIA (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) aAlt aAlt_computable
    (fun _ => PublicationSchedule.succ) succSchedule_computable
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁) aAlt_range

/-- `altPair_a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem altPair_a : altPair.a = aAlt := rfl

/-- The alternating pair's reader is FAF's LIA over the ledger process.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem altPair_H :
    altPair.H = liaHistory (ledgerProcess (paperDP 𝗜𝚺₁) aAlt (fun _ => PublicationSchedule.succ)) :=
  rfl

/-- **Both polarities occur in the alternating pair's ledger** (`r = −1` affirmed, `r = 2`
denied), for every item and day. This is li-quote-lane's `ledgerSchedule_both_polarities` and
holds for *every* `[0,1]` table, constant ones included; it is a sanity check on the ledger, not
evidence that the table varies (for that: `aAlt_not_const`, `side_aAlt_zero`/`side_aAlt_one`).
Source: mandate T3 (non-degeneracy; `li-quote-lane` `ledgerSchedule_both_polarities`)
Kind: L (instance; every table has it)
Fidelity: n/a
Hyps: (a) none -/
theorem altPair_both_polarities (j n : ℕ) :
    (∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (-1 : ℚ)), true) ∈
        (ledgerSchedule altPair.a altPair.e).lits s) ∧
      ∃ s, (ledgerFamily, ledgerPayload j n (Encodable.encode (2 : ℚ)), false) ∈
        (ledgerSchedule altPair.a altPair.e).lits s :=
  ledgerSchedule_both_polarities _ _ aAlt_range j n

/-- **Lemma B on the alternating pair, hypothesis-free**: `|𝔼^H_{n+1}(𝟙 g_n) − s_n| → 0`.
Source: mandate T3; [[lean-deference-2-inventory]] 007
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem altPair_Y_sub_side :
    Tendsto (fun n => |altPair.Y succDeferral n - side (aAlt 0) n|) atTop (𝓝 0) :=
  lemmaB_expect_table altPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padTrueSide_aAlt_codes padFalseSide_aAlt_codes padG_codes_succ

/-- **2a on the alternating pair, hypothesis-free (headline 2)**: for every `ε > 0`, eventually
`½ − ε ≤ |aAlt 0 n − 𝔼^H_{n+1}(𝟙 g_n)|`, with `H` FAF's LIA over the paper process plus the
alternating ledger. Every certificate of `tracking_fails` discharged: (a) throughout.
Scope: one-way.
Source: mandate T3; [[self-referential-settlement-target]] §10 ("Non-vacuity", anson-003)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem altPair_tracking_fails :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, 1 / 2 - ε ≤ |(aAlt 0 n : ℝ) - altPair.Y succDeferral n| :=
  tracking_fails altPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padTrueSide_aAlt_codes padFalseSide_aAlt_codes padG_codes_succ

/-- **The credence defect on the alternating pair tends to `1`**, twice the bound: the quote and
the realized side are always `1` apart, and the reader's credence tracks the side.
Scope: one-way.
Source: mandate T3, T5(i)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem altPair_defect_tendsto_one :
    Tendsto (fun n => |(aAlt 0 n : ℝ) - altPair.Y succDeferral n|) atTop (𝓝 1) := by
  have h := altPair_Y_sub_side
  have h2 : Tendsto (fun n => |(aAlt 0 n : ℝ) - altPair.Y succDeferral n| - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) h
    rw [Real.norm_eq_abs, ← aAlt_defect_eq_one n]
    calc |(|(aAlt 0 n : ℝ) - altPair.Y succDeferral n| - |(aAlt 0 n : ℝ) - side (aAlt 0) n|)|
        ≤ |((aAlt 0 n : ℝ) - altPair.Y succDeferral n) - ((aAlt 0 n : ℝ) - side (aAlt 0) n)| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |altPair.Y succDeferral n - side (aAlt 0) n| := by
          rw [abs_sub_comm]; congr 1; ring
  have h3 := h2.add_const 1
  rw [zero_add] at h3
  refine h3.congr fun n => ?_
  ring

/-- **2a as `¬ Tracking` on the alternating pair, hypothesis-free.**
Scope: one-way.
Source: mandate T3
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem altPair_not_tracking : ¬ ((fun n => (aAlt 0 n : ℝ)) ≈ₙ altPair.Y succDeferral) :=
  not_tracking altPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padTrueSide_aAlt_codes padFalseSide_aAlt_codes padG_codes_succ

/-! ## C. The constant best response `½` -/

/-- **The constant best-response table** `aHalf ≡ ½`: the source's non-vacuity witness
(anson-003), the one quote whose settlement defect is exactly the infimum `½`.
Scope: one-way (the table alone).
Source: [[self-referential-settlement-target]] §2.3, §10 ("Non-vacuity"); anson-003
Kind: D
Fidelity: exact
Hyps: n/a -/
def aHalf (_ _ : ℕ) : ℚ := 1 / 2

/-- The constant table is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aHalf_computable : Computable fun p : ℕ × ℕ => aHalf p.1 p.2 :=
  (Primrec.const (1 / 2 : ℚ)).to_comp

/-- The constant table is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem aHalf_range (j n : ℕ) : 0 ≤ aHalf j n ∧ aHalf j n ≤ 1 := by unfold aHalf; norm_num

/-- The side of the constant table is identically `1` (ties → `g_n` true).
Source: mandate T3 ("`s_n ≡ 1`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem side_aHalf (n : ℕ) : side (aHalf 0) n = 1 := by
  unfold side aHalf; rw [if_pos le_rfl]

/-- On the constant table the padded true-side family **is** `li-diagonal`'s padded `g` family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem padTrueSide_aHalf_succ (m : ℕ) :
    padTrueSide aHalf succDeferral m = padG succDeferral m := by
  rw [padG_succ]
  cases m with
  | zero =>
    unfold padTrueSide
    rw [dif_neg, if_pos rfl]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    have h := padTrueSide_apply aHalf succDeferral (fun _ _ hab => Nat.succ_injective hab) k
    have h2 : trueSide aHalf k = gDiag k := by
      unfold trueSide aHalf; rw [if_pos le_rfl]
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, ← h2]
    exact h

/-- The padded false-side family of the constant table at `succDeferral`, in closed form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem padFalseSide_aHalf_succ (m : ℕ) : padFalseSide aHalf succDeferral m =
    if m = 0 then ∼ (⊤ : Sentence) else ∼ gDiag (m - 1) := by
  cases m with
  | zero =>
    unfold padFalseSide
    rw [dif_neg, if_pos rfl]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    have h := padFalseSide_apply aHalf succDeferral (fun _ _ hab => Nat.succ_injective hab) k
    have h2 : falseSide aHalf k = ∼ gDiag k := by
      unfold falseSide aHalf; rw [if_pos le_rfl]
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, ← h2]
    exact h

/-- The constant table's true-side certificate is `padG_codes_succ`.
Source: mandate T3 (certificates)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padTrueSide_aHalf_codes : MachineSentenceCodes (padTrueSide aHalf succDeferral) :=
  MachineSentenceCodes.of_eq padG_codes_succ fun m => (padTrueSide_aHalf_succ m).symm

/-- The constant table's false-side certificate.
Source: mandate T3 (certificates)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padFalseSide_aHalf_codes : MachineSentenceCodes (padFalseSide aHalf succDeferral) := by
  have hbot : MachineSentenceCodes (fun _ : ℕ => (∼ (⊤ : Sentence) : Sentence)) :=
    MachineSentenceCodes.const _
  have h := MachineSentenceCodes.ifZero hbot gDiag_pred_codes.neg UnaryRuler.id
  refine MachineSentenceCodes.of_eq h fun m => ?_
  simp only [padFalseSide_aHalf_succ]

/-- **The constant-½ pair** (N−: a constant table): FAF's LIA over the paper process plus the
ledger of the constant best response.
Scope: one-way.
Source: [[self-referential-settlement-target]] §10 ("Non-vacuity"); anson-003
Kind: N−
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable def halfPair : TablePair :=
  TablePair.ofLIA (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) aHalf aHalf_computable
    (fun _ => PublicationSchedule.succ) succSchedule_computable
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁) aHalf_range

/-- `halfPair_a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem halfPair_a : halfPair.a = aHalf := rfl

/-- **On the constant best response the reader's deferred credence of `g_n` tends to `1`**
(`g_n` is true every day).
Scope: one-way.
Source: mandate T3 ("`Y_n → 1`"); anson-003
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem halfPair_Y_tendsto_one : Tendsto (halfPair.Y succDeferral) atTop (𝓝 1) := by
  have h := lemmaB_expect_table halfPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padTrueSide_aHalf_codes padFalseSide_aHalf_codes padG_codes_succ
  simp only [halfPair_a, side_aHalf] at h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using h

/-- **The best any quote achieves is still a failure**: on the constant best response the
credence defect tends to exactly `½`, the infimum of Lemma 2.1.
Scope: one-way.
Source: [[self-referential-settlement-target]] §2.3 ("the best any quote achieves is residual exactly `½` … still a failure of tracking"); anson-003
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem halfPair_defect_tendsto_half :
    Tendsto (fun n => |(aHalf 0 n : ℝ) - halfPair.Y succDeferral n|) atTop (𝓝 (1 / 2)) := by
  have h := ((tendsto_const_nhds (x := (1 / 2 : ℝ))).sub halfPair_Y_tendsto_one).abs
  have e : |(1 / 2 : ℝ) - 1| = 1 / 2 := by norm_num
  rw [e] at h
  refine h.congr fun n => ?_
  norm_num [aHalf]

/-- **2a on the constant-½ pair, hypothesis-free** (N−).
Scope: one-way.
Source: mandate T3; anson-003
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem halfPair_tracking_fails :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, 1 / 2 - ε ≤ |(aHalf 0 n : ℝ) - halfPair.Y succDeferral n| :=
  tracking_fails halfPair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padTrueSide_aHalf_codes padFalseSide_aHalf_codes padG_codes_succ

/-- **The source's limit-agreement example, refuted with no hypothesis** (T6 on the constant
table). [[no-timely-pointwise-tower]] §6 says the diagonal "is consistent with" limit agreement
"(both sides sit at `½` in the limit)"; on the constant-`½` table — one instance (the natural
one) of what that parenthetical describes, `lim a = lim Y = ½` — `a ≡ ½` and the reader's
deferred credence tends to `1`, so `a → ½`
and `Y → ½` cannot both hold. Unlike `limit_agreement_fails` this needs no certificate: the
constant table's certificates are discharged. For a table with a non-e.c. side the question is
open (F-Oracle's conjecture would allow `a → ½`, `Y → ½`): see findings F-LimitAgreement.
Scope: one-way (the constant pair).
Source: [[no-timely-pointwise-tower]] §6 (anson-015), the parenthetical example; audit r1 probe `HalfTableLimit`
Kind: N− (constant table; hypothesis-free)
Fidelity: exact (the note's own example)
Hyps: (a) none -/
theorem halfPair_no_limit_agreement_at_half :
    ¬ (Tendsto (fun n => (aHalf 0 n : ℝ)) atTop (𝓝 (1 / 2)) ∧
        Tendsto (halfPair.Y succDeferral) atTop (𝓝 (1 / 2))) := by
  rintro ⟨-, hY⟩
  have h := tendsto_nhds_unique hY halfPair_Y_tendsto_one
  norm_num at h

/-! ## E. Late publication: the certificates replace reading by computing (F-Regimes, concrete) -/

/-- **Publication 100 days late**: `e n := n + 100`.
Source: audit r1 probe `LatePublication`; findings F-Regimes
Kind: D
Fidelity: n/a
Hyps: n/a -/
def lateSchedule : PublicationSchedule := ⟨fun n => n + 100, fun n => by omega⟩

/-- The late schedule is computable (as `succSchedule_computable`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lateSchedule_computable :
    Computable fun p : ℕ × ℕ => ((fun _ : ℕ => lateSchedule) p.1).e p.2 :=
  (Primrec.nat_add.comp Primrec.snd (Primrec.const 100)).to_comp

/-- **The alternating pair with late publication**: FAF's LIA over the paper process plus the
alternating ledger, the quote entering the process 100 days after the day it is about.
Scope: one-way.
Source: audit r1 probe `LatePublication`; findings F-Regimes
Kind: N+
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable def latePair : TablePair :=
  TablePair.ofLIA (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁) aAlt aAlt_computable
    (fun _ => lateSchedule) lateSchedule_computable
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁) aAlt_range

/-- **2a with the credence read 99 days before the quote is published**: on `latePair`, `Y_n` is
read at day `n + 1` while the ledger receives `a_n` at day `n + 100`, and the bound holds
hypothesis-free with the *same* certificates as `altPair_tracking_fails` — they mention neither
`e` nor the process. The reader is not reading the quote; its traders compute the side. This is
the sense in which the N+ witness's cost model is degenerate (module docstring) and the concrete
form of F-Regimes: over FAF the publication schedule does not enter 2a.
Scope: one-way.
Source: audit r1 probe `LatePublication`; findings F-Regimes; vq-wiki-045 (the regime split, refuted for e.c. sides)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem latePair_tracking_fails :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, 1 / 2 - ε ≤ |(aAlt 0 n : ℝ) - latePair.Y succDeferral n| :=
  tracking_fails latePair succDeferral (fun _ _ hab => Nat.succ_injective hab)
    padTrueSide_aAlt_codes padFalseSide_aAlt_codes padG_codes_succ

end Cleanroom.Deference.DefObstruction
