import Cleanroom.Bli.BliTransfer.AttemptA.WitnessOracle
import Cleanroom.Bli.BliTransfer.AttemptA.Computable
import Cleanroom.Bli.BliTransfer.AttemptA.Witnesses
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-transfer` (attempt A) · WitnessLia: non-vacuity over FAF's logical inductor (T1.5)

The N+ for the transfer theorem, with the full hypothesis package inhabited by the real
construction: `Q := liaHistory DP` with `LIA_is_logical_inductor DP hDP` (`thm:lia`), and the
witness map `wExpr` — on day `0`, every atom of the run's family `7` (tag `wTag`) is re-priced to
`1/2` — with `wOv DP` (`1/2` where the map fires, `Q`'s own exact quote elsewhere: Tier B).

* `wRunAgrees`: the run-level lookup of `WitnessOracle.lean` agrees with `wExpr` on **every**
  spelling `parseRpn` accepts (canonical run, Gödel escape, structured escape — the last never
  denotes a family atom), by case analysis on `parseRpn_cons`.
* `wMap DP : ExprMap (liaHistory DP) (wOv DP)`: every atom is large on day `0`
  (`three_le_tokenSize_atom`, `sizeBound 0 = 2`), so `fires` holds without a size test.
* `wCertificate : SpliceCertificate wExpr` and `wOv_computableTable`: the instance's two
  obligations, discharged.
* **Non-degeneracy, proved not assumed**: the day-`0` LIA state is a finite table quoting `0` off
  it (`RationalBeliefState.quote_eq_zero_of_not_mem`), and the family is infinite, so some family
  atom is priced `0` by `Q` and `1/2` by the overlay (`overlay_ne_lia`). And the trader side: the
  efficiently computable `familyReader` (reading `price ⌜a⌝ 0` for a family atom every day) has a
  splice that is not the identity (`familyReader_splice_ne`).
* `witness_isLogicalInductor`: the transfer theorem at the witness, for every computable process,
  and at `paperDP 𝗜𝚺₁` (with `paperDP_hworld` supplying the process's consistent worlds, so the
  criterion is not vacuous there — mandate trap (v)).

Scope note (disclosed): the witness map fires on day `0` only, where every atom is large, so its
oracle needs no comparison of a run's length with `2^{2^k}`; a map firing on large family atoms of
every day `k` would need that comparison (a capped double-exponential in unary) on top of the
family test. This is the shape `bli-assemble`'s oracle extends.

Sources: mandate T1.5; FAF `Construction/LIACompiler.lean:3890`, `Construction/LIA.lean`,
`Construction/MarketMaker.lean:672–710`, `Construction/Paper/TheoremDP.lean`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The witness map -/

/-- **The witness expression map**: on day `0`, every family-`wTag` atom is re-priced to the
constant `1/2`; nothing else fires.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def wExpr (k : ℕ) (ψ : Sentence) : Option EF :=
  match ψ with
  | Formula.atom a => if k = 0 ∧ a.unpair.1 = wTag then some (EF.const (1 / 2)) else none
  | _ => none

@[simp] lemma wExpr_atom (k a : ℕ) :
    wExpr k (Formula.atom a) = if k = 0 ∧ a.unpair.1 = wTag then some (EF.const (1 / 2)) else none :=
  rfl
@[simp] lemma wExpr_falsum (k : ℕ) : wExpr k Formula.falsum = none := rfl
@[simp] lemma wExpr_imp (k : ℕ) (φ ψ : Sentence) : wExpr k (Formula.imp φ ψ) = none := rfl
@[simp] lemma wExpr_and (k : ℕ) (φ ψ : Sentence) : wExpr k (Formula.and φ ψ) = none := rfl
@[simp] lemma wExpr_or (k : ℕ) (φ ψ : Sentence) : wExpr k (Formula.or φ ψ) = none := rfl

/-- The bodies' rank discipline: `const` has rank `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wExpr_rank : ∀ k ψ e, wExpr k ψ = some e → e.rank ≤ k := by
  intro k ψ e h
  cases ψ with
  | atom a =>
      simp only [wExpr_atom] at h
      split_ifs at h with hc
      · obtain rfl := Option.some.inj h
        simp [EF.rank]
  | falsum => simp [wExpr] at h
  | imp _ _ => simp [wExpr] at h
  | and _ _ => simp [wExpr] at h
  | or _ _ => simp [wExpr] at h

/-- Every atom is large on day `0`.
Source: none: infrastructure (`three_le_tokenSize_atom`, `sizeBound 0 = 2`)
Kind: L
Fidelity: n/a -/
lemma atom_not_smallOn_zero (a : ℕ) : ¬ SmallOn 0 (Formula.atom a) := by
  unfold SmallOn
  have h := three_le_tokenSize_atom a
  have h2 : sizeBound 0 = 2 := by norm_num [sizeBound]
  omega

/-! ## Run-level agreement on every spelling -/

/-- Foundation's decoder at a successor code with tag `1` is the atom of the payload.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ofNat_tag_one {e : ℕ} (h : e.unpair.1 = 1) :
    (LO.Propositional.Formula.ofNat (e + 1) : Option Sentence) = some (Formula.atom e.unpair.2) := by
  simp [LO.Propositional.Formula.ofNat, h]

/-- The witness map at a decoded code, in terms of the code alone.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wExpr_decode {c : ℕ} {φ : Sentence}
    (h : (LO.Propositional.Formula.ofNat c : Option Sentence) = some φ) (D : ℕ) :
    wExpr D φ = if D = 0 ∧ 1 ≤ c ∧ (c - 1).unpair.1 = 1 ∧ (c - 1).unpair.2.unpair.1 = wTag
      then some (EF.const (1 / 2)) else none := by
  cases c with
  | zero => simp [LO.Propositional.Formula.ofNat] at h
  | succ e =>
      simp only [Nat.add_sub_cancel, le_add_iff_nonneg_left, zero_le, true_and]
      rcases hv : e.unpair.1 with _ | _ | _ | _ | _ | n
      · simp [LO.Propositional.Formula.ofNat, hv] at h
        subst h
        rw [if_neg (fun hc => by omega)]
        rfl
      · simp [LO.Propositional.Formula.ofNat, hv] at h
        subst h
        simp
      · cases hL : (LO.Propositional.Formula.ofNat e.unpair.2.unpair.1 : Option Sentence) with
        | none => simp [LO.Propositional.Formula.ofNat, hv, hL] at h
        | some a =>
            cases hR : (LO.Propositional.Formula.ofNat e.unpair.2.unpair.2 : Option Sentence) with
            | none => simp [LO.Propositional.Formula.ofNat, hv, hL, hR] at h
            | some b =>
                simp [LO.Propositional.Formula.ofNat, hv, hL, hR] at h
                subst h
                rw [if_neg (fun hc => by omega)]
                rfl
      · cases hL : (LO.Propositional.Formula.ofNat e.unpair.2.unpair.1 : Option Sentence) with
        | none => simp [LO.Propositional.Formula.ofNat, hv, hL] at h
        | some a =>
            cases hR : (LO.Propositional.Formula.ofNat e.unpair.2.unpair.2 : Option Sentence) with
            | none => simp [LO.Propositional.Formula.ofNat, hv, hL, hR] at h
            | some b =>
                simp [LO.Propositional.Formula.ofNat, hv, hL, hR] at h
                subst h
                rw [if_neg (fun hc => by omega)]
                rfl
      · cases hL : (LO.Propositional.Formula.ofNat e.unpair.2.unpair.1 : Option Sentence) with
        | none => simp [LO.Propositional.Formula.ofNat, hv, hL] at h
        | some a =>
            cases hR : (LO.Propositional.Formula.ofNat e.unpair.2.unpair.2 : Option Sentence) with
            | none => simp [LO.Propositional.Formula.ofNat, hv, hL, hR] at h
            | some b =>
                simp [LO.Propositional.Formula.ofNat, hv, hL, hR] at h
                subst h
                rw [if_neg (fun hc => by omega)]
                rfl
      · simp [LO.Propositional.Formula.ofNat, hv] at h

/-- A structured escape denotes a tag-`5` atom.
Source: none: infrastructure (from `parseStructuredPaperPrime`'s definition)
Kind: L
Fidelity: n/a -/
lemma parseStructuredPaperPrime_atom {payload : List ℕ} {φ : Sentence} {rest : List ℕ}
    (h : parseStructuredPaperPrime payload = some (φ, rest)) :
    ∃ x, φ = Formula.atom (Nat.pair 5 x) := by
  cases payload with
  | nil => simp [parseStructuredPaperPrime] at h
  | cons polarity framed =>
      simp only [parseStructuredPaperPrime] at h
      split_ifs at h with hpol
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨p, -, h⟩ := h
        split at h <;> (try split_ifs at h) <;> (try split at h) <;> first
          | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨_, rfl⟩)
          | exact absurd h (by simp)

/-- A family run never starts with a token in `{2, 3, 4}`, nor with `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma familyRun_cons_small {t : ℕ} (h5 : t < 5) (h1 : t ≠ 1) (rest : List ℕ) :
    familyRun (t :: rest) = false := by
  match rest with
  | [] => simp [familyRun]; omega
  | [c] => simp [familyRun, h1]
  | _ :: _ :: _ => rfl

/-- The witness lookup agrees with the witness map on every spelling `parseRpn` accepts.
Source: mandate T1.5 (the certificate "quantified over every spelling")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem wRunAgrees : RunAgrees wExpr wExprRun := by
  intro b φ hb D
  cases b with
  | nil => simp at hb
  | cons t rest =>
      rw [List.length_cons, parseRpn_cons] at hb
      by_cases h0 : t = 0
      · subst h0
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp [wExprRun, familyRun, wExpr]
      by_cases h1 : t = 1
      · subst h1
        rw [if_neg h0, if_pos rfl] at hb
        match rest, hb with
        | [], hb => simp at hb
        | 0 :: payload, hb =>
            obtain ⟨x, rfl⟩ := parseStructuredPaperPrime_atom hb
            have hexpr : wExpr D (Formula.atom (Nat.pair 5 x)) = none := by
              simp [wTag, cleanroomBaseTag]
            rw [hexpr]
            simp only [Option.map_none, wExprRun]
            have hfam : familyRun (1 :: 0 :: payload) = false := by
              cases payload <;> simp [familyRun]
            simp [hfam]
        | (c + 1) :: tail, hb =>
            simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hb
            obtain ⟨φ', hdec, rfl, rfl⟩ := hb
            have hdec' : (LO.Propositional.Formula.ofNat (c + 1) : Option Sentence) = some φ' := hdec
            rw [wExpr_decode hdec' D]
            simp only [wExprRun, familyRun, Nat.add_sub_cancel, le_add_iff_nonneg_left, zero_le,
              true_and]
            by_cases hD : D = 0
            · by_cases hfam : (c.unpair.1 = 1 ∧ c.unpair.2.unpair.1 = wTag)
              · simp [hD, hfam, wBody, EF.rawSerialize]
              · simp [hD, hfam]
            · simp [hD]
      by_cases h2 : t = 2
      · subst h2
        rw [if_neg h0, if_neg h1, if_pos rfl] at hb
        simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨p, -, q, -, rfl, -⟩ := hb
        simp [wExprRun, wExpr, familyRun_cons_small (by norm_num) h1]
      by_cases h3 : t = 3
      · subst h3
        rw [if_neg h0, if_neg h1, if_neg h2, if_pos rfl] at hb
        simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨p, -, q, -, rfl, -⟩ := hb
        simp [wExprRun, wExpr, familyRun_cons_small (by norm_num) h1]
      by_cases h4 : t = 4
      · subst h4
        rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos rfl] at hb
        simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨p, -, q, -, rfl, -⟩ := hb
        simp [wExprRun, wExpr, familyRun_cons_small (by norm_num) h1]
      · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have h5 : 5 ≤ t := by omega
        simp only [wExprRun, familyRun, wExpr_atom]
        by_cases hD : D = 0
        · by_cases htag : (t - 5).unpair.1 = wTag
          · simp [hD, htag, h5, wBody, EF.rawSerialize]
          · simp [hD, htag]
        · simp [hD]

/-- **The witness certificate.**
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
noncomputable def wCertificate : SpliceCertificate wExpr where
  exprRun := wExprRun
  agrees := wRunAgrees
  oracle := wOracle

/-! ## The expression map over the LIA -/

/-- The witness re-pricing: `1/2` where the map fires, the LIA's own exact quote elsewhere.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
noncomputable def wOv (DP : DeductiveProcess) (k : ℕ) (ψ : Sentence) : ℚ :=
  if (wExpr k ψ).isSome then 1 / 2 else liaQuote DP k ψ

/-- **The witness expression map over the LIA.**
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
noncomputable def wMap (DP : DeductiveProcess) : ExprMap (liaHistory DP) (wOv DP) where
  expr := wExpr
  closed := by
    intro k ψ e h
    cases ψ with
    | atom a =>
        simp only [wExpr_atom] at h
        split_ifs at h with hc
        · obtain rfl := Option.some.inj h
          rfl
    | falsum => simp [wExpr] at h
    | imp _ _ => simp [wExpr] at h
    | and _ _ => simp [wExpr] at h
    | or _ _ => simp [wExpr] at h
  leaves := by
    intro k ψ e h
    cases ψ with
    | atom a =>
        simp only [wExpr_atom] at h
        split_ifs at h with hc
        · obtain rfl := Option.some.inj h
          simp [EF.priceQueries]
    | falsum => simp [wExpr] at h
    | imp _ _ => simp [wExpr] at h
    | and _ _ => simp [wExpr] at h
    | or _ _ => simp [wExpr] at h
  fires := by
    intro k ψ e h
    cases ψ with
    | atom a =>
        simp only [wExpr_atom] at h
        split_ifs at h with hc
        · obtain rfl := Option.some.inj h
          obtain ⟨rfl, htag⟩ := hc
          rw [overlay_large (atom_not_smallOn_zero a)]
          simp [wOv, EF.denote, EF.denoteWith, htag]
    | falsum => simp [wExpr] at h
    | imp _ _ => simp [wExpr] at h
    | and _ _ => simp [wExpr] at h
    | or _ _ => simp [wExpr] at h
  silent := by
    intro k ψ h
    left
    simp only [wOv, h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rfl
  ov_range := by
    intro k ψ
    unfold wOv
    split_ifs
    · norm_num
    · exact (liaStates DP k).quote_mem_Icc ψ

/-! ## The re-pricing is a computable table -/

/-- The family test on a day and a sentence code.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def famCode (n c : ℕ) : Bool :=
  decide (n = 0 ∧ 1 ≤ c ∧ (c - 1).unpair.1 = 1 ∧ (c - 1).unpair.2.unpair.1 = wTag)

/-- The family test is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma famCode_prim : Primrec₂ famCode := by
  have hc : Primrec fun p : ℕ × ℕ => p.2 - 1 := pSub Primrec.snd (Primrec.const 1)
  have hu1 : Primrec fun p : ℕ × ℕ => (p.2 - 1).unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hu2 : Primrec fun p : ℕ × ℕ => (p.2 - 1).unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hc)))
  have h : PrimrecPred fun p : ℕ × ℕ =>
      p.1 = 0 ∧ 1 ≤ p.2 ∧ (p.2 - 1).unpair.1 = 1 ∧ (p.2 - 1).unpair.2.unpair.1 = wTag :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).and
      ((Primrec.nat_le.comp (Primrec.const 1) Primrec.snd).and
        ((Primrec.eq.comp hu1 (Primrec.const 1)).and (Primrec.eq.comp hu2 (Primrec.const wTag))))
  obtain ⟨_, h⟩ := h
  refine Primrec.of_eq h (fun p => ?_)
  simp only [famCode]
  exact decide_eq_decide.mpr Iff.rfl

/-- The family test at a sentence's own code is whether the witness map fires.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma famCode_encode (n : ℕ) (ψ : Sentence) :
    famCode n (Encodable.encode ψ) = (wExpr n ψ).isSome := by
  have h := wExpr_decode (c := Encodable.encode ψ) (φ := ψ)
    (LO.Propositional.Formula.ofNat_toNat ψ) n
  rw [h]
  simp only [famCode]
  by_cases hc : n = 0 ∧ 1 ≤ Encodable.encode ψ ∧ (Encodable.encode ψ - 1).unpair.1 = 1 ∧
      (Encodable.encode ψ - 1).unpair.2.unpair.1 = wTag
  · simp [hc]
  · simp [hc]

/-- The witness re-pricing is a computable table.
Source: mandate T1.5 (the instance's obligation `hov`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem wOv_computableTable (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP) :
    ComputableTable (wOv DP) := by
  obtain ⟨tabQ, hex, hcomp⟩ := ComputableMarket.exists_computableTable
    (LIA_is_logical_inductor DP hDP).marketComputable
  refine ⟨fun n c => if famCode n c then 1 / 2 else tabQ n c, ?_, ?_⟩
  · intro n ψ
    simp only [wOv, famCode_encode]
    split_ifs
    · rfl
    · apply Rat.cast_injective (α := ℝ)
      rw [← hex n ψ]
      rfl
  · have hc : Computable fun z : ℕ => famCode z.unpair.1 z.unpair.2 :=
      (famCode_prim.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
    have h := Computable.cond hc (Computable.const (Encodable.encode (1 / 2 : ℚ))) hcomp
    refine h.of_eq fun z => ?_
    simp only [Bool.cond_eq_ite]
    split_ifs <;> rfl

/-! ## Non-degeneracy -/

/-- **The overlay changes a price**: on day `0`, some family atom is quoted `0` by the LIA
(off its finite table) and `1/2` by the overlay. Proved from the market maker's finite `entries`,
not assumed.
Source: mandate T1.5 (non-degeneracy)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_ne_lia (DP : DeductiveProcess) :
    ∃ ψ, overlay (liaHistory DP) (wOv DP) 0 ψ ≠ liaHistory DP 0 ψ := by
  set S := (liaStates DP 0).support with hS
  set M := S.sup (Encodable.encode : Sentence → ℕ) with hM
  refine ⟨Formula.atom (Nat.pair wTag (M + 1)), ?_⟩
  have hnot : (Formula.atom (Nat.pair wTag (M + 1)) : Sentence) ∉ S := by
    intro hmem
    have h1 : Encodable.encode (Formula.atom (Nat.pair wTag (M + 1)) : Sentence) ≤ M :=
      Finset.le_sup (f := (Encodable.encode : Sentence → ℕ)) hmem
    rw [encode_atom] at h1
    have h2 : M + 1 ≤ Nat.pair wTag (M + 1) := Nat.right_le_pair _ _
    have h3 : Nat.pair wTag (M + 1) ≤ Nat.pair 1 (Nat.pair wTag (M + 1)) := Nat.right_le_pair _ _
    omega
  have hq : liaHistory DP 0 (Formula.atom (Nat.pair wTag (M + 1))) = 0 := by
    rw [liaHistory_eq_quote_cast]
    show (((liaStates DP 0).quote (Formula.atom (Nat.pair wTag (M + 1))) : ℚ) : ℝ) = 0
    rw [(liaStates DP 0).quote_eq_zero_of_not_mem hnot]
    simp
  have hov : overlay (liaHistory DP) (wOv DP) 0 (Formula.atom (Nat.pair wTag (M + 1))) = 1 / 2 := by
    rw [overlay_large (atom_not_smallOn_zero _)]
    simp [wOv, Nat.unpair_pair]
  rw [hov, hq]
  norm_num

/-- **The family reader**: every day, one share of `⊥` at the coefficient `price ⌜a⌝ 0` for the
family atom `a = Nat.pair wTag 0` (large on day `0`).
Source: mandate T1.5 (trader side)
Kind: D
Fidelity: n/a -/
def familyReader : Trader where
  strat n :=
    { trades := (List.range 1).map fun _ =>
        (EF.price (Formula.atom (Nat.pair wTag 0)) 0, (⊥ : Sentence))
      rank_le := by
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [EF.rank] }

/-- The family reader is efficiently computable (fixed coefficient).
Source: mandate T1.5 (trader side); FAF `EfficientlyComputable.ofTradeBlocksBig`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma familyReader_ec : EfficientlyComputable familyReader :=
  EfficientlyComputable.ofTradeBlocksBig familyReader (fun _ => 1)
    (fun _ => EF.price (Formula.atom (Nat.pair wTag 0)) 0) (fun _ => (⊥ : Sentence))
    (UnaryRuler.const 1)
    (MachineSpliceStream.serialize_price (MachineSentenceCodes.const (Formula.atom (Nat.pair wTag 0)))
      (UnaryRuler.const 0) (MachineDigits.const 0))
    (MachineSentenceCodes.const ⊥)
    (fun _ => rfl)

/-- **The trader side is exercised**: the family reader's splice is not the identity on any day
(its coefficient becomes `letE (price ⌜a⌝ 0) (const (1/2))`).
Source: mandate T1.5 (trader side)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem familyReader_splice_ne (n : ℕ) :
    ((Trader.spliceOn wExpr wExpr_rank familyReader).strat n).trades ≠
      (familyReader.strat n).trades := by
  have hfire : wExpr 0 (Formula.atom (Nat.pair wTag 0)) = some (EF.const (1 / 2)) := by
    simp [Nat.unpair_pair]
  simp [familyReader, EF.spliceOn_price_some wExpr hfire]

/-! ## The instance -/

/-- **The transfer theorem at the witness, over FAF's logical inductor**: for every computable
deductive process, the day-`0` family-`7` overlay of `liaHistory DP` is a logical inductor over
`DP`. The full hypothesis package is inhabited by the real construction (`LIA_is_logical_inductor`),
the map changes prices (`overlay_ne_lia`) and rewrites an e.c. trader non-trivially
(`familyReader_splice_ne`).
Source: mandate T1.5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem witness_isLogicalInductor (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP) :
    IsLogicalInductor (overlay (liaHistory DP) (wOv DP)) DP :=
  haveI := LIA_is_logical_inductor DP hDP
  overlay_isLogicalInductor' (liaHistory DP) DP (wOv DP) (wMap DP) wCertificate
    (wOv_computableTable DP hDP)

/-- The instance at the paper's single market over `𝗜𝚺₁`, whose stages all have consistent worlds
(`paperDP_hworld`), so the criterion there is not vacuous.
Source: mandate T1.5 (trap (v))
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem witness_isLogicalInductor_paperDP :
    IsLogicalInductor (overlay (liaHistory (paperDP 𝗜𝚺₁)) (wOv (paperDP 𝗜𝚺₁))) (paperDP 𝗜𝚺₁) :=
  witness_isLogicalInductor _ (paperDP_computable 𝗜𝚺₁)

/-- The process of the instance has a consistent world at every stage (non-vacuity of the
criterion's world quantifier).
Source: mandate T1.5 (trap (v)); FAF `paperDP_hworld`
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem witness_process_hworld (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  paperDP_hworld 𝗜𝚺₁ n

end Cleanroom.Bli.BliTransfer.AttemptA
