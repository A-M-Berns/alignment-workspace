import Cleanroom.Li.LiProjection.Defs
import LogicalInduction.Construction.Primcodable
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `li-projection` · Market: the `ComputableMarket` certificate of the projected table (T1.3)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 6 of the layout. FAF's
`IsLogicalInductor` carries `marketComputable : ComputableMarket P` — an exact rational table
`quote : ℕ → ℕ → ℚ` keyed by sentence code, with a `Nat.Partrec.Code` evaluating it. The projected
market's table is `q n * quote n ⌜φ⟦u:=⊤⟧⌝ + (1 − q n) * quote n ⌜φ⟦u:=⊥⟧⌝`, so the certificate
needs the substitution **on codes**: `substCode u b ⌜φ⌝ = ⌜φ⟦substAtom u b⟧⌝`, primitive recursive by
strong recursion on Foundation's `Nat.pair`-nested codes (the pattern of FAF's `negFormulaCode_prim`).
`q` enters as `Computable q`, which FAF derives from `MachineRatCodes q`
(`MachineRatCodes.computable`, `Construction/Quotation/MarketQuoteCodes.lean`), so Lemma A's
hypothesis (i) is the only computability hypothesis on the weight.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional

-- `Primrec` elaboration over deep products unfolds `Nat.sqrt` during `whnf` and loops
-- (FAF's `notes/lean-gotchas.md`); make it locally irreducible, as FAF does.
attribute [local irreducible] Nat.sqrt

/-! ## Prices in `[0,1]` -/

/-- The projected prices lie in `[0,1]` when the base prices do and `q n ∈ [0,1]`.
Source: none: infrastructure (`ComputableMarket` range field)
Kind: L
Fidelity: n/a -/
lemma project_mem_Icc (P : History) (u : ℕ) (q : ℕ → ℚ)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (n : ℕ) (φ : Sentence) :
    0 ≤ project P u q n φ ∧ project P u q n φ ≤ 1 := by
  rw [project_apply]
  obtain ⟨ha0, ha1⟩ := hP n (φ⟦substAtom u true⟧)
  obtain ⟨hb0, hb1⟩ := hP n (φ⟦substAtom u false⟧)
  have hq0 : (0 : ℝ) ≤ q n := by exact_mod_cast (hq n).1
  have hq1 : (q n : ℝ) ≤ 1 := by exact_mod_cast (hq n).2
  constructor
  · nlinarith
  · nlinarith

/-! ## The substitution on codes -/

/-- The substitution `φ ↦ φ⟦substAtom u b⟧` on Foundation's formula codes
(`toNat`: `⊥ ↦ ⟪0,0⟫+1`, `atom a ↦ ⟪1,a⟫+1`, binary connectives `⟪2|3|4, ⟪⌜φ⌝,⌜ψ⌝⟫⟫+1`),
by well-founded recursion on the code.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def substCode (u : ℕ) (b : Bool) : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
      let a := e.unpair.1
      let c := e.unpair.2
      if a = 0 then Nat.pair 0 0 + 1
      else if a = 1 then
        (if c = u then Encodable.encode (if b then (⊤ : Sentence) else ⊥) else Nat.pair 1 c + 1)
      else if a = 2 ∨ a = 3 ∨ a = 4 then
        Nat.pair a (Nat.pair (substCode u b c.unpair.1) (substCode u b c.unpair.2)) + 1
      else 0
decreasing_by
  all_goals
    simp_wf
    first
      | exact le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      | exact le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)

/-- `substCode_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma substCode_zero (u : ℕ) (b : Bool) : substCode u b 0 = 0 := by rw [substCode]

/-- `substCode_succ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma substCode_succ (u : ℕ) (b : Bool) (e : ℕ) :
    substCode u b (e + 1) =
      if e.unpair.1 = 0 then Nat.pair 0 0 + 1
      else if e.unpair.1 = 1 then
        (if e.unpair.2 = u then Encodable.encode (if b then (⊤ : Sentence) else ⊥)
          else Nat.pair 1 e.unpair.2 + 1)
      else if e.unpair.1 = 2 ∨ e.unpair.1 = 3 ∨ e.unpair.1 = 4 then
        Nat.pair e.unpair.1
          (Nat.pair (substCode u b e.unpair.2.unpair.1) (substCode u b e.unpair.2.unpair.2)) + 1
      else 0 := by
  rw [substCode]

/-- `encode_sentence_eq_toNat`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma encode_sentence_eq_toNat (φ : Sentence) : Encodable.encode φ = Formula.toNat φ := rfl

/-- **`substCode` is the substitution on codes**: `substCode u b ⌜φ⌝ = ⌜φ⟦substAtom u b⟧⌝`.
Source: none: infrastructure
Kind: P
Fidelity: n/a -/
theorem substCode_encode (u : ℕ) (b : Bool) :
    ∀ φ : Sentence, substCode u b (Encodable.encode φ) = Encodable.encode (φ⟦substAtom u b⟧) := by
  intro φ
  induction φ using Formula.rec' with
  | hfalsum =>
      show substCode u b (Nat.pair 0 0 + 1) = Nat.pair 0 0 + 1
      rw [substCode_succ]
      simp only [Nat.unpair_pair, if_true]
  | hatom a =>
      show substCode u b (Nat.pair 1 a + 1) = Formula.toNat (substAtom u b a)
      rw [substCode_succ]
      simp only [Nat.unpair_pair, one_ne_zero, if_false, if_true]
      by_cases h : a = u
      · subst h
        simp only [substAtom, if_true]
        rfl
      · rw [if_neg h, substAtom_of_ne u b h]
        rfl
  | himp φ ψ ihφ ihψ =>
      show substCode u b (Nat.pair 2 (Nat.pair (Formula.toNat φ) (Formula.toNat ψ)) + 1) =
        Nat.pair 2 (Nat.pair (Formula.toNat (φ⟦substAtom u b⟧)) (Formula.toNat (ψ⟦substAtom u b⟧))) + 1
      rw [substCode_succ]
      simp only [Nat.unpair_pair]
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
      rw [encode_sentence_eq_toNat, encode_sentence_eq_toNat] at ihφ ihψ
      rw [ihφ, ihψ]
  | hand φ ψ ihφ ihψ =>
      show substCode u b (Nat.pair 3 (Nat.pair (Formula.toNat φ) (Formula.toNat ψ)) + 1) =
        Nat.pair 3 (Nat.pair (Formula.toNat (φ⟦substAtom u b⟧)) (Formula.toNat (ψ⟦substAtom u b⟧))) + 1
      rw [substCode_succ]
      simp only [Nat.unpair_pair]
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
      rw [encode_sentence_eq_toNat, encode_sentence_eq_toNat] at ihφ ihψ
      rw [ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      show substCode u b (Nat.pair 4 (Nat.pair (Formula.toNat φ) (Formula.toNat ψ)) + 1) =
        Nat.pair 4 (Nat.pair (Formula.toNat (φ⟦substAtom u b⟧)) (Formula.toNat (ψ⟦substAtom u b⟧))) + 1
      rw [substCode_succ]
      simp only [Nat.unpair_pair]
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
      rw [encode_sentence_eq_toNat, encode_sentence_eq_toNat] at ihφ ihψ
      rw [ihφ, ihψ]

/-! ### Primitive recursion of `substCode` (the pattern of FAF's `negFormulaCode_prim`) -/

/-- Memoized mirror of `substCode`: recursive calls become lookups at smaller indices. -/
private def substCodeCore (u : ℕ) (b : Bool) (n : ℕ) (look : ℕ → ℕ) : ℕ :=
  match n with
  | 0 => 0
  | e + 1 =>
      if e.unpair.1 = 0 then Nat.pair 0 0 + 1
      else if e.unpair.1 = 1 then
        (if e.unpair.2 = u then Encodable.encode (if b then (⊤ : Sentence) else ⊥)
          else Nat.pair 1 e.unpair.2 + 1)
      else if e.unpair.1 = 2 ∨ e.unpair.1 = 3 ∨ e.unpair.1 = 4 then
        Nat.pair e.unpair.1 (Nat.pair (look e.unpair.2.unpair.1) (look e.unpair.2.unpair.2)) + 1
      else 0

/-- `substCodeCore_spec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
private lemma substCodeCore_spec (u : ℕ) (b : Bool) (n : ℕ) (look : ℕ → ℕ)
    (hlook : ∀ i, i < n → look i = substCode u b i) :
    substCodeCore u b n look = substCode u b n := by
  rcases n with _ | e
  · rw [substCode_zero]; rfl
  have hc : e.unpair.2 ≤ e := Nat.unpair_right_le e
  have h1 : e.unpair.2.unpair.1 < e + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) hc)
  have h2 : e.unpair.2.unpair.2 < e + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) hc)
  rw [substCodeCore, substCode_succ]
  simp only [hlook _ h1, hlook _ h2]

/-- `substCodeG`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
private def substCodeG (u : ℕ) (b : Bool) (prev : List ℕ) : Option ℕ :=
  some (substCodeCore u b prev.length fun i => (prev[i]?).getD 0)

/-- `substCodeG_spec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
private lemma substCodeG_spec (u : ℕ) (b : Bool) (n : ℕ) :
    substCodeG u b ((List.range n).map (substCode u b)) = some (substCode u b n) := by
  rw [substCodeG, show ((List.range n).map (substCode u b)).length = n from by simp]
  congr 1
  refine substCodeCore_spec u b n _ fun i hi => ?_
  have hib : i < ((List.range n).map (substCode u b)).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map, List.getElem_range]

/-- `substCodeG_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
private lemma substCodeG_prim (u : ℕ) (b : Bool) : Primrec (substCodeG u b) := by
  have hlen : Primrec fun prev : List ℕ => prev.length := Primrec.list_length
  have ha : Primrec fun x : List ℕ × ℕ => x.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hc : Primrec fun x : List ℕ × ℕ => x.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hlookOf : ∀ {i : List ℕ × ℕ → ℕ}, Primrec i →
      Primrec fun x : List ℕ × ℕ => ((x.1[i x]?).getD 0) := fun hi =>
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst hi) (Primrec.const 0)
  have hl1 := hlookOf (Primrec.fst.comp (Primrec.unpair.comp hc))
  have hl2 := hlookOf (Primrec.snd.comp (Primrec.unpair.comp hc))
  have heqa : ∀ k : ℕ, PrimrecPred fun x : List ℕ × ℕ => x.2.unpair.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ha (Primrec.const k)
  have heqc : PrimrecPred fun x : List ℕ × ℕ => x.2.unpair.2 = u :=
    PrimrecRel.comp Primrec.eq hc (Primrec.const u)
  have hatom : Primrec fun x : List ℕ × ℕ =>
      (if x.2.unpair.2 = u then Encodable.encode (if b then (⊤ : Sentence) else ⊥)
        else Nat.pair 1 x.2.unpair.2 + 1) :=
    Primrec.ite heqc (Primrec.const _)
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hc))
  have hbin : Primrec fun x : List ℕ × ℕ =>
      Nat.pair x.2.unpair.1 (Nat.pair ((x.1[x.2.unpair.2.unpair.1]?).getD 0)
        ((x.1[x.2.unpair.2.unpair.2]?).getD 0)) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp ha (Primrec₂.natPair.comp hl1 hl2))
  have hor : PrimrecPred fun x : List ℕ × ℕ =>
      x.2.unpair.1 = 2 ∨ x.2.unpair.1 = 3 ∨ x.2.unpair.1 = 4 :=
    (heqa 2).or ((heqa 3).or (heqa 4))
  have hbody : Primrec fun x : List ℕ × ℕ =>
      if x.2.unpair.1 = 0 then Nat.pair 0 0 + 1
      else if x.2.unpair.1 = 1 then
        (if x.2.unpair.2 = u then Encodable.encode (if b then (⊤ : Sentence) else ⊥)
          else Nat.pair 1 x.2.unpair.2 + 1)
      else if x.2.unpair.1 = 2 ∨ x.2.unpair.1 = 3 ∨ x.2.unpair.1 = 4 then
        Nat.pair x.2.unpair.1 (Nat.pair ((x.1[x.2.unpair.2.unpair.1]?).getD 0)
          ((x.1[x.2.unpair.2.unpair.2]?).getD 0)) + 1
      else 0 :=
    Primrec.ite (heqa 0) (Primrec.const _) <|
      Primrec.ite (heqa 1) hatom <| Primrec.ite hor hbin (Primrec.const 0)
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hlen (Primrec.const 0) hbody.to₂)).of_eq fun prev => ?_
  rw [substCodeG]
  rcases hn : prev.length with _ | e
  · simp [substCodeCore]
  simp [substCodeCore]

/-- **`substCode` is primitive recursive.**
Source: none: infrastructure (the pattern of FAF's `negFormulaCode_prim`)
Kind: P
Fidelity: n/a -/
theorem substCode_prim (u : ℕ) (b : Bool) : Primrec (substCode u b) := by
  have hF : Primrec₂ (fun (_ : Unit) => substCode u b) :=
    Primrec.nat_strong_rec _ ((substCodeG_prim u b).comp Primrec.snd).to₂
      fun _ n => substCodeG_spec u b n
  exact hF.comp (Primrec.const ()) Primrec.id

/-! ## The computable-market certificate -/

/-- A market program's quote table is computable in any computable pair of arguments (after
`li-quote-lane`'s `marketComputation_quote_computable`, restated here to keep this file's imports
light).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem marketComputation_quote_computable' {P : History} (M : MarketComputation P)
    {d g : ℕ → ℕ} (hd : Computable d) (hg : Computable g) :
    Computable fun a => M.quote (d a) (g a) := by
  have hin : Computable fun a => Nat.pair (d a) (g a) := Primrec₂.natPair.to_comp.comp hd hg
  have heval : Partrec fun a => M.code.eval (Nat.pair (d a) (g a)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const M.code) hin
  have henc : Computable fun a => Encodable.encode (M.quote (d a) (g a)) :=
    heval.of_eq fun a => Part.eq_some_iff.mpr (by simpa using M.code_spec (Nat.pair (d a) (g a)))
  exact Computable.encode_iff.mp henc

/-- **T1.3. The projected market is a `ComputableMarket`** whenever the base market is and the
weight is computable: the table `q n * quote n (substCode u true c) + (1 − q n) * quote n (substCode u false c)`
is exact for `project P u q` and computable. This is the `marketComputable` field of Lemma A's
conclusion.
Source: [[dose-response]] §6.1 Lemma A ("Computability … immediate"); mandate T1.3
Kind: C
Fidelity: exact
Hyps: (a) `hP` is the base inductor's own field; `hq` is derived from Lemma A's (i) by FAF's `MachineRatCodes.computable` -/
theorem computableMarket_project (P : History) (u : ℕ) (q : ℕ → ℚ) (hP : ComputableMarket P)
    (hq : Computable q) (hq01 : ∀ n, 0 ≤ q n ∧ q n ≤ 1) :
    ComputableMarket (project P u q) := by
  obtain ⟨M⟩ := hP.nonemptyComputation
  refine ComputableMarket.ofComputableTable
    (fun n c => q n * M.quote n (substCode u true c) + (1 - q n) * M.quote n (substCode u false c))
    (project_mem_Icc P u q M.price_mem_Icc hq01) ?_ ?_
  · intro n φ
    rw [project_apply, M.quote_exact n (φ⟦substAtom u true⟧), M.quote_exact n (φ⟦substAtom u false⟧),
      substCode_encode, substCode_encode]
    push_cast
    ring
  · apply Computable.encode.comp
    have hfst : Computable fun z : ℕ => z.unpair.1 :=
      (Primrec.fst.comp Primrec.unpair).to_comp
    have hsnd : Computable fun z : ℕ => z.unpair.2 :=
      (Primrec.snd.comp Primrec.unpair).to_comp
    have hqz : Computable fun z : ℕ => q z.unpair.1 := hq.comp hfst
    have hA : Computable fun z : ℕ => M.quote z.unpair.1 (substCode u true z.unpair.2) :=
      marketComputation_quote_computable' M hfst ((substCode_prim u true).to_comp.comp hsnd)
    have hB : Computable fun z : ℕ => M.quote z.unpair.1 (substCode u false z.unpair.2) :=
      marketComputation_quote_computable' M hfst ((substCode_prim u false).to_comp.comp hsnd)
    exact ratAdd_prim.to_comp.comp (ratMul_prim.to_comp.comp hqz hA)
      (ratMul_prim.to_comp.comp (ratSub_prim.to_comp.comp (Computable.const 1) hqz) hB)

/-- `ComputableMarket` of the projection from Lemma A's hypothesis (i) directly.
Source: mandate T1.3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem computableMarket_project_ofMachineRatCodes (P : History) (u : ℕ) (q : ℕ → ℚ)
    (hP : ComputableMarket P) (hq : MachineRatCodes q) (hq01 : ∀ n, 0 ≤ q n ∧ q n ≤ 1) :
    ComputableMarket (project P u q) :=
  computableMarket_project P u q hP hq.computable hq01

end Cleanroom.Li.LiProjection
