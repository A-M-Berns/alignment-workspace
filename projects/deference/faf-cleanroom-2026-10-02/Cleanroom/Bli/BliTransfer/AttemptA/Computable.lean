import Cleanroom.Bli.BliTransfer.AttemptA.Headline

/-!
# `bli-transfer` (attempt A) · Computable: the overlay is a computable market (T1.4)

`ComputableMarket (overlay Q ov)` from `Q`'s own certificate (`IsLogicalInductor.marketComputable`:
an exact rational table `quote : ℕ → ℕ → ℚ` on sentence codes and a `Nat.Partrec.Code` for it),
a computable rational table for `ov` (`ComputableTable`), and a **computable smallness test on
Gödel codes**. The last is the only content: `tokenSize` is structural on `Formula`, and
Foundation's decoder `Formula.ofNat` recurses on strictly smaller codes, so the size of the
decoded sentence is compiled by primitive-recursive course-of-values recursion on the code
(`tsCode`, the pattern of FAF's `sentencePrimcodable` in `Construction/Primcodable.lean`), with
the base-4 digit length of an atom index compiled the same way (`dl4`). No polynomial-time content
is claimed here — only computability, which is what `ComputableMarket` asks.

Then `overlay_isLogicalInductor'`: the headline with the overlay's computability *derived*, so the
remaining hypotheses are the certificate (the instance's oracle) and the computability of the
instance's own re-pricing table.

Sources: mandate T1.4; FAF `Criterion.lean:1067` (`ComputableMarket`), `:1091`
(`ComputableMarket.ofComputableTable`), `Construction/Primcodable.lean:70–240`,
`Framework/Emission/Computable.lean:100` (`Primrec.of_courseOfValues`).
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Primitive-recursion plumbing -/

section Plumbing

variable {α : Type*} [Primcodable α] {c f g : α → ℕ}

/-- Natural-number exponentiation is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prim_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

/-- Sum of two primitive-recursive functions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pAdd (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a + g a :=
  Primrec₂.comp Primrec.nat_add hf hg

/-- Truncated difference of two primitive-recursive functions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pSub (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a - g a :=
  Primrec₂.comp Primrec.nat_sub hf hg

/-- Quotient of two primitive-recursive functions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pDiv (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a / g a :=
  Primrec₂.comp Primrec.nat_div hf hg

/-- Power of two primitive-recursive functions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pPow (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a ^ g a :=
  Primrec₂.comp prim_natPow hf hg

/-- Branch on a primitive-recursive value equalling a constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pIte (k : ℕ) (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a = k then f a else g a :=
  Primrec.ite (PrimrecRel.comp Primrec.eq hc (Primrec.const k)) hf hg

/-- Table lookup with default `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pGetD {ℓ : α → List ℕ} (hℓ : Primrec ℓ) (hf : Primrec f) :
    Primrec fun a => List.getD (ℓ a) (f a) 0 :=
  Primrec₂.comp (f := fun (l : List ℕ) (n : ℕ) => List.getD l n 0) (Primrec.list_getD 0) hℓ hf

end Plumbing

/-- The `i`-th entry of the course-of-values table is `f i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma getD_range_map (f : ℕ → ℕ) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  have hlen : i < ((List.range n).map f).length := by simpa using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

/-! ## The base-4 digit length -/

/-- The number of base-4 digits of `n` (`(natDigits4 n).length`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def dl4 (n : ℕ) : ℕ := (natDigits4 n).length

/-- The halving recursion of the digit length.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dl4_succ (n : ℕ) : dl4 (n + 1) = dl4 ((n + 1) / 4) + 1 := by
  unfold dl4
  rw [natDigits4]
  simp

/-- The course-of-values step of `dl4`. -/
def dl4Step (L : List ℕ) : ℕ :=
  if L.length = 0 then 0 else L.getD (L.length / 4) 0 + 1

/-- `dl4Step` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dl4Step_prim : Primrec dl4Step := by
  have hlen : Primrec (fun L : List ℕ => L.length) := Primrec.list_length
  have h : Primrec fun L : List ℕ =>
      if L.length = 0 then 0 else L.getD (L.length / 4) 0 + 1 :=
    pIte 0 hlen (Primrec.const 0)
      (pAdd (pGetD Primrec.id (pDiv hlen (Primrec.const 4))) (Primrec.const 1))
  exact h.of_eq fun _ => rfl

/-- `dl4Step` computes `dl4` from its earlier values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dl4Step_rec (n : ℕ) : dl4Step ((List.range n).map dl4) = dl4 n := by
  cases n with
  | zero => simp [dl4Step, dl4, natDigits4]
  | succ m =>
      have hlen : ((List.range (m + 1)).map dl4).length = m + 1 := by simp
      rw [dl4Step, hlen, if_neg (Nat.succ_ne_zero m),
        getD_range_map dl4 (Nat.div_lt_self (Nat.succ_pos m) (by norm_num)), dl4_succ]

/-- The base-4 digit length is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dl4_prim : Primrec dl4 :=
  Primrec.of_courseOfValues dl4 dl4Step_prim dl4Step_rec

/-! ## The token size on Gödel codes -/

/-- The token size of the sentence a code denotes, shifted by one so that `0` marks an invalid
code: `tokenSize φ + 1` when `Formula.ofNat n = some φ`, `0` otherwise.
Source: mandate T1.4 (the structural smallness test on codes)
Kind: D
Fidelity: n/a -/
def tsCode (n : ℕ) : ℕ :=
  match (LO.Propositional.Formula.ofNat n : Option Sentence) with
  | none => 0
  | some φ => tokenSize φ + 1

/-- The binary-connective step: `k` plus the two children's sizes, or `0` if either child is
invalid.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tsBinary (k : ℕ) (prior : List ℕ) (children : ℕ) : ℕ :=
  let left := prior.getD children.unpair.1 0
  let right := prior.getD children.unpair.2 0
  if left = 0 ∨ right = 0 then 0 else k + (left - 1) + (right - 1) + 1

/-- `tsBinary k` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsBinary_prim (k : ℕ) : Primrec₂ (tsBinary k) := by
  let childLeft : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.1 0
  let childRight : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.2 0
  have hindexLeft : Primrec fun p : List ℕ × ℕ => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hindexRight : Primrec fun p : List ℕ × ℕ => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hleft : Primrec childLeft := (Primrec.list_getD 0).comp Primrec.fst hindexLeft
  have hright : Primrec childRight := (Primrec.list_getD 0).comp Primrec.fst hindexRight
  have hbad : PrimrecPred fun p : List ℕ × ℕ => childLeft p = 0 ∨ childRight p = 0 :=
    (Primrec.eq.comp hleft (Primrec.const 0)).or (Primrec.eq.comp hright (Primrec.const 0))
  have hresult : Primrec fun p : List ℕ × ℕ =>
      k + (childLeft p - 1) + (childRight p - 1) + 1 :=
    pAdd (pAdd (pAdd (Primrec.const k) (pSub hleft (Primrec.const 1)))
      (pSub hright (Primrec.const 1))) (Primrec.const 1)
  exact (Primrec.ite hbad (Primrec.const 0) hresult).to₂.of_eq fun prior children => by
    simp only [tsBinary, childLeft, childRight]

/-- The successor step: dispatch on Foundation's constructor tag.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tsSucc (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then 2
  else if tag = 1 then dl4 (payload + 5) + 2
  else if tag = 2 then tsBinary 2 prior payload
  else if tag = 3 then tsBinary 2 prior payload
  else if tag = 4 then tsBinary 3 prior payload
  else 0

/-- `tsSucc` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsSucc_prim : Primrec₂ tsSucc := by
  let tag : List ℕ × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List ℕ × ℕ → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hatom : Primrec fun p : List ℕ × ℕ => dl4 (payload p + 5) + 2 :=
    pAdd (dl4_prim.comp (pAdd hpayload (Primrec.const 5))) (Primrec.const 2)
  have hbinary (k : ℕ) : Primrec fun p : List ℕ × ℕ => tsBinary k p.1 (payload p) :=
    (tsBinary_prim k).comp Primrec.fst hpayload
  have htagEq (k : ℕ) : PrimrecPred fun p : List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  exact (Primrec.ite (htagEq 0) (Primrec.const 2)
    (Primrec.ite (htagEq 1) hatom
      (Primrec.ite (htagEq 2) (hbinary 2)
        (Primrec.ite (htagEq 3) (hbinary 2)
          (Primrec.ite (htagEq 4) (hbinary 3)
            (Primrec.const 0)))))).to₂.of_eq fun prior e => by
    simp only [tsSucc, tag, payload]

/-- The course-of-values step of `tsCode`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tsStep (prior : List ℕ) : ℕ := prior.length.casesOn 0 (tsSucc prior)

/-- `tsStep` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsStep_prim : Primrec tsStep :=
  (Primrec.nat_casesOn Primrec.list_length (Primrec.const 0) tsSucc_prim).of_eq fun prior => by
    simp only [tsStep]

/-- The course-of-values table of `tsCode` reads back `tsCode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsCode_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map tsCode).getD k 0 = tsCode k :=
  getD_range_map tsCode hk

/-- The binary step on the table is the size of the connective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsBinary_history (k payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    tsBinary k ((List.range n).map tsCode) payload =
      match (LO.Propositional.Formula.ofNat payload.unpair.1 : Option Sentence),
          (LO.Propositional.Formula.ofNat payload.unpair.2 : Option Sentence) with
      | some φ, some ψ => k + tokenSize φ + tokenSize ψ + 1
      | _, _ => 0 := by
  unfold tsBinary
  rw [tsCode_getD hleft, tsCode_getD hright]
  cases hL : (LO.Propositional.Formula.ofNat payload.unpair.1 : Option Sentence) <;>
    cases hR : (LO.Propositional.Formula.ofNat payload.unpair.2 : Option Sentence) <;>
    simp [tsCode, hL, hR]

/-- `tsStep` computes `tsCode` from its earlier values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsStep_rec (n : ℕ) : tsStep ((List.range n).map tsCode) = tsCode n := by
  cases n with
  | zero => simp [tsStep, tsCode, LO.Propositional.Formula.ofNat]
  | succ e =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      have hleft : payload.unpair.1 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : payload.unpair.2 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      by_cases h0 : tag = 0
      · simp [tsStep, tsSucc, tsCode, LO.Propositional.Formula.ofNat, tag, h0]
      by_cases h1 : tag = 1
      · simp [tsStep, tsSucc, tsCode, LO.Propositional.Formula.ofNat, tag, h1, dl4]
      have hbin : ∀ (t k : ℕ), (t = 2 ∧ k = 2) ∨ (t = 3 ∧ k = 2) ∨ (t = 4 ∧ k = 3) →
          e.unpair.1 = t →
          tsStep ((List.range (e + 1)).map tsCode) = tsCode (e + 1) := by
        intro t k ht htag
        have hb := tsBinary_history k payload (e + 1) hleft hright
        rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          · simp only [tsStep, List.length_map, List.length_range, tsSucc, htag, ↓reduceIte]
            rw [hb]
            unfold tsCode
            simp only [LO.Propositional.Formula.ofNat, htag]
            cases (LO.Propositional.Formula.ofNat payload.unpair.1 : Option Sentence) <;>
              cases (LO.Propositional.Formula.ofNat payload.unpair.2 : Option Sentence) <;>
              simp
      by_cases h2 : tag = 2
      · exact hbin 2 2 (Or.inl ⟨rfl, rfl⟩) h2
      by_cases h3 : tag = 3
      · exact hbin 3 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) h3
      by_cases h4 : tag = 4
      · exact hbin 4 3 (Or.inr (Or.inr ⟨rfl, rfl⟩)) h4
      · have htag : 5 ≤ tag := by omega
        simp [tsStep, tsSucc, tsCode, LO.Propositional.Formula.ofNat, tag, h0, h1, h2, h3, h4]

/-- **The token size on codes is primitive recursive.**
Source: mandate T1.4
Kind: P
Fidelity: exact -/
lemma tsCode_prim : Primrec tsCode :=
  Primrec.of_courseOfValues tsCode tsStep_prim tsStep_rec

/-- On a sentence's own code, `tsCode` is its token size plus one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsCode_encode (φ : Sentence) : tsCode (Encodable.encode φ) = tokenSize φ + 1 := by
  have h : (LO.Propositional.Formula.ofNat (Encodable.encode φ) : Option Sentence) = some φ :=
    LO.Propositional.Formula.ofNat_toNat φ
  simp [tsCode, h]

/-! ## The smallness test on codes -/

/-- `sizeBound` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sizeBound_prim : Primrec sizeBound := by
  have h : Primrec fun n : ℕ => 2 ^ (2 ^ n) :=
    pPow (Primrec.const 2) (pPow (Primrec.const 2) Primrec.id)
  exact h.of_eq fun n => rfl

/-- The day-`n` smallness test on a sentence code.
Source: mandate T1.4
Kind: D
Fidelity: n/a -/
def smallCode (n c : ℕ) : Bool := decide (tsCode c ≤ sizeBound n + 1)

/-- The smallness test is primitive recursive.
Source: mandate T1.4
Kind: L
Fidelity: exact -/
lemma smallCode_prim : Primrec₂ smallCode := by
  have h : PrimrecPred fun p : ℕ × ℕ => tsCode p.2 ≤ sizeBound p.1 + 1 :=
    Primrec.nat_le.comp (tsCode_prim.comp Primrec.snd)
      (pAdd (sizeBound_prim.comp Primrec.fst) (Primrec.const 1))
  obtain ⟨_, h⟩ := h
  refine Primrec.of_eq h (fun p => ?_)
  simp only [smallCode]
  exact decide_eq_decide.mpr Iff.rfl

/-- The smallness test on a sentence's own code is smallness.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallCode_encode (n : ℕ) (φ : Sentence) :
    smallCode n (Encodable.encode φ) = true ↔ SmallOn n φ := by
  simp only [smallCode, tsCode_encode, decide_eq_true_eq, SmallOn]
  omega

/-! ## Computable tables and the overlay's market certificate -/

/-- A rational sentence table presented computably on codes — the second conjunct of FAF's
`ComputableMarket`, with `Computable` in place of the explicit code (equivalent through
`Nat.Partrec.Code.exists_code`).
Source: mandate T1.4
Kind: D
Fidelity: n/a -/
def ComputableTable (ov : ℕ → Sentence → ℚ) : Prop :=
  ∃ tab : ℕ → ℕ → ℚ, (∀ n φ, ov n φ = tab n (Encodable.encode φ)) ∧
    Computable fun z : ℕ => Encodable.encode (tab z.unpair.1 z.unpair.2)

/-- A computable market's quote table is a computable table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ComputableMarket.exists_computableTable {P : History} (h : ComputableMarket P) :
    ∃ tab : ℕ → ℕ → ℚ, (∀ n φ, P n φ = (tab n (Encodable.encode φ) : ℝ)) ∧
      Computable fun z : ℕ => Encodable.encode (tab z.unpair.1 z.unpair.2) := by
  obtain ⟨_, tab, code, hexact, hcode⟩ := h
  refine ⟨tab, hexact, ?_⟩
  have h1 : Nat.Partrec code.eval := Nat.Partrec.Code.exists_code.mpr ⟨code, rfl⟩
  have h2 : Nat.Partrec fun z : ℕ =>
      Part.some (Encodable.encode (tab z.unpair.1 z.unpair.2)) :=
    Nat.Partrec.of_eq h1 (fun z => Part.eq_some_iff.mpr (hcode z))
  exact Partrec.nat_iff.mpr h2

/-- The combined table: `Q`'s quote on small codes, `ov`'s on the others.
Source: mandate T1.4
Kind: D
Fidelity: n/a -/
def overlayTable (tabQ tabOv : ℕ → ℕ → ℚ) (n c : ℕ) : ℚ :=
  if smallCode n c then tabQ n c else tabOv n c

/-- **The overlay of a computable market by a computable re-pricing is a computable market**,
through the primitive-recursive smallness test on codes.
Source: mandate T1.4
Kind: C
Fidelity: exact
Hyps: (a) `hQ` (the inductor's certificate), `hov` (the re-pricing's own table), `hrange` -/
theorem overlay_computableMarket {Q : History} {ov : ℕ → Sentence → ℚ}
    (hQ : ComputableMarket Q) (hov : ComputableTable ov)
    (hrange : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1) :
    ComputableMarket (overlay Q ov) := by
  obtain ⟨tabQ, hQexact, hQcomp⟩ := ComputableMarket.exists_computableTable hQ
  obtain ⟨tabOv, hOvexact, hOvcomp⟩ := hov
  refine ComputableMarket.ofComputableTable (overlayTable tabQ tabOv)
    (overlay_range hrange hQ.1) ?_ ?_
  · intro n φ
    unfold overlayTable
    by_cases hs : SmallOn n φ
    · rw [overlay_small hs, if_pos ((smallCode_encode n φ).mpr hs), hQexact]
    · rw [overlay_large hs, if_neg (fun h => hs ((smallCode_encode n φ).mp h)), hOvexact]
  · have hc : Computable fun z : ℕ => smallCode z.unpair.1 z.unpair.2 :=
      (smallCode_prim.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.snd.comp Primrec.unpair)).to_comp
    have h := Computable.cond hc hQcomp hOvcomp
    refine h.of_eq fun z => ?_
    simp only [overlayTable]
    cases smallCode z.unpair.1 z.unpair.2 <;> simp

/-- **The expressible-overlay transfer theorem, with the overlay's computability derived** (the
headline of record). Hypotheses: `Q` a logical inductor, an expression map `E`, its certificate
`C`, and the re-pricing `ov` given as a computable table.
Source: [[bli-program]] §3.1; bli-paper-039; mandate T1 (`overlay_isLogicalInductor'`)
Kind: C
Fidelity: exact (as `Headline.overlay_isLogicalInductor`, with `hcomp` discharged)
Hyps: (a) except `C` (the certificate) and `hov` (the re-pricing's computable table) — both the instance's obligations -/
theorem overlay_isLogicalInductor' (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (C : SpliceCertificate E.expr) (hov : ComputableTable ov) :
    IsLogicalInductor (overlay Q ov) DP :=
  overlay_isLogicalInductor Q DP ov E C
    (overlay_computableMarket hQ.marketComputable hov E.ov_range)

end Cleanroom.Bli.BliTransfer.AttemptA
