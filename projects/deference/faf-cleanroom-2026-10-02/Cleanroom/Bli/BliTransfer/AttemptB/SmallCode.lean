import Cleanroom.Bli.BliTransfer.AttemptB.Defs

/-!
# `bli-transfer` · attempt B · SmallCode: `tokenSize` is primitive recursive (closes T1.4's gap)

`tokenSize` is a structural recursion on formulas; on Gödel codes it is a course-of-values
recursion (`Primrec.nat_strong_rec`) following Foundation's `Formula.ofNat`: a code `e + 1`
unpairs into a tag and a payload; tag `0` is `⊥`, tag `1` an atom (whose token costs
`(natDigits4 (a + 5)).length + 1` digits), tags `2`–`4` the binary connectives (two smaller
codes, `2 + · + ·`), anything else is not a code. The recursion is stated on
`tsc n := encode ((decode n : Option Sentence).map tokenSize)` — `0` on non-codes, `tokenSize + 1`
on codes — which is exactly what `Primrec (tokenSize : Sentence → ℕ)` unfolds to. The digit
count `digitLen n := (natDigits4 n).length` is its own small course-of-values recursion
(`digitLen (n+1) = digitLen ((n+1)/4) + 1`).

Result: `tsc_primrec` (which is `Primrec tokenSize` under FAF's `Primcodable Sentence`), `sizeBound_primrec`,
`smallCode_primrec` — the smallness test on codes is primitive recursive, hence computable
(`Computable.lean`), certified on `ℕ` alone.

Sources: mandate T1.4; FAF `Construction/Primcodable.lean` (the idiom).
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The digit count -/

/-- The number of base-4 digits FAF's `natDigits4` emits.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def digitLen (n : ℕ) : ℕ := (natDigits4 n).length

/-- `natDigits4 0` is empty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitLen_zero : digitLen 0 = 0 := by simp [digitLen, natDigits4]

/-- The digit-count recursion: one digit plus the count of the quotient by `4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitLen_succ (n : ℕ) : digitLen (n + 1) = digitLen ((n + 1) / 4) + 1 := by
  unfold digitLen
  rw [natDigits4]
  simp

/-- The course-of-values step for `digitLen`: from the list of earlier values.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def digitLenStep (hist : List ℕ) : ℕ :=
  Nat.casesOn hist.length 0 fun e => hist.getD ((e + 1) / 4) 0 + 1

/-- The step applied to the history of earlier values computes the value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitLenStep_spec (n : ℕ) : digitLenStep ((List.range n).map digitLen) = digitLen n := by
  cases n with
  | zero => simp [digitLenStep, digitLen_zero]
  | succ e =>
      have hlt : (e + 1) / 4 < e + 1 := Nat.div_lt_self (Nat.succ_pos e) (by norm_num)
      simp only [digitLenStep, List.length_map, List.length_range]
      rw [digitLen_succ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
      rfl

/-- The step is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitLenStep_primrec : Primrec digitLenStep :=
  Primrec.nat_casesOn Primrec.list_length (Primrec.const 0)
    (Primrec.nat_add.comp
      ((Primrec.list_getD 0).comp Primrec.fst
        (Primrec.nat_div.comp (Primrec.succ.comp Primrec.snd) (Primrec.const 4)))
      (Primrec.const 1)).to₂

/-- `digitLen` is primitive recursive.
Source: none: infrastructure
Kind: P
Fidelity: n/a -/
lemma digitLen_primrec : Primrec digitLen := by
  have h := Primrec.nat_strong_rec (fun (_ : Unit) n => digitLen n)
    (g := fun _ hist => some (digitLenStep hist))
    (Primrec.option_some.comp (digitLenStep_primrec.comp Primrec.snd)).to₂
    (fun _ n => by rw [digitLenStep_spec])
  exact h.comp (Primrec.const ()) Primrec.id

/-- The smallness test on Gödel codes: `true` iff `c` decodes to a sentence small on day `n`.
Source: mandate T1.4
Kind: D
Fidelity: n/a -/
def smallCode (n c : ℕ) : Bool :=
  ((Encodable.decode (α := Sentence) c).map fun φ => decide (SmallOn n φ)).getD false

/-- On a sentence's own code the test decides `SmallOn`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallCode_encode (n : ℕ) (ψ : Sentence) :
    smallCode n (Encodable.encode ψ) = decide (SmallOn n ψ) := by
  simp [smallCode, Encodable.encodek]

/-! ## `tokenSize` on codes -/

/-- `tokenSize` transported to Gödel codes as `Primrec` reads it: `0` on non-codes,
`tokenSize φ + 1` on the code of `φ`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tsc (n : ℕ) : ℕ :=
  Encodable.encode ((Encodable.decode (α := Sentence) n).map tokenSize)

/-- `tsc` as an `Option.getD`: `0` on non-codes, `tokenSize + 1` on codes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsc_eq (n : ℕ) : tsc n = ((Encodable.decode (α := Sentence) n).map fun φ => tokenSize φ + 1).getD 0 := by
  unfold tsc
  cases Encodable.decode (α := Sentence) n <;> simp

/-- `tsc n = 0` exactly on non-codes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tsc_eq_zero_iff (n : ℕ) : tsc n = 0 ↔ Encodable.decode (α := Sentence) n = none := by
  rw [tsc_eq]
  cases Encodable.decode (α := Sentence) n <;> simp

/-- The course-of-values step for `tsc`, following `Formula.ofNat`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tscStep (hist : List ℕ) : ℕ :=
  Nat.casesOn hist.length 0 fun e =>
    if e.unpair.1 = 0 then 2
    else if e.unpair.1 = 1 then digitLen (e.unpair.2 + 5) + 2
    else if e.unpair.1 = 2 ∨ e.unpair.1 = 3 ∨ e.unpair.1 = 4 then
      (if hist.getD e.unpair.2.unpair.1 0 = 0 ∨ hist.getD e.unpair.2.unpair.2 0 = 0 then 0
       else hist.getD e.unpair.2.unpair.1 0 + hist.getD e.unpair.2.unpair.2 0 +
         (if e.unpair.1 = 4 then 2 else 1))
    else 0

/-- Foundation's decode is `Formula.ofNat`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma decode_eq_ofNat (n : ℕ) :
    Encodable.decode (α := Sentence) n = Formula.ofNat n := rfl

/-- The step applied to the history of earlier values computes `tsc` (following `Formula.ofNat`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tscStep_spec (n : ℕ) : tscStep ((List.range n).map tsc) = tsc n := by
  cases n with
  | zero =>
      rw [tsc_eq, decode_eq_ofNat, Formula.ofNat]
      rfl
  | succ e =>
      have h1 : e.unpair.2.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
      have h2 : e.unpair.2.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
      have hget1 : ((List.range (e + 1)).map tsc).getD e.unpair.2.unpair.1 0
          = tsc e.unpair.2.unpair.1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1]; rfl
      have hget2 : ((List.range (e + 1)).map tsc).getD e.unpair.2.unpair.2 0
          = tsc e.unpair.2.unpair.2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h2]; rfl
      simp only [tscStep, List.length_map, List.length_range, hget1, hget2]
      rw [tsc_eq (e + 1), decode_eq_ofNat, Formula.ofNat]
      simp only [tsc_eq, decode_eq_ofNat]
      rcases hi : e.unpair.1 with _ | _ | _ | _ | _ | i
      · simp
      · simp [digitLen]
      all_goals first
        | (cases hφ : Formula.ofNat (α := ℕ) e.unpair.2.unpair.1 with
          | none => simp
          | some φ =>
              cases hψ : Formula.ofNat (α := ℕ) e.unpair.2.unpair.2 with
              | none => simp
              | some ψ => simp; omega)
        | simp

/-- The step is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tscStep_primrec : Primrec tscStep := by
  have hi : Primrec fun p : List ℕ × ℕ => p.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hc : Primrec fun p : List ℕ × ℕ => p.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have ha : Primrec fun p : List ℕ × ℕ => p.1.getD p.2.unpair.2.unpair.1 0 :=
    (Primrec.list_getD 0).comp Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp hc))
  have hb : Primrec fun p : List ℕ × ℕ => p.1.getD p.2.unpair.2.unpair.2 0 :=
    (Primrec.list_getD 0).comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp hc))
  have hi0 : PrimrecPred fun p : List ℕ × ℕ => p.2.unpair.1 = 0 := Primrec.eq.comp hi (Primrec.const 0)
  have hi1 : PrimrecPred fun p : List ℕ × ℕ => p.2.unpair.1 = 1 := Primrec.eq.comp hi (Primrec.const 1)
  have hi234 : PrimrecPred fun p : List ℕ × ℕ =>
      p.2.unpair.1 = 2 ∨ p.2.unpair.1 = 3 ∨ p.2.unpair.1 = 4 :=
    (Primrec.eq.comp hi (Primrec.const 2)).or
      ((Primrec.eq.comp hi (Primrec.const 3)).or (Primrec.eq.comp hi (Primrec.const 4)))
  have hab : PrimrecPred fun p : List ℕ × ℕ =>
      p.1.getD p.2.unpair.2.unpair.1 0 = 0 ∨ p.1.getD p.2.unpair.2.unpair.2 0 = 0 :=
    (Primrec.eq.comp ha (Primrec.const 0)).or (Primrec.eq.comp hb (Primrec.const 0))
  have hi4 : PrimrecPred fun p : List ℕ × ℕ => p.2.unpair.1 = 4 := Primrec.eq.comp hi (Primrec.const 4)
  have hinner : Primrec fun p : List ℕ × ℕ =>
      if p.1.getD p.2.unpair.2.unpair.1 0 = 0 ∨ p.1.getD p.2.unpair.2.unpair.2 0 = 0 then 0
      else p.1.getD p.2.unpair.2.unpair.1 0 + p.1.getD p.2.unpair.2.unpair.2 0 +
        (if p.2.unpair.1 = 4 then 2 else 1) :=
    Primrec.ite hab (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.nat_add.comp ha hb)
        (Primrec.ite hi4 (Primrec.const 2) (Primrec.const 1)))
  have hatom : Primrec fun p : List ℕ × ℕ => digitLen (p.2.unpair.2 + 5) + 2 :=
    Primrec.nat_add.comp (digitLen_primrec.comp (Primrec.nat_add.comp hc (Primrec.const 5)))
      (Primrec.const 2)
  exact Primrec.nat_casesOn Primrec.list_length (Primrec.const 0)
    (Primrec.ite hi0 (Primrec.const 2)
      (Primrec.ite hi1 hatom (Primrec.ite hi234 hinner (Primrec.const 0)))).to₂

/-- `tsc` is primitive recursive (course-of-values recursion on codes).
Source: mandate T1.4
Kind: P
Fidelity: n/a -/
lemma tsc_primrec : Primrec tsc := by
  have h := Primrec.nat_strong_rec (fun (_ : Unit) n => tsc n)
    (g := fun _ hist => some (tscStep hist))
    (Primrec.option_some.comp (tscStep_primrec.comp Primrec.snd)).to₂
    (fun _ n => by rw [tscStep_spec])
  exact h.comp (Primrec.const ()) Primrec.id

/-- `sizeBound n = 2^{2^n}` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sizeBound_primrec : Primrec sizeBound := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have h2 : Primrec fun n : ℕ => 2 ^ n := hpow.comp (Primrec.const 2) Primrec.id
  exact (hpow.comp (Primrec.const 2) h2).of_eq (fun n => rfl)

/-- The smallness test on codes through `tsc`: false on non-codes, else `tokenSize ≤ sizeBound`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallCode_eq_tsc (n c : ℕ) :
    smallCode n c = if tsc c = 0 then false else decide (tsc c - 1 ≤ sizeBound n) := by
  rw [tsc_eq]
  unfold smallCode
  cases Encodable.decode (α := Sentence) c with
  | none => simp
  | some φ =>
      simp only [Option.map_some, Option.getD_some, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel]
      exact decide_eq_decide.2 Iff.rfl

/-- **The smallness test on codes is primitive recursive**, hence computable — on `ℕ` alone,
through `tsc` (so no `Primcodable Sentence` instance is needed; FAF's lives in its
construction layer). `Nat.Primrec tsc` *is* `Primrec (tokenSize : Sentence → ℕ)` under that
instance.
Source: mandate T1.4
Kind: P
Fidelity: exact -/
theorem smallCode_primrec : Primrec₂ smallCode := by
  have hle' : PrimrecPred fun p : ℕ × ℕ => tsc p.2 - 1 ≤ sizeBound p.1 :=
    Primrec.nat_le.comp (Primrec.nat_sub.comp (tsc_primrec.comp Primrec.snd) (Primrec.const 1))
      (sizeBound_primrec.comp Primrec.fst)
  have hle : Primrec fun p : ℕ × ℕ => decide (tsc p.2 - 1 ≤ sizeBound p.1) := by
    obtain ⟨_, h⟩ := hle'
    exact h.of_eq (fun p => decide_eq_decide.2 Iff.rfl)
  have h : Primrec fun p : ℕ × ℕ =>
      if tsc p.2 = 0 then false else decide (tsc p.2 - 1 ≤ sizeBound p.1) :=
    Primrec.ite (Primrec.eq.comp (tsc_primrec.comp Primrec.snd) (Primrec.const 0))
      (Primrec.const false) hle
  exact (h.of_eq (fun p => (smallCode_eq_tsc p.1 p.2).symm)).to₂

end Cleanroom.Bli.BliTransfer.AttemptB
