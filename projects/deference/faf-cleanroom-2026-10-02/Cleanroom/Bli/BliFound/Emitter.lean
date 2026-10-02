import Cleanroom.Bli.BliFound.Bridge
import Cleanroom.Bli.BliFound.State
import LogicalInduction.Framework.Machine.WriteOutMachine
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `bli-found` · Emitter: state atoms are not machine-nameable (stretch S2)

**The claim.** "Traders never touch state atoms" has a generator-side form: no efficiently
metered *emitter* can write the state atoms out. FAF's `MachineSentenceCodes φ` says a
polynomial-time machine writes, on the unary day `d`, a block-well-formed bit word whose
tokens `TokenFold.decodeBits (F (unaryDay d)) = undigitize (bitsToDigits (F (unaryDay d)))`
parse (`parseRpn`) to `φ d`. That is the same digit pipeline the bridge lemma meters, so the
same argument gives the **emitter bridge** `machineSentenceCodes_eventually_small`: a
machine-metered sentence family is eventually day-small. Hence a family of state atoms whose
write-outs are long infinitely often — `sizeBound n ≤ Nat.log 4 (q n)` for infinitely many
`n` — is not machine-nameable (`not_machineSentenceCodes_stateAtom`), by `stateAtom_large`.

Sources: mandate S2; bli-slides-002/030 ("traders don't touch large sentences", generator side);
[[bli-program]] §2.1.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-- **The emitter bridge.** A machine-metered sentence family (`MachineSentenceCodes`, FAF's
polynomial-time write-out class) is eventually day-small: `∃ N, ∀ d ≥ N, SmallOn d (φ d)`. The
route is the bridge lemma's — the FP output-length polynomial, the digit/token bounds on
`undigitize ∘ bitsToDigits`, the parse-size lemma with both escape bounds, and the growth
arithmetic — applied to a single parsed block instead of a strategy.
Source: mandate S2; FAF `MachineSentenceCodes` (`Framework/Machine/WriteOutMachine.lean:505`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem machineSentenceCodes_eventually_small {φ : ℕ → Sentence} (h : MachineSentenceCodes φ) :
    ∃ N, ∀ d ≥ N, SmallOn d (φ d) := by
  obtain ⟨s, ⟨F, hF, -, hdec⟩, hparse⟩ := h
  obtain ⟨C, hC⟩ := tokenSize_le_of_structured
  obtain ⟨p, hp⟩ := Complexity.Cobham.output_length_poly_of_mem_FP hF
  set A := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i with hA
  set E := p.natDegree with hE
  obtain ⟨N, hN⟩ := eventually_poly_le_two_pow ((C + 6) * (A + 1)) E
  refine ⟨N, fun d hd => ?_⟩
  -- the token stream is the trader pipeline's
  have hsd : s d = undigitize (bitsToDigits (F (unaryDay d))) := by
    rw [← hdec d]; rfl
  set ds := bitsToDigits (F (unaryDay d)) with hds
  have hts_len : (s d).length ≤ ds.length := by rw [hsd]; exact length_undigitize_le ds
  have hts_lt : ∀ t ∈ s d, t < 4 ^ ds.length := by
    rw [hsd]; exact fun t ht => lt_pow_length_of_mem_undigitize ht
  have hS : Monotone fun L => 2 ^ (C * L) + C := fun a b hab => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.mul_le_mul_left C hab)
    exact Nat.add_le_add_right this C
  have hbound := tokenSize_le_of_parseRpn (fun L => 2 ^ (C * L) + C) hS hC (s d).length (s d)
    (hparse d) hts_lt
  have hL : (s d).length - ([] : List ℕ).length ≤ ds.length := by
    simp only [List.length_nil, Nat.sub_zero]; exact hts_len
  have hmono := hS hL
  simp only at hmono
  have hsize : tokenSize (φ d) ≤ bridgeBound C ds.length := by
    unfold bridgeBound
    calc tokenSize (φ d) ≤ ((s d).length - ([] : List ℕ).length) *
          (4 ^ ds.length + (2 ^ (C * ((s d).length - ([] : List ℕ).length)) + C) + 3) := hbound
      _ ≤ ds.length * (4 ^ ds.length + (2 ^ (C * ds.length) + C) + 3) :=
          Nat.mul_le_mul hL (Nat.add_le_add_right (Nat.add_le_add_left hmono _) 3)
  -- the digit length is polynomial in the day
  have hdig : ds.length ≤ p.eval d := by
    rw [hds, length_bitsToDigits]
    have := hp (unaryDay d)
    rw [length_unaryDay] at this
    omega
  have hpoly : p.eval d + 1 ≤ (A + 1) * (d + 1) ^ E := by
    have h1 := polynomial_eval_le p d
    have h2 : 1 ≤ (d + 1) ^ E := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hexp : (C + 6) * (p.eval d + 1) ≤ 2 ^ d := by
    calc (C + 6) * (p.eval d + 1) ≤ (C + 6) * ((A + 1) * (d + 1) ^ E) :=
          Nat.mul_le_mul_left _ hpoly
      _ = (C + 6) * (A + 1) * (d + 1) ^ E := by ring
      _ ≤ 2 ^ d := hN d hd
  unfold SmallOn sizeBound
  calc tokenSize (φ d) ≤ bridgeBound C ds.length := hsize
    _ ≤ bridgeBound C (p.eval d) := bridgeBound_mono C hdig
    _ ≤ 2 ^ ((C + 6) * (p.eval d + 1)) := bridgeBound_le C _
    _ ≤ 2 ^ (2 ^ d) := Nat.pow_le_pow_right (by norm_num) hexp

/-- **N+ for the emitter bridge**: FAF's day-varying atom family `n ↦ ⌜aₙ⌝`
(`machineSentenceCodes_atom`: a token whose *value* grows with the day) is eventually day-small.
Source: mandate S2 (witness); FAF `Framework/Machine/Witnesses.lean:189`
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem machineSentenceCodes_atom_eventually_small :
    ∃ N, ∀ d ≥ N, SmallOn d (Formula.atom d : Sentence) :=
  machineSentenceCodes_eventually_small machineSentenceCodes_atom

/-- **N+ for the emitter bridge, growing word**: FAF's conjunction of the first `n` atoms
(`machineSentenceCodes_conjRange`: the token *count* grows with the day) is eventually day-small.
Source: mandate S2 (witness); FAF `Framework/Machine/Witnesses.lean:209`
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem machineSentenceCodes_conjRange_eventually_small :
    ∃ N, ∀ d ≥ N, SmallOn d
      (sentenceConjunction ((List.range d).map (fun j => (Formula.atom j : Sentence)))) :=
  machineSentenceCodes_eventually_small machineSentenceCodes_conjRange

/-- **State atoms are not machine-nameable (S2).** If the write-out codes `q n` are long
infinitely often (`sizeBound n ≤ Nat.log 4 (q n)`, i.e. at least `2^{2^n}` base-4 digits), no
polynomial-time emitter writes the family `n ↦ stateAtom n (q n)`: the contrapositive of the
emitter bridge through `stateAtom_large`. This is the honest generator-side form of "traders
never touch state atoms".
Source: mandate S2; bli-paper-032 (the state atom is longer than every sentence it prices)
Kind: C (composes `machineSentenceCodes_eventually_small` with `stateAtom_large`; regraded from P after audit r2 N5)
Fidelity: stronger: the hypothesis is "infinitely often", not "always"
Hyps: (a) -/
theorem not_machineSentenceCodes_stateAtom (q : ℕ → ℕ)
    (hq : ∀ N, ∃ n ≥ N, sizeBound n ≤ Nat.log 4 (q n)) :
    ¬ MachineSentenceCodes (fun n => stateAtom n (q n)) := by
  intro h
  obtain ⟨N, hN⟩ := machineSentenceCodes_eventually_small h
  obtain ⟨n, hn, hlong⟩ := hq N
  exact stateAtom_large hlong n le_rfl (hN n hn)

/-- **Witness (S2)**: the family with `q n = 4 ^ sizeBound n` (exactly `sizeBound n + 1` digits)
is not machine-nameable.
Source: mandate S2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem not_machineSentenceCodes_stateAtom_pow :
    ¬ MachineSentenceCodes (fun n => stateAtom n (4 ^ sizeBound n)) :=
  not_machineSentenceCodes_stateAtom _ fun N => ⟨N, le_rfl, by
    rw [Nat.log_pow (by norm_num)]⟩

end Cleanroom.Bli.BliFound
