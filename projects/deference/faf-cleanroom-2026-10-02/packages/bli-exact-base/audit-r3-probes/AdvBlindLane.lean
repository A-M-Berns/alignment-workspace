import Cleanroom.Bli.BliExactBase.Live

/-!
# Probe (bli-exact-base audit r3, adversarial): the quotation guard `OwnQuoteLane` holds at
every history — through a quote code that never reads the price

Repair round 2 replaced `ReflectsRounded` by `Open.OwnQuoteLane C round P`: there is a predicate
`T` with a FAF `BooleanQuoteCode` such that `T ⟨m, ⟨⌜φ⌝, r⟩⟩ ↔ round m (P m φ) = r` and the
literals are that code's quotation atoms. The docstring of `Live.quoteLane_clause_inhabited`
says the clause `OwnQuoteLane ∧ LiveLane` "is not inhabited for free: a constant lane fails it,
and a non-computable market has no quote code of its cell truth". But `round : ℕ → ℝ → ℕ` is
existentially quantified in all three OPEN rows and nothing ties it to the cells, the
representatives or the price. With the constant rounding `round m x := 0`, the predicate
"`round m (P m φ) = r`" is "`r = 0`" for **every** history `P`, computable or not; its quote code
(`blindCode`, by `BooleanQuoteCode.ofComputable`) is a program that ignores the price; the
family whose literals are its quotation atoms (`blindFamily`, cells `{0, 1}`, representatives
`1`/`0`) is a `CellFamilyT (paperDP 𝗜𝚺₁)`, is an own quote lane of every history
(`blindFamily_ownQuoteLane`), and is live on `smallCodes` (`blindFamily_live`, by the same
machine-metered-family argument as the splice's lane). So the lane clause of
`worldMarket_exists`, `bundleMarket_LI_exists` and `weakening_exists` holds at every history
(`lane_clause_for_every_history`), exactly as round 1's `ReflectsRounded ∧ LiveLane` did; the
"not inhabited for free" sentence is false, and `quoteLane_clause_inhabited`'s N+ is again at a
clause no market can fail.

Under this lane `D_NNUcell` at a pinned coordinate reads `P n φ = P n ⌜blind(n+1, ⌜φ⌝, 0)⌝`
(`blind_identity`): today's price of `φ` equals today's price of a theory-valid atom
(`blindLit_zero_valid`) that no stage `n` mentions and that says nothing about `φ` — not
self-trust. It closes no row: an LI prices the e.c. sequence of provable atoms
`n ↦ blind(n+1, ⌜⊥⌝, 0)` toward `1` and `⊥` toward `0`, so (α)/(β) are not satisfiable this way,
and under `D_PCsmall` the weakening's identity at `⊥` forces the provable atom to price `0`, which
a one-share-a-day trader exploits. The point is that the rows still quantify over lanes the
program never meant, so "with its own quote lane" is not what the statements force. Fix: tie
`round` to the lane — e.g. require that the rounding is a genuine cell map with the
representative in the cell and sensitive to the price (`∀ m x ∈ [0,1], round m x ∈ C.cells m`,
`|C.rep m (round m x) − x| ≤ w m` with `w m < 1`, and `round m 0 ≠ round m 1`), or fix the grid
family (`round m x := ⌊x · d m⌋`-style with `d m ≥ 2`) instead of quantifying over `round`; the
splice's lane at `roundR`/`rep01` satisfies both.
-/

namespace Cleanroom.Bli.BliExactBase.AuditR3Adv

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB Cleanroom.Bli.BliAssemble
open Cleanroom.Bli.BliExactBase

/-- The price-blind predicate: the folded input's cell index is `0`. -/
def blindTruth (z : ℕ) : Prop := z.unpair.2.unpair.2 = 0

theorem blindTruth_computable : ComputablePred blindTruth := by
  rw [ComputablePred.computable_iff]
  have hr : Computable fun z : ℕ => z.unpair.2.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  refine ⟨fun z => decide (z.unpair.2.unpair.2 = 0), ?_, ?_⟩
  · exact ((Primrec.eq.decide.to_comp).comp hr (Computable.const 0) : _)
  · funext z
    simp [blindTruth]

/-- A FAF quote code of the price-blind predicate. -/
noncomputable def blindCode : BooleanQuoteCode 𝗜𝚺₁ blindTruth :=
  BooleanQuoteCode.ofComputable blindTruth_computable

/-- The blind lane's literal: the quotation atom of `blindCode` at `⟨m, ⟨⌜φ⌝, r⟩⟩`. -/
noncomputable def blindLit (m : ℕ) (φ : Sentence) (r : ℕ) : Sentence :=
  blindCode.sentence (Nat.pair m (Nat.pair (Encodable.encode φ) r))

lemma blindLit_reflected (m : ℕ) (φ : Sentence) (r : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) : v.Holds (blindLit m φ r) ↔ r = 0 := by
  have := blindCode.reflected (paperQuotationPresentation 𝗜𝚺₁)
    (Nat.pair m (Nat.pair (Encodable.encode φ) r)) v hv
  simpa [blindLit, blindTruth, Nat.unpair_pair] using this

/-- The cell-`0` literal is theory-valid. -/
lemma blindLit_zero_valid (m : ℕ) (φ : Sentence) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) : v.Holds (blindLit m φ 0) :=
  (blindLit_reflected m φ 0 v hv).2 rfl

/-- **The blind lane**: cells `{0, 1}`, representatives `1` at cell `0` and `0` at cell `1`. -/
noncomputable def blindFamily : CellFamilyT (paperDP 𝗜𝚺₁) where
  literal := blindLit
  cells := twoCells
  rep := fun _ r => if r = 0 then 1 else 0
  excl := by
    intro m φ r r' hne v hv ⟨h, h'⟩
    rw [blindLit_reflected m φ r v hv] at h
    rw [blindLit_reflected m φ r' v hv] at h'
    exact hne (h.trans h'.symm)
  exh := by
    intro m φ v hv
    exact ⟨0, by simp [twoCells], (blindLit_reflected m φ 0 v hv).2 rfl⟩

/-- **`OwnQuoteLane` holds at every history** with the constant rounding `0`. -/
theorem blindFamily_ownQuoteLane (P : History) : OwnQuoteLane blindFamily (fun _ _ => 0) P :=
  ⟨blindTruth, blindCode,
    fun m φ r => by
      simp only [blindTruth, Nat.unpair_pair]
      exact eq_comm,
    fun _ _ _ => rfl⟩

/-- The blind literal of a fixed coordinate is a machine-metered family in the day (the proof
of `QuoteLane.spliceCellSentenceQ_machineSentenceCodes` at `blindCode`). -/
theorem blindLit_machineSentenceCodes (c r : ℕ) :
    MachineSentenceCodes fun n => blindCode.sentence (Nat.pair (n + 1) (Nat.pair c r)) := by
  have hd : MachineDigits fun n => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair blindCode.code (Nat.pair (n + 1) (Nat.pair c r))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            (MachineDigits.const blindCode.code)
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
              (MachineDigits.const (Nat.pair c r))))))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

theorem blindLit_eventually_small (c r : ℕ) :
    ∃ N, ∀ n ≥ N, SmallOn n (blindCode.sentence (Nat.pair (n + 1) (Nat.pair c r))) :=
  machineSentenceCodes_eventually_small (blindLit_machineSentenceCodes c r)

/-- **The blind lane is live on the small codes** (the proof of `Live.spliceCF_live`). -/
theorem blindFamily_live : LiveLane blindFamily smallCodes := by
  refine ⟨fun φ => ?_, fun m => ⟨1, by simp [blindFamily, twoCells], by simp [blindFamily]⟩⟩
  obtain ⟨N, hN⟩ := Live.smallOn_eventually φ
  obtain ⟨N₀, h₀⟩ := blindLit_eventually_small (Encodable.encode φ) 0
  obtain ⟨N₁, h₁⟩ := blindLit_eventually_small (Encodable.encode φ) 1
  refine ⟨max N (max N₀ N₁), fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨hnN, hn0, hn1⟩ := hn
  rw [mem_pinned]
  refine ⟨List.mem_map.2 ⟨φ, mem_smallList.2 (SmallOn.mono (Nat.le_succ n) (hN n hnN)), rfl⟩,
    fun r hr => ?_⟩
  simp only [blindFamily, twoCells, Finset.mem_insert, Finset.mem_singleton] at hr
  show SmallOn n (blindLit (n + 1) (sentenceOfCode (Encodable.encode φ)) r)
  rw [sentenceOfCode_encode]
  unfold blindLit
  rcases hr with rfl | rfl
  · exact h₀ n hn0
  · exact h₁ n hn1

/-- **The lane clause of the three OPEN rows holds at every history**, computable or not, with a
quote code that never reads the price. -/
theorem lane_clause_for_every_history (P : History) :
    ∃ (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
      OwnQuoteLane C round P ∧ LiveLane C smallCodes :=
  ⟨blindFamily, fun _ _ => 0, blindFamily_ownQuoteLane P, blindFamily_live⟩

/-- What `D_NNUcell` says under the blind lane at a pinned coordinate: today's price of `φ` is
today's price of the theory-valid atom `blind(n+1, ⌜φ⌝, 0)`. -/
theorem blind_identity (P : History) (n : ℕ) {c : ℕ} (hc : c ∈ pinned blindFamily smallCodes n)
    (hD : D_NNUcell blindFamily smallCodes P) :
    P n (sentenceOfCode c) = P n (blindLit (n + 1) (sentenceOfCode c) 0) := by
  have h := hD n c hc
  change P n (sentenceOfCode c) = ∑ r ∈ twoCells (n + 1),
    ((if r = 0 then (1 : ℚ) else 0 : ℚ) : ℝ) * P n (blindLit (n + 1) (sentenceOfCode c) r) at h
  rw [h, twoCells, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp

end Cleanroom.Bli.BliExactBase.AuditR3Adv
