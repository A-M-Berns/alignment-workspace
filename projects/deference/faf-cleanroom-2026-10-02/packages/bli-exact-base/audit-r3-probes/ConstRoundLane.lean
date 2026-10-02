import Cleanroom.Bli.BliExactBase.Live

/-!
# Probe (bli-exact-base audit r3, fidelity): `OwnQuoteLane ∧ LiveLane` holds at every history,
through a constant rounding

Repair round 2's guard `Open.OwnQuoteLane C round P` asks for a `BooleanQuoteCode 𝗜𝚺₁ T` with
`T ⟨m, ⟨⌜φ⌝, r⟩⟩ ↔ round m (P m φ) = r` and the literals its quotation atoms. The rounding
`round : ℕ → ℝ → ℕ` is existentially quantified in each OPEN row, and nothing asks it to depend on
the price. With the constant rounding `round m x := 0`, the predicate `T` is "the third component
is `0`" — computable whatever `P` is — so a FAF `BooleanQuoteCode` for it exists
(`BooleanQuoteCode.ofComputable`), its quotation atoms form a `CellFamilyT (paperDP 𝗜𝚺₁)`
(`constLane`: cell `0`'s literal is theory-provable, cell `1`'s theory-refuted), the lane is an own
quote lane of **every** history (`constLane_ownQuoteLane`) and is live on `smallCodes`
(`constLane_live`: the literals are quotation atoms of a fixed code, machine-metered in the day).
Hence `own_live_lane_for_every_history`: the lane conjuncts `OwnQuoteLane ∧ LiveLane` of the three
M4 OPEN rows restrict the market not at all — exactly the situation audit r2 (adversarial N1)
found for round 1's clause, one level up. The claim in `Live.quoteLane_clause_inhabited`'s
docstring ("the clause `OwnQuoteLane ∧ LiveLane` is not inhabited for free … a non-computable
market has no quote code of its cell truth") is false as stated: the cell truth of a constant
rounding needs no information about the market.

What `D_NNUcell` says under this lane (`constLane_identity`): at every pinned coordinate, today's
price of `φ` equals today's price of the day-`(n+1)` cell-`1` literal — a quotation atom that
every completed-theory world refutes (`constLane_lit1_refuted`). No logical inductor meets that
at `⊤` (its price of a refuted sentence tends to `0`), and `weakening_exists` cannot be met
through it either (a bounded-magnitude trader sells the refuted literal, priced `1` at `⊤`, every
day), so the lane closes no row: it makes each row a disjunction over lanes that includes a
degenerate one, and makes the "not inhabited for free" claim false. A one-line fix is to require
the rounding to hit every cell (`∀ m r, r ∈ C.cells m → ∃ x, round m x = r`) or, more faithfully
to [[bli-program]] §2.6, to fix `round` to a rounding onto a grid with representatives inside
their cells.
-/

namespace Cleanroom.Bli.BliExactBase.AuditR3Fid

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB Cleanroom.Bli.BliAssemble
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Live

/-- The cell truth of the constant rounding: the folded input's cell component is `0`. -/
def constTruth (z : ℕ) : Prop := z.unpair.2.unpair.2 = 0

/-- It is computable, whatever the market. -/
theorem constTruth_computable : ComputablePred constTruth := by
  rw [ComputablePred.computable_iff]
  have hr : Computable fun z : ℕ => z.unpair.2.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  refine ⟨fun z => decide (z.unpair.2.unpair.2 = 0), ?_, ?_⟩
  · exact ((Primrec.eq.decide.to_comp).comp hr (Computable.const 0) : _)
  · funext z
    simp [constTruth]

/-- A FAF quote code of the constant cell truth. -/
noncomputable def constCode : BooleanQuoteCode 𝗜𝚺₁ constTruth :=
  BooleanQuoteCode.ofComputable constTruth_computable

/-- The constant rounding. -/
noncomputable def constRound (_m : ℕ) (_x : ℝ) : ℕ := 0

/-- Reflection of the constant code's literals. -/
lemma constCode_reflected (z : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    v.Holds (constCode.sentence z) ↔ constTruth z :=
  constCode.reflected (paperQuotationPresentation 𝗜𝚺₁) z v hv

/-- **The constant-rounding lane**: the quotation atoms of `constCode`, cells `{0, 1}`,
representatives `0`, `1`. -/
noncomputable def constLane : CellFamilyT (paperDP 𝗜𝚺₁) where
  literal m φ r := constCode.sentence (Nat.pair m (Nat.pair (Encodable.encode φ) r))
  cells := twoCells
  rep := fun _ r => (r : ℚ)
  excl := by
    intro m φ r r' hne v hv ⟨h, h'⟩
    rw [constCode_reflected _ v hv] at h h'
    simp only [constTruth, Nat.unpair_pair] at h h'
    exact hne (h.trans h'.symm)
  exh := by
    intro m φ v hv
    refine ⟨0, by simp [twoCells], ?_⟩
    rw [constCode_reflected _ v hv]
    simp [constTruth, Nat.unpair_pair]

/-- **The constant-rounding lane is an own quote lane of every history.** -/
theorem constLane_ownQuoteLane (P : History) : OwnQuoteLane constLane constRound P :=
  ⟨constTruth, constCode,
    fun m φ r => by simp [constTruth, constRound, Nat.unpair_pair, eq_comm],
    fun _ _ _ => rfl⟩

/-- Its day-`(n+1)` literal of a fixed coordinate and cell is a machine-metered family in the
day (the proof of `QuoteLane.spliceCellSentenceQ_machineSentenceCodes` at `constCode`). -/
theorem constLane_lit_machine (c r : ℕ) :
    MachineSentenceCodes fun n => constCode.sentence (Nat.pair (n + 1) (Nat.pair c r)) := by
  have hd : MachineDigits fun n => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair constCode.code (Nat.pair (n + 1) (Nat.pair c r))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            (MachineDigits.const constCode.code)
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
              (MachineDigits.const (Nat.pair c r))))))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

/-- **The constant-rounding lane is live on the small codes.** -/
theorem constLane_live : LiveLane constLane smallCodes := by
  refine ⟨fun φ => ?_, fun m => ⟨0, by simp [constLane, twoCells],
    by show ((0 : ℕ) : ℚ) < 1; norm_num⟩⟩
  obtain ⟨N, hN⟩ := smallOn_eventually φ
  obtain ⟨N₀, h₀⟩ :=
    machineSentenceCodes_eventually_small (constLane_lit_machine (Encodable.encode φ) 0)
  obtain ⟨N₁, h₁⟩ :=
    machineSentenceCodes_eventually_small (constLane_lit_machine (Encodable.encode φ) 1)
  refine ⟨max N (max N₀ N₁), fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨hnN, hn0, hn1⟩ := hn
  rw [mem_pinned]
  refine ⟨List.mem_map.2 ⟨φ, mem_smallList.2 (SmallOn.mono (Nat.le_succ n) (hN n hnN)), rfl⟩,
    fun r hr => ?_⟩
  simp only [constLane, twoCells, Finset.mem_insert, Finset.mem_singleton] at hr
  show SmallOn n (constCode.sentence (Nat.pair (n + 1)
    (Nat.pair (Encodable.encode (sentenceOfCode (Encodable.encode φ))) r)))
  rw [sentenceOfCode_encode]
  rcases hr with rfl | rfl
  · exact h₀ n hn0
  · exact h₁ n hn1

/-- **The lane conjuncts of the three M4 OPEN rows hold at every history.** -/
theorem own_live_lane_for_every_history (P : History) :
    ∃ (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
      OwnQuoteLane C round P ∧ LiveLane C smallCodes :=
  ⟨constLane, constRound, constLane_ownQuoteLane P, constLane_live⟩

/-- Under the constant-rounding lane, the `D_NNUcell` identity at a coordinate reads: today's
price of `φ` is today's price of the day-`(n+1)` cell-`1` literal. -/
theorem constLane_identity (P : History) (n : ℕ) (φ : Sentence) :
    (P n φ = ∑ r ∈ constLane.cells (n + 1),
        (constLane.rep (n + 1) r : ℝ) * P n (constLane.literal (n + 1) φ r)) ↔
      P n φ = P n (constCode.sentence (Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) 1))) := by
  have hsum : ∑ r ∈ constLane.cells (n + 1),
      (constLane.rep (n + 1) r : ℝ) * P n (constLane.literal (n + 1) φ r) =
      P n (constCode.sentence (Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) 1))) := by
    show ∑ r ∈ twoCells (n + 1), ((r : ℚ) : ℝ) *
      P n (constCode.sentence (Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) r))) = _
    rw [twoCells, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    simp
  rw [hsum]

/-- The cell-`1` literal is refuted in every completed-theory world. -/
theorem constLane_lit1_refuted (n : ℕ) (φ : Sentence) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    ¬ v.Holds (constCode.sentence (Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) 1))) := by
  rw [constCode_reflected _ v hv]
  simp [constTruth, Nat.unpair_pair]

/-- Under the constant-rounding lane and `D_NNUcell`, every sentence's price is, from some day
on, the price of a theory-refuted quotation atom. -/
theorem constLane_D_NNUcell_pointwise (P : History) (hD : D_NNUcell constLane smallCodes P)
    (φ : Sentence) :
    ∃ N₀, ∀ n ≥ N₀,
      P n φ = P n (constCode.sentence (Nat.pair (n + 1) (Nat.pair (Encodable.encode φ) 1))) := by
  obtain ⟨N₀, hN⟩ := D_NNUcell_live_pointwise constLane_live hD φ
  exact ⟨N₀, fun n hn => (constLane_identity P n φ).1 (hN n hn)⟩

end Cleanroom.Bli.BliExactBase.AuditR3Fid
