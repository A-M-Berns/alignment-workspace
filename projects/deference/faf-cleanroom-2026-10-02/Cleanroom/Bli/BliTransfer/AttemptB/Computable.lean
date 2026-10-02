import Cleanroom.Bli.BliTransfer.AttemptB.Transfer
import Cleanroom.Bli.BliTransfer.AttemptB.SmallCode

/-!
# `bli-transfer` · attempt B · Computable: `ComputableMarket (overlay Q ov)` (T1.4)

The overlay inherits `Q`'s computable-market certificate: its rational quote table is
`quote' n c := if smallCode n c then quote n c else ovQ n c`, where `quote` is `Q`'s table (a
`Nat.Partrec.Code` computes it; `Nat.Partrec.of_eq_tot` turns the membership certificate into
computability), `ovQ` is a computable code-level table for `ov`, and `smallCode n c` decides
whether `c` decodes to a sentence small on day `n`. A `Nat.Partrec.Code` for the new table is
recovered by `Nat.Partrec.Code.exists_code`.

Two computability inputs are hypotheses of `overlay_computableMarket`:

* `Computable₂ (fun n c => encode (ovQ n c))` — `ov`'s computability on codes (encoded values,
  so no `Primcodable ℚ` instance is needed outside FAF's construction layer), which for any concrete overlay is a separate proof
  (the mandate allows it as a disclosed field of the certificate);
* `Computable₂ smallCode` — the smallness test on codes, **proved** in `SmallCode.lean` by a
  course-of-values recursion on Foundation's formula codes (`smallCode_primrec`).

`overlay_isLogicalInductor_of_transfer'` is the headline with `hcomp` discharged from these:
the transfer for every e.c. trader and `ov`'s code-level computability are its only hypotheses.

Sources: mandate T1.4.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- The smallness test on codes is computable (`SmallCode.smallCode_primrec`).
Source: mandate T1.4
Kind: L
Fidelity: exact -/
theorem smallCode_computable : Computable₂ smallCode :=
  smallCode_primrec.to_comp

/-- **The overlay is a computable market** given `Q`'s certificate, a computable code-level
table for `ov`, and the computable smallness test.
Source: mandate T1.4
Kind: C
Fidelity: exact
Hyps: (a) `hQ`, `hov`; (a) `hovQ`/`hovc` — `ov`'s presentation on codes and its computability
(a hypothesis by the mandate's allowance); (a) `hsmall` — `smallCode_computable` -/
theorem overlay_computableMarket (Q : History) (hQ : ComputableMarket Q)
    (ov : ℕ → Sentence → ℚ) (hov : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1)
    (ovQ : ℕ → ℕ → ℚ) (hovQ : ∀ n ψ, ovQ n (Encodable.encode ψ) = ov n ψ)
    (hovc : Computable₂ fun n c => Encodable.encode (ovQ n c)) (hsmall : Computable₂ smallCode) :
    ComputableMarket (overlay Q ov) := by
  obtain ⟨hrange, quote, code, hquote, hcode⟩ := hQ
  -- `Q`'s table is computable on paired codes
  have hQnat : Nat.Partrec (fun z : ℕ => Encodable.encode (quote z.unpair.1 z.unpair.2)) :=
    Nat.Partrec.of_eq_tot (Nat.Partrec.Code.exists_code.2 ⟨code, rfl⟩) hcode
  have hQcomp : Computable (fun z : ℕ => Encodable.encode (quote z.unpair.1 z.unpair.2)) :=
    Partrec.nat_iff.2 hQnat
  have hquoteE : Computable (fun p : ℕ × ℕ => Encodable.encode (quote p.1 p.2)) :=
    (hQcomp.comp (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)).of_eq
      (fun p => by simp)
  -- the new table
  let quote' : ℕ → ℕ → ℚ := fun n c => if smallCode n c then quote n c else ovQ n c
  have hq' : Computable (fun p : ℕ × ℕ => Encodable.encode (quote' p.1 p.2)) := by
    have h := Computable.cond (c := fun p : ℕ × ℕ => smallCode p.1 p.2) hsmall hquoteE hovc
    exact h.of_eq (fun p => by
      simp only [quote']
      cases smallCode p.1 p.2 <;> simp)
  have hcomp : Computable (fun z : ℕ => Encodable.encode (quote' z.unpair.1 z.unpair.2)) :=
    (hq'.comp Computable.unpair).of_eq (fun z => rfl)
  obtain ⟨code', hcode'⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hcomp)
  refine ⟨overlay_mem_Icc hrange hov, quote', code', fun n φ => ?_, fun z => ?_⟩
  · simp only [quote', smallCode_encode]
    by_cases hs : SmallOn n φ
    · simp [hs, hquote n φ]
    · simp [hs, hovQ n φ]
  · rw [hcode']
    exact Part.mem_some _

/-- **The headline with computability discharged**: given the transfer for every e.c. trader
and a computable code-level table for `ov`, the overlay is a logical inductor.
Source: mandate T1 (`overlay_isLogicalInductor'`)
Kind: C
Fidelity: exact for the stated hypotheses
Hyps: (a) `hQ`; (a) `htrans` — the certificate's output for every e.c. trader, explicit here;
(a) `hovQ`/`hovc` — `ov`'s computability -/
theorem overlay_isLogicalInductor_of_transfer' (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (htrans : ∀ Tr : Trader, EfficientlyComputable Tr → EfficientlyComputable (E.spliceTrader Tr))
    (ovQ : ℕ → ℕ → ℚ) (hovQ : ∀ n ψ, ovQ n (Encodable.encode ψ) = ov n ψ)
    (hovc : Computable₂ fun n c => Encodable.encode (ovQ n c)) :
    IsLogicalInductor (overlay Q ov) DP :=
  overlay_isLogicalInductor_of_transfer Q DP ov E htrans
    (overlay_computableMarket Q hQ.marketComputable ov E.ov_range ovQ hovQ hovc
      smallCode_computable)

end Cleanroom.Bli.BliTransfer.AttemptB
