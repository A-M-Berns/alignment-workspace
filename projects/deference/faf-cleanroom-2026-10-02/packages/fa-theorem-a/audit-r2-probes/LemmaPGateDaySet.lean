import Cleanroom.Fa.FaTheoremA.LemmaP

/-!
# Audit r2 (fidelity) probe — `lemmaP` accepts a price-dependent day-set

`lemmaP`'s Fidelity line and the ledger row (adopted in repair round 1 from audit r1 fidelity N7)
say: "an `EF` denotes a continuous function of the day's prices, so a `{0,1}`-valued one is
constant in the prices on each day — `hE01` forces `E` to be a price-independent day-set, which
is precisely the note's e.c. `E ⊆ ℕ⁺`". That reasoning holds for a feature that is `{0,1}`-valued
at *every* price vector; `hE01` only asks `(E n).denote A ∈ {0,1}` at `A`'s *realized* prices.
So the upper gate `Ind_δ(a_n > q)` of `A`'s own quote — a price-dependent feature — is an
admissible `E` whenever the quote never lands inside the ramp band `(q, q + δ)`, and `lemmaP`
then gives `a_n → c` along the days `{n | a_n ≥ q + δ}` selected by `A`'s own quote. The note's
e.c. day-sets are the price-independent special case: the Lean is *stronger* than the docstring
says, not "nearly exact". Not imported by the library.
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- Lemma P along the day-set selected by the gate `Ind_δ(a_n > q)` on `A`'s own quote: if the
quote never lands in the band `(q, q + δ)` (so the gate is `{0,1}`-valued at `A`'s prices) and
`Y_n → c` along the days with `a_n ≥ q + δ`, then `a_n → c` along those days. The day-set depends
on `A`'s prices; `lemmaP` accepts it with no change. -/
theorem probe_lemmaP_gate_dayset {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n)) (q δ : ℚ) (hδ : 0 < δ)
    (hband : ∀ n, (Y n).expect A n ≤ (q : ℝ) ∨ (q : ℝ) + δ ≤ (Y n).expect A n) {c : ℝ}
    (hY : Tendsto (realized H f X)
      (atTop ⊓ 𝓟 {n | (quoteRampAbove Y q δ n).denote A = 1}) (𝓝 c)) :
    Tendsto (quoteSeq Y A)
      (atTop ⊓ 𝓟 {n | (quoteRampAbove Y q δ n).denote A = 1}) (𝓝 c) := by
  refine lemmaP pkg hworldA (quoteRampAbove_pgenerable Y pkg.quote_codes q δ)
    (fun n => ?_) hY
  rcases hband n with h | h
  · left
    rw [quoteRampAbove_denote Y hδ]
    exact (ctsInd_eq_zero_iff hδ _ _).2 h
  · right
    exact (quoteRampAbove_eq_one_iff Y hδ A n).2 (by linarith)

/-- The selected day-set is `{n | q + δ ≤ a_n}` — a set defined by `A`'s realized prices. -/
theorem probe_gate_dayset_eq {A : History} (Y : ℕ → LUV) (q δ : ℚ) (hδ : 0 < δ) :
    {n | (quoteRampAbove Y q δ n).denote A = 1} = {n | (q : ℝ) + δ ≤ (Y n).expect A n} := by
  ext n
  simp only [Set.mem_setOf_eq, quoteRampAbove_eq_one_iff Y hδ A n]
  constructor <;> intro h <;> linarith

#print axioms probe_lemmaP_gate_dayset
#print axioms probe_gate_dayset_eq

end Cleanroom.Fa.FaTheoremA
