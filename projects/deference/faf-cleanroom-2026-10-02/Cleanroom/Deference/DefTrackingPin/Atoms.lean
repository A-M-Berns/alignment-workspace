import Cleanroom.Deference.DefTrackingPin.Defs
import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Codes
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.TimelyLearning

/-!
# `def-tracking-pin` · Atoms: forced learning about the fixed market on the ledger atoms (T4)

anson-2-023 (iii) ("`P_n(α_n(φ,q)) → 𝟙[A_n(φ) ≥ q]` as the `α`'s are decided — follows directly
from Garrabrant"): the one-way face of anson-019. Over `li-quote-lane`'s ledger the atom is
`⌜α_{j,n} > q⌝ = (ledgerLuv j n).gt q`, decided **strictly** — true iff `q < a j n` (disclosure (β)
of that package; `q = a j n` is the unconstrained threshold, and the strict pattern is what the
ledger publishes), so the target pattern is `𝟙[q < a_{j,n}]`, mirrored exactly.

It "follows from Garrabrant" — FAF's `lic_provind` (`thm:provind`) — **for an e.c. pattern**:
provability induction is diagonal (day `n`, sentence `n`) and asks for *every* member of the
family to be a theorem, so the true and the refuted atoms must be split into two e.c. families.
The split is `φ_n := if q < a_{j,n} then ⌜α_{j,n} > q⌝ else ⊤` and
`ψ_n := if q < a_{j,n} then ∼⊤ else ⌜α_{j,n} > q⌝`, and their e.c. certificates `hpat` are the
same H-class clause as T1's `hz`, in Boolean form: a machine must emit the polarity pattern of the
table. The (a) instance is a table converging to a limit `≠ q`, where the pattern is eventually
constant: `ledger_atom_learned_ofTendsto`, through an **eventual** form of provability induction
(`provind_eventually_true` / `_false`: FAF's `lic_provind_true` demands the family be theorems at
every day; the one-sided vanishing-error affine provability induction takes an eventual world bound,
so the eventual form is a direct corollary).

The source's *literal* claim (chat 01 L536, "as we condition on later `P`-states") is the eventual
grade at a fixed atom — `atom_eventually_learned`, grade (a), no `hpat`. `ledger_atom_learned` is
the mandate's timely strengthening (day-`n` price of the day-`n` atom), and `hpat` is its price.

Roles: `P` is the reader (the inductor over the ledger-augmented process; in `OneWayPair` the
field `H`); the fixed market is the one whose prices the table `a` records. Scope: one-way.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## Eventual provability induction -/

/-- **Provability induction, eventual form (true side):** an e.c. sentence family whose members
are *eventually* theorems of the completed theory (`∀ᶠ n, ∀ v, v.ConsistentWithTheory DP →
v.Holds (φ n)`) is priced `→ 1` on the diagonal. FAF's `lic_provind_true` asks for every member;
this form takes the one-sided vanishing-error affine provability induction
(`affine_provind_theory_le_const` / `_ge_const`) at the one-share family `sentenceAffine φ`, whose
world bound is eventual. Reader `P`; one-way.
Source: none: infrastructure (FAF `thm:provind`, `lic_provind_true`; the eventual form the (a) instance of T4 and T6's decided-sentence corollary need)
Kind: C
Fidelity: n/a (stronger than FAF's endpoint on the hypothesis side)
Hyps: (a) none -/
theorem provind_eventually_true (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hthm : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (φ n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (φ n)) ≈ₙ fun _ => 1 := by
  have hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hpoly := AffineCombination.sentenceAffine_polySequence φ hφ
  have hbounded := AffineCombination.sentenceAffine_bounded φ P hP
  have hmag : ∃ C : ℝ, ∀ n, (AffineCombination.sentenceAffine φ n).magnitude P ≤ C :=
    ⟨1, fun n => by simp⟩
  have hvalue : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      (AffineCombination.sentenceAffine φ n).value P v.payout = 1 := by
    filter_upwards [hthm] with n hn v hv
    simp [AffineCombination.sentenceAffine, AffineCombination.value, PCWorld.payout, hn v hv]
  have hle := hpoly.affine_provind_theory_le_const P DP hbounded hmag hworld 1
    (fun ε hε => by
      filter_upwards [hvalue] with n hn v hv
      rw [hn v hv]
      linarith)
  have hge := hpoly.affine_provind_theory_ge_const P DP hbounded hmag hworld 1
    (fun ε hε => by
      filter_upwards [hvalue] with n hn v hv
      rw [hn v hv]
      linarith)
  have heq := asympEq_iff_asympLE_asympGE.2 ⟨hle, hge⟩
  simpa using heq

/-- **Provability induction, eventual form (refuted side):** an e.c. sentence family whose members
are eventually refuted by the completed theory is priced `→ 0` on the diagonal. Dual of
`provind_eventually_true`. Reader `P`; one-way.
Source: none: infrastructure (FAF `thm:provind`, `lic_provind_false`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem provind_eventually_false (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ)
    (hdis : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (∼ψ n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (ψ n)) ≈ₙ fun _ => 0 := by
  have hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hpoly := AffineCombination.sentenceAffine_polySequence ψ hψ
  have hbounded := AffineCombination.sentenceAffine_bounded ψ P hP
  have hmag : ∃ C : ℝ, ∀ n, (AffineCombination.sentenceAffine ψ n).magnitude P ≤ C :=
    ⟨1, fun n => by simp⟩
  have hvalue : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      (AffineCombination.sentenceAffine ψ n).value P v.payout = 0 := by
    filter_upwards [hdis] with n hn v hv
    have hfalse : ¬ v.Holds (ψ n) := (PCWorld.holds_neg v (ψ n)).mp (hn v hv)
    simp [AffineCombination.sentenceAffine, AffineCombination.value, PCWorld.payout, hfalse]
  have hle := hpoly.affine_provind_theory_le_const P DP hbounded hmag hworld 0
    (fun ε hε => by
      filter_upwards [hvalue] with n hn v hv
      rw [hn v hv]
      linarith)
  have hge := hpoly.affine_provind_theory_ge_const P DP hbounded hmag hworld 0
    (fun ε hε => by
      filter_upwards [hvalue] with n hn v hv
      rw [hn v hv]
      linarith)
  have heq := asympEq_iff_asympLE_asympGE.2 ⟨hle, hge⟩
  simpa using heq

/-! ## The ledger atoms at a fixed threshold are an e.c. sentence family -/

/-- One poly-fueled program emits `⌜α_{j,n} > q⌝`'s code from `n`, for a fixed item `j` and
threshold `q` — the pair shell of `li-quote-lane`'s T1.3 certificate with the day as the only
variable.
Source: none: infrastructure (`li-quote-lane` `encode_ledgerLuv_gt`)
Kind: L
Fidelity: n/a -/
lemma ledgerLuv_gt_polySentenceCodes (j : ℕ) (q : ℚ) :
    PolySentenceCodes (fun n => (ledgerLuv j n).gt q) :=
  ⟨_, (((PolyFueled.const 1).pair ((PolyFueled.const (cleanroomBaseTag + ledgerFamily)).pair
    (PolyFueled.id.pair ((PolyFueled.const j).pair
      (PolyFueled.const (Encodable.encode q)))))).succ_comp).of_eq
    fun n => (encode_ledgerLuv_gt j n q).symm⟩

/-- **The ledger atoms at a fixed threshold are an e.c. sentence family** (FAF's
`MachineSentenceCodes`), for every item `j` and rational `q`.
Source: none: infrastructure (T4's (a) certificate)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerLuv_gt_sentenceCodes (j : ℕ) (q : ℚ) :
    MachineSentenceCodes (fun n => (ledgerLuv j n).gt q) :=
  MachineSentenceCodes.ofPolySentenceCodes (ledgerLuv_gt_polySentenceCodes j q)

/-! ## T4: the reader learns the polarity pattern -/

/-- In every world consistent with every stage of the ledger process, `⌜α_{j,n} > q⌝` holds iff
`q < a j n` (strict; disclosure (β) of `li-quote-lane`). The theory-level form of
`ledgerLuv_decided_by`.
Source: none: infrastructure (`li-quote-lane` `ledgerLuv_decided_by`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ledgerLuv_gt_holds_iff (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (j n : ℕ) (q : ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerProcess base a e)) :
    v.Holds ((ledgerLuv j n).gt q) ↔ q < a j n := by
  have hs : n ≤ max (max n j) (max (Encodable.encode q) ((e j).e n)) ∧
      j ≤ max (max n j) (max (Encodable.encode q) ((e j).e n)) ∧
      Encodable.encode q ≤ max (max n j) (max (Encodable.encode q) ((e j).e n)) ∧
      (e j).e n ≤ max (max n j) (max (Encodable.encode q) ((e j).e n)) :=
    ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have h := ledgerLuv_decided_by base a e j n q hs v (hv _)
  constructor
  · intro hh
    by_contra hq
    exact h.2 (not_lt.1 hq) hh
  · exact h.1

/-- **T4 (headline). Forced learning about the fixed market on the ledger atoms** (anson-2-023
(iii), the one-way face of anson-019): for a reader `P` over the ledger process (every stage
satisfiable), a fixed item `j` and threshold `q`, the reader's day-`n` price of the ledger atom
`⌜α_{j,n} > q⌝` tends to its polarity: `P_n(⌜α_{j,n} > q⌝) ≈ₙ 𝟙[q < a_{j,n}]` (strict, as the
ledger decides it — disclosure (β)), **provided the polarity pattern is e.c.**: `hpat₁`, `hpat₂`
are FAF `MachineSentenceCodes` certificates for the two subfamilies `φ_n := if q < a_{j,n} then
⌜α_{j,n} > q⌝ else ⊤` (the affirmed atoms, padded with `⊤`) and `ψ_n := if q < a_{j,n} then ∼⊤
else ⌜α_{j,n} > q⌝` (the refuted atoms, padded with `∼⊤`). Route: FAF's `lic_provind` on the two
families, with `ledgerLuv_decided_by` supplying the theorem / refutation clauses through
`ConsistentWithTheory`; on each day exactly one family carries the atom. "Follows directly from
Garrabrant" — it does, for an e.c. pattern. **`hpat` is the H-class clause** (T1's `hz` in Boolean
form): a trader must emit the table's polarity pattern; FAF has one trader class, so the corpus's
relativized reading is a modelling substitution. Reader `P` (the pair's `H`); the fixed market's
prices are the table `a`; one-way.
**Grade of the source's own claim.** Chat 01 L536 reads "`P_n(α_n(φ,q)) → 𝟙[A_n(φ) ≥ q]` *as we
condition on later `P`-states observing the relevant `D⁺`-resolution*" — the **eventual** grade
(a fixed day-`n` atom, the reader's day `m → ∞`), which holds at grade (a) with no pattern
hypothesis (`atom_eventually_learned` below). This theorem is the mandate's **timely** reading
(the day-`n` price of the day-`n` atom), strictly stronger; `hpat` is the price of that
strengthening, not of the source's claim (audit r1 fidelity N2, adversarial N3).
Source: anson-2-023 (iii) (chat 01 L526–540); anson-019 (one-way face); FAF `thm:provind`
Kind: C
Fidelity: stronger: timely (day `n`) in place of the source's conditional-on-resolution (eventual) form, at the cost of `hpat`; variant: plain trader class — the e.c. polarity pattern (`hpat`) in place of the corpus's unstated class; strict polarity `q < a` (disclosure (β)), with `q = a_{j,n}` unconstrained
Hyps: (c) `hpat₁`, `hpat₂` — e.c. certificates for the polarity pattern of the table, in FAF's one trader class (the cost of the timely strengthening; the source's eventual form is (a)); all else (a) -/
theorem ledger_atom_learned (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (j : ℕ) (q : ℚ)
    (hpat₁ : MachineSentenceCodes (fun n => if q < a j n then (ledgerLuv j n).gt q else ⊤))
    (hpat₂ : MachineSentenceCodes (fun n => if q < a j n then ∼(⊤ : Sentence)
      else (ledgerLuv j n).gt q)) :
    (fun n => P n ((ledgerLuv j n).gt q)) ≈ₙ (fun n => if q < a j n then 1 else 0) := by
  have h1 := lic_provind_true P (ledgerProcess base a e) _ hpat₁
    (fun n v hv => by
      by_cases hq : q < a j n
      · rw [if_pos hq]
        exact (ledgerLuv_gt_holds_iff base a e j n q v hv).2 hq
      · rw [if_neg hq]
        exact PCWorld.holds_top v) hworld
  have h2 := lic_provind_false P (ledgerProcess base a e) _ hpat₂
    (fun n v hv => by
      by_cases hq : q < a j n
      · rw [if_pos hq, PCWorld.holds_neg, PCWorld.holds_neg, not_not]
        exact PCWorld.holds_top v
      · rw [if_neg hq, PCWorld.holds_neg]
        exact fun hh => hq ((ledgerLuv_gt_holds_iff base a e j n q v hv).1 hh)) hworld
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [asympEq_iff_eventuallyWithin.1 h1 ε hε,
    asympEq_iff_eventuallyWithin.1 h2 ε hε] with n hn1 hn2
  by_cases hq : q < a j n
  · rw [if_pos hq] at hn1 ⊢
    exact hn1
  · rw [if_neg hq] at hn2 ⊢
    exact hn2

/-- **anson-2-023 (iii) at its own (eventual) grade, (a):** for any inductor `P` over the ledger
process (every stage satisfiable), a fixed item `j`, day `n` and threshold `q`, the reader's price
of the day-`n` atom tends, as the *reader's* day `m → ∞`, to the atom's polarity `𝟙[q < a_{j,n}]`
— the source's "`P_n(α_n(φ,q)) → 𝟙[A_n(φ) ≥ q]` as we condition on later `P`-states observing the
relevant `D⁺`-resolution" (chat 01 L536), rendered as the eventual limit at a fixed atom. No
`hpat`: the family is constant (`MachineSentenceCodes.const`), and `provind_eventually_true` /
`_false` apply through `ledgerLuv_gt_holds_iff`. The timely form (day-`n` price of the day-`n`
atom) is `ledger_atom_learned`, which costs `hpat`. Reader `P`; one-way. (Proof after the audit r1
adversarial probe `AdvT4EventualGrade.lean`.)
Source: anson-2-023 (iii) (chat 01 L536, the literal eventual claim); FAF `thm:provind`
Kind: L (one application of `provind_eventually_true` / `_false` at a constant family)
Fidelity: exact (the source's eventual grade; strict polarity, disclosure (β))
Hyps: (a) none -/
theorem atom_eventually_learned (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (j n : ℕ) (q : ℚ) :
    (fun m => P m ((ledgerLuv j n).gt q)) ≈ₙ (fun _ => if q < a j n then 1 else 0) := by
  by_cases hq : q < a j n
  · rw [if_pos hq]
    exact provind_eventually_true P _ (fun _ => (ledgerLuv j n).gt q)
      (MachineSentenceCodes.const _)
      (Filter.Eventually.of_forall fun _ v hv =>
        (ledgerLuv_gt_holds_iff base a e j n q v hv).2 hq) hworld
  · rw [if_neg hq]
    exact provind_eventually_false P _ (fun _ => (ledgerLuv j n).gt q)
      (MachineSentenceCodes.const _)
      (Filter.Eventually.of_forall fun _ v hv =>
        (PCWorld.holds_neg v _).2 fun hh => hq ((ledgerLuv_gt_holds_iff base a e j n q v hv).1 hh))
      hworld

/-- **T4 at a one-way pair:** `ledger_atom_learned` with the reader `p.H` and the table `p.a`
(the fixed market `p.A`'s prices, `p.a_eq`). Reader `p.H`; fixed market `p.A`; one-way.
Source: anson-2-023 (iii); anson-019
Kind: L (instance of `ledger_atom_learned`)
Fidelity: as `ledger_atom_learned`
Hyps: (c) `hpat₁`, `hpat₂` (as `ledger_atom_learned`) -/
theorem OneWayPair.atom_learned (p : OneWayPair) (j : ℕ) (q : ℚ)
    (hpat₁ : MachineSentenceCodes (fun n => if q < p.a j n then (ledgerLuv j n).gt q else ⊤))
    (hpat₂ : MachineSentenceCodes (fun n => if q < p.a j n then ∼(⊤ : Sentence)
      else (ledgerLuv j n).gt q)) :
    (fun n => p.H n ((ledgerLuv j n).gt q)) ≈ₙ (fun n => if q < p.a j n then 1 else 0) :=
  haveI := p.H_inductor
  ledger_atom_learned p.H p.DPH p.a p.e p.hworld j q hpat₁ hpat₂

/-- **T4, the (a) instance: a convergent table.** If item `j`'s table converges to a real `L ≠ q`,
the reader's price of `⌜α_{j,n} > q⌝` tends to `𝟙[q < L]` with **no pattern hypothesis**: the
polarity pattern is eventually constant, the atoms at a fixed threshold are an e.c. family
(`ledgerLuv_gt_sentenceCodes`), and the eventual provability induction `provind_eventually_true` /
`_false` applies. Grade (a). This is the instance on which `hpat` is idle; the witness on which
`ledger_atom_learned` as written is load-bearing would need a table whose polarity pattern at `q`
has no limit. Reader `P`; one-way.
Source: anson-2-023 (iii), the decided-limit case; FAF `thm:provind`
Kind: C
Fidelity: exact (at a convergent table)
Hyps: (a) none -/
theorem ledger_atom_learned_ofTendsto (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (j : ℕ) (q : ℚ) {L : ℝ} (hconv : Tendsto (fun n => (a j n : ℝ)) atTop (𝓝 L))
    (hne : (q : ℝ) ≠ L) :
    (fun n => P n ((ledgerLuv j n).gt q)) ≈ₙ (fun _ => if (q : ℝ) < L then 1 else 0) := by
  rcases lt_or_gt_of_ne hne with hqL | hLq
  · rw [if_pos hqL]
    refine provind_eventually_true P _ _ (ledgerLuv_gt_sentenceCodes j q) ?_ hworld
    filter_upwards [hconv.eventually (lt_mem_nhds hqL)] with n hn v hv
    exact (ledgerLuv_gt_holds_iff base a e j n q v hv).2 (by exact_mod_cast hn)
  · rw [if_neg (not_lt.2 hLq.le)]
    refine provind_eventually_false P _ _ (ledgerLuv_gt_sentenceCodes j q) ?_ hworld
    filter_upwards [hconv.eventually (gt_mem_nhds hLq)] with n hn v hv
    rw [PCWorld.holds_neg]
    intro hh
    have := (ledgerLuv_gt_holds_iff base a e j n q v hv).1 hh
    have hlt : (a j n : ℝ) < q := by exact_mod_cast hn
    have hlt' : (q : ℝ) < a j n := by exact_mod_cast this
    linarith

end Cleanroom.Deference.DefTrackingPin
