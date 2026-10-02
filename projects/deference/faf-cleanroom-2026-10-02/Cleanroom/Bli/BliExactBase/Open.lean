import Cleanroom.Bli.BliExactBase.Tables
import LogicalInduction.Framework.Affine

/-!
# `bli-exact-base` — M4's routes and the named weakening as OPEN statements; bli-slides-043 as a
definition; K7 as the finite-horizon form of M4

**bli-slides-043 as a definition** (`ExactlyEnforceable 𝒞 DP`): a constraint family `𝒞` on a
market is *exactly enforceable* over `DP` when some computable market satisfying the logical
induction criterion over `DP` satisfies `𝒞` on every day. The programme's (ii). K7 gives the
**finite-horizon instance** for every `H` (`exactlyEnforceable_segment`, Kind `C` from K7a/K7b):
the segment forms of small-sentence coherence and non-dogmatism are exactly enforceable over
`paperDP 𝗜𝚺₁` for every horizon. The all-days form is the first OPEN row
(`exactlyEnforceable_allDays`): K7 is the finite-horizon form of M4, every `H` is achievable,
the infinite case is open (findings F2).

**M4's routes, stated and OPEN** (program §3.8, §4 row M4, §5 partial credit). Each row's
quote-lane clause is `OwnQuoteLane ∧ LiveLane ∧ D_NNUcell`. **`LiveLane`** (repair round 1;
audit r1 B1 of both lenses) is the non-vacuity guard — every sentence is pinned from some day on,
and every day has a cell of representative `< 1` — without which the clause is satisfiable by a
cell family whose literals are never small (`Live.padFamily`), for which `D_NNUcell` is vacuous
and round 0's statement of route (β) is a theorem of FAF's LIA
(`Live.bundleMarket_LI_exists_unguarded`; findings F21). **`OwnQuoteLane`** (repair round 2;
audit r2 fidelity B2, adversarial N1) is the quotation guard — the literals are the quotation
atoms of a `BooleanQuoteCode` of the market's own cell truth — without which (round 1's
`ReflectsRounded`, truth values only) the lane clause held at *every* history through a constant
`⊤`/`⊥` lane (`Live.certFamily`), under which `D_NNUcell` read "today's price is tomorrow's
rounded price", not self-trust. The splice's own lane satisfies both guards
(`Live.spliceCF_ownQuoteLane`, `Live.spliceCF_live`; `Live.quoteLane_clause_inhabited`), so they
are satisfiable by the package's objects, and under them `D_NNUcell` says that every sentence's
price is, from some day on, the representative-weighted sum of the prices of the market's own
next-day quotation atoms for it (`Live.D_NNUcell_own_pointwise`), atoms no stage has decided
(`Live.ownQuoteLane_literal_undecided`).

* (α) **the world market** `worldMarket_exists`: a computable logical inductor over
  `paperDP 𝗜𝚺₁` that is small-sentence coherent on every day **and** exactly `D_NNUcell` on every
  day with **its own quote lane** (`OwnQuoteLane`: the cell literals are the quotation atoms of a
  quote code of the market's own cell truth, so they reflect the rounding of its own price in
  every completed-theory world) on the index of the small codes;
* (β) **the bundle market as an LI** `bundleMarket_LI_exists`: the same without coherence —
  `D_NNUcell` by definition (`Bundle.lean`'s object extended to all coordinates and days),
  LIC the open part; `Bundle.bundleMarket_not_acceptable` says this cannot come from a per-day
  acceptance search at its own prices;
* (γ) projection is excluded (needs `bli-transfer`'s Route A; not stated);
* **the named weakening** `weakening_exists`: a computable, small-sentence-coherent, exactly
  self-trusting market (own quote lane) that no efficiently computable trader of **bounded
  per-day magnitude** exploits. `BoundedMagnitude Tr V` (`∃ M, ∀ n, (Tr.strat n).magnitude V ≤ M`,
  FAF's `Strategy.magnitude` — the ℓ¹ share volume of the day's strategy against `V`) is defined
  here: FAF has the day-wise `magnitude` and the total `Trader.magnitude` (a `tsum`), not the
  uniform bound. The obstruction theorem does **not** refute it (findings F3): the bundle
  trade's cumulative value along the trajectory is the self-trust bias of FAF's `thm:st`,
  bounded for any inductor.

Nothing in this module is marked proved beyond `exactlyEnforceable_segment`; the ledger Status
of the four OPEN rows is `open`, with the obstruction cited as the reason the static route is
closed.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB Cleanroom.Bli.BliAssemble

/-- **The index of the small codes**: the codes of `smallList n` (listing every day-`n` small
sentence; `IndexCodes` by `sentenceOfCode_encode`).
Source: mandate § Definitions (`segmentIndex`)
Kind: D
Fidelity: exact -/
def smallCodes (n : ℕ) : List ℕ := (smallList n).map Encodable.encode

/-- The small codes are genuine codes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem smallCodes_indexCodes (n : ℕ) : IndexCodes smallCodes n := by
  intro c hc
  obtain ⟨φ, -, rfl⟩ := List.mem_map.1 hc
  simp

/-- **A cell family reflects the rounding of a market's own price**: in every completed-theory
world of `DP`, the literal `C.literal m φ r` holds iff `round m (P m φ) = r`. This is the
quote-lane condition that makes a `D_NNUcell` claim about `P` be about *`P`'s* cells
(`bli-found`'s `cellSentence_reflected` at FAF's LIA; `QuoteLane.lean` for the splice).
Source: mandate § 3 (a) ("what makes any linkage claim about the spliced market")
Kind: D
Fidelity: exact -/
def ReflectsRounded (DP : DeductiveProcess) (C : CellFamilyT DP) (round : ℕ → ℝ → ℕ)
    (P : History) : Prop :=
  ∀ (m : ℕ) (φ : Sentence) (r : ℕ) (v : PCWorld), v.ConsistentWithTheory DP →
    (v.Holds (C.literal m φ r) ↔ round m (P m φ) = r)

/-- **A live quote lane** (the non-vacuity guard of the OPEN rows; repair round 1): every sentence
is pinned from some day on — its code is in the day-`(n+1)` index and all its day-`(n+1)` cell
literals are small on day `n` — and every day has a cell of representative `< 1` (the obstruction
theorem's guard). Without the first clause the `D_NNUcell` conjunct is vacuous for a family whose
literals are never small (audit r1 B1; `Live.padFamily`, `Live.padFamily_not_live`); the splice's
own lane satisfies both (`Live.spliceCF_live`).
Source: audit r1 fidelity B1 / adversarial B1; mandate § 3 (b) (`pinned_eventually`)
Kind: D
Fidelity: exact -/
def LiveLane {DP : DeductiveProcess} (C : CellFamilyT DP) (index : ℕ → List ℕ) : Prop :=
  (∀ φ : Sentence, ∃ N₀, ∀ n ≥ N₀, Encodable.encode φ ∈ pinned C index n) ∧
  ∀ m, ∃ r ∈ C.cells m, C.rep m r < 1

/-- **The cell literals are the quotation atoms of a quote code of the market's own cell truth**
(repair round 2; audit r2 fidelity B2, adversarial N1): there is a predicate `T` on `ℕ` with a
FAF `BooleanQuoteCode` (a program code `code.code` whose folded universal schemas `𝗜𝚺₁` proves at
exactly the inputs where `T` holds), such that on the folded inputs `⟨m, ⟨⌜φ⌝, r⟩⟩` the predicate
`T` is exactly "`round m (P m φ) = r`", and `C.literal m φ r` is that code's quotation atom at
`⟨m, ⟨⌜φ⌝, r⟩⟩`. This is what "its own quote lane" means ([[bli-program]] §2.6/§3.8: `D-NNU`
over the market's own `quote_{n+1,φ,I}` literals): the literal is a sentence *about `P`'s rounded
price, named through a program deciding it* — not merely a sentence with the right truth value in
every completed-theory world, which `ReflectsRounded` alone allows and which the constant lane
(`⊤` at the selected cell, `⊥` elsewhere) satisfies for every history (`Live.certFamily`).
Consequences proved in `Live.lean`: `ReflectsRounded` (`ownQuoteLane_reflectsRounded`); every
day-`(n+1)` literal is an atom no sentence of stage `n` mentions (`ownQuoteLane_literal_fresh`,
`ownQuoteLane_stageFresh`) and so is undecided at stage `n` (`ownQuoteLane_literal_undecided`);
a lane with a constant literal is excluded (`Live.not_ownQuoteLane_of_constant`). The splice's own
lane satisfies it (`Live.spliceCF_ownQuoteLane`). The values of `T` off the sentence-coded inputs
are immaterial, which is why `T` is quantified.
Source: [[bli-program]] §2.6, §3.8; mandate § 3 (a); audit r2 fidelity B2, adversarial N1
Kind: D
Fidelity: exact -/
def OwnQuoteLane (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ) (P : History) : Prop :=
  ∃ (T : ℕ → Prop) (code : BooleanQuoteCode 𝗜𝚺₁ T),
    (∀ (m : ℕ) (φ : Sentence) (r : ℕ),
      T (Nat.pair m (Nat.pair (Encodable.encode φ) r)) ↔ round m (P m φ) = r) ∧
    ∀ (m : ℕ) (φ : Sentence) (r : ℕ),
      C.literal m φ r = code.sentence (Nat.pair m (Nat.pair (Encodable.encode φ) r))

/-- **Bounded per-day magnitude**: a uniform bound on the ℓ¹ share volume of the trader's day-`n`
strategy against `V` (FAF's `Strategy.magnitude`).
Source: [[bli-program]] §5 (the named weakening: "bounded-magnitude e.c. trader"); mandate § 9;
FAF `Strategy.magnitude` (`Framework/Affine.lean:95`)
Kind: D
Fidelity: exact (per-day uniform bound; FAF's `Trader.magnitude` is the total `tsum`) -/
def BoundedMagnitude (Tr : Trader) (V : History) : Prop :=
  ∃ M : ℝ, ∀ n, (Tr.strat n).magnitude V ≤ M

/-- **bli-slides-043 (ii) as a definition**: the constraint family `𝒞` is exactly enforceable over
`DP` when a computable logical inductor over `DP` satisfies it.
Source: bli-slides-043 (ii); mandate § 10 (a)
Kind: D
Fidelity: exact -/
def ExactlyEnforceable (𝒞 : History → DeductiveProcess → Prop) (DP : DeductiveProcess) : Prop :=
  ∃ P : History, ComputableMarket P ∧ IsLogicalInductor P DP ∧ 𝒞 P DP

/-- **K7 is the finite-horizon form of M4**: for every horizon `H`, small-sentence coherence and
non-dogmatism on `[0, H)` are exactly enforceable over `paperDP 𝗜𝚺₁` — by the spliced inductor.
Source: bli-slides-043 (ii) for `{D_PC (small), D_ND}` on a finite segment; mandate § 10 (a)
(`exactlyEnforceable_segment`)
Kind: C
Fidelity: exact (small form of `D_PC`; segment)
Hyps: (a) -/
theorem exactlyEnforceable_segment (H : ℕ) :
    ExactlyEnforceable (fun P DP => D_PCsmall_on H P DP ∧ D_ND_on H P DP) (paperDP 𝗜𝚺₁) :=
  ⟨spliceHistory H segmentPrice, (spliceSegment_isLogicalInductor H).marketComputable,
    spliceSegment_isLogicalInductor H, segment_D_PCsmall_on H, segment_D_ND_on H⟩

/-- **OPEN — bli-slides-043 (ii) at infinity for `{D_PC (small), D_ND}`**: a computable logical
inductor over `paperDP 𝗜𝚺₁` small-sentence coherent and non-dogmatic on **every** day. K7 gives
every finite horizon; `thm:ifp` cannot reach infinitely many coordinates
(`not_overgeneral_ifp`), and no other route is known in the run.
Source: bli-slides-043 (ii), bli-slides-044 (small form); mandate § 10 (a) ("the all-days form as
§ 9's OPEN")
Kind: OPEN
Fidelity: weaker: small form of `D_PC`
Hyps: n/a -/
theorem exactlyEnforceable_allDays :
    ExactlyEnforceable (fun P DP => D_PCsmall P DP ∧ D_ND P DP) (paperDP 𝗜𝚺₁) := by
  sorry

/-- **OPEN — M4 route (α), the world market**: a computable logical inductor over `paperDP 𝗜𝚺₁`
that is small-sentence coherent on every day and exactly `D_NNUcell` on every day, with cell
literals that are the quotation atoms of a quote code of its own cell truth (its own quote lane,
`OwnQuoteLane`; hence reflecting the rounding of its own price, `Live.ownQuoteLane_reflectsRounded`,
and fresh at the stage, `Live.ownQuoteLane_literal_undecided`) on the index of the small codes —
the program's P12. The obstruction theorem (`Obstruction.obstruction`) closes the per-day
market-maker route to it; no other route is known.
The lane is guarded by `LiveLane` (repair round 1): every sentence eventually pinned, so the
`D_NNUcell` conjunct is pointwise self-trust at every sentence from some day on at the market's
own quotation atoms (`Live.D_NNUcell_own_pointwise`). Repair round 2 replaced the reflection
conjunct `ReflectsRounded` by `OwnQuoteLane`, which implies it: with reflection alone the lane
clause held at every history through a constant `⊤`/`⊥` lane (audit r2 fidelity B2,
adversarial N1; `Live.certFamily`), under which `D_NNUcell` was not self-trust.
Source: [[bli-program]] §3.8 (M4), §4 row M4, §5; bli-slides-044; mandate § 9 (α)
Kind: OPEN
Fidelity: weaker: small form of `D_PC`; guarded (`OwnQuoteLane ∧ LiveLane`; round 0's form admitted padding, round 1's a quote-free lane)
Hyps: n/a -/
theorem worldMarket_exists :
    ∃ (P : History) (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
      ComputableMarket P ∧ IsLogicalInductor P (paperDP 𝗜𝚺₁) ∧ D_PCsmall P (paperDP 𝗜𝚺₁) ∧
      OwnQuoteLane C round P ∧ LiveLane C smallCodes ∧
      D_NNUcell C smallCodes P := by
  sorry

/-- **OPEN — M4 route (β), the bundle market as an LI**: a computable logical inductor over
`paperDP 𝗜𝚺₁` that is exactly `D_NNUcell` on every day with its own quote lane (`OwnQuoteLane`:
the literals are the quotation atoms of a quote code of its own cell truth; coherence not
required). `Bundle.bundleMarket_not_acceptable` says it is not the output of a per-day acceptance
search at its own prices; whether some other construction yields it is open. The lane is
guarded by `LiveLane` (repair round 1): round 0's unguarded form is a theorem of FAF's LIA with a
never-small lane (`Live.bundleMarket_LI_exists_unguarded`, findings F21), so it did not state the
bundle market as an LI; round 1's `ReflectsRounded ∧ LiveLane` form admitted a quote-free
constant lane (`Live.certFamily`, audit r2); this form does state it — every sentence's own
next-day quotation atoms are eventually small and the identity holds at each.
Source: bli-soto-b-025 (the implicit LIC claim); mandate § 9 (β)
Kind: OPEN
Fidelity: exact (guarded; the bundle's grid and representatives are not fixed, as the program
does not fix them)
Hyps: n/a -/
theorem bundleMarket_LI_exists :
    ∃ (P : History) (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
      ComputableMarket P ∧ IsLogicalInductor P (paperDP 𝗜𝚺₁) ∧
      OwnQuoteLane C round P ∧ LiveLane C smallCodes ∧
      D_NNUcell C smallCodes P := by
  sorry

/-- **OPEN — the named weakening** (program §5 partial credit): a computable, small-sentence
coherent, exactly self-trusting market (own quote lane, `OwnQuoteLane`) that no efficiently
computable trader of bounded per-day magnitude exploits. Not refuted by the obstruction theorem:
the bundle trade's cumulative value along the trajectory is the self-trust bias of FAF's
`thm:st`, bounded for any inductor (findings F3).
The lane is guarded by `LiveLane` (repair round 1) and `OwnQuoteLane` (repair round 2).
`BoundedMagnitude` is this package's definition (FAF has the day-wise `Strategy.magnitude` and
the `tsum` total, not the uniform bound).
Source: [[bli-program]] §5 (partial credit for M4); mandate § 9
Kind: OPEN
Fidelity: weaker: small form of `D_PC`; guarded (`OwnQuoteLane ∧ LiveLane`)
Hyps: n/a (`BoundedMagnitude` is a definition of this package, disclosed) -/
theorem weakening_exists :
    ∃ P : History, ComputableMarket P ∧ D_PCsmall P (paperDP 𝗜𝚺₁) ∧
      (∃ (C : CellFamilyT (paperDP 𝗜𝚺₁)) (round : ℕ → ℝ → ℕ),
        OwnQuoteLane C round P ∧ LiveLane C smallCodes ∧
          D_NNUcell C smallCodes P) ∧
      ∀ Tr : Trader, EfficientlyComputable Tr → BoundedMagnitude Tr P →
        ¬ Tr.Exploits P (paperDP 𝗜𝚺₁) := by
  sorry

end Cleanroom.Bli.BliExactBase
