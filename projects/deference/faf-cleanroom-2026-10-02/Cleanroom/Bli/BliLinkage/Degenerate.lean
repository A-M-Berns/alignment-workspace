import Cleanroom.Bli.BliLinkage.Defs
import Cleanroom.Bli.BliLinkageB.DegenerateCells
import Cleanroom.Bli.BliLinkage.AttemptA.Degenerate

/-!
# `bli-linkage` — K3: no degenerate linked BLI over an inductor whose rounded prices move
(of record)

**Where the attempts agreed and where one repaired the other.** Both attempts proved K3a (under
the degenerate package the base prices every non-today cell literal at `0` and today's at `1`)
and K3b (a one-share trader on a cheap, stage-entailed, infinitely-often-true family exploits;
`hmove` explicit, by `exploits_of_bddBelow_of_unbounded`), and both diagnosed the same gap in
the mandate's K3 plan: the move sentence `∼ lit_{n+1, χ n, todayIdx n}` names *today's rounded
price*, so its `MachineSentenceCodes` certificate is not "from `χ`'s" and is dischargeable only
when the rounded price is eventually fixed, i.e. exactly when `hmove` fails (A's F-A3, B's
FB-14). Attempt A left its conclusion of record with that certificate as a hypothesis
(`AttemptA.no_degenerate_linked_bli`, flagged); attempt B **repaired** it with a price-reading
trader (`sellCells`: sells, for every cell, `price_n(lit_r)` shares of `lit_r`, the coefficient
an expressible feature read by the market machinery, so the trader reads today's cell instead of
naming it) and instantiated the result at FAF's actual LIA over `paperDP 𝗜𝚺₁` with `hmove` the
only hypothesis not about instance data (`InstanceB2.no_degenerate_linked_bli_LIA`, at a *fixed*
coordinate — since repair round 1 flagged: for a fixed sentence `hmove` forces the LIA's limit
price to be exactly `1/2` and is false at `⊥`/`⊤`; the instance of record is the family form
`InstanceK3.no_degenerate_linked_bli_LIA_family`). **Attempt B's is the conclusion of record.**
Attempt A's `buyOne` trader and its two-literal remark survive as the simpler K3b engine and the
N− check that summability is not decorative.

**The "moves" clause.** Both attempts confirm the mandate's reading: the program's derivation
of "moves" from `lic_provind` is a misreading (findings); `hmove` is a hypothesis, grade (a).
No inhabitant of `hmove` at the LIA is shipped: for a fixed sentence it is confined to the
limit-`1/2` boundary and false at `⊥`/`⊤` (`InstanceK3`); for a family it is open in both
directions. The OPEN `BliLinkageB.InstanceMoves.leakQ_rounded_price_moves` (listed in
`bli-linkage-open.txt`, stated once there and not restated) is over `leakQ`/`leakDP` and the
family `memberAtom n`; as stated it instantiates no K3 instance at `paperDP` (it would
instantiate `InstanceK3Grid.no_degenerate_linked_bli_LIA_oneCoord`'s shape over `leakDP` only
with a leak-quoting literal family, T7, not built).

**The package's satisfiability (audit r2 B1; settled at the LIA in repair r3, audit r3 B1).**
`no_degenerate_linked_bli`'s package `PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate` forces the inductor
`Q` to be exactly stage-coherent on the small sentences on every day — it must price every
small tautology at exactly `1` (`LiaPackage.package_forces_valid_one`), doubly-exponentially
many per day. **FAF's LIA cannot, over any deductive process**
(`LiaPackage.not_lia_small_coherent_mixture_exists`: its day-`n` belief state lists at most
polynomially many sentences, `LiaSupport.liaStates_support_card_le_poly`), so every K3
instance at the LIA (`InstanceB2`, `InstanceK3`, `InstanceK3Grid`) is vacuous
(`InstanceK3Local`). Whether some *other* logical inductor is exactly small-coherent is not
settled (a `ComputableMarket` may price every tautology at `1`; its LI-ness is unproved), and
no such inductor is exhibited. **The local form** `no_degenerate_linked_bli_lit` replaces
`E1x` by agreement on the pinned cell literals only (`E1xLit`), which is all K3 ever used
(`degenerate_literal_indicator` is a statement about `P`; `E1x` only transfers it): its LIA
instances (`InstanceK3Local`) demand one listed sentence per day, not the small algebra, and
are not counted out. The superbelief-side predicates are jointly satisfiable with the base
equal to the superbelief in the no-move regime (`InstanceB2Point.pointMass_degenerate_of_still`,
`InstanceK3Grid.pointMass_oneCoord_package_iff_still`), which is all the shipped artifact
checks show.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

section Record

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- **K3a — under the degenerate package the base's prices of tomorrow's cell literals are the
indicator of today's cell**: `Q n (lit_{n+1,c,r}) = [r = t]` where `t` is the degenerate table's
entry at the pinned coordinate `c`. K1 with all the mass on `deg n`.
Source: [[bli-program]] §3.6(iii); bli-paper-043; mandate K3a; attempt B `degenerate_literal_indicator` (A: `degenerate_lit_zero`/`_one`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem degenerate_literal_indicator (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hdeg : Degenerate (stateOf C) P deg) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {t : ℕ}
    (hentry : entryOf c (tableOfCode (deg n)) = some t) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    Q n (C.literal (n + 1) (sentenceOfCode c) r) = if r = t then 1 else 0 :=
  Cleanroom.Bli.BliLinkageB.degenerate_literal_indicator C hcoh hatoms hE5 hE1 hdegS hdeg n hsp
    hc hentry hr

/-- **K3b, the price-reading trader exploits (of record).** `sellCells L d` sells, on day `n`,
`price_n(L n r)` shares of `L n r` for every cell `r < d`. If from day `N` on the market prices
the family as the indicator of `today n` (`hpr`), every stage has a world, a moved day's
"today" literal is refuted by some stage (`hdec`), and there are infinitely many moved days
(**`hmove`, a hypothesis**), the trader exploits: bounded below by `−∑_{i<N} ∑_r |p_{i,r}|`
(the sale `p(p − w)` is `≥ −|p|` for `w ∈ [0,1]`), unbounded above along worlds consistent with
ever-later stages, by FAF's `exploits_of_bddBelow_of_unbounded`.
Source: [[bli-program]] §3.6(iii); desiderata I2; mandate K3b; attempt B `TraderCells.sellCells_exploits` (FB-14)
Kind: P
Fidelity: exact (`hmove` explicit)
Hyps: (a) (`hmove`, `hdec`, `hworld` are hypotheses of the statement) -/
theorem sellCells_exploits (L : ℕ → ℕ → Sentence) (d : ℕ) (V : History) (DP : DeductiveProcess)
    (N : ℕ) (today : ℕ → ℕ)
    (hpr : ∀ n ≥ N, ∀ r < d, V n (L n r) = if r = today n then 1 else 0)
    (htoday : ∀ n ≥ N, today n < d)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      ¬ v.Holds (L n (today n)))
    (hmove : Set.Infinite {n | moved n}) :
    (Cleanroom.Bli.BliLinkageB.sellCells L d).Exploits V DP :=
  Cleanroom.Bli.BliLinkageB.sellCells_exploits L d V DP N today hpr htoday hworld hdec hmove

/-- **The price-reading trader is efficiently computable** whenever the *paired* literal family
`z ↦ L z.unpair.1 z.unpair.2` is machine-metered: FAF's `EfficientlyComputable.ofTradeBlocksBig`
at the constant count `d`, coefficients `(−1) · EF.price` serialized by
`MachineSpliceStream.serialize_price`. No metering of today's cell is asked (the repair of FB-14).
Source: mandate K3b; FAF `ofTradeBlocksBig`, `serialize_price`; attempt B `TraderCells.sellCells_ec`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem sellCells_ec {L : ℕ → ℕ → Sentence} (d : ℕ)
    (hlit : MachineSentenceCodes fun z => L z.unpair.1 z.unpair.2) :
    EfficientlyComputable (Cleanroom.Bli.BliLinkageB.sellCells L d) :=
  Cleanroom.Bli.BliLinkageB.sellCells_ec d hlit

/-- **K3 — no degenerate linked BLI over an inductor whose rounded prices move (conclusion of
record, abstract).** Over `[IsLogicalInductor Q DP]`, a grid with cells `range d` and
`SpuriousEntails`, a coordinate family `χ` pinned from day `N` on, the degenerate table listing
`χ n` at `todayIdx n` (`hentry`), the paired literal family machine-metered (`hψ`), every stage
inhabited (`hworld`), a moved day's "today" literal refuted by some stage (`hdec`), and
**infinitely many moved days (`hmove`)**: no `P` satisfies `PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate`.
Proof: K3a makes the inductor price tomorrow's literals as the indicator of today's cell from
day `N`; `sellCells` then exploits, against `noExploit`. Where the content lives (audit r3
fidelity N5): on a moved day whose refuting stage `k` (from `hdec`) is `≤ n`, the package is
already contradicted by stage coherence alone (every charged day-`n` world holds the literal
`lit_{n+1, χ n, todayIdx n}`, which `D k ⊆ D n`'s worlds refute), with no inductor and no
trader; the exploitation argument carries the theorem only for moved days whose literal is
refuted *after* day `n`. Only `E1x` at the pinned cell literals is used: see
`no_degenerate_linked_bli_lit`.
Source: [[bli-program]] §3.6(iii); desiderata I2; bli-paper-043; bli-soto-a-007; mandate K3 (judged item 3); attempt B `DegenerateCells.no_degenerate_linked_bli_cells`
Kind: C
Fidelity: exact (`hmove` explicit, as mandate § K3 requires; metering asked only of the paired literal family)
Hyps: (a) (`hmove` is the one clause no FAF theorem discharges; at FAF's LIA the full package is empty — `LiaPackage.not_lia_small_coherent_mixture_exists` — so the LIA instances of this theorem are vacuous; the local form `no_degenerate_linked_bli_lit` is the one with LIA instances not counted out) -/
theorem no_degenerate_linked_bli [IsLogicalInductor Q DP] (deg χ todayIdx : ℕ → ℕ)
    (d N : ℕ) (hcells : ∀ n, C.cells (n + 1) = Finset.range d)
    (hpin : ∀ n ≥ N, χ n ∈ pinned C index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (ht : ∀ n, todayIdx n < d)
    (hentry : ∀ n, entryOf (χ n) (tableOfCode (deg n)) = some (todayIdx n))
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n)
    (hψ : MachineSentenceCodes fun z =>
      C.literal (z.unpair.1 + 1) (sentenceOfCode (χ z.unpair.1)) z.unpair.2)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      ¬ v.Holds (C.literal (n + 1) (sentenceOfCode (χ n)) (todayIdx n)))
    (hmove : Set.Infinite {n | moved n}) :
    ¬ (PCPσ atoms DP P ∧ E5σ (stateOf C) S P ∧ E1x Q P ∧ Degenerate (stateOf C) P deg) :=
  Cleanroom.Bli.BliLinkageB.no_degenerate_linked_bli_cells C deg χ todayIdx d N hcells hpin hdegS
    ht hentry hsp hatoms hψ hworld hdec hmove

/-! ### The local form: `E1x` only at the pinned cell literals (repair round 3) -/

/-- **`E1x` restricted to the pinned cell literals**: on every day `n`, for every pinned
coordinate `c` and every cell `r`, the base and the superbelief agree on `lit_{n+1, c, r}`.
Strictly weaker than `E1x` (`e1xLit_of_e1x`): it asks agreement on `|pinned| · d` sentences a
day, not on the whole small algebra. This is all of `E1x` that K3 uses.
Source: this run (repair r3, audit r3 adversarial B1 fix (v)); mandate K3
Kind: D
Fidelity: variant: `E1x` localized to the pinned literals -/
def E1xLit (C : CellFamily 𝒲) (index : ℕ → List ℕ) (Q P : History) : Prop :=
  ∀ n, ∀ c ∈ pinned C index n, ∀ r ∈ C.cells (n + 1),
    P n (C.literal (n + 1) (sentenceOfCode c) r) = Q n (C.literal (n + 1) (sentenceOfCode c) r)

/-- `E1x` implies its localization (pinned literals are day-small).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem e1xLit_of_e1x (hE1 : E1x Q P) : E1xLit C index Q P := fun n c hc r hr =>
  hE1 n _ (by rw [mem_smallSet]; exact ((mem_pinned C index n c).1 hc).2 r hr)

/-- **K3a is a statement about the superbelief**: under `PCPσ ∧ E5σ ∧ Degenerate` the
superbelief itself prices tomorrow's cell literals as the indicator of today's cell, and any
base agreeing with it on those literals (`E1xLit`) does too. `degenerate_literal_indicator` at
`Q := P` with the trivial `E1x P P`, then the local agreement.
Source: this run (repair r3); mandate K3a
Kind: C
Fidelity: stronger: `E1xLit` in place of `E1x`
Hyps: (a) -/
theorem degenerate_literal_indicator_lit (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1xLit C index Q P) {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hdeg : Degenerate (stateOf C) P deg) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {t : ℕ}
    (hentry : entryOf c (tableOfCode (deg n)) = some t) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    Q n (C.literal (n + 1) (sentenceOfCode c) r) = if r = t then 1 else 0 := by
  rw [← hE1 n c hc r hr]
  exact degenerate_literal_indicator C hcoh hatoms hE5 (Q := P) (fun _ _ _ => rfl) hdegS hdeg n
    hsp hc hentry hr

/-- **K3, local form: no degenerate BLI linked to an inductor *on the pinned literals* whose
rounded prices move.** The same hypotheses as `no_degenerate_linked_bli`; the package's
`E1x Q P` replaced by `E1xLit C index Q P` — agreement on tomorrow's cell literals of the
pinned coordinates only. Strictly stronger than `no_degenerate_linked_bli`
(`e1xLit_of_e1x`), and the form whose LIA instances are not counted out: the full `E1x` at
FAF's LIA is unsatisfiable (`LiaPackage.not_lia_small_coherent_mixture_exists`), while
`E1xLit` asks the LIA to list one sentence a day with exact quote `1`
(`InstanceK3Local.lit_package_forces_today_listed`).
Source: this run (repair r3, audit r3 adversarial B1 fix (v)); [[bli-program]] §3.6(iii); mandate K3 (judged item 3)
Kind: C
Fidelity: stronger: `E1xLit` in place of `E1x` (`hmove` explicit, as mandate § K3 requires)
Hyps: (a) (`hmove` is the one clause no FAF theorem discharges) -/
theorem no_degenerate_linked_bli_lit [IsLogicalInductor Q DP] (deg χ todayIdx : ℕ → ℕ)
    (d N : ℕ) (hcells : ∀ n, C.cells (n + 1) = Finset.range d)
    (hpin : ∀ n ≥ N, χ n ∈ pinned C index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (ht : ∀ n, todayIdx n < d)
    (hentry : ∀ n, entryOf (χ n) (tableOfCode (deg n)) = some (todayIdx n))
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n)
    (hψ : MachineSentenceCodes fun z =>
      C.literal (z.unpair.1 + 1) (sentenceOfCode (χ z.unpair.1)) z.unpair.2)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      ¬ v.Holds (C.literal (n + 1) (sentenceOfCode (χ n)) (todayIdx n)))
    (hmove : Set.Infinite {n | moved n}) :
    ¬ (PCPσ atoms DP P ∧ E5σ (stateOf C) S P ∧ E1xLit C index Q P ∧
      Degenerate (stateOf C) P deg) := by
  rintro ⟨hcoh, hE5, hE1, hdeg⟩
  refine Cleanroom.Bli.BliLinkageB.no_inductor_prices_indicator_eventually
    (L := fun n r => C.literal (n + 1) (sentenceOfCode (χ n)) r) (d := d) hψ Q DP N todayIdx
    ?_ (fun n _ => ht n) hworld hdec hmove
  intro n hn r hr
  exact degenerate_literal_indicator_lit C hcoh hatoms hE5 hE1 hdegS hdeg n (hsp n) (hpin n hn)
    (hentry n) (by rw [hcells]; exact Finset.mem_range.2 hr)

end Record

section BuyOne

/-- **K3b, the one-share trader (attempt A's engine, restated).** `buyOne ψ` buys one share of
`ψ n` on day `n`. With bounded partial price sums (`hbdd`, the finite form of `Summable ε`),
every stage inhabited, moved days' sentences entering a stage, and **infinitely many moved days
(`hmove`)**, it exploits. The simpler engine; its instantiation at the degenerate package needs
the family `∼ lit_{n+1, χ n, todayIdx n}` to be machine-metered, which is the gap `sellCells`
closes (FB-14/F-A3).
Source: [[bli-program]] §3.6(iii); desiderata I2; mandate K3b; attempt A `buyOne_exploits` (B: `Trader.buyOne_exploits`)
Kind: P
Fidelity: exact (`hmove` explicit; `hbdd` generalizes `Summable ε`)
Hyps: (a) -/
theorem buyOne_exploits (Q : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (moved : ℕ → Prop)
    (hdec : ∀ n, moved n → ∃ k, ψ n ∈ DP.D k) (hmove : Set.Infinite {n | moved n})
    (C : ℝ) (hbdd : ∀ n, ∑ i ∈ Finset.range (n + 1), Q i (ψ i) ≤ C) :
    (AttemptA.buyOne ψ).Exploits Q DP :=
  AttemptA.buyOne_exploits Q DP hworld ψ moved hdec hmove C hbdd

/-- **The one-share trader is efficiently computable** for a machine-metered family (FAF's
`ofSingleTradeBlocksBig` with the constant feature stream).
Source: mandate K3b; FAF `ofSingleTradeBlocksBig`; attempt A `buyOne_efficientlyComputable`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem buyOne_efficientlyComputable (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    EfficientlyComputable (AttemptA.buyOne ψ) :=
  AttemptA.buyOne_efficientlyComputable ψ hψ

/-- **Summability is not decorative** (N−): with all prices `1` the one-share trader's net worth
in a falsifying world is `−(n+1)`, unbounded below.
Source: desiderata I2; mandate K3 (`degenerate_summable_needed`); attempt A
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem degenerate_summable_needed (ψ : ℕ → Sentence) (Q : History) (hQ : ∀ n, Q n (ψ n) = 1)
    (v : PCWorld) (hv : ∀ n, ¬ v.Holds (ψ n)) (n : ℕ) :
    (AttemptA.buyOne ψ).netWorth Q v n = -((n : ℝ) + 1) :=
  AttemptA.degenerate_summable_needed ψ Q hQ v hv n

end BuyOne

end Cleanroom.Bli.BliLinkage
