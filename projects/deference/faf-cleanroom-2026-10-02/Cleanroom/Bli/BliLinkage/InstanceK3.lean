import Cleanroom.Bli.BliLinkage.InstanceB2Point
import Cleanroom.Bli.BliLinkage.Degenerate
import LogicalInduction.Properties.AffinePersistence

/-!
# `bli-linkage` — K3 at FAF's LIA: what a fixed coordinate can and cannot do, and the
family form (repair round 1, fidelity B2)

`InstanceB2.no_degenerate_linked_bli_LIA` instantiates the abstract K3 conclusion
(`Degenerate.no_degenerate_linked_bli`, over a coordinate *family* `χ : ℕ → ℕ`) at the
**constant** family `χ := fun _ => c`. The fidelity audit (B2) observed that for a fixed
sentence FAF's `lic_limitingBelief_tendsto` makes the LIA's price converge, so its `halfRound`
cell can change infinitely often only if the limit is exactly `1/2` and the price crosses it
infinitely often — the instance's `hmove` is satisfiable, if at all, only on that boundary.
This module makes that exact, refutes `hmove` outright at the fixed grid's coordinates, and
restates the instance over a coordinate family, where a non-boundary `hmove` could live.

1. **`hmove_fixed_forces_limit_half`**: for a fixed coordinate code `c`, if the LIA's rounded
   price of `sentenceOfCode c` moves infinitely often then
   `limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (sentenceOfCode c) = 1/2`. Contrapositive of
   convergence: a limit off `1/2` puts the price on one side of `1/2` from some day on.
2. **`not_hmove_falsum` / `not_hmove_verum`**: at `⌜⊥⌝` and `⌜⊤⌝` — the coordinates of the fixed
   grid — `hmove` is **false** (the rounded prices settle at `0` and `1`,
   `InstanceB2Point.tbl01_eventually`). So the fixed-`c` instance of record, applied to the B2
   witness index, has a false hypothesis: it says nothing there. Its ledger row now says so.
3. **`no_degenerate_linked_bli_LIA_family`**: the instance over a coordinate family `χ` whose
   sentence codes are machine-metered (`hχ : MachineDigits (n ↦ ⌜sentenceOfCode (χ n)⌝)`,
   the e.c. certificate the mandate's "`MachineSentenceCodes` follows from `χ`'s" asks for),
   with `hmove` about the price of `χ n` between days `n` and `n+1`. The paired literal family
   is metered from `hχ` by FAF's `MachineDigits.comp` at the unary ruler `unpairFst`
   (`cellSentence_family_machineSentenceCodes`); everything else is as in the fixed-`c`
   instance, which is the special case `χ := fun _ => c`, `hχ := MachineDigits.const _`.
   This is the honest shape of mandate § K3's instance ("with `χ n` listed and pinned
   eventually"): for a *varying* family convergence of each coordinate's price does not by
   itself exclude `hmove`, since the day-`n` and day-`(n+1)` prices are of a different
   sentence each day — **off the fixed grid's index**. On `witnessIndex` itself `hpin ∧ hmove`
   is contradictory for every family (`family_hmove_false_on_witnessIndex`, audit r2
   adversarial B2), so the family form has content only on a grid listing a varying
   coordinate: that grid is built in `InstanceK3Grid` (`oneIndex`/`oneSystem`,
   `no_degenerate_linked_bli_LIA_oneCoord`, whose only hypotheses are `hχ` and `hmove`).
   **No inhabitant of `hmove` is shipped** (unknown in both directions: no example of a
   machine-metered family with infinitely many `halfRound` moves at the LIA is known, and
   nothing excludes one): the candidate remains bli-leak's pseudorandom family, and the OPEN
   `BliLinkageB.InstanceMoves.leakQ_rounded_price_moves` is stated over `leakQ`/`leakDP` with
   a literal family quoting `leakQ` not yet built (mandate § K3, "Quote lane for the moving
   market": T7), so it instantiates neither this theorem nor the fixed-`c` one as stated.
   The ledger and the open list say this.
4. **The package at the LIA is empty — every instance in this module is vacuous** (audit r2
   B1 raised it; repair r3 / audit r3 B1 settled it): the `E1x (liaHistory (paperDP 𝗜𝚺₁)) P`
   conjunct with `PCPσ` forces the LIA to list every small tautology at exactly `1`,
   `2^(2^n − 2)` of them on day `n`, against its polynomial day-`n` support
   (`LiaPackage.not_lia_small_coherent_mixture_exists`, `LiaSupport.liaStates_support_card_le_poly`).
   The conclusions hold with `hχ` and `hmove` dropped (`InstanceK3Local`); `hmove` is not the
   operative hypothesis. The instances are kept as the mandate's K3 shape, labelled vacuous;
   the instances with content are the local forms in `InstanceK3Local` (`E1xLit`: agreement on
   the pinned literals only), whose precondition is one listed sentence a day. The point mass
   of `InstanceB2Point` inhabits a package with base `pointMass v`, not this one.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset Filter
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (fixedCF fixedSystemR σB2 twoCells_eq_range halfRound_lt_two)

/-! ## A fixed coordinate: `hmove` forces the limit price to be exactly `1/2` -/

/-- The move set of a fixed coordinate code `c` (the `hmove` set of
`InstanceB2.no_degenerate_linked_bli_LIA`).
Source: mandate K3 (`moved n`); `InstanceB2.no_degenerate_linked_bli_LIA`
Kind: D
Fidelity: exact -/
def moveSet (c : ℕ) : Set ℕ :=
  {n | halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode c)))) ≠
    halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c))))}

/-- Off the limit `1/2`, the price is on the limit's side of `1/2` once within
`|L − 1/2|` of it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma side_of_close {x L : ℝ} (hne : L ≠ 1 / 2) (hd : |x - L| < |L - 1 / 2|) :
    x < 1 / 2 ↔ L < 1 / 2 := by
  rcases lt_or_gt_of_ne hne with hL | hL
  · rw [abs_of_neg (by linarith : L - 1 / 2 < 0)] at hd
    have := (abs_lt.1 hd).2
    exact ⟨fun _ => hL, fun _ => by linarith⟩
  · rw [abs_of_pos (by linarith : 0 < L - 1 / 2)] at hd
    have := (abs_lt.1 hd).1
    exact ⟨fun h => absurd h (by linarith), fun h => absurd h (by linarith)⟩

/-- **For a fixed coordinate, `hmove` forces the LIA's limit price to be exactly `1/2`.** The
LIA's price of a fixed sentence converges (`lic_limitingBelief_tendsto`); if the limit is off
`1/2`, from some day on the price is on the limit's side of `1/2`, the `halfRound` cell is
constant, and the move set is finite. So the fixed-`c` instance of record
(`InstanceB2.no_degenerate_linked_bli_LIA`) has content only on the boundary where the
limit is exactly `1/2` and the price crosses it infinitely often.
Source: FAF `thm:con` (`lic_limitingBelief_tendsto`); this run (audit r1 fidelity B2)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hmove_fixed_forces_limit_half (c : ℕ) (hmove : (moveSet c).Infinite) :
    limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (sentenceOfCode c) = 1 / 2 := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) := paperLIA 𝗜𝚺₁
  by_contra hne
  have hconv := lic_limitingBelief_tendsto (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁) (sentenceOfCode c)
  have hε : 0 < |limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (sentenceOfCode c) - 1 / 2| :=
    abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hconv _ hε
  have hside : ∀ n ≥ N,
      (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c))) < 1 / 2 ↔
        limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (sentenceOfCode c) < 1 / 2) := by
    intro n hn
    have hd := hN n hn
    rw [Real.dist_eq] at hd
    have h2 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    rw [← Rat.cast_lt (K := ℝ), h2, marketValue_pair_cast]
    exact side_of_close hne hd
  have hconst : ∀ n ≥ N, n ∉ moveSet c := by
    intro n hn hmem
    apply hmem
    unfold halfRound
    by_cases hL : limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (sentenceOfCode c) < 1 / 2
    · rw [if_pos ((hside (n + 1) (by omega)).2 hL), if_pos ((hside n hn).2 hL)]
    · rw [if_neg fun h => hL ((hside (n + 1) (by omega)).1 h),
        if_neg fun h => hL ((hside n hn).1 h)]
  refine hmove ((Set.finite_Iio N).subset fun n hn => ?_)
  rw [Set.mem_Iio]
  by_contra h
  exact hconst n (not_lt.1 h) hn

/-! ## At the fixed grid's coordinates `hmove` is false -/

/-- **At `⌜⊥⌝` the LIA's rounded price does not move infinitely often**: it is `0` from some
day on (`tbl01_eventually`). So `InstanceB2.no_degenerate_linked_bli_LIA` at `c := ⌜⊥⌝` — the
fixed grid's first coordinate — has a false hypothesis.
Source: this run (audit r1 fidelity B2); FAF `thm:provind`
Kind: P (refutation of the instance's hypothesis at the witness index)
Fidelity: exact
Hyps: (a) -/
theorem not_hmove_falsum : ¬ (moveSet (Encodable.encode (⊥ : Sentence))).Infinite := by
  intro hmove
  obtain ⟨N, hN⟩ := tbl01_eventually
  refine hmove ((Set.finite_Iio N).subset fun n hn => ?_)
  rw [Set.mem_Iio]
  by_contra h
  have hn' : N ≤ n := not_lt.1 h
  apply hn
  show halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode
      (sentenceOfCode (Encodable.encode (⊥ : Sentence)))))) =
    halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode
      (sentenceOfCode (Encodable.encode (⊥ : Sentence))))))
  rw [sentenceOfCode_encode]
  exact ((hN (n + 1) (by omega)).1).trans (hN n hn').1.symm

/-- **At `⌜⊤⌝` the LIA's rounded price does not move infinitely often**: it is `1` from some
day on.
Source: this run (audit r1 fidelity B2); FAF `thm:provind`
Kind: P (refutation of the instance's hypothesis at the witness index)
Fidelity: exact
Hyps: (a) -/
theorem not_hmove_verum : ¬ (moveSet (Encodable.encode (⊤ : Sentence))).Infinite := by
  intro hmove
  obtain ⟨N, hN⟩ := tbl01_eventually
  refine hmove ((Set.finite_Iio N).subset fun n hn => ?_)
  rw [Set.mem_Iio]
  by_contra h
  have hn' : N ≤ n := not_lt.1 h
  apply hn
  show halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode
      (sentenceOfCode (Encodable.encode (⊤ : Sentence)))))) =
    halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode
      (sentenceOfCode (Encodable.encode (⊤ : Sentence))))))
  rw [sentenceOfCode_encode]
  exact ((hN (n + 1) (by omega)).2).trans (hN n hn').2.symm

/-! ## The family form -/

/-- **The paired B2 literal family over a machine-metered coordinate family is
machine-metered**: `z ↦ cellSentence (z.unpair.1 + 1) (χ z.unpair.1) z.unpair.2` at `𝗜𝚺₁`,
`halfRound`, for `χ` with `MachineDigits χ`. The atom's code is a `Nat.pair`-nest of constants,
`z.unpair.1 + 1`, `χ z.unpair.1` (by `MachineDigits.comp` at the unary ruler `unpairFst`) and
`z.unpair.2`. The fixed-`c` form `BliLinkageB.cellSentence_pair_machineSentenceCodes` is the
case `χ := fun _ => c`.
Source: FAF `MachineDigits.comp`/`natPair`/`ofUnaryRuler`, `UnaryRuler.unpairFst`/`unpairSnd`; attempt B `cellSentence_pair_machineSentenceCodes`
Kind: L
Fidelity: n/a -/
theorem cellSentence_family_machineSentenceCodes (χ : ℕ → ℕ) (hχ : MachineDigits χ) :
    MachineSentenceCodes fun z =>
      cellSentence 𝗜𝚺₁ halfRound halfRound_computable (z.unpair.1 + 1) (χ z.unpair.1) z.unpair.2 := by
  have hd : MachineDigits fun z => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
        (Nat.pair (z.unpair.1 + 1) (Nat.pair (χ z.unpair.1) z.unpair.2))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            (MachineDigits.const (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code)
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.unpairFst).add (MachineDigits.const 1))
              (MachineDigits.natPair (hχ.comp UnaryRuler.unpairFst)
                (MachineDigits.ofUnaryRuler UnaryRuler.unpairSnd))))))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

/-- **K3 at FAF's LIA over `paperDP 𝗜𝚺₁`, family form.** `Q := liaHistory (paperDP 𝗜𝚺₁)`
(FAF's `paperLIA`), the B2 cell family at `halfRound` with any representatives, a coordinate
family `χ` whose sentence codes are machine-metered (`hχ`), listed and pinned from day `N`
on, the degenerate table listing `χ n` at today's rounding of the LIA's exact quote of
`sentenceOfCode (χ n)` (`hentry`): **if the LIA's rounded price of `χ n` moves between days
`n` and `n+1` infinitely often (`hmove`)**, no `P` satisfies `PCPσ ∧ E5σ ∧ E1x ∧ Degenerate` at
the B2 state sentence. Metering (`cellSentence_family_machineSentenceCodes` from `hχ`), stage
entry (`cellSentence_neg_enters`) and `hworld` (`paperDP_hworld`) are discharged; `hmove` and
`hχ` are the hypotheses not derived (the e.c. certificate of the family is the mandate's own
clause). The fixed-`c` instance is the case `χ := fun _ => c`, `hχ := MachineDigits.const _`,
where `hmove` is confined to the boundary (`hmove_fixed_forces_limit_half`) and false at the
witness index (`not_hmove_falsum`/`_verum`). On the fixed grid's index `witnessIndex` the
hypotheses `hpin ∧ hmove` are contradictory for *every* family
(`family_hmove_false_on_witnessIndex`); the grid on which a varying family is pinned is
`InstanceK3Grid.oneIndex`/`oneSystem`, and `InstanceK3Grid.no_degenerate_linked_bli_LIA_oneCoord`
is this theorem with every grid hypothesis discharged. No inhabitant of `hmove` is shipped
(module docstring). **The package is empty — the theorem is vacuous** (repair r3):
`PCPσ ∧ E1x (liaHistory …) P` is unsatisfiable (`LiaPackage.not_lia_small_coherent_mixture_exists`),
so the conclusion holds with `hχ` and `hmove` dropped
(`InstanceK3Local.no_degenerate_linked_bli_LIA_family_vacuous`); the local form
`InstanceK3Local.no_degenerate_linked_bli_LIA_family_lit` is the one with content.
Source: [[bli-program]] §3.6(iii); desiderata I2; mandate K3 ("with `χ n` listed and pinned eventually"); this run (audit r1 fidelity B2, fix (a))
Kind: C
Fidelity: exact (`hmove` and the family's e.c. certificate `hχ` the hypotheses not derived; the degenerate table's shape and the grid conditions are instance data)
Hyps: (a); `hmove` is the honest conditional of mandate § K3; `hχ` the family's certificate; **vacuous**: the package is empty at FAF's LIA (`LiaPackage.not_lia_small_coherent_mixture_exists`) -/
theorem no_degenerate_linked_bli_LIA_family (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ)
    (S : StateSystem) {atoms : ℕ → Finset ℕ} {P : History} (χ : ℕ → ℕ)
    (hχ : MachineDigits fun n => Encodable.encode (sentenceOfCode (χ n))) (deg : ℕ → ℕ) (N : ℕ)
    (hpin : ∀ n ≥ N, χ n ∈ pinned (fixedCF rep) index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hentry : ∀ n, entryOf (χ n) (tableOfCode (deg n)) =
      some (halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))))
    (hsp : ∀ n, SpuriousEntails (stateOf (fixedCF rep)) (fixedCF rep).literal S index
      (fixedCF rep).cells n)
    (hatoms : ∀ n, stateAtoms (stateOf (fixedCF rep)) S n ⊆ atoms n)
    (hmove : Set.Infinite {n |
      halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n))))) ≠
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))}) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ (stateOf (fixedCF rep)) S P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P deg) := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) := paperLIA 𝗜𝚺₁
  have hψ : MachineSentenceCodes fun z =>
      (fixedCF rep).literal (z.unpair.1 + 1) (sentenceOfCode (χ z.unpair.1)) z.unpair.2 :=
    cellSentence_family_machineSentenceCodes
      (fun n => Encodable.encode (sentenceOfCode (χ n))) hχ
  refine no_degenerate_linked_bli (fixedCF rep) deg χ
    (fun n => halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n))))))
    2 N (fun n => twoCells_eq_range (n + 1)) hpin hdegS (fun n => halfRound_lt_two _ _) hentry hsp
    hatoms hψ (paperDP_hworld 𝗜𝚺₁) ?_ hmove
  intro n hn
  obtain ⟨k, hk⟩ := cellSentence_neg_enters 𝗜𝚺₁ halfRound halfRound_computable hn
  exact ⟨k, fun v hv => (PCWorld.holds_neg v _).1 (hv _ hk)⟩

/-- The fixed-`c` instance of record is the family form at the constant family.
Source: none: infrastructure (consistency check)
Kind: L
Fidelity: n/a -/
theorem no_degenerate_linked_bli_LIA_of_family (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ)
    (S : StateSystem) {atoms : ℕ → Finset ℕ} {P : History} (c : ℕ) (deg : ℕ → ℕ) (N : ℕ)
    (hpin : ∀ n ≥ N, c ∈ pinned (fixedCF rep) index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hentry : ∀ n, entryOf c (tableOfCode (deg n)) =
      some (halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c))))))
    (hsp : ∀ n, SpuriousEntails (stateOf (fixedCF rep)) (fixedCF rep).literal S index
      (fixedCF rep).cells n)
    (hatoms : ∀ n, stateAtoms (stateOf (fixedCF rep)) S n ⊆ atoms n)
    (hmove : (moveSet c).Infinite) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ (stateOf (fixedCF rep)) S P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P deg) :=
  no_degenerate_linked_bli_LIA_family rep index S (fun _ => c) (MachineDigits.const _) deg N hpin
    hdegS hentry hsp hatoms hmove

/-! ## On the fixed grid's index the family form's `hmove` is false for every family -/

/-- **On `witnessIndex` the family form's `hpin ∧ hmove` is contradictory for every coordinate
family**: pinned on `[⌜⊥⌝, ⌜⊤⌝]` means `χ n ∈ {⌜⊥⌝, ⌜⊤⌝}` for all `n ≥ N`, both rounded prices
settle (`tbl01_eventually`), so the move set is finite. So the family form says nothing on the
only grid the package built before repair round 2; the grid that carries a varying family is
`InstanceK3Grid.oneIndex`/`oneSystem` (`no_degenerate_linked_bli_LIA_oneCoord`).
Source: this run (audit r2 adversarial B2, probe `FamilyHmoveWitnessIndex.family_hmove_false_on_witnessIndex`)
Kind: P (refutation of the family form's hypothesis package on the fixed grid's index)
Fidelity: exact (`hmove`'s set verbatim from `no_degenerate_linked_bli_LIA_family`)
Hyps: (a) -/
theorem family_hmove_false_on_witnessIndex (rep : ℕ → ℕ → ℚ) (χ : ℕ → ℕ) (N : ℕ)
    (hpin : ∀ n ≥ N, χ n ∈ pinned (fixedCF rep) witnessIndex n) :
    ¬ Set.Infinite {n |
      halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n))))) ≠
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))} := by
  intro hinf
  obtain ⟨M, hM⟩ := tbl01_eventually
  refine hinf ((Set.finite_Iio (max N M)).subset fun n hn => ?_)
  rw [Set.mem_Iio]
  by_contra h
  have hn' : max N M ≤ n := not_lt.1 h
  have hN : N ≤ n := le_of_max_le_left hn'
  have hMn : M ≤ n := le_of_max_le_right hn'
  apply hn
  have hc := ((mem_pinned _ _ _ _).1 (hpin n hN)).1
  rcases Cleanroom.Bli.BliLinkageB.mem_witnessIndex_iff.1 hc with hχ | hχ
  · show halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode
        (sentenceOfCode (χ n))))) =
      halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))
    rw [hχ, sentenceOfCode_encode]
    exact ((hM (n + 1) (by omega)).1).trans (hM n hMn).1.symm
  · show halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode
        (sentenceOfCode (χ n))))) =
      halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))
    rw [hχ, sentenceOfCode_encode]
    exact ((hM (n + 1) (by omega)).2).trans (hM n hMn).2.symm

end Cleanroom.Bli.BliLinkage
