import Cleanroom.Deference.DefArgmaxValue.Concentration
import Cleanroom.Deference.DefArgmaxValue.Witness
import Cleanroom.Deference.DefLatticeArrows.Transfer
import Cleanroom.Deference.DefSqueezeDiamond.PaperExpert

/-!
# `def-argmax-value` · Theorem: Total Trust + fold + conditional-stability ⟹ argmax Value (target 8)

[[total-trust-implies-value]] §Theorem, over FAF, in the two-process form (the expert's own
process `DPE`, in which its selection package, its follower and the composite are reflected and
over which its history is an inductor; the novice's process `DPH ⊇ DPE`, over which the novice is
an inductor and Total Trust is stated):

**(H1)** `TotalTrust P DPH E` and ramp quotes for the composite `D_n := ½(S_n − O^i_n + 1)` —
the composite itself is data (`Composite`): "the ledger prices the whole closure", the page's
**rich-ledger observability**, `(c)` for a general expert (finding: the mandate's "(a) for the
self-expert via the gap packages" is not available — those are gaps against *quotes*, not
between two LUVs; the N+ instance uses a menu on which the composites are selects of
constants, `Instance.lean`).
**(H2)** the fold at the concentration ramps, `ConcentrationFolds` (`(a)` for the self-expert).
**(H3)** `CondStableOn M pkg`, a condition on the **menu**: the liar probe satisfies every other
hypothesis of this theorem and violates H3 and the conclusion (`Refuted.lean`), so H3 is not
implied by the rest and the theorem is not a squeeze (2-025, AUDIT §3.3).

Proof (`scoped_value`): Lemma 2 (`endorse_of_concentrates`, concentration **proved inside** from
H2) gives `E*(S_n) ≳ₙ M_n ≥ m^i_n`, so `E*(D_n) ≳ₙ ½` (expert-side provind on the composite);
`expert_bound_transfer_of_totalTrust` at `v = ½` gives `E^P_n(D_n) ≳ₙ ½`; the novice's provind on
`[(1, D), (−½, S), (½, O^i), const −½]` (valued `0` within slack) unpacks to
`E^P_n(S_n) ≳ₙ E^P_n(O^i_n)`. **The slack of H2 is absorbed**: `δ, ε'` are quantified outside,
per-`ε` instances are intersected at the `liminf`, and the conclusion is the exact `≳ₙ`.

Also: `ValueOnStable` (8b, the scoped predicate — `def-lattice`'s `Value` docstring reserves the
name for this package), `valueOnStable_of_totalTrust`, `value_of_valueOnStable_of_condStable`
(vacuous, for the record), and the one-way headline `scoped_value_paperExpert` (8c): the paper
expert read by a distinct novice, with `TotalTrust`, `CondStableOn` and the composite left.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## Recasting an expert to another process -/

/-- The same expert data (history, deferral, range) viewed over another deductive process —
`def-lattice`'s `Expert DP` carries `DP` only as a phantom index.
Source: none: infrastructure (`def-squeeze-diamond`'s `paperExpert T f DPH` is the self-expert
recast)
Kind: D
Fidelity: n/a -/
def _root_.Cleanroom.Found.DefLattice.Expert.recast {DPE : DeductiveProcess} (E : Expert DPE)
    (DPH : DeductiveProcess) : Expert DPH := ⟨E.A, E.f, E.range⟩

/-- Recasting preserves estimates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem _root_.Cleanroom.Found.DefLattice.Expert.recast_estimate {DPE : DeductiveProcess}
    (E : Expert DPE) (DPH : DeductiveProcess) (X : ℕ → LUV) (n : ℕ) :
    (E.recast DPH).estimate X n = E.estimate X n := rfl

/-! ## The composite (rich-ledger observability) -/

/-- **The rescaled composite** `D_n := ½(S_n − O_n + 1)`: an e.c. LUV valued within a vanishing
slack at `(x_S − x_O + 1)/2` whenever `S_n`, `O_n` are valued `x_S`, `x_O`. The page's
"rich-ledger observability" (the ledger prices the composite the novice bets on) as data:
`(c)` for a general expert.
Source: [[total-trust-implies-value]] §Lemma 1 remarks ("rich-ledger observability is spent
exactly here"); mandate target 8a (H1)
Kind: D
Fidelity: exact (the `GapMesh` rescaling to `[0,1]`, within slack) -/
structure Composite (DP : DeductiveProcess) (S O : ℕ → LUV) where
  /-- the composite LUV -/
  D : ℕ → LUV
  /-- it is e.c. -/
  codes : LUV.MachineThresholdCodeSeq D
  /-- the reflection slack -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- `D n` is valued within `slack n` of `(x_S − x_O + 1)/2` -/
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ xS xO,
    v.ValuesAt (S n) xS → v.ValuesAt (O n) xO →
      ∃ z, v.ValuesAt (D n) z ∧ |z - (xS - xO + 1) / 2| ≤ slack n

/-- The composite is world-valued when its parts are.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Composite.valued {DP : DeductiveProcess} {S O : ℕ → LUV} (c : Composite DP S O)
    (hS : Valued DP S) (hO : Valued DP O) : Valued DP c.D := fun n v hv => by
  obtain ⟨xS, hxS⟩ := hS n v hv
  obtain ⟨xO, hxO⟩ := hO n v hv
  obtain ⟨z, hz, -⟩ := c.reflected n v hv xS xO hxS hxO
  exact ⟨z, hz⟩

/-- **Composites exist for every e.c. valued pair** — the disclosed `(c)` existence clause for a
general expert (the rich ledger).
Source: mandate target 8a
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def CompositesAvailable (DP : DeductiveProcess) : Prop :=
  ∀ S O : ℕ → LUV, LUV.MachineThresholdCodeSeq S → LUV.MachineThresholdCodeSeq O →
    Valued DP S → Valued DP O → Nonempty (Composite DP S O)

/-! ## The two provind steps on the composite -/

/-- **The expert's estimate of the composite**: `E*(D_n) ≈ₙ ½E*(S_n) − ½E*(O_n) + ½` (deferred
provind on `D − ½S + ½O − ½`, valued `0` within slack).
Source: [[total-trust-implies-value]] §Theorem ("its quote tracks `E^A_n(Ŝ_n) − m^i_n` by the
expert's `loe` with constant coefficients")
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem composite_estimate {DP : DeductiveProcess} {E : Expert DP} [IsLogicalInductor E.A DP]
    (hf : StrictlyIncreasingDeferral E.f) {S O : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S)
    (hO : LUV.MachineThresholdCodeSeq O) (hSv : Valued DP S) (hOv : Valued DP O)
    (c : Composite DP S O) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate c.D n) ≈ₙ
      (fun n => (1 / 2 : ℝ) * E.estimate S n - (1 / 2 : ℝ) * E.estimate O n + 1 / 2) := by
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [((fun _ => EF.const 1), c.D), ((fun _ => EF.const (-1 / 2)), S),
      ((fun _ => EF.const (1 / 2)), O)] with hterms
  have h := expect_deferred_asympEq_zero_of_slack (P := E.A) (DP := DP) E.f hf
    (c₀ := fun _ => EF.const (-1 / 2)) (constWeighting _) (terms := terms)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact constWeighting _)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact c.codes
      · exact hS
      · exact hO)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact c.valued hSv hOv
      · exact hSv
      · exact hOv)
    (B := 3) (by norm_num)
    (fun m => by simp [hterms, EF.denote_const]; try norm_num)
    c.slack c.slack_tendsto
    (fun n v hv ν hν => by
      obtain ⟨xS, hxS⟩ := hSv n v hv
      obtain ⟨xO, hxO⟩ := hOv n v hv
      obtain ⟨z, hz, hb⟩ := c.reflected n v hv xS xO hxS hxO
      have e1 : ν (c.D n) = z :=
        (hν ((fun _ => EF.const 1), c.D) (by simp [hterms])).eq hz
      have e2 : ν (S n) = xS :=
        (hν ((fun _ => EF.const (-1 / 2)), S) (by simp [hterms])).eq hxS
      have e3 : ν (O n) = xO :=
        (hν ((fun _ => EF.const (1 / 2)), O) (by simp [hterms])).eq hxO
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const, e1, e2, e3]
      push_cast
      have : (-1 / 2 : ℝ) + (1 * z + (-1 / 2 * xS + (1 / 2 * xO + 0))) = z - (xS - xO + 1) / 2 := by
        ring
      rw [this]
      exact hb) hworld
  have hE : deferredExpect E.A E.f (fun _ => EF.const (-1 / 2)) terms =
      fun n => E.estimate c.D n -
        ((1 / 2 : ℝ) * E.estimate S n - (1 / 2 : ℝ) * E.estimate O n + 1 / 2) := by
    funext n
    simp only [deferredExpect, hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **The novice's expectation of the composite**: `E^P_n(D_n) ≈ₙ ½E^P_n(S_n) − ½E^P_n(O_n) + ½`
(same-day provind on `[(1, D), (−½, S), (½, O)]` with constant `−½`, valued `0` within slack),
in every `DPH`-world when `DPH`-worlds are `DPE`-worlds.
Source: [[total-trust-implies-value]] §Theorem ("the novice's `loe` splits the difference")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem composite_expect {DPE DPH : DeductiveProcess}
    (hext : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory DPE)
    {P : History} [IsLogicalInductor P DPH] {S O : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S)
    (hO : LUV.MachineThresholdCodeSeq O) (hSv : Valued DPE S) (hOv : Valued DPE O)
    (c : Composite DPE S O) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (fun n => (c.D n).expect P n) ≈ₙ
      (fun n => (1 / 2 : ℝ) * (S n).expect P n - (1 / 2 : ℝ) * (O n).expect P n + 1 / 2) := by
  set ts : List (ℚ × (ℕ → LUV)) := [(1, c.D), (-1 / 2, S), (1 / 2, O)] with hts
  have h := expect_listComb_eq_of_slack (P := P) (DP := DPH) (constStream_splice (-1 / 2))
    (B := 1) (fun _ => by norm_num) (ts := ts)
    (fun p hp => by
      simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact c.codes
      · exact hS
      · exact hO)
    (listComb_worldValued _ (fun p hp => by
      simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact fun n v hv => c.valued hSv hOv n v (hext v hv)
      · exact fun n v hv => hSv n v (hext v hv)
      · exact fun n v hv => hOv n v (hext v hv)))
    0 (slack := c.slack) c.slack_tendsto
    (fun n v hv ν hν => by
      have hv' := hext v hv
      obtain ⟨xS, hxS⟩ := hSv n v hv'
      obtain ⟨xO, hxO⟩ := hOv n v hv'
      obtain ⟨z, hz, hb⟩ := c.reflected n v hv' xS xO hxS hxO
      have e1 := (listComb_valuesAt_mem hν (p := (1, c.D)) (by simp [hts])).eq hz
      have e2 := (listComb_valuesAt_mem hν (p := (-1 / 2, S)) (by simp [hts])).eq hxS
      have e3 := (listComb_valuesAt_mem hν (p := (1 / 2, O)) (by simp [hts])).eq hxO
      rw [listComb_value]
      simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e1, e2, e3]
      push_cast
      have : (-1 / 2 : ℝ) + (1 * z + (-1 / 2 * xS + (1 / 2 * xO + 0))) - 0 =
          z - (xS - xO + 1) / 2 := by ring
      rw [this]
      exact hb) hworld
  have hE : (fun n => (listComb (fun _ => (-1 / 2 : ℚ)) ts n).expect P n) =
      fun n => (c.D n).expect P n -
        ((1 / 2 : ℝ) * (S n).expect P n - (1 / 2 : ℝ) * (O n).expect P n + 1 / 2) := by
    funext n
    rw [listComb_expect]
    simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- From `E(D) ≳ₙ ½` and `E(D) ≈ₙ ½E(S) − ½E(O) + ½`, `E(S) ≳ₙ E(O)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympGE_of_composite {d s o : ℕ → ℝ} (hd : d ≳ₙ (fun _ => (1 / 2 : ℝ)))
    (he : d ≈ₙ (fun n => (1 / 2 : ℝ) * s n - (1 / 2 : ℝ) * o n + 1 / 2)) : s ≳ₙ o := by
  intro ε hε
  have h1 := hd (ε / 4) (by linarith)
  have h2 := asympEq_eventually_abs_le he (show (0 : ℝ) < ε / 4 by linarith)
  filter_upwards [h1, h2] with n hn1 hn2
  rw [abs_le] at hn2
  linarith [hn2.1, hn2.2]

/-! ## Lemma 1 on the composite: from the self-endorsement instance to Value -/

/-- **From the self-endorsement instance to argmax Value, per menu** (Lemma 1 on the composite;
the tail of the scoped theorem, factored out in repair round 1): if the expert's estimate of the
follower is `≳ₙ` its maximal quote, then under Total Trust with ramp quotes on the composite
`½(S − O^i + 1)`, the novice has `E^P_n(S_n) ≳ₙ E^P_n(O^i_n)`. Proof: `E*(D) ≳ₙ ½`
(`composite_estimate`), `expert_bound_transfer_of_totalTrust` at `v = ½`, `composite_expect`.
Nothing here mentions the selection package, the fold or H3: those are what *produce* `hSE`
(Lemma 2, `scoped_value`), or an eventually-constant selection (`Decisive.lean`).
Source: [[total-trust-implies-value]] §Theorem (Lemma 1 applied to the composite)
Kind: C
Fidelity: exact
Hyps: (a) the two provind steps, bounds transfer; `hf`, `hext`; (c) `hTT` (deference), `hramp`,
`comp`; `hSE` is the instance (derived in `scoped_value`) -/
theorem value_of_selfEndorse_instance {DPE DPH : DeductiveProcess}
    (hext : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory DPE)
    {E : Expert DPE} [IsLogicalInductor E.A DPE] (hf : StrictlyIncreasingDeferral E.f)
    {P : History} [IsLogicalInductor P DPH] {k : ℕ} {M : Menu k} (hM : M.Valued DPE)
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hSv : Valued DPE S)
    (hSE : (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n))
    (i : Fin (k + 1)) (comp : Composite DPE S (M.O i))
    (hTT : TotalTrust P DPH (E.recast DPH))
    (hramp : RampQuotesAvailable DPH (E.recast DPH) comp.D)
    (hworldE : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPE.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n) := by
  -- the expert's estimate of the composite is ≳ₙ ½
  have hD := composite_estimate hf hS (M.codes i) hSv (hM i) comp hworldE
  have hA : (fun n => (E.recast DPH).estimate comp.D n) ≳ₙ (fun _ => (((1 / 2 : ℚ)) : ℝ)) := by
    simp only [Expert.recast_estimate]
    have h1 : (fun n => (1 / 2 : ℝ) * E.estimate S n - (1 / 2 : ℝ) * E.estimate (M.O i) n + 1 / 2) ≳ₙ
        (fun _ => (((1 / 2 : ℚ)) : ℝ)) := by
      intro ε hε
      filter_upwards [hSE (2 * ε) (by linarith)] with n hn
      have := M.quote_le_maxQuote E i n
      push_cast
      simp only [Menu.quote] at this
      linarith
    exact asympGE_iff.2 ((asympGE_iff.1 h1).trans_asympEq hD.symm)
  -- Lemma 1: transfer
  have hH := expert_bound_transfer_of_totalTrust hTT comp.codes hramp hA hworldH
  -- the novice unpacks
  have hN := composite_expect (P := P) hext hS (M.codes i) hSv (hM i) comp hworldH
  push_cast at hH
  exact asympGE_of_composite hH hN

/-! ## The scoped theorem -/

/-- **Total Trust + fold + conditional-stability ⟹ argmax Value, per menu** (target 8a,
load-bearing 5). Two processes: the expert `E` is an inductor over its own `DPE`, in which its
selection package, the follower and the composite are reflected; the novice `P` is an inductor
over `DPH` whose worlds are `DPE`-worlds (`hext`), and Total Trust is stated over `DPH` for
`E.recast DPH`. Hypotheses: **(H1)** `TotalTrust` and ramp quotes on the composite; **(H2)**
`ConcentrationFolds` — the fold at the pairwise ramps, `(a)` for the self-expert; **(H3)**
`CondStableOn M pkg`, a condition on the menu. Concentration is **proved inside**
(`concentrates_of_folds`), Lemma 2 is `endorse_of_concentrates`, Lemma 1 is
`expert_bound_transfer_of_totalTrust` at `v = ½` on the composite. H3 is not implied by the
rest: the liar probe satisfies (H1) (`selfTotalTrust`), (H2) (`concentrationFolds_self`) and the
package, violates H3 by `−s(1−s)` and violates the conclusion (`Refuted.lean`). The slack of H2
is absorbed: `δ, ε'` are quantified outside and the conclusion is the exact `≳ₙ`.
Source: [[total-trust-implies-value]] §Theorem; lean-deference-069; vq-wiki-014; 2-025
Kind: C
Fidelity: exact (H2 as FAF's fold with its slack; the composite as data)
Hyps: (a) Lemma 2, concentration, the two provind steps; `hf`; (c) `hTT` is the deference
hypothesis, `hramp` (ramp quotes on the composite — (a) for the paper expert,
`paperExpert_rampQuotesAvailable`), `comp` (the rich ledger prices the composite), `hfold` ((a)
for the self-expert); H3 `h3` is the scope condition -/
theorem scoped_value {DPE DPH : DeductiveProcess}
    (hext : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory DPE)
    {E : Expert DPE} [IsLogicalInductor E.A DPE] (hf : StrictlyIncreasingDeferral E.f)
    {P : History} [IsLogicalInductor P DPH] {k : ℕ} {M : Menu k} (hM : M.Valued DPE)
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DPE E M I Q)
    (hfold : ConcentrationFolds DPE E M I) (h3 : CondStableOn M pkg)
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DPE E M S)
    (i : Fin (k + 1)) (comp : Composite DPE S (M.O i))
    (hTT : TotalTrust P DPH (E.recast DPH))
    (hramp : RampQuotesAvailable DPH (E.recast DPH) comp.D)
    (hworldE : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPE.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n) := by
  have hSv : Valued DPE S := follows_valued hM hfol
  -- Lemma 2: E*(S) ≳ₙ M_n
  have hL2 := endorse_of_concentrates hf hM pkg h3 (concentrates_of_folds hf pkg hfold hworldE)
    hS hfol hworldE
  -- Lemma 1 on the composite
  exact value_of_selfEndorse_instance hext hf hM hS hSv hL2 i comp hTT hramp hworldE hworldH

/-! ## The predicate (8b) -/

/-- **Scoped Value** — `def-lattice`'s `Value` with its menu quantifier restricted to
conditionally-stable menus (through any selection package): for every valued menu, every
selection package on which `CondStableOn` holds, every e.c. follower and every `i`,
`E^H_n(S_n) ≳ₙ E^H_n(O^i_n)`. The predicate the `Value` docstring reserves for this package.
Source: [[total-trust-implies-value]] §Theorem; `def-lattice` `Value` ("the scoped predicate is
`def-argmax-value`'s"); mandate target 8b
Kind: D
Fidelity: exact -/
def ValueOnStable (P : History) (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (k : ℕ) (M : Menu k), M.Valued DP → ∀ (I Q : Fin (k + 1) → ℕ → LUV)
    (pkg : SelectionPackage DP E M I Q), CondStableOn M pkg →
    ∀ S : ℕ → LUV, LUV.MachineThresholdCodeSeq S → Follows DP E M S →
      ∀ i, (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n)

/-- An expert recast to its own process is itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem _root_.Cleanroom.Found.DefLattice.Expert.recast_self {DP : DeductiveProcess}
    (E : Expert DP) : E.recast DP = E := rfl

/-- **Scoped Value from Total Trust** (predicate level, 8b), single process: an inductor-expert
with the fold on every menu *through its selection packages*, composites and ramp quotes
available (on e.c. valued LUVs), and Total Trust, has `ValueOnStable`. The availability clauses
are quantified exactly as `ValueOnStable`'s quantifier needs them (repair round 1, audit r1 B2 /
fidelity item 1: the draft asked for the fold on *every* indicator family and ramp quotes on
every e.c. `D`, which the self-expert cannot supply); the self-expert discharges `hfold`
(`concentrationFolds_self`), `hramp` (`paperExpert_rampQuotesAvailable`) and `hTT`
(`selfTotalTrust`) — `Instance.lean` `valueOnStable_self`, with `CompositesAvailable` the one
hypothesis left.
Source: mandate target 8b
Kind: L
Fidelity: exact
Hyps: (c) `hcomp` (the rich ledger), `hramp`, `hfold` (existence clauses; (a) for the self-expert
except the composites); `hTT` the deference hypothesis; `hf` -/
theorem valueOnStable_of_totalTrust {DP : DeductiveProcess} {E : Expert DP}
    [IsLogicalInductor E.A DP] (hf : StrictlyIncreasingDeferral E.f) {P : History}
    [IsLogicalInductor P DP] (hTT : TotalTrust P DP E) (hcomp : CompositesAvailable DP)
    (hramp : ∀ D : ℕ → LUV, LUV.MachineThresholdCodeSeq D → Valued DP D →
      RampQuotesAvailable DP E D)
    (hfold : ∀ (k : ℕ) (M : Menu k) (I Q : Fin (k + 1) → ℕ → LUV),
      SelectionPackage DP E M I Q → ConcentrationFolds DP E M I)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : ValueOnStable P DP E := by
  intro k M hM I Q pkg h3 S hS hfol i
  have hSv : Valued DP S := follows_valued hM hfol
  obtain ⟨comp⟩ := hcomp S (M.O i) hS (M.codes i) hSv (hM i)
  exact scoped_value (fun _ hv => hv) hf hM pkg (hfold k M I Q pkg) h3 hS hfol i comp hTT
    (hramp comp.D comp.codes (comp.valued hSv (hM i))) hworld hworld

/-- **If the global `CondStable` held, `Value` would follow from `ValueOnStable`** — vacuous for
inductor-experts (`CondStable` is refuted, `Refuted.lean`); recorded so the ledger can say the
scoped predicate is `Value` with its quantifier restricted.
Source: mandate target 8b
Kind: L
Fidelity: exact
Hyps: (c) `hpkg` (packages exist); `hcs` is false for the self-expert -/
theorem value_of_valueOnStable_of_condStable {DP : DeductiveProcess} {E : Expert DP}
    {P : History} (hV : ValueOnStable P DP E) (hcs : CondStable DP E)
    (hpkg : SelectionPackagesAvailable DP E) : Value P DP E := by
  intro k M hM S hS hfol i
  obtain ⟨I, Q, ⟨pkg⟩⟩ := hpkg k M hM
  exact hV k M hM I Q pkg (hcs k M hM I Q pkg) S hS hfol i

/-! ## 8c — the paper expert read by a distinct novice (the one-way headline) -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The scoped theorem for the paper expert read by a distinct novice** (target 8c, one-way):
over any `DPH` extending `paperDP T` and any inductor `P` over `DPH`, with the self-expert's own
selection package (`selectionPackage_self`) and fold (`concentrationFolds_self`, both (a)), the
hypotheses left are **Total Trust** `TotalTrust P DPH (paperExpert T f DPH)`, the scope condition
`CondStableOn`, and the composite (rich ledger). Ramp quotes on the composite are
`paperExpert_rampQuotesAvailable` (a). Witness for the non-deference hypotheses: the ledger
novice of li-quote-lane; the `TotalTrust` antecedent's only known inhabitant is `P = A` — N− (diag),
as the squeeze ledger records.
Source: mandate target 8c; `def-squeeze-diamond` target 4
Kind: C
Fidelity: exact
Hyps: (a) the package, the fold, the ramp quotes, Lemma 2 and the provind steps; `hf`, `hext`;
`hTT` the deference hypothesis; `comp` (c) the rich ledger; `h3` the scope condition -/
theorem scoped_value_paperExpert (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {DPH : DeductiveProcess} (hext : ExtendsBase T DPH) {P : History} [IsLogicalInductor P DPH]
    {k : ℕ} (M : Menu k) (hM : M.Valued (paperDP T))
    (h3 : CondStableOn M (selectionPackage_self T f M)) {S : ℕ → LUV}
    (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows (paperDP T) (selfExpert T f) M S)
    (i : Fin (k + 1)) (comp : Composite (paperDP T) S (M.O i))
    (hTT : TotalTrust P DPH (paperExpert T f DPH))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n) :=
  scoped_value (DPE := paperDP T) (DPH := DPH) hext hf hM (selectionPackage_self T f M)
    (concentrationFolds_self T f hf M (selectionPackage_self T f M)) h3 hS hfol i comp hTT
    (paperExpert_rampQuotesAvailable T f hext hf.injective comp.codes
      (comp.valued (follows_valued hM hfol) (hM i)))
    (paperDP_hworld T) hworldH

end

end Cleanroom.Deference.DefArgmaxValue
