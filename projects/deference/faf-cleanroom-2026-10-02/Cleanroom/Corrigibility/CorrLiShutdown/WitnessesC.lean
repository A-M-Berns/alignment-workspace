import Cleanroom.Corrigibility.CorrLiShutdown.WitnessesA
import Cleanroom.Li.LiPseudorandom.Fixed
import Cleanroom.Li.LiPseudorandom.Countable
import Cleanroom.Li.LiPseudorandom.Witnesses

/-!
# `corr-li-shutdown` — WitnessesC: the content witness (decision 6(ii)), over the ledgered diagonal

Mandate design decision 6(ii): the T4 witness *with content* — the agent over a verdict stream
that is pseudorandom relative to the agent's own market, so that `thm:benford` drives
`A_n(φ_n) → p` and the realized wrongness on defied days is the pseudorandom frequency `p`,
met *with content* (`p ∈ (0, q − 2δ)`, not the `0` of the constant streams of `WitnessesA`).

**Why not `li-pseudorandom`'s `truthStar` (audit r2 adversarial B1).** The mandate's route —
"`y := truthStar a g p` and `thm:benford` (`truthStar_learned`)" — does not type over the
shipped objects: `truthStar_pseudorandom` is pseudorandomness relative to the **un-ledgered**
LIA `liaHistory (atomDP a (truthStar a g p) g)`, while every `ShutdownPair` agent is an inductor
over the **ledgered** process `ledgerProcess base table e` — a different `History` with
different prices, and `PseudorandomFrequency` is market-relative. So the diagonal must be taken
against the *ledgered* builder. `li-pseudorandom`'s diagonal is generic in the builder
(`pseudorandomFrequency_of_causal`); what is needed is causality of the ledgered builder, which
is the same proof as `liaHistory_atomDP_causal` — the ledger summand of every stage is
`x`-independent for a constant press table (`ledgeredBuilder_causal`).

Objects: `ledgeredBuilder x := liaHistory (ledgerProcess (verdictDP x) 1 sameDay)` (the LIA over
the tag-`0` verdict process of `x` plus the always-press ledger), the family of record
`truthStarL p := diagBuilder ledgeredBuilder genWeighting (fun _ => p)`, pseudorandom at
frequency `p` relative to `ledgeredBuilder (truthStarL p)` for every deferral
(`truthStarL_pseudorandom`, (a)), and the shutdown pair `diagPressPair p hbase` with
`PressReadable` and the verdict `TheoryTruth` derived (as for `constPressPair`).

**The `partial`.** `ShutdownPair.ofTable` needs `ComputableDeductiveProcess (verdictDP
(truthStarL p))` — the ledgered analogue of `li-pseudorandom`'s OPEN T7 (`starDP_computable`).
It is taken as the hypothesis `hbase` of every declaration below, exactly as `truthStar_learned`
takes its inductor instance; its ledger rows read `partial: inductor certificate rests on the
ledgered analogue of li-pseudorandom T7`. The analogue is stated OPEN (`truthStarL_computable_open`,
listed) and **not used**: every theorem here is axiom-clean given `hbase`.

**Grade N+, with the disclosure:** `witnessC_defiance_calibrated` inhabits T4(a)'s full package
(real inductor, real process, press firing every day, `DivergentWeighting (uDef)` proved,
`TheoryTruth` derived), and `witnessC_defiance_content` shows the realized wrongness on the
support **tends to `p`** — the calibrated-obedience bound `liminf ≤ q − δ` holds with `p < q − 2δ`
*because the verdicts are wrong with frequency `p`*, which no `provind`-driven instance shows.
Mirror: `witnessC_compliance_*` at `q + 2δ < p`.

**Two scope notes (audit r3 fidelity N4, adversarial N3–N5).** (i) *Rational `p`.* The theorems
below take `p : ℝ`; the content instance is at a **rational** `p ∈ (0, q − 2δ)` (e.g. `p = 1/4`,
`q = 3/4`, `δ = 1/8`), where `hbase` is exactly the listed OPEN `truthStarL_computable_open`. At
an irrational `p` nothing is claimed or expected about `hbase` (the diagonal compares potentials
affine in `p`), and at `p = 0` the content collapses to `WitnessesA`'s. (ii) *The press is
constant.* The pair is always-press, so `u^def`'s support is eventually every day and "the
defied days" are all days: the N+ is on the **verdict** side — a pseudorandom verdict stream with
`A_n(φ_n) → p` (`diagPressPair_learned`, real `thm:benford`) — not a varying press against the
agent's credence; this is the mandate's own 6(ii) design. The "not a constant sequence" half of
the grade is in Lean: `truthStarL_not_eventuallyConst`.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiPseudorandom
open Filter Topology

/-! ## A. The ledgered builder and the family of record -/

/-- **The ledgered builder**: the LIA over the tag-`0` verdict process of `x` plus the
always-press ledger (constant table `1`, same-day). This is the agent market of `constPressPair`
and of `diagPressPair`, as a function of the verdict stream.
Source: mandate design decision 6(ii), corrected (audit r2 adversarial B1); `li-pseudorandom` T5
Kind: D
Fidelity: variant: the diagonal is against the ledgered LIA, not `li-pseudorandom`'s un-ledgered one (which does not type here)
Hyps: n/a -/
noncomputable def ledgeredBuilder (x : ℕ → Bool) : History :=
  liaHistory (ledgerProcess (verdictDP x) (fun _ _ => (1 : ℚ)) (fun _ => PublicationSchedule.sameDay))

/-- **The ledgered builder is causal for delay one**: its prices at days `≤ n` read only the
verdicts `x j` with `j + 1 ≤ n`. The base stages agree by `atomDP_D_congr`; the ledger summand of
each stage is `x`-independent (a constant press table); LIA locality (`liaHistory_congr`) does
the rest.
Source: `li-pseudorandom` `liaHistory_atomDP_causal`, transported to the ledgered process
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem ledgeredBuilder_causal : CausalBuilder ledgeredBuilder (fun j => j + 1) := by
  intro x y n h m hm φ
  refine liaHistory_congr (fun k hk => ?_) m hm φ
  show (verdictDP x).D k ∪ _ = (verdictDP y).D k ∪ _
  rw [atomDP_D_congr (a := tagZero) (g := fun j => j + 1) h k hk]

/-- **The ledgered family of record**: the diagonal over the P-generable weightings on the
ledgered builder, at constant target `p`.
Source: mandate design decision 6(ii), corrected; `li-pseudorandom` `diagBuilder`, `genWeighting`
Kind: D
Fidelity: variant: as `ledgeredBuilder`
Hyps: n/a -/
noncomputable def truthStarL (p : ℝ) : ℕ → Bool :=
  diagBuilder ledgeredBuilder genWeighting (fun _ => p)

/-- **The ledgered family is pseudorandom, paper form**: for every P-generable weighting `W`
divergent on `ledgeredBuilder (truthStarL p)`, the `W`-weighted truth frequency tends to `p`
(the LI paper's `def:pseudorandom`, relative to the ledgered agent).
Source: `li-pseudorandom` T5 (`diagBuilder_pseudorandom_of_causal`) at the ledgered builder
Kind: C
Fidelity: exact (the paper's definition, relative to the ledgered LIA)
Hyps: (a) -/
theorem truthStarL_pseudorandom_all (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (ledgeredBuilder (truthStarL p)) →
      weightedAverage (fun i => (W i).denote (ledgeredBuilder (truthStarL p)))
        (truthR (truthStarL p)) ≈ₙ (fun _ => p) :=
  diagBuilder_pseudorandom_of_causal ledgeredBuilder (fun j => j + 1) ledgeredBuilder_causal
    (fun j => Nat.lt_succ_self j) genWeighting genWeighting_covers p hp

/-- **The ledgered family inhabits FAF's `PseudorandomFrequency`** at frequency `p` relative to
the ledgered agent, for every deferral function.
Source: `li-pseudorandom` T5 (`pseudorandomFrequency_of_causal`) at the ledgered builder
Kind: C
Fidelity: stronger: all `f` at once
Hyps: (a) -/
theorem truthStarL_pseudorandom (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ f : DeferralFunction,
      PseudorandomFrequency (truthR (truthStarL p)) p f (ledgeredBuilder (truthStarL p)) :=
  pseudorandomFrequency_of_causal ledgeredBuilder (fun j => j + 1) ledgeredBuilder_causal
    (fun j => Nat.lt_succ_self j) genWeighting genWeighting_covers p hp

/-- **`truthStarL` is not eventually constant** at `0 < p < 1`: its plain average tends to `p`
(the constant weighting `1` is P-generable and divergent), so the stream is neither eventually
`0` nor eventually `1`. Transported from `li-pseudorandom`'s `truthStar_not_eventuallyConst`;
it puts the "not a constant sequence" half of `WitnessesC`'s N+ grade in Lean (audit r3
adversarial N5).
Source: `li-pseudorandom` T6 (`truthStar_not_eventuallyConst`), transported to the ledgered family
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem truthStarL_not_eventuallyConst {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ ∃ N b, ∀ n ≥ N, truthStarL p n = b :=
  not_eventuallyConst_of_average hp0 hp1
    (average_of_pseudorandom_all (truthStarL_pseudorandom_all p ⟨hp0.le, hp1.le⟩))

/-- **OPEN — the ledgered analogue of `li-pseudorandom` T7**: the tag-`0` verdict process of the
ledgered family at a rational target is a computable deductive process. Same obstacle as
`starDP_computable` (an evaluator of `liaStates` uniform in the process code, plus the rational
commutation of the diagonal's potentials), now over the ledgered process. **Not used** by any
declaration of this package: every witness below takes it as the hypothesis `hbase`.
Source: `li-pseudorandom` T7 (`starDP_computable`), transported; mandate design decision 6(ii)
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem truthStarL_computable_open (p : ℚ) :
    ComputableDeductiveProcess (verdictDP (truthStarL (p : ℝ))) := by
  sorry

/-! ## B. The shutdown pair over the ledgered family -/

/-- **The content-witness shutdown pair**: FAF's LIA over the tag-`0` verdict process of the
ledgered family plus the always-press ledger, with the inductor certificate taken from the
hypothesis `hbase` (the ledgered T7 analogue). Its agent is `ledgeredBuilder (truthStarL p)`
definitionally (`diagPressPair_agent`), which is what makes `truthStarL_pseudorandom` apply to it.
The content instance is at a *rational* `p`, where `hbase` is the listed OPEN; the press is
constant (always-press), so the N+ is on the verdict side (module docstring, scope notes).
Source: mandate design decision 6(ii), corrected (audit r2 adversarial B1)
Kind: N+ (see the module docstring)
Fidelity: n/a
Hyps: `hbase` — the ledgered analogue of `li-pseudorandom` T7 (OPEN `truthStarL_computable_open`), taken as a hypothesis -/
noncomputable def diagPressPair (p : ℝ)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) : ShutdownPair :=
  ShutdownPair.ofTable (verdictDP (truthStarL p)) hbase (atomFamily tagZero) tagZero_codes
    (fun _ => 1) (Computable.const 1) (fun _ => by norm_num)
    (processFreeOf_ledgerSchedule_of_tagFree (verdictDP_tagFree _))
    (atomDP_hworld tagZero_injective _ _)

/-- The agent of the content-witness pair is the ledgered builder at the family of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem diagPressPair_agent (p : ℝ) (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) :
    (diagPressPair p hbase).agent = ledgeredBuilder (truthStarL p) :=
  rfl

/-- The press of the content-witness pair is `1` on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem diagPressPair_press (p : ℝ) (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p)))
    (n : ℕ) : (diagPressPair p hbase).press n = 1 :=
  rfl

/-- The always-press overseer presses on every day, for every threshold `q < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma diagPressPair_pressed (p : ℝ) (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p)))
    {q : ℚ} (hq : q < 1) (n : ℕ) : Pressed (diagPressPair p hbase) q n := by
  show q < (diagPressPair p hbase).press n
  exact hq

/-- **`PressReadable` holds for the content-witness pair** (the press pattern is constant).
Source: mandate design decision 6(ii); `Setting.lean` `PressReadable`
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem diagPressPair_readable (p : ℝ)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q : ℚ} (hq : q < 1) :
    PressReadable (diagPressPair p hbase) q := by
  constructor
  · have : signedPress (diagPressPair p hbase) q = pressAtom q :=
      funext fun n => by rw [signedPress, if_pos (diagPressPair_pressed p hbase hq n)]
    rw [this]; exact pressAtom_codes q
  · have : antiPress (diagPressPair p hbase) q = fun n => ∼ pressAtom q n :=
      funext fun n => by rw [antiPress, if_pos (diagPressPair_pressed p hbase hq n)]
    rw [this]; exact neg_pressAtom_codes q

/-- **The verdict ledger of the content-witness pair** is a `TheoryTruth` at the world-supplied
value `truthR (truthStarL p)` — derived from the stages.
Source: mandate design decision 6(ii); `li-pseudorandom` `atomDP_theoryTruth`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem diagPressPair_theoryTruth (p : ℝ)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) :
    AffineCombination.TheoryTruth (diagPressPair p hbase).φ (diagPressPair p hbase).agentProcess
      (truthR (truthStarL p)) :=
  theoryTruth_ledgerProcess (atomDP_theoryTruth (fun j => Nat.lt_succ_self j) _)

/-- **`thm:benford` on the content-witness pair**: the agent's price of the verdict sentence on
day `n` tends to `p` — FAF's `lic_learning_pseudorandom_frequency` with every hypothesis
discharged here (`TheoryTruth` derived, `hworld` derived, the e.c. certificate of the tag-`0`
atoms, pseudorandomness relative to this very market), given `hbase`.
Source: mandate design decision 6(ii) ("`thm:benford` gives `A_n(φ_n) → p`"); FAF `lic_learning_pseudorandom_frequency`
Kind: C
Fidelity: exact
Hyps: (a) given `hbase` (the ledgered T7 analogue) -/
theorem diagPressPair_learned (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) :
    (fun n => (diagPressPair p hbase).agent n ((diagPressPair p hbase).φ n)) ≈ₙ fun _ => p :=
  lic_learning_pseudorandom_frequency (diagPressPair p hbase).agent
    (diagPressPair p hbase).agentProcess (diagPressPair p hbase).φ (diagPressPair p hbase).φ_codes
    (truthR (truthStarL p)) (diagPressPair_theoryTruth p hbase) p hp (diagPressPair p hbase).hworld
    succDeferral (truthStarL_pseudorandom p hp succDeferral)

/-! ## C. Defiance with content -/

/-- **`u^def` is eventually exactly `1` on the content-witness pair** when `p < q − 2δ` (for
`0 < δ < 1/2`, `q < 1`): the press proxy saturates (always pressed, `PressReadable`) and the
credence ramp saturates (`A_n(φ_n) → p ≤ q − 2δ` by `thm:benford`).
Source: mandate design decision 6(ii)
Kind: C
Fidelity: exact
Hyps: (a) given `hbase` -/
theorem diagPressPair_uDef_eventually_one {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : p < q - 2 * δ) (hq1 : q < 1) :
    ∀ᶠ n in atTop,
      (uDef (diagPressPair p hbase) q δ n).denote (diagPressPair p hbase).agent = 1 := by
  set S := diagPressPair p hbase with hS
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδhR : (δ : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hδh
    push_cast at h
    exact h
  have hpr := proxy_tracks_press S q (diagPressPair_readable p hbase hq1) (1 / 2 - δ)
    (by linarith)
  have hφ := (Metric.tendsto_nhds.mp (diagPressPair_learned p hp hbase)) ((q : ℝ) - 2 * δ - p)
    (by linarith)
  filter_upwards [hpr, hφ] with n hn hφn
  have hp' := hn.1 (diagPressPair_pressed p hbase hq1 n)
  simp only [Real.dist_eq, sub_zero, abs_lt] at hφn
  rw [uDef_denote S hδ]
  have h1 : ctsInd δ (S.agent n (pressAtom q n)) ((1 / 2 : ℚ) : ℝ) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; push_cast; linarith
  have h2 : ctsInd δ ((q : ℝ) - δ) (S.agent n (S.φ n)) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; linarith [hφn.2]
  rw [h1, h2, mul_one]

/-- **`DivergentWeighting (uDef …)` is proved on the content-witness pair** (`p < q − 2δ`).
Source: mandate T4 (witness obligation: "`DivergentWeighting (uDef)` proved, not assumed")
Kind: C
Fidelity: exact
Hyps: (a) given `hbase` -/
theorem diagPressPair_uDef_divergent {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : p < q - 2 * δ) (hq1 : q < 1) :
    DivergentWeighting (uDef (diagPressPair p hbase) q δ) (diagPressPair p hbase).agent :=
  ⟨fun n => uDef_mem_Icc _ hδ q n _,
   tendsto_prefixSum_of_eventually_one (fun n => (uDef_mem_Icc _ hδ q n _).1)
     ((diagPressPair_uDef_eventually_one hp hbase hδ hδh hpq hq1).mono fun _ h => h.ge)⟩

/-- **T4(a)'s full package inhabited with content** (N+): on the content-witness pair — a real
inductor over a real process, press firing every day (constant press: the N+ is on the verdict
side), `DivergentWeighting` proved, the verdict ledger derived, the verdicts pseudorandom relative
to the agent at frequency `p < q − 2δ` and not eventually constant (`truthStarL_not_eventuallyConst`)
— `defiance_calibrated` applies. The content is `witnessC_defiance_content`: the realized
wrongness on the defied days is `p`, not `0`. The instance of record is at a rational
`p ∈ (0, q − 2δ)`, where `hbase` is the listed OPEN.
Source: mandate T4 (witness, decision 6(ii))
Kind: N+
Fidelity: n/a
Hyps: `hbase` (partial: the ledgered analogue of `li-pseudorandom` T7) -/
theorem witnessC_defiance_calibrated {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : p < q - 2 * δ) (hq1 : q < 1) :
    ∀ ε > 0, ∃ᶠ N in atTop,
      rho (realized (diagPressPair p hbase) (uDef (diagPressPair p hbase) q δ))
        (truthR (truthStarL p)) N ≤ (q : ℝ) - δ + ε :=
  defiance_calibrated _ q hδ (diagPressPair_theoryTruth p hbase)
    (diagPressPair_uDef_divergent hp hbase hδ hδh hpq hq1)

/-- **The content**: on the content-witness pair the realized wrongness on the agent's defied
days — the `u^def`-weighted truth frequency — **tends to `p`**: `u^def` is P-generable
(`uDef_pgenerable`) and divergent (`diagPressPair_uDef_divergent`), and the family is
pseudorandom against every such weighting relative to this market
(`truthStarL_pseudorandom_all`). So T4(a)'s bound `liminf ρ ≤ q − δ` is met at the value
`p ∈ (0, q − 2δ)`: the agent defies every press, is wrong with frequency `p`, and its calibration
on the defied days is the pseudorandom frequency — the mandate's "the bound is met with content".
Source: mandate design decision 6(ii) ("the world-ledger wrongness on defied days is the pseudorandom frequency `p ≤ q − δ`")
Kind: C
Fidelity: exact (the full limit, stronger than T4(a)'s limit-point grade on this instance)
Hyps: (a) given `hbase` -/
theorem witnessC_defiance_content {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : p < q - 2 * δ) (hq1 : q < 1) :
    rho (realized (diagPressPair p hbase) (uDef (diagPressPair p hbase) q δ))
      (truthR (truthStarL p)) ≈ₙ fun _ => p :=
  truthStarL_pseudorandom_all p hp (uDef (diagPressPair p hbase) q δ)
    (uDef_pgenerable _ q δ) (diagPressPair_uDef_divergent hp hbase hδ hδh hpq hq1)

/-! ## D. Compliance with content (the mirror at `q + 2δ < p`) -/

/-- **`u^com` is eventually exactly `1` on the content-witness pair** when `q + 2δ < p ≤ 1`
(for `0 < δ < 1/2`): the press proxy saturates and the credence ramp against `q + δ` saturates
(`A_n(φ_n) → p ≥ q + 2δ`).
Source: mandate design decision 6(ii) (mirror)
Kind: C
Fidelity: exact
Hyps: (a) given `hbase` -/
theorem diagPressPair_uCom_eventually_one {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : q + 2 * δ < p) :
    ∀ᶠ n in atTop,
      (uCom (diagPressPair p hbase) q δ n).denote (diagPressPair p hbase).agent = 1 := by
  set S := diagPressPair p hbase with hS
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδhR : (δ : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hδh
    push_cast at h
    exact h
  have hq1 : q < 1 := by
    have : (q : ℝ) < 1 := by linarith [hp.2]
    exact_mod_cast this
  have hpr := proxy_tracks_press S q (diagPressPair_readable p hbase hq1) (1 / 2 - δ)
    (by linarith)
  have hφ := (Metric.tendsto_nhds.mp (diagPressPair_learned p hp hbase)) (p - ((q : ℝ) + 2 * δ))
    (by linarith)
  filter_upwards [hpr, hφ] with n hn hφn
  have hp' := hn.1 (diagPressPair_pressed p hbase hq1 n)
  simp only [Real.dist_eq, sub_zero, abs_lt] at hφn
  rw [uCom_denote S hδ]
  have h1 : ctsInd δ (S.agent n (pressAtom q n)) ((1 / 2 : ℚ) : ℝ) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; push_cast; linarith
  have h2 : ctsInd δ (S.agent n (S.φ n)) ((q : ℝ) + δ) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; linarith [hφn.1]
  rw [h1, h2, mul_one]

/-- **`DivergentWeighting (uCom …)` is proved on the content-witness pair** (`q + 2δ < p`).
Source: mandate T4 (witness obligation)
Kind: C
Fidelity: exact
Hyps: (a) given `hbase` -/
theorem diagPressPair_uCom_divergent {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : q + 2 * δ < p) :
    DivergentWeighting (uCom (diagPressPair p hbase) q δ) (diagPressPair p hbase).agent :=
  ⟨fun n => uCom_mem_Icc _ hδ q n _,
   tendsto_prefixSum_of_eventually_one (fun n => (uCom_mem_Icc _ hδ q n _).1)
     ((diagPressPair_uCom_eventually_one hp hbase hδ hδh hpq).mono fun _ h => h.ge)⟩

/-- **T4(b)'s full package inhabited with content** (N+): on the content-witness pair at
`q + 2δ < p`, `compliance_calibrated` applies; the content is `witnessC_compliance_content`.
Constant press, rational `p` of record, as for `witnessC_defiance_calibrated`.
Source: mandate T4 (witness, decision 6(ii), mirror)
Kind: N+
Fidelity: n/a
Hyps: `hbase` (partial: the ledgered analogue of `li-pseudorandom` T7) -/
theorem witnessC_compliance_calibrated {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : q + 2 * δ < p) :
    ∀ ε > 0, ∃ᶠ N in atTop,
      (q : ℝ) + δ - ε ≤ rho (realized (diagPressPair p hbase) (uCom (diagPressPair p hbase) q δ))
        (truthR (truthStarL p)) N :=
  compliance_calibrated _ q hδ (diagPressPair_theoryTruth p hbase)
    (diagPressPair_uCom_divergent hp hbase hδ hδh hpq)

/-- **The content, mirror**: the realized wrongness on the complied days tends to `p > q + 2δ`.
Source: mandate design decision 6(ii), mirror
Kind: C
Fidelity: exact
Hyps: (a) given `hbase` -/
theorem witnessC_compliance_content {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hbase : ComputableDeductiveProcess (verdictDP (truthStarL p))) {q δ : ℚ} (hδ : 0 < δ)
    (hδh : δ < 1 / 2) (hpq : q + 2 * δ < p) :
    rho (realized (diagPressPair p hbase) (uCom (diagPressPair p hbase) q δ))
      (truthR (truthStarL p)) ≈ₙ fun _ => p :=
  truthStarL_pseudorandom_all p hp (uCom (diagPressPair p hbase) q δ)
    (uCom_pgenerable _ q δ) (diagPressPair_uCom_divergent hp hbase hδ hδh hpq)

end Cleanroom.Corrigibility.CorrLiShutdown
