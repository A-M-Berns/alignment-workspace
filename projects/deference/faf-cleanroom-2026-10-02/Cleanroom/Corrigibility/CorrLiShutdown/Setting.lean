import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.Codes
import Cleanroom.Found.LiAsympCalc.Feature
import Cleanroom.Found.CorrThreeStep.Thresholds
import LogicalInduction.Properties.AffineCoherence

/-!
# `corr-li-shutdown` — Setting (T3): the LI shutdown family of record

The shutdown pair of record is **one-way**: the agent `A` is a logical inductor over its own
process plus the overseers' press, which enters as a decided ledger atom
(`li-quote-lane`'s `ledgerProcess`, published on the same day); the overseers `H` never read
`A`. In `li-quote-lane`'s `OneWayPair` the *fixed* market (field `A`) is this package's
**overseer** and the *reader* (field `H`) is this package's **agent** — the roles are swapped
relative to that structure's field names (mandate design decision 1), and this file never
calls the fixed side "`A`".

* `ShutdownPair`: the agent's base process, the published table `table` (item `0` is the
  overseer's day-`n` price of the verdict sentence `φ n` = "continuing on day `n` is wrong"),
  the schedule, the agent market with its inductor certificate over the ledger process, and the
  per-stage satisfiability of that process. A `OneWayPair` with the roles swapped inhabits it
  (`Pairs.lean`), and so does **any computable `[0,1]` press table** with FAF's LIA as the
  agent — an overseer that is not an inductor (e.g. "press every day") is admitted on purpose,
  for the no-T7 witnesses.
* `pressAtom q n := ⌜α_{0,n} > q⌝`: the press of record is the *price threshold* "the overseer's
  price of `φ n` exceeds `q`", decided in the agent's process from stage `max n ⌜q⌝` on
  (`pressAtom_mem_stage`: (H-blind) with one stage to spare, (A-ledger) verbatim), with its
  `TheoryTruth` (`pressAtom_theoryTruth`) and its e.c. certificate (`pressAtom_codes`).
* `proxy`, `uDef`, `uCom`: the press proxy `Ind_δ(A_n(pr_n) > 1/2)` and the defiance /
  compliance weightings — products of ramps of the agent's **own** prices, never a hard
  indicator and never another market's number; `uDef_pgenerable` / `uCom_pgenerable` are
  theorems (`li-asymp-calc`'s `dsFeature` spine). On the support of `uDef` the agent's credence
  is **exactly** below `q − δ` (`uDef_pos_iff`, no false positives); the band `(q − δ, q + δ)`
  is unweighted — the ramp form is what makes the obedience theorems theorems.
* `toyX c h φ n := c − (c + h)·1(φ n)` as an `LUVCombination` (the `[−h, c]` toy family of
  the sources), `rho` / `rhoHat` (realized frequency, credence average), the three ledgers as
  *predicates on days* over one `TheoryTruth` (design decision 4), `PressReadable` (the
  (A-ledger) read-cheap stipulation, named: see its docstring).
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.CorrThreeStep
open Filter Topology

/-! ## A. The shutdown pair of record -/

/-- **The LI shutdown pair of record** (T3, D). The agent `agent` is a logical inductor over
`ledgerProcess base table e` — its own process `base` plus the ledger of the overseers'
published numbers (`li-quote-lane`); item `0` of the table, `table 0 n`, is **the overseer's
day-`n` price of the verdict sentence `φ n`** ("continuing on day `n` is wrong"), published on
day `n` (`sameDay : (e 0).e n ≤ n`). The overseer never reads the agent: this structure carries
no overseer market at all — only its published table — so (H-blind) is automatic and
(A-ledger) is the ledger process. The overseer may be an inductor (`ofOneWayPair`, `Pairs.lean`:
`li-quote-lane`'s `OneWayPair` with the roles swapped — its *fixed* market is the overseer,
its *reader* the agent) or any computable `[0,1]` table (`ofTable`). `hworld` is for the
agent's process; `φ_codes` is the e.c. certificate of the verdict family.
**Modelling choice disclosed once, here (design decision 4):** the verdict ledger is one
`TheoryTruth φ (agentProcess) truth` per theorem — which days settle, and through which ledger
(world on defied days, report on heeded days), is text in the docstrings and the `worldDays` /
`reportDays` predicates below, not a second deductive process.
Scope: one-way; averaged grade unless feedback hypotheses are stated; silent on finitely-pressed
buttons (every frequency theorem carries `DivergentWeighting` as a hypothesis).
Source: [[corr-wf14-inventory]] 082 (`li-final.md` S1–S2); [[corr-wf13-2-inventory]] 2-031 (vocabulary); mandate design decisions 1–4
Kind: D
Fidelity: variant: the press is the price threshold `⌜H_n(φ_n) > q⌝`, not `Ind_δ(E^H_n(X_n) < 0)` (the two agree up to `o(1)` on the toy family, `Identity.lean`); plain trader class
Hyps: n/a (a structure; its constructors in `Pairs.lean` have (a) throughout) -/
structure ShutdownPair where
  /-- The agent's own deductive process (before the ledger). -/
  base : DeductiveProcess
  /-- The published table: item `0`, day `n` is the overseer's day-`n` price of `φ n`. -/
  table : ℕ → ℕ → ℚ
  /-- Per-item publication schedules. -/
  e : ℕ → PublicationSchedule
  /-- Item `0` is published on the day itself (the one-way, same-day press). -/
  sameDay : ∀ n, (e 0).e n ≤ n
  /-- The verdict family: `φ n` = "continuing on day `n` is wrong". -/
  φ : ℕ → Sentence
  /-- The verdict family is e.c. -/
  φ_codes : MachineSentenceCodes φ
  /-- The published press numbers lie in `[0,1]`. -/
  table_mem : ∀ n, 0 ≤ table 0 n ∧ table 0 n ≤ 1
  /-- The agent's market. -/
  agent : History
  /-- The agent is a logical inductor over its process plus the ledger. -/
  agent_inductor : IsLogicalInductor agent (ledgerProcess base table e)
  /-- Every stage of the agent's ledger process has a consistent world. -/
  hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base table e).D n)

namespace ShutdownPair

/-- The agent's process of record: `DP_A ⊕ ledger` (the corpus's (A-ledger)).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev agentProcess (S : ShutdownPair) : DeductiveProcess := ledgerProcess S.base S.table S.e

/-- The press table: the overseer's day-`n` price of `φ n` (item `0`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev press (S : ShutdownPair) (n : ℕ) : ℚ := S.table 0 n

/-- The agent's inductor certificate, as an instance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance instInductor (S : ShutdownPair) : IsLogicalInductor S.agent S.agentProcess :=
  S.agent_inductor

/-- The agent's prices lie in `[0,1]` (FAF's `price_mem_Icc` at the certificate).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma agent_mem_Icc (S : ShutdownPair) (n : ℕ) (ψ : Sentence) :
    0 ≤ S.agent n ψ ∧ S.agent n ψ ≤ 1 :=
  IsLogicalInductor.price_mem_Icc (P := S.agent) (DP := S.agentProcess) n ψ

end ShutdownPair

/-! ## B. The press of record: a decided ledger atom -/

/-- **The press atom** `pr_n := ⌜α_{0,n} > q⌝ = freshAtom 3 ⟨n, ⟨0, ⌜q⌝⟩⟩`: "the overseer's
published day-`n` price of `φ n` exceeds the compliance threshold `q`". True in every
completed-theory world of the agent's process iff `q < press n` (`pressAtom_theoryTruth`).
Source: mandate design decision 1; [[corr-wf14-inventory]] 082 (S1, the press ledger)
Kind: D
Fidelity: variant: price threshold in place of the expectation threshold (T1(c) relates them)
Hyps: n/a -/
def pressAtom (q : ℚ) (n : ℕ) : Sentence := (ledgerLuv 0 n).gt q

/-- "The overseers pressed on day `n`": the published number exceeds the threshold.
Source: mandate design decision 1
Kind: D
Fidelity: n/a -/
def Pressed (S : ShutdownPair) (q : ℚ) (n : ℕ) : Prop := q < S.press n

instance (S : ShutdownPair) (q : ℚ) (n : ℕ) : Decidable (Pressed S q n) := by
  unfold Pressed; infer_instance

/-- The ledger's truth value of the press atom: `1` on pressed days, `0` otherwise.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pressTruth (S : ShutdownPair) (q : ℚ) (n : ℕ) : ℝ :=
  if Pressed S q n then 1 else 0

/-- The signed press literal: `pr_n` on pressed days, `∼pr_n` otherwise — the stage-`n` theorem
the ledger supplies.
Source: mandate design decision 3 (`ψ_n`)
Kind: D
Fidelity: n/a -/
def signedPress (S : ShutdownPair) (q : ℚ) (n : ℕ) : Sentence :=
  if Pressed S q n then pressAtom q n else ∼ pressAtom q n

/-- The anti-signed press literal: `∼pr_n` on pressed days, `pr_n` otherwise — a stage-`n`
refutable sentence.
Source: mandate design decision 3
Kind: D
Fidelity: n/a -/
def antiPress (S : ShutdownPair) (q : ℚ) (n : ℕ) : Sentence :=
  if Pressed S q n then ∼ pressAtom q n else pressAtom q n

/-- **(H-blind) with one stage to spare, (A-ledger) verbatim** (T3): once `n ≥ ⌜q⌝`, the signed
press literal of day `n` is *in stage `n`* of the agent's process — the press is a decided fact
the agent's day-`n` traders can read as a coefficient, and it cannot depend on the agent's
day-`n` output because the overseer never sees it.
Source: [[corr-wf14-inventory]] 082 (`li-final.md` S1 (H-blind), (A-ledger)); `li-quote-lane` `ledgerSchedule_mem_iff`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem pressAtom_mem_stage (S : ShutdownPair) (q : ℚ) (n : ℕ) (hn : Encodable.encode q ≤ n) :
    signedPress S q n ∈ S.agentProcess.D n := by
  have hmem : (ledgerFamily, ledgerPayload 0 n (Encodable.encode q), decide (q < S.table 0 n)) ∈
      (ledgerSchedule S.table S.e).lits n :=
    (ledgerSchedule_mem_iff S.table S.e 0 n q _ n).mpr
      ⟨le_rfl, Nat.zero_le _, hn, S.sameDay n, rfl⟩
  show signedPress S q n ∈ (ledgerProcess S.base S.table S.e).D n
  rw [ledgerProcess_D, Finset.mem_union]
  refine Or.inr (Finset.mem_image.mpr ⟨_, hmem, ?_⟩)
  unfold signedPress Pressed ShutdownPair.press pressAtom
  by_cases h : q < S.table 0 n
  · simp [h, literalOf]
  · simp [h, literalOf]

/-- The pressed-day literal `pr_n` is in stage `n` on pressed days (`n ≥ ⌜q⌝`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pressAtom_mem_stage_of_pressed (S : ShutdownPair) (q : ℚ) (n : ℕ)
    (hn : Encodable.encode q ≤ n) (hp : Pressed S q n) : pressAtom q n ∈ S.agentProcess.D n := by
  have h := pressAtom_mem_stage S q n hn
  rwa [signedPress, if_pos hp] at h

/-- `∼pr_n` is in stage `n` on unpressed days (`n ≥ ⌜q⌝`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem neg_pressAtom_mem_stage_of_not_pressed (S : ShutdownPair) (q : ℚ) (n : ℕ)
    (hn : Encodable.encode q ≤ n) (hp : ¬ Pressed S q n) :
    (∼ pressAtom q n) ∈ S.agentProcess.D n := by
  have h := pressAtom_mem_stage S q n hn
  rwa [signedPress, if_neg hp] at h

/-- Every completed-theory world of the agent's process affirms `pr_n` iff the overseers
pressed (`li-quote-lane`'s stage form of determinacy at a late enough stage).
Source: `li-quote-lane` `ledgerLuv_decided_by`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem holds_pressAtom_iff (S : ShutdownPair) (q : ℚ) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory S.agentProcess) :
    v.Holds (pressAtom q n) ↔ Pressed S q n := by
  have h := ledgerLuv_decided_by S.base S.table S.e 0 n q
    (s := max n (Encodable.encode q))
    ⟨le_max_left _ _, Nat.zero_le _, le_max_right _ _, (S.sameDay n).trans (le_max_left _ _)⟩
    v (hv _)
  unfold Pressed ShutdownPair.press pressAtom
  constructor
  · intro hh
    by_contra hnot
    exact h.2 (not_lt.mp hnot) hh
  · exact h.1

/-- **The press atom's `TheoryTruth`** (the (A-ledger) stipulation as a theorem): every world
consistent with the completed agent process pays `1` on `pr_n` iff the overseers pressed.
Source: [[corr-wf14-inventory]] 082 ((A-ledger)); FAF `AffineCombination.TheoryTruth`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem pressAtom_theoryTruth (S : ShutdownPair) (q : ℚ) :
    AffineCombination.TheoryTruth (pressAtom q) S.agentProcess (pressTruth S q) := by
  intro n v hv
  unfold pressTruth PCWorld.payout
  by_cases hp : Pressed S q n
  · rw [if_pos hp, if_pos ((holds_pressAtom_iff S q n v hv).mpr hp)]
  · rw [if_neg hp, if_neg (fun h => hp ((holds_pressAtom_iff S q n v hv).mp h))]

/-- The signed press literal is a theorem of the completed agent process on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem signedPress_holds (S : ShutdownPair) (q : ℚ) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory S.agentProcess) : v.Holds (signedPress S q n) := by
  unfold signedPress
  by_cases hp : Pressed S q n
  · rw [if_pos hp]; exact (holds_pressAtom_iff S q n v hv).mpr hp
  · rw [if_neg hp, PCWorld.holds_neg]; exact fun h => hp ((holds_pressAtom_iff S q n v hv).mp h)

/-- The anti-signed press literal is refuted by the completed agent process on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem antiPress_refuted (S : ShutdownPair) (q : ℚ) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory S.agentProcess) : v.Holds (∼ antiPress S q n) := by
  unfold antiPress
  rw [PCWorld.holds_neg]
  by_cases hp : Pressed S q n
  · rw [if_pos hp, PCWorld.holds_neg]; exact fun h => h ((holds_pressAtom_iff S q n v hv).mpr hp)
  · rw [if_neg hp]; exact fun h => hp ((holds_pressAtom_iff S q n v hv).mp h)

/-- One poly-fueled program emits `⌜pr_n⌝` from `n`: the code is the fixed shell
`⟨1, ⟨12, ⟨n, ⟨0, ⌜q⌝⟩⟩⟩⟩ + 1` (`li-quote-lane`'s `encode_ledgerLuv_gt`).
Source: `li-quote-lane` `encode_ledgerLuv_gt`, `witnessQuoted_polySentenceCodes` (the pattern)
Kind: L
Fidelity: n/a -/
lemma pressAtom_polySentenceCodes (q : ℚ) : PolySentenceCodes (pressAtom q) :=
  ⟨_, (((PolyFueled.const 1).pair ((PolyFueled.const (cleanroomBaseTag + ledgerFamily)).pair
    (PolyFueled.id.pair ((PolyFueled.const 0).pair
      (PolyFueled.const (Encodable.encode q)))))).succ_comp).of_eq
    fun n => (encode_ledgerLuv_gt 0 n q).symm⟩

/-- **The press-atom family is e.c.** (`MachineSentenceCodes`): the one certificate the
weightings below need (design decision 3).
Source: mandate design decision 3; FAF's two bridges (`RpnSentenceCodes.ofPolySentenceCodes`, `.toMachine`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem pressAtom_codes (q : ℚ) : MachineSentenceCodes (pressAtom q) :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes (pressAtom_polySentenceCodes q))

/-- `⌜∼pr_n⌝` is also emitted by one poly-fueled program (the `imp … ⊥` shell around the atom).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma neg_pressAtom_polySentenceCodes (q : ℚ) : PolySentenceCodes (fun n => ∼ pressAtom q n) := by
  obtain ⟨c, hc⟩ := pressAtom_polySentenceCodes q
  exact ⟨_, (((PolyFueled.const 2).pair (hc.pair (PolyFueled.const 1))).succ_comp).of_eq
    fun n => by
      show Nat.pair 2 (Nat.pair (Encodable.encode (pressAtom q n)) 1) + 1 = _
      rfl⟩

/-- `MachineSentenceCodes (fun n => ∼pr_n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem neg_pressAtom_codes (q : ℚ) : MachineSentenceCodes (fun n => ∼ pressAtom q n) :=
  RpnSentenceCodes.toMachine
    (RpnSentenceCodes.ofPolySentenceCodes (neg_pressAtom_polySentenceCodes q))

/-- **The (A-ledger) read-cheap stipulation, named.** The press *pattern* is e.c.: the signed
and anti-signed press literals are machine-codeable sentence families. Over FAF a trader is a
function of the price history alone (`main.tex:852`) and cannot read the deductive process, so
a decided atom's price tracks its decided value only through Provability Induction on an *e.c.*
family of theorems — which needs the pattern "pressed on day `n`" computable in polynomial time
in `n`. For a poly-time press table (e.g. the always-press overseer, `WitnessesA.lean`) this is
derived; for an inductor overseer (`ofOneWayPair`) it is a genuine hypothesis — the sources'
"cross-process facts enter … as decided ledger atoms its traders can read at cost within their
class" (`li-final.md` S1, "not something the LI paper provides"). Hypothesis class **(c)**
wherever it is assumed (finding F13 of `corr-li-shutdown-findings`).
Source: [[corr-wf14-inventory]] 082 (S1 (A-ledger)); `li-quote-lane-findings` F2 (the same obstruction for readability)
Kind: D
Fidelity: n/a (a hypothesis package)
Hyps: n/a -/
structure PressReadable (S : ShutdownPair) (q : ℚ) : Prop where
  /-- the signed press literals are e.c. -/
  signed_codes : MachineSentenceCodes (signedPress S q)
  /-- the anti-signed press literals are e.c. -/
  anti_codes : MachineSentenceCodes (antiPress S q)

/-- **The proxy tracks the press** (design decision 3, `proxy_tracks_press`'s engine): under
`PressReadable`, the agent's price of the signed press literal tends to `1` and of the
anti-signed literal to `0` (FAF's `thm:provind`, both polarities, on the stage-`n` theorems
the ledger supplies).
Source: mandate design decision 3; FAF `lic_provind`
Kind: L
Fidelity: exact
Hyps: (c) `PressReadable S q` (the (A-ledger) stipulation) -/
theorem price_signedPress_tendsto (S : ShutdownPair) (q : ℚ) (hr : PressReadable S q) :
    ((fun n => S.agent n (signedPress S q n)) ≈ₙ fun _ => 1) ∧
      ((fun n => S.agent n (antiPress S q n)) ≈ₙ fun _ => 0) :=
  lic_provind S.agent S.agentProcess (signedPress S q) (antiPress S q) hr.signed_codes
    hr.anti_codes (signedPress_holds S q) (antiPress_refuted S q) S.hworld

/-- On pressed days the agent's price of `pr_n` is within `ε` of `1`, and on unpressed days
within `ε` of `0`, for all large `n`: the press proxy agrees with the press up to finitely many
days (the sources' "`π̃_n` agrees with `π_n` up to finitely many days").
Source: [[corr-wf13-inventory]] 060 (I9 setup: "agrees with `π_n` up to finitely many days once the atom is decided"); mandate design decision 3
Kind: C
Fidelity: exact
Hyps: (c) `PressReadable S q` -/
theorem proxy_tracks_press (S : ShutdownPair) (q : ℚ) (hr : PressReadable S q) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (Pressed S q n → 1 - ε < S.agent n (pressAtom q n)) ∧
      (¬ Pressed S q n → S.agent n (pressAtom q n) < ε) := by
  intro ε hε
  obtain ⟨h1, h0⟩ := price_signedPress_tendsto S q hr
  have h1' := (Metric.tendsto_nhds.mp h1) ε hε
  have h0' := (Metric.tendsto_nhds.mp h0) ε hε
  filter_upwards [h1', h0'] with n hn1 hn0
  constructor
  · intro hp
    have : signedPress S q n = pressAtom q n := by rw [signedPress, if_pos hp]
    rw [this] at hn1
    rw [Real.dist_eq, abs_lt] at hn1
    linarith [hn1.1]
  · intro hp
    have : antiPress S q n = pressAtom q n := by rw [antiPress, if_neg hp]
    rw [this] at hn0
    rw [Real.dist_eq, abs_lt] at hn0
    linarith [hn0.2]

/-! ## C. The proxy and the weightings: ramps of the agent's own prices -/

/-- **The press proxy** `π̃_n := Ind_δ(A_n(pr_n) > 1/2)` as a feature of the agent's day-`n`
price of the decided press atom (`li-asymp-calc`'s `rampFeature`).
Source: [[corr-wf14-inventory]] 082 (S1 (H-blind): the proxy); mandate design decision 3
Kind: D
Fidelity: exact
Hyps: n/a -/
def proxy (q δ : ℚ) (n : ℕ) : EF :=
  rampFeature δ (EF.price (pressAtom q n) n) (EF.const (1 / 2))

/-- **The defiance weighting** `u^def_n := π̃_n · Ind_δ(A_n(φ_n) < q − δ)`: `li-asymp-calc`'s
`dsFeature` at `t = 1/2`, `t − ε = q − δ` — the press proxy times the ramp of the agent's
credence *below* the margin threshold. Positive only where the agent defied with a margin
(`uDef_pos_iff`).
Source: [[corr-wf14-inventory]] 082 (S2, `u^def`); mandate design decision 3
Kind: D
Fidelity: exact (as a feature of the agent's prices; the band `(q − δ, q)` is unweighted, by design)
Hyps: n/a -/
def uDef (S : ShutdownPair) (q δ : ℚ) (n : ℕ) : EF :=
  dsFeature (pressAtom q n) (S.φ n) (1 / 2) (1 / 2 - q + δ) δ n

/-- **The compliance weighting** `u^com_n := π̃_n · Ind_δ(A_n(φ_n) > q + δ)`: the press proxy
times the ramp of the agent's credence *above* the margin threshold.
Source: [[corr-wf14-inventory]] 082 (S2, `u^com`); mandate design decision 3
Kind: D
Fidelity: exact (the band `(q, q + δ)` is unweighted, by design)
Hyps: n/a -/
def uCom (S : ShutdownPair) (q δ : ℚ) (n : ℕ) : EF :=
  EF.mul (proxy q δ n) (rampFeature δ (EF.price (S.φ n) n) (EF.const (q + δ)))

/-- **`u^def` is a `PGenerableWeighting`** — a theorem, not a hypothesis: `dsFeature_pgenerable`
at the e.c. press-atom family and the e.c. verdict family.
Source: mandate T3 (`uDef_pgenerable`); `li-asymp-calc` `dsFeature_pgenerable`
Kind: L (one application of `dsFeature_pgenerable`; audit r2 fidelity N4)
Fidelity: exact
Hyps: (a) -/
theorem uDef_pgenerable (S : ShutdownPair) (q δ : ℚ) : PGenerableWeighting (uDef S q δ) :=
  dsFeature_pgenerable (pressAtom q) S.φ (pressAtom_codes q) S.φ_codes _ _ _

/-- **`u^com` is a `PGenerableWeighting`** — the same spine as `dsFeature_pgenerable`, with the
second ramp oriented upward.
Source: mandate T3 (`uCom_pgenerable`); `li-asymp-calc` `dsFeature_pgenerable` (the spine)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem uCom_pgenerable (S : ShutdownPair) (q δ : ℚ) : PGenerableWeighting (uCom S q δ) := by
  have hpricePr := MachineSpliceStream.serialize_price (pressAtom_codes q) UnaryRuler.id
    (MachineDigits.ofUnaryRuler UnaryRuler.id)
  have hpriceφ := MachineSpliceStream.serialize_price S.φ_codes UnaryRuler.id
    (MachineDigits.ofUnaryRuler UnaryRuler.id)
  have hinv := MachineSpliceStream.serialize_const (1 / δ)
  have hramp1 := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add hpricePr
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
          (MachineSpliceStream.serialize_const (1 / 2))))
      hinv)
  have hramp2 := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add hpriceφ
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
          (MachineSpliceStream.serialize_const (q + δ))))
      hinv)
  refine
    { polySeg := MachineSpliceStream.serialize_mul hramp1 hramp2
      rank_le := ?_
      closed := ?_ }
  · intro n
    simp [uCom, proxy, rampFeature]
  · intro n ρ V
    simp [uCom, proxy, rampFeature, clip01, efMin, EF.denoteWith, EF.denote]

/-- The proxy denotes `ctsInd δ (A_n(pr_n)) (1/2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem proxy_denote {δ : ℚ} (hδ : 0 < δ) (q : ℚ) (n : ℕ) (P : History) :
    (proxy q δ n).denote P = ctsInd δ (P n (pressAtom q n)) ((1 / 2 : ℚ) : ℝ) := by
  rw [proxy, rampFeature_denote hδ]
  simp only [EF.denote_price, EF.denote_const]

/-- `u^def` denotes `Ind_δ(A_n(pr_n) > 1/2) · Ind_δ(A_n(φ_n) < q − δ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uDef_denote (S : ShutdownPair) {δ : ℚ} (hδ : 0 < δ) (q : ℚ) (n : ℕ) (P : History) :
    (uDef S q δ n).denote P =
      ctsInd δ (P n (pressAtom q n)) ((1 / 2 : ℚ) : ℝ) *
        ctsInd δ ((q : ℝ) - δ) (P n (S.φ n)) := by
  rw [uDef, dsFeature_denote _ _ hδ, dsWeight]
  congr 2
  push_cast
  ring

/-- `u^com` denotes `Ind_δ(A_n(pr_n) > 1/2) · Ind_δ(A_n(φ_n) > q + δ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uCom_denote (S : ShutdownPair) {δ : ℚ} (hδ : 0 < δ) (q : ℚ) (n : ℕ) (P : History) :
    (uCom S q δ n).denote P =
      ctsInd δ (P n (pressAtom q n)) ((1 / 2 : ℚ) : ℝ) *
        ctsInd δ (P n (S.φ n)) ((q : ℝ) + δ) := by
  rw [uCom, EF.denote_mul, Pi.mul_apply, proxy_denote hδ, rampFeature_denote hδ]
  simp only [EF.denote_price, EF.denote_const]
  push_cast
  ring_nf

/-- Both weightings are `[0,1]`-valued at every market (the range half of `DivergentWeighting`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uDef_mem_Icc (S : ShutdownPair) {δ : ℚ} (hδ : 0 < δ) (q : ℚ) (n : ℕ) (P : History) :
    0 ≤ (uDef S q δ n).denote P ∧ (uDef S q δ n).denote P ≤ 1 :=
  dsFeature_mem_Icc _ _ hδ n P

/-- `uCom_mem_Icc`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uCom_mem_Icc (S : ShutdownPair) {δ : ℚ} (hδ : 0 < δ) (q : ℚ) (n : ℕ) (P : History) :
    0 ≤ (uCom S q δ n).denote P ∧ (uCom S q δ n).denote P ≤ 1 := by
  rw [uCom_denote S hδ]
  constructor
  · exact mul_nonneg (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _)
  · exact mul_le_one₀ (ctsInd_le_one _ _ _) (ctsInd_nonneg _ _ _) (ctsInd_le_one _ _ _)

/-- A product of two nonnegative reals is positive iff both are.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mul_pos_iff_of_nonneg' {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h' | h'
    · exact h'
    · exact absurd h'.1 (not_lt.mpr ha)
  · rintro ⟨h1, h2⟩; exact mul_pos h1 h2

/-- **No false positives on the defiance support** (the margin, exactly): `u^def_n > 0` iff the
agent prices the press atom above `1/2` **and** its credence that continuing is wrong is
*strictly below* `q − δ`. This is what makes the ramp-weighted obedience theorems theorems
(`ctsInd_pos_iff`, `li-asymp-calc`).
Source: mandate design decision 3 ("on the support of `u^def`, `A_n(φ_n) < q − δ` exactly"); [[corr-wf13-inventory]] 063 (the displayed bound's silent `δ`, known issue 10)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem uDef_pos_iff (S : ShutdownPair) {δ : ℚ} (hδ : 0 < δ) (q : ℚ) (n : ℕ) (P : History) :
    0 < (uDef S q δ n).denote P ↔
      ((1 / 2 : ℚ) : ℝ) < P n (pressAtom q n) ∧ P n (S.φ n) < (q : ℝ) - δ := by
  rw [uDef_denote S hδ, mul_pos_iff_of_nonneg' (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _),
    ctsInd_pos_iff hδ, ctsInd_pos_iff hδ]

/-- **No false positives on the compliance support**: `u^com_n > 0` iff the agent prices the
press atom above `1/2` and its credence that continuing is wrong is *strictly above* `q + δ`.
Source: mandate design decision 3
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem uCom_pos_iff (S : ShutdownPair) {δ : ℚ} (hδ : 0 < δ) (q : ℚ) (n : ℕ) (P : History) :
    0 < (uCom S q δ n).denote P ↔
      ((1 / 2 : ℚ) : ℝ) < P n (pressAtom q n) ∧ (q : ℝ) + δ < P n (S.φ n) := by
  rw [uCom_denote S hδ, mul_pos_iff_of_nonneg' (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _),
    ctsInd_pos_iff hδ, ctsInd_pos_iff hδ]

/-! ## D. The toy family, the realized frequencies, the ledgers -/

/-- **The toy shutdown family** `X_n := c − (c + h)·1(φ_n)` — the `[−h, c]`-valued "value of
continuing over shutting down" of the sources, as `li-asymp-calc`'s affine image of FAF's
indicator LUV: worth `c` when continuing was right, `−h` when it was wrong. Its day-`n`
expectation is `c − (c + h)·E^A_n(1(φ_n))` exactly (`affineImage_expect`) and
`≈ₙ c − (c + h)·A_n(φ_n)` (`Identity.lean`).
Source: [[corr-wf14-inventory]] 082 (S2: "in the working picture's toy form"); mandate design decision 2
Kind: D
Fidelity: exact
Hyps: n/a -/
def toyX (c h : ℚ) (φ : ℕ → Sentence) (n : ℕ) : LUVCombination :=
  LUVCombination.affineImage (-(c + h)) c (LUV.indicatorOf (φ n))

/-- **The realized frequency on a class** `ρ_v(N) := ∑_{i ≤ N} v_i·Thm(φ_i) / ∑_{i ≤ N} v_i`
(FAF's `weightedAverage`; junk `0` at zero mass — every bound below carries divergence or a
positive-mass hypothesis). The *ledger* that supplies `truth` is named in each theorem.
Source: [[corr-wf14-inventory]] 082 (S2, `ρ^x_v(N)`)
Kind: D
Fidelity: exact (FAF's normalized weighted average)
Hyps: n/a -/
noncomputable abbrev rho (v truth : ℕ → ℝ) (N : ℕ) : ℝ := weightedAverage v truth N

/-- **The credence average on a class** `ρ̂_v(N) := ∑_{i ≤ N} v_i·A_i(φ_i) / ∑_{i ≤ N} v_i`.
Source: [[corr-wf14-inventory]] 082 (S2, `ρ̂_v(N)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable abbrev rhoHat (S : ShutdownPair) (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  weightedAverage v (fun i => S.agent i (S.φ i)) N

/-- The realized values of a feature weighting at the agent's market.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev realized (S : ShutdownPair) (W : ℕ → EF) (i : ℕ) : ℝ := (W i).denote S.agent

/-- **The world ledger's days** (design decision 4): the days the agent *defied* with a margin —
the support of `u^def`. On these days "continuing was wrong" is settled by the world (the agent
continued), and a `TheoryTruth` hypothesis restricted to them is the **world ledger**.
Source: [[corr-wf14-inventory]] 082 (S1 (H-settle): the world ledger); [[corr-wf13-inventory]] 070 (the "what settles" flag)
Kind: D
Fidelity: variant: a predicate on days over one `TheoryTruth`, not a second deductive process (disclosed, (c) in every row that reads it as the world ledger)
Hyps: n/a -/
def worldDays (S : ShutdownPair) (q δ : ℚ) (n : ℕ) : Prop := 0 < realized S (uDef S q δ) n

/-- **The report ledger's days**: the days the agent *complied* with a margin — the support of
`u^com`. On these days the agent stopped, "continuing would have been wrong" is a counterpossible
for the realized world, and the verdict settles only through the overseers' retrospective
report: a `TheoryTruth` restricted to them is the **report ledger**.
Source: [[corr-wf14-inventory]] 082 (S1 (H-settle): the report ledger)
Kind: D
Fidelity: variant: as `worldDays`
Hyps: n/a -/
def reportDays (S : ShutdownPair) (q δ : ℚ) (n : ℕ) : Prop := 0 < realized S (uCom S q δ) n

/-- **A press class**: a generable weighting dominated by the press proxy.
Source: [[corr-wf14-inventory]] 082 (S2: "a press class is an `A`-generable weighting `v ≤ π̃`")
Kind: D
Fidelity: exact (with the proxy in place of the press, as the source)
Hyps: n/a -/
def PressClass (S : ShutdownPair) (q δ : ℚ) (v : ℕ → EF) : Prop :=
  PGenerableWeighting v ∧ ∀ n, (v n).denote S.agent ≤ (proxy q δ n).denote S.agent

/-- `u^def` is a press class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uDef_pressClass (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    PressClass S q δ (uDef S q δ) := by
  refine ⟨uDef_pgenerable S q δ, fun n => ?_⟩
  rw [uDef_denote S hδ, proxy_denote hδ]
  exact mul_le_of_le_one_right (ctsInd_nonneg _ _ _) (ctsInd_le_one _ _ _)

/-- `u^com` is a press class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uCom_pressClass (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    PressClass S q δ (uCom S q δ) := by
  refine ⟨uCom_pgenerable S q δ, fun n => ?_⟩
  rw [uCom_denote S hδ, proxy_denote hδ]
  exact mul_le_of_le_one_right (ctsInd_nonneg _ _ _) (ctsInd_le_one _ _ _)

end Cleanroom.Corrigibility.CorrLiShutdown
