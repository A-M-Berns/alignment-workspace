import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpLocalOpt.Sia

/-!
# `dp-referents-cdt`: the referent family, the `cf` slot and the structural hypotheses

Definitions of record for the package `dp-referents-cdt` (mandate §3). Everything is stated over
`dp-core-tree`'s trees, `dp-calibration`'s states and `dp-local-opt`'s `siaSum`; no object is
re-defined here.

**Parameters** (the `dp-calibration` discipline): `obs : ι → Finset Ω`, `actEv : (d : ι) → acts d
→ Finset Ω`, states `s : ι → State Ω K`, a procedure `C`, a tree `B`, a point `d`. Every referent
is a function `acts d → K`; the ones defined by a quotient (`refR1State`, `refR2Real`,
`refR2RealObs`, `refR3`) return Lean's `x / 0 = 0` at a null denominator, a junk value that every
theorem guards explicitly (mandate §7 trap 4).

**The referent family** (`faithful.md` Definition F2; mandate §3.2):
* `refR1Prior C B d a := V_B(C[d ↦ a])` — the prior-weighted all-instance deviation;
* `refR1State obs C B d a := 𝔼_{C[d ↦ a]}[r ∣ O_d]` — the deviation conditioned on `O_d`;
* `refR2Sia C B d a := ∑_{q : d_q = d} R_q(C) G_q(C, a)` — Theorem 1's unnormalised SIA sum
  (`dp-local-opt`'s `siaSum`);
* `refR2Real actEv C B d a` — reach-weighted single-instance forcing at the **node-action-veridical**
  `d`-nodes only (`realFiber`), every other node (simulations included) still drawing from `C`,
  unconditioned on `O_d`: reading 1 of dp-sl-2-058, Definition F2's letter;
* `refR2RealObs obs actEv C B d a` — reading 2: the same with both sums restricted to the leaves
  whose world lies in `O_d`;
* `refR3 obs actEv C B d a := limitVal C B (a ∧ O_d)` — Remark 3.9's tremble-limit evidential
  act value, taken algebraically (`dp-calibration`'s `limitVal`).

Never a Lean name called "CDT": `refR2Real` is `refR2Real` (dp-sl-004's flag; mandate §3.6).

**The `cf` slot** (v2 Definition 2, act values only): `Cf`, `CfCalibratedAt`, `TCdtAt`,
`EvidentialCriterionAt`, `TEdtExtAt`; the strict evidential value `evStrict` and its R3
extension `evExt`.

**Structural hypotheses** (mandate §3.4): `ActEvDisjoint` (Definition 3's pairwise disjointness,
§7 trap 1), `ActRecordingStructural` (F3′ for every full-support procedure), `ActRecordingTrembles`,
`RecordsForTrembles`, with the equivalences to `ActRecording uniformProc` / `RecordsForAll`.

**Definition 6′ conditionals** for the seed rows: `paySum'`, `condExp'`, `refR1State'`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## The referent family -/

section referents

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **R1-prior**: the all-instance deviation, prior-weighted: `V_B(C[d ↦ a])`.
Source: `cf-workflow/phase2-notes/repair/faithful.md` line 38 (Definition F2, R1 "prior `⊤`");
[[decision-problems-v2]] Remark 3.11 (the deviation counterfactual); dp-sl-004
Kind: D
Fidelity: exact -/
def refR1Prior (d : ι) (a : acts d) : K := value (C.deviatePure d a) B

/-- **R1-state**: the all-instance deviation conditioned on the observation: `𝔼_{C[d ↦ a]}[r ∣ O_d]`.
Junk `0` where `ν_{C[d ↦ a]}(O_d) = 0`; every theorem carries the guard.
Source: `faithful.md` line 38 (Definition F2, R1 "observation-conditioned `O_d` = R1-state");
dp-sl-004
Kind: D
Fidelity: exact (guarded quotient) -/
def refR1State (d : ι) (a : acts d) : K := condExp (C.deviatePure d a) B (obs d)

/-- **R2-SIA**: Theorem 1's unnormalised fiber sum `∑_{q : d_q = d} R_q(C) G_q(C, a)`, `dp-local-opt`'s
`siaSum`; the normaliser is `𝔼_μ[#_d]` (`sum_reach_fiber_eq_expCount`).
Source: `faithful.md` line 38 (Definition F2, R2 "SIA weights `∑_q R_q G_q` (Theorem 1)");
[[decision-problems-v2]] §8 Theorem 1
Kind: D
Fidelity: exact (unnormalised, as v2's Theorem 1 states it) -/
def refR2Sia (d : ι) (a : acts d) : K := siaSum C B d a

/-- The **real fiber**: the `d`-nodes that are node-action-veridical (F3′'s node notion: every leaf
below the `a`-edge lies in the action event `a`, for every `a`). A structural set (no `C`).
Source: `faithful.md` line 38 (Definition F2, R2-real "averaged over the node-action-veridical
instances"); line 40 (Definition F3′)
Kind: D -/
noncomputable def realFiber (d : ι) : Finset B.DecNode := by
  classical exact (fiber B d).filter fun q => NodeActionVeridical actEv B q

/-- Membership in the real fiber. Source: none: infrastructure. Kind: L -/
theorem mem_realFiber (d : ι) (q : B.DecNode) :
    q ∈ realFiber actEv B d ↔ pt B q = d ∧ NodeActionVeridical actEv B q := by
  unfold realFiber
  simp only [Finset.mem_filter, fiber, Finset.mem_univ, true_and]

/-- The reach-weighted forced payoff mass at the real fiber: `∑_{q ∈ realFiber} R_q(C) G_q(C, a)`
rendered as `∑_q forcedBelow (ofProc C) q a` (no division), `a` transported along `pt B q = d`
as `siaSum_eq_sum_fiber_forcedBelow` does it.
Source: `faithful.md` line 38 (Definition F2, R2-real); mandate §3.2
Kind: D -/
noncomputable def realForced (d : ι) (a : acts d) : K :=
  ∑ q ∈ realFiber actEv B d,
    if h : pt B q = d then forcedBelow B (NodePolicy.ofProc C B) q (h ▸ a) else 0

/-- The reach mass of the real fiber: `∑_{q ∈ realFiber} R_q(C)`.
Source: `faithful.md` line 38 (Definition F2, R2-real: "a reach-weighted average"); mandate §3.2
Kind: D -/
noncomputable def realReach (d : ι) : K := ∑ q ∈ realFiber actEv B d, reach C B q

/-- **R2-real, reading 1** (Definition F2's letter; the toolkit's `r2real`): reach-weighted
single-instance forcing at the node-action-veridical `d`-nodes only, every other node — the
predictor's simulations included — still drawing from `C`, **unconditioned on `O_d`**:
`(∑_{q ∈ realFiber} R_q G_q(a)) / (∑_{q ∈ realFiber} R_q)`. Junk `0` at a null denominator (a
selection node such as Told-You-So's `d₅`); every theorem carries the guard. Classical CDT's
counterfactual *by construal* (FA-19′: "in the act-recording algebra"; ATTRIBUTION-UNVETTED) — the
Lean name never says "CDT".
Source: `faithful.md` line 38 (Definition F2, R2-real "not `O_d`-conditioned — a reach-weighted
average unconditioned on `O_d`"); dp-sl-2-058 reading 1; FA-19′; mandate §3.2
Kind: D
Fidelity: exact (reading 1 of an ambiguous source; reading 2 is `refR2RealObs`) -/
noncomputable def refR2Real (d : ι) (a : acts d) : K :=
  realForced actEv C B d a / realReach actEv C B d

/-- Reading 2's numerator: the forced payoff mass at each real-fiber node, restricted to the
leaves whose world lies in `O_d`.
Source: dp-sl-2-058 reading 2 (`O_d`-conditioned forcing); mandate §3.2
Kind: D -/
noncomputable def realForcedObs (d : ι) (a : acts d) : K :=
  ∑ q ∈ realFiber actEv B d,
    if h : pt B q = d then
      ∑ ℓ ∈ (leavesBelow B q).filter (fun ℓ => world B ℓ ∈ obs d),
        leafLawNode B ((NodePolicy.ofProc C B).update q (FinDistr.pure (h ▸ a))) ℓ * payoff B ℓ
    else 0

/-- Reading 2's denominator: the `C`-mass of the leaves below the real-fiber nodes whose world
lies in `O_d`.
Source: dp-sl-2-058 reading 2; mandate §3.2
Kind: D -/
noncomputable def realReachObs (d : ι) : K :=
  ∑ q ∈ realFiber actEv B d,
    ∑ ℓ ∈ (leavesBelow B q).filter (fun ℓ => world B ℓ ∈ obs d), leafLaw C B ℓ

/-- **R2-real, reading 2**: reading 1 with both sums restricted to the leaves whose world lies in
`O_d` (`O_d`-conditioned forcing). Agrees with reading 1 wherever every node-action-veridical
`d`-node is subtree-veridical (F3′'s first clause) and differs on the post-act coin tree
(`Rows.lean`).
Source: dp-sl-2-058 reading 2; `repair/C1.md` Open 3; mandate T1(b)
Kind: D
Fidelity: variant: the second of two readings of an ambiguous source -/
noncomputable def refR2RealObs (d : ι) (a : acts d) : K :=
  realForcedObs obs actEv C B d a / realReachObs obs actEv C B d

/-- **R3**: Remark 3.9's tremble-limit evidential act value `lim_{ε→0⁺} 𝔼_{C^ε}[r ∣ a ∧ O_d]`,
taken algebraically by `dp-calibration`'s `limitVal` (lowest-order coefficients). Meaningful when
`nuPoly C B (a ∧ O_d) ≠ 0` (the act is tremble-reachable within `O_d`); junk `0` otherwise.
Source: `faithful.md` line 38 (Definition F2, R3 `cf^tr`); [[decision-problems-v2]] Remark 3.9
(advice stance); dp-sl-004
Kind: D
Fidelity: variant: limit taken algebraically (inherited from `dp-calibration`'s `limitVal`) -/
noncomputable def refR3 [∀ d, Nonempty (acts d)] (d : ι) (a : acts d) : K :=
  limitVal C B (actEv d a ∩ obs d)

end referents

/-! ## The strict evidential value, its R3 extension, and the `cf` slot -/

section cfSlot

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- The **strict evidential act value** `V_{s_d}(a)`: the state's desirability of the action
event, read only on `A_d^+` (junk off it, like every `V` on a null event).
Source: [[decision-problems-v2]] Definition 17 (`V_{s_d}(a)`, `a ∈ A_d^+`); mandate §3.2
Kind: D
Fidelity: exact -/
def evStrict (d : ι) (a : acts d) : K := (s d).V (actEv d a)

/-- The **R3-extended evidential value**: `V_{s_d}(a)` on `A_d^+`, `refR3 a` off it — Theorem
C2-A′'s hypothesis (b-R3) ("evidential act values at nulled acts read as R3") as a definition.
Source: `sl-workflow/notes/repair/C2.md` line 50 (Theorem C2-A′, hypothesis (b-R3)); mandate §3.2
Kind: D
Fidelity: exact ((b-R3) rendered as a definition, so it is never a hypothesis) -/
noncomputable def evExt [∀ d, Nonempty (acts d)] (d : ι) (a : acts d) : K :=
  if a ∈ APlus s actEv d then evStrict s actEv d a else refR3 obs actEv C B d a

/-- **The `cf` slot, act values only**: `cf d a` is the supposed desirability `V^a_{s_d}(a)` of
act `a` under supposing `a`. v2's `cf_s` returns a probability-and-desirability pair on every
non-`⊥` event; only the act-value coordinate is read by any theorem of this package, so only it is
modelled.
Source: [[decision-problems-v2]] §1 Definition 2 clause 3 (`cf_s`); mandate §3.3
Kind: D
Fidelity: variant: act values only (the probability coordinate and non-act events are not
modelled) -/
abbrev Cf (ι : Type) (acts : ι → Type) (K : Type) : Type := (d : ι) → acts d → K

/-- **Counterfactual calibration** of the `cf` slot to a referent `R` on a domain `dom`
(Remark 3.11's "adopting … as *the* referent of `cf_s`").
Source: [[decision-problems-v2]] Remark 3.11; Definition 20 ("counterfactual calibration");
mandate §3.3
Kind: D -/
def CfCalibratedAt (cf : Cf ι acts K) (d : ι) (R : acts d → K) (dom : acts d → Prop) : Prop :=
  ∀ a, dom a → cf d a = R a

/-- **`T_CDT` at `d`**, Definition 18's advocacy shape with the `cf` slot as act value and the
**full** domain `A_d`: `supp C(d) ⊆ argmax_{a ∈ A_d} cf d a`. P12-6 and the C2 thread use this
domain (v2 says "each with its own act value and maximization domain"); the domain difference
from `TEdtAt` (`A_d^+`) is what the R3 extension bridges.
Source: [[decision-problems-v2]] Definition 18 (`T_CDT` "analogously"); `repair/P12.md` P12-6;
`C2.md` line 50; mandate §3.3
Kind: D
Fidelity: variant: domain `A_d` (disclosed; v2 leaves `T_CDT`'s domain to the evaluator) -/
def TCdtAt (cf : Cf ι acts K) (C : Proc ι acts K) (d : ι) : Prop :=
  ∀ a, 0 < (C d).w a → ∀ b, cf d b ≤ cf d a

/-- **Definition 20's evidential criterion, value half, on `A_d^+`**: `cf d a = V_{s_d}(a)` for
every subjectively possible act. The probability half (`P^a_{s_d} = P_{s_d}(· ∣ a)`) is not
modelled (the `cf` slot carries act values only).
Source: [[decision-problems-v2]] Definition 20 ("the *evidential criterion*"); mandate §3.3
Kind: D
Fidelity: variant: value half only, on `A_d^+` -/
def EvidentialCriterionAt (cf : Cf ι acts K) (d : ι) : Prop :=
  ∀ a ∈ APlus s actEv d, cf d a = evStrict s actEv d a

/-- **`T_EDT` at `d` with the R3-extended evidential value** (the (b-R3) reading of Theorem
C2-A′): `supp C(d) ⊆ argmax_{a ∈ A_d} evExt a`. `dp-calibration`'s `TEdtAt` (domain `A_d^+`) is
the (b-int) reading.
Source: `C2.md` line 50 (Theorem C2-A′: "`T_EDT`(R3-extended)"); mandate §3.3
Kind: D
Fidelity: exact for the R3-extended reading -/
def TEdtExtAt [∀ d, Nonempty (acts d)] (d : ι) : Prop :=
  ∀ a, 0 < (C d).w a → ∀ b, evExt s obs actEv C B d b ≤ evExt s obs actEv C B d a

end cfSlot

/-! ## Structural hypotheses: Definition 3's disjointness, F3′ structural, recording for the trembles -/

section structural

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
variable [∀ d, Nonempty (acts d)]

/-- **Definition 3's pairwise disjointness of the action events at `d`**. `ActRecording` carries
no exclusivity clause (a leaf in `actEv d b` need not lie below a `b`-edge), so the factorisation
`ν_C(a ∧ O_d) = C(d)(a) ∑_q R_q` needs this structural hypothesis by name (mandate §7 trap 1;
`recordsFor_iff_actRecordingOn` shows it is exactly the clause that turns F3′ into recording).
Source: [[decision-problems-v2]] §2 Definition 3 ("pairwise disjoint as events")
Kind: D -/
def ActEvDisjoint (d : ι) : Prop := ∀ a b : acts d, a ≠ b → Disjoint (actEv d a) (actEv d b)

/-- **F3′ structural**: veridical act-recording at `d` for *every* full-support procedure — every
chance-positive `O_d`-run passes exactly one node-action-veridical `d`-node, each subtree-veridical.
Source: `C2.md` line 50 (hypothesis (d′), "F3′ structural"); `faithful.md` FA-17′(b) ("F3′ for
the trembles `C^ε` (equivalently for every full-support procedure)"); mandate §3.4
Kind: D -/
def ActRecordingStructural (B : Tree Ω ι acts K) (d : ι) : Prop :=
  ∀ C : Proc ι acts K, C.FullSupport → ActRecording obs actEv C B d

/-- **F3′ for the trembles** of `C`: `ActRecording` for `C^ε` at every `ε ∈ (0, 1]`.
Source: `faithful.md` FA-20′(i) ("veridically act-recording at `d` (F3′) for the trembles
`C^ε`"); mandate §3.4
Kind: D -/
def ActRecordingTrembles (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (d : ι) : Prop :=
  ∀ ε : K, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ActRecording obs actEv (tremble C ε h0.le h1) B d

/-- **Definition 7 recording for the trembles** of `C`: `RecordsFor` for `C^ε` at every
`ε ∈ (0, 1]`.
Source: `faithful.md` FA-20′(ii), FA-25′(2′) ("Definition 7 recording for `C^ε`"); mandate §3.4
Kind: D -/
def RecordsForTrembles (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (d : ι) : Prop :=
  ∀ ε : K, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), RecordsFor obs actEv (tremble C ε h0.le h1) B d

variable {obs actEv}

/-- A leaf of positive mass under any procedure is chance-positive, hence of positive mass under
every full-support procedure. Source: none: infrastructure. Kind: L -/
theorem leafLaw_pos_of_pos_of_fullSupport {C C' : Proc ι acts K} (hC' : C'.FullSupport)
    (B : Tree Ω ι acts K) {ℓ : B.Leaves} (h : 0 < leafLaw C B ℓ) : 0 < leafLaw C' B ℓ :=
  leafLaw_pos_of_fullSupport hC' B ℓ (Positive.of_leafLaw_pos C h)

/-- F3′ transfers from a full-support procedure to every procedure (the run-dependent clause only
quantifies over positive-mass leaves, which are chance-positive).
Source: `faithful.md` FA-17′(b) ("equivalently for every full-support procedure"); mandate §3.4
Kind: L -/
theorem ActRecording.of_fullSupport {C' : Proc ι acts K} (hC' : C'.FullSupport)
    {B : Tree Ω ι acts K} {d : ι} (h : ActRecording obs actEv C' B d) (C : Proc ι acts K) :
    ActRecording obs actEv C B d :=
  ⟨h.1, fun ℓ hpos hobs => h.2 ℓ (leafLaw_pos_of_pos_of_fullSupport hC' B hpos) hobs⟩

/-- Recording transfers from a full-support procedure to every procedure.
Source: `sl-synthesis.md` line 20 ("for every procedure"); mandate §3.4
Kind: L -/
theorem RecordsFor.of_fullSupport {C' : Proc ι acts K} (hC' : C'.FullSupport)
    {B : Tree Ω ι acts K} {d : ι} (h : RecordsFor obs actEv C' B d) (C : Proc ι acts K) :
    RecordsFor obs actEv C B d :=
  fun ℓ hpos hobs => h ℓ (leafLaw_pos_of_pos_of_fullSupport hC' B hpos) hobs

/-- The uniform procedure has full support. Source: none: infrastructure. Kind: L -/
theorem uniformProc_fullSupport :
    (uniformProc (ι := ι) (acts := acts) (K := K)).FullSupport :=
  fun _ a => FinDistr.uniform_w_pos a

/-- **F3′ structural is F3′ for the uniform procedure** (the lemma `L` of mandate §3.4).
Source: mandate §3.4
Kind: L -/
theorem actRecordingStructural_iff_uniform (B : Tree Ω ι acts K)
    (d : ι) :
    ActRecordingStructural obs actEv B d ↔ ActRecording obs actEv uniformProc B d :=
  ⟨fun h => h _ uniformProc_fullSupport,
    fun h C _ => ActRecording.of_fullSupport uniformProc_fullSupport h C⟩

/-- F3′ structural gives F3′ for every procedure, full support or not.
Source: mandate §3.4
Kind: L -/
theorem ActRecordingStructural.actRecording {B : Tree Ω ι acts K}
    {d : ι} (h : ActRecordingStructural obs actEv B d) (C : Proc ι acts K) :
    ActRecording obs actEv C B d :=
  ActRecording.of_fullSupport uniformProc_fullSupport (h _ uniformProc_fullSupport) C

/-- **F3′ structural is F3′ for the trembles** (of any procedure).
Source: `faithful.md` FA-17′(b), FA-20′(i); mandate §3.4
Kind: L -/
theorem actRecordingStructural_iff_trembles (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) :
    ActRecordingStructural obs actEv B d ↔ ActRecordingTrembles obs actEv C B d := by
  constructor
  · intro h ε h0 h1
    exact h _ (tremble_fullSupport C ε h0 h1)
  · intro h C' _
    exact ActRecording.of_fullSupport (tremble_fullSupport C 1 one_pos le_rfl)
      (h 1 one_pos le_rfl) C'

/-- **Recording for the trembles is recording for every procedure** (what lets the tremble
theorems reuse `nu_factor_of_recordsForAll`).
Source: mandate §3.4 ("equivalent to `RecordsForAll obs actEv B d` by the same lemma")
Kind: L -/
theorem recordsForTrembles_iff_recordsForAll (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) :
    RecordsForTrembles obs actEv C B d ↔ RecordsForAll obs actEv B d := by
  constructor
  · intro h C'
    exact RecordsFor.of_fullSupport (tremble_fullSupport C 1 one_pos le_rfl) (h 1 one_pos le_rfl) C'
  · intro h ε h0 h1
    exact h _

/-- Recording for every procedure is recording for the uniform one.
Source: mandate §3.4
Kind: L -/
theorem recordsForAll_iff_uniform (B : Tree Ω ι acts K) (d : ι) :
    RecordsForAll obs actEv B d ↔ RecordsFor obs actEv uniformProc B d :=
  ⟨fun h => h _, fun h C => RecordsFor.of_fullSupport uniformProc_fullSupport h C⟩

end structural

/-! ## R2-real on a one-node fiber is `G_q` -/

section oneNode

variable (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **R2-real on a one-node real fiber is single-instance forcing `G_q` at that node**: the
identification `dp-causal-consist` makes with its `CDT_π` is one line through this lemma.
Source: `faithful.md` FA-19′ ("forcing at the node-action-veridical instance"); mandate §3.6
Kind: L -/
theorem refR2Real_eq_gNode_of_singleton [∀ d, Nonempty (acts d)] {d : ι} {q : B.DecNode}
    (hfib : realFiber actEv B d = {q}) (hq : pt B q = d) (a : acts d) :
    refR2Real actEv C B d a = gNode B (NodePolicy.ofProc C B) q (hq ▸ a) := by
  unfold refR2Real realForced realReach gNode
  rw [hfib, Finset.sum_singleton, Finset.sum_singleton, dif_pos hq, reachNode_ofProc]

end oneNode

/-! ## Definition 6′ conditionals for the seed rows -/

section seed

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- `∑_{λ ⊨ X} μ'_{B,C}(ℓ) r(ℓ)`: the payoff mass of an event under the shared-seed law.
Source: `seeds.md` Definition 6′; mandate §7 trap 7
Kind: D -/
def paySum' (X : Finset Ω) : K := ∑ ℓ ∈ worldEv B X, leafLaw' C B ℓ * payoff B ℓ

/-- `𝔼_{μ'}[r ∣ λ ⊨ X] := paySum' X / ν'(X)`, junk `0` at a null denominator.
Source: `seeds.md` Definition 6′; `C2.md` C2-3″ (EV′); mandate T4, T7, T14
Kind: D -/
def condExp' (X : Finset Ω) : K := paySum' C B X / nu' C B X

/-- **R1-state′**: the shared-seed deviation conditioned on `O_d`, `𝔼_{μ'_{C[d ↦ a]}}[r ∣ O_d]`.
Source: `faithful.md` line 113 ("R1-state under shared seed — the `O_d`-conditioned shared-seed
deviation"); mandate T7
Kind: D -/
def refR1State' (obs : ι → Finset Ω) (d : ι) (a : acts d) : K :=
  condExp' (C.deviatePure d a) B (obs d)

end seed

end Cleanroom.Decision.DpReferentsCdt
