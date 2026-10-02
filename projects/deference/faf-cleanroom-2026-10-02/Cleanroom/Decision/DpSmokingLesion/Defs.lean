import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Found.DpCoreTree.Tickle
import Cleanroom.Found.DpCoreTree.Multilinear
import Cleanroom.Found.DpCoreTree.RecordingFull
import Cleanroom.Found.DpCoreTree.Screening

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `dp-smoking-lesion`: definitions of record

Package `dp-smoking-lesion` (area `decision`). This file holds the conventions of
[[dp-smoking-lesion-mandate]] §3: the lesion family's worlds and events, the observation
`O_d = ⊤` and the action events `{m = ·}`, the stipulation (S2) as a predicate on a state, the
shape-form and predicate-form renderings of (S1)'s "cancer drawn from the lesion only", the
catalogue trees of the package (`slOne`, `cexA`, `e2a`, `e13`, `slOneCausal`), the three
referents Proposition 13 compares (R1-state, R2-SIA, R2-real in both readings), and the
abstract problems `Σ_SL(S1–S3)` and `Σ_SL(S1–S4)`.

## Modelling choices, disclosed once here

* **Worlds** are `dp-core-tree`'s `TickleW = Bool × Bool × Bool` (`(ℓ, m, k)`); the events
  `evM m = {m = ·}` and `evK = {k = 1}` are `dp-core-tree`'s (`Tickle.lean`); `evL = {ℓ = 1}`
  is new. **(S3)** is `slObs := fun _ => ⊤`; the action events are `slActEv _ m := evM m`.
* **(S4) is never a `def`**: it is `RecordsFor slObs slActEv C B d` in every statement, with
  the recording form (`RecordsFor` for `C` / for the self-model / `RecordsForAll` / `HStar`)
  named in the docstring.
* **(S2)** is cross-multiplied with both conditionals guarded (`S2`): `P(m=1) > 0`, `P(m=0) > 0`
  and `P(k ∧ m=0)·P(m=1) < P(k ∧ m=1)·P(m=0)`.
* **(S1)'s lesion-only clause** has a shape form (the enumerated tree `slOne`) and a
  predicate form (`LesionOnlyAt`, kind `D`, disclosed): at every `d`-node the lesion is decided
  and the cancer mass below every action edge is `γ_{ℓ(q)}` times the edge mass. The
  theorems of `General.lean` use the weaker `PostQueryIndep`: the cancer mass below the edges
  of a `d`-node is proportional to the edge mass with one constant per node.
* **R2-real** (dp-sl-2-058, ill-posed in v2) is fixed here as **reading 2**: the reach-weighted
  average of `forcedBelow` over the `d`-nodes that are a.s. node-action-veridical *and met on
  a positive `O_d`-run* (`r2Real`); reading 1 (all a.s. node-action-veridical `d`-nodes,
  off-`O_d` included) is `r2RealAll`. FA-19′'s identification of either with classical CDT is
  ATTRIBUTION-UNVETTED and not asserted.
* Every referent is a pair (payoff mass, normaliser). The division form `r1StateVal` exists
  for readability and is read by a headline only where its normaliser is `1` — every `⊤`
  tree, where `r1StateNu = ν_{C[d↦a]}(⊤) = 1` (`prop13_slOne_smokes_by_alpha`, `e2a_r1State`,
  `e13_verdicts`, `steelman_r1State_vs_limit`); no headline divides by a quantity that can
  vanish.
* Scalars are `ℚ` for the catalogue trees and a linearly ordered field `K` for the general
  theorems, as in the dependencies.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## Worlds, events, observation and action events -/

/-- The lesion event `{ℓ = 1}` on the `(ℓ, m, k)` worlds.
Source: [[decision-problems-v2]] §7.3 (S1)
Kind: D -/
def evL : Finset TickleW := Finset.univ.filter fun w => w.1 = true

/-- Membership in `evL`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evL (w : TickleW) : w ∈ evL ↔ w.1 = true := by simp [evL]

/-- Membership in `evM`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evM (m : Bool) (w : TickleW) : w ∈ evM m ↔ w.2.1 = m := by simp [evM]

/-- Membership in `evK`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evK (w : TickleW) : w ∈ evK ↔ w.2.2 = true := by simp [evK]

/-- **(S3): the uninformative observation `O_d = ⊤`** at every point.
Source: [[decision-problems-v2]] §7.3 (S3)
Kind: D -/
def slObs {ι : Type} : ι → Finset TickleW := fun _ => Finset.univ

/-- The action events `{m = ·}` at every point (the act coordinate of the world).
Source: [[decision-problems-v2]] §7.3 ("act `m`")
Kind: D -/
def slActEv {ι : Type} : ι → Bool → Finset TickleW := fun _ m => evM m

/-- `slObs d = ⊤`. Source: none: infrastructure. Kind: L -/
@[simp] theorem slObs_apply {ι : Type} (d : ι) : slObs d = Finset.univ := rfl

/-- `slActEv d m = evM m`. Source: none: infrastructure. Kind: L -/
@[simp] theorem slActEv_apply {ι : Type} (d : ι) (m : Bool) : slActEv d m = evM m := rfl

/-- `evM true` and `evM false` are disjoint. Source: none: infrastructure. Kind: L -/
theorem evM_disjoint : Disjoint (evM true) (evM false) := by
  rw [Finset.disjoint_left]; intro w h1 h0; simp at h1 h0; rw [h1] at h0; exact Bool.noConfusion h0

/-- `evM true ∪ evM false = ⊤`. Source: none: infrastructure. Kind: L -/
theorem evM_union : evM true ∪ evM false = Finset.univ := by
  ext w; simp only [Finset.mem_union, mem_evM, Finset.mem_univ, iff_true]; cases w.2.1 <;> simp

/-! ## The stipulation (S2) and flat statistics -/

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **(S2)**: the state's act-conditionals of cancer correlate, both defined —
`P(m=1) > 0`, `P(m=0) > 0` and, cross-multiplied, `P(k ∧ m=0) · P(m=1) < P(k ∧ m=1) · P(m=0)`
(i.e. `P(k ∣ m=0) < P(k ∣ m=1)`).
Source: [[decision-problems-v2]] §7.3 (S2) ("`P_s(k ∣ m=1) > P_s(k ∣ m=0)`, both defined")
Kind: D
Fidelity: exact (cross-multiplied; "both defined" is the two positivity clauses) -/
def S2 (s : State TickleW K) : Prop :=
  0 < s.pr (evM true) ∧ 0 < s.pr (evM false) ∧
    s.pr (evK ∩ evM false) * s.pr (evM true) < s.pr (evK ∩ evM true) * s.pr (evM false)

section trees

variable {ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)]

/-- The act-conditionals of cancer under `ν_{B,C}` are flat, cross-multiplied:
`ν(k ∧ m=1) · ν(m=0) = ν(k ∧ m=0) · ν(m=1)`. This is the conclusion of the repaired Lemma 3
(`k ⊥ m` under `ν`) in the form every refutation of (S2) needs.
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("`m ⊥ (ℓ, k)` under `ν_{B,C}`"), the `k`-clause
Kind: D -/
def NuFlat (C : Proc ι acts K) (B : Tree TickleW ι acts K) : Prop :=
  nu C B (evK ∩ evM true) * nu C B (evM false) = nu C B (evK ∩ evM false) * nu C B (evM true)

/-- The lesion is independent of the act under `ν`, cross-multiplied against `ν(⊤) = 1`:
`ν(ℓ ∧ m) · ν(⊤) = ν(ℓ) · ν(m)` for both acts.
Source: [[decision-problems-v2]] §7.3 Lemma 3, the `ℓ`-clause
Kind: D -/
def NuLesionIndep (C : Proc ι acts K) (B : Tree TickleW ι acts K) : Prop :=
  ∀ m, nu C B (evL ∩ evM m) * nu C B Finset.univ = nu C B evL * nu C B (evM m)

variable [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-- **Clause 1 at `O_d = ⊤` pins `P_{s_d}` to `ν`**: `P_{s_d}(X) = ν(X)` for every `X`.
Source: [[decision-problems-v2]] §3.1 Definition 8 clause 1 at `O_d = ⊤`
Kind: L -/
theorem pr_eq_nu_of_strictClause1At_univ (s : ι → State TickleW K) (C : Proc ι acts K)
    (B : Tree TickleW ι acts K) (d : ι) (h : StrictClause1At s slObs C B d) (X : Finset TickleW) :
    (s d).pr X = nu C B X := by
  have := h X
  rwa [slObs_apply, nu_univ, mul_one, Finset.inter_univ] at this

/-- **Flat `ν` refutes (S2) at every strictly-clause-1 state at `⊤`**: if
`ν(k ∧ m=1) · ν(m=0) = ν(k ∧ m=0) · ν(m=1)` and `P_{s_d} = ν(· ∣ ⊤)`, then `s_d` violates (S2).
Source: [[decision-problems-v2]] §7.3 Proposition 11 (the step "`P_s(k ∣ m=1) = P_s(k) =
P_s(k ∣ m=0)`, contradicting (S2)")
Kind: L -/
theorem not_S2_of_nuFlat (s : ι → State TickleW K) (C : Proc ι acts K)
    (B : Tree TickleW ι acts K) (d : ι) (h1 : StrictClause1At s slObs C B d)
    (hflat : NuFlat C B) : ¬ S2 (s d) := by
  rintro ⟨-, -, hlt⟩
  rw [pr_eq_nu_of_strictClause1At_univ s C B d h1, pr_eq_nu_of_strictClause1At_univ s C B d h1,
    pr_eq_nu_of_strictClause1At_univ s C B d h1, pr_eq_nu_of_strictClause1At_univ s C B d h1,
    hflat] at hlt
  exact lt_irrefl _ hlt

/-- **At `O_d = ⊤`, `H*` is Definition-7 recording and nothing more**: the second clause of
`H*` ("every positive run through a `d`-node is an `O_d`-run") is automatic. Cited wherever
Proposition 13's SSC clause is applied to a lesion tree (`dp-core-tree`'s `coinQuery_hStar_iff`
is the one-tree pattern).
Source: `sl-synthesis.md` line 20 (`H*`); mandate §3.3
Kind: L -/
theorem hStar_iff_recordsFor_slObs (C : Proc ι (fun _ => Bool) K)
    (B : Tree TickleW ι (fun _ => Bool) K) (d : ι) :
    HStar slObs slActEv C B d ↔ RecordsFor slObs slActEv C B d :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ => Finset.mem_univ _⟩⟩

end trees

/-! ## The lesion parameters and the catalogue trees -/

/-- The parameters of (S1): the lesion rate `ρ` and the cancer rates `γ₁ > γ₀` (the strict
inequality is the field `S1`), all in `[0, 1]`.
Source: [[decision-problems-v2]] §7.3 (S1) (`ℓ ∼ Bern(ρ)`, `k ∼ Bern(γ_ℓ)`, `γ₁ > γ₀`)
Kind: D -/
structure Lesion where
  /-- The lesion rate. -/
  ρ : ℚ
  /-- The cancer rate with the lesion. -/
  γ₁ : ℚ
  /-- The cancer rate without the lesion. -/
  γ₀ : ℚ
  ρ_nonneg : 0 ≤ ρ
  ρ_le_one : ρ ≤ 1
  γ₁_nonneg : 0 ≤ γ₁
  γ₁_le_one : γ₁ ≤ 1
  γ₀_nonneg : 0 ≤ γ₀
  γ₀_le_one : γ₀ ≤ 1

namespace Lesion

/-- The lesion coin (index `0` = `ℓ = 1`). Source: (S1). Kind: D -/
def coinL (L : Lesion) : FinDistr ℚ (Fin 2) := FinDistr.coin L.ρ L.ρ_nonneg L.ρ_le_one

/-- The cancer coin at lesion value `ℓ` (index `0` = `k = 1`): `Bern(γ_ℓ)`.
Source: [[decision-problems-v2]] §7.3 (S1) ("cancer drawn from the lesion only")
Kind: D -/
def coinK (L : Lesion) (ℓ : Bool) : FinDistr ℚ (Fin 2) :=
  FinDistr.coin (tickleGamma L.γ₁ L.γ₀ ℓ)
    (by unfold tickleGamma; split_ifs; exact L.γ₁_nonneg; exact L.γ₀_nonneg)
    (by unfold tickleGamma; split_ifs; exact L.γ₁_le_one; exact L.γ₀_le_one)

/-- `γ₁ > γ₀`: the lesion raises the cancer rate. Source: (S1). Kind: D -/
def S1 (L : Lesion) : Prop := L.γ₀ < L.γ₁

/-- The FDT-paper numbers `ρ = ½`, `γ = (99/100, 1/100)` used by S2, S3, E2a, E13, cexA.
Source: `sl-defensible-claims.md` S2 ("FDT numbers"); `adv_l1_counterexamples.py` line 15
Kind: D -/
def fdt : Lesion :=
  ⟨1/2, 99/100, 1/100, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- The E1-tickle numbers `ρ = ½`, `γ = (¾, ¼)`.
Source: `sl_zoo.py` line 129 (`E1_tickle` defaults); S5
Kind: D -/
def quarters : Lesion :=
  ⟨1/2, 3/4, 1/4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

end Lesion

/-- A leaf of the lesion family: world `(ℓ, m, k)`, payoff `α·m − β·k`.
Source: [[decision-problems-v2]] §7.3 ("leaf `(ℓ, m, k)`", `r = αm − βk`)
Kind: D -/
def slLeaf {ι : Type} {acts : ι → Type} (α β : ℚ) (ℓ m k : Bool) : Tree TickleW ι acts ℚ :=
  .leaf (ℓ, m, k) (ticklePay α β (ℓ, m, k))

/-- The cancer block: `k ∼ Bern(γ_ℓ)` then the leaf `(ℓ, m, k)`.
Source: [[decision-problems-v2]] §7.3 ("chance `k`; leaf `(ℓ, m, k)`")
Kind: D -/
def kBlock {ι : Type} {acts : ι → Type} (L : Lesion) (α β : ℚ) (ℓ m : Bool) :
    Tree TickleW ι acts ℚ :=
  .chance 2 (L.coinK ℓ) fun j => slLeaf α β ℓ m (decide (j = 0))

/-- **The recorded one-point instantiation** (`Σ_SL`'s enumerated shape): chance `ℓ ∼ Bern(ρ)`
(index `0` = `ℓ = 1`); query `d` (one point, `O_d = ⊤`, actions `Bool`, `true` = smoke); chance
`k ∼ Bern(γ_ℓ)`; leaf `(ℓ, m, k)`. The one-point sibling of `dp-core-tree`'s `tickle`.
Source: [[decision-problems-v2]] §7.3 ("Instantiations: chance `ℓ`; query `d`; act `m`; chance
`k`; leaf `(ℓ, m, k)`"); mandate §3.2(i)
Kind: D -/
def slOne (L : Lesion) (α β : ℚ) : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 L.coinL fun i => .decision () fun m => kBlock L α β (decide (i = 0)) m

/-- **Counterexample A** (the adversary's third population): a root coin `τ ∈ {E, A}` with
weight `π` on `E` (index `0`); on `E` the agent is queried *before* the lesion draw (one
`d`-node), then `ℓ ∼ Bern(ρ)`, then `k ∼ Bern(γ_ℓ)`; on `A` an automaton smokes iff lesioned
(`m := ℓ`), no query. Worlds record `(ℓ, m, k)` only. Every run meets `d` at most once and
post-query chance is a function of `ℓ` and the drawn action only (visible from the
constructors), but the `A`-runs satisfy `O_d = ⊤` and meet no `d`-node: coverage fails.
Source: `sl-workflow/notes/adversary/L1-scratch/adv_l1_counterexamples.py` lines 14–27;
`sl-synthesis.md` §1.2 "Register" (counterexample A); mandate §3.7
Kind: D -/
def cexA (π : ℚ) (p0 : 0 ≤ π) (p1 : π ≤ 1) (L : Lesion) (α β : ℚ) :
    Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 (FinDistr.coin π p0 p1)
    ![.decision () fun m => .chance 2 L.coinL fun i => kBlock L α β (decide (i = 0)) m,
      .chance 2 L.coinL fun i => kBlock L α β (decide (i = 0)) (decide (i = 0))]

/-- The population smoking rates of the reference class, `σ_ℓ ∈ [0, 1]`.
Source: `sl_zoo.py` line 134 (`s1`, `s0`)
Kind: D -/
structure RefClass where
  /-- Smoking rate of the reference class with the lesion. -/
  σ₁ : ℚ
  /-- Smoking rate of the reference class without the lesion. -/
  σ₀ : ℚ
  σ₁_nonneg : 0 ≤ σ₁
  σ₁_le_one : σ₁ ≤ 1
  σ₀_nonneg : 0 ≤ σ₀
  σ₀_le_one : σ₀ ≤ 1

namespace RefClass

/-- The reference class's smoking coin at lesion value `ℓ` (index `0` = smokes).
Source: `sl_zoo.py` line 138 (`bern("m", s, …)`)
Kind: D -/
def coinM (R : RefClass) (ℓ : Bool) : FinDistr ℚ (Fin 2) :=
  FinDistr.coin (if ℓ then R.σ₁ else R.σ₀)
    (by split_ifs; exact R.σ₁_nonneg; exact R.σ₀_nonneg)
    (by split_ifs; exact R.σ₁_le_one; exact R.σ₀_le_one)

/-- S3's reconciled rates `σ = (9/10, 1/10)` (the script's default `(¾, ¼)` gives `149/200`,
not S3's `223/250`; mandate §3.7).
Source: `sl-defensible-claims.md` S3 (`223/250`), reconciled by the mandate writer
Kind: D -/
def s3 : RefClass := ⟨9/10, 1/10, by norm_num, by norm_num, by norm_num, by norm_num⟩

end RefClass

/-- **The reference class E2a** (coverage failure): root `ℓ ∼ Bern(ρ)`; then a chance "who"
node — with weight `π` (index `0`) the agent is consulted (`d`, `O_d = ⊤`) and `k ∼ Bern(γ_ℓ)`
follows; with weight `1 − π` another member of the population writes `m ∼ Bern(σ_ℓ)` and
`k ∼ Bern(γ_ℓ)` follows. Worlds record `(ℓ, m, k)` only: the algebra does not say who acted.
Source: `sl_zoo.py` lines 126–140 (`E2a_refclass`); `sl-defensible-claims.md` S2 (R-a), S3;
mandate §3.7
Kind: D -/
def e2a (π : ℚ) (p0 : 0 ≤ π) (p1 : π ≤ 1) (L : Lesion) (R : RefClass) (α β : ℚ) :
    Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 L.coinL fun i =>
    .chance 2 (FinDistr.coin π p0 p1)
      ![.decision () fun m => kBlock L α β (decide (i = 0)) m,
        .chance 2 (R.coinM (decide (i = 0))) fun j => kBlock L α β (decide (i = 0)) (decide (j = 0))]

/-- The compulsion rates `c_ℓ ∈ [0, 1]`: the probability that a drawn refusal is overridden.
Source: `sl_zoo.py` line 719 (`c1`, `c0`)
Kind: D -/
structure Compulsion where
  /-- Override rate with the lesion. -/
  c₁ : ℚ
  /-- Override rate without the lesion. -/
  c₀ : ℚ
  c₁_nonneg : 0 ≤ c₁
  c₁_le_one : c₁ ≤ 1
  c₀_nonneg : 0 ≤ c₀
  c₀_le_one : c₀ ≤ 1

namespace Compulsion

/-- The override coin at lesion value `ℓ` (index `0` = forced to smoke).
Source: `sl_zoo.py` line 730 (`chance(("forced", c, …), ("free", 1 − c, …))`)
Kind: D -/
def coinF (T : Compulsion) (ℓ : Bool) : FinDistr ℚ (Fin 2) :=
  FinDistr.coin (if ℓ then T.c₁ else T.c₀)
    (by split_ifs; exact T.c₁_nonneg; exact T.c₀_nonneg)
    (by split_ifs; exact T.c₁_le_one; exact T.c₀_le_one)

/-- E13's numbers `c = (9/10, 1/10)`. Source: `sl_zoo.py` line 719. Kind: D -/
def e13Rates : Compulsion := ⟨9/10, 1/10, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Compulsion

/-- **The compulsion E13** (action-veridicality failure): root `ℓ ∼ Bern(ρ)`; query `d`
(`O_d = ⊤`) drawing `m_d`; if `m_d = 1` the realized act is `m = 1`; if `m_d = 0` a chance node
forces `m := 1` with probability `c_ℓ` (index `0`) and leaves `m := 0` otherwise; then
`k ∼ Bern(γ_ℓ)`; the leaf `(ℓ, m, k)` records the *realized* act only.
Source: `sl_zoo.py` lines 716–735 (`compulsion`, `record_draw=False`); `sl-defensible-claims.md`
S2 (R-b); mandate §3.7
Kind: D -/
def e13 (L : Lesion) (T : Compulsion) (α β : ℚ) : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 L.coinL fun i =>
    .decision () fun md =>
      cond md (kBlock L α β (decide (i = 0)) true)
        (.chance 2 (T.coinF (decide (i = 0))) fun j =>
          kBlock L α β (decide (i = 0)) (decide (j = 0)))

/-- **The flipped table** (chewing gum causally protects): a recorded one-point tree whose
cancer coin depends on the act, `k ∼ Bern(κ_m)`, with no lesion (`ℓ := false`). Records for
every procedure, yet (S2) can hold at the strict state when `κ_1 > κ_0` — (S1)'s lesion-only
clause is load-bearing for the `k`-conclusion even under recording.
Source: `sl-defensible-claims.md` S3 ("a flipped CGTA table (chewing causally protects) makes
(S2) hold at a *recorded* point"); mandate T1(d)
Kind: D -/
def slOneCausal (κ₁ : ℚ) (k10 : 0 ≤ κ₁) (k11 : κ₁ ≤ 1) (κ₀ : ℚ) (k00 : 0 ≤ κ₀) (k01 : κ₀ ≤ 1)
    (α β : ℚ) : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .decision () fun m =>
    .chance 2 (FinDistr.coin (if m then κ₁ else κ₀) (by split_ifs <;> assumption)
        (by split_ifs <;> assumption)) fun j =>
      slLeaf α β false m (decide (j = 0))


/-! ## Post-query statistics at a node: the predicate forms of (S1) -/

section nodeStats

variable {Ω ι : Type} [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)]

/-- The mass of the leaves below `q` taking edge `a` (the `a`-edge mass of `q`).
Source: none: infrastructure (`dp-core-tree`'s `mass_edge` reads it as `C(d_q)(a)` times the
mass below `q`)
Kind: D -/
def edgeMass (C : Proc ι acts K) (B : Tree Ω ι acts K) (q : B.DecNode) (a : acts (pt B q)) :
    K :=
  ∑ ℓ, if edgeOf B q ℓ = some a then leafLaw C B ℓ else 0

/-- The mass of the leaves below `q` taking edge `a` whose world lies in `X`.
Source: none: infrastructure
Kind: D -/
def edgeMassIn (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) (q : B.DecNode)
    (a : acts (pt B q)) : K :=
  ∑ ℓ, if edgeOf B q ℓ = some a ∧ world B ℓ ∈ X then leafLaw C B ℓ else 0

/-- **Post-query independence of `X` from the draw at `d`**: at every `d`-node the mass of
`X` below an action edge is proportional to the edge mass, with one constant per node
(cross-multiplied over pairs of actions). This is the printed Lemma 3's informal "post-query
chance depends on the path only through pre-query chance and the drawn action", specialised to
the event `X` and made a tree predicate; `LesionOnlyAt` (the (S1) clause) implies it with
`X = evK`.
Source: [[decision-problems-v2]] §7.3 Lemma 3 (hypothesis); mandate T1(c) ("the weakest
hypothesis you found")
Kind: D -/
def PostQueryIndep (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) : Prop :=
  ∀ q, pt B q = d → ∀ a b : acts (pt B q),
    edgeMassIn C B X q a * edgeMass C B q b = edgeMassIn C B X q b * edgeMass C B q a

end nodeStats

section lesionOnly

variable {ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- The lesion value decided at a node: `true` iff every leaf below `q` has `ℓ = 1`
(meaningful under `DecidedAt B q evL`).
Source: mandate §3.2(ii) ("`ℓ(q)` is the lesion value decided at `q`")
Kind: D -/
noncomputable def lesionOf (B : Tree TickleW ι acts K) (q : B.DecNode) : Bool := by
  classical exact decide (∀ ℓ ∈ leavesBelow B q, world B ℓ ∈ evL)

/-- **(S1)'s lesion-only clause, predicate form**: at every `d`-node the lesion is decided and,
for every action `a`, the cancer mass below the `a`-edge is `γ_{ℓ(q)}` times the `a`-edge
mass. A modelling rendering of "cancer drawn from the lesion only" (kind `D`, disclosed);
the theorems use its consequence `PostQueryIndep C B d evK`.
Source: [[decision-problems-v2]] §7.3 (S1) ("cancer drawn from the lesion only"); mandate
§3.2(ii)
Kind: D
Fidelity: variant: rendered as a per-node mass identity under decidedness of the lesion -/
def LesionOnlyAt (L : Lesion) (C : Proc ι acts ℚ) (B : Tree TickleW ι acts ℚ) (d : ι) : Prop :=
  ∀ q, pt B q = d → DecidedAt B q evL ∧ ∀ a : acts (pt B q),
    edgeMassIn C B evK q a = tickleGamma L.γ₁ L.γ₀ (lesionOf B q) * edgeMass C B q a

/-- The lesion-only clause implies post-query independence of cancer from the draw.
Source: none: infrastructure
Kind: L -/
theorem LesionOnlyAt.postQueryIndep {L : Lesion} {C : Proc ι acts ℚ} {B : Tree TickleW ι acts ℚ}
    {d : ι} (h : LesionOnlyAt L C B d) : PostQueryIndep C B d evK := by
  intro q hq a b
  rw [(h q hq).2 a, (h q hq).2 b]; ring

end lesionOnly

/-! ## The referents of Proposition 13 -/

section referents

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- Transport of an action along an equality of points.
Source: none: infrastructure
Kind: D -/
def transport {d d' : ι} (h : d = d') (a : acts d) : acts d' := h ▸ a

/-- Transport along `rfl` is the identity. Source: none: infrastructure. Kind: L -/
@[simp] theorem transport_rfl {d : ι} (a : acts d) : transport (acts := acts) rfl a = a := rfl

/-- On a constant action family the transport is the identity.
Source: none: infrastructure. Kind: L -/
@[simp] theorem transport_const {α : Type} {d d' : ι} (h : d = d') (a : α) :
    transport (acts := fun _ => α) h a = a := by subst h; rfl

/-- **R1-state, the payoff mass**: `∑_{ℓ : λ(ℓ) ⊨ O_d} μ_{B,C[d↦a]}(ℓ) r(ℓ)` — the all-instance
deviation `C[d ↦ a]` conditioned on the observation, numerator.
Source: `sl-synthesis.md` §0 ("R1-state = all-instance deviation `C[d↦a]` conditioned on
`O_d`"); [[decision-problems-v2]] Remark 3.11 (the all-instance deviation)
Kind: D -/
def r1StatePay (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (a : acts d) : K :=
  paySum (C.deviatePure d a) B (obs d)

/-- **R1-state, the normaliser**: `ν_{B,C[d↦a]}(O_d)`.
Source: `sl-synthesis.md` §0 (R1-state)
Kind: D -/
def r1StateNu (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (a : acts d) : K :=
  nu (C.deviatePure d a) B (obs d)

/-- R1-state as a quotient (readability; `0` when the normaliser is `0`). Read by a headline
only where the normaliser is `1`: on every `⊤` tree `r1StateNu = ν_{C[d↦a]}(⊤) = 1`, so there
`r1StateVal = r1StatePay` (audit r1 fidelity §3.3).
Source: `sl-synthesis.md` §0 (R1-state)
Kind: D -/
noncomputable def r1StateVal (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (d : ι) (a : acts d) : K :=
  r1StatePay obs C B d a / r1StateNu obs C B d a

/-- **R2-SIA, the numerator**: `∑_{q ∈ fiber d} R_q · G_q(C, a) = ∑_q forcedBelow_q(a)` —
Theorem 1's reach-weighted single-instance forcing, summed over every `d`-node (the action
transported to the node's type along `pt q = d`). `dp-local-opt`'s `siaSum` is the same object
by its `siaSum_eq_sum_fiber_forcedBelow` (not imported; stated here in four lines over
`dp-core-tree`'s `forcedBelow`).
Source: [[decision-problems-v2]] §8 Theorem 1 (`∑_{q : d_q = d} R_q G_q`); `sl-synthesis.md`
§0 (R2-SIA)
Kind: D -/
def r2Sia (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (a : acts d) : K :=
  ∑ q ∈ fiber B d, if h : pt B q = d then
    forcedBelow B (NodePolicy.ofProc C B) q (transport h.symm a) else 0

/-- **R2-SIA, the normaliser**: `∑_{q ∈ fiber d} R_q`.
Source: [[decision-problems-v2]] §8 Theorem 1 (`∑_q R_q`)
Kind: D -/
def fiberMass (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : K :=
  ∑ q ∈ fiber B d, reach C B q

/-- The `d`-nodes that are a.s. node-action-veridical and met on a positive `O_d`-run (the
averaging set of R2-real under **reading 2**, dp-sl-2-058).
Source: `sl-synthesis.md` §0 (R2-real: "single-instance forcing at the real,
node-action-veridical instance"); dp-sl-2-058 reading 2
Kind: D -/
noncomputable def realFiber (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Finset B.DecNode := by
  classical exact (fiber B d).filter fun q =>
    NodeActionVeridicalAS actEv C B q ∧ ActiveNode obs C B d q

/-- Membership in `realFiber`. Source: none: infrastructure. Kind: L -/
theorem mem_realFiber (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) :
    q ∈ realFiber obs actEv C B d ↔
      pt B q = d ∧ NodeActionVeridicalAS actEv C B q ∧ ActiveNode obs C B d q := by
  unfold realFiber
  simp only [Finset.mem_filter, fiber, Finset.mem_univ, true_and]

/-- The a.s. node-action-veridical `d`-nodes, on or off the `O_d`-runs (the averaging set of
R2-real under **reading 1**, dp-sl-2-058).
Source: dp-sl-2-058 reading 1 (C1's ledger and the toolkit's `r2real`)
Kind: D -/
noncomputable def realFiberAll (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) : Finset B.DecNode := by
  classical exact (fiber B d).filter fun q => NodeActionVeridicalAS actEv C B q

/-- Membership in `realFiberAll`. Source: none: infrastructure. Kind: L -/
theorem mem_realFiberAll (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) :
    q ∈ realFiberAll actEv C B d ↔ pt B q = d ∧ NodeActionVeridicalAS actEv C B q := by
  unfold realFiberAll
  simp only [Finset.mem_filter, fiber, Finset.mem_univ, true_and]

/-- **R2-real (reading 2), the numerator**: the forcing masses summed over `realFiber`.
Source: `sl-synthesis.md` §0 (R2-real); dp-sl-2-058, reading of record = reading 2
Kind: D
Fidelity: variant: construal — averaging set = a.s. veridical `d`-nodes on positive
`O_d`-runs (dp-sl-2-058 reading 2); FA-19′'s identification with classical CDT is
ATTRIBUTION-UNVETTED and not asserted -/
noncomputable def r2RealPay (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (a : acts d) : K :=
  ∑ q ∈ realFiber obs actEv C B d, if h : pt B q = d then
    forcedBelow B (NodePolicy.ofProc C B) q (transport h.symm a) else 0

/-- **R2-real (reading 2), the normaliser**: the reach masses summed over `realFiber`.
Source: dp-sl-2-058 reading 2
Kind: D -/
noncomputable def r2RealMass (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : K :=
  ∑ q ∈ realFiber obs actEv C B d, reach C B q

/-- **R2-real (reading 1), the numerator**: the forcing masses summed over `realFiberAll`.
Source: dp-sl-2-058 reading 1
Kind: D -/
noncomputable def r2RealAllPay (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) (a : acts d) : K :=
  ∑ q ∈ realFiberAll actEv C B d, if h : pt B q = d then
    forcedBelow B (NodePolicy.ofProc C B) q (transport h.symm a) else 0

/-- **R2-real (reading 1), the normaliser**.
Source: dp-sl-2-058 reading 1
Kind: D -/
noncomputable def r2RealAllMass (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) : K :=
  ∑ q ∈ realFiberAll actEv C B d, reach C B q

end referents

/-! ## The abstract problems `Σ_SL(S1–S3)` and `Σ_SL(S1–S4)` -/

/-- A tree is an **(S1)–(S3) instantiation**: one of the four catalogue shapes (`slOne`,
`cexA`, `e2a`, `e13`) at parameters with `γ₁ > γ₀` and `α, β > 0`. (The family is the
package's rendering of "instantiations of (S1)–(S3)"; it is closed under nothing, and the
consistency claims below quantify over it. It is **not** a family of non-recording trees:
`slOne` records for every procedure, and the other three shapes have recording members at
degenerate parameters — `e13` at `c = (0, 0)`, `e2a` and `cexA` at `π = 1` — so no theorem
should read "`Σ_SL(S1–S3)`" as "the non-recording instantiations"; none does.)
Source: [[decision-problems-v2]] §7.3 (S1)–(S3); mandate T2(a)
Kind: D
Fidelity: weaker: shape family (four shapes, not "every tree satisfying (S1)–(S3)") -/
def IsS123Tree (B : Tree TickleW Unit (fun _ => Bool) ℚ) : Prop :=
  ∃ (L : Lesion) (α β : ℚ), L.S1 ∧ 0 < α ∧ 0 < β ∧
    (B = slOne L α β ∨
     (∃ π p0 p1, B = cexA π p0 p1 L α β) ∨
     (∃ π p0 p1 R, B = e2a π p0 p1 L R α β) ∨
     (∃ T, B = e13 L T α β))

/-- A tree is the **recorded (S4) instantiation**: `slOne` at parameters with `γ₁ > γ₀` and
`α, β > 0`.
Source: [[decision-problems-v2]] §7.3 ("Instantiations: chance `ℓ`; query `d`; act `m`;
chance `k`; leaf `(ℓ, m, k)`"); mandate T2(b)
Kind: D
Fidelity: weaker: shape family -/
def IsS1234Tree (B : Tree TickleW Unit (fun _ => Bool) ℚ) : Prop :=
  ∃ (L : Lesion) (α β : ℚ), L.S1 ∧ 0 < α ∧ 0 < β ∧ B = slOne L α β

/-- **`Σ_SL(S1–S3)`**: the instantiations whose tree is an (S1)–(S3) shape and whose state at
`d` satisfies (S2).
Source: [[decision-problems-v2]] §7.3 (`Σ_SL`); mandate T2(a)
Kind: D
Fidelity: weaker: shape family -/
def sigmaSL123 : AbstractProblem TickleW Unit (fun _ => Bool) ℚ :=
  {I | IsS123Tree I.B ∧ S2 (I.s ())}

/-- **`Σ_SL(S1–S4)`**: the instantiations whose tree is `slOne` and whose state at `d`
satisfies (S2).
Source: [[decision-problems-v2]] §7.3 (`Σ_SL` with the enumerated shape); mandate T2(b)
Kind: D
Fidelity: weaker: shape family -/
def sigmaSL1234 : AbstractProblem TickleW Unit (fun _ => Bool) ℚ :=
  {I | IsS1234Tree I.B ∧ S2 (I.s ())}

end Cleanroom.Decision.DpSmokingLesion
