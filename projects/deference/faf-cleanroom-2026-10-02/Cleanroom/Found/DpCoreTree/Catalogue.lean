import Cleanroom.Found.DpCoreTree.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Fin

/-!
# The catalogue: the corpus's trees as definitions over `ℚ`

T13 of [[dp-core-tree-mandate]]: one `def` per tree over an explicit finite world type with named
coordinates. Definitions only; the values this package's witnesses need are proved in the
witness files. Each docstring cites its source line. Every tree is over `K = ℚ`.

Conventions: two-action points use `Act2` (`a`/`b`; the docstring says what `a` and `b` mean in
the source). A fair coin is `FinDistr.coin (1/2)`; index `0` of a `Fin 2` chance node is the
*first-named* branch of the source sentence. Observations `obs` and action events `actEv` are
given beside each tree as functions, following the source's algebra.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

/-! ### Building blocks -/

/-- Two actions.
Source: none: infrastructure (the two-action points of the catalogue)
Kind: D -/
inductive Act2 : Type
  | a
  | b
  deriving DecidableEq, Fintype

instance : Nonempty Act2 := ⟨Act2.a⟩

/-- `univ = {a, b}`. Source: none: infrastructure. Kind: L -/
theorem Act2.univ_eq : (Finset.univ : Finset Act2) = {.a, .b} := by
  ext x; cases x <;> simp

/-- Sums over `Act2`. Source: none: infrastructure. Kind: L -/
theorem Act2.sum_univ {M : Type} [AddCommMonoid M] (f : Act2 → M) : ∑ x, f x = f .a + f .b := by
  rw [Act2.univ_eq, Finset.sum_pair (by decide)]

/-- Sums over the (single) leaf of a leaf tree. Source: none: infrastructure. Kind: L -/
theorem Tree.sum_leaves_leaf {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)]
    {M : Type} [AddCommMonoid M] (ω : Ω) (r : ℚ)
    (f : (Tree.leaf ω r : Tree Ω ι acts ℚ).Leaves → M) : ∑ ℓ, f ℓ = f () := by
  show ∑ ℓ : Unit, f ℓ = f ()
  simp

/-- The mixed action `(q, 1 − q)` on `Act2`. Source: none: infrastructure. Kind: D -/
def FinDistr.act2 (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDistr ℚ Act2 where
  w := fun | .a => q | .b => 1 - q
  nonneg := by intro x; cases x <;> simp <;> linarith
  sum_one := by rw [Act2.sum_univ]; simp

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.act2_a (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (FinDistr.act2 q h0 h1).w .a = q := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.act2_b (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (FinDistr.act2 q h0 h1).w .b = 1 - q := rfl

/-- The one-point procedure `C(d) = (q, 1 − q)` on a `Unit`-point tree.
Source: none: infrastructure (`q := C(d)(a)` throughout the sources)
Kind: D -/
def procQ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc Unit (fun _ => Act2) ℚ :=
  fun _ => FinDistr.act2 q h0 h1

/-- A two-point coin with weight `p` on index `0`.
Source: none: infrastructure
Kind: D -/
def FinDistr.coin (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinDistr ℚ (Fin 2) where
  w := ![p, 1 - p]
  nonneg := by
    intro i; fin_cases i
    · simpa using h0
    · simp; linarith
  sum_one := by simp [Fin.sum_univ_two]

/-- A fair coin.
Source: [[decision-problems-v2]] Proposition 6 ("fair coin")
Kind: D -/
def FinDistr.fair : FinDistr ℚ (Fin 2) := FinDistr.coin (1/2) (by norm_num) (by norm_num)

/-- Three equiprobable branches.
Source: `calibration.md` line 23 ("chance root with three equiprobable branches")
Kind: D -/
def FinDistr.third : FinDistr ℚ (Fin 3) where
  w := ![1/3, 1/3, 1/3]
  nonneg := by intro i; fin_cases i <;> norm_num
  sum_one := by simp [Fin.sum_univ_three]; norm_num

namespace Catalogue

/-! ### The AMD (Proposition 5(c)) -/

/-- AMD worlds: the draw sequence `seq ∈ {a, ba, bb}`.
Source: `calibration.md` line 23 ("worlds recording the draw sequence `seq ∈ {a, ba, bb}`")
Kind: D -/
inductive AmdW : Type
  | sa
  | sba
  | sbb
  deriving DecidableEq, Fintype

/-- **The AMD** (v2 Proposition 5(c)): one point `d` at two nested nodes; first node `a → 0`,
`b →` second node; second node `a → 4`, `b → 1`.
Source: [[decision-problems-v2]] Proposition 5(c) (line 203)
Kind: D -/
def amd : Tree AmdW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .sa 0
    | .b => .decision () fun
      | .a => .leaf .sba 4
      | .b => .leaf .sbb 1

/-- AMD action events, **last-draw** encoding: `a := {seq ∈ {a, ba}}`, `b := {seq = bb}`.
Source: `calibration.md` line 23
Kind: D -/
def amdActEvLast : (d : Unit) → Act2 → Finset AmdW
  | _, .a => {.sa, .sba}
  | _, .b => {.sbb}

/-- AMD action events, **first-draw** encoding: `a := {seq = a}`, `b := {seq ∈ {ba, bb}}`.
Source: `calibration.md` line 23
Kind: D -/
def amdActEvFirst : (d : Unit) → Act2 → Finset AmdW
  | _, .a => {.sa}
  | _, .b => {.sba, .sbb}

/-- AMD observation: `⊤` (the source states none; nothing in this package reads it).
Source: none: infrastructure
Kind: D -/
def amdObs : Unit → Finset AmdW := fun _ => Finset.univ

/-! ### Remark 4.3's miniature -/

/-- Miniature worlds: `(sample, live)` draws.
Source: [[decision-problems-v2]] Remark 4.3 (line 172)
Kind: D -/
abbrev MiniW : Type := Act2 × Act2

/-- Miniature payoff: `2` on (live `a`, sample `b`), `1` on (live `b`, sample `a`), else `0`.
Source: [[decision-problems-v2]] Remark 4.3
Kind: D -/
def miniPay : Act2 → Act2 → ℚ
  | .b, .a => 2      -- sample b, live a
  | .a, .b => 1      -- sample a, live b
  | _, _ => 0

/-- **Remark 4.3's miniature**: `d` is sampled upstream by a predictor (independent draw from
`C(d)`), then queried live; leaf world `(sample, live)`.
Source: [[decision-problems-v2]] Remark 4.3 (line 172); mandate T13
Kind: D -/
def miniature : Tree MiniW Unit (fun _ => Act2) ℚ :=
  .decision () fun s => .decision () fun l => .leaf (s, l) (miniPay s l)

/-! ### Counterfactual Mugging `B₁` / `B₂` (Proposition 6) -/

/-- Mugging worlds: `(coin, choice, transfer)` restricted to the four leaf-worlds
`(T, pay, 0)`, `(T, refuse, 0)`, `(H, ⊥, 1)`, `(H, ⊥, 0)`.
Source: [[decision-problems-v2]] Proposition 6 (line 211)
Kind: D -/
inductive MugW : Type
  | tPay
  | tRefuse
  | hOne
  | hZero
  deriving DecidableEq, Fintype

/-- Mugging payoff `r = −x·1[pay] + y·1[transfer]`.
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mugPay (x y : ℚ) : MugW → ℚ
  | .tPay => -x
  | .tRefuse => 0
  | .hOne => y
  | .hZero => 0

/-- The leaf-world of the mugging `B₁` at chance index `i` (`0` = `T`, `1` = `H`) and action
`act` (`a` = pay, `b` = refuse): `(T, pay, 0)`, `(T, refuse, 0)`, `(H, ⊥, 1)`, `(H, ⊥, 0)`.
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mugWorld1 (i : Fin 2) (act : Act2) : MugW :=
  if i = 0 then (if act = .a then .tPay else .tRefuse) else (if act = .a then .hOne else .hZero)

/-- The leaf-world of `B₂`: the `H`-branch transfers swapped.
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mugWorld2 (i : Fin 2) (act : Act2) : MugW :=
  if i = 0 then (if act = .a then .tPay else .tRefuse) else (if act = .a then .hZero else .hOne)

/-- **`B₁` (Counterfactual Mugging)**: fair coin (index `0` = `T`); on `T` query `d`
(`a` = pay → `(T, pay, 0)`, `b` = refuse → `(T, refuse, 0)`); on `H` query `d` hypothetically
(pay → `(H, ⊥, 1)`, refuse → `(H, ⊥, 0)`). The two branches have one shape (query `d`, leaf),
so the chance children are one lambda in the index.
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mug1 (x y : ℚ) : Tree MugW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision () fun act => .leaf (mugWorld1 i act) (mugPay x y (mugWorld1 i act))

/-- **`B₂`**: identical to `B₁` with the `H`-branch transfers swapped.
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mug2 (x y : ℚ) : Tree MugW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision () fun act => .leaf (mugWorld2 i act) (mugPay x y (mugWorld2 i act))

/-- Mugging observation `O_T = {coin = T}`.
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mugObs : Unit → Finset MugW := fun _ => {.tPay, .tRefuse}

/-- Mugging action events `{choice = pay}`, `{choice = refuse}`.
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mugActEv : (d : Unit) → Act2 → Finset MugW
  | _, .a => {.tPay}
  | _, .b => {.tRefuse}

/-! ### Tree J -/

/-- Tree-J worlds: the recorded act.
Source: `sl-synthesis.md` line 121
Kind: D -/
abbrev JW : Type := Act2

/-- **Tree J**: `q₁: a → (act=a, 1); b → q₂: a → (act=b, 4), b → (act=b, 0)`, one point `d`
at both nodes, `O_d = ⊤`.
Source: `sl-workflow/notes/final/sl-synthesis.md` line 121 (C2-B′)
Kind: D -/
def treeJ : Tree JW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .a 1
    | .b => .decision () fun
      | .a => .leaf .b 4
      | .b => .leaf .b 0

/-- Tree-J observation `⊤` and action events `{act = a}`, `{act = b}`.
Source: `sl-synthesis.md` line 121
Kind: D -/
def jObs : Unit → Finset JW := fun _ => Finset.univ

/-- Tree-J action events `{act = a}`, `{act = b}` (the leaf-world is the first `d`-draw).
Source: `sl-synthesis.md` line 121 (C2-B′)
Kind: D -/
def jActEv : (d : Unit) → Act2 → Finset JW
  | _, .a => {.a}
  | _, .b => {.b}

/-! ### The routing root (Remark 3.4) -/

/-- Routing-root worlds: in `O` or out of `O`.
Source: [[decision-problems-v2]] Remark 3.4
Kind: D -/
inductive RouteW : Type
  | inO
  | outO
  deriving DecidableEq, Fintype

/-- **The routing root**: a root `d`-node whose `a`-edge alone leads into `O`-worlds.
Source: [[decision-problems-v2]] Remark 3.4 ("a root query whose `a`-edge alone leads into
`O`-worlds")
Kind: D -/
def routingRoot : Tree RouteW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .inO 0
    | .b => .leaf .outO 0

/-- Routing-root observation `O = {inO}`: the `a`-edge alone leads into `O`-worlds.
Source: [[decision-problems-v2]] Remark 3.4
Kind: D -/
def routeObs : Unit → Finset RouteW := fun _ => {.inO}

/-- Routing-root action events `a := {inO}`, `b := {outO}`.
Source: [[decision-problems-v2]] Remark 3.4
Kind: D -/
def routeActEv : (d : Unit) → Act2 → Finset RouteW
  | _, .a => {.inO}
  | _, .b => {.outO}

/-! ### Opaque Newcomb -/

/-- Opaque-Newcomb worlds: `(fill, act)` with `fill ∈ {0,1}` and `act ∈ {one, two}`
(`Act2.a` = one-box, `Act2.b` = two-box).
Source: `sl-synthesis.md` line 120 ("opaque Newcomb"); dp-sl-2-041
Kind: D -/
abbrev OpaqueW : Type := Bool × Act2

/-- Opaque-Newcomb payoff `L·fill + S·1[two]`.
Source: `sl-synthesis.md` line 120 (`L = 4, S = 1`)
Kind: D -/
def opaquePay (L S : ℚ) : OpaqueW → ℚ
  | (f, act) => (if f then L else 0) + (if act = .b then S else 0)

/-- The box's fill at chance index `i` given the sample `s`: index `0` = "prediction correct"
(filled iff `s` = one-box), index `1` = "prediction wrong".
Source: `sl-synthesis.md` line 120
Kind: D -/
def opaqueFill (s : Act2) (i : Fin 2) : Bool :=
  if i = 0 then decide (s = .a) else decide (s = .b)

/-- **Opaque Newcomb** with predictor reliability `p`: a predictor `d`-node upstream samples
`C(d)`, the box is filled according to the sample with probability `p` (index `0`) and
contrary to it with probability `1 − p` (index `1`), then the live `d`-node is queried;
`O_d = ⊤`.
Source: `sl-synthesis.md` line 120; dp-sl-2-041 ("predictor node upstream sampling `C(d)`")
Kind: D -/
def opaqueNewcomb (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    Tree OpaqueW Unit (fun _ => Act2) ℚ :=
  .decision () fun s =>
    .chance 2 (FinDistr.coin p h0 h1) fun i =>
      .decision () fun l => .leaf (opaqueFill s i, l) (opaquePay L S (opaqueFill s i, l))

/-- Opaque-Newcomb observation `⊤` (the agent sees nothing that distinguishes the simulation from the real query).
Source: `sl-synthesis.md` line 120; dp-sl-2-041
Kind: D -/
def opaqueObs : Unit → Finset OpaqueW := fun _ => Finset.univ

/-- Opaque-Newcomb action events: the world's act coordinate.
Source: `sl-synthesis.md` line 120; dp-sl-2-041
Kind: D -/
def opaqueActEv : (d : Unit) → Act2 → Finset OpaqueW
  | _, act => Finset.univ.filter fun w => w.2 = act

/-! ### The two-point out/in family: fantasy trees, FR-12, the threat tree -/

/-- Two points: `p1` (the out/in point, `O = ⊤`) and `p2` (the inner point, `O = {in}`).
Source: `fair-repair.md` line 107 ("Two points, `O₁ = ⊤`: out → 0; in → point `d₂`")
Kind: D -/
inductive Pt2 : Type
  | p1
  | p2
  deriving DecidableEq, Fintype

/-- Two-point worlds: `out`, `(in, x)`, `(in, y)`.
Source: `fair-repair.md` line 107
Kind: D -/
inductive TwoW : Type
  | out
  | inX
  | inY
  deriving DecidableEq, Fintype

/-- **The two-point out/in tree** `(r_out; r_x, r_y)`: at `p1`, `a` = out → `r_out`; `b` = in →
`p2`: `a` = x → `r_x`, `b` = y → `r_y`. Instances: fantasy `(2;4,1)`, `(5;4,1)`, `(0;4,1)`
(the §3.2 imperfect equilibrium), FR-12 `(0;0,−1)`, the threat tree `(1;2,0)`.
Source: `fair-repair.md` lines 107, 114 (FR-12); `adversary/calibration.md` lines 35–36
(fantasy `(2;4,1)`, `(5;4,1)`); `repair/identity.md` line 38 (the threat tree); mandate T13
Kind: D -/
def twoPoint (rOut rX rY : ℚ) : Tree TwoW Pt2 (fun _ => Act2) ℚ :=
  .decision .p1 fun
    | .a => .leaf .out rOut
    | .b => .decision .p2 fun
      | .a => .leaf .inX rX
      | .b => .leaf .inY rY

/-- Two-point observations: `O_{p1} = ⊤`, `O_{p2} = {act₁ = in}`.
Source: `fair-repair.md` line 107; `identity.md` line 38 (`O_{e₂} = {act₁ = b}`)
Kind: D -/
def twoObs : Pt2 → Finset TwoW
  | .p1 => Finset.univ
  | .p2 => {.inX, .inY}

/-- Two-point action events: `p1`: out / in; `p2`: x / y.
Source: `fair-repair.md` line 107
Kind: D -/
def twoActEv : (d : Pt2) → Act2 → Finset TwoW
  | .p1, .a => {.out}
  | .p1, .b => {.inX, .inY}
  | .p2, .a => {.inX}
  | .p2, .b => {.inY}

/-- Fantasy `(2;4,1)`. Source: `adversary/calibration.md` line 35. Kind: D -/
def fantasy241 : Tree TwoW Pt2 (fun _ => Act2) ℚ := twoPoint 2 4 1

/-- Fantasy `(5;4,1)`. Source: `adversary/calibration.md` line 36. Kind: D -/
def fantasy541 : Tree TwoW Pt2 (fun _ => Act2) ℚ := twoPoint 5 4 1

/-- The FR-12 tree `(0;0,−1)`. Source: `fair-repair.md` line 114. Kind: D -/
def fr12 : Tree TwoW Pt2 (fun _ => Act2) ℚ := twoPoint 0 0 (-1)

/-- The threat tree `(1;2,0)`: `e₁: a → 1, b → e₂: x → 2, y → 0`, `O_{e₂} = {act₁ = b}`.
Source: `repair/identity.md` line 38; mandate T13. Kind: D -/
def threat : Tree TwoW Pt2 (fun _ => Act2) ℚ := twoPoint 1 2 0

/-! ### The gate tree (T5's second separation) -/

/-- Gate-tree points: `e` (the gate) and `d`.
Source: mandate T5 ("a two-point tree where a point `e`'s answer decides whether `d` is met
twice")
Kind: D -/
inductive GatePt : Type
  | e
  | d
  deriving DecidableEq, Fintype

/-- **The gate tree**: at `e`, `a` → one `d`-node, `b` → two nested `d`-nodes; every leaf
records the last `d`-draw; `O_d = ⊤`.
Source: mandate T5
Kind: D -/
def gate : Tree Act2 GatePt (fun _ => Act2) ℚ :=
  .decision .e fun
    | .a => .decision .d fun x => .leaf x 0
    | .b => .decision .d fun _ => .decision .d fun y => .leaf y 0

/-- Gate-tree observations `⊤` at both points.
Source: mandate T5
Kind: D -/
def gateObs : GatePt → Finset Act2 := fun _ => Finset.univ

/-- Gate-tree action events: trivial at the gate `e`, `{x}` at `d` (the leaf records the last `d`-draw).
Source: mandate T5
Kind: D -/
def gateActEv : (_ : GatePt) → Act2 → Finset Act2
  | .e, _ => Finset.univ
  | .d, x => {x}

/-! ### Told-You-So Five-and-Ten (§7.1) -/

/-- `5` or `10`.
Source: [[decision-problems-v2]] §7.1
Kind: D -/
inductive Five10 : Type
  | five
  | ten
  deriving DecidableEq, Fintype

instance : Nonempty Five10 := ⟨Five10.five⟩

/-- Told-You-So worlds `(n, m)`: announced and taken.
Source: [[decision-problems-v2]] §7.1
Kind: D -/
abbrev TysW : Type := Five10 × Five10

/-- The numeric value of `5`/`10`. Source: [[decision-problems-v2]] §7.1. Kind: D -/
def Five10.val : Five10 → ℚ
  | .five => 5
  | .ten => 10

/-- **Told-You-So `B_P`**: root = query `d₅` (`five` = take 5 → `(5,5)`; `ten` → query `d₁₀`:
`ten` → `(10,10)`, `five` → `(10,5)`); payoff `r = m`.
Source: [[decision-problems-v2]] §7.1 (line 225)
Kind: D -/
def toldYouSo : Tree TysW Five10 (fun _ => Five10) ℚ :=
  .decision .five fun
    | .five => .leaf (.five, .five) 5
    | .ten => .decision .ten fun
      | .ten => .leaf (.ten, .ten) 10
      | .five => .leaf (.ten, .five) 5

/-- `O_{d_k} = {n = k}`. Source: [[decision-problems-v2]] §7.1. Kind: D -/
def tysObs (k : Five10) : Finset TysW := Finset.univ.filter fun w => w.1 = k

/-- `A_{d_k} = {{m = 5}, {m = 10}}`. Source: [[decision-problems-v2]] §7.1. Kind: D -/
def tysActEv (_ : Five10) (v : Five10) : Finset TysW := Finset.univ.filter fun w => w.2 = v

/-! ### Transparent Newcomb V1(p) / V2(p) (§7.2) -/

/-- Newcomb acts: `large` (one-box) or `both`.
Source: [[decision-problems-v2]] §7.2
Kind: D -/
inductive Box : Type
  | large
  | both
  deriving DecidableEq, Fintype

instance : Nonempty Box := ⟨Box.large⟩

/-- Newcomb points `d_F` (box seen full) and `d_E` (seen empty).
Source: [[decision-problems-v2]] §7.2
Kind: D -/
inductive TnPt : Type
  | F
  | E
  deriving DecidableEq, Fintype

/-- Newcomb worlds `(fill, act)`. Source: [[decision-problems-v2]] §7.2. Kind: D -/
abbrev TnW : Type := Bool × Box

/-- Newcomb payoff `r = fill·L + S·1[act = both]`. Source: [[decision-problems-v2]] §7.2. Kind: D -/
def tnPay (L S : ℚ) : TnW → ℚ
  | (f, act) => (if f then L else 0) + (if act = .both then S else 0)

/-- The real branch at chance index `i`: index `0` = full (query `d_F`, leaf `(1, act)`),
index `1` = empty (query `d_E`, leaf `(0, act)`).
Source: [[decision-problems-v2]] §7.2
Kind: D -/
def tnReal (L S : ℚ) (i : Fin 2) : Tree TnW TnPt (fun _ => Box) ℚ :=
  .decision (if i = 0 then .F else .E) fun act =>
    .leaf (decide (i = 0), act) (tnPay L S (decide (i = 0), act))

/-- **V1(p)**: query `d_F` hypothetically (answer `x`); chance sends the run to the full branch
(index `0`) with probability `p` if `x = large`, else `1 − p`; full branch queries `d_F`, empty
branch `d_E`.
Source: [[decision-problems-v2]] §7.2 (line 231)
Kind: D -/
def tnV1 (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) : Tree TnW TnPt (fun _ => Box) ℚ :=
  .decision .F fun x =>
    .chance 2 (FinDistr.coin (if x = .large then p else 1 - p)
      (by split_ifs <;> linarith) (by split_ifs <;> linarith)) (tnReal L S)

/-- **V2(p)**: query `d_F` then `d_E` hypothetically (answers `(x, y)`); full branch with
probability `p` if `(x, y) = (large, large)`, else `1 − p`; real branches as in V1.
Source: [[decision-problems-v2]] §7.2 (line 231)
Kind: D -/
def tnV2 (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) : Tree TnW TnPt (fun _ => Box) ℚ :=
  .decision .F fun x => .decision .E fun y =>
    .chance 2 (FinDistr.coin (if x = .large ∧ y = .large then p else 1 - p)
      (by split_ifs <;> linarith) (by split_ifs <;> linarith)) (tnReal L S)

/-- `O_F = {fill = 1}`, `O_E = {fill = 0}`. Source: [[decision-problems-v2]] §7.2. Kind: D -/
def tnObs : TnPt → Finset TnW
  | .F => Finset.univ.filter fun w => w.1 = true
  | .E => Finset.univ.filter fun w => w.1 = false

/-- Newcomb action events `{act = ·}`. Source: [[decision-problems-v2]] §7.2. Kind: D -/
def tnActEv (_ : TnPt) (act : Box) : Finset TnW := Finset.univ.filter fun w => w.2 = act

/-! ### The tickle tree (§7.3, Proposition 12) -/

/-- Tickle worlds `(ℓ, m, k)`: lesion, smoke, cancer.
Source: [[decision-problems-v2]] §7.3
Kind: D -/
abbrev TickleW : Type := Bool × Bool × Bool

/-- Tickle payoff `r = α·m − β·k`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def ticklePay (α β : ℚ) : TickleW → ℚ
  | (_, m, k) => (if m then α else 0) - (if k then β else 0)

/-- The cancer weight at lesion `ℓ`: `γ₁` if `ℓ`, else `γ₀`.
Source: [[decision-problems-v2]] §7.3 (S1) (`k ∼ Bern(γ_ℓ)`)
Kind: D -/
def tickleGamma (γ₁ γ₀ : ℚ) (ℓ : Bool) : ℚ := if ℓ then γ₁ else γ₀

/-- **The tickle tree** (Proposition 12's lesion-informative instantiation): `ℓ ∼ Bern(ρ)`
(chance index `0` = `ℓ = 1`); at lesion `ℓ` query `d_ℓ` (point `ℓ : Bool`, `O = {ℓ}`); acts
`m ∈ {1, 0}` (`true`/`false`); then `k ∼ Bern(γ_ℓ)` (index `0` = `k = 1`); leaves `(ℓ, m, k)`.
Both lesion branches have one shape, so every chance node's children are one lambda in the
index.
Source: [[decision-problems-v2]] §7.3, Proposition 12 (line 260); mandate T12
Kind: D -/
def tickle (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (γ₁ : ℚ) (g10 : 0 ≤ γ₁) (g11 : γ₁ ≤ 1)
    (γ₀ : ℚ) (g00 : 0 ≤ γ₀) (g01 : γ₀ ≤ 1) (α β : ℚ) : Tree TickleW Bool (fun _ => Bool) ℚ :=
  .chance 2 (FinDistr.coin ρ r0 r1) fun i =>
    .decision (decide (i = 0)) fun m =>
      .chance 2 (FinDistr.coin (tickleGamma γ₁ γ₀ (decide (i = 0)))
          (by unfold tickleGamma; split_ifs <;> assumption)
          (by unfold tickleGamma; split_ifs <;> assumption)) fun j =>
        .leaf (decide (i = 0), m, decide (j = 0))
          (ticklePay α β (decide (i = 0), m, decide (j = 0)))

/-- `O_{d_ℓ} = {ℓ}`. Source: [[decision-problems-v2]] §7.3 Proposition 12. Kind: D -/
def tickleObs (ℓ : Bool) : Finset TickleW := Finset.univ.filter fun w => w.1 = ℓ

/-- Tickle action events `{m = ·}`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def tickleActEv (_ : Bool) (m : Bool) : Finset TickleW := Finset.univ.filter fun w => w.2.1 = m

/-! ### The selection-forcing tree -/

/-- Selection-forcing worlds `(o = 1, act, real/fake)`.
Source: `cf-workflow/phase2-notes/repair/calibration.md` line 23
Kind: D -/
inductive SelW : Type
  | realA
  | realB
  | fakeA
  | fakeB
  deriving DecidableEq, Fintype

/-- **`S_sel(u_a, u_b; r_a, r_b)`**: chance root with three equiprobable branches — a real
`d`-node (`a → realA`, payoff `u_a`; `b → realB`, `u_b`), a fake-`a` leaf (`r_a`), a fake-`b`
leaf (`r_b`); `O_d = ⊤`.
Source: `calibration.md` line 23; mandate T13
Kind: D -/
def selectionForcing (ua ub ra rb : ℚ) : Tree SelW Unit (fun _ => Act2) ℚ :=
  .chance 3 FinDistr.third
    ![.decision () fun | .a => .leaf .realA ua | .b => .leaf .realB ub,
      .leaf .fakeA ra,
      .leaf .fakeB rb]

/-- Selection-forcing observation `⊤`.
Source: `calibration.md` line 23; mandate T13
Kind: D -/
def selObs : Unit → Finset SelW := fun _ => Finset.univ

/-- Selection-forcing action events: `a := {realA, fakeA}`, `b := {realB, fakeB}` (the fake leaves count as the act).
Source: `calibration.md` line 23; mandate T13
Kind: D -/
def selActEv : (_ : Unit) → Act2 → Finset SelW
  | _, .a => {.realA, .fakeA}
  | _, .b => {.realB, .fakeB}

/-! ### The coin-then-query tree (a non-degenerate pre-query event) -/

/-- Coin-then-query worlds `(coin, act)`.
Source: mandate T6 (the N+ for Lemma 3′ needs a pre-query chance event that is neither `∅` nor
`O_d` on the `O_d`-runs)
Kind: D -/
abbrev CoinQueryW : Type := Bool × Act2

/-- **The coin-then-query tree**: a fair coin `c` (index `0` = `c = 1`), then one `d`-node
(`O_d = ⊤`) whose `a`-edge leads to `(c, a)` and `b`-edge to `(c, b)`; payoffs `0`. Recorded at
`d` for every procedure; `{c = 1}` is a pre-query event with `ν({c = 1} ∩ O_d) = ½`.
Source: mandate T6 (witness design); none in the corpus
Kind: D -/
def coinQuery : Tree CoinQueryW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision () fun act => .leaf (decide (i = 0), act) 0

/-- Coin-then-query observation `O_d = ⊤`.
Source: mandate T6 (witness design); none in the corpus
Kind: D -/
def cqObs : Unit → Finset CoinQueryW := fun _ => Finset.univ

/-- Coin-then-query action events `{act = ·}` (the leaf records the draw).
Source: mandate T6 (witness design); none in the corpus
Kind: D -/
def cqActEv (_ : Unit) (act : Act2) : Finset CoinQueryW := Finset.univ.filter fun w => w.2 = act

/-- The pre-query event `{c = 1}`. Source: mandate T6. Kind: D -/
def cqCoin : Finset CoinQueryW := Finset.univ.filter fun w => w.1 = true

end Catalogue

end Cleanroom.Found.DpCoreTree
