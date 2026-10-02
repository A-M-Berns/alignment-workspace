import Cleanroom.Bli.UdtBliSist.Inert
import Cleanroom.Bli.UdtBliCore.Mugging
import Mathlib.Data.Fintype.Option

/-!
# `udt-bli-sist` · Iterated: `K` nodes, each a mugging — SIST at every node (T6 a)

bli-soto-b-2-012 (i), finite horizon: **`K` muggings**, node `k` with its own coin sentence
`node_k` and its own tables `Ask_k` (coin `1`, `node_k` `1`), `Rec_k` (coin `0`, `node_k` `1`),
plus the residual `Other`; masses `w` on the `2K + 1` states; independent uniform points; the
utility at node `k` reads the policy at `Ask_k` (`−c·[give]` at `Ask_k`, `V·[give]` at `Rec_k`),
the residual reads its own table. **At every `Ask_k`** the class `𝒞_k = {Ask_k, Rec_k}` is inert
at `Ask_k` (`classInert_node`, derived: the other nodes' tables read their own `Ask_j`, `j ≠ k`)
and the verdict is the per-node class-cut `EU Ask_k give − EU Ask_k refuse = w(Rec_k)·V −
w(Ask_k)·c` (`verdict`), so one-step UDT pays at every node whenever `c·w(Ask_k) < V·w(Rec_k)`
(`isOneStepChoice_pay_all`; the uniform instance `instance_uniform`). The N− is the singleton
class at every node (`not_classInert_single`).

**What this object is and is not** (finding F17). The `K` nodes are *parallel*: each world is at
one node, with that node's payoff; "utilities additive over nodes" holds in the sense that the
prior mixes the `K` muggings and each node's verdict is computed in its own class. It is not the
*sequential* tree in which one play visits all `K` nodes and the world's utility sums all `K`
payoffs: there, every table on a play through `Ask_k` carries the node-`k` term `pp·Ask_k`, so
`{Ask_k, Rec_k}` is **not** inert and the mandate's recipe does not apply as written (the verdict
still holds by the partition cut over the coin coordinate; see the findings).

Sources: bli-soto-b-2-012 (i); mandate T6(a); audit round 1 A2/B1.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore LogicalInduction LO.Propositional Finset

namespace Iter

variable (K : ℕ)

/-- The coin sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev coinS : Sentence := Formula.atom 0

/-- The node sentences `node_k := atom (k + 1)`.
Source: bli-soto-b-2-012 (i) ("every node is a counterfactual mugging")
Kind: D
Fidelity: n/a -/
def nodeS (k : Fin K) : Sentence := Formula.atom (k.val + 1)

/-- `nodeS` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nodeS_injective : Function.Injective (nodeS K) := by
  intro k k' h
  unfold nodeS at h
  exact Fin.ext (Nat.succ_injective (Formula.atom.inj h))

/-- A node sentence is not the coin.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nodeS_ne_coinS (k : Fin K) : nodeS K k ≠ coinS := by
  intro h
  unfold nodeS coinS at h
  have := Formula.atom.inj h
  omega

/-- The sentences: the coin and the `K` node sentences.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def iterDay : Finset Sentence := {coinS} ∪ univ.image (nodeS K)

/-- **The index**: the same sentences every day.
Source: mandate T6(a)
Kind: D
Fidelity: exact -/
def iterIndex : SmallIndex where
  S := fun _ => iterDay K
  mono := fun _ => Finset.Subset.refl _

/-- The coin is small.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coinS_mem : coinS ∈ (iterIndex K).S 1 := by simp [iterIndex, iterDay]

/-- Every node sentence is small.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nodeS_mem (k : Fin K) : nodeS K k ∈ (iterIndex K).S 1 := by
  simp only [iterIndex, iterDay, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨k, Finset.mem_univ _, rfl⟩

/-- The coin as a small sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev coin1 : ↥((iterIndex K).S 1) := ⟨coinS, coinS_mem K⟩

/-- A node sentence as a small sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev node1 (k : Fin K) : ↥((iterIndex K).S 1) := ⟨nodeS K k, nodeS_mem K k⟩

/-- The state indices: `some (true, k)` = `Ask_k`, `some (false, k)` = `Rec_k`, `none` = `Other`.
Source: mandate T6(a)
Kind: D
Fidelity: n/a -/
abbrev Idx : Type := Option (Bool × Fin K)

/-- **The tables**: `Ask_k` prices the coin `1` and `node_k` `1`; `Rec_k` the coin `0` and
`node_k` `1`; `Other` everything `0`.
Source: bli-soto-b-2-012 (i); mandate T6(a) ("node `k`'s `Ask_k`/`Rec_k` with its own coin")
Kind: D
Fidelity: exact -/
def iterTable : Idx K → Table (iterIndex K) 1
  | none => fun _ => 0
  | some (b, k) => fun φ => if φ.1 = coinS then (if b then 1 else 0)
      else if φ.1 = nodeS K k then 1 else 0

/-- `iterTable (some (b, k))` at the coin.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma iterTable_some_coin (b : Bool) (k : Fin K) :
    iterTable K (some (b, k)) (coin1 K) = if b then 1 else 0 := by simp [iterTable]

/-- `iterTable (some (b, k))` at a node sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma iterTable_some_node (b : Bool) (k k' : Fin K) :
    iterTable K (some (b, k)) (node1 K k') = if k' = k then 1 else 0 := by
  have hc := nodeS_ne_coinS K k'
  by_cases h : k' = k
  · subst h; simp [iterTable, hc]
  · have hne : nodeS K k' ≠ nodeS K k := fun e => h (nodeS_injective K e)
    simp [iterTable, hc, hne, h]

/-- `iterTable none = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma iterTable_none (φ : ↥((iterIndex K).S 1)) : iterTable K none φ = 0 := rfl

/-- The tables are `0/1`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma iterTable_zeroOne (s : Idx K) (φ : ↥((iterIndex K).S 1)) :
    iterTable K s φ = 0 ∨ iterTable K s φ = 1 := by
  rcases s with _ | ⟨b, k⟩
  · exact Or.inl rfl
  · simp only [iterTable]
    split_ifs <;> simp

/-- `iterTable` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma iterTable_injective : Function.Injective (iterTable K) := by
  intro s s' h
  rcases s with _ | ⟨b, k⟩ <;> rcases s' with _ | ⟨b', k'⟩
  · rfl
  · have := congrFun h (node1 K k'); simp at this
  · have := congrFun h (node1 K k); simp at this
  · have hc := congrFun h (coin1 K)
    have hd := congrFun h (node1 K k)
    simp only [iterTable_some_coin, iterTable_some_node, if_true] at hc hd
    have hb : b = b' := by cases b <;> cases b' <;> simp at hc <;> rfl
    have hkk : k = k' := by
      by_contra hne
      rw [if_neg hne] at hd
      norm_num at hd
    rw [hb, hkk]

/-- **The carrier**: the `2K + 1` tables.
Source: mandate T6(a)
Kind: D
Fidelity: exact -/
def iterTables : Finset (Table (iterIndex K) 1) := univ.image (iterTable K)

/-- The state of an index.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def st (s : Idx K) : ↥(iterTables K) :=
  ⟨iterTable K s, Finset.mem_image_of_mem _ (Finset.mem_univ s)⟩

/-- `st` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma st_injective : Function.Injective (st K) := fun _ _ h =>
  iterTable_injective K (congrArg Subtype.val h)

/-- Every carrier table is some `st s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma st_surjective : Function.Surjective (st K) := by
  intro T
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp T.2
  exact ⟨s, Subtype.ext hs⟩

/-- All carrier tables are `0/1`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma iterTables_zeroOne : ∀ (T : ↥(iterTables K)) (φ : ↥((iterIndex K).S 1)),
    T.1 φ = 0 ∨ T.1 φ = 1 := by
  intro T φ
  obtain ⟨s, rfl⟩ := st_surjective K T
  exact iterTable_zeroOne K s φ

/-! ## The prior -/

/-- `Ask_k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev askT (k : Fin K) : ↥(iterTables K) := st K (some (true, k))

/-- `Rec_k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev recT (k : Fin K) : ↥(iterTables K) := st K (some (false, k))

/-- `Other`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev otherT : ↥(iterTables K) := st K none

/-- **The node class** `𝒞_k = {Ask_k, Rec_k}`.
Source: mandate T6(a)
Kind: D
Fidelity: exact -/
def nodeClass (k : Fin K) : Finset ↥(iterTables K) := {askT K k, recT K k}

/-- The reference table: node `k`'s states read `Ask_k`; the residual reads its own table.
Source: mandate T6(a) (each node a mugging with its own point)
Kind: D
Fidelity: exact (the residual reads `Other`, not the observed table, so that it is inert at
every node — a disclosed difference from `udt-bli-core`'s F-13) -/
def iterRef : Idx K → ↥(iterTables K)
  | none => st K none
  | some (_, k) => st K (some (true, k))

/-- The payoff: `−c·[give]` at `Ask_k`, `V·[give]` at `Rec_k`, `r₀` at `Other`.
Source: bli-soto-b-2-012 (i); mandate T6(a)
Kind: D
Fidelity: exact -/
def iterPay (c V : ℚ) (r₀ : Bool → ℚ) : Idx K → Bool → ℚ
  | none => r₀
  | some (true, _) => fun b => -c * ind b
  | some (false, _) => fun b => V * ind b

/-- The uniform point weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def half : ↥(iterTables K) → Bool → ℚ := fun _ _ => 1 / 2

/-- `half` sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma half_sum : ∀ T, ∑ a, half K T a = 1 := by intro T; simp [half]

variable (w : Idx K → ℚ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (c V : ℚ) (r₀ : Bool → ℚ)

/-- **The `K`-node data**: base the state indices with masses `w`, `0/1` faith, independent
uniform points, the payoff read at `iterRef`.
Source: bli-soto-b-2-012 (i); mandate T6(a)
Kind: D
Fidelity: exact (finite; parallel nodes — see the module docstring) -/
def iterData : IndepData (iterIndex K) 1 (iterTables K) Bool where
  Ω₀ := Idx K
  μ₀ := w
  μ₀_nonneg := hw
  μ₀_sum_one := hw1
  state₀ := st K
  small₀ := fun s φ => decide ((st K s).1 φ = 1)
  faith₀ := faith_of_zeroOne _ _ (iterTables_zeroOne K)
  ν := prodLaw (half K)
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [half])
  ν_sum_one := sum_prodLaw (half_sum K)
  U₀ := fun s π => iterPay K c V r₀ s (π (iterRef K s))

/-- **The `K`-node prior.**
Source: bli-soto-b-2-012 (i); mandate T6(a)
Kind: D
Fidelity: exact -/
def iterPrior : FiniteBLIPrior (iterIndex K) 1 (iterTables K) Bool := (iterData K w hw hw1 c V r₀).toPrior

/-- The state coordinate of the data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma state₀_eq (s : Idx K) : (iterData K w hw hw1 c V r₀).state₀ s = st K s := rfl

/-- Decidable equality of the base (it is `Idx K`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecEqBase : DecidableEq (iterData K w hw hw1 c V r₀).Ω₀ :=
  inferInstanceAs (DecidableEq (Idx K))

/-- The points are independent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma indep : (iterData K w hw hw1 c V r₀).toPrior.IndependentPoints :=
  (iterData K w hw hw1 c V r₀).independentPoints_toPrior_of_prodLaw (half K) (half_sum K) rfl

/-- Every point has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_point (T : ↥(iterTables K)) (a : Bool) :
    massOf (iterData K w hw hw1 c V r₀).ν (fun π => π T = a) = 1 / 2 := by
  change massOf (prodLaw (half K)) (fun π => π T = a) = 1 / 2
  rw [IndepData.massOf_prodLaw_point (half K) (half_sum K)]
  rfl

/-- The utility has the reference shape.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma shaped : ∀ s π, (iterData K w hw hw1 c V r₀).U₀ s π = iterPay K c V r₀ s (π (iterRef K s)) :=
  fun _ _ => rfl

/-- A state outside the node class reads a table other than `Ask_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ref_ne_of_not_mem (k : Fin K) (s : Idx K) (hs : s ∉ ({some (true, k), some (false, k)} : Finset (Idx K))) :
    iterRef K s ≠ askT K k := by
  rcases s with _ | ⟨b, j⟩
  · show st K none ≠ st K (some (true, k))
    intro h
    exact Option.some_ne_none _ (st_injective K h).symm
  · show st K (some (true, j)) ≠ st K (some (true, k))
    intro h
    have hj : j = k := by simpa using st_injective K h
    subst hj
    apply hs
    cases b <;> simp

/-- **The per-node inertness**: at every `Ask_k`, the other nodes' tables and the residual are
inert — `ClassInert 𝒞_k Ask_k` derived from the construction by `classInert_of_ref`.
Source: bli-soto-b-2-012 (i); mandate T6(a) ("inertness of the other nodes' tables")
Kind: N+ (the hypothesis of the per-node class lemma inhabited at every node)
Fidelity: exact
Hyps: (a) none -/
theorem classInert_node (k : Fin K) :
    ClassInert (iterPrior K w hw hw1 c V r₀) (nodeClass K k) (askT K k) := by
  unfold iterPrior
  apply classInert_of_ref _ (indep K w hw hw1 c V r₀) (iterRef K) (iterPay K c V r₀)
    (shaped K w hw hw1 c V r₀)
  show ∀ s : Idx K, st K s ∉ nodeClass K k → iterRef K s ≠ askT K k
  intro s hs
  apply ref_ne_of_not_mem K k s
  intro hmem
  apply hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl <;> simp [nodeClass]

/-- The node's two states read `Ask_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma iterRef_eq (k : Fin K) :
    ∀ s ∈ ({some (true, k), some (false, k)} : Finset (Idx K)), iterRef K s = askT K k := by
  intro s hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl <;> rfl

/-- **The verdict at every node**: `EU Ask_k give − EU Ask_k refuse = w(Rec_k)·V − w(Ask_k)·c`,
by the per-node class lemma with `𝒞_k = {Ask_k, Rec_k}`.
Source: bli-soto-b-2-012 (i) ("SIST applies at every node"); mandate T6(a)
Kind: C (`classCut_ref_injective` at `S = {Ask_k, Rec_k}`)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem verdict (k : Fin K) :
    (iterPrior K w hw hw1 c V r₀).EU (askT K k) true - (iterPrior K w hw hw1 c V r₀).EU (askT K k) false =
      w (some (false, k)) * V - w (some (true, k)) * c := by
  unfold iterPrior
  rw [classCut_ref_injective (iterData K w hw hw1 c V r₀) (st_injective K)
    (indep K w hw hw1 c V r₀) (iterRef K) (iterPay K c V r₀) (shaped K w hw hw1 c V r₀)
    ({some (true, k), some (false, k)} : Finset (Idx K)) (askT K k) (iterRef_eq K k)
    (ref_ne_of_not_mem K k)
    true false (by rw [massOf_point]; norm_num) (by rw [massOf_point]; norm_num)]
  show ∑ s ∈ ({some (true, k), some (false, k)} : Finset (Idx K)),
      w s * (iterPay K c V r₀ s true - iterPay K c V r₀ s false) =
    w (some (false, k)) * V - w (some (true, k)) * c
  rw [Finset.sum_pair (by simp : (some (true, k) : Idx K) ≠ some (false, k))]
  simp only [iterPay, ind_true, ind_false]
  ring

/-- **One-step UDT pays at every node** whenever `c·w(Ask_k) < V·w(Rec_k)` at every `k` — SIST
"does not sputter out" over the `K` nodes.
Source: bli-soto-b-2-012 (i) ("one-step UDT does not sputter out into oblivion"); mandate T6(a)
("at every `Ask_k`, `IsOneStepChoice Ask_k give`")
Kind: C
Fidelity: exact (finite horizon, parallel nodes)
Hyps: (a) the per-node inequality; does not use faith -/
theorem isOneStepChoice_pay_all (h : ∀ k, c * w (some (true, k)) < V * w (some (false, k))) :
    ∀ k, (iterPrior K w hw hw1 c V r₀).IsOneStepChoice (askT K k) true ∧
      (iterPrior K w hw hw1 c V r₀).EU (askT K k) false <
        (iterPrior K w hw hw1 c V r₀).EU (askT K k) true := by
  intro k
  have hd := verdict K w hw hw1 c V r₀ k
  have hk := h k
  refine ⟨fun b => ?_, by linarith⟩
  cases b
  · linarith
  · exact le_rfl

/-- **The N− at every node**: the singleton class `{Ask_k}` is not inert (`Rec_k`'s value moves
with the action at `Ask_k`) when `Rec_k` has mass and `V ≠ 0`.
Source: mandate T6(a) (the class is `{Ask_k, Rec_k}`, not `{Ask_k}`); [[bli-program]] §7 item 9
Kind: N−
Fidelity: exact
Hyps: (a) `0 < w (Rec_k)`, `V ≠ 0` -/
theorem not_classInert_single (k : Fin K) (hk : 0 < w (some (false, k))) (hV : V ≠ 0) :
    ¬ ClassInert (iterPrior K w hw hw1 c V r₀) {askT K k} (askT K k) := by
  intro h
  have hmem : recT K k ∉ ({askT K k} : Finset ↥(iterTables K)) := by
    simp only [Finset.mem_singleton, askT, recT, (st_injective K).eq_iff]
    simp
  have hpos : ∀ a, 0 < (iterPrior K w hw hw1 c V r₀).jointMass (recT K k) (askT K k) a := by
    intro a
    unfold iterPrior
    rw [jointMass_toPrior_of_injective (iterData K w hw hw1 c V r₀) (st_injective K)
      (some (false, k) : Idx K) (recT K k) rfl, massOf_point]
    exact mul_pos hk (by norm_num)
  have := h (recT K k) hmem true false (hpos true) (hpos false)
  unfold iterPrior at this
  rw [condEU_ref_of_eq_single (iterData K w hw hw1 c V r₀) (st_injective K) (iterRef K)
      (iterPay K c V r₀) (shaped K w hw hw1 c V r₀) (some (false, k) : Idx K) (recT K k) rfl
      (askT K k) rfl true (by rw [massOf_point]; norm_num) (ne_of_gt hk),
    condEU_ref_of_eq_single (iterData K w hw hw1 c V r₀) (st_injective K) (iterRef K)
      (iterPay K c V r₀) (shaped K w hw hw1 c V r₀) (some (false, k) : Idx K) (recT K k) rfl
      (askT K k) rfl false (by rw [massOf_point]; norm_num) (ne_of_gt hk)] at this
  simp only [iterPay, ind_true, ind_false, mul_one, mul_zero] at this
  exact hV this

/-! ## The uniform instance -/

/-- The masses: `ε` on every node table, `1 − 2Kε` on the residual.
Source: mandate T6(a)
Kind: D
Fidelity: exact -/
def wIter (ε : ℚ) : Idx K → ℚ
  | none => 1 - 2 * K * ε
  | some _ => ε

/-- `wIter ≥ 0` for `0 ≤ ε` and `2Kε ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wIter_nonneg {ε : ℚ} (hε : 0 ≤ ε) (hK : 2 * K * ε ≤ 1) : ∀ s, 0 ≤ wIter K ε s := by
  intro s
  rcases s with _ | s
  · simp only [wIter]; linarith
  · exact hε

/-- `∑ wIter = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wIter_sum (ε : ℚ) : ∑ s, wIter K ε s = 1 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [wIter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool]
  ring

/-- **The uniform instance pays at every node**: `0 < ε`, `2Kε ≤ 1`, `c < V`.
Source: bli-soto-b-2-012 (i); mandate T6(a)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < ε`, `2Kε ≤ 1`, `c < V` -/
theorem instance_uniform {ε : ℚ} (hε : 0 < ε) (hK : 2 * K * ε ≤ 1) (hcV : c < V) :
    ∀ k, (iterPrior K (wIter K ε) (wIter_nonneg K (le_of_lt hε) hK) (wIter_sum K ε) c V r₀).IsOneStepChoice
        (askT K k) true ∧
      (iterPrior K (wIter K ε) (wIter_nonneg K (le_of_lt hε) hK) (wIter_sum K ε) c V r₀).EU (askT K k) false <
        (iterPrior K (wIter K ε) (wIter_nonneg K (le_of_lt hε) hK) (wIter_sum K ε) c V r₀).EU (askT K k) true :=
  isOneStepChoice_pay_all K _ _ _ c V r₀ (fun k => by
    simp only [wIter]
    exact mul_lt_mul_of_pos_right hcV hε)

end Iter

end Cleanroom.Bli.UdtBliSist
