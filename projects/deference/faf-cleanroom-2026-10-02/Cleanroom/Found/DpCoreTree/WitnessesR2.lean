import Cleanroom.Found.DpCoreTree.WitnessesR1
import Cleanroom.Found.DpCoreTree.Multilinear

/-!
# Witnesses added in repair round 2

* **`H*` with an informative observation** (adversarial audit r2 B1; round 1's A.8). The
  package's first inhabitant of `H*`, `coinQuery_hStar`, has `O_d = ⊤`, where `H*`'s second
  clause — every positive run through a `d`-node is an `O_d`-run — is automatic
  (`coinQuery_hStar_iff`: on that tree `H*` is `RecordsFor` and nothing more). The **routed
  coin-then-query tree** `routedCoinQuery` (adopted from the auditor's probe
  `audit-r2-probes/HStarWitness.lean`, renamed) repairs this: at the root a point `e` routes;
  its `a`-edge leads to a fair coin `c` and then a `d`-node whose leaves record `(o = 1, c, act)`;
  its `b`-edge leads to the leaf `(o = 0, c = 0, a)` with no `d`-node. `O_d = {o = 1}` is
  informative, `occ(d)` is the `e = a` half of the run space (`routedCoinQuery_occ_ne_univ`,
  `routedCoinQuery_ssc_values`: `μ(occ) = ½`), and `H*` holds at `d` for **every** procedure
  with both clauses doing work (`routedCoinQuery_hStar`): the second clause holds because the
  `e = b` leaf meets no `d`-node, not because `O_d = ⊤`. `{c = 1}` is pre-query
  (`routedCoinQuery_preQuery_coin`) and `X ∩ O_d ∉ {∅, O_d}`. With `C(e)(a) = ½`,
  `C(d) = (q, 1−q)`: `ν(O) = ½`, `ν(X ∩ O) = ¼`, `ν(a ∩ O) = q/2`, `ν(X ∩ a ∩ O) = q/4`
  (`routedCoinQuery_nu_values`), so Lemma 3′ reads `q/4 · ½ = ¼ · q/2`
  (`routedCoinQuery_screening_instance`) and the SSC form under `H*` reads the same on `occ(d)`
  (`routedCoinQuery_ssc_instance`, `routedCoinQuery_ssc_values`).
* **T11's nesting N−** (mandate stretch): on the AMD, where the leaf `(b, a)` meets `d` twice
  (`amd_count_sba`), the disposition identity of `disposition_faithful` **fails** at
  `C(d) = ½` with `S = drew_b` (the runs that drew `b` at `d`), `a`: `¼ · 1 ≠ 0 · ¾`
  (`amd_disposition_fails`, `amd_disposition_values`). The hypothesis `#_d ≤ 1` is therefore necessary, not an artefact
  of the proof.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Catalogue Tree

/-! ### The degenerate `H*` instance, disclosed -/

/-- With `O_d = ⊤`, `H*`'s second clause ("every positive run through a `d`-node is an
`O_d`-run") is automatic, so on the coin-then-query tree `H*` is exactly `RecordsFor`:
`coinQuery_hStar` inhabits `H*` without exercising the clause that separates it from recording.
Source: adversarial audit r2 B1 (probe `audit-r2-probes/Content.lean`, `coinQuery_hStar_iff`)
Kind: L -/
theorem coinQuery_hStar_iff (C : Proc Unit (fun _ => Act2) ℚ) :
    HStar cqObs cqActEv C coinQuery () ↔ RecordsFor cqObs cqActEv C coinQuery () :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ => by simp [cqObs]⟩⟩

/-! ### The routed coin-then-query tree -/

/-- Worlds of the routed coin-then-query tree, `(o, c, act)`: whether `d` was really faced, the
coin, the recorded act.
Source: adversarial audit r2 B1 (witness design; none in the corpus)
Kind: D -/
abbrev RcqW : Type := Bool × Bool × Act2

/-- **The routed coin-then-query tree**: at the root the point `e` routes; `e = a` leads to a
fair coin `c` (index `0` = `c = 1`) and then one `d`-node whose leaves record `(o = 1, c, act)`;
`e = b` leads to the leaf `(o = 0, c = 0, a)` with no `d`-node. Payoffs `0`. `O_d = {o = 1}`
holds exactly on the runs that meet `d`, so `H*` holds at `d` for every procedure with its
second clause a real constraint (`routedCoinQuery_hStar`).
Source: adversarial audit r2 B1 (witness design; the coin-then-query tree of mandate T6 behind
a routing root, cf. [[decision-problems-v2]] Remark 3.4); none in the corpus
Kind: D -/
def routedCoinQuery : Tree RcqW GatePt (fun _ => Act2) ℚ :=
  .decision .e fun
    | .a => .chance 2 FinDistr.fair fun i =>
        .decision .d fun act => .leaf (true, decide (i = 0), act) 0
    | .b => .leaf (false, false, .a) 0

/-- Observations of the routed tree: `O_e = ⊤`, `O_d = {o = 1}`.
Source: adversarial audit r2 B1 (witness design); none in the corpus
Kind: D -/
def rcqObs : GatePt → Finset RcqW
  | .e => Finset.univ
  | .d => Finset.univ.filter fun w => w.1 = true

/-- Action events of the routed tree: trivial at `e`, `{act = ·}` at `d`.
Source: adversarial audit r2 B1 (witness design); none in the corpus
Kind: D -/
def rcqActEv : (_ : GatePt) → Act2 → Finset RcqW
  | .e, _ => Finset.univ
  | .d, x => Finset.univ.filter fun w => w.2.2 = x

/-- The pre-query event `{c = 1}` on the routed tree.
Source: adversarial audit r2 B1 (witness design); mandate T6
Kind: D -/
def rcqCoin : Finset RcqW := Finset.univ.filter fun w => w.2.1 = true

/-- The procedure `C(e)(a) = ½`, `C(d)(a) = q` on the routed tree.
Source: adversarial audit r2 B1 (witness design)
Kind: D -/
def rcqProc (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc GatePt (fun _ => Act2) ℚ :=
  gateProc (1/2) (by norm_num) (by norm_num) q h0 h1

/-- The routed tree is Definition-7 recorded at `d` for every procedure.
Source: [[decision-problems-v2]] Definition 7; adversarial audit r2 B1
Kind: N+ -/
theorem routedCoinQuery_recordsFor (C : Proc GatePt (fun _ => Act2) ℚ) :
    RecordsFor rcqObs rcqActEv C routedCoinQuery .d := by
  unfold routedCoinQuery
  intro ℓ _ hobs
  rcases ℓ with ⟨_ | _, ℓ⟩
  · rcases ℓ with ⟨i, act, _⟩
    refine ⟨rfl, ?_⟩
    rintro (_ | ⟨_ | _, q⟩) hq x hx
    · simp at hq
    · rcases q with ⟨i', (_ | ⟨y, q'⟩)⟩
      · by_cases hi : i = i'
        · subst hi
          simp only [edgeOf_decision_some, edgeOf_chance, dite_true, edgeOf_decision_none,
            Option.some.injEq] at hx
          subst hx
          refine ⟨?_, ?_, ?_⟩
          · rintro ⟨_ | _, ℓ'⟩ hℓ'
            · rcases ℓ' with ⟨j, act', _⟩; simp [rcqObs]
            · simp [edgeOf_decision_some] at hℓ'
          · simp [rcqActEv]
          · intro a' ha'
            simp [rcqActEv] at ha'
            exact ha'.symm
        · simp [edgeOf_decision_some, edgeOf_chance, hi] at hx
      · exact q'.elim
    · exact q.elim
  · exfalso
    simp [rcqObs] at hobs

/-- **`H*` at `d` for every procedure, with an informative `O_d`**: recorded, and every positive
run through a `d`-node has `o = 1`. The second clause is not automatic here: the `e = b` leaf
has positive mass under any procedure with `C(e)(b) > 0` and lies outside `O_d` — it meets no
`d`-node, which is what the clause demands. Contrast `coinQuery_hStar` (`O_d = ⊤`,
`coinQuery_hStar_iff`).
Source: `sl-synthesis.md` line 20 (`H*`); adversarial audit r2 B1
Kind: N+ -/
theorem routedCoinQuery_hStar (C : Proc GatePt (fun _ => Act2) ℚ) :
    HStar rcqObs rcqActEv C routedCoinQuery .d := by
  refine ⟨routedCoinQuery_recordsFor C, ?_⟩
  intro ℓ _ hc
  unfold routedCoinQuery at ℓ hc ⊢
  rcases ℓ with ⟨_ | _, ℓ⟩
  · rcases ℓ with ⟨i, act, _⟩; simp [rcqObs]
  · simp at hc

/-- `occ(d)` is not the whole run space: the `e = b` leaf has mass `½` under `rcqProc` and meets
no `d`-node. So `H*`'s second clause is a real constraint on this tree.
Source: adversarial audit r2 B1
Kind: N+ -/
theorem routedCoinQuery_occ_ne_univ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∃ ℓ : routedCoinQuery.Leaves,
      0 < leafLaw (rcqProc q h0 h1) routedCoinQuery ℓ ∧ count .d routedCoinQuery ℓ = 0 := by
  refine ⟨⟨.b, ()⟩, ?_, ?_⟩
  · unfold routedCoinQuery
    simp [rcqProc, gateProc]
    norm_num
  · unfold routedCoinQuery
    simp

/-- `{c = 1}` is pre-query for `d` on the routed tree under every procedure.
Source: `sl-defensible-claims.md` S4 (pre-query events); adversarial audit r2 B1
Kind: N+ -/
theorem routedCoinQuery_preQuery_coin (C : Proc GatePt (fun _ => Act2) ℚ) :
    PreQuery rcqObs C routedCoinQuery .d rcqCoin := by
  intro ℓ _ _ q hq he
  unfold routedCoinQuery at ℓ q hq he ⊢
  rcases q with (_ | ⟨_ | _, q⟩)
  · simp at hq
  · rcases q with ⟨i', (_ | ⟨y, q'⟩)⟩
    · by_cases hi : i' = 0
      · left
        rintro ⟨_ | _, ℓ'⟩ hℓ'
        · rcases ℓ' with ⟨j, act', _⟩
          rw [mem_leavesBelow] at hℓ'
          by_cases hji : j = i'
          · subst hji; simp [rcqCoin, hi]
          · simp [edgeOf_decision_some, edgeOf_chance, hji] at hℓ'
        · simp [edgeOf_decision_some] at hℓ'
      · right
        rintro ⟨_ | _, ℓ'⟩ hℓ'
        · rcases ℓ' with ⟨j, act', _⟩
          rw [mem_leavesBelow] at hℓ'
          by_cases hji : j = i'
          · subst hji; simp [rcqCoin, hi]
          · simp [edgeOf_decision_some, edgeOf_chance, hji] at hℓ'
        · simp [edgeOf_decision_some] at hℓ'
    · exact q'.elim
  · exact q.elim

/-- `ν` on the routed tree as an explicit sum.
Source: none: infrastructure
Kind: L -/
theorem routedCoinQuery_nu (C : Proc GatePt (fun _ => Act2) ℚ) (X : Finset RcqW) :
    nu C routedCoinQuery X =
      (C .e).w .a * (∑ i : Fin 2, ∑ act : Act2,
        if (true, decide (i = 0), act) ∈ X then (1/2 : ℚ) * (C .d).w act else 0) +
      (C .e).w .b * (if (false, false, Act2.a) ∈ X then 1 else 0) := by
  rw [nu_eq_sum]
  unfold routedCoinQuery
  rw [sum_leaves_decision, Act2.sum_univ]
  congr 1
  · rw [sum_leaves_chance, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_leaves_decision, Finset.mul_sum]
    refine Finset.sum_congr rfl fun act _ => ?_
    rw [Tree.sum_leaves_leaf]
    simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf, world_decision, world_chance,
      world_leaf, FinDistr.fair, FinDistr.coin, mul_one]
    fin_cases i <;> simp
    all_goals ring_nf
  · rw [Tree.sum_leaves_leaf]
    simp only [leafLaw_decision, leafLaw_leaf, world_decision, world_leaf]
    split_ifs <;> simp

/-- The four masses of Lemma 3′ on the routed tree with `C(e)(a) = ½`, `C(d) = (q, 1−q)`,
`X = {c = 1}`, `a`: `ν(X ∩ a ∩ O) = q/4`, `ν(O) = ½`, `ν(X ∩ O) = ¼`, `ν(a ∩ O) = q/2`.
Neither `ν(O)` nor `ν(X ∩ O)/ν(O)` is `0` or `1`: the observation and the pre-query event are
both informative.
Source: adversarial audit r2 B1; mandate T6
Kind: N+ -/
theorem routedCoinQuery_nu_values (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu (rcqProc q h0 h1) routedCoinQuery (rcqCoin ∩ rcqActEv .d .a ∩ rcqObs .d) = q / 4 ∧
    nu (rcqProc q h0 h1) routedCoinQuery (rcqObs .d) = 1 / 2 ∧
    nu (rcqProc q h0 h1) routedCoinQuery (rcqCoin ∩ rcqObs .d) = 1 / 4 ∧
    nu (rcqProc q h0 h1) routedCoinQuery (rcqActEv .d .a ∩ rcqObs .d) = q / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [routedCoinQuery_nu]
    simp [Act2.sum_univ, rcqProc, gateProc, rcqCoin, rcqActEv, rcqObs]
    all_goals ring

/-- **Lemma 3′ instantiated with an informative observation**: `screening_recorded` on the
routed tree, for every procedure and `a`; numerically `q/4 · ½ = ¼ · q/2` under `rcqProc`
(`routedCoinQuery_nu_values`). Answers round 1's A.8.
Source: `sl-defensible-claims.md` S4; mandate T6; adversarial audit r1 A.8, r2 §3.3
Kind: N+ -/
theorem routedCoinQuery_screening_instance (C : Proc GatePt (fun _ => Act2) ℚ) (act : Act2) :
    nu C routedCoinQuery (rcqCoin ∩ rcqActEv .d act ∩ rcqObs .d) *
        nu C routedCoinQuery (rcqObs .d) =
      nu C routedCoinQuery (rcqCoin ∩ rcqObs .d) *
        nu C routedCoinQuery (rcqActEv .d act ∩ rcqObs .d) :=
  screening_recorded rcqObs rcqActEv (routedCoinQuery_recordsFor C)
    (routedCoinQuery_preQuery_coin C) act

/-- **The SSC form under `H*` instantiated where `H*`'s second clause is not automatic**:
`screening_ssc_of_hStar` on the routed tree, for every procedure and `a`.
Source: `sl-defensible-claims.md` S4 ("the SSC version needs `H*`"); adversarial audit r2 B1
Kind: N+ -/
theorem routedCoinQuery_ssc_instance (C : Proc GatePt (fun _ => Act2) ℚ) (act : Act2) :
    mass C routedCoinQuery (worldEv routedCoinQuery (rcqCoin ∩ rcqActEv .d act) ∩
        occ .d routedCoinQuery) * mass C routedCoinQuery (occ .d routedCoinQuery) =
      mass C routedCoinQuery (worldEv routedCoinQuery rcqCoin ∩ occ .d routedCoinQuery) *
        mass C routedCoinQuery (worldEv routedCoinQuery (rcqActEv .d act) ∩
          occ .d routedCoinQuery) :=
  screening_ssc_of_hStar rcqObs rcqActEv (routedCoinQuery_hStar C)
    (routedCoinQuery_preQuery_coin C) act

/-- The four run-level masses of the SSC form on the routed tree under `rcqProc`:
`μ(X ∩ a ∩ occ) = q/4`, `μ(occ) = ½`, `μ(X ∩ occ) = ¼`, `μ(a ∩ occ) = q/2` — the same numbers
as `routedCoinQuery_nu_values`, because under `H*` the `occ(d)`-runs are the `O_d`-runs
(`mass_worldEv_inter_occ_of_hStar`); in particular `μ(occ(d)) = ½ ≠ 1`, so the passage from
the `O_d`-runs to `occ(d)` that the headline adds to Lemma 3′ is exercised.
Source: adversarial audit r2 B1
Kind: N+ -/
theorem routedCoinQuery_ssc_values (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    mass (rcqProc q h0 h1) routedCoinQuery (worldEv routedCoinQuery (rcqCoin ∩ rcqActEv .d .a) ∩
        occ .d routedCoinQuery) = q / 4 ∧
    mass (rcqProc q h0 h1) routedCoinQuery (occ .d routedCoinQuery) = 1 / 2 ∧
    mass (rcqProc q h0 h1) routedCoinQuery (worldEv routedCoinQuery rcqCoin ∩
        occ .d routedCoinQuery) = 1 / 4 ∧
    mass (rcqProc q h0 h1) routedCoinQuery (worldEv routedCoinQuery (rcqActEv .d .a) ∩
        occ .d routedCoinQuery) = q / 2 := by
  have h := routedCoinQuery_hStar (rcqProc q h0 h1)
  obtain ⟨v1, v2, v3, v4⟩ := routedCoinQuery_nu_values q h0 h1
  have hu : mass (rcqProc q h0 h1) routedCoinQuery (occ .d routedCoinQuery) =
      nu (rcqProc q h0 h1) routedCoinQuery (rcqObs .d) := by
    have hw : worldEv routedCoinQuery Finset.univ = Finset.univ := by
      ext ℓ; simp [worldEv]
    have := mass_worldEv_inter_occ_of_hStar rcqObs rcqActEv h Finset.univ
    rw [Finset.univ_inter, hw, Finset.univ_inter] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mass_worldEv_inter_occ_of_hStar rcqObs rcqActEv h]; exact v1
  · rw [hu]; exact v2
  · rw [mass_worldEv_inter_occ_of_hStar rcqObs rcqActEv h]; exact v3
  · rw [mass_worldEv_inter_occ_of_hStar rcqObs rcqActEv h]; exact v4

/-! ### T11's nesting N−: the disposition identity fails on the AMD -/

/-- The AMD leaf `(b, a)` meets `d` twice.
Source: [[decision-problems-v2]] Proposition 5(c); mandate T11 (nesting N−)
Kind: L -/
theorem amd_count_sba : count () amd ⟨.b, ⟨.a, ()⟩⟩ = 2 := by
  unfold amd; simp

/-- `μ` on the AMD of a run event as an explicit three-term sum.
Source: none: infrastructure
Kind: L -/
theorem amd_mass (C : Proc Unit (fun _ => Act2) ℚ) (P : amd.Leaves → Prop) [DecidablePred P] :
    mass C amd (Finset.univ.filter P) =
      (if P ⟨.a, ()⟩ then (C ()).w .a else 0) +
      ((if P ⟨.b, ⟨.a, ()⟩⟩ then (C ()).w .b * (C ()).w .a else 0) +
       (if P ⟨.b, ⟨.b, ()⟩⟩ then (C ()).w .b * (C ()).w .b else 0)) := by
  rw [mass_filter]
  unfold amd
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
    Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp only [leafLaw_decision, leafLaw_leaf, mul_one]

/-- `occ(d)` on the AMD is every run.
Source: none: infrastructure
Kind: L -/
theorem amd_occ_eq_univ : occ () amd = Finset.univ := by
  ext ℓ
  simp only [mem_occ, Finset.mem_univ, iff_true]
  unfold amd at ℓ ⊢
  rcases ℓ with ⟨_ | _, ℓ⟩ <;> simp

/-- The four masses of the disposition identity on the AMD at `C(d) = ½` with `S = drew_b`
(the runs that drew `b` at `d` — on the AMD, exactly the runs that reach the second node) and
`a`: `μ(S ∩ drew_a) = ¼` (the run `(b, a)`), `μ_{C[d↦a]}(occ) = 1`, `μ_{C[d↦a]}(S ∩ occ) = 0`
(under `δ_a` nothing draws `b`), `μ(drew_a) = ¾`.
Source: `faithful.md` FA-4 / FA-8 (the nesting caveat); mandate T11 (nesting N−)
Kind: N− -/
theorem amd_disposition_values :
    mass (procQ (1/2) (by norm_num) (by norm_num)) amd (drew () .b amd ∩ drew () .a amd) =
      1 / 4 ∧
    mass ((procQ (1/2) (by norm_num) (by norm_num)).deviatePure () .a) amd (occ () amd) = 1 ∧
    mass ((procQ (1/2) (by norm_num) (by norm_num)).deviatePure () .a) amd
      (drew () .b amd ∩ occ () amd) = 0 ∧
    mass (procQ (1/2) (by norm_num) (by norm_num)) amd (drew () .a amd) = 3 / 4 := by
  have e1 : drew () .b amd ∩ drew () .a amd =
      Finset.univ.filter fun ℓ => (⟨(), .b⟩ : Σ d : Unit, Act2) ∈ draws amd ℓ ∧
        (⟨(), .a⟩ : Σ d : Unit, Act2) ∈ draws amd ℓ := by
    ext ℓ; simp
  have e3 : drew () .b amd ∩ occ () amd =
      Finset.univ.filter fun ℓ => (⟨(), .b⟩ : Σ d : Unit, Act2) ∈ draws amd ℓ := by
    rw [amd_occ_eq_univ, Finset.inter_univ]
    ext ℓ; simp
  have e4 : drew () .a amd =
      Finset.univ.filter fun ℓ => (⟨(), .a⟩ : Σ d : Unit, Act2) ∈ draws amd ℓ := by
    ext ℓ; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, amd_mass]
    simp [amd, procQ, Sigma.mk.injEq, heq_eq_eq]
    norm_num
  · rw [amd_occ_eq_univ, mass_univ]
  · rw [e3, amd_mass]
    simp [amd, Proc.deviatePure, Proc.deviate, FinDistr.pure_w, Sigma.mk.injEq, heq_eq_eq]
  · rw [e4, amd_mass]
    simp [amd, procQ, Sigma.mk.injEq, heq_eq_eq]
    norm_num

/-- **The disposition identity fails under nesting**: on the AMD at `C(d) = ½` with
`S = drew_b` (the runs that drew `b` at `d`) and `a`,
`μ(S ∩ drew_a) · μ_{C[d↦a]}(occ) = ¼ · 1 ≠ 0 · ¾ = μ_{C[d↦a]}(S ∩ occ) · μ(drew_a)`. The run
`(b, a)` meets `d` twice (`amd_count_sba`), so `disposition_faithful`'s hypothesis `#_d ≤ 1` is
necessary: conditioning on "drew `a`" is not the deviation `C[d↦a]` restricted to `occ(d)`
when a run can draw at `d` twice and disagree.
Source: `faithful.md` FA-4 (the identity) and FA-8 (the nesting caveat); mandate T11 ("the
nesting N−")
Kind: N−
Fidelity: exact (the refuted statement is `disposition_faithful`'s conclusion without its
`#_d ≤ 1` hypothesis, at one `S` and one `C`) -/
theorem amd_disposition_fails :
    mass (procQ (1/2) (by norm_num) (by norm_num)) amd (drew () .b amd ∩ drew () .a amd) *
      mass ((procQ (1/2) (by norm_num) (by norm_num)).deviatePure () .a) amd (occ () amd) ≠
    mass ((procQ (1/2) (by norm_num) (by norm_num)).deviatePure () .a) amd
        (drew () .b amd ∩ occ () amd) *
      mass (procQ (1/2) (by norm_num) (by norm_num)) amd (drew () .a amd) := by
  obtain ⟨h1, h2, h3, h4⟩ := amd_disposition_values
  rw [h1, h2, h3, h4]; norm_num

/-! ### A node-level instance of `valueNode_affine` on the AMD (round 1's A.3) -/

/-- The AMD's second `d`-node: the one below the root's `b`-edge.
Source: [[decision-problems-v2]] Proposition 5(c); §8 (node-level policies); adversarial audit
r1 A.3
Kind: D -/
def amdSecondNode : amd.DecNode := some ⟨.b, none⟩

/-- The three node-level values of `valueNode_affine` at the AMD's second node under the tied
policy `p_q := C(d_q)` with `C(d) = (q, 1−q)`: `V(p) = (1−q)(3q+1)`; forcing `a` at the
second node, `V(p[q₂↦δ_a]) = 4(1−q)`; forcing `b`, `V(p[q₂↦δ_b]) = 1−q`. The root still draws
(`q · 0 + (1−q) · 4`, `q · 0 + (1−q) · 1`): the single-instance counterfactual of v2 §8, not
the point deviation `C[d↦a]`, which forces the root too (`V(C[d↦a]) = 0`, `V(C[d↦b]) = 1`).
Source: [[decision-problems-v2]] §8 ("forcing the single instance, all other nodes … still
drawing"); Proposition 5(c); adversarial audit r1 A.3
Kind: N+ -/
theorem amd_valueNode_values (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    valueNode amd (NodePolicy.ofProc (procQ q h0 h1) amd) = (1 - q) * (3 * q + 1) ∧
    valueNode amd ((NodePolicy.ofProc (procQ q h0 h1) amd).update amdSecondNode
      (FinDistr.pure .a)) = 4 * (1 - q) ∧
    valueNode amd ((NodePolicy.ofProc (procQ q h0 h1) amd).update amdSecondNode
      (FinDistr.pure .b)) = 1 - q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [valueNode_ofProc, amd_value]
  all_goals
    unfold valueNode amdSecondNode amd
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [NodePolicy.update, NodePolicy.ofProc, NodePolicy.restrictDecision, procQ,
      FinDistr.pure_w, FinDistr.act2_a, FinDistr.act2_b]
    all_goals ring

/-- **`valueNode_affine` instantiated at the AMD's second node** under the tied policy: with
`amd_valueNode_values`, `(1−q)(3q+1) = q · 4(1−q) + (1−q) · (1−q)` (`amd_valueNode_affine_check`)
— a non-degenerate instance, the two forced values differing and both depending on `q` through
the still-drawing root.
Source: [[decision-problems-v2]] §8 Theorem 1 proof; mandate T7(i); adversarial audit r1 A.3
Kind: N+ -/
theorem amd_valueNode_affine_instance (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    valueNode amd (NodePolicy.ofProc (procQ q h0 h1) amd) =
      ∑ x, ((NodePolicy.ofProc (procQ q h0 h1) amd) amdSecondNode).w x *
        valueNode amd ((NodePolicy.ofProc (procQ q h0 h1) amd).update amdSecondNode
          (FinDistr.pure x)) :=
  valueNode_affine amd _ amdSecondNode

/-- The numbers of `amd_valueNode_affine_instance` check: `(1−q)(3q+1) = q · 4(1−q) + (1−q)²`.
Source: adversarial audit r1 A.3
Kind: N+ -/
theorem amd_valueNode_affine_check (q : ℚ) :
    (1 - q) * (3 * q + 1) = q * (4 * (1 - q)) + (1 - q) * (1 - q) := by ring

end Cleanroom.Found.DpCoreTree
