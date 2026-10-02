import Cleanroom.Li.LiPseudorandom.Witnesses
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.DeductiveDovetail
import LogicalInduction.Properties.Coherence
import LogicalInduction.Properties.NonDogmatism

/-!
# `li-pseudorandom` — the market of record varies with the stream; certified inductors over
fixed families

Adopted in repair round 2 from the round-2 adversarial probe `MarketVaries.lean` (items 1–2 of
that audit), generalized from constant streams to every primitive recursive stream and placement.

Both round-1 audits and the round-1 repair left one caveat on T6: nothing showed that the market
of record `x ↦ liaHistory (atomDP a x g)` *varies* with `x` — if the LIA ignored `atomDP`'s
stages, `truthStar_pseudorandom` would be T4 over a fixed history wearing T6's name. This module
settles it with FAF's own criterion theorems, and along the way makes the T4 witness's market a
*certified* logical inductor:

* `atomDP_succ_computable`: for primitive recursive `a` and `x`, `atomDP a x (·+1)` is a
  `ComputableDeductiveProcess` — its stage `n` is the list of the first `n` literals (FAF's
  `encode_stage_prim_of_list` + `ComputableDeductiveProcess.ofEncodePrim`); hence
  `atomDP_succ_isLogicalInductor` by FAF's `LIA_is_logical_inductor` (`thm:lia`).
* On the all-`false` stream `∼atom 0` is in stage `1`, so `lic_disprovable_tendsto_zero` gives
  `liaHistory … n (atom 0) → 0`; on the all-`true` stream the atom world holds `atom 0` and is
  consistent with every stage, so `lic_exists_limit_pos` gives a positive limit; hence the two
  histories differ: **the builder of record is not a constant map** (`liaHistory_atomDP_ne`,
  `builder_not_const`).
* `diagBuilder_liaHistory_certified`: T4's package over the LIA of a fixed primitive recursive
  family, with the inductor certificate, FAF's `PseudorandomFrequency` for every `f`, and
  non-constancy of the stream, in one statement — the T4 witness of record.

What this does *not* show: that a price-reading P-generable weighting is divergent on the LIA
of record; that needs the LIA's prices on the *undecided* members of the family of record, which
is T7-level (`Computable.lean`). The T6 witness `truthStar_not_eventuallyConst` still certifies
the stream through the constant weighting only.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction LO.Propositional Filter Topology

/-! ## `atomDP` over primitive recursive data is a computable deductive process -/

/-- `n ↦ atom n` is primitive recursive (FAF's own proof shape).
Source: none: infrastructure; FAF `encode_atom`
Kind: L
Fidelity: n/a -/
lemma atom_prim : Primrec (fun c : ℕ => (Formula.atom c : Sentence)) :=
  Primrec.encode_iff.mp
    ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id)).of_eq
      (fun c => (encode_atom c).symm))

/-- `n ↦ ∼atom n` is primitive recursive (FAF's own proof shape).
Source: none: infrastructure; FAF `encode_negAtom`
Kind: L
Fidelity: n/a -/
lemma negAtom_prim : Primrec (fun c : ℕ => (∼(Formula.atom c) : Sentence)) :=
  Primrec.encode_iff.mp
    ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id))
        (Primrec.const (Nat.pair 0 0 + 1))))).of_eq
      (fun c => (encode_negAtom c).symm))

/-- The literal map is primitive recursive when the placement and the stream are.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma literalOf_prim {a : ℕ → ℕ} {x : ℕ → Bool} (ha : Primrec a) (hx : Primrec x) :
    Primrec (literalOf a x) :=
  (Primrec.cond hx (atom_prim.comp ha) (negAtom_prim.comp ha)).of_eq
    (fun j => by cases h : x j <;> simp [literalOf, h])

/-- Stage `n` of the delay-one process is the list of the first `n` literals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomDP_succ_stage (a : ℕ → ℕ) (x : ℕ → Bool) (n : ℕ) :
    (atomDP a x (fun j => j + 1)).D n = ((List.range n).map (literalOf a x)).toFinset := by
  ext φ
  rw [mem_atomDP_iff, List.mem_toFinset, List.mem_map]
  simp only [List.mem_range]
  constructor
  · rintro ⟨j, ⟨_, hj⟩, rfl⟩
    exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, ⟨by omega, by omega⟩, rfl⟩

/-- **The delay-one process over primitive recursive data is a computable deductive process**
(the paper's `def:dedproc` certificate), by FAF's stage-list criterion.
Source: mandate T6/T7 (the fixed-family case); FAF `encode_stage_prim_of_list`,
`ComputableDeductiveProcess.ofEncodePrim`; round-2 adversarial audit, item 2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem atomDP_succ_computable {a : ℕ → ℕ} {x : ℕ → Bool} (ha : Primrec a) (hx : Primrec x) :
    ComputableDeductiveProcess (atomDP a x (fun j => j + 1)) :=
  ComputableDeductiveProcess.ofEncodePrim (encode_stage_prim_of_list
    (Primrec.list_map Primrec.list_range ((literalOf_prim ha hx).comp Primrec.snd).to₂)
    (atomDP_succ_stage a x))

/-- **The LIA over the delay-one process of a primitive recursive family is a logical inductor**
(FAF's `thm:lia`).
Source: mandate T6/T7 (the fixed-family case); FAF `LIA_is_logical_inductor`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem atomDP_succ_isLogicalInductor {a : ℕ → ℕ} {x : ℕ → Bool} (ha : Primrec a)
    (hx : Primrec x) :
    IsLogicalInductor (liaHistory (atomDP a x (fun j => j + 1))) (atomDP a x (fun j => j + 1)) :=
  LIA_is_logical_inductor _ (atomDP_succ_computable ha hx)

/-! ## The market of record depends on the stream -/

/-- The constant stream.
Source: none: infrastructure (witness)
Kind: D
Fidelity: n/a -/
abbrev constStream (b : Bool) : ℕ → Bool := fun _ => b

/-- The delay-one process over the constant stream at placement `id`.
Source: none: infrastructure (witness)
Kind: D
Fidelity: n/a -/
abbrev constDP (b : Bool) : DeductiveProcess := atomDP id (constStream b) (fun j => j + 1)

/-- Both constant-stream processes are computable deductive processes.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
theorem constDP_computable (b : Bool) : ComputableDeductiveProcess (constDP b) :=
  atomDP_succ_computable Primrec.id (Primrec.const b)

/-- The LIA over each constant-stream process is a logical inductor.
Source: none: infrastructure (witness); FAF `LIA_is_logical_inductor`
Kind: L
Fidelity: n/a -/
instance constDP_isLogicalInductor (b : Bool) :
    IsLogicalInductor (liaHistory (constDP b)) (constDP b) :=
  LIA_is_logical_inductor _ (constDP_computable b)

/-- Every stage of a constant-stream process has a consistent world.
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
lemma constDP_hworld (b : Bool) : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((constDP b).D n) :=
  atomDP_hworld Function.injective_id _ _

/-- On the all-`false` stream the LIA's price of `atom 0` tends to `0` (`∼atom 0` is in stage
`1`; FAF's `lic_disprovable_tendsto_zero`).
Source: none: infrastructure (witness); FAF `lic_disprovable_tendsto_zero`
Kind: L
Fidelity: n/a -/
theorem price_atom_zero_false :
    ConvergesTo (fun n => liaHistory (constDP false) n (Formula.atom 0)) 0 :=
  lic_disprovable_tendsto_zero (liaHistory (constDP false)) (constDP false) (Formula.atom 0)
    ⟨1, by
      have h := literalOf_mem_atomDP (a := id) (x := constStream false) (g := fun j => j + 1)
        (fun j => Nat.lt_succ_self j) (j := 0) (n := 1) le_rfl
      simpa [literalOf, constStream] using h⟩
    (constDP_hworld false)

/-- On the all-`true` stream the LIA's price of `atom 0` has a positive limit (the atom world
holds `atom 0` and is consistent with every stage; FAF's `lic_exists_limit_pos`).
Source: none: infrastructure (witness); FAF `lic_exists_limit_pos`
Kind: L
Fidelity: n/a -/
theorem price_atom_zero_true_pos :
    ∃ L, ConvergesTo (fun n => liaHistory (constDP true) n (Formula.atom 0)) L ∧ 0 < L :=
  lic_exists_limit_pos (liaHistory (constDP true)) (constDP true) (Formula.atom 0) (fun n =>
    ⟨atomWorld id (constStream true),
      atomWorld_consistentWith Function.injective_id (constStream true) (fun j => j + 1) n,
      by rw [PCWorld.holds_atom]; exact ⟨0, rfl, rfl⟩⟩)

/-- **The LIA over `atomDP` depends on the stream**: the all-`true` and all-`false` streams give
different histories.
Source: mandate T6 (non-vacuity of the market of record); round-1 audits' T6 caveat; round-2
adversarial audit, item 1
Kind: N+
Fidelity: n/a -/
theorem liaHistory_atomDP_ne : liaHistory (constDP true) ≠ liaHistory (constDP false) := by
  intro h
  obtain ⟨L, hL, hpos⟩ := price_atom_zero_true_pos
  have h0 := price_atom_zero_false
  rw [h] at hL
  have := tendsto_nhds_unique hL h0
  linarith

/-- **The builder of record `x ↦ liaHistory (atomDP id x (·+1))` is not a constant map.**
Source: mandate T6 (non-vacuity of the market of record); round-2 adversarial audit, item 1
Kind: N+
Fidelity: n/a -/
theorem builder_not_const :
    ∃ x y : ℕ → Bool,
      liaHistory (atomDP id x (fun j => j + 1)) ≠ liaHistory (atomDP id y (fun j => j + 1)) :=
  ⟨_, _, liaHistory_atomDP_ne⟩

/-! ## T4 over a certified logical inductor -/

/-- **T4's witness of record, certified.** For primitive recursive `a`, `y` and `p ∈ (0,1)`: the
LIA over `atomDP a y (·+1)` is a logical inductor (FAF's criterion, whole), the fixed-history
family over it inhabits FAF's `PseudorandomFrequency` at `p` for every `f`, and that family is
not eventually constant.
Source: mandate T4 (witness); [[STANDARDS]] §3; round-2 adversarial audit, item 2
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem diagBuilder_liaHistory_certified {a : ℕ → ℕ} {y : ℕ → Bool} (ha : Primrec a)
    (hy : Primrec y) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    IsLogicalInductor (liaHistory (atomDP a y (fun j => j + 1))) (atomDP a y (fun j => j + 1)) ∧
    (∀ f : DeferralFunction,
      PseudorandomFrequency
        (truthR (diagBuilder (fun _ => liaHistory (atomDP a y (fun j => j + 1))) genWeighting
          (fun _ => p)))
        p f (liaHistory (atomDP a y (fun j => j + 1)))) ∧
    ¬ ∃ N b, ∀ n ≥ N,
      diagBuilder (fun _ => liaHistory (atomDP a y (fun j => j + 1))) genWeighting (fun _ => p) n
        = b :=
  ⟨atomDP_succ_isLogicalInductor ha hy,
   pseudorandomFrequency_of_history _ genWeighting genWeighting_covers p ⟨hp0.le, hp1.le⟩,
   diagBuilder_liaHistory_not_eventuallyConst a _ y hp0 hp1⟩

end Cleanroom.Li.LiPseudorandom
