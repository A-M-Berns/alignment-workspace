import Cleanroom.Fa.FaAdaptiveJoint.Defs

/-!
# `fa-adaptive-joint` · Expressibility: (A4) decided — the softened machine is generable (T1)

[[fa-adaptive-joint-mandate]] T1. The day-`n` serialization of `adaptFire w f θ n` is the
concatenation of the `n + 1` bindings' serializations followed by `n` `letE` tags
(`serialize_adaptFire`); each binding's serialization is a bounded frame around the open sum —
`j` fixed-shape summands, each a written-out constant (the open test, decided by `openCount`'s
ruler) times a written-out variable index — and the ramp of `w j` (FAF's `ctsIndFeature`). Both
concatenations are FAF's `MachineSpliceStream.concatVar` (a machine-metered triangle over the
unary pair), so the whole stream is machine-metered: `adaptFire_pgenerable`. Rank `≤ n` because
the open sum is price-free and the ramp has `w`'s rank; closed because the chain denotes the same
value in every environment (`adaptFire_denoteWith`).

The two-market reading of (A4) — closure of joint legibility under the machine — is
`legibleOn_fireSeq` / `legibleOn_fireSeq_joint`, through the real firing sequence `fireSeq` and
the uniqueness of the recursion law (`FireRec.unique`, `Counting.lean` has the real-sequence
facts; the uniqueness is here because the closure needs it).
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology

/-! ## A. Serialization laws -/

/-- The partial open sum serializes as `[1, ⌜0⌝]` followed by one summand block per piece
(FAF's `serialize_armChain` shape).
Source: none: infrastructure (FAF `serialize_armChain`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem serialize_openExprAux (f : DeferralFunction) (j : ℕ) : ∀ m,
    (openExprAux f j m).serialize
      = [1, Encodable.encode ((0 : ℚ))]
        ++ (List.range m).flatMap (fun i => (pieceTerm f (Nat.pair j i)).serialize ++ [2])
  | 0 => by simp [openExprAux, EF.serialize]
  | m + 1 => by
      rw [openExprAux]
      simp only [EF.serialize]
      rw [serialize_openExprAux f j m, List.range_succ, List.flatMap_append,
        List.flatMap_singleton]
      simp [List.append_assoc]

/-- A chain serializes as the bindings' serializations, the body's, then one `letE` tag (`8`) per
binding.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem serialize_chainList : ∀ (xs : List EF) (b : EF),
    (chainList xs b).serialize = xs.flatMap EF.serialize ++ b.serialize ++ List.replicate xs.length 8
  | [], b => by simp [chainList]
  | a :: xs, b => by
      rw [chainList]
      simp only [EF.serialize]
      rw [serialize_chainList xs b, List.flatMap_cons, List.length_cons, List.replicate_succ']
      simp [List.append_assoc]

/-- **The day-`n` serialization of `adaptFire`**: the `n + 1` bindings in order, then `n` tags `8`.
Source: [[fa-adaptive-joint-mandate]] § T1 ("a straight-line program of `O(n)` `letE` bindings")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem serialize_adaptFire (w : ℕ → EF) (f : DeferralFunction) (θ : ℚ) (n : ℕ) :
    (adaptFire w f θ n).serialize
      = (List.range (n + 1)).flatMap (fun i => (fireExpr w f θ i).serialize)
        ++ List.replicate n 8 := by
  rw [adaptFire, serialize_chainList, List.length_map, List.length_range, List.range_succ,
    List.flatMap_append, List.flatMap_singleton, List.flatMap_map]

/-! ## B. The emission certificate -/

/-- One summand block (the open-test constant times the variable index, then the `add` tag) is a
machine-metered spliceable stream over the unary pair: the constant by `ifZero` on the open-test
ruler, the index by `MachineDigits.ofUnaryRuler` of `⟨j, m⟩ ↦ j − 1 − m`.
Source: [[fa-adaptive-joint-mandate]] § T1 (`serialize_add`/`serialize_mul` templates, `f.graph_fp` at emission time)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem pieceTerm_spliceStream (f : DeferralFunction) :
    MachineSpliceStream (fun z => (pieceTerm f z).serialize ++ [2]) := by
  have hind : MachineSpliceStream (fun z => (openInd f z).serialize) :=
    ((MachineSpliceStream.serialize_const 1).ifZero (MachineSpliceStream.serialize_const 0)
      (openCount_ruler f)).of_eq (fun z => by
        unfold openInd
        split_ifs <;> rfl)
  have hvar : MachineSpliceStream (fun z => (EF.var (z.unpair.1 - 1 - z.unpair.2)).serialize) :=
    MachineSpliceStream.serialize_var (MachineDigits.ofUnaryRuler
      ((UnaryRuler.unpairFst.sub (UnaryRuler.const 1)).sub UnaryRuler.unpairSnd))
  exact ((MachineSpliceStream.serialize_mul hind hvar).append
    (MachineSpliceStream.tag 2 (by norm_num))).of_eq (fun z => rfl)

/-- The open sum `openExpr f j` is a machine-metered spliceable stream in `j`: the head constant,
then `j` summand blocks by `concatVar` on the identity ruler.
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem openExpr_spliceStream (f : DeferralFunction) :
    MachineSpliceStream (fun j => (openExpr f j).serialize) :=
  ((MachineSpliceStream.serialize_const 0).append
    ((pieceTerm_spliceStream f).concatVar UnaryRuler.id)).of_eq (fun j => by
      rw [openExpr, serialize_openExprAux f j]
      rfl)

/-- The ramp is a legal feature progression (FAF's `ctsIndFeature_generated` at the constant
threshold `θ/2`).
Source: [[fa-adaptive-joint-mandate]] § T1; FAF `ctsIndFeature_generated`
Kind: L
Fidelity: exact
Hyps: (a) `hw` -/
theorem ramp_pgenerable {w : ℕ → EF} (hw : PGenerableWeighting w) (θ : ℚ) :
    PGenerableWeighting (ramp θ w) :=
  ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / (θ / 2))) hw
    (pgenerableWeighting_const (θ / 2))

/-- The day-`j` binding is a machine-metered spliceable stream in `j`.
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: n/a
Hyps: (a) `hw` -/
theorem fireExpr_spliceStream {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) : MachineSpliceStream (fun j => (fireExpr w f θ j).serialize) :=
  (MachineSpliceStream.serialize_mul
    (MachineSpliceStream.serialize_add (MachineSpliceStream.serialize_const 1)
      (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
        (openExpr_spliceStream f)))
    (ramp_pgenerable hw θ).polySeg).of_eq (fun _ => rfl)

/-- **The firing feature's serialization is machine-metered**: the `n + 1` bindings by `concatVar`
on the successor ruler (block `j` of day `n` is the day-`j` binding, reindexed through
`unpairSnd`), then `n` `letE` tags by `repeatTag`.
Source: [[fa-adaptive-joint-mandate]] § T1 ("the `MachineSpliceStream` certificate is the work")
Kind: L
Fidelity: n/a
Hyps: (a) `hw` -/
theorem adaptFire_spliceStream {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) : MachineSpliceStream (fun n => (adaptFire w f θ n).serialize) :=
  ((((fireExpr_spliceStream hw f θ).comp UnaryRuler.unpairSnd).concatVar UnaryRuler.id.succ).append
    (MachineSpliceStream.repeatTag 8 (by norm_num) UnaryRuler.id)).of_eq (fun n => by
      rw [serialize_adaptFire]
      simp [Nat.unpair_pair])

/-! ## C. Rank -/

/-- The open sum is price-free: rank `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem openExprAux_rank (f : DeferralFunction) (j : ℕ) : ∀ m, (openExprAux f j m).rank = 0
  | 0 => by simp [openExprAux]
  | m + 1 => by simp [openExprAux, pieceTerm, openInd, EF.rank, openExprAux_rank f j m]

/-- The day-`j` binding has rank `≤ j` (the ramp has `w j`'s rank).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) `hw` -/
theorem fireExpr_rank_le {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) (j : ℕ) : (fireExpr w f θ j).rank ≤ j := by
  simp only [fireExpr, EF.rank_mul, oneMinus_rank, openExpr, openExprAux_rank]
  exact Nat.max_le.2 ⟨Nat.zero_le _, (ramp_pgenerable hw θ).rank_le j⟩

/-- A chain's rank is bounded by a common bound on its bindings and body.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem chainList_rank_le {N : ℕ} : ∀ (xs : List EF) (b : EF),
    (∀ a ∈ xs, a.rank ≤ N) → b.rank ≤ N → (chainList xs b).rank ≤ N
  | [], _, _, hb => hb
  | a :: xs, b, hxs, hb => by
      rw [chainList, EF.rank_letE]
      exact Nat.max_le.2 ⟨hxs a List.mem_cons_self,
        chainList_rank_le xs b (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) hb⟩

/-- **`adaptFire w f θ n` has rank `≤ n`** (mandate `adaptFire_rank_le`).
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) `hw` -/
theorem adaptFire_rank_le {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) (n : ℕ) : (adaptFire w f θ n).rank ≤ n := by
  refine chainList_rank_le _ _ (fun a ha => ?_) (fireExpr_rank_le hw f θ n)
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  exact (fireExpr_rank_le hw f θ i).trans (List.mem_range.1 hi).le

/-! ## D. T1: (A4)'s expressibility half, decided -/

/-- **T1 (headline, load-bearing). (A4) holds over FAF's `EF`: the softened one-position machine
on any legal feature progression is itself a legal feature progression.** For every
`PGenerableWeighting w`, lookahead `f : DeferralFunction` and rational `θ`, the firing feature
`adaptFire w f θ` — day `n`'s expression binds `fire 0 … fire (n−1)` once each by `letE` and
returns `fire n = (1 − ∑_{m<n, n<f m} fire m) · ctsInd (θ/2) (w n) (θ/2)` — is a
`PGenerableWeighting`: its serialization is a machine-metered spliceable stream
(`adaptFire_spliceStream`: a `concatVar` triangle of bounded blocks, each carrying the ramp of
`w n` and the day's open test decided by `f.graph_fp`), its rank is `≤ n`
(`adaptFire_rank_le`) and it is closed (`adaptFire_denoteWith`). The hypothesis `0 < θ` of the
mandate's statement is not needed for expressibility (only for reading the ramp as `ctsInd`,
`adaptFireR_rec`).
Scope: one-way (a single market; the two-market reading is `legibleOn_fireSeq_joint`).
Family: any `PGenerableWeighting w` (in T3, the violation weight's feature). Lookahead: any
`DeferralFunction f` (v3: `2^n`). Threshold: per rational `θ`. Grade: exact (a syntactic fact).
(A4): expressibility proved here; exploitation via T4 (`Bridge.lean`, OPEN, listed).
Source: [[fa-positive-results-corrected-v3]] §4 "(A4)" (ii); root-fa-020; lean-deference-043; [[fa-adaptive-joint-mandate]] § T1
Kind: P
Fidelity: variant: the additive softening of the mandate (v3's prose admits the product reading, which over-fires — findings F2); "size linear in `n`" rendered as FAF's polynomial-time emission (`MachineSpliceStream`), findings F3; the lookahead is a general `DeferralFunction` (K3)
Hyps: (a) `hw`; no (b), no (c). -/
theorem adaptFire_pgenerable {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) : PGenerableWeighting (adaptFire w f θ) where
  polySeg := adaptFire_spliceStream hw f θ
  rank_le := adaptFire_rank_le hw f θ
  closed := fun n ρ V => by
    rw [adaptFire_denoteWith hw, EF.denote, adaptFire_denoteWith hw]

/-! ## E. The real firing sequence and the two-market reading of (A4) -/

/-- **The firing sequence of a real weighting** `w` under lookahead `f` and threshold `θ`: the
unique solution of the recursion law `FireRec` (`fireSeq_fireRec`, `FireRec.unique`). It is what
`adaptFire` denotes on any market where `w` is the denoted values (`adaptFireR_eq_fireSeq`), and
what `v3Theorem2` runs on.
Source: [[fa-adaptive-joint-mandate]] § T1, § T2
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def fireSeq (f : ℕ → ℕ) (θ : ℚ) (w : ℕ → ℝ) : ℕ → ℝ
  | n => (1 - ∑ m ∈ (Finset.range n).attach, (if n < f m.1 then fireSeq f θ w m.1 else 0))
      * ctsInd (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ)
  termination_by n => n
  decreasing_by exact Finset.mem_range.1 m.2

/-- `fireSeq` satisfies the recursion law.
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fireSeq_fireRec (f : ℕ → ℕ) (θ : ℚ) (w : ℕ → ℝ) : FireRec f θ w (fireSeq f θ w) := by
  intro n
  have hatt := Finset.sum_attach (Finset.range n)
    (fun m : ℕ => if n < f m then fireSeq f θ w m else (0 : ℝ))
  rw [fireSeq, openMass, hatt]

/-- **Uniqueness of the recursion law**: two solutions agree (strong induction; `openMass` reads
only earlier days).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem FireRec.unique {f : ℕ → ℕ} {θ : ℚ} {w u u' : ℕ → ℝ} (hu : FireRec f θ w u)
    (hu' : FireRec f θ w u') : u = u' := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hsum : openMass f u n = openMass f u' n := by
      unfold openMass
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [ih m (Finset.mem_range.1 hm)]
    rw [hu n, hu' n, hsum]

/-- The denoted firing sequence is `fireSeq` of the denoted weighting.
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) `hw`, `hθ` -/
theorem adaptFireR_eq_fireSeq {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) (V : History) :
    adaptFireR w f θ V = fireSeq f.f θ (fun n => (w n).denote V) :=
  FireRec.unique (adaptFireR_fireRec hw f hθ V) (fireSeq_fireRec _ _ _)

/-- `adaptFire` denotes `fireSeq` of the denoted weighting, on any market.
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) `hw`, `hθ` -/
theorem adaptFire_denote_fireSeq {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) (V : History) (n : ℕ) :
    (adaptFire w f θ n).denote V = fireSeq f.f θ (fun n => (w n).denote V) n := by
  rw [adaptFire_denote hw, adaptFireR_eq_fireSeq hw f hθ]

/-- **Closure of legibility under the machine** (the single-market form of (A4)'s two-market
reading): if the real sequence `x` is a legal feature progression of `P`'s market, so is its
firing sequence `fireSeq f θ x`.
Scope: one-way. Lookahead: any `DeferralFunction`. Threshold: per rational `θ > 0`.
Source: [[fa-positive-results-corrected-v3]] §4 "(A4)" ("`u_n` is a joint-generable weighting"); [[fa-adaptive-joint-mandate]] § T1 ("closure of legibility under the machine")
Kind: C
Fidelity: variant: "joint-generable" rendered as `LegibleOn` on each market (K1)
Hyps: (a) `hθ`; (c) `hx` (`LegibleOn`, the package's one (c)-shape, inherited from `fa-forcing-trader`). -/
theorem legibleOn_fireSeq {P : History} {x : ℕ → ℝ} (hx : LegibleOn P x) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) : LegibleOn P (fireSeq f.f θ x) := by
  obtain ⟨G, hG, hGx⟩ := hx
  refine ⟨adaptFire G f θ, adaptFire_pgenerable hG f θ, fun n => ?_⟩
  rw [adaptFire_denote_fireSeq hG f hθ]
  congr 1
  funext m
  exact hGx m

/-- **(A4)'s two-market reading**: joint legibility of `x` on `A` and `H` is closed under the
machine — the firing sequence is legible on both. This is v3's "(ii) its firing indicator `u_n` is
a joint-generable weighting", stated through `LegibleOn` on each market (K1); it is what T3
consumes.
Scope: two-way in its hypothesis (partial: over the OPEN pair — no two-market inhabitant of
`LegibleOn` is known, `fa-forcing-trader`'s T11).
Source: [[fa-positive-results-corrected-v3]] §4 "(A4)" (ii); [[fa-adaptive-joint-mandate]] § T1
Kind: C
Fidelity: variant: as `legibleOn_fireSeq`
Hyps: (a) `hθ`; (c) `hjoint` (joint legibility, v3's (A1)/(A4) carrier). -/
theorem legibleOn_fireSeq_joint {A H : History} {x : ℕ → ℝ} (hjoint : LegibleOn A x ∧ LegibleOn H x)
    (f : DeferralFunction) {θ : ℚ} (hθ : 0 < θ) :
    LegibleOn A (fireSeq f.f θ x) ∧ LegibleOn H (fireSeq f.f θ x) :=
  ⟨legibleOn_fireSeq hjoint.1 f hθ, legibleOn_fireSeq hjoint.2 f hθ⟩

end Cleanroom.Fa.FaAdaptiveJoint
