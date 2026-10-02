import Cleanroom.Bli.BliAssemble.Headline
import Cleanroom.Bli.BliAssemble.Process
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.Machine.SentenceMachine

/-!
# `bli-assemble` · Inherit: L7 — `𝐏` inherits FAF's §4 theorems on small e.c. families, and
where the inclusion stops (target 10)

All of (a)–(d) is transport by design ([[bli-program]] §4 row L7's own failure mode is to
present it as content): on every family an efficiently computable trader can name
(`MachineSentenceCodes`), the family is eventually small (`bli-found`'s
`machineSentenceCodes_eventually_small`), where `𝐏` copies the base exactly (`bli_small`).

* (a) `bliHistory_eventually_eq_on_machineSentenceCodes` — `𝐏 n (φ n) = Q n (φ n)` from some day on.
* (b) `bliHistory_asympEq_base` — `(fun n => 𝐏 n (φ n)) ≈ₙ fun n => Q n (φ n)`.
* (c) `limitingBelief_bliHistory_eq` — a fixed sentence is small from day `tokenSize ψ` on, so
  the limiting beliefs (FAF's `limitingBelief`, a `limsup`) coincide.
* (d) `bliHistory_provind_iff_base` — FAF's `lic_provind_true` conclusion for `𝐏` on a family is
  the same statement as for the base; and `lic_provind_true_bliHistory_of_base`: the §4 theorem
  for `𝐏` on a machine-named family follows from the **base's** inductor instance alone — L2 is
  not needed for it. That is the sense in which the inheritance is content-free.
* (e) **Where it stops.** The day-varying family `n ↦ ⌜𝑸_{n+1} = code (A_n)⌝` of face points:
  `𝐏` charges it on every day (`bliHistory_tent_nonDegenerate` at a face point,
  `exists_mem_faceProd`), no e.c. trader names it (`not_machineSentenceCodes_nextStateAtoms`, from
  `stateAtom_large`), and `𝐏 ≠ Q` there on every day — in the dichotomy form
  `bliHistory_ne_base_on_stateAtoms_dichotomy` (either some day-`(n+1)` candidate atom is priced
  differently, or the base already distributes mass one over the candidates — `E5` for `𝐏` plus a
  case split, kind `L`), and outright under the named hypothesis that the base prices a face
  point's atom `0` (`bliHistory_ne_base_on_stateAtoms_of_zero`, kind `C`: conditional, not a
  witness). For a general base the hypothesis cannot be dropped (a base agreeing with `𝐏` on the
  state algebra is a base); for FAF's LIA over `paperDP 𝗜𝚺₁` it is discharged from `bli-overlay`'s
  `N₀` on (`Lia.lean`'s `bliHistory_ne_lia_from`, repair round 1), which is where the N+ for
  "where L7 stops" lives.
* **§2.5's "learns" half** (repair round 1, the fidelity audit's N6):
  `bliHistory_stateAtom_tendsto_one_of_stateLearns` — under an inductor instance over the
  state-learning process `bliDP DP states actual` whose realized states are this base's own
  (`StateLearns`), `𝐏`'s price on the settled state atom `⌜𝑸_m = actual m⌝` tends to `1`: FAF's
  `lic_provind_true` at the constant family, with `hthm` from `bliDP_exclusive`, transported by (d).

Finding (recorded in `bli-assemble-findings.md`): bli-slides-040 (i)'s "BLIs are propositionally
coherent" is **not** delivered by L2 — coherence among Tier-A/Tier-B large sentences is
unconstrained, and `bli-superbelief` E7 shows the LIA base itself is incoherent on `smallSet`.

Sources: bli-slides-040 (i); [[bli-program]] §4 row L7; mandate target 10.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional Filter Topology
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

variable (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜)

/-! ## (a)–(d): transport on machine-named families -/

/-- **(a)** On a machine-named family, `𝐏` is the base from some day on.
Source: [[bli-program]] §4 row L7; mandate target 10(a)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bliHistory_eventually_eq_on_machineSentenceCodes (φ : ℕ → Sentence)
    (h : MachineSentenceCodes φ) :
    ∃ N, ∀ n ≥ N, bliHistory Q 𝓜 sk c n (φ n) = ratHistory Q n (φ n) := by
  obtain ⟨N, hN⟩ := machineSentenceCodes_eventually_small h
  exact ⟨N, fun n hn => bli_small c sk Q n (φ n) (mem_smallSet.mpr (hN n hn))⟩

/-- **(b)** On a machine-named family, `𝐏` and the base are asymptotically equal.
Source: [[bli-program]] §4 row L7; mandate target 10(b)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bliHistory_asympEq_base (φ : ℕ → Sentence) (h : MachineSentenceCodes φ) :
    (fun n => bliHistory Q 𝓜 sk c n (φ n)) ≈ₙ fun n => ratHistory Q n (φ n) := by
  obtain ⟨N, hN⟩ := bliHistory_eventually_eq_on_machineSentenceCodes Q 𝓜 sk c φ h
  unfold AsympEq
  refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
  rw [EventuallyEq, eventually_atTop]
  exact ⟨N, fun n hn => by
    show (0 : ℝ) = bliHistory Q 𝓜 sk c n (φ n) - ratHistory Q n (φ n)
    rw [hN n hn, sub_self]⟩

/-- A sentence is small on every day at or after its token size (`n ≤ 2^(2^n)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallOn_of_tokenSize_le {n : ℕ} {ψ : Sentence} (h : tokenSize ψ ≤ n) : SmallOn n ψ := by
  unfold SmallOn sizeBound
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self (n := n)
  have h2 : 2 ^ n < 2 ^ (2 ^ n) := Nat.lt_two_pow_self (n := 2 ^ n)
  omega

/-- **(c)** The limiting belief (FAF's `limsup`) of `𝐏` at a fixed sentence is the base's: the
sentence is small from day `tokenSize ψ` on.
Source: [[bli-program]] §4 row L7; mandate target 10(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem limitingBelief_bliHistory_eq (ψ : Sentence) :
    limitingBelief (bliHistory Q 𝓜 sk c) ψ = limitingBelief (ratHistory Q) ψ := by
  unfold limitingBelief
  apply limsup_congr
  rw [eventually_atTop]
  exact ⟨tokenSize ψ, fun n hn =>
    bli_small c sk Q n ψ (mem_smallSet.mpr (smallOn_of_tokenSize_le hn))⟩

/-- **(d)** FAF's `lic_provind_true` conclusion for `𝐏` on a machine-named family is the same
statement as for the base.
Source: [[bli-program]] §4 row L7; mandate target 10(d)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bliHistory_provind_iff_base (φ : ℕ → Sentence) (h : MachineSentenceCodes φ) :
    ((fun n => bliHistory Q 𝓜 sk c n (φ n)) ≈ₙ fun _ => (1 : ℝ)) ↔
      ((fun n => ratHistory Q n (φ n)) ≈ₙ fun _ => (1 : ℝ)) :=
  ⟨fun hP => (bliHistory_asympEq_base Q 𝓜 sk c φ h).symm.trans hP,
    fun hQ => (bliHistory_asympEq_base Q 𝓜 sk c φ h).trans hQ⟩

/-- **(d), the worked transport**: FAF's `lic_provind_true` (provable sentences of a
machine-named family are priced `→ 1`) holds for `𝐏` **from the base's inductor instance
alone** — L2 is not needed. This is the honest content of L7: on everything an e.c. trader can
name, `𝐏` is `Q`, and FAF's §4 is about `Q`.
Source: FAF `lic_provind_true` (`Properties/AffineCoherence.lean`); [[bli-program]] §4 row L7; mandate target 10(d)
Kind: L
Fidelity: exact (transport)
Hyps: (a) the base's inductor instance and FAF's hypotheses `hthm`, `hworld` -/
theorem lic_provind_true_bliHistory_of_base (DP : DeductiveProcess)
    [IsLogicalInductor (ratHistory Q) DP] (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (φ n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => bliHistory Q 𝓜 sk c n (φ n)) ≈ₙ fun _ => (1 : ℝ) :=
  (bliHistory_provind_iff_base Q 𝓜 sk c φ hφ).mpr
    (lic_provind_true (ratHistory Q) DP φ hφ hthm hworld)

/-! ## (e): where the inclusion stops -/

/-- The product face of a table is nonempty: the `0/1` table copying the `1`s of `t` on the old
coordinates and `0` elsewhere.
Source: none: infrastructure
Kind: N+
Fidelity: n/a -/
lemma exists_mem_faceProd (m : ℕ) (t : Table smallIndex m) :
    ∃ A, A ∈ faceProd smallIndex 𝓜.d m t := by
  refine ⟨fun ψ => if h : ψ.1 ∈ smallIndex.S m then (if t ⟨ψ.1, h⟩ = 1 then 1 else 0) else 0, ?_⟩
  rw [mem_faceProd_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_grid_iff]
    intro ψ
    split_ifs
    · exact one_mem_gridVals (𝓜.d_pos _)
    · exact zero_mem_gridVals _
    · exact zero_mem_gridVals _
  · rintro ⟨φ, hφ⟩ h01
    rw [Table.restrict_apply]
    split_ifs with h1 h2
    · exact h2.symm
    · rcases h01 with h0 | h1'
      · exact h0.symm
      · exact absurd h1' h2
    · exact absurd hφ h1
    · exact absurd hφ h1

/-- **No e.c. trader names the next-day state family**: for any choice of candidate codes
`q (n+1) ∈ c.states (n+1)`, the family `n ↦ ⌜𝑸_{n+1} = q (n+1)⌝` is not `MachineSentenceCodes`
(its members are large on their own day, `stateAtom_large`).
Source: `bli-found` `not_machineSentenceCodes_stateAtom`; mandate target 10(e)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_machineSentenceCodes_nextStateAtoms (q : ℕ → ℕ)
    (hq : ∀ n, q (n + 1) ∈ c.states (n + 1)) :
    ¬ MachineSentenceCodes (fun n => stateAtom (n + 1) (q (n + 1))) := by
  intro h
  obtain ⟨N, hN⟩ := machineSentenceCodes_eventually_small h
  exact stateAtom_large (c.large_of_mem (hq N)) N (Nat.le_succ N) (hN N le_rfl)

/-- **`𝐏` charges a face point's atom on every day.**
Source: `bli-trajectory` `bliHistory_tent_nonDegenerate`; mandate target 10(e)
Kind: N+
Fidelity: n/a
Hyps: (a) `hQ` -/
theorem bliHistory_pos_on_face (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) :
    ∃ A ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex Q n),
      0 < bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A)) := by
  obtain ⟨A, hA⟩ := exists_mem_faceProd 𝓜 n (actualTable smallIndex Q n)
  refine ⟨A, hA, ?_⟩
  have := bliHistory_tent_nonDegenerate c Q hQ n A hA
  unfold bliHistory
  exact_mod_cast this

/-- **Where L7 stops, dichotomy form** (unconditional): on every day `n`, either `𝐏` and the base
disagree on some day-`(n+1)` candidate atom, or the base already distributes total mass one over
the day-`(n+1)` candidates (as `𝐏` does, `E5`). The second disjunct is a strong condition on a base
that knows nothing of the state algebra. This is `E5` for `𝐏` plus a case split — plumbing about
an arbitrary base, not a witness (regraded `L` in repair round 1; the N+ is
`bliHistory_pos_on_face` + `not_machineSentenceCodes_nextStateAtoms`, and for FAF's LIA
`Lia.lean`'s `bliHistory_ne_lia_from`).
Source: bli-slides-040 (i); [[bli-program]] §4 row L7; mandate target 10(e)
Kind: L
Fidelity: variant: dichotomy (the "≠ on every day" needs a hypothesis on the base, below)
Hyps: (a) none -/
theorem bliHistory_ne_base_on_stateAtoms_dichotomy (n : ℕ) :
    (∃ q ∈ c.states (n + 1),
        bliHistory Q 𝓜 sk c n (stateAtom (n + 1) q) ≠ ratHistory Q n (stateAtom (n + 1) q)) ∨
      ∑ q ∈ c.states (n + 1), Q n (stateAtom (n + 1) q) = 1 := by
  by_cases h : ∃ q ∈ c.states (n + 1),
      bliHistory Q 𝓜 sk c n (stateAtom (n + 1) q) ≠ ratHistory Q n (stateAtom (n + 1) q)
  · exact Or.inl h
  · right
    push Not at h
    have hE5 := (bli_partition c sk Q n).1
    rw [bliStateSystem_states] at hE5
    rw [Finset.sum_congr rfl (fun q hq => h q hq)] at hE5
    unfold ratHistory at hE5
    exact_mod_cast hE5

/-- **Where L7 stops, outright**: if the base prices some face point's day-`(n+1)` atom `0` on day
`n` (named hypothesis `hzero`), `𝐏 ≠ Q` there — `𝐏` charges every face point. The family
`n ↦ ⌜𝑸_{n+1} = code (A_n)⌝` so obtained is one no e.c. trader names
(`not_machineSentenceCodes_nextStateAtoms`). Conditional on the named `hzero`, so a composition,
not a witness (regraded `C` in repair round 1); `hzero` is discharged for FAF's LIA over
`paperDP 𝗜𝚺₁` from `bli-overlay`'s `N₀` on (`Lia.lean`'s `bliHistory_ne_lia_from`).
Source: bli-slides-040 (i); [[bli-program]] §4 row L7; mandate target 10(e)
Kind: C
Fidelity: exact under `hzero`
Hyps: (a) `hQ`; `hzero` named (true for a base that quotes `0` off a finite support, e.g. FAF's LIA at an atom off its day-`n` support — `Lia.lean`) -/
theorem bliHistory_ne_base_on_stateAtoms_of_zero (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ)
    (hzero : ∃ A ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex Q n),
      Q n (stateAtom (n + 1) (c.code (n + 1) A)) = 0) :
    ∃ A ∈ faceProd smallIndex 𝓜.d n (actualTable smallIndex Q n),
      bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A)) ≠
        ratHistory Q n (stateAtom (n + 1) (c.code (n + 1) A)) := by
  obtain ⟨A, hA, h0⟩ := hzero
  refine ⟨A, hA, ?_⟩
  have hpos := bliHistory_tent_nonDegenerate c Q hQ n A hA
  unfold bliHistory ratHistory
  rw [h0]
  intro h
  have : bliPrice Q 𝓜 (tentSkeleton smallIndex 𝓜) c n (stateAtom (n + 1) (c.code (n + 1) A)) = 0 := by
    exact_mod_cast h
  exact absurd this (ne_of_gt hpos)

/-! ## §2.5's "learns" half: the settled state atom is driven to `1` -/

/-- **`𝐏` drives the settled state atom to `1`** — the "learns" half of [[bli-program]] §2.5's
"under the B2 encoding the state sentence is a decidable claim the base itself prices and learns",
stated for `𝐏`. If the base is a logical inductor over the state-learning process
`bliDP DP states actual` whose realized states are this base's own rounded states (`StateLearns`),
and every stage of the process has a consistent world, then for every day `m` the price `𝐏` puts
on the realized state atom `⌜𝑸_m = actual m⌝` tends to `1`. Composition: the constant family is
machine-named (`MachineSentenceCodes.const`); every world consistent with the process's theory
holds the atom (`bliDP_exclusive` at stage `m + 1`, with `actual m ∈ states m` from
`StateLearns`); FAF's `lic_provind_true` for the base; and the transport (d) to `𝐏`. Together
with `bliDP_settles_states` (the process settles it) and `bliHistory_pastStateAtom` (`𝐏` prices
it by the base on later days) this is §2.5's sentence. The inductor instance over `bliDP …` is a
hypothesis: none is constructed in this package (`actualFix` is noncomputable as defined).
Source: [[bli-program]] §2.5; mandate target 9(b); FAF `lic_provind_true`
Kind: C
Fidelity: exact for the stated hypotheses
Hyps: (a) the inductor instance over `bliDP DP states actual` (named; not instantiated here), `StateLearns` named, `hworld` (at `paperDP T`: `bliDP_paperDP_hworld`) -/
theorem bliHistory_stateAtom_tendsto_one_of_stateLearns (DP : DeductiveProcess)
    (states : ℕ → Finset ℕ) (actual : ℕ → ℕ)
    [IsLogicalInductor (ratHistory Q) (bliDP DP states actual)]
    (h : StateLearns Q 𝓜 c states actual)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((bliDP DP states actual).D n)) (m : ℕ) :
    (fun n => bliHistory Q 𝓜 sk c n (stateAtom m (actual m))) ≈ₙ fun _ => (1 : ℝ) := by
  have hmem : actual m ∈ states m := by
    rw [h.1 m, h.2 m]
    exact (bliStateSystem Q 𝓜 c).actual_mem m
  exact lic_provind_true_bliHistory_of_base Q 𝓜 sk c (bliDP DP states actual)
    (fun _ => stateAtom m (actual m)) (MachineSentenceCodes.const _)
    (fun _ v hv => (bliDP_exclusive DP states actual (hv (m + 1)) m (Nat.lt_succ_self m)
      (actual m) hmem).mpr rfl)
    hworld

end

end Cleanroom.Bli.BliAssemble
