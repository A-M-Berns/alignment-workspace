import Cleanroom.Bli.BliAssemble.Headline

/-!
# `bli-assemble` · Process: the corollary over `bliDP` (target 9)

* (a) `bliHistory_isLogicalInductor_bliDP` — L2's row of record at `bli-found`'s state-learning
  process `bliDP DP states actual`: an instance of `bliHistory_isLogicalInductor_of` (`L`, said so).
  Non-vacuity of the process: `bliDP_paperDP_hworld` (every stage of `bliDP (paperDP 𝗜𝚺₁) …` has
  a consistent world) — cited in the docstring and conjoined in `Lia.lean`'s witness.
* (b) `StateLearns` — the self-consistency predicate: the process's candidate sets are the
  coding's, and its realized states are **this base's** rounded actual tables
  (`(bliStateSystem Q 𝓜 c).actual m = c.code m (actualState …)`), the table-level tie
  `bli-found`'s `RoundsOf` makes. Under it, `bliDP_settles_states`: every world consistent with a
  stage `s` of `bliDP` holds the day-`m < s` state atom `⌜𝑸_m = q⌝` iff `q` is the base's realized
  day-`m` state (a rewrite of `bliDP_exclusive`, `L`). And `bliHistory_pastStateAtom`: a past
  state atom (`m ≤ n`) is Tier B at day `n`, so `𝐏` prices it by the base (`L`; Known issue 9).
  This is the honest reading of [[bli-program]] §2.5's "under the B2 encoding the state sentence
  is a decidable claim the base itself prices and learns": the process settles it, the base
  prices it, and `𝐏` copies the base there — the convergence of the base's price to the settled
  truth value is FAF's `lic_provind`-type business on the base, not a claim of this package.
* (c) the fixpoint in `actual` for the LIA's own `liaQuote` is **proved** in `Fixpoint.lean`
  (`liaStates_eq_of_eq_prefix`, the day-locality of FAF's LIA in the deductive process, and
  `exists_stateLearns_fixpoint` by strong recursion), and instantiated at `paperDP 𝗜𝚺₁` in
  `Lia.lean`. It is the self-consistent state-learning process of [[bli-program]] §2.5's B2
  encoding — not `bli-linkage`'s K5 (linked superbelief, bracket balance), which it does not touch.
  The "learns" half of §2.5's sentence — `𝐏` drives the settled state atom to `1` — is
  `Inherit.lean`'s `bliHistory_stateAtom_tendsto_one_of_stateLearns` (repair round 1), under an
  inductor instance over `bliDP …` that this package does not construct.

Sources: [[bli-program]] §2.5, §7 item 4; mandate target 9.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

/-! ## (a) L2 over the state-learning process -/

/-- **L2 over `bliDP`** (target 9(a)): the row of record at the process `bliDP DP states actual`.
Trivially an instance of `bliHistory_isLogicalInductor_of` — the process is a parameter there.
Non-vacuity of the process is `bli-found`'s `bliDP_paperDP_hworld` (a conjunct of `Lia.lean`'s
witness), not a side remark.
Source: [[bli-program]] §2.5, §7 item 4; mandate target 9(a)
Kind: L
Fidelity: exact
Hyps: (a) the inductor instance over `bliDP`; `C`, `hov` named (OPEN at `dyadicMesh`/`writeOutCoding`) -/
theorem bliHistory_isLogicalInductor_bliDP (Q : RatHistory) (DP : DeductiveProcess)
    (states : ℕ → Finset ℕ) (actual : ℕ → ℕ) (𝓜 : Mesh) (c : StateCoding 𝓜)
    [IsLogicalInductor (ratHistory Q) (bliDP DP states actual)]
    (C : SpliceCertificate (tentExprMap 𝓜 c))
    (hov : ComputableTable (bliOv Q 𝓜 (tentSkeleton smallIndex 𝓜) c)) :
    IsLogicalInductor (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) (bliDP DP states actual) :=
  bliHistory_isLogicalInductor_of Q (bliDP DP states actual) 𝓜 c C hov

/-! ## (b) Self-consistency: the process learns this base's states -/

/-- **`StateLearns Q 𝓜 c states actual`**: the process's day-`m` candidates are the coding's
candidate codes, and its realized day-`m` state is the code of **this base's** rounded actual
table — `(bliStateSystem Q 𝓜 c).actual m = c.code m (roundTo (𝓜.d m) (actualTable smallIndex Q m))`.
The table-level tie `bli-found`'s `RoundsOf` makes, at the level of the process.
Source: [[bli-program]] §2.5 (B2 encoding); mandate target 9(b)
Kind: D
Fidelity: exact -/
def StateLearns (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜) (states : ℕ → Finset ℕ)
    (actual : ℕ → ℕ) : Prop :=
  (∀ m, states m = c.states m) ∧ ∀ m, actual m = (bliStateSystem Q 𝓜 c).actual m

/-- **The process settles each past state atom at the base's realized state**: under
`StateLearns`, every world consistent with stage `s` of `bliDP DP states actual` holds
`⌜𝑸_m = q⌝` (for `m < s`, `q` a candidate) iff `q` is the base's realized day-`m` state. A
rewrite of `bli-found`'s `bliDP_exclusive`.
Source: [[bli-program]] §2.5; mandate target 9(b)
Kind: L
Fidelity: exact
Hyps: (a) `h : StateLearns …` (the self-consistency predicate, named) -/
theorem bliDP_settles_states (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜)
    (DP : DeductiveProcess) (states : ℕ → Finset ℕ) (actual : ℕ → ℕ)
    (h : StateLearns Q 𝓜 c states actual) {v : PCWorld} {s : ℕ}
    (hv : v.ConsistentWith ((bliDP DP states actual).D s)) :
    ∀ m < s, ∀ q ∈ c.states m,
      (v.Holds (stateAtom m q) ↔ q = (bliStateSystem Q 𝓜 c).actual m) := by
  intro m hm q hq
  rw [← h.2 m]
  exact bliDP_exclusive DP states actual hv m hm q ((h.1 m).symm ▸ hq)

/-- A past state atom (`m ≤ n`) is Tier B at day `n`: `parse` sees no future atom, so the chain
is empty.
Source: [[bli-program]] §2.5 (past state atoms are Tier B); mandate Known issue 9
Kind: L
Fidelity: n/a -/
lemma tierA_pastStateAtom {𝓜 : Mesh} (c : StateCoding 𝓜) {m n q : ℕ} (hmn : m ≤ n) :
    tierA c n (stateAtom m q) = none := by
  rw [stateAtom_eq_atom]
  simp [tierA, parse, futureStateAtom, not_lt.mpr hmn]

/-- **`𝐏` prices a past state atom by the base** (`m ≤ n`): small-first if it is small on day
`n`, Tier B otherwise. So the state sentence the process settles is priced by `Q` on every later
day, exactly as [[bli-program]] §2.5 reads it; whether `Q`'s price converges to the settled truth
value is a §4-type question about the base.
Source: [[bli-program]] §2.5; mandate target 9(b), Known issue 9
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bliHistory_pastStateAtom (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d)
    (c : StateCoding 𝓜) {m n q : ℕ} (hmn : m ≤ n) :
    bliHistory Q 𝓜 sk c n (stateAtom m q) = ratHistory Q n (stateAtom m q) := by
  unfold bliHistory ratHistory
  by_cases hs : SmallOn n (stateAtom m q)
  · rw [bliPrice_of_small hs]
  · rw [bliPrice_of_tierB hs (tierA_pastStateAtom c hmn)]

end

end Cleanroom.Bli.BliAssemble
