import Cleanroom.Bli.BliAssemble.Process
import LogicalInduction.Construction.LIA

/-!
# `bli-assemble` · Fixpoint: the self-consistent state-learning instance (target 9(c))

The B2 existence question seen from here (`bli-linkage` K5/K7): is there a realized-state
sequence `actual` such that FAF's LIA over the state-learning process
`bliDP DP c.states actual` learns **its own** rounded states — `StateLearns` for its own
`liaQuote`? A fixpoint in `actual`. It exists, for **every** deductive process `DP`, by strong
recursion on the day, because of two locality facts:

* `liaStates_eq_of_eq_prefix` — FAF's LIA at day `k` depends on the deductive process only
  through its stages `≤ k`: by strong induction on `k`, the past is the same by induction and the
  trading firm's day-`k` strategy depends on stages `≤ k` only (FAF's
  `TradingFirmAtFromStages_eq_of_eq_prefix`); the market maker sees the strategy and the past.
* `bliDP_D_eq_of_eq_prefix` — stage `s` of `bliDP DP states actual` depends on `actual m` for
  `m < s` only (`stateEntries` is a `biUnion` over `range s`).

`actualFix` is built from approximants `approx m` (the realized states on days `< m`, `0`
elsewhere); `actualFix_spec` is the fixpoint equation, and `exists_stateLearns_fixpoint` the
existence. Day `m`'s state is read off the LIA's day-`m` quote over the process built from the
days before it, which is the LIA's day-`m` quote over the process built from the whole `actualFix`.

Sources: [[bli-program]] §2.5 (B2 encoding); mandate target 9(c); FAF `Construction/LIA.lean`,
`Construction/TradingFirm.lean` (`TradingFirmAtFromStages_eq_of_eq_prefix`).
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory

open Classical

noncomputable section

/-! ## Locality of the state-learning process in `actual` -/

/-- Stage `s` of the state schedule reads `actual` on days `< s` only.
Source: none: infrastructure (`bli-found` `stateEntries`)
Kind: L
Fidelity: n/a -/
lemma stateEntries_eq_of_eq_prefix (states : ℕ → Finset ℕ) {a a' : ℕ → ℕ} {s : ℕ}
    (h : ∀ m < s, a m = a' m) : stateEntries states a s = stateEntries states a' s := by
  unfold stateEntries
  apply Finset.biUnion_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  rw [h m hm]

/-- Stage `s` of `bliDP DP states actual` depends on `actual` on days `< s` only.
Source: none: infrastructure (`bli-found` `bliDP_D`)
Kind: L
Fidelity: n/a -/
lemma bliDP_D_eq_of_eq_prefix (DP : DeductiveProcess) (states : ℕ → Finset ℕ) {a a' : ℕ → ℕ}
    {s : ℕ} (h : ∀ m < s, a m = a' m) :
    (bliDP DP states a).D s = (bliDP DP states a').D s := by
  rw [bliDP_D, bliDP_D, stateEntries_eq_of_eq_prefix states h]

/-! ## Locality of FAF's LIA in the deductive process -/

/-- **FAF's LIA at day `k` depends on the deductive process only through its stages `≤ k`.**
Strong induction on `k`: the past (days `< k`) agrees by induction, and the trading firm's
day-`k` strategy depends on stages `≤ k` only (`TradingFirmAtFromStages_eq_of_eq_prefix`); the
market maker reads the strategy and the past.
Source: FAF `Construction/LIA.lean` (`liaStates`), `Construction/TradingFirm.lean` (`TradingFirmAtFromStages_eq_of_eq_prefix`); mandate target 9(c) ("the day-locality of `liaStates`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem liaStates_eq_of_eq_prefix (DP₁ DP₂ : DeductiveProcess) :
    ∀ k, (∀ m ≤ k, DP₁.D m = DP₂.D m) → liaStates DP₁ k = liaStates DP₂ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hD
    have hpast : (List.ofFn fun i : Fin k => liaStates DP₁ i) =
        List.ofFn fun i : Fin k => liaStates DP₂ i := by
      congr 1
      funext i
      exact ih i i.isLt (fun m hm => hD m (hm.trans i.isLt.le))
    rw [liaStates.eq_1 DP₁ k, liaStates.eq_1 DP₂ k, hpast]
    congr 1
    show TradingFirmAt DP₁ _ k = TradingFirmAt DP₂ _ k
    rw [← TradingFirmAtFromStages_eq_of_eq_prefix DP₁ DP₁.D _ k (fun _ _ => rfl),
      ← TradingFirmAtFromStages_eq_of_eq_prefix DP₂ DP₁.D _ k hD]

/-! ## The fixpoint -/

variable (𝓜 : Mesh) (c : StateCoding 𝓜) (DP : DeductiveProcess)

/-- One step: the day-`m` realized state read off the LIA over the process built from `prev`.
Source: mandate target 9(c)
Kind: D
Fidelity: n/a -/
def fixStep (prev : ℕ → ℕ) (m : ℕ) : ℕ :=
  c.code m (actualState smallIndex 𝓜.d (liaQuote (bliDP DP c.states prev)) m)

/-- The approximants: `approx m` carries the realized states of days `< m` (`0` elsewhere).
Source: mandate target 9(c)
Kind: D
Fidelity: n/a -/
def approx : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, j => if j = m then fixStep 𝓜 c DP (approx m) m else approx m j

/-- **The self-consistent realized-state sequence.**
Source: mandate target 9(c)
Kind: D
Fidelity: n/a -/
def actualFix (m : ℕ) : ℕ := approx 𝓜 c DP (m + 1) m

/-- The approximants are stable: `approx m` agrees with `actualFix` on days `< m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma approx_eq_actualFix (m : ℕ) : ∀ j < m, approx 𝓜 c DP m j = actualFix 𝓜 c DP j := by
  induction m with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    intro j hj
    by_cases hjm : j = m
    · subst hjm; rfl
    · have h : approx 𝓜 c DP (m + 1) j = approx 𝓜 c DP m j := by
        simp [approx, hjm]
      rw [h]
      exact ih j (by omega)

/-- The LIA over the `m`-th approximant agrees with the LIA over `actualFix` up to day `m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma liaStates_approx (m : ℕ) : ∀ k ≤ m,
    liaStates (bliDP DP c.states (approx 𝓜 c DP m)) k =
      liaStates (bliDP DP c.states (actualFix 𝓜 c DP)) k := by
  intro k hk
  apply liaStates_eq_of_eq_prefix
  intro s hs
  apply bliDP_D_eq_of_eq_prefix
  intro j hj
  exact approx_eq_actualFix 𝓜 c DP m j (by omega)

/-- The rounded actual table of day `m` depends on the history at day `m` only.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualState_congr {𝒮 : SmallIndex} (d : ℕ → ℕ) {Q Q' : RatHistory} {m : ℕ}
    (h : ∀ φ, Q m φ = Q' m φ) : actualState 𝒮 d Q m = actualState 𝒮 d Q' m := by
  unfold actualState Cleanroom.Bli.BliFinite.actualTable
  congr 1
  funext φ
  exact h φ.1

/-- **The fixpoint equation**: `actualFix m` is the code of the rounded day-`m` actual table of
the LIA over the process built from `actualFix` itself.
Source: mandate target 9(c)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem actualFix_spec (m : ℕ) :
    actualFix 𝓜 c DP m =
      c.code m (actualState smallIndex 𝓜.d (liaQuote (bliDP DP c.states (actualFix 𝓜 c DP))) m) := by
  have hq : ∀ φ, liaQuote (bliDP DP c.states (approx 𝓜 c DP m)) m φ =
      liaQuote (bliDP DP c.states (actualFix 𝓜 c DP)) m φ := by
    intro φ
    simp only [liaQuote]
    rw [liaStates_approx 𝓜 c DP m m le_rfl]
  have hstep : actualFix 𝓜 c DP m = fixStep 𝓜 c DP (approx 𝓜 c DP m) m := by
    unfold actualFix
    simp only [approx, ↓reduceIte]
  rw [hstep]
  unfold fixStep
  rw [actualState_congr 𝓜.d hq]

/-- **The self-consistent state-learning instance exists, for every deductive process**
(target 9(c), `bli-linkage`'s B2 existence K5/K7 seen from here): `actualFix` makes the LIA over
`bliDP DP c.states actualFix` learn its own rounded states.
Source: [[bli-program]] §2.5 (B2 encoding); mandate target 9(c)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_stateLearns_fixpoint :
    ∃ actual : ℕ → ℕ, StateLearns (liaQuote (bliDP DP c.states actual)) 𝓜 c c.states actual :=
  ⟨actualFix 𝓜 c DP, fun _ => rfl, fun m => actualFix_spec 𝓜 c DP m⟩

end

end Cleanroom.Bli.BliAssemble
