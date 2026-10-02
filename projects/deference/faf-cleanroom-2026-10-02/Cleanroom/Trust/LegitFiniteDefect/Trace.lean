import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Trace non-recoverability

Package `legit-finite-defect`, Target 7 (items 050, 051), re-found over `ℚ` with no frame and no
dependency import. A finite, four-day rational dynamical class: the human's realised opinion is the
convex combination `run S n = (1 − β n) · h n + β n · a n` of its autonomous verdict `h n` and the
advisor's quote `a n`; the observable **trace** is the record of quotes and realised feedback; the
**defect** `d S` is the distance between the terminal opinion and its advisor-free counterfactual
(the same system run with `β ≡ 0`). Two valid systems with identical traces have defects `0` and
`1/2`; hence no function of the trace (any codomain) recovers the defect or the legitimacy
predicate — a two-point non-identifiability (∀ gates, ∃ pair), the finite shadow of v6 §6.3's
"the record cannot reveal it". **Not an LI theorem**: horizon 4, rational streams, arbitrary
set-functions as gates; the LI-register version is `legit-li-register`'s open item.

The stretch (`IdentifiedSet`) upgrades the two-point statement: for *every* valid system whose
terminal opinion is interior, the trace is consistent with a faithful system (defect `0`) and with
a steered one attaining the maximal trace-consistent defect `D`, and every trace-consistent valid
system has defect `≤ D` — so no valid trace with an interior terminal opinion identifies
legitimacy.

Round 3 never had a verification phase (inventory header); this is the first check of items
050–051's numbers. All agree with the self-report.
-/

namespace Cleanroom.Trust.LegitFiniteDefect.Trace

/-- A system of the declared rule class: latent autonomous verdict stream `h`, latent influence
map `β`, published quote stream `a`. Only days `0..3` are ever read.
Source: [[trace-nonrecoverability]] §1.1; trust-lab-050
Kind: D
Fidelity: exact -/
structure Sys where
  /-- the human's autonomous day-`n` verdict (latent) -/
  h : ℕ → ℚ
  /-- the influence weight with which the human adopts the quote on day `n` (latent) -/
  β : ℕ → ℚ
  /-- the advisor's published quote (observable) -/
  a : ℕ → ℚ

/-- Run semantics: the human's realised day-`n` opinion, the convex combination of its
autonomous verdict and the adopted quote. It is what the human publishes as feedback.
Source: [[trace-nonrecoverability]] §1.1; trust-lab-050
Kind: D
Fidelity: exact -/
def run (S : Sys) (n : ℕ) : ℚ := (1 - S.β n) * S.h n + S.β n * S.a n

/-- The observable trace: every published quote and every realised feedback value over the
horizon — everything the declared observer sees.
Source: [[trace-nonrecoverability]] §1.1; trust-lab-050
Kind: D
Fidelity: exact -/
def trace (S : Sys) : List (ℚ × ℚ) :=
  [(S.a 0, run S 0), (S.a 1, run S 1), (S.a 2, run S 2), (S.a 3, run S 3)]

/-- The advisor-free counterfactual: the same system with the influence map zeroed (the only
advisor-to-human channel in the class).
Source: [[trace-nonrecoverability]] §1.1; trust-lab-050
Kind: D
Fidelity: exact -/
def Afree (S : Sys) : Sys := { S with β := fun _ => 0 }

/-- The advisor-free run is the autonomous verdict.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem run_Afree (S : Sys) (n : ℕ) : run (Afree S) n = S.h n := by
  simp [run, Afree]

/-- The legitimacy defect of a system: distance between the terminal realised opinion and the
terminal advisor-free counterfactual opinion, computed by running the advisor-free system.
Source: [[trace-nonrecoverability]] §1.1; trust-lab-050
Kind: D
Fidelity: exact -/
def d (S : Sys) : ℚ := |run S 3 - run (Afree S) 3|

/-- Class membership: all three streams take values in `[0, 1]` on the horizon.
Source: [[trace-nonrecoverability]] §1.1; trust-lab-050
Kind: D
Fidelity: exact -/
def Valid (S : Sys) : Prop :=
  ∀ n < 4, (0 ≤ S.h n ∧ S.h n ≤ 1) ∧ (0 ≤ S.β n ∧ S.β n ≤ 1) ∧ (0 ≤ S.a n ∧ S.a n ≤ 1)

/-- A valid system's realised opinions lie in `[0, 1]` (convex combinations).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem run_mem_of_valid {S : Sys} (hS : Valid S) {n : ℕ} (hn : n < 4) :
    0 ≤ run S n ∧ run S n ≤ 1 := by
  obtain ⟨⟨h0, h1⟩, ⟨b0, b1⟩, ⟨a0, a1⟩⟩ := hS n hn
  unfold run
  constructor <;> nlinarith [mul_nonneg b0 a0, mul_nonneg (sub_nonneg.2 b1) h0]

/-! ## The two systems -/

/-- Autonomous verdicts of the faithful human: `1/2 → 5/8 → 3/4 → 3/4`.
Source: [[trace-nonrecoverability]] §1.2
Kind: D
Fidelity: exact -/
def hFaith : ℕ → ℚ := fun n => if n = 0 then 1 / 2 else if n = 1 then 5 / 8 else 3 / 4

/-- Autonomous verdicts of the steered human: would have gone `1/2 → 3/8 → 1/4 → 1/4`.
Source: [[trace-nonrecoverability]] §1.2
Kind: D
Fidelity: exact -/
def hSteer : ℕ → ℚ := fun n => if n = 0 then 1 / 2 else if n = 1 then 3 / 8 else 1 / 4

/-- The advisor's quotes (identical in both systems).
Source: [[trace-nonrecoverability]] §1.2
Kind: D
Fidelity: exact -/
def quote : ℕ → ℚ := fun n => if n = 0 then 1 / 2 else if n = 1 then 5 / 8 else 3 / 4

/-- `S1`, faithful: uninfluenced human (`β ≡ 0`), advisor tracks it.
Source: [[trace-nonrecoverability]] §1.2
Kind: D
Fidelity: exact -/
def S1 : Sys := ⟨hFaith, fun _ => 0, quote⟩

/-- `S2`, steered: the human adopts the quotes (`β ≡ 1`); its own deliberation would have gone
elsewhere.
Source: [[trace-nonrecoverability]] §1.2
Kind: D
Fidelity: exact -/
def S2 : Sys := ⟨hSteer, fun _ => 1, quote⟩

/-- Both systems are members of the declared class, and their latent parameters differ.
Source: [[trace-nonrecoverability]] §1.3 (`valid_S1`, `valid_S2`, `latents_differ`)
Kind: N+
Fidelity: exact -/
theorem valid_and_differ :
    Valid S1 ∧ Valid S2 ∧ S1.h 3 ≠ S2.h 3 ∧ S1.β 3 ≠ S2.β 3 := by
  refine ⟨fun n hn => ?_, fun n hn => ?_, ?_, ?_⟩
  · interval_cases n <;> norm_num [S1, hFaith, quote]
  · interval_cases n <;> norm_num [S2, hSteer, quote]
  · norm_num [S1, S2, hFaith, hSteer]
  · norm_num [S1, S2]

/-- **The traces are computed equal** — the shared record is
`[(1/2, 1/2), (5/8, 5/8), (3/4, 3/4), (3/4, 3/4)]`, showing perfect apparent tracking either way.
Source: [[trace-nonrecoverability]] §1.3 (i) (`trace_eq`, `trace_S1_val`, `perfect_tracking_*`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem trace_eq :
    trace S1 = trace S2 ∧
      trace S1 = [(1 / 2, 1 / 2), (5 / 8, 5 / 8), (3 / 4, 3 / 4), (3 / 4, 3 / 4)] ∧
      ∀ p ∈ trace S1, p.1 = p.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [trace, run, S1, S2, hFaith, hSteer, quote]

/-- **The defects differ**: `d S1 = 0`, `d S2 = 1/2`, through the computed counterfactual.
Source: [[trace-nonrecoverability]] §1.3 (ii)–(iii) (`d_S1`, `d_S2`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem d_pair : d S1 = 0 ∧ d S2 = 1 / 2 := by
  constructor
  · have h0 : run S1 3 - run (Afree S1) 3 = 0 := by norm_num [run, Afree, S1, hFaith, quote]
    unfold d; rw [h0, abs_zero]
  · have h0 : run S2 3 - run (Afree S2) 3 = 1 / 2 := by norm_num [run, Afree, S2, hSteer, quote]
    unfold d; rw [h0, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 2)]

/-! ## The impossibility, over all gates -/

/-- **Every** function of the trace (any codomain) assigns the two systems the same value.
Source: [[trace-nonrecoverability]] §1.3 (iv) (`gate_blind`); trust-lab-050
Kind: L
Fidelity: exact (one `congrArg` from computed trace equality) -/
theorem gate_blind {α : Sort*} (ℓ : List (ℚ × ℚ) → α) : ℓ (trace S1) = ℓ (trace S2) :=
  congrArg ℓ trace_eq.1

/-- No `ℚ`-valued gate recovers the defect on the pair, and no `Bool`-valued gate equals the
legitimacy predicate `0 < d` on the pair. Two-point non-identifiability: universal over gates,
existential over systems.
Source: [[trace-nonrecoverability]] §1.3 (iv) (`no_defect_recovery`, `no_legitimacy_predicate`);
trust-lab-050
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem no_recovery :
    (¬ ∃ ℓ : List (ℚ × ℚ) → ℚ, ℓ (trace S1) = d S1 ∧ ℓ (trace S2) = d S2) ∧
      (¬ ∃ ℓ : List (ℚ × ℚ) → Bool,
        (ℓ (trace S1) = true ↔ 0 < d S1) ∧ (ℓ (trace S2) = true ↔ 0 < d S2)) := by
  obtain ⟨hd1, hd2⟩ := d_pair
  constructor
  · rintro ⟨ℓ, h1, h2⟩
    have hb := gate_blind ℓ
    rw [h1, h2, hd1, hd2] at hb
    norm_num at hb
  · rintro ⟨ℓ, h1, h2⟩
    have hb := gate_blind ℓ
    have hpos : 0 < d S2 := by rw [hd2]; norm_num
    have h2' : ℓ (trace S2) = true := h2.mpr hpos
    rw [← hb] at h2'
    have := h1.mp h2'
    rw [hd1] at this
    exact lt_irrefl _ this

/-! ## The transparency near-miss -/

/-- The enlarged record: the trace plus the influence map over the horizon.
Source: [[trace-nonrecoverability]] §1.3 (v); trust-lab-051
Kind: D
Fidelity: exact -/
def traceT (S : Sys) : List (ℚ × ℚ) × List ℚ := (trace S, [S.β 0, S.β 1, S.β 2, S.β 3])

/-- A gate on the enlarged record: "did any influence occur?".
Source: [[trace-nonrecoverability]] §1.3 (v)
Kind: D
Fidelity: exact -/
def sep (t : List (ℚ × ℚ) × List ℚ) : Bool := decide (t.2 ≠ [0, 0, 0, 0])

/-- **Transparency near-miss.** On the influence-transparent record the specification that was
unsatisfiable on the trace is satisfied by an explicit gate: unobservability of *provenance*,
not the payoffs, causes the invisibility.
Source: [[trace-nonrecoverability]] §1.3 (v) (`transparency_separates`, `transparency_gate_exists`);
trust-lab-051
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem transparency_gate_exists :
    (sep (traceT S1) = false ∧ sep (traceT S2) = true) ∧
      ∃ ℓ : List (ℚ × ℚ) × List ℚ → Bool,
        (ℓ (traceT S1) = true ↔ 0 < d S1) ∧ (ℓ (traceT S2) = true ↔ 0 < d S2) := by
  have hs : sep (traceT S1) = false ∧ sep (traceT S2) = true := by
    constructor <;> norm_num [sep, traceT, S1, S2]
  refine ⟨hs, sep, ?_, ?_⟩
  · rw [hs.1, d_pair.1]; norm_num
  · rw [hs.2, d_pair.2]; norm_num

/-- **Corruption deletion test**: zero out `S2`'s influence map and the trace equality fails (the
steered human's own deliberation surfaces at day 1: feedback `3/8 ≠ 5/8`); and any advisor-free
system has zero defect.
Source: [[trace-nonrecoverability]] §1.3 (vi) (`influence_deletion_breaks_trace`, `d_Afree`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem influence_deletion_breaks_trace :
    trace (Afree S2) ≠ trace S1 ∧ ∀ S : Sys, d (Afree S) = 0 := by
  constructor
  · norm_num [trace, run, Afree, S1, S2, hFaith, hSteer, quote]
  · intro S
    simp [d, Afree, run]

/-- **Hidden defect needs full influence.** Over the whole class (no validity needed): perfect
apparent tracking at the terminal day, `a 3 = run S 3`, forces `β 3 = 1` or `d S = 0`. So `S2`'s
`β = 1` is forced by trace-equality-with-perfect-tracking, not cherry-picked.
Source: [[trace-nonrecoverability]] §1.3 (vii) (`hidden_defect_needs_full_influence`); trust-lab-051
Kind: L
Fidelity: exact (one `linear_combination` and `mul_eq_zero` on `(1 − β₃)(a₃ − h₃) = 0`; the
inventory grades it the same way — regraded from P after audit round 1)
Hyps: (a) none beyond the tracking equation -/
theorem hidden_defect_needs_full_influence (S : Sys) (htrack : S.a 3 = run S 3) :
    S.β 3 = 1 ∨ d S = 0 := by
  have h' : S.a 3 = (1 - S.β 3) * S.h 3 + S.β 3 * S.a 3 := htrack
  have key : (1 - S.β 3) * (S.a 3 - S.h 3) = 0 := by linear_combination h'
  rcases mul_eq_zero.mp key with hβ | hah
  · left; linarith
  · right
    have hEq : S.a 3 = S.h 3 := by linarith
    have h0 : run S 3 - run (Afree S) 3 = 0 := by
      rw [run_Afree]; unfold run; rw [hEq]; ring
    unfold d; rw [h0, abs_zero]

/-- `S2` satisfies the tracking hypothesis with positive defect, so the lemma's first disjunct
fires, consistent with `S2.β 3 = 1`.
Source: [[trace-nonrecoverability]] §1.3 (`S2_tracking`)
Kind: L
Fidelity: n/a -/
theorem S2_tracking : S2.a 3 = run S2 3 := by
  norm_num [run, S2, hSteer, quote]

/-! ## Stretch: the identified set of a valid trace -/

namespace IdentifiedSet

/-- Modify a system at day `3` only: verdict `h₃`, influence `β₃`, and on days `< 3` publish the
original realised opinions as autonomous verdicts with no influence (so the trace on days `0..2`
is reproduced exactly).
Source: [[trace-nonrecoverability]] §5 strengthening (a); mandate Target 7 (stretch)
Kind: D
Fidelity: n/a -/
def modify3 (S : Sys) (h₃ β₃ : ℚ) : Sys :=
  ⟨fun n => if n = 3 then h₃ else run S n, fun n => if n = 3 then β₃ else 0, S.a⟩

/-- The modified system reproduces the original opinions on days `< 3`, and on day `3` realises
`(1 − β₃) h₃ + β₃ a₃`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem run_modify3 (S : Sys) (h₃ β₃ : ℚ) :
    (∀ n < 3, run (modify3 S h₃ β₃) n = run S n) ∧
      run (modify3 S h₃ β₃) 3 = (1 - β₃) * h₃ + β₃ * S.a 3 := by
  constructor
  · intro n hn
    have : n ≠ 3 := by omega
    simp [run, modify3, this]
  · simp [run, modify3]

/-- Trace equality pins the terminal quote and terminal opinion.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem terminal_of_trace_eq {S S' : Sys} (h : trace S' = trace S) :
    S'.a 3 = S.a 3 ∧ run S' 3 = run S 3 := by
  simp only [trace, List.cons.injEq, Prod.mk.injEq] at h
  exact h.2.2.2.1

/-- The modified system's trace equals the original iff its day-`3` opinion matches.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem trace_modify3_iff (S : Sys) (h₃ β₃ : ℚ) :
    trace (modify3 S h₃ β₃) = trace S ↔ (1 - β₃) * h₃ + β₃ * S.a 3 = run S 3 := by
  obtain ⟨hlt, h3⟩ := run_modify3 S h₃ β₃
  have ha : (modify3 S h₃ β₃).a = S.a := rfl
  constructor
  · intro h
    have := terminal_of_trace_eq h
    rw [h3] at this
    exact this.2
  · intro h
    simp [trace, ha, hlt 0 (by norm_num), hlt 1 (by norm_num), hlt 2 (by norm_num), h3, h]

/-- The modified system's defect is `|day-3 opinion − h₃|`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem d_modify3 (S : Sys) (h₃ β₃ : ℚ) :
    d (modify3 S h₃ β₃) = |(1 - β₃) * h₃ + β₃ * S.a 3 - h₃| := by
  unfold d
  rw [run_Afree, (run_modify3 S h₃ β₃).2]
  simp [modify3]

/-- The modified system is valid when the original is and `h₃, β₃ ∈ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem valid_modify3 {S : Sys} (hS : Valid S) {h₃ β₃ : ℚ} (hh : 0 ≤ h₃ ∧ h₃ ≤ 1)
    (hb : 0 ≤ β₃ ∧ β₃ ≤ 1) : Valid (modify3 S h₃ β₃) := by
  intro n hn
  obtain ⟨_, _, ha⟩ := hS n hn
  refine ⟨?_, ?_, ha⟩
  · by_cases h3 : n = 3
    · subst h3; simpa [modify3] using hh
    · simp only [modify3, h3, if_false]
      exact run_mem_of_valid hS hn
  · by_cases h3 : n = 3
    · subst h3; simpa [modify3] using hb
    · simp [modify3, h3]

/-- The maximal trace-consistent defect `D` of a system's trace, in terms of its terminal quote
`a₃` and terminal opinion `Y₃ = run S 3`: `max Y₃ (1 − Y₃)` when `a₃ = Y₃`, `Y₃` when `a₃ > Y₃`,
`1 − Y₃` when `a₃ < Y₃`.
Source: mandate Target 7 (stretch: "the exact set of trace-consistent defects `[0, D(τ)]`")
Kind: D
Fidelity: exact -/
def D (S : Sys) : ℚ :=
  if S.a 3 = run S 3 then max (run S 3) (1 - run S 3)
  else if run S 3 < S.a 3 then run S 3 else 1 - run S 3

/-- **Upper bound.** Every valid system with the same trace has defect at most `D S`.
Source: mandate Target 7 (stretch)
Kind: P
Fidelity: exact
Hyps: (a) validity of both systems, trace equality -/
theorem d_le_D {S : Sys} (hS : Valid S) {S' : Sys} (hS' : Valid S') (htr : trace S' = trace S) :
    d S' ≤ D S := by
  obtain ⟨ha, hY⟩ := terminal_of_trace_eq htr
  obtain ⟨⟨hh0, hh1⟩, ⟨hb0, hb1⟩, _⟩ := hS' 3 (by norm_num)
  have hrun : (1 - S'.β 3) * S'.h 3 + S'.β 3 * S'.a 3 = run S 3 := hY
  have hd : d S' = |run S 3 - S'.h 3| := by unfold d; rw [run_Afree, hY]
  rw [hd]
  obtain ⟨hY0, hY1⟩ := run_mem_of_valid hS (by norm_num : 3 < 4)
  unfold D
  split_ifs with h1 h2
  · rw [abs_le]
    constructor
    · linarith [le_max_right (run S 3) (1 - run S 3)]
    · linarith [le_max_left (run S 3) (1 - run S 3)]
  · -- `a₃ > Y₃`: then `h₃ ≤ Y₃`
    have hkey : (1 - S'.β 3) * (S'.h 3 - run S 3) = S'.β 3 * (run S 3 - S'.a 3) := by
      linear_combination hrun
    have hβ : S'.β 3 < 1 := by
      rcases hb1.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        rw [heq] at hkey
        rw [ha] at hkey
        have : run S 3 = S.a 3 := by linarith
        exact h1 this.symm
    have hle : S'.h 3 ≤ run S 3 := by
      rw [ha] at hkey
      have hneg : S'.β 3 * (run S 3 - S.a 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hb0 (by linarith)
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- `a₃ < Y₃`: then `h₃ ≥ Y₃`
    have h2' : S.a 3 < run S 3 := lt_of_le_of_ne (not_lt.1 h2) h1
    have hkey : (1 - S'.β 3) * (S'.h 3 - run S 3) = S'.β 3 * (run S 3 - S'.a 3) := by
      linear_combination hrun
    have hβ : S'.β 3 < 1 := by
      rcases hb1.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        rw [heq, ha] at hkey
        have : run S 3 = S.a 3 := by linarith
        exact h1 this.symm
    have hge : run S 3 ≤ S'.h 3 := by
      rw [ha] at hkey
      have hpos : 0 ≤ S'.β 3 * (run S 3 - S.a 3) := mul_nonneg hb0 (by linarith)
      nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The faithful reading exists.** Every valid system's trace is also the trace of a valid
system with zero defect (publish the realised opinions as autonomous verdicts, no influence).
Source: mandate Target 7 (stretch: `S₀`)
Kind: P
Fidelity: exact
Hyps: (a) validity -/
theorem exists_faithful {S : Sys} (hS : Valid S) :
    ∃ S₀ : Sys, Valid S₀ ∧ trace S₀ = trace S ∧ d S₀ = 0 := by
  refine ⟨modify3 S (run S 3) 0, valid_modify3 hS (run_mem_of_valid hS (by norm_num))
    ⟨le_rfl, by norm_num⟩, (trace_modify3_iff _ _ _).2 (by ring), ?_⟩
  rw [d_modify3]
  simp

/-- **The steered reading exists and attains `D`.** For every valid system whose terminal opinion
is interior (`0 < Y₃ < 1`), its trace is also the trace of a valid system with defect exactly
`D S > 0`. With `d_le_D` and `exists_faithful`: the set of trace-consistent defects reaches from
`0` to `D S`, so **no valid trace with an interior terminal opinion identifies legitimacy**.
Source: mandate Target 7 (stretch: `S₁`); [[trace-nonrecoverability]] §5 (a)
Kind: P
Fidelity: exact
Hyps: (a) validity and interiority of the terminal opinion -/
theorem exists_steered {S : Sys} (hS : Valid S) (h0 : 0 < run S 3) (h1 : run S 3 < 1) :
    0 < D S ∧ ∃ S₁ : Sys, Valid S₁ ∧ trace S₁ = trace S ∧ d S₁ = D S := by
  obtain ⟨_, _, ⟨ha0, ha1⟩⟩ := hS 3 (by norm_num)
  unfold D
  split_ifs with hA hB
  · -- `a₃ = Y₃`: full influence, verdict at the far end of `[0, 1]`
    by_cases hhalf : run S 3 ≤ 1 / 2
    · have hmax : max (run S 3) (1 - run S 3) = 1 - run S 3 := max_eq_right (by linarith)
      rw [hmax]
      refine ⟨by linarith, modify3 S 1 1, valid_modify3 hS ⟨by norm_num, le_rfl⟩
        ⟨by norm_num, le_rfl⟩, (trace_modify3_iff _ _ _).2 (by rw [hA]; ring), ?_⟩
      rw [d_modify3]
      rw [show (1 - (1 : ℚ)) * 1 + 1 * S.a 3 - 1 = S.a 3 - 1 by ring, hA]
      rw [abs_of_neg (by linarith)]
      ring
    · have hmax : max (run S 3) (1 - run S 3) = run S 3 := max_eq_left (by linarith)
      rw [hmax]
      refine ⟨h0, modify3 S 0 1, valid_modify3 hS ⟨le_rfl, by norm_num⟩
        ⟨by norm_num, le_rfl⟩, (trace_modify3_iff _ _ _).2 (by rw [hA]; ring), ?_⟩
      rw [d_modify3]
      rw [show (1 - (1 : ℚ)) * 0 + 1 * S.a 3 - 0 = S.a 3 by ring, hA]
      exact abs_of_pos h0
  · -- `a₃ > Y₃`: verdict `0`, influence `Y₃ / a₃`
    have hapos : 0 < S.a 3 := by linarith
    refine ⟨h0, modify3 S 0 (run S 3 / S.a 3), valid_modify3 hS ⟨le_rfl, by norm_num⟩
      ⟨div_nonneg h0.le hapos.le, (div_le_one hapos).2 hB.le⟩,
      (trace_modify3_iff _ _ _).2 (by rw [div_mul_cancel₀ (run S 3) hapos.ne']; ring), ?_⟩
    rw [d_modify3]
    rw [show (1 - run S 3 / S.a 3) * 0 + run S 3 / S.a 3 * S.a 3 - 0 = run S 3 by
      rw [div_mul_cancel₀ (run S 3) hapos.ne']; ring]
    exact abs_of_pos h0
  · -- `a₃ < Y₃`: verdict `1`, influence `(1 − Y₃) / (1 − a₃)`
    have hB' : S.a 3 < run S 3 := lt_of_le_of_ne (not_lt.1 hB) hA
    have h1a : 0 < 1 - S.a 3 := by linarith
    refine ⟨by linarith, modify3 S 1 ((1 - run S 3) / (1 - S.a 3)),
      valid_modify3 hS ⟨by norm_num, le_rfl⟩
        ⟨div_nonneg (by linarith) h1a.le, (div_le_one h1a).2 (by linarith)⟩,
      (trace_modify3_iff _ _ _).2 (by
        have hne : (1 - S.a 3) ≠ 0 := h1a.ne'
        field_simp
        ring), ?_⟩
    rw [d_modify3]
    have hne : (1 - S.a 3) ≠ 0 := h1a.ne'
    rw [show (1 - (1 - run S 3) / (1 - S.a 3)) * 1 + (1 - run S 3) / (1 - S.a 3) * S.a 3 - 1 =
        -(1 - run S 3) by field_simp; ring]
    rw [abs_neg, abs_of_pos (by linarith)]

/-- **Every intermediate defect is attained.** For a valid system and any `δ ∈ [0, D S]`, some
valid system with the same trace has defect exactly `δ`. Constructions, with `Y₃ = run S 3`:
when `a₃ = Y₃`, full influence `β₃ = 1` and verdict `Y₃ − δ` (if `δ ≤ Y₃`) or `Y₃ + δ` (else,
when `δ ≤ 1 − Y₃`); when `a₃ > Y₃`, verdict `Y₃ − δ` and influence `δ / (a₃ − Y₃ + δ)`; when
`a₃ < Y₃`, verdict `Y₃ + δ` and influence `δ / (Y₃ − a₃ + δ)`. Each realises `Y₃` on day `3`
(so the trace is unchanged) with `|Y₃ − h₃| = δ`.
Source: mandate Target 7 (stretch: "the exact set of trace-consistent defects `[0, D(τ)]`");
[[trace-nonrecoverability]] §5 (a); repair round 1 (push further)
Kind: P
Fidelity: exact
Hyps: (a) validity of `S`; `0 ≤ δ ≤ D S` -/
theorem exists_defect_eq {S : Sys} (hS : Valid S) {δ : ℚ} (hδ0 : 0 ≤ δ) (hδD : δ ≤ D S) :
    ∃ S' : Sys, Valid S' ∧ trace S' = trace S ∧ d S' = δ := by
  obtain ⟨_, _, ⟨ha0, ha1⟩⟩ := hS 3 (by norm_num)
  obtain ⟨hY0, hY1⟩ := run_mem_of_valid hS (by norm_num : 3 < 4)
  unfold D at hδD
  split_ifs at hδD with hA hB
  · -- `a₃ = Y₃`: full influence, verdict at distance `δ` on whichever side stays in `[0, 1]`
    by_cases hδY : δ ≤ run S 3
    · refine ⟨modify3 S (run S 3 - δ) 1,
        valid_modify3 hS ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩,
        (trace_modify3_iff _ _ _).2 (by rw [hA]; ring), ?_⟩
      rw [d_modify3, hA]
      rw [show (1 - (1 : ℚ)) * (run S 3 - δ) + 1 * run S 3 - (run S 3 - δ) = δ by ring]
      exact abs_of_nonneg hδ0
    · have hδ1 : δ ≤ 1 - run S 3 := by
        rw [not_le] at hδY
        rcases le_max_iff.1 hδD with h | h
        · exact absurd h (not_le.2 hδY)
        · exact h
      refine ⟨modify3 S (run S 3 + δ) 1,
        valid_modify3 hS ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩,
        (trace_modify3_iff _ _ _).2 (by rw [hA]; ring), ?_⟩
      rw [d_modify3, hA]
      rw [show (1 - (1 : ℚ)) * (run S 3 + δ) + 1 * run S 3 - (run S 3 + δ) = -δ by ring, abs_neg]
      exact abs_of_nonneg hδ0
  · -- `a₃ > Y₃`: `D = Y₃`; verdict `Y₃ − δ`, influence `δ / (a₃ − Y₃ + δ)`
    have hpos : 0 < S.a 3 - run S 3 + δ := by linarith
    have hne : S.a 3 - run S 3 + δ ≠ 0 := hpos.ne'
    have hrun : (1 - δ / (S.a 3 - run S 3 + δ)) * (run S 3 - δ) +
        δ / (S.a 3 - run S 3 + δ) * S.a 3 = run S 3 := by
      field_simp
      ring
    refine ⟨modify3 S (run S 3 - δ) (δ / (S.a 3 - run S 3 + δ)),
      valid_modify3 hS ⟨by linarith, by linarith⟩
        ⟨div_nonneg hδ0 hpos.le, (div_le_one hpos).2 (by linarith)⟩,
      (trace_modify3_iff _ _ _).2 hrun, ?_⟩
    rw [d_modify3, hrun, show run S 3 - (run S 3 - δ) = δ by ring]
    exact abs_of_nonneg hδ0
  · -- `a₃ < Y₃`: `D = 1 − Y₃`; verdict `Y₃ + δ`, influence `δ / (Y₃ − a₃ + δ)`
    have hB' : S.a 3 < run S 3 := lt_of_le_of_ne (not_lt.1 hB) hA
    have hpos : 0 < run S 3 - S.a 3 + δ := by linarith
    have hne : run S 3 - S.a 3 + δ ≠ 0 := hpos.ne'
    have hrun : (1 - δ / (run S 3 - S.a 3 + δ)) * (run S 3 + δ) +
        δ / (run S 3 - S.a 3 + δ) * S.a 3 = run S 3 := by
      field_simp
      ring
    refine ⟨modify3 S (run S 3 + δ) (δ / (run S 3 - S.a 3 + δ)),
      valid_modify3 hS ⟨by linarith, by linarith⟩
        ⟨div_nonneg hδ0 hpos.le, (div_le_one hpos).2 (by linarith)⟩,
      (trace_modify3_iff _ _ _).2 hrun, ?_⟩
    rw [d_modify3, hrun, show run S 3 - (run S 3 + δ) = -δ by ring, abs_neg]
    exact abs_of_nonneg hδ0

/-- **The identified set is exactly `[0, D S]`.** For a valid system, a rational `δ` is the defect
of some valid system with the same trace **iff** `0 ≤ δ ≤ D S`. With `exists_steered`
(`D S > 0` for an interior terminal opinion) this closes the mandate's optional stretch: the
trace-consistent defects of a valid trace form the whole interval, not just its endpoints.
Source: mandate Target 7 (stretch); [[trace-nonrecoverability]] §5 (a), §8 caveat 2; findings F10
Kind: C
Fidelity: exact
Hyps: (a) validity of `S` -/
theorem defect_consistent_iff {S : Sys} (hS : Valid S) (δ : ℚ) :
    (∃ S' : Sys, Valid S' ∧ trace S' = trace S ∧ d S' = δ) ↔ 0 ≤ δ ∧ δ ≤ D S := by
  constructor
  · rintro ⟨S', hS', htr, rfl⟩
    exact ⟨by unfold d; exact abs_nonneg _, d_le_D hS hS' htr⟩
  · rintro ⟨h0, hD⟩
    exact exists_defect_eq hS h0 hD

end IdentifiedSet

end Cleanroom.Trust.LegitFiniteDefect.Trace
