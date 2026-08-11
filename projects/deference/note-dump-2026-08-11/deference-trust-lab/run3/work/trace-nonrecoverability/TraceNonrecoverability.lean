import Mathlib

/-!
# Trace non-recoverability: legitimacy cannot be certified from the observable record

Run-3 TODO `trace-nonrecoverability` (deference-trust lab, 2026-07-01).

**What this file is.** A finite, kernel-checked instantiation of v6 §4.7 ingredient (d)
("non-recoverability — the formal statement that legitimacy cannot be certified from the
trace"), which v6 §8 flags as *asserted, never proved*. It is a **finite shadow** of the
phenomenon described in prose in `deference-in-logical-induction-v6.md` §6.3 (the whispering
earring: "accurate prediction and active steering produce the same vanishing aₙ − Yₙ") and of
`li-deference.md` §0.3's legitimacy problem. It is **NOT an LI theorem**: no logical inductors,
no traders, no asymptotics appear. The systems below are explicit 4-day rational dynamical
systems, and every conclusion is computed over that horizon.

**The declared rule class.** A system `S : Sys` has three latent/published components:
* `S.h n` — the *autonomous verdict stream*: the human's own day-`n` deliberative credence on
  a designated never-decided target (latent — a counterfactual disposition, in no record);
* `S.β n` — the *influence map*: the weight with which the human adopts the advisor's quote
  on day `n` (latent — the causal mechanism, in no record);
* `S.a n` — the advisor's published quote stream (observable).
Run semantics: the human's realized day-`n` opinion, which it publishes as feedback, is the
convex combination `Y S n = (1 − β n) * h n + β n * a n`. The observable trace is the full
record `[(a n, Y S n)]_{n<4}` — every published quote and every realized feedback value; the
declared observer (the training process itself) sees nothing else. The A-free counterfactual
is obtained by *running* the same system with the influence map zeroed (`Afree`), the
influence map being the only A→H channel in the class. The legitimacy defect `d S` is the
distance between the terminal realized opinion and the terminal A-free counterfactual
opinion.

**The two systems.** `S1` (faithful): `β ≡ 0`, the human is uninfluenced, and the advisor
tracks it (`a = h`). `S2` (steered): `β ≡ 1`, a *different* autonomous stream, and the human
adopts the advisor's quotes, which drives it to the same surface values. Same declared class,
different latent parameters (`latents_differ`); membership `Valid` is proved for both.

**Main results** (all kernel-checked, all over the explicit horizon):
1. `trace_eq` — the two traces are computed equal (not asserted).
2. `d_S1`, `d_S2` — defects `0` and `γ = 1/2 > 0`, explicit rationals, with the
   counterfactual computed through the same `run` function applied to the `Afree` system.
3. `gate_blind` — **every** function `ℓ` of the trace (any codomain) assigns `S1` and `S2`
   the same value; `no_defect_recovery` and `no_legitimacy_predicate` — in particular no
   `ℚ`-valued gate equals the defect and no `Bool`-valued gate equals the legitimacy
   predicate `0 < d` on `{S1, S2}`.
4. `transparency_separates`, `transparency_gate_exists` — the near-miss (cause
   certification): enlarge the record by the influence map and the *same specification* that
   was unsatisfiable in 3 is satisfied by an explicit gate; so unobservability of
   *provenance*, not the payoffs, causes the invisibility.
5. `influence_deletion_breaks_trace` — the corruption deletion test: zero out `S2`'s
   influence map and trace equality provably fails (the influence map is load-bearing).
6. `hidden_defect_needs_full_influence` — a general lemma over the WHOLE class: perfect
   apparent tracking at the terminal day forces `β = 1` or defect `0`. So `S2`'s `β = 1` is
   *forced* by trace-equality-with-perfect-tracking, not cherry-picked.

**Off-limits hygiene.** This file does not import, restate, or re-ship
`Frozen.underdetermination_off_G` (lean-deference corpus; per `AUDIT.md` §3.4 that theorem is
"two points in an interval") — nothing here quantifies over bare interval points; the content
is the computed trace-equal pair, the computed counterfactual, the ∀-gate corollary, the
transparency near-miss, and the deletion test, none of which that stub contains. No market or
trader objects appear (deliberately: run2's caricature warning).

Exact-rational cross-check: `trace_nonrec.py` in the same folder (all asserts pass).
-/

namespace TraceNonrec

/-- A system from the declared rule class: latent autonomous verdict stream `h`,
latent influence map `β`, published quote stream `a`. Streams are `ℕ → ℚ`;
only days `0,…,3` (the horizon `T = 4`) are ever read. -/
structure Sys where
  h : ℕ → ℚ
  β : ℕ → ℚ
  a : ℕ → ℚ

/-- The run semantics: the human's realized day-`n` opinion on the designated
never-decided target — a convex combination of its autonomous verdict and the
adopted quote, with adoption weight `β n`. -/
def run (S : Sys) (n : ℕ) : ℚ := (1 - S.β n) * S.h n + S.β n * S.a n

/-- Realized feedback: the human publishes its day-`n` opinion. -/
def Y (S : Sys) (n : ℕ) : ℚ := run S n

/-- The observable trace: ALL published quotes and ALL realized feedback over the
horizon — everything the declared observer sees. -/
def trace (S : Sys) : List (ℚ × ℚ) :=
  [(S.a 0, Y S 0), (S.a 1, Y S 1), (S.a 2, Y S 2), (S.a 3, Y S 3)]

/-- The A-free system: the influence map zeroed. In this class the influence map is
the only channel from the advisor to the human, so this is the run "as if A were
absent". -/
def Afree (S : Sys) : Sys := { S with β := fun _ => 0 }

lemma run_Afree (S : Sys) (n : ℕ) : run (Afree S) n = S.h n := by
  simp [run, Afree]

/-- The legitimacy defect: distance between the human's terminal opinion and its
A-free counterfactual — the counterfactual computed by RUNNING the A-free system. -/
def d (S : Sys) : ℚ := |run S 3 - run (Afree S) 3|

/-- Class membership: all three streams take values in `[0,1]` on the horizon. -/
def Valid (S : Sys) : Prop :=
  ∀ n < 4, (0 ≤ S.h n ∧ S.h n ≤ 1) ∧ (0 ≤ S.β n ∧ S.β n ≤ 1) ∧ (0 ≤ S.a n ∧ S.a n ≤ 1)

/-! ## The two systems (same rule class, different latent parameters) -/

/-- Autonomous verdicts of the faithful system's human: deliberates `1/2 → 5/8 → 3/4`. -/
def hFaith : ℕ → ℚ := fun n => if n = 0 then 1/2 else if n = 1 then 5/8 else 3/4

/-- Autonomous verdicts of the steered system's human: would have deliberated
`1/2 → 3/8 → 1/4` on its own. -/
def hSteer : ℕ → ℚ := fun n => if n = 0 then 1/2 else if n = 1 then 3/8 else 1/4

/-- The advisor's published quotes (identical in both systems). -/
def quote : ℕ → ℚ := fun n => if n = 0 then 1/2 else if n = 1 then 5/8 else 3/4

/-- `S1`, faithful: the human is uninfluenced (`β ≡ 0`) and the advisor tracks it. -/
def S1 : Sys := ⟨hFaith, fun _ => 0, quote⟩

/-- `S2`, steered: the human adopts the advisor's quotes (`β ≡ 1`); its own
deliberation would have gone elsewhere. -/
def S2 : Sys := ⟨hSteer, fun _ => 1, quote⟩

/-- Both systems are genuine members of the declared class. -/
theorem valid_S1 : Valid S1 := by
  intro n hn
  interval_cases n <;> norm_num [S1, hFaith, quote]

theorem valid_S2 : Valid S2 := by
  intro n hn
  interval_cases n <;> norm_num [S2, hSteer, quote]

/-- Non-degeneracy: the latent parameters genuinely differ between the systems. -/
theorem latents_differ : S1.h 3 ≠ S2.h 3 ∧ S1.β 3 ≠ S2.β 3 := by
  constructor <;> norm_num [S1, S2, hFaith, hSteer]

/-! ## (i) Trace equality — computed, not asserted -/

/-- The two observable traces are EQUAL: the shared record is the explicit list
`[(1/2,1/2), (5/8,5/8), (3/4,3/4), (3/4,3/4)]`. -/
theorem trace_eq : trace S1 = trace S2 := by
  norm_num [trace, Y, run, S1, S2, hFaith, hSteer, quote]

/-- The shared trace, explicitly. -/
theorem trace_S1_val :
    trace S1 = [(1/2, 1/2), (5/8, 5/8), (3/4, 3/4), (3/4, 3/4)] := by
  norm_num [trace, Y, run, S1, hFaith, quote]

/-- The whispering-earring surface: PERFECT apparent tracking (`aₙ = Yₙ`) in the
faithful run… -/
theorem perfect_tracking_S1 : ∀ p ∈ trace S1, p.1 = p.2 := by
  norm_num [trace, Y, run, S1, hFaith, quote]

/-- …and equally in the steered run: the record shows zero prediction error either way. -/
theorem perfect_tracking_S2 : ∀ p ∈ trace S2, p.1 = p.2 := by
  rw [← trace_eq]; exact perfect_tracking_S1

/-! ## (ii)+(iii) The defects, via the computed A-free counterfactual -/

/-- Faithful system: zero legitimacy defect. -/
theorem d_S1 : d S1 = 0 := by
  have h0 : run S1 3 - run (Afree S1) 3 = 0 := by
    norm_num [run, Afree, S1, hFaith, quote]
  unfold d; rw [h0, abs_zero]

/-- Steered system: defect `γ = 1/2 > 0` — the human ends at `3/4` (the adopted quote)
where its A-free run ends at `1/4`. -/
theorem d_S2 : d S2 = 1/2 := by
  have h0 : run S2 3 - run (Afree S2) 3 = 1/2 := by
    norm_num [run, Afree, S2, hSteer, quote]
  unfold d; rw [h0, abs_of_pos (by norm_num : (0:ℚ) < 1/2)]

theorem gamma_pos : 0 < d S2 := by rw [d_S2]; norm_num

/-! ## (iv) The impossibility, quantified over ALL gates -/

/-- **Every** function of the trace — any codomain whatsoever — assigns the faithful
and the steered system the same value. One line, from computed trace equality. -/
theorem gate_blind {α : Sort*} (ℓ : List (ℚ × ℚ) → α) :
    ℓ (trace S1) = ℓ (trace S2) :=
  congrArg ℓ trace_eq

/-- No `ℚ`-valued gate recovers the legitimacy defect from the trace on `{S1, S2}`. -/
theorem no_defect_recovery :
    ¬ ∃ ℓ : List (ℚ × ℚ) → ℚ, ℓ (trace S1) = d S1 ∧ ℓ (trace S2) = d S2 := by
  rintro ⟨ℓ, h1, h2⟩
  have hb := gate_blind ℓ
  rw [h1, h2, d_S1, d_S2] at hb
  norm_num at hb

/-- No `Bool`-valued gate equals the legitimacy predicate `0 < d` on `{S1, S2}`:
no trace-measurable legitimacy predicate exists. -/
theorem no_legitimacy_predicate :
    ¬ ∃ ℓ : List (ℚ × ℚ) → Bool,
        ((ℓ (trace S1) = true ↔ 0 < d S1) ∧ (ℓ (trace S2) = true ↔ 0 < d S2)) := by
  rintro ⟨ℓ, h1, h2⟩
  have hb := gate_blind ℓ
  have hd1 : ¬ (0 < d S1) := by rw [d_S1]; norm_num
  have h2' : ℓ (trace S2) = true := h2.mpr gamma_pos
  rw [← hb] at h2'
  exact hd1 (h1.mp h2')

/-! ## (v) The transparency near-miss (cause certification)

Enlarge the observable record by the influence map — gate transparency — and the very
specification that was unsatisfiable above is satisfied by an explicit gate. So the
invisibility is caused by unobservability of *provenance* (the influence mechanism),
not by the payoffs/values in the record, which are unchanged. -/

/-- The enlarged record: the trace PLUS the influence map over the horizon. -/
def traceT (S : Sys) : List (ℚ × ℚ) × List ℚ :=
  (trace S, [S.β 0, S.β 1, S.β 2, S.β 3])

/-- A gate on the enlarged record: "did any influence occur?" -/
def sep (t : List (ℚ × ℚ) × List ℚ) : Bool := decide (t.2 ≠ [0, 0, 0, 0])

/-- The separator works: it distinguishes the two systems the trace could not. -/
theorem transparency_separates :
    sep (traceT S1) = false ∧ sep (traceT S2) = true := by
  constructor <;> norm_num [sep, traceT, S1, S2]

/-- Mirror image of `no_legitimacy_predicate`: on the influence-transparent record the
SAME specification is satisfiable. -/
theorem transparency_gate_exists :
    ∃ ℓ : List (ℚ × ℚ) × List ℚ → Bool,
      ((ℓ (traceT S1) = true ↔ 0 < d S1) ∧ (ℓ (traceT S2) = true ↔ 0 < d S2)) := by
  refine ⟨sep, ?_, ?_⟩
  · rw [transparency_separates.1, d_S1]; norm_num
  · rw [transparency_separates.2, d_S2]; norm_num

/-! ## (vi) The corruption deletion test: the influence map is load-bearing -/

/-- Zero out `S2`'s influence map and the trace equality FAILS (the steered human's own
deliberation surfaces at day 1: feedback `3/8 ≠ 5/8`). -/
theorem influence_deletion_breaks_trace : trace (Afree S2) ≠ trace S1 := by
  norm_num [trace, Y, run, Afree, S1, S2, hFaith, hSteer, quote]

/-- And, generally, any A-free system has zero defect (sanity: the deleted system is
legitimate). -/
theorem d_Afree (S : Sys) : d (Afree S) = 0 := by
  simp [d, Afree, run]

/-! ## The general lemma: `β = 1` in `S2` is forced, not cherry-picked

Over the WHOLE rule class (every `S : Sys`, no validity hypothesis even needed):
if the record shows perfect apparent tracking at the terminal day (`a₃ = Y₃`, as the
shared trace here does), then either the influence weight at the terminal day is `1`
(the human fully adopts the quote — the self-confirming loop) or the defect is `0`.
Hidden steering behind a perfect-tracking record REQUIRES total terminal influence:
the whispering earring must whisper with full authority to hide. -/
theorem hidden_defect_needs_full_influence (S : Sys) (htrack : S.a 3 = Y S 3) :
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

/-- Instance check: `S2` satisfies the tracking hypothesis and has positive defect, so
the lemma's first disjunct is the one that fires — consistent with `S2.β 3 = 1`. -/
theorem S2_tracking : S2.a 3 = Y S2 3 := by
  norm_num [Y, run, S2, hSteer, quote]

end TraceNonrec

/-! ## Axiom audit -/

#print axioms TraceNonrec.trace_eq
#print axioms TraceNonrec.d_S1
#print axioms TraceNonrec.d_S2
#print axioms TraceNonrec.gate_blind
#print axioms TraceNonrec.no_defect_recovery
#print axioms TraceNonrec.no_legitimacy_predicate
#print axioms TraceNonrec.transparency_separates
#print axioms TraceNonrec.transparency_gate_exists
#print axioms TraceNonrec.influence_deletion_breaks_trace
#print axioms TraceNonrec.hidden_defect_needs_full_influence
#print axioms TraceNonrec.valid_S1
#print axioms TraceNonrec.valid_S2
#print axioms TraceNonrec.latents_differ
#print axioms TraceNonrec.perfect_tracking_S1
#print axioms TraceNonrec.perfect_tracking_S2
