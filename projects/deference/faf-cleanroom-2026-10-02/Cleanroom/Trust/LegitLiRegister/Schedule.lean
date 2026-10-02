import Cleanroom.Bli.BliFound.Extend
import Cleanroom.Bli.BliFound.PaperInstances
import LogicalInduction.Properties.Pseudorandomness
import LogicalInduction.Construction.Statistics.FeedbackTruth
import LogicalInduction.Framework.Emission.RpnSplice

/-!
# `legit-li-register` · Schedule: schedule corruption as the hypothesis surface of `thm:wub`
(Target 9)

trust-lab-072 / scout-fresh-eyes Q6: "truth-correlated feedback timing voids unbiasedness while
every item resolves truthfully." Over FAF the claim is about which hypotheses of `lic_wub`
(`thm:wub`) fail, and FAF makes the schedule hypotheses explicit:

* **The surface, named** (`WubScheduleSurface`, D): `StrictlyIncreasingDeferral f` (strict
  temporal order of the feedback days), `WeightingSupportedOnDeferralImage W P f` (the weighting
  bets only on scheduled days), and — inside the bridge `FeedbackTruthSequence` — the clause
  `feedback_price : ∀ k, (sequence (f (k+1))).price P (f (k+1)) = (As (f k)).price P (f (k+1)) −
  truth (f k)`: **item `f k`'s truth is priced in by day `f (k+1)`**. That clause is the timing
  hypothesis; nothing else in `lic_wub` reads the *timing* of the schedule (`emit`, the emission
  certificate, is indexed by the deferral, but it is a computational hypothesis, not a timing
  one). The truth hypothesis `TheoryTruth` (every completed-theory world pays the truth) is
  **schedule-free**.
* **A truth-correlated decidability schedule** (`truthProcess`, D): over any base process, an e.c.
  atom family decided *true at day `n + 1`* and *false at day `g n`* for a chosen delay profile
  `g` — built the way `def-frozen-sibling` builds its contract schedules (`bli-found`'s
  `LiteralSchedule.ofList` and `extendBy`). FAF's process is a set sequence: timing is the stage
  index, disclosed. Membership lemmas: `schedAtom_mem_of_true`, `neg_schedAtom_mem_of_false`.
* **Every item resolves truthfully, whatever the delay** (`truthProcess_theoryTruth`, L): the
  `TheoryTruth` hypothesis of `lic_wub` holds for every `g` — so 072's "while every item resolves
  truthfully" is exactly the statement that the schedule attack leaves `TheoryTruth` intact and
  can only act on `feedback_price`/`hsupport` (the finding, [[legit-li-register-findings]] F7).
* **FAF's bridge is schedule-blind and market-blind** ((iii), proved —
  `truthProcess_bridge_alternating`, L): FAF's public constructor
  `feedbackTruthSequence_ofDetermined` builds the bridge from the family's e.c.-ness
  (`schedAtom_codes`), the market's `[0,1]` range, `TheoryTruth` (`truthProcess_theoryTruth`),
  satisfiable stages (`truthProcess_hworld`) and a `FeedbackTruthComputation` — a machine-metered
  value stream read at the paired index `⟨k, f (k+1)⟩`, which **never reads the process**. So for
  any truth stream with a `FeedbackTruthComputation` along `f` (`truthProcess_bridge_ofComputation`
  — `schedule_leak_open`'s conclusion with the certificate in place of the delay bound), in
  particular FAF's alternating stream (its own witness, `alternatingFeedbackTruthComputation_nonempty`;
  the headline `truthProcess_bridge_alternating`), the bridge exists at **every** delay profile `g`,
  bounded or not, truth-correlated or not, computable or not, every strictly increasing deferral
  `f`, and **every `[0,1]`-valued market** — the inductor property is never read (audit round 2:
  the round-1 statement carried the inductor as an idle instance; the instance form is now the
  corollary `truthProcess_bridge_alternating_inductor`). In FAF's rendering of `thm:wub`, "when
  feedback arrives" is the deferral `f` at which the certificate is read, not the stage at which
  the process decides the item: the delay profile is not a hypothesis the theorem has. Witnesses:
  **N+** `truthProcess_bridge_alternating_lia` — FAF's LIA over the scheduled process itself
  (`truthProcess_lia_inductor`, from `schedEnum_primrec` and `bli-found`'s
  `extendBy_ofList_computable`) at `paperDP 𝗜𝚺₁`, the successor deferral and every
  primitive-recursive delay profile, closed at `doubleDelay` (false items decided at `2n + 2`);
  **N−** `truthProcess_bridge_alternating_constHalf` — the constant-`½` market, which exhibits
  the blindness.
* **The leak** (extension, (ii)): if the delay is bounded by a computable `B` with `g n ≤ B n`,
  then "decided by day `B n`" is a stage fact for every `n` (`decided_by_bound`, L). The
  trader-level statement — a bridge for an *arbitrary* truth stream `x` at a deferral that outruns
  the bound, `B (f k) ≤ f (k+1)` (audit round 1 corrected the mandate's `f n := B n + 1`, which
  prices item `f k` before `B (f k)` for superlinear `B`) — is OPEN (`schedule_leak_open`) and
  expected false in general: FAF's `FeedbackTruthComputation` must be *machine-metered* on the
  paired index, while the process's computability (`IsLogicalInductor.processComputable`) is a
  partial-recursive stage program with no polynomial bound; the route "read the truth off
  non-arrival by day `B (f k)`" needs a bridge from the one to the other that FAF does not have
  (the only constructors of `FeedbackTruthComputation` are its three non-vacuity witnesses).
* The recurrent-bias half of the scout's (ii) (a pseudorandom family) is recorded, not
  formalized; the paper's `θ`-clusters example is cited, never re-narrated.
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound AffineCombination

/-- **The schedule surface of `thm:wub`**: the two hypotheses of `lic_wub` that read the feedback
schedule — strict increase of the deferral and support of the weighting on its image — bundled
under one name. The third timing clause, `FeedbackTruthSequence.feedback_price`, lives inside
FAF's bridge structure and is not a free hypothesis (see the module docstring).
Source: trust-lab-072 (the hypothesis surface); FAF `lic_wub` (`StrictlyIncreasingDeferral`, `WeightingSupportedOnDeferralImage`, `FeedbackTruthSequence`)
Kind: D
Fidelity: exact (FAF's own predicates)
Hyps: n/a -/
structure WubScheduleSurface (W : ℕ → EF) (P : History) (f : DeferralFunction) : Prop where
  /-- The feedback days are strictly increasing. -/
  strict : StrictlyIncreasingDeferral f
  /-- The weighting bets only on scheduled days. -/
  support : WeightingSupportedOnDeferralImage W P f

/-- The fresh-atom family of the schedule atoms (tag `17` of the run's registry; not used by any
dependency of this package).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def schedFamily : ℕ := 17

/-- The `n`-th schedule atom.
Source: trust-lab-072; mandate Target 9 (i)
Kind: D
Fidelity: n/a -/
def schedAtom (n : ℕ) : Sentence := freshAtom schedFamily n

/-- The schedule atoms are e.c. (one poly-fueled program writes the atom's code from `n`; the route
of `def-frozen-sibling`'s `contract5_codes`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem schedAtom_polySentenceCodes : PolySentenceCodes schedAtom :=
  ⟨_, (((PolyFueled.const 1).pair ((PolyFueled.const (cleanroomBaseTag + schedFamily)).pair
    PolyFueled.id)).succ_comp).of_eq fun _ => rfl⟩

/-- `schedAtom_codes`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem schedAtom_codes : MachineSentenceCodes schedAtom :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes schedAtom_polySentenceCodes)

/-- The enumeration of the literals adjoined by stage `s`: `(schedFamily, n, true)` once
`n + 1 ≤ s` when `x n`, `(schedFamily, n, false)` once `g n ≤ s` when `¬ x n`.
Source: mandate Target 9 (i) ("decided true at day `n + 1` and false at day `g n`")
Kind: D
Fidelity: n/a -/
def schedEnum (x : ℕ → Bool) (g : ℕ → ℕ) (s : ℕ) : List (ℕ × ℕ × Bool) :=
  (List.range (s + 1)).filterMap (fun n =>
    if x n then (if n + 1 ≤ s then some (schedFamily, n, true) else none)
    else (if g n ≤ s then some (schedFamily, n, false) else none))

/-- The enumeration is monotone under membership.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem schedEnum_mono (x : ℕ → Bool) (g : ℕ → ℕ) :
    ∀ s, ∀ e ∈ schedEnum x g s, e ∈ schedEnum x g (s + 1) := by
  intro s e he
  unfold schedEnum at he ⊢
  rw [List.mem_filterMap] at he ⊢
  obtain ⟨n, hn, hfn⟩ := he
  refine ⟨n, List.mem_range.2 (Nat.lt_succ_of_lt (List.mem_range.1 hn)), ?_⟩
  by_cases hx : x n = true
  · rw [if_pos hx] at hfn ⊢
    by_cases h1 : n + 1 ≤ s
    · rw [if_pos h1] at hfn
      rw [if_pos (Nat.le_succ_of_le h1)]
      exact hfn
    · rw [if_neg h1] at hfn
      exact absurd hfn (by simp)
  · rw [if_neg hx] at hfn ⊢
    by_cases h1 : g n ≤ s
    · rw [if_pos h1] at hfn
      rw [if_pos (Nat.le_succ_of_le h1)]
      exact hfn
    · rw [if_neg h1] at hfn
      exact absurd hfn (by simp)

/-- A scheduled literal's polarity is the truth value of its atom, and its family is the schedule
family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_schedEnum_bool {x : ℕ → Bool} {g : ℕ → ℕ} {s f p : ℕ} {b : Bool}
    (h : (f, p, b) ∈ schedEnum x g s) : x p = b ∧ f = schedFamily := by
  unfold schedEnum at h
  rw [List.mem_filterMap] at h
  obtain ⟨n, -, hn⟩ := h
  by_cases hx : x n = true
  · rw [if_pos hx] at hn
    by_cases h1 : n + 1 ≤ s
    · rw [if_pos h1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl, rfl⟩ := hn
      exact ⟨hx, rfl⟩
    · rw [if_neg h1] at hn
      exact absurd hn (by simp)
  · rw [if_neg hx] at hn
    by_cases h1 : g n ≤ s
    · rw [if_pos h1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl, rfl⟩ := hn
      exact ⟨by simpa using hx, rfl⟩
    · rw [if_neg h1] at hn
      exact absurd hn (by simp)

/-- **The truth-correlated decidability schedule**: atom `n` is adjoined positively at stage
`n + 1` when `x n`, negatively at stage `g n` when `¬ x n` — so a false item is decided by
stage `max (g n) (n + 1)` (`neg_schedAtom_mem_of_false`; exactly `g n` when `g n ≥ n + 1`, the
natural case).
Source: trust-lab-072 (the attack model: delay as a function of the truth value); mandate Target 9 (i)
Kind: D
Fidelity: variant: FAF's process is a set sequence — "when feedback arrives" is the stage index
Hyps: n/a -/
def truthSched (x : ℕ → Bool) (g : ℕ → ℕ) : LiteralSchedule :=
  LiteralSchedule.ofList (schedEnum x g) (schedEnum_mono x g)

/-- The schedule is functional: no atom is scheduled with both polarities (its polarity is its
truth value).
Source: none: infrastructure (`bli-found` `LiteralSchedule.Functional`)
Kind: L
Fidelity: n/a -/
theorem truthSched_functional (x : ℕ → Bool) (g : ℕ → ℕ) : (truthSched x g).Functional := by
  intro s f p ⟨ht, hf⟩
  unfold truthSched at ht hf
  rw [LiteralSchedule.ofList_lits, List.mem_toFinset] at ht hf
  have h1 := (mem_schedEnum_bool ht).1
  have h2 := (mem_schedEnum_bool hf).1
  rw [h1] at h2
  simp at h2

/-- Every family the schedule uses is the schedule family `17`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthSched_families (x : ℕ → Bool) (g : ℕ → ℕ) :
    ∀ f ∈ (truthSched x g).families, f = schedFamily := by
  rintro f ⟨s, ⟨f', p, b⟩, hx, rfl⟩
  unfold truthSched at hx
  rw [LiteralSchedule.ofList_lits, List.mem_toFinset] at hx
  exact (mem_schedEnum_bool hx).2

/-- **The scheduled process**: a base process with the truth-correlated schedule adjoined.
Source: mandate Target 9 (i) (over `extendBy (paperDP T) sched`; stated over any base)
Kind: D
Fidelity: exact
Hyps: n/a -/
def truthProcess (DP : DeductiveProcess) (x : ℕ → Bool) (g : ℕ → ℕ) : DeductiveProcess :=
  extendBy DP (truthSched x g)

/-- **Every stage of the scheduled process is satisfiable** over a base that never mentions the
schedule family and has satisfiable stages (`bli-found`'s `extendBy_hworld`: the schedule is
functional and fresh for the base).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthProcess_hworld (DP : DeductiveProcess)
    (hDP : TagFreeProcess (cleanroomBaseTag + schedFamily) DP)
    (hw : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (x : ℕ → Bool) (g : ℕ → ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((truthProcess DP x g).D n) :=
  extendBy_hworld (truthSched_functional x g)
    (ProcessFreeOf.of_tagFree fun f hf => by rw [truthSched_families x g f hf]; exact hDP) hw

/-- A true item is decided (positively) by day `n + 1`.
Source: mandate Target 9 (i)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedAtom_mem_of_true (DP : DeductiveProcess) (x : ℕ → Bool) (g : ℕ → ℕ) {n : ℕ}
    (hx : x n = true) : schedAtom n ∈ (truthProcess DP x g).D (n + 1) := by
  unfold truthProcess
  rw [extendBy_D]
  refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(schedFamily, n, true), ?_, rfl⟩)
  unfold truthSched
  rw [LiteralSchedule.ofList_lits, List.mem_toFinset]
  unfold schedEnum
  rw [List.mem_filterMap]
  exact ⟨n, List.mem_range.2 (by omega), by rw [if_pos hx, if_pos le_rfl]⟩

/-- A false item is decided (negatively) by day `g n`.
Source: mandate Target 9 (i)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem neg_schedAtom_mem_of_false (DP : DeductiveProcess) (x : ℕ → Bool) (g : ℕ → ℕ) {n : ℕ}
    (hx : x n = false) : ∼schedAtom n ∈ (truthProcess DP x g).D (max (g n) (n + 1)) := by
  unfold truthProcess
  rw [extendBy_D]
  refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(schedFamily, n, false), ?_, rfl⟩)
  unfold truthSched
  rw [LiteralSchedule.ofList_lits, List.mem_toFinset]
  unfold schedEnum
  rw [List.mem_filterMap]
  refine ⟨n, List.mem_range.2 ?_, ?_⟩
  · have := le_max_right (g n) (n + 1)
    omega
  · rw [if_neg (by simp [hx]), if_pos (le_max_left _ _)]

/-- **Every item resolves truthfully, whatever the delay**: `lic_wub`'s `TheoryTruth` hypothesis
holds for the schedule atoms at the truth `𝟙[x n]`, for every delay profile `g` — a completed-theory
world holds every stage member (`holds_of_mem_stage`). So the schedule attack cannot touch this
hypothesis; what it can touch is the bridge's `feedback_price` and `hsupport` (findings F7). Stated
for every base `DP`: over a base that already decides a schedule atom the other way no world is
consistent and `TheoryTruth` holds vacuously; the non-vacuous case is a base free of family `17`
(`truthProcess_hworld`).
Source: trust-lab-072 ("while every item resolves truthfully"); FAF `TheoryTruth`, `lic_wub`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem truthProcess_theoryTruth (DP : DeductiveProcess) (x : ℕ → Bool) (g : ℕ → ℕ) :
    TheoryTruth schedAtom (truthProcess DP x g) (fun n => if x n then 1 else 0) := by
  intro n v hv
  unfold PCWorld.payout
  by_cases hx : x n = true
  · have hh := hv.holds_of_mem_stage ⟨_, schedAtom_mem_of_true DP x g hx⟩
    simp [hh, hx]
  · have hx' : x n = false := by simpa using hx
    have h := hv.holds_of_mem_stage ⟨_, neg_schedAtom_mem_of_false DP x g hx'⟩
    rw [PCWorld.holds_neg] at h
    simp [h, hx']

/-- **Bounded delay makes "decided by day `B n`" a stage fact**: with `g n ≤ B n` and `n + 1 ≤ B n`,
every item is decided, one way or the other, by stage `B n` — the process-level half of the leak
(a reader of the stage learns the truth from arrival-or-not; a trader does not read stages, which
is why the trader-level half is OPEN).
Source: mandate Target 9 (ii) (the leak); trust-lab-072
Kind: L
Fidelity: exact (process level)
Hyps: (a) none -/
theorem decided_by_bound (DP : DeductiveProcess) (x : ℕ → Bool) (g B : ℕ → ℕ)
    (hgB : ∀ n, g n ≤ B n) (hnB : ∀ n, n + 1 ≤ B n) (n : ℕ) :
    schedAtom n ∈ (truthProcess DP x g).D (B n) ∨ ∼schedAtom n ∈ (truthProcess DP x g).D (B n) := by
  by_cases hx : x n = true
  · exact Or.inl ((truthProcess DP x g).mono_le (hnB n) (schedAtom_mem_of_true DP x g hx))
  · have hx' : x n = false := by simpa using hx
    refine Or.inr ((truthProcess DP x g).mono_le ?_ (neg_schedAtom_mem_of_false DP x g hx'))
    exact max_le (hgB n) (hnB n)

/-! ## (iii) FAF's bridge is schedule-blind: the positive contrast, proved for every delay profile -/

open scoped Classical in
/-- **The alternating truth stream as a Boolean**: `true` exactly on the even part of the deferral
image — FAF's `FeedbackTruth.alternatingTruth f` is its `{0,1}`-valued real form (`altBool_truth`).
Noncomputable as data (classical `decide` over the deferral's image); at the successor deferral it
is the computable `altBoolSucc` (`altBool_succDeferral`), which is what the LIA witness uses.
Source: FAF `FeedbackTruth.alternatingTruth`; mandate Target 9 (iii)
Kind: D
Fidelity: n/a -/
noncomputable def altBool (f : DeferralFunction) (n : ℕ) : Bool :=
  decide (∃ k, f.f k = n ∧ k % 2 = 0)

/-- The indicator of `altBool f` is FAF's alternating truth stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem altBool_truth (f : DeferralFunction) :
    (fun n => if altBool f n then (1 : ℝ) else 0) = FeedbackTruth.alternatingTruth f := by
  funext n
  unfold altBool FeedbackTruth.alternatingTruth
  by_cases h : ∃ k, f.f k = n ∧ k % 2 = 0
  · simp [h]
  · simp [h]

/-- **The `thm:wub` bridge exists for every truth stream that is machine-computable along the
deferral, at every delay profile and every `[0,1]`-valued market** (the general shape behind
Target 9 (iii); added in repair round 2 after the fidelity audit's "expected true, by the same
route"). Over a base free of the schedule family with satisfiable stages, for every truth stream
`x`, every delay profile `g`, every strictly increasing deferral `f`, every market `P` with prices
in `[0,1]` and every `FeedbackTruthComputation` for `𝟙[x]` along `f`, the `FeedbackTruthSequence`
for the schedule atoms exists. Read against `schedule_leak_open`: this is the OPEN's conclusion
with the computation certificate `C` as a hypothesis in place of the delay bound `B` — so the
whole content of the OPEN is the construction of `C` from the bound (reading the truth off
non-arrival by day `B (f k)` within `poly(f (k+1))`), which FAF does not provide. The
alternating headline `truthProcess_bridge_alternating` is the instance at FAF's own witness.
Source: trust-lab-072; scout-fresh-eyes Q6; mandate Target 9 (ii)/(iii); FAF `feedbackTruthSequence_ofDetermined`; audit round 2 (fidelity) N1 (a)
Kind: L (one FAF constructor at an instance)
Fidelity: variant: the stream's computability along the deferral is taken as FAF's `FeedbackTruthComputation`, the paper's own premise as FAF renders it
Hyps: (a) none (`C` is a hypothesis of `thm:wub` itself — the paper's "`ThmValue(A_{f k})` computable within `poly(f(k+1))`" — not a modelling substitution of this package; `hP` is the market's `[0,1]` range) -/
theorem truthProcess_bridge_ofComputation (DP : DeductiveProcess)
    (hDP : TagFreeProcess (cleanroomBaseTag + schedFamily) DP)
    (hw : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (x : ℕ → Bool) (g : ℕ → ℕ)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruth.FeedbackTruthComputation (fun n => if x n then (1 : ℝ) else 0) f)
    (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom) (fun n => if x n then 1 else 0)
      P (truthProcess DP x g) f) := by
  have hdet : DeterminedViaTheory (sentenceAffine schedAtom) P (truthProcess DP x g)
      (fun n => if x n then 1 else 0) := by
    intro n v hv
    simpa [sentenceAffine, AffineCombination.value] using truthProcess_theoryTruth DP x g n v hv
  exact ⟨FeedbackTruth.feedbackTruthSequence_ofDetermined
    (sentenceAffine_polySequence schedAtom schedAtom_codes)
    (sentenceAffine_bounded schedAtom P hP) hdet C hstrict (fun n => by simp) hP
    (truthProcess_hworld DP hDP hw x g)⟩

/-- **The `thm:wub` bridge exists for the alternating truth stream at every delay profile and
every `[0,1]`-valued market** (Target 9 (iii), the positive contrast — and more: FAF's bridge is
*schedule-blind* and *market-blind*; the instance of `truthProcess_bridge_ofComputation` at FAF's
alternating witness). Over a base free of the schedule family with satisfiable
stages, for **every** delay profile `g` (bounded or not, truth-correlated or not, computable or
not), every strictly increasing deferral `f` and every market `P` with prices in `[0,1]`, a
`FeedbackTruthSequence` for the schedule atoms at the alternating truth exists. Route: one
application of FAF's public constructor `feedbackTruthSequence_ofDetermined`, every input
discharged by a cited lemma — the family's e.c.-ness (`schedAtom_codes`), the price bounds `hP`,
the truth determined in every completed-theory world (`truthProcess_theoryTruth`), satisfiable
stages (`truthProcess_hworld`) and FAF's alternating `FeedbackTruthComputation` — a machine-metered
value stream on the paired index `⟨k, f (k+1)⟩`, which never reads the process. Neither `g` nor
the market's inductor property enters: the round-1 statement carried
`[IsLogicalInductor P (truthProcess …)]`, of which the proof used only `price_mem_Icc` (audit
round 2, both lenses); the instance form is the corollary `truthProcess_bridge_alternating_inductor`.
In FAF's rendering of `thm:wub`, "when feedback arrives" is the deferral at which the certificate
is read, not the stage at which the process decides the item (findings F7). What the theorem does
*not* say: anything about a truth stream that is not machine-computable along `f` (that is
`schedule_leak_open`); for any other stream with a `FeedbackTruthComputation` along `f` the general
form `truthProcess_bridge_ofComputation` applies (FAF constructs three such streams).
Source: trust-lab-072 (against "voids unbiasedness"); scout-fresh-eyes Q6 (the positive contrast); mandate Target 9 (iii); FAF `feedbackTruthSequence_ofDetermined`, `alternatingFeedbackTruthComputation_nonempty`; audit round 2 B1 (both lenses)
Kind: L (one FAF constructor at an instance; the content is `truthProcess_theoryTruth` and FAF's alternating witness)
Fidelity: variant: the truth stream is FAF's alternating witness (computable along the deferral); "poly-decidable timing" is not a hypothesis FAF's bridge reads, so the contrast is with the stream's computability, not the timing's
Hyps: (a) none (`hDP`, `hw` are the base's freshness and non-vacuity; `hP` is the market's `[0,1]` range, which every inductor has — `price_mem_Icc`) -/
theorem truthProcess_bridge_alternating (DP : DeductiveProcess)
    (hDP : TagFreeProcess (cleanroomBaseTag + schedFamily) DP)
    (hw : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (g : ℕ → ℕ) (f : DeferralFunction)
    (hstrict : StrictlyIncreasingDeferral f) (P : History)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom) (FeedbackTruth.alternatingTruth f)
      P (truthProcess DP (altBool f) g) f) := by
  obtain ⟨C⟩ := FeedbackTruth.alternatingFeedbackTruthComputation_nonempty hstrict
  have C' : FeedbackTruth.FeedbackTruthComputation
      (fun n => if altBool f n then (1 : ℝ) else 0) f := by
    rw [altBool_truth]; exact C
  have h := truthProcess_bridge_ofComputation DP hDP hw (altBool f) g f hstrict C' P hP
  rwa [altBool_truth] at h

/-- The successor deferral is strictly increasing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem succDeferral_strict : StrictlyIncreasingDeferral succDeferral :=
  fun _ _ h => Nat.succ_lt_succ h

/-- **The bridge at an inductor over the scheduled process** (the round-1 form of the headline,
now a corollary): every inductor's prices lie in `[0,1]` (`price_mem_Icc`), which is all the bridge
reads. Non-vacuous only where an inductor over the scheduled process exists, i.e. at a computable
`g` (`IsLogicalInductor.processComputable`); inhabited by FAF's LIA at every primitive-recursive
`g` (`truthProcess_lia_inductor`, `truthProcess_bridge_alternating_lia`).
Source: mandate Target 9 (iii); audit round 2 B1 (both lenses)
Kind: L
Fidelity: as `truthProcess_bridge_alternating`
Hyps: (a) none (the instance is discharged by `truthProcess_lia_inductor` at the witness) -/
theorem truthProcess_bridge_alternating_inductor (DP : DeductiveProcess)
    (hDP : TagFreeProcess (cleanroomBaseTag + schedFamily) DP)
    (hw : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (g : ℕ → ℕ) (f : DeferralFunction)
    (hstrict : StrictlyIncreasingDeferral f) (P : History)
    [IsLogicalInductor P (truthProcess DP (altBool f) g)] :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom) (FeedbackTruth.alternatingTruth f)
      P (truthProcess DP (altBool f) g) f) :=
  truthProcess_bridge_alternating DP hDP hw g f hstrict P fun n φ =>
    IsLogicalInductor.price_mem_Icc (DP := truthProcess DP (altBool f) g) n φ

/-- **Market-blindness exhibited** (N− of `truthProcess_bridge_alternating`): at the constant-`½`
market — an inductor over nothing — over `paperDP 𝗜𝚺₁` at the successor deferral, for every delay
profile `g`, the bridge exists. Degenerate on purpose: it shows that the bridge reads nothing of
the market beyond its range (audit round 2, adversarial B1's probe `BridgeMarketBlind.lean`,
incorporated). The same market is `Predication`'s `halfMarket` (not imported here).
Source: audit round 2 (adversarial) B1
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem truthProcess_bridge_alternating_constHalf (g : ℕ → ℕ) :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom)
      (FeedbackTruth.alternatingTruth succDeferral) (fun _ _ => (1 / 2 : ℝ))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) g) succDeferral) :=
  truthProcess_bridge_alternating (paperDP 𝗜𝚺₁)
    (paperDP_tagFree 𝗜𝚺₁ (by simp [cleanroomBaseTag])) (paperDP_hworld 𝗜𝚺₁) g succDeferral
    succDeferral_strict _ (fun _ _ => by norm_num)

/-! ## (iii) FAF's LIA over the scheduled process: the inductor hypothesis inhabited -/

/-- **The alternating stream at the successor deferral, computably**: `true` exactly at odd `n`
(the image of the even `k` under `k ↦ k + 1`). `altBool_succDeferral` identifies it with the
classically defined `altBool succDeferral`.
Source: none: infrastructure (audit round 2 B1, the fidelity lens's fix 1)
Kind: D
Fidelity: n/a -/
def altBoolSucc (n : ℕ) : Bool := decide (n % 2 = 1)

/-- `altBool_succDeferral`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem altBool_succDeferral : altBool succDeferral = altBoolSucc := by
  funext n
  unfold altBool altBoolSucc
  rw [decide_eq_decide]
  constructor
  · rintro ⟨k, hk, hk2⟩
    change k + 1 = n at hk
    omega
  · intro h
    exact ⟨n - 1, by change n - 1 + 1 = n; omega, by omega⟩

/-- `altBoolSucc_primrec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem altBoolSucc_primrec : Primrec altBoolSucc :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 1)).decide

/-- **The schedule enumeration is primitive recursive** for a primitive-recursive truth stream and
delay profile: a `filterMap` over `List.range (s + 1)` of a decidable test (the pattern of
`def-frozen-sibling`'s `enum0_primrec`, with `Primrec.listFilterMap` in place of `list_map`).
Source: none: infrastructure (audit round 2 B1)
Kind: L
Fidelity: n/a -/
theorem schedEnum_primrec {x : ℕ → Bool} {g : ℕ → ℕ} (hx : Primrec x) (hg : Primrec g) :
    Primrec (schedEnum x g) := by
  have hpos : Primrec fun p : ℕ × ℕ =>
      (if p.2 + 1 ≤ p.1 then some (schedFamily, p.2, true) else none) :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
        Primrec.fst)
      (Primrec.option_some.comp
        ((Primrec.const schedFamily).pair (Primrec.snd.pair (Primrec.const true))))
      (Primrec.const none)
  have hneg : Primrec fun p : ℕ × ℕ =>
      (if g p.2 ≤ p.1 then some (schedFamily, p.2, false) else none) :=
    Primrec.ite (Primrec.nat_le.comp (hg.comp Primrec.snd) Primrec.fst)
      (Primrec.option_some.comp
        ((Primrec.const schedFamily).pair (Primrec.snd.pair (Primrec.const false))))
      (Primrec.const none)
  have hbody : Primrec₂ fun (s n : ℕ) =>
      (if x n then (if n + 1 ≤ s then some (schedFamily, n, true) else none)
        else (if g n ≤ s then some (schedFamily, n, false) else none)) :=
    (Primrec.cond (hx.comp Primrec.snd) hpos hneg).of_eq fun p => by
      cases hxn : x p.2 <;> simp [hxn]
  exact Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ) hbody

/-- **The scheduled process is computable** over a computable base, for a primitive-recursive
truth stream and delay profile (`bli-found`'s `extendBy_ofList_computable`). This is the
computability certificate the round-1 "witness" lacked.
Source: none: infrastructure (audit round 2 B1); FAF `ComputableDeductiveProcess`
Kind: L
Fidelity: n/a -/
theorem truthProcess_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    {x : ℕ → Bool} {g : ℕ → ℕ} (hx : Primrec x) (hg : Primrec g) :
    ComputableDeductiveProcess (truthProcess DP x g) :=
  extendBy_ofList_computable hDP (schedEnum x g) (schedEnum_mono x g) (schedEnum_primrec hx hg)

/-- **FAF's LIA over the truth-correlated schedule is a logical inductor over it** (`thm:lia`) at
the paper's base `paperDP 𝗜𝚺₁`, the alternating stream at the successor deferral and every
primitive-recursive delay profile `g` — the inductor hypothesis of
`truthProcess_bridge_alternating_inductor`, inhabited by a real inductor over a real process.
Source: FAF `LIA_is_logical_inductor`; audit round 2 B1
Kind: L
Fidelity: n/a -/
theorem truthProcess_lia_inductor (g : ℕ → ℕ) (hg : Primrec g) :
    IsLogicalInductor (liaHistory (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) g))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) g) := by
  rw [altBool_succDeferral]
  exact LIA_is_logical_inductor _
    (truthProcess_computable (paperDP_computable 𝗜𝚺₁) altBoolSucc_primrec hg)

/-- **The bridge at FAF's LIA over the scheduled process** (N+ of
`truthProcess_bridge_alternating` and of its inductor form): over `paperDP 𝗜𝚺₁` at the successor
deferral, for every primitive-recursive delay profile `g`, FAF's `thm:lia` market over the
truth-correlated process carries the bridge. Every hypothesis of the inductor form is discharged
(the market, its inductor instance, the base's freshness and non-vacuity, the deferral's
strictness); the delay profile is the one remaining binder, closed below at `doubleDelay`.
Source: mandate Target 9 (iii) (witness); audit round 2 B1 (the fidelity lens's fix 1)
Kind: N+
Fidelity: n/a
Hyps: (a) none beyond `Primrec g` (one-way in the base and the deferral) -/
theorem truthProcess_bridge_alternating_lia (g : ℕ → ℕ) (hg : Primrec g) :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom)
      (FeedbackTruth.alternatingTruth succDeferral)
      (liaHistory (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) g))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) g) succDeferral) :=
  haveI := truthProcess_lia_inductor g hg
  truthProcess_bridge_alternating_inductor (paperDP 𝗜𝚺₁)
    (paperDP_tagFree 𝗜𝚺₁ (by simp [cleanroomBaseTag])) (paperDP_hworld 𝗜𝚺₁) g succDeferral
    succDeferral_strict _

/-- A truth-correlated delay profile with every binder closed: false items are decided at
`2n + 2` (true ones at `n + 1`); primitive recursive.
Source: audit round 2 (fidelity) B1
Kind: D
Fidelity: n/a -/
def doubleDelay (n : ℕ) : ℕ := 2 * n + 2

/-- `doubleDelay_primrec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem doubleDelay_primrec : Primrec doubleDelay :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 2)

/-- **The closed instance**: `truthProcess_bridge_alternating_lia` at `doubleDelay` — the bridge at
FAF's LIA over a truth-correlated schedule, no binder left.
Source: audit round 2 (fidelity) B1
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem truthProcess_bridge_alternating_lia_double :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom)
      (FeedbackTruth.alternatingTruth succDeferral)
      (liaHistory (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay))
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay) succDeferral) :=
  truthProcess_bridge_alternating_lia doubleDelay doubleDelay_primrec

/-! ## (ii) The leak at an arbitrary truth stream: OPEN -/

/-- **OPEN — the leak theorem** (Target 9 (ii), extension): for an arbitrary truth stream `x` with a
truth-correlated delay bounded by `B`, and a deferral that outruns the bound (`B (f k) ≤ f (k+1)`:
item `f k` is decided, one way or the other, by the next scheduled day), there is a
`FeedbackTruthSequence` for the schedule atoms over the scheduled process — the trader "reads the
truth off non-arrival". **Indexing corrected after audit round 1**: the mandate's `f n := B n + 1`
prices item `f k` at day `f (k+1) = B (k+1) + 1`, which for superlinear `B` precedes `B (f k)`
(e.g. `B n = 2n + 2`: item `2k + 3` is decided by `4k + 8 > 2k + 5`), so that form was expected
false. **Diagnosis**: FAF's bridge takes its truth values from a `FeedbackTruthComputation`, a
*machine-metered* (polynomial-time write-out) value stream on the paired index `⟨k, f (k+1)⟩` that
never reads the stages; the process's computability (`IsLogicalInductor.processComputable`) is a
partial-recursive stage program with no polynomial bound. The route needs a bridge from the latter
to the former — simulate the stage program to day `B (f k) ≤ f (k+1)` within `poly(f (k+1))` and
emit the arrival bit — which FAF does not provide (the only constructors of
`FeedbackTruthComputation` are its three non-vacuity witnesses). Expected **false in general**
(a computable but not poly-time truth stream); **proved** for any stream with a
`FeedbackTruthComputation` along `f` (`truthProcess_bridge_ofComputation`: this conclusion with the
certificate `C` in place of the bound `B`, so the whole content of this OPEN is the construction
of `C` from the bound — in which case `g` is irrelevant), with FAF's alternating stream as the
instance (`truthProcess_bridge_alternating`).
Source: trust-lab-072 (refutation target); mandate Target 9 (ii); audit round 1 (adversarial) N2
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem schedule_leak_open (DP : DeductiveProcess) (x : ℕ → Bool) (g B : ℕ → ℕ)
    (hgB : ∀ n, g n ≤ B n) (hnB : ∀ n, n + 1 ≤ B n) (f : DeferralFunction)
    (hstrict : StrictlyIncreasingDeferral f) (hf : ∀ k, B (f.f k) ≤ f.f (k + 1))
    (P : History) [IsLogicalInductor P (truthProcess DP x g)] :
    Nonempty (FeedbackTruthSequence (sentenceAffine schedAtom) (fun n => if x n then 1 else 0)
      P (truthProcess DP x g) f) := by
  sorry

end Cleanroom.Trust.LegitLiRegister
