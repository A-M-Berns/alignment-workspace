import LogicalInduction.Construction.Conditioning.Endpoints
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.Affine

/-!
# `legit-li-register` · Predication: "predicated on its own non-corruption" at the LI register
(Target 8)

[[li-deference]] §0.3: "All the actual feedback it gets should be assumed legitimate; the training
process is predicated on its own non-corruption in the present." trust-lab-2-033 / scout-legitimacy
Q8 reads this as an axiom scheme — update unconditionally on received feedback — and asks whether it
is dynamically consistent against retro-detection ("day-`k` feedback was corrupt", decided later),
conjecturing a **trilemma**: (1) predication, (2) retro-detection, (3) no finite Dutch book from
the learner's own two verdicts are "jointly unsatisfiable whenever retro-detection has positive
probability".

**The one FAF rendering** (the inventory's own pointer): the history conditioned on the **growing
prefix** of the received-feedback sentences `ψ_0, …, ψ_n` — FAF's `conditionedHistory P (fun n =>
sentenceConjunction (…ψ…))` — which `lic_conditioned_growing_ofSequence` (`thm:scon`) proves to be
a logical inductor over `DP.union (prefixProcess ψ)` for **every** e.c. `ψ`. Under this reading:

* **Predication (horn 1) is built in**: the conditioned market has updated on every received
  sentence, unconditionally (`predicatedHistory`).
* **No book (horn 3) is the criterion's own field**: `IsLogicalInductor.noExploit` — no e.c.
  trader exploits the conditioned market, *whatever contracts it bundles*, including "I updated on
  `ψ_k`" against a later verdict "`ψ_k` was corrupt" (`predication_no_book`).
* **Retro-detection (horn 2) is a later `ψ_{k'}`** entering the prefix. It is harmless **iff the
  stages stay satisfiable** (`predication_dichotomy`): if the theory links the verdict to `∼ψ_k`
  and both are received, the union process has an unsatisfiable stage and the criterion holds
  **vacuously** — every computable market is then an inductor over that process
  (`predication_vacuous_of_unsat`, FAF's `isLogicalInductor_of_stage_unsatisfiable`): the market
  is *dead*, not *booked*. In the satisfiable branch the market is alive: it learns every e.c.
  theorem family of the received process (`predication_learns_theorems`).

**Register (corrected after audit round 1).** Under FAF's criterion horns 1–3 are jointly
satisfiable exactly when the received prefix stays satisfiable, and the price of retro-detection is
vacuity, not a Dutch book. This is **not a refutation of the scout's conjecture**, for two reasons
([[legit-li-register-findings]] F6): (i) horn 3's *finite* two-contract book is rendered here as
FAF's *asymptotic* `Trader.Exploits` over completed-theory worlds — a different object, so
`predication_no_book` is `Fidelity: variant` — and under that rendering every conditioned e.c.
prefix is an inductor for free (`thm:scon`): horn 3 is satisfied by construction, not tested;
(ii) horn 2 has no non-vacuous rendering over FAF's objects: a verdict logically unlinked to `ψ_k`
is not retro-detection in any sense the scout could mean (the predicated market keeps `ψ_k` at
`≈ 1` whatever the verdict says), and a linked verdict makes a stage unsatisfiable, where
`Exploits` quantifies over no worlds. In the linked branch the scout's finite book *does* exist
whenever the base market prices the two contradictory conjunctions at or above the prefix: FAF's
`conditionalQuote` then returns `1` for **both** polarities (`retroFamily_junk_pair`), and with
the two-contract payout identity (`payout_add_payout_neg`) the seller of one unit of each collects
`2` and pays `1` in every propositional valuation (`retroFamily_book_net`) — while FAF reports
vacuity. So the honest verdict is: the trilemma cannot be posed non-vacuously over FAF's objects;
the consistency horn holds under the asymptotic reading; the finite-book conjecture is exhibited
at a logical inductor over the dead process (the constant-`½` market, which FAF's criterion
accepts there and which the book beats on every day — `dead_inductor_booked`, audit round 2) and
untested at FAF's LIA over a linked family (the exact-rational toy was not built). The reading "predication = prefix
conditioning; book = e.c. exploitation of the conditioned history" is ATTRIBUTION-UNVETTED, one of
several the scout's prose admits. The scout's pre-registered fake — a book so loose that any belief
change is exploitable — is avoided; the junk value of `conditionalQuote` (`1` whenever the
numerator is at least the denominator, including a zero denominator) is inside FAF's theorem, and
it is exactly what the linked branch's finite book rides on.

Witnesses: N− for the vacuous branch, `retroFamily u` (`atom u` received on day `0`, its negation
on day `1`: stage `1` is unsatisfiable, `retroFamily_unsat`). For the satisfiable branch, in
`Witness.lean`: `predicated_learns_feedback` is **N−** (the learned sentence is a conjunct of the
conditioning prefix, on which FAF's conditioning returns `≈ 1` by definition — audit round 1);
the N+ is `predicated_learns_monitor` — the predicated market at `onGSystem`'s advised reasoner,
conditioned on the decided literals *with a nominal verdict atom received on day `1`*, learns the
ledger-threshold monitors, which are not in the prefix — with `verdict_no_book` the
no-exploitation instance at that configuration (the "all three horns, alive" configuration,
inhabited). The exact-rational two-contract toy (the scout's EXEC) was not built.
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional
open Filter Topology

/-- **The predicated history**: the market conditioned on the growing prefix of received feedback
sentences `ψ_0 ⋏ … ⋏ ψ_n` (FAF's `conditionedHistory` at the prefix conjunction).
Source: [[li-deference]] §0.3 (the predication clause); trust-lab-2-033; FAF `conditionedHistory`
Kind: D
Fidelity: variant: "update unconditionally on received feedback" rendered as conditioning on the received prefix (FAF's `thm:scon` object)
Hyps: n/a -/
noncomputable def predicatedHistory (P : History) (ψ : ℕ → Sentence) : History :=
  conditionedHistory P (fun n => sentenceConjunction ((List.range (n + 1)).map ψ))

/-- **The received process**: the base process with the received prefix adjoined stage-wise.
Source: FAF `prefixProcess`, `DeductiveProcess.union`
Kind: D
Fidelity: exact
Hyps: n/a -/
def receivedProcess (DP : DeductiveProcess) (ψ : ℕ → Sentence) : DeductiveProcess :=
  DP.union (prefixProcess ψ)

/-- **Predication is an inductor** (horn 1, built in): for every e.c. feedback family `ψ`, the
predicated history is a logical inductor over the received process — FAF's `thm:scon`, named for
the instance.
Source: trust-lab-2-033 (the FAF rendering); FAF `lic_conditioned_growing_ofSequence`
Kind: L (a named instance)
Fidelity: variant: as `predicatedHistory`
Hyps: (a) none -/
theorem predication_inductor (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    IsLogicalInductor (predicatedHistory P ψ) (receivedProcess DP ψ) :=
  ConditioningCompile.lic_conditioned_growing_ofSequence P DP ψ hψ

/-- **No book** (horn 3): no efficiently computable trader exploits the predicated history over
the received process — the criterion's own `noExploit` field at the conditioned market, stated so
that the two verdicts ("I updated on `ψ_k`": `ψ_k` is in the prefix; "`ψ_k` was corrupt": any later
`ψ_{k'}`) are both inside the one object the trader is tested against.
Source: trust-lab-2-033 (horn 3); FAF `IsLogicalInductor.noExploit`
Kind: L
Fidelity: variant: the horn's *finite* two-contract book is rendered as FAF's *asymptotic* `Trader.Exploits` over completed-theory worlds (a different object: finitely incoherent and asymptotically unexploitable coexist; audit round 1 B1); not a weaker book — but one that every conditioned e.c. prefix satisfies for free
Hyps: (a) none -/
theorem predication_no_book (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    ∀ Tr : Trader, EfficientlyComputable Tr →
      ¬ Tr.Exploits (predicatedHistory P ψ) (receivedProcess DP ψ) :=
  (predication_inductor P DP ψ hψ).noExploit

/-- **The dichotomy**: either every stage of the received process is satisfiable, or some stage is
not. Propositional; the content is in the two branch theorems below.
Source: trust-lab-2-033 (the trilemma, resolved); mandate Target 8
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem predication_dichotomy (DP : DeductiveProcess) (ψ : ℕ → Sentence) :
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((receivedProcess DP ψ).D n)) ∨
      ∃ N, ∀ v : PCWorld, ¬ v.ConsistentWith ((receivedProcess DP ψ).D N) := by
  by_cases h : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((receivedProcess DP ψ).D n)
  · exact Or.inl h
  · right
    rw [not_forall] at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun v hv => hN ⟨v, hv⟩⟩

/-- **The satisfiable branch is alive**: with every stage of the received process satisfiable,
the predicated history learns every e.c. family of theorems of the received process (FAF's
`lic_provind_true` at the conditioned market) — the criterion is not holding vacuously.
Source: trust-lab-2-033 (the consistency horn); FAF `thm:provind`
Kind: L
Fidelity: exact
Hyps: (a) none (`hworld` is the branch) -/
theorem predication_learns_theorems (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((receivedProcess DP ψ).D n))
    (L : ℕ → Sentence) (hL : MachineSentenceCodes L)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (receivedProcess DP ψ) → v.Holds (L n)) :
    (fun n => predicatedHistory P ψ n (L n)) ≈ₙ (fun _ => 1) := by
  haveI := predication_inductor P DP ψ hψ
  exact lic_provind_true (predicatedHistory P ψ) (receivedProcess DP ψ) L hL hthm hworld

/-- **The unsatisfiable branch is dead, not booked**: if some stage of the received process has no
consistent world (the theory links a retro-detection verdict to the negation of a received
sentence, and both are received), then **every** computable market is a logical inductor over the
received process — FAF's `isLogicalInductor_of_stage_unsatisfiable`, with the process's
computability taken from `thm:scon`'s instance. The criterion holds vacuously; "no Dutch book"
is true of every price sequence, and so says nothing.
Source: trust-lab-2-033 (the vacuity cost of horn 2); FAF `isLogicalInductor_of_stage_unsatisfiable`
Kind: L (composition of two FAF facts)
Fidelity: exact
Hyps: (a) none (`hN` is the branch) -/
theorem predication_vacuous_of_unsat (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) {N : ℕ}
    (hN : ∀ v : PCWorld, ¬ v.ConsistentWith ((receivedProcess DP ψ).D N))
    (V : History) (hV : ComputableMarket V) : IsLogicalInductor V (receivedProcess DP ψ) :=
  isLogicalInductor_of_stage_unsatisfiable V _ hV
    (predication_inductor P DP ψ hψ).processComputable hN

/-! ## The vacuous branch's witness (N−): retro-detection that contradicts the received prefix -/

/-- **The retro-detection family**: feedback `atom u` received on day `0`, the verdict "it was
corrupt" rendered as `∼atom u` received on day `1`, nothing afterwards (`⊤`). This is the extreme
case in which the theory *identifies* the verdict with the negation of the feedback.
Source: trust-lab-2-033 (retro-detection); mandate Target 8 (N− for the vacuous branch)
Kind: D
Fidelity: n/a (a witness)
Hyps: n/a -/
def retroFamily (u : ℕ) (n : ℕ) : Sentence :=
  if n = 0 then Formula.atom u else if n - 1 = 0 then ∼(Formula.atom u) else ⊤

/-- The retro-detection family is e.c. (two `ifZero` dispatches on the day).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem retroFamily_codes (u : ℕ) : MachineSentenceCodes (retroFamily u) :=
  (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (Formula.atom u))
    (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (∼(Formula.atom u)))
      (MachineSentenceCodes.const ⊤) (UnaryRuler.id.sub (UnaryRuler.const 1)))
    UnaryRuler.id).of_eq (fun n => by
      unfold retroFamily
      rfl)

/-- **Stage `1` of the received process is unsatisfiable** at the retro-detection family: it
contains both `atom u` and `∼atom u`.
Source: trust-lab-2-033; mandate Target 8 (N−)
Kind: N−
Fidelity: n/a (degenerate by design: the verdict is the literal negation)
Hyps: (a) none -/
theorem retroFamily_unsat (DP : DeductiveProcess) (u : ℕ) :
    ∀ v : PCWorld, ¬ v.ConsistentWith ((receivedProcess DP (retroFamily u)).D 1) := by
  intro v hv
  have h0 : retroFamily u 0 ∈ (receivedProcess DP (retroFamily u)).D 1 := by
    show retroFamily u 0 ∈ DP.D 1 ∪ ((List.range (1 + 1)).map (retroFamily u)).toFinset
    refine Finset.mem_union_right _ ?_
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨0, by simp, rfl⟩
  have h1 : retroFamily u 1 ∈ (receivedProcess DP (retroFamily u)).D 1 := by
    show retroFamily u 1 ∈ DP.D 1 ∪ ((List.range (1 + 1)).map (retroFamily u)).toFinset
    refine Finset.mem_union_right _ ?_
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨1, by simp, rfl⟩
  have ha : v.Holds (Formula.atom u) := by simpa [retroFamily] using hv _ h0
  have hb : v.Holds (∼(Formula.atom u)) := by simpa [retroFamily] using hv _ h1
  rw [PCWorld.holds_neg] at hb
  exact hb ha

/-- **The vacuous branch inhabited**: at the retro-detection family every computable market is an
inductor over the received process (the instance of `predication_vacuous_of_unsat` at
`retroFamily_unsat`).
Source: trust-lab-2-033; mandate Target 8 (N− for the vacuous branch)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem predication_vacuous_retroFamily (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (u : ℕ) (V : History) (hV : ComputableMarket V) :
    IsLogicalInductor V (receivedProcess DP (retroFamily u)) :=
  predication_vacuous_of_unsat P DP (retroFamily u) (retroFamily_codes u)
    (retroFamily_unsat DP u) V hV

/-! ## Received-process worlds are base-process worlds -/

/-- A world consistent with the completed theory of the received process is consistent with the
completed theory of the base process (the received stages contain the base stages).
Source: none: infrastructure (FAF `PCWorld.consistentWith_union_iff`)
Kind: L
Fidelity: n/a -/
theorem consistentWithTheory_of_received {DP : DeductiveProcess} {ψ : ℕ → Sentence}
    {v : PCWorld} (hv : v.ConsistentWithTheory (receivedProcess DP ψ)) :
    v.ConsistentWithTheory DP :=
  fun n => ((PCWorld.consistentWith_union_iff v DP (prefixProcess ψ) n).mp (hv n)).1

/-! ## The finite book in the linked branch (audit round 1): where FAF's `Exploits` sees no world,
the scout's two-contract book is a sure profit at the junk quotes -/

/-- **Two-contract payout identity**: in every propositional valuation exactly one of `φ`, `∼φ`
pays, so a book holding one unit of each pays exactly `1`.
Source: scout-legitimacy Q8 (horn 3: "a two-contract book"); FAF `PCWorld.payout`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem payout_add_payout_neg (w : PCWorld) (φ : Sentence) :
    w.payout φ + w.payout (∼φ) = 1 := by
  unfold PCWorld.payout
  by_cases h : w.Holds φ
  · simp [h]
  · simp [h]

/-- The received prefix of the retro-detection family at day `n` (`atom u ⋏ ∼atom u ⋏ ⊤ ⋏ …`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def retroPrefix (u n : ℕ) : Sentence :=
  sentenceConjunction ((List.range (n + 1)).map (retroFamily u))

/-- **The linked branch's quotes land on the junk value**: at the retro-detection family, on any
day on which the base market prices the two (contradictory) conjunctions `atom u ⋏ C_n` and
`∼atom u ⋏ C_n` at or above the prefix `C_n`, FAF's `conditionalQuote` returns `1` for **both**
polarities. The linked branch is days `n ≥ 1`, once the verdict `∼atom u` is in the prefix (at
`n = 0` the prefix is `atom u` alone); the statement holds for every `n` because the price
condition does the work. The hypothesis is a condition on the base market's day-`n` prices of
three refutable sentences: it is met on every day by any market that prices them at a common
value — in particular by the constant-`½` market, which is a **logical inductor over the dead
received process** (`halfMarket_inductor_dead`; so `dead_inductor_booked`: an object FAF calls a
logical inductor, finitely booked on every day — audit round 2). Whether FAF's LIA over a
*linked* family meets it on infinitely many days is not known (over a process with an
unsatisfiable stage no FAF limit theorem applies, so nothing is known about the three prices'
limits either), which is why the finite-book conjecture is *untested at FAF's LIA*.
Source: scout-legitimacy Q8 (horn 3); audit round 1 (fidelity) B1; audit round 2 (adversarial) N1; FAF `conditionalQuote_eq_one`
Kind: L
Fidelity: variant: the book is exhibited under a price condition on the base market, not derived from the inductor
Hyps: (c) `h1`, `h0`: the base market's day-`n` prices of the two conjunctions dominate its price of the prefix -/
theorem retroFamily_junk_pair (P : History) (u n : ℕ)
    (h1 : P n (retroPrefix u n) ≤ P n (Formula.atom u ⋏ retroPrefix u n))
    (h0 : P n (retroPrefix u n) ≤ P n (∼(Formula.atom u) ⋏ retroPrefix u n)) :
    predicatedHistory P (retroFamily u) n (Formula.atom u) = 1 ∧
      predicatedHistory P (retroFamily u) n (∼(Formula.atom u)) = 1 :=
  ⟨conditionalQuote_eq_one h1, conditionalQuote_eq_one h0⟩

/-- **The book's net**: under `retroFamily_junk_pair`'s price condition (read on days `n ≥ 1`,
once the verdict is in the prefix), selling one unit each of `atom u` and `∼atom u` at the
predicated quotes collects `2` and pays `1` in **every** propositional valuation `w`, consistent
with the theory or not — the right notion for a finite book against stated prices, and one FAF's
`Exploits` cannot see, since it quantifies over completed-theory worlds and no valuation is
consistent with stage `1` (`retroFamily_unsat`).
Source: scout-legitimacy Q8 (horn 3: "a genuine finite arbitrage against stated prices"); audit round 1 (fidelity) B1; audit round 2 (adversarial) N1
Kind: L
Fidelity: as `retroFamily_junk_pair`
Hyps: (c) as `retroFamily_junk_pair` -/
theorem retroFamily_book_net (P : History) (u n : ℕ)
    (h1 : P n (retroPrefix u n) ≤ P n (Formula.atom u ⋏ retroPrefix u n))
    (h0 : P n (retroPrefix u n) ≤ P n (∼(Formula.atom u) ⋏ retroPrefix u n)) (w : PCWorld) :
    (predicatedHistory P (retroFamily u) n (Formula.atom u) +
        predicatedHistory P (retroFamily u) n (∼(Formula.atom u))) -
      (w.payout (Formula.atom u) + w.payout (∼(Formula.atom u))) = 1 := by
  obtain ⟨e1, e0⟩ := retroFamily_junk_pair P u n h1 h0
  rw [e1, e0, payout_add_payout_neg]
  norm_num

/-! ## The dead branch at an object FAF calls a logical inductor (audit round 2) -/

/-- **The constant-`½` market.** A market, not an inductor over any process with satisfiable
stages; over the dead received process it *is* one (`halfMarket_inductor_dead`).
Source: audit round 2 (adversarial) N1 (probe `DeadInductorBooked.lean`, incorporated)
Kind: D
Fidelity: n/a -/
noncomputable def halfMarket : History := fun _ _ => (1 / 2 : ℝ)

/-- The constant-`½` market is a computable market (constant rational table, constant program).
Source: none: infrastructure; FAF `ComputableMarket.ofComputableTable`
Kind: L
Fidelity: n/a -/
theorem halfMarket_computable : ComputableMarket halfMarket :=
  ComputableMarket.ofComputableTable (fun _ _ => (1 / 2 : ℚ))
    (fun _ _ => by norm_num [halfMarket]) (fun _ _ => by simp [halfMarket])
    (Computable.const _)

/-- **A logical inductor over the dead received process**: the constant-`½` market, by the
vacuity branch (`predication_vacuous_retroFamily`), given any inductor over the base.
Source: audit round 2 (adversarial) N1
Kind: L (instance of `predication_vacuous_retroFamily`)
Fidelity: n/a
Hyps: (a) none (the base inductor is any; FAF's LIA over any computable process is one) -/
theorem halfMarket_inductor_dead (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (u : ℕ) : IsLogicalInductor halfMarket (receivedProcess DP (retroFamily u)) :=
  predication_vacuous_retroFamily P DP u halfMarket halfMarket_computable

/-- **…which the scout's two-contract book beats on every day in every valuation**:
`retroFamily_book_net` with the price condition discharged by reflexivity.
Source: audit round 2 (adversarial) N1
Kind: L
Fidelity: as `retroFamily_book_net` (the (c) price condition is discharged, not assumed)
Hyps: (a) none -/
theorem halfMarket_booked (u n : ℕ) (w : PCWorld) :
    (predicatedHistory halfMarket (retroFamily u) n (Formula.atom u) +
        predicatedHistory halfMarket (retroFamily u) n (∼(Formula.atom u))) -
      (w.payout (Formula.atom u) + w.payout (∼(Formula.atom u))) = 1 :=
  retroFamily_book_net halfMarket u n le_rfl le_rfl w

/-- **A logical inductor, finitely booked** (N− for the dead branch, sharpened): over the dead
received process the constant-`½` market satisfies FAF's criterion *and* the scout's finite
two-contract book nets `1` against it on every day in every valuation. "FAF reports no
exploitation while the finite book exists" is thus an instance about an object FAF calls a
logical inductor, not merely about a market. Degenerate as a market (constant); the content is
the coexistence. At FAF's LIA over a *linked* family the price condition is untested.
Source: scout-legitimacy Q8 (horn 3); audit round 2 (adversarial) N1
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem dead_inductor_booked (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (u : ℕ) :
    IsLogicalInductor halfMarket (receivedProcess DP (retroFamily u)) ∧
      ∀ n (w : PCWorld),
        (predicatedHistory halfMarket (retroFamily u) n (Formula.atom u) +
            predicatedHistory halfMarket (retroFamily u) n (∼(Formula.atom u))) -
          (w.payout (Formula.atom u) + w.payout (∼(Formula.atom u))) = 1 :=
  ⟨halfMarket_inductor_dead P DP u, fun n w => halfMarket_booked u n w⟩

end Cleanroom.Trust.LegitLiRegister
