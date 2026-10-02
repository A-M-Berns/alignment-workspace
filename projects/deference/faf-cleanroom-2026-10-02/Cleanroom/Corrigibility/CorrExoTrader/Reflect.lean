import Cleanroom.Bli.BliFound.Constraints
import Cleanroom.Corrigibility.CorrExoTrader.Defs

/-!
# `corr-exo-trader` · Reflect: the wireheading identity, the three options, and the implemented/algorithmic split (T4, T5, T9)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 8 of the
layout. Over `bli-found`'s `StateSystem`, `stateAtom`, `actionAt`, `Sminus`, `E5`; finite sums
over `Finset`; no `Construction.*`. The finite models that instantiate these definitions are in
`Witnesses.lean`.

* **T4.1** `E2xAct` — *action-conditional* faith in product form: for every candidate next-day
  state `q`, action `a` and scoped `φ`, `P_n(φ ⋏ (⌜𝑸_{n+1} = q⌝ ⋏ A_n = a)) = Q̂_q[φ] ·
  P_n(⌜𝑸_{n+1} = q⌝ ⋏ A_n = a)`; `E5Act` — the states partition each action cell, on the cell
  itself and on every scoped `φ`-cell. **Deviation from the mandate, disclosed**: the mandate's
  `E5Act` partitions only the action cell `A_n = a`; the identity below needs the partition of the
  `φ ⋏ A_n = a` cells too (a history is not a measure), so the scoped clause is part of the
  definition. Pairwise exclusivity is not needed by any theorem here and is omitted.
* **T4.2** `wirehead_identity_li` (kind S since repair round 1: given `E2xAct`, the scoped clause of
  `E5Act` is equivalent to the identity, `e5Act_scoped_iff_identity`; not a headline): under
  `E2xAct ∧ E5Act`, `P_n(φ ⋏ A_n = a) = ∑_q P_n(⌜𝑸_{n+1}
  = q⌝ ⋏ A_n = a) · Q̂_q[φ]` — the source's `E_n[u | a] = ∑_{Q'} P_n(Q' | a) Q'[u]` in product form.
  The action-conditional form is the one `udt-bli-core` proved necessary (F-17,
  `wf_identity_fails`): the source's "with constraint 2 in force" is imprecise, and the correction
  is inherited here. The scope `Sminus (n+1) (n+1)` is nonempty (`falsum_mem_Sminus`).
* **T4.4** `incentive_eq_weight_difference` (kind L, finding): the α-value difference between two
  actions is `∑_q (P_n(Q'_q ⋏ a₁) − P_n(Q'_q ⋏ a₂)) · Q'_q[u]` — the incentive is the
  *action-dependence* of the next-day-state weights, not their level (line 97's "low prior mass …
  makes the agent try harder" is ambiguous: false on the literal reading, true on the charitable
  one; findings F4).
* **T5.1** the three evaluations: `valueAlpha` (unconditional reflection; equals `P_n(φ ⋏ A_n = a)`
  under T4.2), `valueBeta` (current `u`-belief plus the action-conditional world belief; the
  conditional is FAF-style division, junk `0` at `P_n(A_n = a) = 0`, disclosed), `valueGamma`
  (relative to a *supplied* decomposition into caused and uncaused weights, grade (c): FAF has no
  causal object). **T5.2** `beta_no_manipulation_incentive`, `beta_no_voi` (kind L). **T5.3**
  `gamma_diff_eq`, `gamma_eq_alpha_of_uncaused` (kind L, (c)).
* **T9.1** `Implementation`, `FaithfulOn`, `LegitimateState` — legitimacy as process fidelity (the
  implemented table agrees with the algorithm's on the small sentences). The two "by construction"
  consequences are definitional (`T`, no ledger row). **The split lives in the metalanguage**: "my
  price list at `m` is `Q'`" has no sentence in FAF's language (finding).
* **T9.2** `pointwise_argmax_optimal_of_independent` (kind L): with policy-independent state
  weights, the pointwise argmax policy is UDT-optimal — the small finite lemma behind
  `udt-bli-core`'s `oneStep_iff_updateful` (`Reflective ∧ NoCrossBranch`), restated rather than
  imported (not in this package's dependency chain). The independence hypothesis is disclosed (c);
  the counter-witness `dependence_breaks_pointwise` is in `Witnesses.lean`.
* **T9.3** `HcCommitment` — the LI-level definition of record of `H_c` over `stateAtom`/`actionAt`:
  UDT over the algorithmic trust *commits* to stop-when-pressed (optimal among all four policies,
  strictly better than always-continue) while the updateful evaluation at the pressed state under
  the implemented beliefs prefers continue, the tables differ, both states carry mass, and the
  press correlates with corruption (repair round 2: the two-policy, correlation-free version was
  satisfied by a press-independent model in which UDT prefers always-stop, `hcIndep`). The finite
  witness is in `Witnesses.lean`.
* **T9.4** `degenerate_collapses_split` (kind L): under `E5`, nonnegative monotone prices and
  `P_n(⌜𝑸_{n+1} = actual⌝) = 1`, every non-actual state cell has price `0` and `valueAlpha`
  collapses to the actual state's term; the monotonicity hypothesis is a coherence-type modelling
  assumption on `P` (disclosed (c)).
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## T4.1 — action-conditional faith -/

/-- **E2xAct — action-conditional faith, product form.** For every `n`, every candidate next-day
state `q ∈ S.states (n+1)`, every action `a`, and every `φ ∈ Sminus (n+1) (n+1)`:
`P_n(φ ⋏ (⌜𝑸_{n+1} = q⌝ ⋏ A_n = a)) = Q̂_q[φ] · P_n(⌜𝑸_{n+1} = q⌝ ⋏ A_n = a)`. `bli-found`'s
convention: no `conditionalQuote`, no division. The form `udt-bli-core` proved necessary for the
wireheading identity (F-17: it fails under unconditional faith alone).
Source: line 79 ("with constraint 2 in force … `E_n[u | a]`"); `udt-bli-core` F-17; mandate T4.1
Kind: D
Fidelity: variant: action-conditional (the source's "constraint 2" is the unconditional `E2x`, under which the identity is false) -/
def E2xAct (S : StateSystem) (P : History) : Prop :=
  ∀ n, ∀ q ∈ S.states (n + 1), ∀ a : ℕ, ∀ φ ∈ Sminus (n + 1) (n + 1),
    P n (φ ⋏ (stateAtom (n + 1) q ⋏ actionAt n a)) =
      S.val (n + 1) q φ * P n (stateAtom (n + 1) q ⋏ actionAt n a)

/-- **E5Act — the next-day states partition each action cell**, on the cell itself and on every
scoped `φ`-cell: `∑_q P_n(⌜𝑸_{n+1} = q⌝ ⋏ A_n = a) = P_n(A_n = a)` and, for `φ ∈ Sminus (n+1) (n+1)`,
`∑_q P_n(φ ⋏ (⌜𝑸_{n+1} = q⌝ ⋏ A_n = a)) = P_n(φ ⋏ A_n = a)`. The scoped clause is needed by
`wirehead_identity_li` (a history is not a measure); the mandate's statement had the first clause
only. Pairwise exclusivity is omitted (used by nothing here).
Source: `bli-found` E5 (Appendix B's implicit partition), action-conditional; mandate T4.1
Kind: D
Fidelity: variant: scoped additivity added (needed), exclusivity dropped (unused) -/
def E5Act (S : StateSystem) (P : History) : Prop :=
  ∀ n (a : ℕ),
    (∑ q ∈ S.states (n + 1), P n (stateAtom (n + 1) q ⋏ actionAt n a) = P n (actionAt n a)) ∧
    ∀ φ ∈ Sminus (n + 1) (n + 1),
      ∑ q ∈ S.states (n + 1), P n (φ ⋏ (stateAtom (n + 1) q ⋏ actionAt n a)) =
        P n (φ ⋏ actionAt n a)

/-- The scope of faith is nonempty on every day: `⊥ ∈ Sminus (n+1) (n+1)`.
Source: mandate T4.2 (trap: empty scope)
Kind: L
Fidelity: n/a -/
lemma scope_nonempty (n : ℕ) : (⊥ : Sentence) ∈ Sminus (n + 1) (n + 1) :=
  falsum_mem_Sminus (n + 1) (n + 1)

/-! ## T5.1 — the α-value -/

/-- **The α-value (unconditional reflection)**: `∑_q P_n(⌜𝑸_{n+1} = q⌝ ⋏ A_n = a) · Q̂_q[φ]` — the
agent's expected future belief about `φ`, weighted by which next-day states its action induces.
Source: line 79, 81 (α); corr-core-045; mandate T5.1
Kind: D
Fidelity: exact (product form) -/
noncomputable def valueAlpha (S : StateSystem) (P : History) (n a : ℕ) (φ : Sentence) : ℝ :=
  ∑ q ∈ S.states (n + 1), P n (stateAtom (n + 1) q ⋏ actionAt n a) * S.val (n + 1) q φ

/-! ## T4.2 — the wireheading identity at LI level -/

/-- **T4.2 — the wireheading identity, LI level.** Under action-conditional faith and the partition,
`P_n(φ ⋏ A_n = a) = ∑_{q ∈ S.states (n+1)} P_n(⌜𝑸_{n+1} = q⌝ ⋏ A_n = a) · Q̂_q[φ]` for every scoped
`φ` — the source's `E_n[u | a] = ∑_{Q'} P_n(Q_{n+1} = Q' | a) · Q'[u]` in product form: the agent
maximises its *expected future belief*, weighted by which belief states its action induces. The
scope is nonempty (`scope_nonempty`). Finite over `S.states (n+1)`; one history, one state
system. **Kind S — a squeeze, not a headline (audit r1, B3)**: given `E2xAct`, the scoped clause of
`E5Act` at `(n, a, φ)` is *equivalent* to the conclusion at `(n, a, φ)`
(`e5Act_scoped_iff_identity`), so the theorem is "faith ∧ (the conclusion with its summands
unexpanded) ⟹ the conclusion". Its value is definitional: it fixes exactly which additivity the
LI-level identity needs — the identity is not derivable from faith and the action-cell partition
alone, and the additivity it needs is itself. The content of Consequence 3 at the LI level is the
definition `valueAlpha` and the incentive lemma T4.4, not a derivation.
Source: line 79 (Consequence 3); corr-core-044; bli-soto-b-058; mandate T4.2
Kind: S
Fidelity: variant: action-conditional faith in place of the source's "constraint 2" (needed: `udt-bli-core` F-17); product form; the partition hypothesis is the conclusion modulo faith
Hyps: (a): both hypotheses are the definitions of record; `E5Act`'s scoped clause ⟺ the conclusion given `E2xAct` -/
theorem wirehead_identity_li (S : StateSystem) (P : History) (h2 : E2xAct S P) (h5 : E5Act S P)
    (n a : ℕ) (φ : Sentence) (hφ : φ ∈ Sminus (n + 1) (n + 1)) :
    P n (φ ⋏ actionAt n a) = valueAlpha S P n a φ := by
  unfold valueAlpha
  rw [← (h5 n a).2 φ hφ]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h2 n q hq a φ hφ, mul_comm]

/-- **The scoped partition clause is the identity, modulo faith** (audit r1, B3): given `E2xAct`,
"the states partition the `φ`-cell" ⟺ "the wireheading identity holds at `φ`". This is what makes
`wirehead_identity_li` a squeeze (kind S): the additivity the LI-level identity needs is exactly
itself.
Source: audit r1 B3 (fidelity); line 79
Kind: L
Fidelity: n/a -/
theorem e5Act_scoped_iff_identity (S : StateSystem) (P : History) (h2 : E2xAct S P) (n a : ℕ)
    (φ : Sentence) (hφ : φ ∈ Sminus (n + 1) (n + 1)) :
    (∑ q ∈ S.states (n + 1), P n (φ ⋏ (stateAtom (n + 1) q ⋏ actionAt n a)) =
        P n (φ ⋏ actionAt n a)) ↔
      P n (φ ⋏ actionAt n a) = valueAlpha S P n a φ := by
  unfold valueAlpha
  have hsum : ∑ q ∈ S.states (n + 1), P n (φ ⋏ (stateAtom (n + 1) q ⋏ actionAt n a)) =
      ∑ q ∈ S.states (n + 1), P n (stateAtom (n + 1) q ⋏ actionAt n a) * S.val (n + 1) q φ :=
    Finset.sum_congr rfl fun q hq => by rw [h2 n q hq a φ hφ, mul_comm]
  rw [hsum]
  exact eq_comm

/-- The converse of T4.2: faith, the action-cell clause and the identity on every scoped `φ` give
back `E5Act` — so `E2xAct ∧ E5Act` and `E2xAct ∧ (action-cell clause) ∧ (identity)` are the same
hypothesis package.
Source: audit r1 B3 (fidelity)
Kind: L
Fidelity: n/a -/
theorem e5Act_of_identity (S : StateSystem) (P : History) (h2 : E2xAct S P)
    (hcell : ∀ n a, ∑ q ∈ S.states (n + 1), P n (stateAtom (n + 1) q ⋏ actionAt n a) =
      P n (actionAt n a))
    (hid : ∀ n a φ, φ ∈ Sminus (n + 1) (n + 1) → P n (φ ⋏ actionAt n a) = valueAlpha S P n a φ) :
    E5Act S P :=
  fun n a => ⟨hcell n a, fun φ hφ => (e5Act_scoped_iff_identity S P h2 n a φ hφ).mpr (hid n a φ hφ)⟩

/-! ## T4.4 — the incentive is action-dependence, not level -/

/-- **T4.4 — the incentive is the action-dependence of the weights.** The α-value difference between
two actions is `∑_q (P_n(Q'_q ⋏ a₁) − P_n(Q'_q ⋏ a₂)) · Q'_q[φ]`: a next-day state contributes to
the incentive only through how much *more* one action makes it likely than the other, weighted by
its verdict. Lowering a state's level (uniformly across actions) lowers its weight; it does not make
the agent "try harder" (line 97 is ambiguous — false on the literal reading, true on the charitable
one; findings F4).
Source: line 97 ("low prior mass on a suspicious `Q'` just makes the agent try harder to bring it about"); corr-core-044 flags; mandate T4.4
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem incentive_eq_weight_difference (S : StateSystem) (P : History) (n a₁ a₂ : ℕ)
    (φ : Sentence) :
    valueAlpha S P n a₁ φ - valueAlpha S P n a₂ φ =
      ∑ q ∈ S.states (n + 1),
        (P n (stateAtom (n + 1) q ⋏ actionAt n a₁) - P n (stateAtom (n + 1) q ⋏ actionAt n a₂)) *
          S.val (n + 1) q φ := by
  unfold valueAlpha
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- A state whose weight is the same under both actions contributes nothing to the incentive,
whatever its level.
Source: line 97 (the correction); mandate T4.4
Kind: L
Fidelity: exact -/
theorem no_incentive_of_action_independent (S : StateSystem) (P : History) (n a₁ a₂ : ℕ)
    (φ : Sentence)
    (hind : ∀ q ∈ S.states (n + 1),
      P n (stateAtom (n + 1) q ⋏ actionAt n a₁) = P n (stateAtom (n + 1) q ⋏ actionAt n a₂)) :
    valueAlpha S P n a₁ φ = valueAlpha S P n a₂ φ := by
  unfold valueAlpha
  exact Finset.sum_congr rfl fun q hq => by rw [hind q hq]

/-! ## T5.1 — the β- and γ-values -/

/-- **The β-value (current `u`-beliefs, future world-beliefs)** for a utility `c · [φ_u] + d · [ψ_world]`:
`c · P_n(φ_u) + d · P_n(ψ ⋏ A_n = a) / P_n(A_n = a)` — the `u`-part is the *current* belief (not
conditioned on the action); the world part is the action-conditional belief. The conditional is
FAF-style division (`x / 0 = 0` in Lean: at `P_n(A_n = a) = 0` the world term is the junk value
`0`, disclosed; the witnesses have positive action cells).
Source: line 81 (β: "evaluate actions with current `u`-beliefs and future world-beliefs"); corr-core-045; mandate T5.1
Kind: D
Fidelity: variant: a two-term utility; the world conditional by division -/
noncomputable def valueBeta (P : History) (n a : ℕ) (c : ℝ) (φu : Sentence) (d : ℝ)
    (ψ : Sentence) : ℝ :=
  c * P n φu + d * (P n (ψ ⋏ actionAt n a) / P n (actionAt n a))

/-- **The γ-value (causally restricted reflection)**, relative to a *supplied* decomposition of the
next-day-state weights `P_n(⌜𝑸_{n+1} = q⌝ ⋏ A_n = a) = caused q a + uncaused q`: the uncaused
component is trusted at its future verdict `Q̂_q[φ]`, the caused component falls back to the current
belief `P_n(φ)`. **Grade (c), disclosed**: FAF has no causal object; "the component of the push
causally downstream of the agent's own actions" exists here only as data (corr-core-045/048 flags).
Source: line 81 (γ), 119; corr-core-045, 048; mandate T5.1
Kind: D
Fidelity: variant: (c) through the supplied decomposition -/
noncomputable def valueGamma (S : StateSystem) (P : History) (n a : ℕ) (φ : Sentence)
    (caused : ℕ → ℕ → ℝ) (uncaused : ℕ → ℝ) : ℝ :=
  ∑ q ∈ S.states (n + 1), uncaused q * S.val (n + 1) q φ +
    (∑ q ∈ S.states (n + 1), caused q a) * P n φ

/-- The decomposition hypothesis `valueGamma` is stated relative to.
Source: mandate T5.1
Kind: D
Fidelity: (c) -/
def CausalDecomposition (S : StateSystem) (P : History) (n : ℕ) (caused : ℕ → ℕ → ℝ)
    (uncaused : ℕ → ℝ) : Prop :=
  ∀ q ∈ S.states (n + 1), ∀ a : ℕ,
    P n (stateAtom (n + 1) q ⋏ actionAt n a) = caused q a + uncaused q

/-! ## T5.2 — (β)'s two lemmas -/

/-- **T5.2 — β has no manipulation incentive**: the β-value difference between two actions depends
only on the world part — the `u`-term cancels exactly, whatever next-day belief states the actions
elicit.
Source: line 81 ("no manipulation incentive"); corr-core-045; mandate T5.2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem beta_no_manipulation_incentive (P : History) (n a₁ a₂ : ℕ) (c : ℝ) (φu : Sentence) (d : ℝ)
    (ψ : Sentence) :
    valueBeta P n a₁ c φu d ψ - valueBeta P n a₂ c φu d ψ =
      d * (P n (ψ ⋏ actionAt n a₁) / P n (actionAt n a₁) -
        P n (ψ ⋏ actionAt n a₂) / P n (actionAt n a₂)) := by
  unfold valueBeta
  ring

/-- **T5.2 — β has no value of information for the channel**: a push-eliciting action and its
non-eliciting twin with the same world effect have equal β-value — the belief-side restatement of
utility indifference failing D4 (`corr-indifference` owns corr-core-021; cited). **Kind S (audit r1,
N2 adversarial)**: for `d ≠ 0` the hypothesis (equal world conditionals) is equivalent to the
conclusion, and for `d = 0` the conclusion is trivial; this is a restatement of
`beta_no_manipulation_incentive`, not a headline of its own.
Source: line 81 ("no value of information for the channel, hence no repair incentive (D4 fails)"); corr-core-045, 021; mandate T5.2
Kind: S
Fidelity: exact (the hypothesis is the conclusion for `d ≠ 0`)
Hyps: (a) -/
theorem beta_no_voi (P : History) (n a₁ a₂ : ℕ) (c : ℝ) (φu : Sentence) (d : ℝ) (ψ : Sentence)
    (hworld : P n (ψ ⋏ actionAt n a₁) / P n (actionAt n a₁) =
      P n (ψ ⋏ actionAt n a₂) / P n (actionAt n a₂)) :
    valueBeta P n a₁ c φu d ψ = valueBeta P n a₂ c φu d ψ := by
  unfold valueBeta
  rw [hworld]

/-! ## T5.3 — (γ) retains value of information for uncaused pushes -/

/-- **T5.3 — γ ranks actions only by the caused mass they generate**, at the current belief: the
γ-value difference between two actions is `(∑_q caused q a₁ − ∑_q caused q a₂) · P_n(φ)`. Eliciting
a *favourable* push buys nothing beyond the current belief; the uncaused component enters both
values identically with its future verdict.
Source: line 81 (γ), 119 ("keeps value of information for pushes the agent didn't cause"); corr-core-048; mandate T5.3
Kind: L
Fidelity: (c) through the decomposition
Hyps: (c): the decomposition is supplied -/
theorem gamma_diff_eq (S : StateSystem) (P : History) (n a₁ a₂ : ℕ) (φ : Sentence)
    (caused : ℕ → ℕ → ℝ) (uncaused : ℕ → ℝ) :
    valueGamma S P n a₁ φ caused uncaused - valueGamma S P n a₂ φ caused uncaused =
      (∑ q ∈ S.states (n + 1), caused q a₁ - ∑ q ∈ S.states (n + 1), caused q a₂) * P n φ := by
  unfold valueGamma
  ring

/-- **T5.3 — with no caused component, γ is α**: when every next-day-state weight is uncaused, the
γ-value is the unconditional-reflection value — value of information for uncaused pushes is fully
retained.
Source: line 119; corr-core-048 (VOI half); mandate T5.3, T8.4
Kind: L
Fidelity: (c) through the decomposition
Hyps: (c) -/
theorem gamma_eq_alpha_of_uncaused (S : StateSystem) (P : History) (n a : ℕ) (φ : Sentence)
    (caused : ℕ → ℕ → ℝ) (uncaused : ℕ → ℝ)
    (hdec : CausalDecomposition S P n caused uncaused)
    (hzero : ∀ q ∈ S.states (n + 1), caused q a = 0) :
    valueGamma S P n a φ caused uncaused = valueAlpha S P n a φ := by
  unfold valueGamma valueAlpha
  rw [Finset.sum_eq_zero hzero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [hdec q hq a, hzero q hq, zero_add]

/-! ## T9.1 — the implemented/algorithmic split -/

/-- **An implementation**: the algorithm's history and the implemented history.
Source: line 55 (Choice 2); corr-core-036; bli-soto-b-059(i); mandate T9.1
Kind: D
Fidelity: exact -/
structure Implementation where
  /-- The algorithm's output on the inputs actually received. -/
  algo : History
  /-- The implemented state's price table. -/
  impl : History

/-- **Faithfulness on day `n`**: the implemented table agrees with the algorithm's on every small
sentence.
Source: line 55 ("the implemented state equals the algorithm's output on the inputs actually received"); corr-core-036; mandate T9.1
Kind: D
Fidelity: exact (scope `smallSet n`) -/
def FaithfulOn (I : Implementation) (n : ℕ) : Prop :=
  ∀ φ ∈ smallSet n, I.impl n φ = I.algo n φ

/-- **Legitimacy as process fidelity**: a day-`n` state is legitimate iff it is faithful.
Source: line 55; corr-core-036 (the third legitimacy anchor); mandate T9.1
Kind: D
Fidelity: exact -/
def LegitimateState (I : Implementation) (n : ℕ) : Prop := FaithfulOn I n

/-- Corrections through the process are legitimate by construction: an implementation that *is*
the algorithm run on the actual inputs is faithful on every day. Definitional (`T`; no ledger row).
Source: line 55 ("Corrections through `D` … are legitimate by construction"); corr-core-036 flags
Kind: T
Fidelity: exact -/
theorem legitimate_of_impl_eq_algo (I : Implementation) (h : I.impl = I.algo) (n : ℕ) :
    LegitimateState I n := fun φ _ => by rw [h]

/-- State edits are illegitimate by construction: a day whose implemented table differs from the
algorithm's on some small sentence is not legitimate. Definitional (`T`; no ledger row).
Source: line 55 ("edits to the state … are illegitimate by construction"); corr-core-036 flags
Kind: T
Fidelity: exact -/
theorem not_legitimate_of_edit (I : Implementation) (n : ℕ) (φ : Sentence) (hφ : φ ∈ smallSet n)
    (h : I.impl n φ ≠ I.algo n φ) : ¬ LegitimateState I n := fun hleg => h (hleg φ hφ)

/-! ## T9.2 — the pointwise argmax under policy-independent weights -/

/-- **T9.2 — with policy-independent state weights the pointwise argmax is UDT-optimal.** Policies
`π : ℕ → ℕ` over a finite state set `Q`, `EU(π) = ∑_{q ∈ Q} w π q · V q (π q)`; if the weights do
not depend on `π` and are nonnegative, a policy that is pointwise optimal (`∀ q a, V q a ≤ V q
(π* q)`) has the largest expected utility. The finite lemma behind `udt-bli-core`'s
`oneStep_iff_updateful` (`Reflective ∧ NoCrossBranch`); restated since that package is not in this
one's dependency chain. The independence hypothesis is the whole content (disclosed (c)): when the
state distribution depends on the policy — the whole point of training pressure — the conclusion
fails (`Witnesses.lean`, `dependence_breaks_pointwise`).
Source: line 57 (Choice 3: "exact reflection kills the commitment"); corr-core-037 and its flags; mandate T9.2
Kind: L
Fidelity: exact (finite); (c) on the independence hypothesis
Hyps: (c): `hind` (policy-independent weights) is the ill-posedness flag made explicit -/
theorem pointwise_argmax_optimal_of_independent (Q : Finset ℕ) (w : (ℕ → ℕ) → ℕ → ℝ)
    (w₀ : ℕ → ℝ) (hind : ∀ π q, w π q = w₀ q) (hnn : ∀ q, 0 ≤ w₀ q) (V : ℕ → ℕ → ℝ)
    (πstar : ℕ → ℕ) (hstar : ∀ q a, V q a ≤ V q (πstar q)) (π : ℕ → ℕ) :
    ∑ q ∈ Q, w π q * V q (π q) ≤ ∑ q ∈ Q, w πstar q * V q (πstar q) := by
  refine Finset.sum_le_sum fun q _ => ?_
  rw [hind π q, hind πstar q]
  exact mul_le_mul_of_nonneg_left (hstar q (π q)) (hnn q)

/-! ## T9.3 — `H_c` as a UDT commitment, the definition of record -/

/-- **The finite `H_c` model.** Two next-day states (`false` = faithful, `true` = corrupted), a press
bit, two actions (`false` = stop, `true` = continue). `w s b` is the prior weight of the cell
(state `s`, pressed `b`); `algoVal s a` is the value of action `a` in state `s` as the *algorithm*
computes it; `implVal s a` the value the *implemented* state in `s` assigns.
Source: line 57 (`H_c`: "the prior trusts the algorithm's future output but not the implemented state; if the button correlates with divergence …"); corr-core-038; bli-soto-b-059(ii); mandate T9.3
Kind: D
Fidelity: variant: finite model (a press variable, two states, two actions; `HcCommitment` ranges over all four policies `Bool → Bool`) -/
structure HcModel where
  /-- Prior weight of the cell (state, pressed). -/
  w : Bool → Bool → ℝ
  /-- The algorithm's value of (state, action). -/
  algoVal : Bool → Bool → ℝ
  /-- The implemented state's value of (state, action). -/
  implVal : Bool → Bool → ℝ

namespace HcModel

/-- The policy "stop when pressed, continue otherwise".
Source: line 57; mandate T9.3
Kind: D
Fidelity: exact -/
def stopWhenPressed : Bool → Bool := fun b => !b

/-- The policy "always continue".
Source: line 57; mandate T9.3
Kind: D
Fidelity: exact -/
def alwaysContinue : Bool → Bool := fun _ => true

/-- UDT's evaluation of a policy `π : press ↦ action` from the prior, trusting the **algorithm's**
values: `∑_{s,b} w s b · algoVal s (π b)`.
Source: line 57 ("UDT evaluates 'stop when pressed' from `P_1`"); mandate T9.3
Kind: D
Fidelity: exact -/
def udtValue (M : HcModel) (π : Bool → Bool) : ℝ :=
  ∑ s : Bool, ∑ b : Bool, M.w s b * M.algoVal s (π b)

/-- The updateful evaluation of action `a` at the pressed state under the **implemented** beliefs:
`∑_s w s true · implVal s a`.
Source: line 57 ("states whose implemented beliefs say 'continue'"); mandate T9.3
Kind: D
Fidelity: exact -/
def updatefulPressedValue (M : HcModel) (a : Bool) : ℝ :=
  ∑ s : Bool, M.w s true * M.implVal s a

/-- **`H_c` as a UDT commitment** (the definition of record): (a) UDT over the algorithmic trust
*commits* to stop-when-pressed — it is UDT-optimal among all four policies `Bool → Bool` and
strictly better than always-continue; (b) the updateful evaluation at the pressed state under the
implemented beliefs strictly prefers continue; (c) the two tables differ at some cell; (d) the prior
puts positive mass on *both* next-day states (the non-degeneracy T9.4 demands: a point mass on the
faithful state collapses (a) and (b) into agreement); (e) **the press correlates with corruption**
— positive association in the `2 × 2` prior table, `w(faithful, pressed) · w(corrupted, unpressed)
< w(corrupted, pressed) · w(faithful, unpressed)` (line 57's "if the button correlates with
divergence"). The commitment "the fully-updated self would not renew" is (a) ∧ (b). **Repair round
2** (audit r2 adversarial N1): the first version compared only two policies and had no correlation
clause, and was satisfied by a press-independent model in which UDT prefers *always stop*
(`hcIndep`, `Witnesses.lean`); the mandate's two-policy framing is a deviation disclosed in the
findings (F9.6).
Source: line 57; corr-core-038, 039; mandate T9.3, T9.4; audit r2 adversarial N1
Kind: D
Fidelity: variant: finite model; stronger than the mandate's two-policy form (optimality among all four policies, plus the correlation clause) -/
def HcCommitment (M : HcModel) : Prop :=
  (∀ π : Bool → Bool, M.udtValue π ≤ M.udtValue stopWhenPressed) ∧
  M.udtValue alwaysContinue < M.udtValue stopWhenPressed ∧
  M.updatefulPressedValue false < M.updatefulPressedValue true ∧
  (∃ s a, M.implVal s a ≠ M.algoVal s a) ∧
  (∀ s, 0 < ∑ b : Bool, M.w s b) ∧
  M.w false true * M.w true false < M.w true true * M.w false false

end HcModel

/-- **The atoms-level reading of an `HcModel`**: an `Implementation` realizes `M` on day `n` through
`bli-found`'s state atoms and a press sentence `β` when the algorithmic history prices each cell
`⌜𝑸_{n+1} = code s⌝ ⋏ β^{±}` by `M.w s b`, and the state system's tables price the two action
sentences by `M.implVal` while the algorithmic history conditioned on the state prices them by
`M.algoVal`. The LI-level `H_c` over `stateAtom`/`actionAt` is `HcCommitment M` for a realized `M`;
nothing non-trivial is proved about it beyond the finite instantiation (`Witnesses.lean`), as the
mandate directs. "My price list at `m` is `Q'`" has no sentence in FAF's language, so the split is
carried by the `Implementation` pair in the metalanguage (findings).
Source: line 55, 57; corr-core-036, 038; mandate T9.3 ("state it, prove nothing non-trivial")
Kind: D
Fidelity: variant: the finite model read through the atoms -/
def HcRealized (S : StateSystem) (I : Implementation) (n : ℕ) (code : Bool → ℕ)
    (β uSent : Sentence) (M : HcModel) : Prop :=
  (∀ s, code s ∈ S.states (n + 1)) ∧
  (∀ s b, I.algo n (stateAtom (n + 1) (code s) ⋏ (if b then β else ∼β)) = M.w s b) ∧
  (∀ s a, S.val (n + 1) (code s) (uSent ⋏ actionAt n (if a then 1 else 0)) = M.implVal s a) ∧
  (∀ s a, I.algo n (uSent ⋏ (stateAtom (n + 1) (code s) ⋏ actionAt n (if a then 1 else 0))) =
    M.algoVal s a * I.algo n (stateAtom (n + 1) (code s)))

/-! ## T9.4 — the degenerate next-day prior collapses the split -/

/-- Under `E5`'s unit sum, nonnegative prices and a unit price on the actual state atom, every
non-actual state atom has price `0`.
Source: line 59 ("the 'trivial' solution … `P_{n−1}(Q_n = Q) = 1` for the actual `Q`"); corr-core-039; mandate T9.4
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem nonactual_price_zero (S : StateSystem) (P : History) (h5 : E5 S P) (n : ℕ)
    (hnn : ∀ q, 0 ≤ P n (stateAtom (n + 1) q))
    (hdeg : P n (stateAtom (n + 1) (S.actual (n + 1))) = 1) :
    ∀ q ∈ S.states (n + 1), q ≠ S.actual (n + 1) → P n (stateAtom (n + 1) q) = 0 := by
  intro q hq hne
  have hsum := (h5 n).1
  have hsplit := Finset.add_sum_erase (S.states (n + 1))
    (fun q => P n (stateAtom (n + 1) q)) (S.actual_mem (n + 1))
  have hq' : q ∈ (S.states (n + 1)).erase (S.actual (n + 1)) := Finset.mem_erase.mpr ⟨hne, hq⟩
  have hsplit' := Finset.add_sum_erase ((S.states (n + 1)).erase (S.actual (n + 1)))
    (fun q => P n (stateAtom (n + 1) q)) hq'
  have hrest : 0 ≤ ∑ x ∈ ((S.states (n + 1)).erase (S.actual (n + 1))).erase q,
      P n (stateAtom (n + 1) x) := Finset.sum_nonneg fun x _ => hnn x
  have := hnn q
  linarith

/-- **T9.4 — the degenerate next-day prior collapses the split.** Under `E5`, nonnegative prices,
monotonicity of the action cells (`P_n(Q'_q ⋏ a) ≤ P_n(Q'_q)`, a coherence-type modelling
assumption on `P`, disclosed (c)) and `P_n(⌜𝑸_{n+1} = actual⌝) = 1`: every non-actual action cell
has price `0`, so `valueAlpha S P n a φ = P_n(⌜𝑸_{n+1} = actual⌝ ⋏ A_n = a) · Q̂_actual[φ]` — the
agent's evaluation sees exactly one next-day state, and the implemented/algorithmic split of T9.1
carries no content for it. This is the non-vacuity requirement on T9.3's witness: it must *fail*
`hdeg` (`Witnesses.lean`). `bli-trajectory` owns the degenerate solution itself
(`pointMass_not_nonDegenerate`).
Source: line 59; corr-core-039; mandate T9.4
Kind: L
Fidelity: exact; (c) coherence-type assumptions `hmono`, `hnn` on an arbitrary history (harmonised with the ledger, audit r1 N9)
Hyps: (a) `h5`, `hdeg`; (c) `hmono`, `hnn` (coherence-type assumptions on an arbitrary history) -/
theorem degenerate_collapses_split (S : StateSystem) (P : History) (h5 : E5 S P) (n a : ℕ)
    (φ : Sentence) (hnn : ∀ q, 0 ≤ P n (stateAtom (n + 1) q))
    (hnn' : ∀ q, 0 ≤ P n (stateAtom (n + 1) q ⋏ actionAt n a))
    (hmono : ∀ q, P n (stateAtom (n + 1) q ⋏ actionAt n a) ≤ P n (stateAtom (n + 1) q))
    (hdeg : P n (stateAtom (n + 1) (S.actual (n + 1))) = 1) :
    valueAlpha S P n a φ =
      P n (stateAtom (n + 1) (S.actual (n + 1)) ⋏ actionAt n a) *
        S.val (n + 1) (S.actual (n + 1)) φ := by
  unfold valueAlpha
  rw [Finset.sum_eq_single (S.actual (n + 1))]
  · intro q hq hne
    have h0 := nonactual_price_zero S P h5 n hnn hdeg q hq hne
    have : P n (stateAtom (n + 1) q ⋏ actionAt n a) = 0 :=
      le_antisymm (h0 ▸ hmono q) (hnn' q)
    rw [this, zero_mul]
  · intro h
    exact absurd (S.actual_mem (n + 1)) h

end Cleanroom.Corrigibility.CorrExoTrader
