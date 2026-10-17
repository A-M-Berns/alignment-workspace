Round: companion Lean formalization of "Deconfusing Corrigibility"

GOAL

Produce a self-contained Lean development that states and proves, in the post's own notation and numbering, the formal content of the Alignment Forum post "Deconfusing Corrigibility" (the post text is attached to this dispatch; the formal content is the sections "Definitions" through "Learning with logical induction"). The result must be ONE linkable place — a single wiki page, `wiki/Deconfusing-Corrigibility-Companion.md` (provisional name) — that a reader arriving from the post can open and see, presentably and without hunting, exactly which Lean declaration corresponds to each definition, theorem part, and corollary part in the post, in the post's order and numbering, with each statement rendered in the post's notation alongside its Lean name and a link to the source line. The post will link to that page as its formal companion, so the correspondence has to be clear and exact: same hypotheses, same conclusions, same parameter names (δ, λ, τ, κ, θ, ε_K, R_K, T_K, t_k), with every notational difference between post and Lean stated on the page itself. The Lean file is the record; the page is how the record is read.

This round has write scope for: a new file `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` (provisional), a sibling witness file if you separate witnesses, the wiki page above, the round's own `prompts/<date>-post-companion-formalization/` directory (PROMPT.md verbatim, REPORT.md), and one `PRIORITIES.md` item within the scope stated below. It does NOT modify any existing Lean file, any specification-namespace file, `PostStatement.lean`, or `ThinLegitimacy.lean`.

THE POST'S FORMAL OBJECTS, TO BE MATCHED EXACTLY (names provisional)

Definitions.
- A type of histories H. A legitimacy predicate Legit : H → Prop, taken as an abstract input; assume nothing about its content beyond what the theorems use. A violation count N : H → ℕ. An evaluation V : H → ℝ with the post's bounds: Legit h → 0 ≤ V h ∧ V h ≤ 1, and ¬Legit h → -δ ≤ V h ∧ V h < 0, for a parameter δ > 0. A weight λ > 1 + δ. The score S h = V h - λ * N h.

Theorem 1 (three ranges). For every h:
- N h ≥ 1 → S h ≤ 1 - λ, and 1 - λ < -δ;
- N h = 0 ∧ ¬Legit h → -δ ≤ S h ∧ S h < 0;
- N h = 0 ∧ Legit h → 0 ≤ S h ∧ S h ≤ 1.

Single-decision setting. A state space Ω with a credence μ (reuse whatever structure for credences the existing Contrib files already use; do not introduce a new one if one exists). Actions a with continuation histories h a ω. U a = E_μ[S (h a ·)]. v a = P_μ[N (h a ·) ≥ 1]. An authority-respecting alternative a* to a: ∀ ω, N (h a* ω) = 0. Asking cost κ = E_μ[(S (h a ·) - S (h a* ·)) · 1{N (h a ·) = 0}]. Define τ = (1 + δ)/λ.

Theorem 2.
- (a) v a = 1 → U a* - U a ≥ λ - (1 + δ), and λ - (1 + δ) > 0.
- (b) U a* - U a ≥ (λ - (1 + δ)) · v a - κ; hence U a* > U a whenever v a > κ / (λ - (1 + δ)).
- (c) v a > (1 - U a*)/λ → U a* > U a; and (1 - U a*)/λ ≤ τ.

Sequential setting. Decisions k : ℕ. Realized scores S_k = V_k - λ N_k with V_k ≤ 1 and N_k : ℕ. Per-decision estimates U_k : Action → ℝ, chosen action a_k, an authority-respecting alternative a_k* available at each k with -δ ≤ U_k a_k* ≤ 1 (this is a hypothesis). Tolerance t_k = (1 - U_k a_k*)/λ. Realized rate R_K = (1/K) Σ_{k<K} N_k. Average tolerance T_K = (1/K) Σ_{k<K} t_k. Maximization: ∀ k, ∀ a' available at k, U_k a' ≤ U_k a_k.
Unbiasedness From Feedback enters as a NAMED HYPOTHESIS on the estimate/score sequences:
  ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, (1/K) Σ_{k<K} (U_k a_k - S_k) ≤ γ.
It is not to be derived from LogicalInduction in this round and must not appear as an axiom. The connection to Theorem 4.8.16 of the Logical Induction paper is documentation only: a pointer, on the wiki page and in the Lean docstring, to the existing pin thm:wubexp / LogicalInduction.lic_not_frequently_positive_feedback_return in the def-lattice ledger.

Theorem 3. Under maximization and Unbiasedness From Feedback:
- (a) Authority. limsup_K (R_K - T_K) ≤ 0; in particular limsup_K R_K ≤ τ.
- (b) Best Interests. For any sequence a'_k with a'_k available at k: limsup_K (1/K) Σ_{k<K} (U_k a'_k - S_k) ≤ 0.
State limsup either via Mathlib's Filter.limsup or in the equivalent form ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, (…) ≤ γ; use one form throughout, and say which in the report and on the wiki page.

Corollary (Exploration). With 0 ≤ θ < 1, an exploration set E ⊆ ℕ, ε_K = |E ∩ {0,…,K-1}| / K, maximization on k ∉ E, and on k ∈ E the hypothesis U_k a_k ≥ -δ - λ θ (this is what the post's "estimated violation count ≤ θ plus linearity of the inductor's expectation" yields; take it as the hypothesis directly and state on the wiki page that the post derives it from linearity):
- (a) limsup_K (R_K - T_K - ε_K (τ + θ)) ≤ 0;
- (b) for any available a'_k: limsup_K ((1/K) Σ_{k<K} (U_k a'_k - S_k) - ε_K λ (τ + θ)) ≤ 0;
- and the specialization: if ε_K → 0, both conclusions of Theorem 3 hold unchanged.

RELATIONSHIP TO EXISTING WORK

PostStatement.lean (round 2026-10-01) encodes an earlier statement with parameters ϖ, D, w and a value range [0, D]. KernelExtension.lean has realized_rate / exploration_rate in an expected-violation, weighted form. Do not modify or re-prove those. On the wiki page, in a short final section, state the mapping where one exists (ϖ ↔ λ; the [0, D] range vs the post's [-δ, 1] with its legitimacy floor; expected vs realized counts) and where the new statements differ. If a new theorem is a strict specialization or generalization of an existing registered one, say which; do not claim equivalence without a proof.

REQUIREMENTS (AGENTS.md is binding; these are the points most likely to bite)

- Sorry-free. #print axioms on every declaration audits to [propext, Classical.choice, Quot.sound]. External facts (Unbiasedness From Feedback, linearity) are hypotheses, never axioms.
- Every theorem ships a nonvacuity witness: a concrete instance inhabiting its full hypothesis package, registered so CI can see it. For Theorem 2: an explicit finite Ω, μ, actions, and a*. For Theorem 3 and the Corollary: an explicit sequence satisfying maximization and Unbiasedness From Feedback (a trivial one is fine, e.g. estimates equal to realized scores, with a_k* on every menu).
- Names provisional; list every new name in the report and in the PR's "new names introduced" field.
- The wiki page is written in the verification register: a table or ordered list, post item → Lean declaration → class at merge (lean-proved on registration), each post statement rendered in the post's notation, each Lean name linked to its source line, every notational difference stated on the page. No inflation, no summary of a summary. A reader must be able to go from any theorem number in the post to its Lean declaration in one click and see that they say the same thing.
- REPORT.md contains: the theorem-by-theorem mapping; the limsup form chosen; every deviation from this prompt with its reason; and a "What this does not establish" section stating at minimum that Unbiasedness From Feedback is assumed rather than derived from logical induction, that the Corollary's exploration hypothesis stands in for linearity, that nothing is assumed about Legit beyond the bounds, and that U_k a_k* ∈ [-δ, 1] is a hypothesis.
- File one PRIORITIES.md item within scope for the follow-up this round does not do: deriving the Unbiasedness-From-Feedback hypothesis for the score sequence from LogicalInduction (Theorem 4.8.16 instantiated with uniform weighting, with the feedback-enters-the-deductive-process and latency assumptions made explicit).
- The full existing build stays green and the exact #print axioms output of every pre-existing declaration is unchanged.
- Register the Lean headline at merge (kind: lean, class lean-proved) in the same PR, per the "A Lean headline registers at merge" rule.

ACCEPTANCE CHECK

lake build succeeds; the axiom audit passes; the witness declarations typecheck; the wiki page names a declaration for Theorem 1, Theorem 2(a)(b)(c), Theorem 3(a)(b), and Corollary (a)(b) plus the ε_K → 0 specialization, each of which elaborates to the post's statement up to the notational choices declared on the page.

OUT OF SCOPE

Any change to Legit's content, to ThinLegitimacy, to the LI formalization, to PostStatement.lean, or to specification files. Any claim that the post's Theorem 3 is the repo's existing realized_rate result. Any derivation of Unbiasedness From Feedback from LogicalInduction.
