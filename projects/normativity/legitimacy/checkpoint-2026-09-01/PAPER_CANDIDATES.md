# Extraction candidates

**Secondary deliverable. No paper is being written here.** This separates
research-program documentation from what might be a publishable claim, and its
main function is to say where the novelty confidence is low.

Four candidates. For each: the core contribution, its dependencies, novelty
confidence, the prior-art check that has *not* been done, and what would still need
proving.

---

## 1. Normative serviceability / Sharp Timely Service

**Core.** A claim stream owed to a normative reason, a schedule of enforcement
authority priced by a liability account, and an exact answer to when the second can
discharge the first: `liminf L_t(1) = 0` for persistence, `sum_t c_t min_{s in [t,t+H]} w_s < infinity`
for timeliness, and the composition theorem

    E_{mu_N}[d] <= L K (2 sqrt(B) + sqrt(U))/sqrt(A_N) + epsbar_N(T) + Dbar R_N/C_N .

The conceptual payload is the pair of separations: *persistence is not
timeliness*, and *cheap enforcement is not conforming enforcement*.

**Dependencies.** Traderized enforcement (for `U` and the per-date modulus);
Actionability (for the coercivity modulus); Service Transport.

**Novelty confidence: moderate, and lower than it first appears.** The
*composition* looks new. Several components have classical antecedents that the
round derived independently: BD1 is a Gale–Hoffman / Horn-1974 specialization, BD2
is an exchange argument in the Jackson/EDD family, and T1's transfer direction is
in substance Le Cam contiguity. See `../../notes/PRIOR_ART.md` §6.

**Prior-art check not done.** Whether D4's *cost* form (sliding-window minimum
against a date-varying concave charge) is classical. Whether the star-shaped vertex
optimum is standard. Whether the "no competitive ratio for the accumulated
resource, qualitative property survives" phenomenon is named.

**Still needed.** A construction for hypothesis (T). Simultaneous (S) and (L). At
least the headline in Lean. And the paper would have to be honest that its
scheduling half is a rediscovery with a new application, not new mathematics.

---

## 2. Liability theory for normative authority

**Core.** Making a bounded reasoner obey a constraint costs something, that cost is
a signed cumulative account over the live worlds, and preservation is exactly the
account staying above a floor. With: the Common-Mixture bound
`E_N(omega) >= -U(1-theta)/theta`; reasonwise accounting (per-row floors give a
uniform subset ceiling, and aggregate safety provably does not); and the strict
unbounded separation between conservative underwriting and signed-account
affordability.

**Dependencies.** Logical Induction and the traderized enforcement compiler.

**Novelty confidence: high** for the framing — "what does it cost to make a learner
obey, and when can it afford to" is not a question the LI literature asks — and
**moderate** for the theorems, which are finite convex algebra over a barycenter.

**Prior-art check not done.** Whether anything in the online-learning-with-
constraints or safe-RL literature has the signed-account shape. The nearest
analogue is probably budgeted or constrained online convex optimization, and that
comparison has not been made at all.

**Still needed.** Necessity of bounded liability (item 40) — without it the theory
proves "the known route no longer applies", not "no safe policy exists", and a
paper must say so. Sufficient state for the signed account.

---

## 3. Traderization and finite-time strengthening of Logical Induction

**Core.** A constraint compiles to a legal trading strategy inside the source's own
market recursion, giving per-date conformance `g_j(P_t) <= delta_t` while
preserving the criterion — a *finite-date* guarantee where the criterion gives only
an asymptotic one.

**Dependencies.** Logical Induction, directly. Kernel-checked in part.

**Novelty confidence: high**, and this is the candidate with the most Lean behind
it. It also engages a live criticism: nostalgebraist's objection is that asymptotic
inexploitability leaves finite behaviour almost unconstrained, and this construction
supplies a finite-date guarantee of a specific shape. That framing is worth stating
carefully and is currently **not** written down anywhere as such.

**Prior-art check not done.** Whether other finite-time strengthenings of the LI
criterion exist. Inductive Coherence is adjacent and is a different strengthening.

**Still needed.** The modified market's computability transcription
(`PROOF_CLOSURE.md` §VII). An efficiently presentable row family for coherence, or
a proof there is none (item 42).

---

## 4. Diachronic answerability under self-revision

**Core.** What must remain invariant if self-revision is not to erase prior
answerability: grounded replay of rule provenance; prospective protocol revision;
slice-wise conservation `c = Satisfied ∨ Disposed ∨ Remaining`; no semantic
laundering; and the answerability–service dichotomy. Deliberately non-conservative
about substantive norms — what is fixed is the auditable history, not any rule.

**Dependencies.** None mathematical; it is self-contained. Its counterparts are
three repository rounds and it already exists as a drafted note.

**Novelty confidence: moderate to high for the synthesis; genuinely uncertain for
the components.** This is the candidate most in need of a literature review before
any claim is made — three specific worries are recorded in
`../../notes/PRIOR_ART.md` §7: the join-semilattice conservation law versus belief
revision; anchored interpretation versus rigid designation and two-dimensional
semantics; and persistent-wait / idle-non-expansion versus standard fairness
arguments in concurrency. The third is the one most likely to already exist.

**Still needed.** Nothing, to state it. To make it *load-bearing*: a theory of
authorized disposition, which is the pivot for the whole Layer II programme.

---

## What is not a paper

**Legitimacy.** There is no legitimacy theorem, no legitimacy predicate, and the
decomposition is a research framing (`LEGITIMACY_DECOMPOSITION.md`). Writing it up
now would be publishing a plan.

**Corrigibility from legitimacy.** Two layers downstream of anything proved.

**The Progress schematic on its own.** It is a composition of the other pieces and
has no independent contribution once (1) and (2) are stated.

---

## One standing hazard

Three of the four candidates rest on results the repository derived independently
and that have classical antecedents. The program's habit of deriving rather than
searching is what produced the exactness, and it is also what makes an unverified
novelty claim likely. **Every candidate above should have its literature review
completed before any claim of novelty is made anywhere outside this repository.**
