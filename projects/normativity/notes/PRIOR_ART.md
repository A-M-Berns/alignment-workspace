# Prior art

Status: **living note; unregistered.** Preservation only — this records work
already identified as materially relevant to the normative-learning and
legitimacy line, so that it is not rediscovered or lost. Nothing here is a claim,
and nothing here has been subsumed by the current architecture.

## How entries are classified

Since the September 2026 checkpoint every entry carries a **role**, because
"related work" is too coarse to be honest with. The roles, in decreasing order of
how much they constrain us:

| role | meaning |
|---|---|
| **direct mathematical dependency** | we use or inherit a theorem or construction |
| **formal substrate** | our objects and theorems are built *inside* a pre-existing framework |
| **conceptual dependency** | the source materially shaped the theory or its terminology |
| **adjacent prior art** | a close mathematical or conceptual analogue; the present result was derived independently and is **not** logically imported |
| **verification target** | our eventual theory should recover, explain or subsume it; it is not an input |
| **historical motivation** | motivated the question, contributes no current theorem or interface |

Two rules the program holds itself to.

**Do not claim philosophical dependence because a source sounds similar.** Several
entries below are *adjacent* precisely because the resemblance is real and the
dependence is not.

**Do not claim mathematical novelty merely because the repository derived
something independently.** Where overlap is plausible and unverified, the entry
says **literature review needed** rather than guessing. Independent derivation is
a fact about our process; novelty is a fact about the literature, and only the
second is a claim.

Citations were checked against search results at the date of this note where a
link is given. Where a remembered label did not check out, that is said. One
author surname appears in backticks: it collides with the name lint, which
cannot distinguish a bibliographic citation from naming the program after a
person. The friction is filed in `PRIORITIES.md`.

## 1. Inquiry and service optimization

*Role: **adjacent prior art** throughout. Nothing in this section is imported;
the entries mark analogues so a later round does not present one as new.*

- **Golovin & Krause, "Adaptive Submodularity: Theory and Applications in Active
  Learning and Stochastic Optimization", JAIR 42 (2011); extended abstract COLT
  2010.** <https://www.jair.org/index.php/jair/article/view/10731>,
  <https://arxiv.org/abs/1003.3967>.
  Generalizes submodularity to adaptive policies and shows an adaptive greedy
  policy is competitive with the optimal policy under that condition. What we
  take: a precise sufficient condition under which sequential information
  gathering has a tractable near-optimal policy.

- **Guillory & Bilmes, "Interactive Submodular Set Cover", ICML 2010.**
  <https://arxiv.org/abs/1002.3345>.
  Generalizes submodular set cover and exact active learning with a finite
  hypothesis class; greedy approximation guarantee with a matching hardness
  result up to constants. What we take: the interactive-cover shape — an
  adversary supplies responses and the learner must cover regardless — as a
  model of inquiry against a non-cooperative world.

- **Azar & Gamzu, "Ranking with Submodular Valuations", SODA 2011, pp.
  1070–1079.** Introduces the submodular ranking problem: order elements to
  minimize the average cover time of a family of submodular functions. What we
  take: the cost model in which *when* something is settled matters, not only
  whether.

- **Covering with delay.** Two verified anchors: **Azar, Ganesh, Ge &
  Panigrahi, "Online Service with Delay", STOC 2017**; and **Azar, Chiplunkar,
  Kutten & Touitou, "Set Cover with Delay — Clairvoyance is not Required", ESA
  2020**, <https://arxiv.org/abs/1807.08543>, which gives an
  `O(log n log m)`-competitive non-clairvoyant algorithm. *A previously
  remembered attribution of "set cover with delay" to Azar–Ganesh–Feldman–Roytman
  at STOC 2017 did not check out and is recorded here as not verified.* What we
  take: delay as a first-class cost, which is the shape of an outstanding
  answerability episode.

**Architectural conclusion, preserved.** Service semantics are general;
submodularity and adaptive submodularity are optional tractable subclasses, not
definitions of legitimate inquiry. What we do **not** take: any suggestion that
an inquiry failing a submodularity condition is thereby illegitimate, or that the
greedy guarantees transfer to a setting where what counts as coverage is itself
contested.

## 2. Reason representation

*Role: **conceptual dependency** for the vocabulary; **adjacent prior art** for the
machinery. Bears on the reason-state round and, since September, on the
answerability slice.*

- **Doyle, "A Truth Maintenance System", Artificial Intelligence 12(3), 1979.**
  Justification-based maintenance with IN/OUT labels and non-monotonic
  justifications. What we take: the identity-bearing justification structure and
  the dependency-directed account of what follows from what.

- **de Kleer, "An Assumption-Based TMS", Artificial Intelligence 28(2), 1986.**
  Labels propositions by the assumption sets supporting them rather than by a
  single current context. What we take: the environment/label separation as a way
  to hold several stances at once without switching.

- **Horty, *Reasons as Defaults*, Oxford University Press, 2012.** Default logic
  read as a theory of reasons, with priorities among defaults. What we take: the
  treatment of a reason's *weight* and *priority* as normative content rather
  than as substrate machinery.

- **Pollock**, on undercutting versus rebutting defeaters — the distinction
  between attacking a conclusion and attacking the connection. What we take: the
  undercut/rebut split, which the reason-state round reproduces as an ordinary
  reason for `~App(sigma, c@n)` rather than as an attack primitive.

- **Prakken, "An abstract framework for argumentation with structured
  arguments", Argument & Computation 1(2), 2010 (ASPIC+).** Structured
  argumentation with strict and defeasible rules, preferences, and attack
  relations. What we take: the vocabulary for stating what an attack *is* when
  arguments have internal structure.

**Preserved.** Support, provenance and defeat machinery is relevant prior art,
but reason representation is not normative force. What we do **not** take: the
identification of a stance with a computed label, or the assumption that a
maintenance procedure is part of the substrate — the reason-state round argues
the substrate is stateless queries and that maintenance is a nameable stance
policy plus caching.

## 3. Answerability and normative practice

*Role: **conceptual dependency**. These sources shaped what "answerability" names
in this repository. None supplies a theorem.*

- **Brandom, *Making It Explicit*, Harvard University Press, 1994.** Deontic
  scorekeeping: discursive practice as the tracking of commitments and
  entitlements attributed and undertaken, with the distinction between
  attributing and acknowledging. What we take: the scorekeeping model, the
  commitment/entitlement split, and the idea that normative status is instituted
  by practice rather than found.

- **Pettit**, on reasons-responsiveness and holding-responsible as a relation
  between agents rather than a property of one. What we take: answerability as a
  two-place relation with a creditor and a debtor, which is what an answerability
  root is.

What we do **not** take: any commitment to the inferentialist semantics these
accounts are embedded in. The architecture uses the scorekeeping shape and leaves
the theory of meaning alone.

## 4. Credal and normative statics

*Role: **formal substrate**. The credal state, the coherence conditions and the
linear-feasibility reduction are the framework our regions live inside.*

- **Walley, *Statistical Reasoning with Imprecise Probabilities*, Chapman &
  Hall, 1991.** Lower and upper previsions, coherence, and the behavioural
  interpretation via acceptable gambles. What we take: the coherence conditions
  and the sets-of-probabilities semantics that the credal state `C_t` is.

- **Williams**, on coherent lower and upper previsions and conditional
  coherence. What we take: the conditional form of the coherence conditions.

- **Levi, *The Enterprise of Knowledge*, MIT Press, 1980.** Convex sets of
  probabilities and of utilities, indeterminate valuation, and E-admissibility.
  What we take: convexity of the credal set as a substantive commitment, and
  indeterminate value as a first-class state rather than ignorance about a
  determinate one.

- **Łukasiewicz**, on probabilistic logic and the linear-programming
  characterisation of probabilistic entailment. What we take: the reduction of
  coherence questions to linear feasibility, which is what makes the region
  machinery exact.

**Preserved.** Credal and convex statics do not themselves provide learning,
legitimacy, or normative authority. What we do **not** take: the reading of a
credal set as already encoding what an agent ought to do, or of convexity as
justified by anything the current architecture has shown.

## 5. Main external comparison targets

*Role: **verification target** for Carroll et al. and `Demski`; **formal substrate**
for Logical Induction; **historical motivation** for Inductive Coherence. The
nostalgebraist entry is a standing criticism, not a target.*

- **`Demski`, "Learning Normativity: A Research Agenda", Alignment Forum /
  LessWrong, 2020.**
  <https://www.lesswrong.com/posts/2JGu9yxiJkoGdQR4s/learning-normativity-a-research-agenda>.
  Argues that norms are the result of negotiation among humans rather than the
  maximization of a value set, and that they are not learnable from behaviour
  alone; sets out desiderata including learning at all levels and uncertain
  feedback. This is the closest statement of the problem the normativity line is
  working on, and the nearest thing to a shared target.

- **Carroll, Foote, Siththaranjan, Russell & Dragan, "AI Alignment with Changing
  and Influenceable Reward Functions", ICML 2024.**
  <https://arxiv.org/abs/2405.17713>. Dynamic Reward MDPs; shows the
  static-preference assumption can implicitly reward influencing user
  preferences. What we take: the formal statement of why value revision must not
  be something the system is rewarded for causing — which is the same concern the
  value/operative separation addresses from a different direction.

- **Garrabrant, Fallenstein, `Demski` & Soares, "Inductive Coherence",
  arXiv:1604.05288, 2016** (previously "Uniform Coherence").
  <https://arxiv.org/abs/1604.05288>. Strengthens coherence to constrain finite
  approximations. Relevant as the immediate predecessor of the logical-induction
  criterion and as an alternative statement of what a good finite approximation
  is. *Author list taken from the arXiv listing rather than from the PDF.*

- **nostalgebraist, "on MIRI's 'Logical Induction' paper", 2017.**
  <https://nostalgebraist.tumblr.com/post/160975105374/on-miris-logical-induction-paper>,
  with discussion at
  <https://www.lesswrong.com/posts/5bd75cc58225bf0670375465/some-criticisms-of-the-logical-induction-paper>.
  Argues the desiderata are too weak: for any given mistake there is a logical
  inductor making it until an arbitrarily large `n`, so asymptotic
  inexploitability leaves the finite behaviour almost unconstrained. Directly
  relevant to any claim this line makes about what a logical inductor's
  guarantees buy at a date, and the criticism is not answered by anything in the
  repository.

- **Garrabrant, Benson-Tilsen, Critch, Soares & Taylor, "Logical Induction",
  arXiv:1609.03543, 2016.** <https://arxiv.org/abs/1609.03543>. The source the
  formalization is of; listed here for the citation rather than as a comparison
  target.

---

## 6. Mathematical prior art for the service and affordability line

Added at the September 2026 checkpoint, when the affordability round produced
results with real classical antecedents. **Three of these are places where the
repository plausibly rediscovered known mathematics**, and saying so is the point
of the section.

### 6.1 Contiguity of measures

- **Le Cam, "Locally asymptotically normal families of distributions", 1960**, and
  the contiguity notion he named around 1955–56.
  <https://encyclopediaofmath.org/wiki/Contiguity_of_probability_measures>,
  <https://en.wikipedia.org/wiki/Contiguity_(probability_theory)>. Two sequences
  `P_n`, `Q_n` are contiguous when `P_n(A_n) -> 0` iff `Q_n(A_n) -> 0` for every
  sequence of events; it extends absolute continuity to sequences.

  **Role: adjacent prior art, bordering on direct dependency.** The definition used
  in `SERVICE_TRANSFER.md` is *the same definition*, and Theorem T1 — that
  contiguity transfers `E_{nu_N}[d] -> 0` to `E_{mu_N}[d] -> 0` for uniformly
  bounded arrays — is in substance the standard consequence of contiguity (Le Cam's
  first lemma direction). What is not obviously standard is T2, the *necessity* for
  triangular arrays with `{0,D}`-valued defects, and the separation from
  **fixed-set contiguity** by a one-step delay.

  **What we take:** the definition and the transfer direction. **What we do not
  take:** the statistical-experiments setting, likelihood ratios, or local
  asymptotic normality — none of which appears here.

  **literature review needed** — on whether the array/fixed-sequence separation is
  recorded in the contiguity literature. The transfer theorem itself should be
  presented as *an application of contiguity*, not as a new theorem, and the round
  documents should be read with that in mind.

### 6.2 Flow feasibility and interval conditions

- **Gale, "A theorem on flows in networks", Pacific J. Math. 7(2), 1957**;
  **Hoffman's circulation theorem**. Feasibility of a demand function holds iff a
  cut-style inequality holds for every subset of nodes.
  <https://projecteuclid.org/journals/pacific-journal-of-mathematics/volume-7/issue-2/A-theorem-on-flows-in-networks/pjm/1103043501.pdf>

- **Horn, "Some simple scheduling algorithms", 1974.** Necessary and sufficient
  conditions for a feasible preemptive schedule with release dates and deadlines on
  a single machine, by reduction to a network-flow problem; described in the
  literature as one of the cornerstones of scheduling theory.

  **Role: adjacent prior art, and very probably a rediscovery.** `BOUNDED_DELAY_TRANSPORT.md`
  Theorem BD1 — a plan exists iff `sum_{[u,v]} c <= sum_{[u,v+H]} a` for every
  interval — is the interval specialization of exactly this. The repository derived
  it independently and should **not** present it as new.

  **What we take:** nothing formally, but the antecedent is close enough that the
  round's statement should cite it. **What we do not take:** the network machinery;
  the round's proof is a direct exchange argument.

  **literature review needed** — on whether the *cost* result (D4, the sliding
  window minimum `sum_t c_t min_{s in [t,t+H]} w_s`) has a classical statement.
  The feasibility half is certainly known; the cost half, with a date-varying
  concave charge, is less obviously so.

### 6.3 Earliest-deadline / first-in-first-out optimality

- **Jackson, 1955**, the earliest due date rule and its optimality for maximum
  lateness under preemption; **Horn, 1974** for the release-date version.

  **Role: adjacent prior art.** `BOUNDED_DELAY_TRANSPORT.md` Theorem BD2 — FIFO is
  optimal and complete for the transport problem — is the same exchange argument in
  a different costume. Independently derived, classical in substance.

### 6.4 Farkas duality and infeasibility certificates

- **Farkas' lemma** and linear-programming duality, in any standard reference.

  **Role: formal substrate.** `EXISTENCE_AND_DUALITY.md`'s finite-horizon overload
  certificate is a Farkas pair. What is *not* classical, and is the round's actual
  open question, is that no converse is known **for the causal problem**: a program
  feasible on every settlement path separately may admit no causal policy, because
  the per-path relaxation hands the controller the path in advance. That gap is
  genuinely ours and is filed as `PRIORITIES.md` item 74.

### 6.5 Online algorithms and competitive analysis

- The standard competitive-ratio framework; and, for the delay setting, the
  **Online Service with Delay** and **Set Cover with Delay** line already recorded
  in §1.

  **Role: adjacent prior art.** `ONLINE_EXISTENCE.md` uses the vocabulary and
  proves two things in it: that persistence has no online penalty as a *property*,
  and that there is **no positive competitive ratio** for accumulated authority.
  The second is a lower-bound construction of the usual kind.

  **literature review needed** — on whether the "no positive ratio for the
  accumulated resource, but the qualitative property survives" phenomenon has a
  name in the online literature. It feels like it should.

### 6.6 Convex projection and separating hyperplanes

- Standard convex analysis: projection onto a closed convex set, and the
  separating-hyperplane theorem.

  **Role: formal substrate.** The enforcement compiler's position
  `zeta = lambda(Pi_K P - P)` is a projection direction, and the Common-Mixture
  argument is finite convex algebra over the barycenter. Nothing here is novel and
  nothing should be presented as such; the content is in *what is being projected*
  and *who pays for it*.

### 6.7 Star-shaped and concave cost functions

  **Role: adjacent prior art, unverified.** `SHARP_PERSISTENCE.md` uses
  star-shapedness (`L(a)/a` nonincreasing) as the exact structural hypothesis for
  both the persistence criterion and the finite-horizon vertex optimum. Star-shaped
  functions are a studied class in convexity theory.

  **literature review needed** — on whether the vertex-optimum result
  (`max sum a_t = max_t L_t^{-1}(B)` for star-shaped costs on a budget simplex)
  is standard. It is a two-line proof, which is usually a sign that it is.

---

## 7. The diachronic-answerability line

- **Doyle 1979 and de Kleer 1986** (see §2) — **conceptual dependency** for the
  slice's provenance structure. The answerability slice's admission witness, with
  its cited evidence and licensing rule, is a justification in Doyle's sense with a
  historical identity attached.

- **Horty 2012** (see §2) — **conceptual dependency**, and the entry that most
  needs care. Horty gives priorities among defaults; the answerability line needs
  *authorized disposition*, which is a licence to stop owing something, not a
  priority ordering. **What we do not take:** the identification of defeat with
  priority. Whether Horty's machinery can express `MayDispose` at all is an open
  question and a good literature target.

- **Brandom 1994** (see §3) — **conceptual dependency** for the commitment ledger.
  The slice-wise conservation law `c = Satisfied ∨ Disposed ∨ Remaining` is a
  scorekeeping identity, and the vocabulary is his.

**literature review needed** on three things, all of them places where the program
may be reinventing something:

1. Whether the **join-semilattice content algebra** with a conservation law across
   transitions has an antecedent in belief revision or in the theory of
   commitments. The absence of a distributive law is the distinctive choice.
2. Whether **anchored interpretation** — a semantics fixed at incurrence and
   immune to later evaluator revision — is a named idea. It resembles rigid
   designation and it resembles two-dimensional semantics, and it is probably
   neither.
3. Whether the **persistent-wait / idle-non-expansion** pair has an antecedent in
   liveness and fairness in concurrency theory. The theorem's shape — permanent
   idleness must stabilize on a fixed blocker — is very close to standard fairness
   arguments, and the honest expectation is that it *is* one.
