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

**The test for *dependency* is about the current proof, not about history.** An
entry is a **direct mathematical dependency** or **formal substrate** when the
answer to

> would the canonical proof still stand if this theorem vanished from the reader's
> toolbox?

is *no*. It is **adjacent prior art** when the answer is *yes* — when the
repository's proof runs from definitions it states, and the external result merely
proves something similar. Having rediscovered a theorem does not make it adjacent;
invoking it in a proof does not make it merely adjacent either. §6 below was
reclassified on exactly this test in the September 2026 cleanup, and one entry moved
as a result.

Citations were checked against search results at the date of this note where a
link is given. Where a remembered label did not check out, that is said. One
author surname appears in backticks: it collides with the name lint, which
cannot distinguish a bibliographic citation from naming the program after a
person. The friction is filed in `PRIORITIES.md`.

**Three grades of citation appear here, and the difference matters for paper
writing.** A full entry with title, venue and year, marked *citation verified*, has
been checked against a source. An entry naming a work without that marking was
carried over from earlier notes and has not been re-checked. An entry marked
**exact source not yet pinned / literature review needed** records an *idea the
program uses* whose source has not been identified — the idea is not thereby
doubtful, but nothing in it may be cited until someone does the work. **No entry
here was completed by guessing a plausible work**, and where a remembered
attribution looked wrong it was demoted rather than replaced.

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

  *Checked 2026-09-03*, in answer to the open question recorded in §7. **The
  machinery cannot express `MayDispose`**, and the reason is deeper than a priority
  ordering failing to license the loser's release: Horty's apparatus computes a
  *proper scenario* — which defaults to reason from — so a defeated default is simply
  not selected, and **there is no account for a licence to operate on.** Nothing is
  owed, so nothing can be licensed to stop being owed. Of the round's three clauses,
  grounds have an image (the winning default; and in *variable priority* default logic
  the ordering is itself established by higher-order defaults, so the ground is in the
  record), a successor has none, and separation has none — the last because a default
  theory has **no participants**, not because the ordering is exogenous, which for
  Horty it is not. **Exclusion is challengeable in-system:** undercutting is a
  triggered default lowering the undercut rule's weight below a threshold, so the
  undercutter is itself defeasible. An exclusionary reason is therefore closer to the
  round's `dispose` than to its `settle`, and the two summands do not collapse.
  `.../rounds/2026-09-03-defeat-landing-horty-standing/HORTY.md`.

  *Verified against primary text, 2026-09-03*, namely **Horty, *Reasons as Defaults*,
  Draft #2, 16 August 2006** — the paper the book develops. Definitions 1–4 give
  `Triggered`, `Conflicted`, `Defeated` and `Binding` as functions of `⟨W, D, <⟩` and a
  scenario `S`, with a stable scenario a fixed point of `Binding`; §3.1 gives variable
  priority theories, where `δ <_S δ'` iff `W ∪ Conclusion(S) ⊢ d ≺ d'`; §3.2 gives
  threshold theories, where undercutting is a priority falling below `τ` and an
  undercut default "provides no reason of its own". Horty states that exclusionary
  reasons "can themselves be excluded" (§3.2 n. 16) and rejects a stratified hierarchy
  of orders. **The OUP 2012 book was not read** and remains unreachable; its
  contribution over the paper is the development of §3.2 into "exclusionary default
  logic" plus the Dancy material. A citation *of the book* still owes that check.

- **Pollock, "Defeasible Reasoning", *Cognitive Science* 11(4), 1987,
  pp. 481–518.** <http://www.horty.umiacs.io/courses/readings/pollock-1987-defreasoning.pdf>,
  DOI `10.1207/s15516709cog1104_4`.
  Distinguishes **rebutting** defeaters, which give a prima facie reason for the
  denial of the conclusion, from **undercutting** defeaters, which attack the
  inference without arguing the conclusion false. *Citation verified 2026-09-01 and
  again 2026-09-05, when the PDF was fetched from the URL above and its first page
  checked against the bibliographic data; the `umiacs.umd.edu` address this entry
  used to carry now redirects there.* What we take: the undercut/rebut split, which the reason-state
  round reproduces as an ordinary reason for `~App(sigma, c@n)` rather than as an
  attack primitive — and which, since 2026-09-03, is recorded as a **conceptual
  dependency in the strong sense** for the defeat line. *A caution on the citation:*
  Horty's 2006 paper attributes the undercutting distinction to **Pollock 1970**, and
  cites **Pollock 1995** for the mature treatment, not the 1987 paper this entry names.
  1987 is a real and citable source for the distinction, but a claim about where it was
  "first pointed out" should follow Horty and say 1970. The dependency for us is: the `answer` / `dispose`
  distinction *is* rebut/undercut, transposed from a belief's warrant to a debt's.
  `answer` rebuts the challenge-warrant; `dispose` undercuts it. The round did not
  arrive at two kinds independently.

- **Prakken, "An abstract framework for argumentation with structured
  arguments", Argument & Computation 1(2), 2010 (ASPIC+).** Structured
  argumentation with strict and defeasible rules, preferences, and attack
  relations. What we take: the vocabulary for stating what an attack *is* when
  arguments have internal structure.

  *Checked 2026-09-03* against the Modgil–Prakken tutorial (read directly). A defeated
  argument is excluded from the extension and leaves **no residue and no successor**;
  there is **reinstatement**, but it is computed by the semantics rather than being a
  licensed act with a recorded ground, which is the opposite of a transfer. The
  preference ordering is **exogenous** in canonical ASPIC+ — making preferences
  themselves argument conclusions is explicitly non-standard — so the attack relation
  is unauthored. ASPIC+ therefore has neither the successor clause nor the separation
  clause.

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

**Pettit was listed here and is removed.** An earlier draft credited him for
holding-responsible being a *relation between agents* rather than a property of one —
the shape behind answerability's creditor/debtor typing. The maintainer confirms **no
source was read for it** (`DECISIONS.md`, 2026-09-01), so it is not a dependency with
a missing citation; it is not a dependency. The removal is recorded rather than
silent, so a later reader can see the entry was examined and dropped.

Where that two-place shape needs an antecedent, **Brandom's scorekeeping** above is
the one the program actually uses. `wiki/Sources.md` separately cites **Fischer &
Ravizza, *Responsibility and Control*, Cambridge, 1998** for reasons-responsive
mechanisms.

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

- **P. M. Williams, "Notes on conditional previsions", School of Mathematical and
  Physical Sciences, University of Sussex, 1975; revised and published in
  *International Journal of Approximate Reasoning* 44(3), 2007, pp. 366–383.**
  <https://www.sciencedirect.com/science/article/pii/S0888613X06001034>. Coherent
  conditional previsions and the envelope theorem: an upper conditional prevision is
  the upper envelope of a family of additive conditional previsions. *Citation
  verified 2026-09-01; the 1975 report circulated unpublished for three decades, so
  cite the 2007 printing.* What we take: the conditional form of the coherence
  conditions.

- **Levi, *The Enterprise of Knowledge*, MIT Press, 1980.** Convex sets of
  probabilities and of utilities, indeterminate valuation, and E-admissibility.
  What we take: convexity of the credal set as a substantive commitment, and
  indeterminate value as a first-class state rather than ignorance about a
  determinate one.

- **Coherence, conditional constraints, and the linear-programming characterisation**
  — **candidate identified, not confirmed read.** The *result* the program uses is
  real and load-bearing: coherence questions reduce to linear feasibility, which is
  what makes the region machinery exact and finitely checkable.

  The attribution recorded here was originally the bare surname "Łukasiewicz", which
  read as a probable garble for Jan Łukasiewicz, whose work is many-valued logic and
  not this. **On the maintainer's recollection it is instead Thomas Lukasiewicz, and
  that checks out**: **Biazzo, Gilio, Lukasiewicz & Sanfilippo, "Probabilistic Logic
  under Coherence: Complexity and Algorithms", *Annals of Mathematics and Artificial
  Intelligence* 45, 2005, pp. 35–81**
  (<https://link.springer.com/article/10.1007/s10472-005-9005-y>), with the earlier
  **Lukasiewicz, "Probabilistic logic programming with conditional constraints",
  *ACM Transactions on Computational Logic* 2(3), 2001**. *Citations verified
  2026-09-01.* This line works in the **de Finettian coherence** setting — conditional
  constraints as interval-valued conditional probabilities, with nonlinear programs
  transformed into equivalent linear ones — which is the same tradition as Walley's
  lower previsions and sets of desirable gambles in §4 above, and is why it belongs
  beside them rather than in a probabilistic-logic section of its own.

  **Still not confirmed as read.** The identification is a plausible and now
  specific reconstruction, not a record of use. What the repository certainly relies
  on is the *reduction to linear feasibility*; whether it inherited that from this
  line, or from the older anchors **Hailperin (1965)** and **Nilsson, "Probabilistic
  Logic", *Artificial Intelligence* 28(1), 1986, pp. 71–87** (verified 2026-09-01),
  is a question only the maintainer can close.

  **What we take:** the reduction of coherence questions to linear feasibility.
  **What we do not take:** conditional-constraint entailment, default reasoning over
  it, or any of the complexity results.

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

  **Role: adjacent prior art, with the definition inherited.** Checked against the
  proof: `SERVICE_TRANSFER.md`'s Theorem T1 argues from the definition directly —
  Markov's inequality on `nu_N` puts the level set `{d > eps}` into the contiguity
  hypothesis, and `E_{mu_N}[d] <= eps + D mu_N(A_N)` closes it. **No external
  theorem is invoked**, and the proof would stand unchanged if Le Cam's lemmas were
  unavailable. So the dependency is on the *definition* and the *name*, which is a
  real inheritance of vocabulary and not of mathematics.

  **What we take:** the definition, and the concept's name. **What we do not take:**
  any lemma; the statistical-experiments setting; likelihood ratios; local
  asymptotic normality.

  **What must not be claimed.** That T1 is a new theorem. The sufficiency direction
  is the standard and expected consequence of contiguity, and the two-line proof is
  short precisely because the definition was designed to make it so. Any novelty
  claim is confined to **T2** — necessity for triangular arrays with `{0,D}`-valued
  defects — and to the **fixed-set / array separation**, and both are
  **literature review needed** before either is asserted anywhere outside this
  repository.

### 6.2 Flow feasibility and interval conditions

- **Gale, "A theorem on flows in networks", Pacific J. Math. 7(2), 1957**;
  **Hoffman's circulation theorem**. Feasibility of a demand function holds iff a
  cut-style inequality holds for every subset of nodes.
  <https://projecteuclid.org/journals/pacific-journal-of-mathematics/volume-7/issue-2/A-theorem-on-flows-in-networks/pjm/1103043501.pdf>

- **Horn, "Some simple scheduling algorithms", 1974.** Necessary and sufficient
  conditions for a feasible preemptive schedule with release dates and deadlines on
  a single machine, by reduction to a network-flow problem; described in the
  literature as one of the cornerstones of scheduling theory.

  **Role: direct mathematical dependency, for BD1's sufficiency.** *Reclassified in
  the September 2026 cleanup; the previous entry said "we take nothing formally" and
  was wrong.* `BOUNDED_DELAY_TRANSPORT.md` Theorem BD1 states that a plan exists iff
  `sum_{[u,v]} c <= sum_{[u,v+H]} a` for every interval, and its **sufficiency proof
  invokes the Gale–Hoffman feasibility condition by name**, using the interval
  neighbourhood structure (the consecutive-ones property) only to cut the check down
  to intervals. Remove Gale–Hoffman from the reader's toolbox and that proof does not
  stand. Necessity is self-contained.

  **What we take:** the feasibility theorem itself, as a cited step. **What we do not
  take:** the max-flow machinery, or any claim that the interval specialization is
  new — it is very probably a rediscovery of Horn's conditions.

  **A cheap way to make this adjacent again, not done here.** The round's own
  Theorem BD2 gives a self-contained route: a busy-period argument on FIFO — take the
  last date before which the backlog was empty, observe that all service since then
  went to claims arriving in the interval, and read off the violated interval
  condition — would prove sufficiency without any external theorem. That is a change
  to a merged round document rather than to a canonical one, so the September cleanup
  recorded the dependency instead of removing it. Either resolution is honest; only
  claiming independence while invoking the theorem is not.

  **literature review needed** — on whether the *cost* result (D4, the sliding window
  minimum `sum_t c_t min_{s in [t,t+H]} w_s`) has a classical statement. The
  feasibility half is certainly known; the cost half, with a date-varying concave
  charge, is less obviously so.

### 6.3 Earliest-deadline / first-in-first-out optimality

- **Jackson, 1955**, the earliest due date rule and its optimality for maximum
  lateness under preemption; **Horn, 1974** for the release-date version.

  **Role: adjacent prior art.** Checked against the proof: `BOUNDED_DELAY_TRANSPORT.md`
  Theorem BD2 gives a complete exchange argument in four lines — if a feasible plan
  serves a later claim earlier, both service dates are legal for both claims, so they
  may be swapped — and **invokes nothing external**. It would stand if Jackson's rule
  were unknown. Classical in substance, independent in presentation; the document's
  own remark that FIFO and earliest-deadline-first coincide under uniform deadlines is
  an observation, not a citation.

### 6.4 Farkas duality and infeasibility certificates

- **Farkas' lemma** and linear-programming duality, in any standard reference.

  **Role: formal substrate for one step; the main theorem is self-contained.**
  Checked against the proof: `EXISTENCE_AND_DUALITY.md`'s Theorem T8 — the soundness
  of the finite-horizon infeasibility certificate — is four lines of linear algebra over a convex hull and
  **invokes nothing**. The certificate *has the shape* of a Farkas pair, which is why
  it is called one, but nothing is imported to prove it sound. What does depend on the
  external theory is the adjacent remark that under a Slater point the per-path program
  has strong duality and the certificate is exact for that program; **that** step is a
  direct use of linear-programming duality.

  What is *not* classical, and is the round's actual open question, is that no converse
  is known **for the causal problem**: a program feasible on every settlement path
  separately may admit no causal policy, because the per-path relaxation hands the
  controller the path in advance. That gap is genuinely ours and is filed as
  `PRIORITIES.md` item 74.

### 6.5 Online algorithms and competitive analysis

- The standard competitive-ratio framework; and, for the delay setting, the
  **Online Service with Delay** and **Set Cover with Delay** line already recorded
  in §1.

  **Role: adjacent prior art — vocabulary only.** Checked against the proofs:
  `ONLINE_EXISTENCE.md` borrows the competitive-ratio *definition* and then argues
  from scratch, both for the positive result (a doubling-threshold rule achieves
  persistence whenever an offline scheduler can) and for the negative one (an
  adversary construction driving the achievable ratio to zero). **No external theorem
  is invoked**, and no competitive-analysis result is inherited.

  **literature review needed** — on whether the "no positive ratio for the
  accumulated resource, but the qualitative property survives" phenomenon has a
  name in the online literature. It feels like it should.

### 6.6 Convex projection and separating hyperplanes

- Standard convex analysis: projection onto a closed convex set, and the
  separating-hyperplane theorem.

  **Role: formal substrate — a genuine dependency.** The enforcement compiler's
  position `zeta = lambda(Pi_K P - P)` *is* a projection onto a closed convex set, and
  the argument uses the projection's defining variational inequality; the
  Common-Mixture bound is finite convex algebra over a barycenter. Remove convex
  projection from the toolbox and neither construction can be stated, let alone proved.
  Nothing here is novel and nothing should be presented as such; the content is in
  *what is being projected* and *who pays for it*.

### 6.7 Star-shaped and concave cost functions

  **Role: adjacent prior art, unverified.** Checked against the proofs:
  `SHARP_PERSISTENCE.md` states star-shapedness (`L(a)/a` nonincreasing) as a
  hypothesis and derives everything it needs from that inequality directly, invoking
  no external result. Star-shaped functions are a studied class in convexity theory,
  which is why the term is borrowed.

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
  priority.

  *The open question is answered, 2026-09-03:* **Horty's machinery cannot express
  `MayDispose`**, because his theory says what to conclude rather than what is owed,
  so there is no account for a licence to operate on. What is genuinely new on our
  side, phrased so a reader of the book can check it: **proper scenarios are a
  function of the current theory and of nothing in the history of defeats** — delete
  the record of which defaults lost, recompute, and the answer is unchanged. The
  defeat line's successor-bearing transfer makes the future depend on that history,
  which is the whole of the difference — and the point is verifiable from the
  definitions: `Binding` is a function of `⟨W, D, <⟩` and the scenario alone.

  *Said fairly, this is a difference of subject rather than a defect.* Horty's is a
  static theory — one default theory, compute its proper scenarios — and does not model
  a process over positions. **Checked against Horty's 2006 paper**, which carries the
  full apparatus; the 2012 book itself was not read. See §2 and the round's
  `HORTY.md`.

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
