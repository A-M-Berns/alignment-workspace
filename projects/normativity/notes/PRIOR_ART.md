# Prior art

Status: **living note; unregistered.** Preservation only — this records work
already identified as materially relevant to the normative-learning and
legitimacy line, so that it is not rediscovered or lost. Nothing here is a claim,
and nothing here has been subsumed by the current architecture.

Citations were checked against search results at the date of this note where a
link is given. Where a remembered label did not check out, that is said. One
author surname appears in backticks: it collides with the name lint, which
cannot distinguish a bibliographic citation from naming the program after a
person. The friction is filed in `PRIORITIES.md`.

## 1. Inquiry and service optimization

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
