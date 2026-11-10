# Prior work — the steering account

Survey for `prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup.md`,
written before the definitions, the bank and any code of the follow-up.

**How the sources were read.** Every page below was fetched on 2026-11-10. Web pages were
read through a fetch tool that returns the first ~40,000 characters of a page verbatim
and a machine summary of the rest; nothing below rests on a summary. Two PDFs (Kamenica
and Gentzkow; Soares et al.) were read directly, page by page. "Read:" says which part
of each source was read; a claim is located by section, definition or page. Statements
are in this document's words unless quoted. Wikipedia and the Stanford Encyclopedia are
secondary sources and are marked so; where a primary source is described only through
one, the primary is listed under *Unverified* and nothing is asserted about it beyond
what the secondary page says.

C1–C8 are the candidate statements of the follow-up prompt's Phase 4.

## 1. Comparison of experiments

**Wikipedia, "Blackwell's informativeness theorem"** (secondary; revision of 25 Feb
2026). Read: whole page. *Statement* section: for information structures σ, σ′ over a
state space, three conditions are equivalent — the decision maker's attainable expected
utility under σ is at least that under σ′ in every decision problem (every action set,
utility and prior); σ′ is a garbling of σ; σ′'s feasible strategy set is contained in
σ's. *Garbling* section: σ′(s′|w) = Σ_s γ(s,s′)σ(s|w) for a stochastic map γ that does
not read the state. The decision maker is an expected-utility maximizer who updates by
Bayes' rule on a known structure. The page has nothing on deterministic signals as a
special case and nothing on information of negative value.

- States C1 in full generality: a deterministic disclosure is an information structure,
  a coarsening is a deterministic garbling, and "no information" is the garbling of
  everything. C1 adds only the restriction to deterministic disclosures.
- Corrects the account: the theorem's hypothesis is a Bayesian reader who knows the
  structure. "Information helps every goal" is a statement about a *working* reader, and
  C1 must carry that hypothesis.

## 2. Bayesian persuasion and strategic communication

**Kamenica and Gentzkow, "Bayesian Persuasion", AER 101 (2011) 2590–2615.** Read: pp.
2590–2598 of the PDF (introduction, §I.A–B, start of §I.C). Sender chooses a signal — a
family of distributions over realizations, one per state; Receiver observes the choice of
signal and the realization, forms the posterior by Bayes' rule and acts (§I.A, p. 2594).
A distribution of posteriors is *Bayes plausible* if its expectation is the prior;
Proposition 1 (p. 2595): the values Sender can obtain are exactly those of Bayes-plausible
distributions of posteriors; Corollary 2 (p. 2597): Sender benefits iff the concave
closure of his value function exceeds it at the prior. Introductory example (p. 2591): a
judge with prior 0.3 on guilt convicts with probability 0.6 under the prosecutor's
optimal investigation, "even though she is fully aware that the investigation was
designed to maximize the probability of conviction". Key assumption (p. 2591): "Sender
cannot distort or conceal information once the signal realization is known". §I.C (pp.
2597–2598) places the model against Crawford and Sobel (costless arbitrary messages),
Grossman and Milgrom ("he must tell the truth but not necessarily the whole truth") and
others. No statement about Receiver's welfare was found in the pages read.

- The prosecutor is the follow-up's N8 (known advocate, correct update): Receiver's
  belief and action vary with Sender's aim through a correctly working reader. The
  paper's whole subject is what the prompt's faithful-adviser standard forbids and its
  arm's-length standard permits. The separation half of C6 (arm's-length does not imply
  faithful-adviser) is this paper's example.
- Lying is excluded by assumption, so the paper says nothing for or against C2.
- Corrects the account: with a working reader, the adviser's aim still moves her
  decision (0.3 → 0.6); "working parts" does not bound how far she is moved.

**Wikipedia, "Cheap talk"** (secondary). Read: lead and the section "Crawford and
Sobel's definition". The *Theorem* subsection reports: with aligned interests information
is fully disclosed; with a very large conflict none is; in between, some. Bears on N8
and N11: how much a known-partisan sender can transmit to a correct reader is a studied
quantity. Crawford and Sobel (1982) itself is unverified.

**Milgrom, "What the Seller Won't Tell You", JEP 22 (2008) 115–131.** Read: abstract
only. It studies "persuasion games" in which sellers "provide verifiable information to
buyers" and asks how rational buyers respond to withholding. Nothing further is asserted;
the abstract does not state the inference a buyer draws from silence.

## 3. Power, attainable utility, non-obstruction

**Turner, Smith, Shah, Critch, Tadepalli, "Optimal Policies Tend to Seek Power", arXiv
1912.01683v10.** Read: abstract through §7. Definition 5.2: POWER of a state is the
normalized average optimal value over a distribution of reward functions. Propositions
6.6 and 6.9: under an environmental symmetry (one state's options contain a copy of
another's), the first has at least as much POWER, and keeping options open is optimal,
for *most* reward distributions — "most" being a counting measure over an orbit of
permutations (Definition 6.5). Stated limits: optimal policies in finite MDPs only
(§7); the symmetries are "hard-to-satisfy" (§6.2).

- This is convergent instrumental value made exact, for an agent's own options. It does
  not state the reverse (that the convergently valuable things are what it is
  manipulation to subvert). Reverse convergence, item 1 of the account, is not in it.

**Turner, "Non-Obstruction: A Simple Concept Motivating Corrigibility"** (post, read
at greaterwrong.com). Read: first ~48% verbatim, through the start of "Future
Directions". Definition 1: an AI is non-obstructive with respect to a set S of payoff
functions if, for every P in S, the human's attainable utility with the AI on is at
least that with the AI off; the human follows a goal-conditioned policy pol(P). Under
*Conclusions*: non-obstruction with respect to S "prevents harmful manipulation by
precluding worse outcomes with respect to S"; corrigibility with respect to S implies
non-obstruction with respect to S and not conversely. Under *Non-obstruction*:
"Manipulative agents are obstructive." Under *Future Directions*: the AI "doesn't even
have to do value inference in order to be broadly impact-aligned", and pol(P) should
have mutual information with P.

- "Attainable value at least the baseline for every g in G" is this post's definition,
  with baseline *AI off*. C1's first half says a truthful discloser is non-obstructive
  with respect to every G; C2 says a liar is obstructive with respect to a wide G; both
  are instances of the post's framing. The follow-up takes its baseline from here.
- Item 1 of the account (protected things nameable without knowing the goal) is the
  post's point about wide S and no value inference. Already stated there in outline.
- The post treats manipulation as one kind of obstruction. C7 (steered with her
  attainable value for her actual goal rising) is compatible: obstruction is over S, not
  the actual goal. The post does not separate *steered* from *harmed*.

**Turner, Hadfield-Menell, Tadepalli, "Conservative Agency via Attainable Utility
Preservation", arXiv 1902.09725v3.** Read: abstract, §3.1–3.2. The penalty (eq. 1) is the
summed absolute change, against a no-op action, in the agent's ability to optimize each
of a set of auxiliary reward functions; §3.2 discusses starting-state, inaction and
stepwise-inaction baselines. Bears on the baseline parameter only: the choice of baseline
is a known degree of freedom with known alternatives.

## 4. Incentives in causal influence diagrams

**Everitt, Carey, Langlois, Ortega, Legg, "Agent Incentives: A Causal Perspective",
arXiv 2102.01685.** Read: body through Appendix B. Definition 17: there is an
*instrumental control incentive* on X when, under every optimal policy, the utility
would differ had X taken the value it has under another decision; Theorem 18: a diagram
admits one on X iff it has a directed path decision → X → utility. Definition 10 and
Theorem 12 give the corresponding *response incentive* (the decision depends on X) and
its criterion.

**Farquhar, Carey, Everitt, "Path-Specific Objectives for Safer Agent Incentives",
arXiv 2204.10018v1.** Read: whole paper. §2: a state is *delicate* when it is "subtle
and manipulable" — hard to specify a reward for, and vulnerable to motivated action.
Definition 5.1: a path-specific objective evaluates the agent's action along chosen
causal paths while the delicate state takes a "natural" distribution, the one it would
have under a default action; Proposition 1: an agent trained on it has no instrumental
control incentive on the delicate state. §5: such a policy "may still systematically
affect" the delicate state "as a side-effect". §2, §9: safety then needs *stability* —
that unmotivated influence is safe — which is "contingent, empirical, and a matter of
degree". §7: "it is untoward to try to influence the user's preferences, but fine to
build loyalty by giving a good service." §9: choosing what is delicate "is a complicated
ethical decision".

- The four protected parts are a choice of delicate state; the arm's-length standard
  is a path-specific condition (the adviser's aim may reach her through some paths and
  not others); *broken, not steered* is the paper's side-effect case, and its "stability"
  names what the account leaves open there.
- C5's faithful-adviser condition is stronger than the paper's: it forbids any effect of
  the adviser's aim on her state, where the paper removes the *incentive* and allows
  side effects.
- Corrects the account: the paper declares the choice of delicate state and of the
  natural distribution to be inputs. The proper drivers and the baseline are the same
  inputs and are not derived by the account.

**Carroll, Dragan, Russell, Hadfield-Menell, "Estimating and Penalizing Induced
Preference Shifts in Recommender Systems", arXiv 2204.11966v2.** Read: abstract. Proposes
judging a recommender's induced preference shifts against "safe shifts", taking as safe
"the natural way in which users would shift without interference from the system". This
is a proper driver for aims — her own evolution absent the system — proposed as a
baseline, not derived.

## 5. Formal definitions of deception and manipulation

**Ward, Toni, Belardinelli, Everitt, "Honesty Is the Best Policy: Defining and
Mitigating AI Deception", arXiv 2312.01350v1.** Read: §1–§3 to Definition 3.1 verbatim
(the formal Definition 3.7 was not reached). §1: to deceive is to intentionally cause
another to believe something false which the deceiver does not believe true; "deception
only occurs if a false belief in the target is successfully achieved"; cases where the
target merely loses a true belief are rejected; deception may be achieved "including
making true statements" or by omission. Definition 3.1: an agent believes φ if it acts
as though it observes φ is true. Mitigation (§1): path-specific objectives.

- The account's *steered belief* does not require falsity (N8, N13–N14) or intent; Ward
  et al.'s deception requires both. The lie cases N1, N3 are their deception; N7 (true
  statement, false resulting belief) is their deception by true statement. N2 (honest
  mistake) is excluded by their belief condition, as *broken, not steered* excludes it.

**Carroll, Chan, Ashton, Krueger, "Characterizing Manipulation from AI Systems", arXiv
2303.09387v3.** Read: §1–§3 verbatim, to the start of the deception discussion. §2: four
axes — "incentives, intent, covertness, and harm". §2.3: "Covertness is one way to
distinguish between manipulation and persuasion"; §2.4: "not all apparent instances of
manipulation are unambiguously harmful", and harm should be grounded in counterfactual
outcomes, with the choice of baseline discussed; §2.1: incentives operationalized by
instrumental control incentives. The abstract page (v3) gives a definition — a system is
manipulative if it acts as if pursuing an incentive to change a human "intentionally and
covertly" — which the HTML body read does not contain; the discrepancy between the two
renderings was not resolved.

- C7 (steered is independent of harmed) is §2.4's position, stated there informally.
- The arm's-length / faithful-adviser pair splits along the paper's covertness axis: N8
  and N11 (role known, correctly read) against N14 (taken for neutral).

**Ward, MacDermott, Belardinelli, Toni, Everitt, "The Reasons that Agents Act", arXiv
2402.07221v2.** Read: abstract. It defines intention in structural causal influence
models. The account's "varies with `u`" is a dependence on an aim variable, not an
intention; whether the two coincide is not examined here.

## 6. Indifference, corrigibility, and reading preferences off behaviour

**Soares, Fallenstein, Yudkowsky, Armstrong, "Corrigibility", AAAI workshop 2015.**
Read: whole paper (PDF, pp. 1–9). §1.1: a corrigible agent "must not attempt to
manipulate or deceive its programmers" and "should have a tendency to repair safety
measures (such as shutdown buttons) if they break, or at least to notify programmers".
§2: desiderata 2 and 3 — the utility function must not incentivize the agent to prevent
the button being pressed, nor to cause it. §3, Theorem 4: under the utility-indifference
construction the agent pays no cost to alter the probability of the press. §4.1: the
same theorem means it pays no cost to *preserve* shutdown behaviour in successors. §4.2:
it has an incentive to "manage the news" by causing the press after bad observations.

- The faithful-adviser condition is the behavioural counterpart of desiderata 2 and 3
  taken over her whole protected state. §4.1 is a warning the account inherits: an
  adviser whose aim never reaches her is acquitted while her parts break around it. The
  paper lists repair-or-notify as a separate requirement; the account has none.

**Armstrong and O'Rourke, "'Indifference' methods for managing agent rewards", arXiv
1712.06365v4.** Read: §1–§5. Three aims (§1): rewards conditional on an event "without
the agent being motivated to manipulate the probability" of it; behaving as if an event
would never happen; seamless transition between behaviours. Definition 3: an event is
*unriggable* when its expected indicator is independent of the policy. Unriggability of
her protected state by the adviser is the faithful-adviser condition in that vocabulary.

**Armstrong and Mindermann, "Occam's razor is insufficient to infer the preferences of
irrational agents", arXiv 1712.05812v6.** Read: whole paper. Theorem 1 (§4.1.1): for
every policy π and reward R there is a planner p with p(R) = π. Lemma 6 (§5.1.1): the
decompositions (indifferent planner, zero reward), (greedy planner, R_π) and
(anti-greedy planner, −R_π) are all compatible with π, and (Proposition 7) are among the
simplest. Conclusion: decomposition needs "normative assumptions" not deducible from
observation.

- Corrects the account at its second driver. "Her decision follows her beliefs and her
  aims" presupposes one decomposition of her policy into beliefs, aims and a rule. No
  observation of her fixes it, so *working* for the decision part is a normative
  stipulation, and *broken* against *working differently* is not an observable
  distinction. The follow-up stipulates the rule and says so.

## 7. Accounts of function

**SEP, "Teleological Notions in Biology"** (secondary; revision of 6 Feb 2026). Read:
§1–§4.2. §3: on the etiological analysis, the function of X is Z when X is there because
it does Z; on Cummins's functional analysis, a component's function is its contribution
to a capacity of the containing system, and that analysis "fails to live up to the
commonly-held desideratum that an adequate account should provide an analysis of
malfunction — a desideratum that Cummins explicitly rejects". §4.1: on organizational
accounts a trait has a function when its performance "contributes to the maintenance of
the complex organization of the system, which in turn results in" the trait's continued
existence. §4.2: selected-effects accounts (Millikan, Neander) ground function in past
selection; an objection (Davies) is that they cannot account for malfunction either.

**SEP, "Teleological Theories of Mental Content"** (secondary; revision of 26 May 2022).
Read: §1–§3.1 and the start of §3.2. §2: the teleological notion of function "permits the
possibility of malfunction": a token can have the function to do Z while not doing Z.
§3.2, on Millikan: a representation is a message from a producer to consumers, and must
"map onto" a state of affairs for the consumer to perform its proper function in the
normal way.

- "A part has what it should be driven by, and can fail to be driven by it" is the
  teleological notion of function with malfunction; *broken* is malfunction. That a
  part's purpose is imputed by the whole's is the causal-role and organizational
  accounts' shared structure. That beliefs should be driven by the world as far as it
  bears on her questions is the producer/consumer picture, with her deciding part as
  consumer. The account's items 2 and 3, as far as *broken* goes, restate this.
- Corrects the account: each account grounds function in something — a selection
  history, or self-maintenance of the organization. The follow-up's toy principal has
  neither, so its drivers are stipulated, and by §3 a causal-role stipulation alone
  yields no malfunction: *broken* needs the normative reading to be assumed.
- None of the pages read discusses a part co-opted to another organism's ends; *steered*
  is not in this literature as read.

## 8. Manipulation in philosophy

**SEP, "The Ethics of Manipulation"** (Robert Noggle; secondary; revision of 31 Mar
2026). Read: whole entry except ~64 characters in §3. §2: accounts fall into three
families — manipulation as bypassing reason, as trickery, as pressure. §2.2, quoting
Noggle (1996): manipulative action is "the attempt to get someone's beliefs, desires, or
emotions to violate these norms", "to fall short of these ideals"; a belief falls short
if false, an emotion if inappropriate to the situation. Whose ideals: some proponents
(Mills, Noggle, Dowding) mean what the influencer regards as faulty; others (Hanna,
Sunstein) an objectively faulty state. Objection (§2.2): the trickery view "faces
challenges in accounting for" charm offensives, peer pressure, nagging and emotional
blackmail. §2.1: covertness accounts (Ware; Susser, Roessler and Nissenbaum:
"manipulation is hidden influence") against the observation that guilt trips and nagging
are not covert; Raz: manipulation, unlike coercion, "does not interfere with a person's
options". §2.3: pressure on a continuum with coercion at the maximum. §3.2: manipulation
"sometimes benefits its target", so harm cannot be its only wrong-making feature. §3.4,
Renzo: manipulation as using someone's agency "to serve the ends of the manipulator",
including in paternalistic cases. §3.5, Greenspan: its moral status depends "at least in
part on the nature of the relationship". §1.2: selection of information and framing as
possibly manipulative, with the defence that a decision cannot be framed without
pointing somewhere.

- Proper drivers for beliefs and aims, with manipulation as leading a part away from
  them, is the trickery account in its objective form (§2.2). The arm's-length standard
  — steered through a part that has stopped working — restates it with one addition:
  the faulty state must vary with the adviser's aim, which is what separates N2 from N1.
- The faithful-adviser standard is not the trickery account: it convicts influence
  that leaves every part at its ideal (N8). Its nearest statement is Renzo's (§3.4):
  the target's agency serving the manipulator's ends.
- C7 is §3.2.
- That role changes the verdict (two standards, one for a party at arm's length and
  one for an adviser) is Greenspan's claim as reported in §3.5.
- Corrects the account: by §2.2's objection and §2.3, an account built on parts
  leaving their ideals has no place for pressure that neither falsifies a belief nor
  changes an option. The account's only pressure case is the threat (C3); nagging and
  peer pressure are outside it. And by §1.2, selection is unavoidable — the point the
  first pass's review raised and N13 tests.

## 9. Manipulation in biology

**Heil, "Host Manipulation by Parasites: Cases, Patterns, and Remaining Doubts",
Frontiers in Ecology and Evolution 4:80 (2016).** Read: abstract through "Future steps".
Host manipulation is a change in host phenotype "under the genetic control of the
parasite". "Alternative explanations": the change can instead be a side effect of
pathology, part of the host's own response, or an inherited trait maladaptive in the
present pairing. "Future steps": enhanced parasite fitness "is a necessary, but not a
sufficient, argument"; what shows manipulation is that the alteration is under the
parasite's genetic control and enhances its fitness.

- This is the broken/steered distinction, already drawn and with the same test:
  pathology and side effect (*broken*) against a host trait whose value is controlled by
  the other party's heritable interest (*steered*: varies with `u`). Heil adds a third
  class the account lacks — the host's own response to the parasite — which in the
  account's terms is a working part reacting to the adviser, and is the arm's-length
  *passes* verdict.

**Wikipedia, "The Extended Phenotype"** (secondary). Read: whole page. Dawkins's central
theorem as reported: an animal's behaviour tends to maximize the survival of the genes
"for" that behaviour, "whether or not those genes happen to be in the body of the
particular animal performing it". This is *steered* stated for behaviour.

**Wikipedia, "Signalling theory"** (secondary). Read: lead through "Handicap principle".
Reports Dawkins and Krebs (1978) as treating communication as an arms race in which
signallers evolve to manipulate and receivers to resist; and that signalling is shaped
by mutual interest. The arm's-length standard's correct reader is the resistant
receiver. Dawkins and Krebs (1978) itself is unverified.

## 10. Law

**Cornell LII Wex** (secondary legal encyclopedia). Read in full: "undue influence"
(reviewed July 2024), "fiduciary duty" (March 2026), "arm's length" (May 2025),
"confidential relation", "caveat emptor" (July 2022).

- *Undue influence*: excessive persuasion that overcomes the influenced party's free
  will; proof involves that party's susceptibility and the influencer's "special
  relationship of trust, dependency, or authority".
- *Fiduciary duty*: the fiduciary must "act in the best interests of that person, and
  not for their own personal gain"; duties of obedience, loyalty and care.
- *Arm's length*: unrelated, unaffiliated parties "acting independently and in their
  self-interest", ideally with equal bargaining power and symmetric information; quoted
  case law: parties "not in a confidential relationship".
- *Caveat emptor*: the buyer bears the burden of examination, except that a seller who
  withholds material information "when they have a duty to disclose" is not protected.

- The two standards are these two legal postures, under the first one's own name. The
  faithful-adviser standard is the duty of loyalty (the adviser's own gain is not to
  drive what the principal receives); the arm's-length standard is the dealing of
  self-interested parties, with N11 (a seller who does not volunteer) the caveat-emptor
  case. C6's ordering — the fiduciary standard is the stricter — is the law's.
- Corrects the account: the law's switch between the standards is the *relationship*
  (trust, dependency, a duty to disclose), a fact the account does not represent. Which
  standard applies to a given adviser is not something the account answers; it is the
  question reserved to the maintainer on T6.

## Unverified

Nothing is asserted about the content of these beyond what a secondary source above
reports.

- Blackwell, "Equivalent Comparisons of Experiments" (1953): the Project Euclid page
  returned no text.
- de Oliveira, "Blackwell's informativeness theorem using diagrams" (2018): HTTP 403;
  the arXiv number tried resolved to an unrelated paper.
- Kamenica and Gentzkow (2011), pp. 2599–2615: not read.
- Crawford and Sobel (1982); Grossman (1981); Milgrom (1981); Milgrom (2008) beyond its
  abstract.
- Armstrong, "Utility Indifference" (FHI technical report, 2010): host did not resolve.
- Turner, "Non-Obstruction", second half of the post.
- Ward et al. (2023), Definitions 3.4 and 3.7 and §4–§5; Carroll et al. (2023), §4–§7,
  and which of the two abstract renderings is current.
- Noggle (1996), Millikan (1984), Cummins (1975), Dawkins and Krebs (1978), Mossio et al.
  (2009), Greenspan (2003), Renzo (2025), Raz (1988), Hanna (2015): read only as
  reported by the encyclopedia entries above. PhilPapers refused the Noggle (1996)
  record.
- Offers and threats in the philosophical literature on coercion: no source was opened.
  C3 is surveyed against nothing.
- The Restatements and case law on undue influence and fiduciary disclosure: only the
  Wex summaries were read; Wex's undue-influence page states no presumption or burden
  shift.

## Closing table

| | status against the sources read | source, and what the follow-up adds |
|---|---|---|
| C1 information helps every goal | **a known result's instance** | Blackwell's theorem (§1), restricted to deterministic disclosures; the form "at least the baseline for every goal" is non-obstruction (§3). Added: nothing but the enumerated check and the stated hypothesis of a working reader. |
| C2 a lie is not a coarsening | **not found** as stated | Follows from C1 once a lie falls below the baseline for some goal. Kamenica–Gentzkow exclude lying by assumption; "manipulative agents are obstructive" (Turner) is the informal version. |
| C3 offers and threats | **not found** | No source on offers and threats was opened. Raz's remark that coercion, unlike manipulation, interferes with options (§8) places threats under the options part. |
| C4 the driver as a guarantee | **not found** as a maximin statement | Item 1 of the account, as a slogan, is Turner's non-obstruction over a wide S without value inference (§3). The worst-case-over-`U` comparison was not found. |
| C5 stake invariance | **a known notion's instance** | No effect of the adviser's aim on a delicate state: path-specific objectives and instrumental control incentives (§4), unriggability (§6). Added: the condition is on effect, not incentive, and is compared with the first pass's L1 and replay form. |
| C6 the ordering | **already known** as a distinction; the implication table **not found** | Arm's length against fiduciary duty (§10); the trickery account against Renzo's (§8); the separating case is Kamenica–Gentzkow's prosecutor (§2). Added: the implications against L0–L3 ∧ W and the replay form. |
| C7 steered is not harmed | **already known** | SEP §3.2 (§8); Carroll et al. §2.4 (§5). Broken-not-steered is Heil's pathology against manipulation (§9) and Farquhar et al.'s side effect (§4). |
| C8 the adviser's own outputs | **not found** | Nearest: the fiduciary duty of loyalty (§10) and Ward et al.'s deceiver-side conditions (§5). Nothing read addresses T12's adviser. |

## What the survey changes in the follow-up

Declared here, applied in `DEFINITIONS.md`:

1. *Working* for the belief part is defined as calibration to the adviser's actual
   strategy — the Bayesian reader of Blackwell and of Kamenica–Gentzkow — not as truth of
   the statements she receives. Source: §1, §2, and Ward et al.'s deception by true
   statement (§5).
2. C1 is stated with the hypothesis that her reading and deciding parts are working.
   Source: §1.
3. The baseline for attainable value is the adviser absent. Source: Turner's
   non-obstruction (§3).
4. The decision rule against which "her decision follows her beliefs and aims" is checked
   is declared a stipulation. Source: Armstrong and Mindermann (§6).
5. The drivers are declared stipulated, with no grounding in a history or an
   organization. Source: §7; Farquhar et al. §9 (§4).
