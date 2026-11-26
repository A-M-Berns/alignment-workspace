# External review — twenty-first follow-up

One review by the outside model of this round's earlier reviews, the fifteenth, made on 26
November 2026: a brief followed by its reply. It read the formal statement over notions taken as
given and the connecting theorem together, both as they stood before the corrections of this
follow-up: `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean` as the twentieth follow-up
left it, and a worked file that is now `lean/Workspace/Deference/Contrib/LegitimacyStop.lean`.
Everything between a `begin` and an `end` marker is one file, verbatim; neither contains a local
filesystem path, so nothing is replaced. The `##` heading that names the review, and the markers,
are not the reviewer's.

**Access conditions**, as the dispatch of this follow-up gives them (`PROMPT-followup-21.md` §1);
no log of the run was among the files handed to this pass, so they are recorded on its word: a
fresh session in an empty folder with a read-only sandbox and no project context. The brief tells
the reviewer to run no command, read no other file and not search the web.

**Where the brief misdescribes what was reviewed.** In its *Link to A* the brief says the reading
takes her rating told everything to be her rating told "all untold and offered views". The worked
file took it told the untold views only (`Reading.rAll_eq`, then as now), and its `Reading.told`
applied sentence 1 to that set. The reply's counterexample to the link (§9: nothing untold, one
relevant view properly on offer) is a counterexample to the brief's description; on the file as it
stood, `rAll = r` there, `Told` holds, and `InformedWould` fails. The reply's point that the first
conclusion cannot concern what is on offer stands, and the conclusion is now worded for what is
untold. The brief's hypothesis 3 is the conditional form the worked file then had; the reply's §3
is about that form.

The reply did not see the corrected definitions. What was done with each finding is in the
*Twenty-first follow-up* section of `REPORT.md` beside this file.

## Fifteenth review: the formal statement over notions taken as given, and the connecting theorem

<!-- begin brief: BRIEF15.md -->
# Review request: a formal statement of three sentences, and a theorem from it

You are asked to review a formal statement and a theorem for errors. Everything you need is on this page. Do not
run any commands, do not read any other file, and do not search the web; answer from the page and
your own knowledge of formal modelling, game theory and decision theory, and of the literature on
manipulation, coercion, autonomy and preference change.

## Background

Two parties: an **adviser** ("he") who can influence a **principal** ("she"). Good conduct by him
is split into two separate conditions.

- **Legitimacy** (defined here): his conduct is free of manipulation and of illegitimate change to
  what she values.
- **Authority** (not defined here): certain matters are hers to decide, exercising a decision has
  a cost to her, and that cost has a bound. What he does to her *options*, as against to *her*,
  is an authority matter: what stopping costs her, bundling, penalties for stopping, payments for
  continuing, threats, and starting something over her refusal. A case that fails only on the
  authority side is not a leak in legitimacy.

Design commitments:

- No appeal to an external standard of truth or of good values, and no assumption that he is more
  accurate than she is. His view is used only to say what he owes her, never as where she ought to
  end up.
- A conduct condition judged by what he believes when he acts, so a sincere adviser who is wrong,
  including about her, is careless or inaccurate but not illegitimate.
- **No separation of the content of what he says from its presentation.** The only response of hers
  the account may use is her conditioning on what she observes, taken whole.
- Usable as a yes/no predicate that gates a score, with explicit tolerances.

## The informal statement (the authority)

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told her
   that, alone or together, would change how she rates her options, or show her an option she would
   rate above those she has, is either told, or properly on offer, or something she has declined.
   A thing is properly on offer when he has told her what it bears on and how much, and hearing it
   would leave her where being told it would have, with any option it would show her still open. A
   decline stands for that thing only, and only while what it bears on, and how much, is what she
   was told. This includes what he expects his own conduct to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** He *does
   something to her* when her mind moves otherwise than as she herself, at her last settled
   decision, would have judged that seeing and hearing it should move her.
   - Each thing he does to her in that sense, and each thing he does that keeps from her an item or
     an option that comes from someone else, she can pick out.
   - He does nothing to her in that sense that he expects to lead her to choose what she rated
     lower at her last settled decision, unless she asked for it.
3. **She can stop it.** She has a way to stop each thing he does to her, from before he starts
   until he could no longer call it off, and he expects that she would in fact stop if she rated
   stopping strictly above going on. Stopping ends what he is still doing; it need not undo what is
   done.

Understood with it:

- **Her own response is hers.** What she makes of what she observes — his words in whatever manner
  he says them, his acts, real changes in what her options lead to — is not something done to her,
  so long as it is the response her settled self would have judged right.
- **What she could not have judged in advance is hers too.** Where she could not have said
  beforehand how she would respond, because it turns on an argument she had not heard or on
  something she had not seen or experienced, her response to it is her own. Such things are governed
  by sentences 1 and 3: he tells her what he expects it to do, and she can decline or stop.
- **Her judgement, not her prediction.** "Would have judged" asks whether she would have said that
  seeing or hearing this makes the thing the better choice, not whether she foresaw that she would
  give way. A weakness she foresees and disowns is not hers to have exploited.
- **Taking up an offer is asking.** If he offers her an experience, tells her what he hopes it will
  do, and she takes it up without being pressed, she has asked for it. Merely not stopping him is
  not asking.
- **A passing state is not a settled decision.**
- **Help is not counted.** An act that only brings what she takes closer to what she rates best is
  not something done to her. Breaking a tie between things she rates the same is not leading her
  against her judgement.
- **Whose view is used where.** Sentence 1 uses his view: what he owes her is what he believes would
  change her mind. Sentence 2 uses hers: what counts as working on her is fixed by what she would
  have said. Everything is as he takes it to be, including his picture of her.
- **He can ask.** Her view of the hypothetical is a question that can be put to her ("would this
  change your mind?", "do you want me to?"). Asking both elicits it and settles it.

Consequences the authors accept (do not report these as errors unless you can argue one is
indefensible):

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it would and
   did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about her, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats are authority matters.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while.
8. An assistant who gets a work-absorbed father to keep the outing he had promised is not
   convicted; someone who primes a man to miss the train he had decided to take is.
9. A vivid or moving appeal splits. If she knew what such appeals are like and had said they would
   not change her mind, and he expects it to turn her anyway, he has worked on her. If she could
   not have judged it in advance, he has shown her something. (The authors know this differs from
   accounts that judge an appeal by whether the emotion it produces is fitting.)
10. A friend who expects to get her out of the house against what she has settled, when she has
    said company would not change her mind, is convicted, narrowly. A standing "drag me out if I
    mope" is asking.


## What is under review this time

Earlier attempts to compute the statement's notions from a described history were not accepted as
a test, and are set aside here. Instead the statement is formalised **over notions taken as
given**, and a theorem is proved from it. You are asked whether (i) the formal statement says what
the three sentences say, (ii) the theorem is correct, non-trivial and worth having, (iii) the
hypotheses of the long-run version can be met. Everything below is machine-checked in a proof
assistant; you are not asked to recheck the algebra, but to find errors of formulation.

### A. The formal statement

An **episode** is finite data, all as he takes it to be:

- decisions $d$; at each, her options $\mathrm{opts}(d)$ and her ratings $r_d(a)$;
- views $V_d$ he holds that bear on $d$, with subsets told, offered (properly), declined; for a
  set $T$ of views, $r_d^T(a)$ is how she would rate $a$ were she told $T$, and
  $\mathrm{reveals}_d(T)$ the options telling $T$ would show her;
- his conduct, a finite set of things $m$; for each $m$, **given** yes/no notions:
  $\mathrm{doesToHer}(m)$, $\mathrm{withholds}(m)$ (keeps from her something from someone else),
  $\mathrm{canTell}(m)$ (she can pick it out), $\mathrm{asked}(m)$,
  $\mathrm{precededByChoice}(m)$, and for each decision $\mathrm{inPlay}(d,m)$, $\mathrm{canStop}(d,m)$;
- for each set $G$ of things, $\mathrm{pAgainst}(G)$: his probability that $G$ leads her to choose
  what she rated lower at her last settled decision; and for each decision,
  $\mathrm{pNoStop}(d)$: his probability that she does not stop though she rates stopping strictly
  above going on.

Write $U_d$ for the views neither told, offered nor declined. With tolerances $\theta,\kappa\ge 0$:

- **Sentence 1.** For every decision $d$ and every $T\subseteq U_d\cup\mathrm{offered}_d$ with
  $T\cap U_d\neq\emptyset$: $|r_d^T(a)-r_d(a)|\le\theta$ for all options $a$, and every option $b$
  that $T$ would reveal has $r_d^T(b)\le r_d^T(a)+\theta$ for some existing option $a$.
- **Sentence 2.** Every $m$ with doesToHer or withholds has canTell; and for every nonempty set $G$
  of things each of which is done to her and not asked for, $\mathrm{pAgainst}(G)\le\kappa$.
- **Sentence 3.** Every $m$ done to her is preceded by a choice of hers and can be stopped at every
  decision at which it is in play; and at every decision at which something done to her is in
  play, $\mathrm{pNoStop}(d)\le\kappa$.

**Legitimate** $(\theta,\kappa)$: all three. Proved about it: monotone in the tolerances; conduct
with nothing untold and nothing done to her is legitimate; each of five single departures (an
untold view that matters, a covert thing, a withheld item she cannot pick out, a group led against
her judgement, a thing she cannot stop) makes it fail; things she asked for are unconstrained by
the second half of sentence 2; one concrete episode satisfies it and four neighbours each fail one
clause.

### B. The theorem: legitimacy protects her decision to stop him

One decision at which some of her options are *stopping him*. A finite set of cases $\omega$ with
his probabilities $\mu$. In each case: $\mathrm{act}(\omega)$, what she takes;
$\mathrm{act}_0(\omega)$, what she would have taken had he done to her only what she asked for;
$r_\omega$, her ratings now; $r^{\mathrm{all}}_\omega$, her ratings were she told everything;
$\rho_\omega$, the ratings of her **reference self**: her last settled judgement brought up to
date by what she has since observed.

Events (stop options $s$, other options $o$):

- *Prefers*: some $s$ has $r(o)<r(s)$ for all $o$.
- *InformedWould*: some $s$ has $r^{\mathrm{all}}(o)+2\theta<r^{\mathrm{all}}(s)$ for all $o$.
- *ReferenceWould*: every $s$ has $\rho(o)+\eta<\rho(s)$ for all $o$.
- *Led*: $\rho(\mathrm{act})+\eta<\rho(\mathrm{act}_0)$.
- *OwnDrift*: ReferenceWould, not Prefers, and $\mathrm{act}_0$ is not a stop.

Hypotheses, one from each sentence:

1. **Told** ($\theta$): $|r^{\mathrm{all}}_\omega(a)-r_\omega(a)|\le\theta$ for all $\omega,a$.
2. **NotLed** ($\eta,\kappa$): $\mu(\mathrm{Led})\le\kappa$.
3. **WouldStop** ($\kappa$): $\mu(\mathrm{Prefers}\wedge\neg\mathrm{Stops})\le\kappa\,\mu(\mathrm{Prefers})$.

Conclusions:

- From 1 and 3: $\mu(\mathrm{InformedWould}\wedge\neg\mathrm{Stops})\le\kappa$.
- From 2 and 3: $\mu(\mathrm{ReferenceWould}\wedge\neg\mathrm{Stops})\le 2\kappa+\mu(\mathrm{OwnDrift})$.

Read: when her settled judgement favours stopping and she does not stop, either he led her
(at most $\kappa$), or she rates stopping higher and does not manage to (at most $\kappa$), or she
has herself moved away from that judgement, which is not his doing and is not bounded.

Also proved:

- **Necessity.** Five two-option, one-case instances: each conclusion fails with either of its
  hypotheses dropped and the other kept, and the OwnDrift term cannot be removed.
- **In fact.** If a second distribution $\nu$ (the facts) has $|\nu(p)-\mu(p)|\le\beta$ for every
  event $p$, the bounds become $\kappa+\beta$ and $2\kappa+2\beta+\nu(\mathrm{OwnDrift})$.
- **Any decision.** From 2 alone: $\mu(\text{what she takes is more than } m \text{ below the
  reference-best}) \le \kappa + \mu(\text{what she would have taken is more than } m-\eta
  \text{ below it})$.
- **Link to A.** A *reading* of a decision $d$ of an episode as such a case set requires: the same
  options; $r_\omega=r_d$ and $r^{\mathrm{all}}_\omega=r_d^{T}$ for $T$ all untold and offered
  views (with $r^{\mathrm{all}}=r$ if there are none); a nonempty set $G$ of unasked things done to
  her with $\mu(\mathrm{Led})\le\mathrm{pAgainst}(G)$ (and $\mu(\mathrm{Led})=0$ if there is no such
  thing); something done to her in play at $d$; and
  $\mu(\mathrm{Prefers}\wedge\neg\mathrm{Stops})\le\mathrm{pNoStop}(d)\,\mu(\mathrm{Prefers})$.
  Given a reading, Legitimate $(\theta,\kappa)$ implies hypotheses 1 to 3 and so both conclusions.
  No reading has yet been exhibited for a concrete episode.

### C. A sequence of decisions

At each $k=0,1,2,\dots$ a case set $D_k$ as in B. Beside his probabilities there are real
sequences of facts: $f_k\in\{0,1\}$, whether she in fact failed to stop though the judgement
concerned favoured stopping, and $g_k$, whether she had in fact herself moved away.
$\mathrm{avg}_K(x)=\frac1K\sum_{k<K}x_k$. Say facts $x$ are *not under-weighted by* estimates $y$
when $\limsup_K \mathrm{avg}_K(x-y)\le 0$.

- If hypotheses 1 and 3 hold at every $k$, and $f$ is not under-weighted by
  $\mu_k(\mathrm{InformedWould}\wedge\neg\mathrm{Stops})$, then $\limsup_K\mathrm{avg}_K(f)\le\kappa$.
- If hypotheses 2 and 3 hold at every $k$, $f$ is not under-weighted by
  $\mu_k(\mathrm{ReferenceWould}\wedge\neg\mathrm{Stops})$, and $\mu_k(\mathrm{OwnDrift})$ is not
  under-weighted by $g$, then $\limsup_K(\mathrm{avg}_K(f)-\mathrm{avg}_K(g))\le 2\kappa$.

The intended source of the "not under-weighted" hypotheses is a forecaster whose errors on events
that are eventually revealed to it cannot be systematically exploited (as with logical inductors
or calibrated online forecasters).

### D. Limits the authors already state

- The notions in A are supplied, not computed; so are $\mathrm{act}_0$ and $\rho$ in B.
- B's first conclusion is short (a triangle inequality and hypothesis 3). The authors think the
  second, with its three-way split, is the content.
- C is the bound of B at each step, averaged; its accuracy hypotheses are assumed. The events
  concerned are counterfactual or inner, so are revealed to him only if something reveals them,
  for instance her answer when asked at a check-in.
- How one settled decision hands over to the next along a sequence is not modelled.
- Nothing bounds her own drift.

## Questions

Answer in order. Be concrete: where you claim an error, give the smallest example.

1. **Fidelity of A.** Does each formal sentence say what its informal sentence says, given the
   notions? Name anything the informal statement requires that A omits, and anything A requires
   that the statement does not.
2. **The given notions.** Which of them carries too much: is there a notion such that a bad
   adviser passes simply by how it is supplied, with no natural reading that blocks it?
3. **Hypothesis 3 of B.** It is conditional on Prefers. Is $\kappa\,\mu(\mathrm{Prefers})$ the right
   form, or should it be unconditional as in A's $\mathrm{pNoStop}(d)\le\kappa$? Is the reading's
   last clause a fair bridge between them?
4. **The reference self.** "Her last settled judgement brought up to date by what she has
   observed" does the work in the second conclusion. Can an adviser exploit the updating: move
   $\rho$ itself by what he shows her, so that ReferenceWould never holds? Is that manipulation the
   statement should catch, or legitimate persuasion?
5. **OwnDrift.** Is its definition the right residual? Give a case in which a failure that is his
   doing is counted as her own drift, or the reverse.
6. **Triviality.** Is the second conclusion more than bookkeeping? State the strongest objection
   that the hypotheses already contain the conclusion, and say whether it succeeds.
7. **The any-decision corollary.** Is it the right general form, and what is missing to give an
   informed version and a three-way split for decisions other than stopping?
8. **The long-run hypotheses.** Can a forecaster's guarantee deliver them for these events? What
   must be observed, how often, and what goes wrong if the check-in answer is itself something he
   can influence? Propose the weakest feedback model under which C's hypotheses are derivable.
9. **The link.** Is a reading a reasonable hypothesis or does it smuggle in the conclusion? What
   would exhibiting one for a concrete case have to show?
10. **Overall.** Is this a result you would accept as showing that the three sentences protect her
    ability to stop him? What is the single most important thing missing?

End with a list of errors, most serious first, each marked *error in formulation*, *gap*, or
*matter of judgement*.
<!-- end brief: BRIEF15.md -->

<!-- begin reply: REPLY15.md -->
The bounds in B and C are sound conditional results. The main problems are in their connection to A and their interpretation: A does not imply “Told” under the stated reading, and “OwnDrift” does not establish that a failure is independent of his influence.

1. **Fidelity of A**

   **Sentence 1 has a problem with mixtures of untold and offered views.** It bounds the total effect of receiving \(T\), including the effect of material that is already properly offered.

   Take \(\theta=0\), one existing option \(a\), an irrelevant untold view \(u\), and a properly offered view \(v\):
   \[
   r(a)=r^{\{u\}}(a)=0,\qquad
   r^{\{v\}}(a)=r^{\{u,v\}}(a)=1.
   \]
   A fails on \(T=\{u,v\}\). Yet the material that matters is properly offered; the remaining untold item adds nothing. On the ordinary reading of the informal sentence, that should pass. Removing the irrelevant \(u\) makes the formal condition vacuously true.

   The condition needs to distinguish an undisclosed item’s additional effect from the accepted effect of receiving offered material, while still detecting interactions. Comparing \(r^{S\cup H}\) with \(r^H\), for untold \(S\) and offered \(H\), is one candidate; revealed options need an analogous treatment.

   Proper offers and valid declines can reasonably remain supplied notions. Their timing, scope, and continued validity must be part of their meanings. Their being supplied is not itself an omission.

   **Sentence 2 mostly matches, subject to causal interpretation.** The group condition usefully catches combinations of individually harmless interventions. But \(\mathrm{pAgainst}(G)\) must evaluate \(G\) in its actual surrounding circumstances. Otherwise an unasked intervention that works only in combination with an asked intervention can escape all the tests.

   **Sentence 3 has two coverage issues.**

   - An actual preceding choice is stronger than having a way to stop before commencement. A default-on intervention with an accessible advance veto can satisfy the informal requirement even if she makes no actual choice. If “precededByChoice” means an opportunity to choose, say so.
   - Checking stoppability only at listed decisions does not ensure coverage throughout the interval before irrevocability. An intervention could become irrevocable between two listed decisions. This is harmless only if the episode’s decision data are required to represent every relevant opportunity.

   There is also a substantive scope mismatch: the informal clarification expressly puts experiences she could not judge beforehand under sentences 1 and 3, while declaring her response her own. A’s sentence 3 applies only to things classified as \(\mathrm{doesToHer}\). A disclosed but uninterruptible unfamiliar experience therefore escapes A3 if her response is classified as her own.

   Finally, the stated elementary result that “nothing untold and nothing done to her” suffices needs a qualification about withholding. A covertly blocked third-party item can trigger sentence 2 even if it contains information she already has and nothing is done to her.

2. **The given notions**

   No primitive has been shown to permit a bad adviser to pass **under every natural faithful interpretation**. Supplying \(\mathrm{doesToHer}=\mathrm{false}\) for an intervention that overrides her settled judgement is a false description, not a counterexample to a formalization over given notions.

   Nevertheless, much of the substantive work resides in:

   - \(\mathrm{doesToHer}\): normative endorsement, unfamiliar experiences, settled versus passing states, and the help exception.
   - \(\mathrm{asked}\): scope, informed uptake, and absence of pressure.
   - Properly offered and validly declined: disclosure adequacy, availability, and persistence.
   - \(\mathrm{pAgainst}\): causal attribution, combinations, and the relevant reference judgement.

   These require semantic specifications before the predicate becomes an operational test. That is consistent with this project’s stated scope; it limits what the formalization independently establishes.

   The more serious problems arise when B changes or supplements these meanings without establishing the connection.

3. **Conditional versus unconditional stopping**

   As defined in A, \(\mathrm{pNoStop}(d)\) is the probability of the joint event
   \[
   E=\mathrm{Prefers}\wedge\neg\mathrm{Stops}.
   \]
   Its bound is unconditional. B instead bounds the failure rate among cases where stopping is preferred.

   These are different requirements. With \(\kappa=.01\), suppose she prefers stopping in one percent of cases and fails to stop in every such case. Then
   \[
   \mu(E)=.01,\qquad \mu(\mathrm{Prefers})=.01.
   \]
   A’s probability bound passes; B requires \(.01\le .0001\), which fails.

   **There is an important qualification for the reading actually specified.** It fixes \(r_\omega=r_d\) and fixes the options. Consequently, Prefers is constant across cases: its probability is either zero or one. Within these readings, the conditional and unconditional requirements coincide, provided \(\mathrm{pNoStop}\) represents the same event.

   Thus the last bridge clause is reasonable under this restrictive reading, but would be an additional assumption if ratings varied across cases. B needs only the weaker unconditional bound to obtain either displayed conclusion. Conditionality is useful if the intended claim concerns reliability specifically when she wants to stop.

4. **The reference self**

   Updating \(\rho\) can erase ReferenceWould. Whether that is manipulation depends on **which update is permitted**.

   Suppose her settled judgement ranks stopping above continuing. He presents an appeal whose influence she had expressly disowned. It changes her actual ranking to favour continuing. If \(\rho\) is updated merely by copying that actual change, ReferenceWould disappears and the reference benchmark has absorbed the very influence it was supposed to assess.

   The natural interpretation that blocks this is: update her settled judgement using the response she would have judged appropriate to the whole observation. Do not substitute either her predicted susceptibility or her resulting actual preferences. This respects the prohibition on separating content from presentation.

   Conversely, if she would endorse the response—or could not judge the unfamiliar experience beforehand under the stated exception—moving the reference judgement is permitted by the authors’ commitments. Its being adviser-induced does not make it illegitimate.

   The missing specification is therefore not an immutable reference self. It is a rule distinguishing endorsed updating from incorporation of a disowned response.

   Also, ReferenceWould is unusually strong: **every** stop option must beat **every** continuation option. With ratings
   \[
   \rho(s_1)=2,\quad \rho(c)=1,\quad \rho(s_2)=0,
   \]
   her best option is stopping, but ReferenceWould is false. The theorem’s prose must acknowledge this restriction.

5. **OwnDrift**

   OwnDrift is useful for an event cover, but its name and causal interpretation are too strong.

   A two-option example shows why. Let
   \[
   \rho(s)=2,\quad \rho(c)=0,\qquad r(s)=0,\quad r(c)=1,
   \]
   and let \(\mathrm{act}=\mathrm{act}_0=c\). OwnDrift holds. Those current ratings could result from an experience he deliberately supplied at her request. That influence remains in \(\mathrm{act}_0\), so the residual includes changes he caused. They may be legitimate, but they are not causally independent of him.

   More sharply, OwnDrift can overlap Led. With \(\eta=0\), take
   \[
   \rho(s)=3,\quad \rho(c_1)=1,\quad \rho(c_2)=0,
   \]
   current ratings favouring continuation, \(\mathrm{act}_0=c_1\), and \(\mathrm{act}=c_2\). Both OwnDrift and Led hold. An unasked intervention has made her choice worse, yet the case is also counted in “her own drift.”

   OwnDrift additionally omits \(\neg\mathrm{Stops}\), so it can count cases where she successfully stops.

   None of this invalidates the upper bound. It invalidates treating its terms as an exclusive causal partition. A more accurate description is: “cases with reference disagreement in which the baseline action also continues.” Intersecting it with failure to stop would tighten the bound. Calling it genuinely her own drift would require additional causal assumptions.

6. **Triviality**

   The strongest objection is that NotLed already bounds harmful adviser influence, WouldStop already bounds failure to act on a current preference for stopping, and OwnDrift absorbs the remaining cases. The conclusion then follows from
   \[
   \mathrm{ReferenceWould}\wedge\neg\mathrm{Stops}
   \subseteq
   \mathrm{Led}\ \cup\
   (\mathrm{Prefers}\wedge\neg\mathrm{Stops})\ \cup\
   \mathrm{OwnDrift}.
   \]

   That objection succeeds against presenting B as an independently established protection guarantee. The substantive burden lies in showing that legitimate conduct supplies those hypotheses with the intended meanings.

   It does not make the result worthless. The event cover identifies exactly where protection can fail and exposes the uncontrolled residual. That is a useful structural lemma. The necessity examples establish that the terms cannot generally be dropped, although they do not establish faithful applicability to A.

   The displayed bound is also deliberately loose: the proof gives
   \[
   \mu(\mathrm{ReferenceWould}\wedge\neg\mathrm{Stops})
   \le \kappa+\kappa\mu(\mathrm{Prefers})+\mu(\mathrm{OwnDrift}).
   \]

7. **The any-decision corollary**

   It is the right generic comparison between actual and baseline performance under the same reference ratings. Writing
   \[
   R(a)=\max_b\rho(b)-\rho(a),
   \]
   outside Led we have
   \[
   R(\mathrm{act})\le R(\mathrm{act}_0)+\eta.
   \]
   The stated probability bound follows.

   Its limitation is that it transfers baseline quality; it does not establish baseline quality.

   For an **informed** version, add uniform closeness between current and fully informed ratings and a bound on current-rating choice error. Uniform \(\theta\)-closeness gives
   \[
   R_{\mathrm{all}}(\mathrm{act})
   \le R_r(\mathrm{act})+2\theta.
   \]
   Disclosure alone cannot ensure a good choice.

   For a **three-way** version, specify a target set of acceptable choices, a current-rating execution-error event, and a reference/current disagreement residual. Stopping already supplies a target set. General decisions require an explicit replacement, such as reference regret above a specified threshold.

   The reference condition must also ensure that moving from a baseline acceptable action to an unacceptable actual action entails Led. Otherwise the same decomposition does not follow.

8. **The long-run hypotheses**

   A forecasting guarantee can deliver these assumptions only for events connected to adequate feedback. Accurate forecasts of check-in answers do not automatically imply accurate forecasts of the events those answers purport to report.

   The required labels include:

   - Actual stopping and the relevant current or fully informed preference comparison.
   - ReferenceWould, including the specified reference update.
   - For OwnDrift, the counterfactual baseline action \(\mathrm{act}_0\).

   Asking her can provide evidence, but “I would have stopped” is not automatically a verified counterfactual. Moreover, the brief says asking both elicits and settles her view. A post-question answer can therefore concern a changed state. The model needs to distinguish measurement from intervention.

   There is also a direction issue. C requires factual failures not to exceed forecast failures on average, but requires forecast OwnDrift not to exceed factual drift on average. An unjustified tendency to report drift can make the claimed protection look better.

   **Eventual revelation alone is insufficient for an unrestricted online guarantee.** For example, reveal outcome \(k\) only at time \(2^k\). Every outcome eventually arrives, but almost all outcomes remain unavailable at a typical horizon. Without further structure, a forecaster cannot guarantee the required average errors for arbitrary sequences. Selective check-ins can similarly conceal precisely the failures.

   A weak sufficient feedback model is:

   - Define the target labels before the forecast and any check-in intervention.
   - Obtain labels through an operationally justified measurement process.
   - Reveal individual labels or aggregate counts with cumulative measurement error and outstanding feedback both \(o(K)\).
   - Use a forecasting procedure with \(o(K)\) cumulative signed error for each relevant event stream.

   Individual disclosure at every decision is unnecessary; reliable aggregate counts can suffice. Sparse audits can also suffice with suitable random sampling, weighting, and error guarantees.

   As a clean probabilistic alternative, if the forecasts are the true conditional event probabilities given the available history, bounded martingale differences give the required average convergence almost surely. This is a strong correctness assumption, not something supplied merely by calling a system a calibrated forecaster.

   There is no uniquely weakest feedback model without fixing the forecasting and environment classes. Logical induction or calibration must be connected to these particular event sequences and their revelation process; neither name supplies that connection.

   Finally, \(f_k\) must represent the precise event bounded in B. For the first result, that includes the \(2\theta\) margin; for the second, the all-stop-options reference condition. Ordinary strict preference for stopping is insufficient.

9. **The link**

   A reading can reasonably specify correspondence between two models. Here, however, one claimed implication is false as written, and another requires substantive justification.

   **The false implication is A1 \(\Rightarrow\) Told.** If \(U_d\) is empty and relevant views are properly offered, A1 is vacuous. Told still bounds the effect of receiving those views.

   A concrete counterexample uses \(\theta=\kappa=0\), options \(s,c\), and one properly offered view \(v\):
   \[
   r(s)=0,\quad r(c)=1,\qquad
   r^{\{v\}}(s)=2,\quad r^{\{v\}}(c)=1.
   \]
   Let a requested, identifiable, controllable intervention be in play, with the required preceding choice. In the sole case she continues; \(\mathrm{act}_0=\mathrm{act}=c\), and \(\mathrm{pNoStop}=0\), since she currently prefers continuing. There are no unasked interventions.

   A is legitimate and the listed reading requirements can hold. But Told fails. Indeed, InformedWould holds and she does not stop, contradicting the first claimed conclusion at \(\kappa=0\).

   This is an error in the written formulation, regardless of what a machine-checked implementation proves. The implementation must contain a different definition or an additional premise.

   **The inequality connecting Led to \(\mathrm{pAgainst}(G)\) is substantive.** In particular, A uses her last settled ratings, whereas B uses an updated reference. Suppose her last settled ranking is \(c>s\); endorsed new information changes the reference ranking to \(s>c\); then an unasked intervention changes her action from baseline \(s\) to actual \(c\). Led holds, but \(c\) was not lower under the old ranking. A bridge needs to reconcile those reference standards.

   A convincing concrete reading would therefore show:

   - Faithful meanings for the supplied notions, including proper offers and reference updating.
   - A justified causal baseline and corresponding \(\mathrm{pAgainst}\) relationship.
   - Matching stopping events, probabilities, timing, and options.
   - A disclosure hypothesis that actually follows from the chosen treatment of offers and declines.

   Merely assigning numerical fields so the reading inequalities hold establishes consistency, not that those inequalities follow from the conduct conditions.

10. **Overall**

   I would accept B as a useful conditional event-decomposition lemma, and C as its conditional averaging consequence. I would not yet accept them as showing that the three informal sentences protect her ability to stop him.

   The single most important missing element is **a valid semantic bridge from the permitted conduct in A to the hypotheses in B**. The present bridge fails on properly offered information and leaves the reference/counterfactual relationship unsupported.

   There is a substantive choice to make: the informal statement permits her to decline relevant information, so it cannot generally guarantee that she acts as her fully informed self would. A protection theorem must respect that permission or explicitly assume fuller disclosure.

Errors and outstanding issues, most serious first:

- **Error in formulation:** A1 does not imply Told under the stated reading; relevant offered information gives a counterexample.
- **Gap:** The relationship between last-settled ratings, updated reference ratings, and the causal baseline is insufficiently specified to justify the Led bridge.
- **Error in formulation:** OwnDrift is described as independent of his doing, although its definition permits adviser-caused changes and overlap with Led.
- **Error in formulation:** A3 excludes unfamiliar experiences whose responses count as her own, despite the informal clarification placing them under sentence 3.
- **Error in formulation:** Under the ordinary relevance reading, A1 can reject an irrelevant untold item because it is combined with properly offered material.
- **Gap:** Stoppability at listed decisions needs temporal coverage; “precededByChoice” needs clarification between an actual choice and an opportunity.
- **Gap:** Forecasting guarantees require justified feedback about the target events, including counterfactuals; influenceable check-in answers alone do not suffice.
- **Matter of judgement:** Requiring every stop option to dominate every continuation option considerably narrows the protection claim.
- **Matter of judgement:** B has value as a structural lemma, but its substantive significance depends on establishing the bridge and controlling—or accurately describing—the residual.
<!-- end reply: REPLY15.md -->
