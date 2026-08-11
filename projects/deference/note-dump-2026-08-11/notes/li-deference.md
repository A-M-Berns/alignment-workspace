(These are human-written notes by Abram -- AIs are not intended to modify this file.)

# 0. Motivation & Background
Lately, I've been wanting to try and formalize _basin of attraction_ arguments for alignment as best I can (eg Paul's basin-of-corrigibility argument). In what ways might an AI (such as a modern LLM) be "good enough" to participate safely in RSI (eg, constitutional AI, deliberative alignment)? What's the appropriate distance metric (if any)? What does the AI need to be correct about, and what can it be wrong about? When are errors self-correcting over the course of self-improvement?

## 0.1 Deference
I'm taking inspiration from [[Deference Done Better]] (DDB)and [[a decision-theoretic approach for managing misalignment]]. These papers characterize alignment through an if-and-only-if statement linking epistemic trust to instrumental trust. The notion of epistemic trust is **Total Trust**; roughly, (without introducing notation carefully):
$$E_a (X | E_b(X)\geq y) \geq y$$
This is in contrast to other epistemic principles such as **Trust**
$$P_a(X|P_b(X)\geq y)\geq y$$
or **Reflection**
$$P_a(X|P_b(X)=y)=y$$
or **Tower**
$$E_a(X)=E_a(E_b(X))$$
The notion of instrumental trust, on the other hand, is **Value**, which roughly says that if the _novice_ is choosing between a collection of random variables (trying to choose the one which will be highest), they're OK with letting the expert choose on their behalf instead (they're happy or at least neutral about it). This notion of instrumental trust sets aside many potential decision-theoretic complications (of the sort which motivates UDT, for example).

In the setting of DDB, all of these principles collapse to the same thing under the further condition of **immodesty**, which essentially says that the expert knows its own probability distribution.^[The way DDB, and the literature on deference more generally, interprets this is instead "the expert doesn't know they are the expert" -- hence the terms modest/immodest rather than something like self-knowledge/self-ignorance. However, I think that interpretation makes less sense.] Previous literature focuses on the immodest case, or inconclusively debates what should happen in the modest case. DDB studies the **modest** case, where these principles do come apart, and shows that in that setting, Total Trust is the one which is equivalent to Value.

However, DDB makes another a big assumption which I have not mentioned yet: it assumes that all the sets involved are finite. In particular, the set of possible worlds is finite, which implies that the novice has narrowed down the expert's possible beliefs to a finite list (and likewise, the modest expert has narrowed down their own beliefs to a finite list). This does not seem like a particularly plausible way to model uncertainty about beliefs: I'm much more liable to think that someone's belief in (say) P = NP is anywhere between 0.1 and 0.0 (any real number in that range, or at least any rational number in that range) than I am to think it is one of some finite list of possibilities in that range.^[You could perhaps argue that the number of possibilities is restricted by physical limits, EG the number of atoms in a human brain. Perhaps so. However, I am uncertain about those limits (I don't have any particular such number in mind), and even if I weren't, I doubt that I would habitually propagate the consequences to how I think about what someone might believe; I would argue I'm better-modeled as imagining some real-numbered degree of belief without restriction. Still, it is not an open-and-shut case.] 

[[Deference and Infinite Frames]] shows that indeed, the Value$\iff$Total Trust result fails for infinite frames, in both directions. This makes the theorem feel quite fragile. Compounding this, the proof in DDB is also somewhat long and uninsightful (the authors call it "excruciating").

## 0.2 Logical Induction
I wanted to use logical induction (LI) as a model of both humans and AIs, because it provides a nice model of beliefs which improve over time. On the AI side, it resembles the progression of model version-numbers, each next AI improving on the previous. On the human side, it provides a good model of philosophical progress: prices (and, at a finer grain, trades) simultaneously play the role of _prediction_ and _evidence_. Prices (and trades) at a given time are _predictions_ about the future prices (trades), but _evidence_ about the quality of past prices (trades). This captures ideas related to reflective equilibrium in philosophy: philosophical intuitions act as evidence by which we judge philosophical theories, but doing philosophy also refines intuitions, hopefully improving them. Empirical observations can be seen as the special case where prices go to 0 or 1 (losing the ability to change thereafter, thus serving as evidence only, no longer predictions which are malleable to future evidence).

When can one logical inductor trust another? What kind of training process can be set up whereby one logical inductor trains another to adequately mimic its scientific-philosophical process? (LI is generally modeled as getting 0-or-1 feedback, but if another LI is treated the target, most sentences will not have 0-or-1 values!)

I was initially hopeful that the DDB result could be translated into the framework of Logical Induction due to the resemblance between the epistemic properties mentioned above and properties in the self-trust section of LI. I reasoned that the analogous proof would probably be simpler and more insightful as well, since LI imposes a broader range of rationality principles.

As it turns out, although LI is a modest setting in some sense (perfect self-knowledge for logical inductors is _contradictory_), the setting is "immodest enough" that the LI analogues of all the above principles collapse into one, similarly to the _immodest_ case in DDB's setting. This is because the appropriate LI analogue of a property is generally asymptotic (since rationality conditions are learned, rather than imposed at all times), and LI also learns about itself over time (so asymptotically speaking, it does have self-knowledge).^[This phenomenon probably depends in some respects on a logical inductor being computable and knowing its own mathematical definition; or to put it a different way, having good feedback about its own beliefs. I could perhaps see an argument that this is not a good model for human reasoning. Would logical inductors without good feedback about beliefs behave more analogously to DDB's immodest case?] This makes the LI version of DDB even simpler than I hoped!

## 0.3 Limitations
The results below fall significantly short of what I want out of a model of basin-of-attraction arguments. So far, I only claim to provide an analogue of the epistemic-trust$\iff$instrumental-trust" result from DDB, characterizing the conditions under which one logical inductor trusts another. This provides only a small amount of advice about building trustworthy AI, since it does little to clarify how to build AI which is epistemically trustworthy. 

My hope is that this can develop into a more informative picture. Imagine a model with a "slow but trusted" logical inductor $H$, representing idealized human scientific and philosophical progress, and a "fast but untrusted" inductor $A$, representing a potentially misaligned AI. Is there some way to construct a combined "fast and trusted" inductor? In one discussion about this, Sam Eisenstat conjectured that such a thing could be constructed by looking only at $A_n$'s beliefs about $H_{f(n)}$, where $f(n)$ is some speedup function. $A$'s beliefs about $H$ should converge to the same limit as $H$ does, which is a good start. Would they also be a logical inductor (satisfy the logical induction criterion)? Would they be trusted by $H$? Those two questions are the substance of the conjecture, although I consider the trust question to be more important than the inductor question.

My hope is that such a model could provide a picture of corrigibility, not just alignment. Think of the human feedback as a general way to "reprogram" the AI. Since the AI is simply trying to predict the human feedback, it has no incentive to block humans from fixing it. For example, if it knows the humans will reliably tell it that it should shut down tomorrow at noon, then it has already formed the opinion that it should shut down tomorrow at noon. Blocking the feedback channel would only deprive it of information, which should be negative expected value. There is, in some sense, no fully-updated-deference problem. (I expect there will still be limits on the sort of corrigibility which can be achieved, however.)

There are several potential conceptual problems, however. (Thanks to Anson Berns, Roman Malov, and Gurkenglass for relevant discussions.) 
 - The AI becomes a sort of time-travel machine, bringing human opinions back from the future, and acting on those future opinions today. Couldn't it bring something nasty back from the future?
	 - Self-fulfilling prophecies: some bad things could happen as a result of being predicted to happen, such as bank runs.
	 - Human manipulation: the sort of alignment provided by this framework does nothing (so far) to rule out an AI which manipulates humans into specific beliefs, since those beliefs would subsequently be confirmed by the feedback. In some sense the proposal eliminates a positive incentive to do this, but doesn't rule out the scenario altogether.
	 - Loss of control: such an AI could potentially cooperate with adversaries who wish to subvert the training process, since if it predicts that those adversaries may succeed, it will pre-emptively give weight to the feedback which it predicts they'll feed it in the future. This can include scenarios where the adversary is the AI itself.
 - How much and what kind of access do $A$ and $H$ have to each other? 
	 - $A$ needs to learn about $H$ in order to converge to the same limit, and more generally, in order to become a good model of human scientific-philosophical progress. Should we model human introspection as adequate to provide this? Humans have difficulty accurately articulating our beliefs, and especially, our values. Arguably, we want the AI to play an important role in figuring out human beliefs and values, rather than assuming that humans are able to articulate them accurately. This suggests that we want to actually _prove_ good feedback from some other assumptions, rather than assuming it outright.
	 - The humans obviously need some kind of access to the AI in order to come to trust it. However, this dramatically weakens the overall safety idea: the AI could corrupt the human scientific-philosophical process in various ways (over-reliance on AI, deception, manipulation, coercion, takeover) and that wouldn't register as a "problem" here. Put simply, the humans having good feedback about the AI creates a reason to question whether the human scientific-philosophical process is "trusted" as the AI gets increasingly capable.
		 - Arguably, we want something more CEV-like, where $H$ is not the _actual_ human scientific-philosophical process, but rather, a branched-off hypothetical timeline in which humans don't build AI. However, this raises questions of its own. 
			 - It is no longer plausible, I think, that $A$ should converge to _the same limit probabilities_ as $H$, since $A$ should know about the real timeline, not just the hypothetical timeline. This raises questions about whether (and in what sense) $H$ could be trusted by real humans, since it will get information wrong about the real timeline.
			 - On the other hand, it may not be plausible that we can 'fool' the humans in the hypothetical timeline about their situation. Even if they never build AI in their timeline, AI is still a mathematical construction which they can investigate theoretically. To what degree can $H$ really be isolated from $A$, given that it is supposed to go all the way to the limit of human investigation?

There are different ways one might seek to address the above problems, but my current sense is that I need to model the _legitimacy_ of feedback: the AI and the humans should anticipate that the training process can be corrupted, and seek to avoid that. The AI should only be trying to imitate human opinion in non-corrupted futures. All the actual feedback it gets should be assumed legitimate; the training process is predicated on its own non-corruption in the present. However, the legitimacy of future feedback should not be taken as a given; the humans have various beliefs about what would make the feedback corrupt, and the AI should only be trying to predict non-corrupt cases.

Consider human manipulation, for example. The AI should treat this like (sober) humans treat addictive drugs: you know that certain drugs are highly pleasurable, but you actively avoid them, rather than seeking them out. You treat them as corrupt feedback signals; the resulting epistemic states are illegitimate.



The difference between the version with no concept of legitimacy vs the legitimate-oracle case is precisely the difference between a 



Anson's work talks about the two routes: you can ask the AI to predict actual future humans, in which case you're vulnerable to self-fulfilling prophecies, or you ask the AI to predict a counterfactual world in which humans don't have the AI advice, in which case its predictions cannot be trusted as corresponding to the real world. This is a classic problem that has plagued oracle AI / epistemic AI proposals. I'm suggesting that we aim between these extremes, in some sense, by predicting conditional on legitimacy, while also making sure that feedback is in fact legitimate. The AI gets feedback about what illegitimate worlds look like from the humans, and can help humans navigate away from those worlds. This is unlike previous counterfactual oracle proposals as far as I am aware, which had to actually deny humans access to the oracle probabilistically in order to get feedback about such things. Legitimate oracles can get feedback about a state without visiting it, _and_ they have the advantage of trying to predict the world that actually happens, rather than the one it'll get weaker feedback about.

Perhaps predicting _conditional on_ legitimacy is not quite right. Rather, the AI should be predicting _reality_, which correlates with feedback in legitimate worlds, and doesn't in illegitimate worlds. Conditioning on legitimacy would make the AI confidently predict legitimacy; we want accurate assessments of risks to legitimacy, too!

I'll say counterfactual oracle to mean the AI safety scheme where you try to make a safe, purely epistemic superintelligent AI by predicting _what would happen if the AI didn't make its prediction_. On the other hand, an actual oracle predicts the real world. An actual oracle is unsafe because of the fixed-point problem; it has to choose self-fulfilling prophecies, and that can easily get dangerous. For an actual oracle, you have to choose the fixed points carefully somehow. The most obvious way to do this is by choosing the highest-expected-value fixed point (fixdt), which requires solving the rest of the alignment problem. In some sense I think this is the right direction, but it abandons the hope for purely epistemic AI. Counterfactual oracles attempt to fix this problem by predicting counterfactual worlds. This has the downside of not predicting the stuff you actually want to predict -- the humans have to figure out the relevance of the counterfactual predictions to the real world. It also has the downside of being harder to train: you're aiming to predict a counterfactual. Counterfactual oracles are made safe (modulo leakage between the actual world and the counterfactual) at the cost of having to predict a world that isn't ours, which is both hard to measure and hard to interpret for use in our world. (CEV is essentially a counterfactual oracle in this sense.) Legitimate oracles fix both of these problems by predicting the real world, so that it is easy to get feedback and easy to interpret predictions. Legitimacy is just the negation of corruption: worlds with corrupt feedback aren't truth-tracking. Legitimacy needs to be defined as a direct modification of the LI versions of Total Trust or Tower or Reflection, one of those epistemic-trust principle variants which (if I understand correctly) are all equivalent to Value in the LI setting. LI comes to trust its future self in these senses because it of course learns over time that its feedback is always legitimate; however, at finite times it may doubt this and believe its feedback to be illegitimate. A finite being who trusts too strongly is going to like the sound of wireheading, going to be vulnerable to self-fulfilling prophecies, etc. This is very much based on a map-territory-correspondence notion of truth. To modify Tower in particular: expectations of the future should equal [expected future expectations, conditional on legitimacy] * [probability of legitimacy] + [average corrected future expectations, conditional on illegitimacy] * [probability of illegitimacy]. To modify Reflection: conditioning on legitimacy, reflection holds; that is, conditioning on legitimacy and our future self thinking x, we think x. The function from conditioning on illegitimate belief in x to y is the correction function.



Some other open questions:
 - **Inner alignment problems**. I consider the work here to be outer-alignment only, since the guarantees are all asymptotic. Malign hypotheses will be eliminated by the training process _eventually_, if the process continues indefinitely, but realistically, malign hypotheses could cause catastrophic problems which end or corrupt the training process before that point. 
 - **Ontology mismatches between humans and AIs**. Since I'm only doing outer-alignment here, the "beliefs" of the AI are only its outwardly-expressed beliefs, which are forced by the training to be expressed in the same language as the humans use. This does not model deep problems of ontology mismatch between humans and AIs, nor does it have much to say about ontology-shift problems.
 - **Decision theory**. The framework here, like DDB, is decision-theoretically unambitious. It does not take a well-considered stance on CDT vs EDT, it does not seek to model the decision-theoretic consequences of environments containing powerful predictors, and it ignores updatelessness.
 - **Complexity Theory**. The current work models AIs which are smarter than humans in raw processing power by assuming the AIs consider hypotheses from a larger complexity class. This is not necessarily a good model of the difference between humans and AIs. EG, humans seem to generalize better on less data than AIs. This is consistent with humans having the larger complexity class, and AIs having other advantages.
 - **Eliciting Latent Knowledge**. Can we prove positive results in the ELK setting with a framework like the one developed here? Motivate reasons why humans understanding AI can justify trust? Achieve bounded-loss versions of ELK reassurances, that the humans won't regret not knowing something the AI was thinking? Use trust results to motivate specific notions of latent knowledge?
 - **Corrigibility**. What can we say about corrigibility in this setting? I expect we can get some positive corrigibility results conditional on legitimacy, meaning you can get corrigibility if you can keep belief in legitimacy high. In the version without any legitimacy, corrigibility is high in general. Fully-updated-deference is established through the time-travel-like quality.
 - **Wireheading**. I expect some anti-wireheading results based on a model of legitimacy as well. This is closely related to no-human-manipulation results.
 - **Embedded Agency**. Can this model be extended into a more serious embedded agency model, containing an account of when we should model something as an agent? Does this model of agent identification also say something about agent boundaries? Can we model agents cooperating and merging into one agent, perhaps with communication channels playing the role of the market? 
 - **Purely Epistemic AI**. Can we show, in some sense, that there's no misaligned agency in the AI, perhaps such that we can give it a purely epistemic goal? Since all the feedback is in fact legitimate, there can be no misaligned goals in there, otherwise there'd be a trader who exploited it?? Therefore, it is purely predicting (things which include subjective values), deciding any fixed point question in the way we would want it to be decided (if we want it decided in a purely epistemic way, whatever we mean by that, we can seek to enforce that on the human reasoning used as feedback). Clearly this isn't true except in a nearly-meaningless asymptotic sense, but that's not nothing. It could be an interesting analysis, and it might spark better ideas. Or there might be some strong impossibility results! Perhaps predictions cannot be purely epistemic, for any number of reasons.
 - **Non-Modification Theorem?** Can we show conditions under which the humans don't have cause to modify the AI, and the AI doesn't have cause to modify itself? This could be an easy corollary of the basic trust picture.
 - **Whispering Earring Problems**. If the humans are using the AI to help themselves think, then predicting future humans might mostly be the AI predicting itself. This is a form of illegitimacy. 

# Formalism
Fix some language $\mathcal{L}=(\mathcal{S}, \vdash)$ in which beliefs will be expressed, with $\mathcal{S}$ the set of propositions and $\vdash$ representing the consequence relation. It should be capable of representing computable functions, statements about real numbers, and anything else important to humans. A __belief state__ over $\mathcal{S}$ is a function assigning each sentence $s \in \mathcal{S}$ to a real value $f(s) \in [0,1]$. An __epistemic process__ is a sequence of belief states, written in blackbord-bold with a subscript, EG $\mathbb{P}_n$. I call the subscript "days" ("what $\mathbb{P}$ believes on day $n$").

In particular, we will be interested in modeling two epistemic processes: $\mathbb{H}$ representing **human philosophical and scientific progress**, and $\mathbb{A}$ representing **AI progress**.

In order to require bounded rationality of an epistemic process $\mathbb{P}$, associate it with a complexity class $\mathcal{C}_P$, closed under polynomial overhead. Unless stated otherwise, we assume $\mathcal{C}_H \subset \mathcal{C}_A$; for example, $\text{P}\subset \text{EXP}$. This represents a scenario where AIs are smarter than humans in raw computational terms.

For a given complexity class $\mathcal{C}$, a $\mathcal{C}$-**inductor** satisfies the logical induction criterion relative to $\mathcal{C}$; roughly, no $\mathcal{C}$-computable strategy can systematically improve the epistemic process (a computationally bounded analogue of no-dutch-book). $\mathbb{H}$ and $\mathbb{A}$ will be $\mathcal{C}_H$- and $\mathcal{C}_A$-inductors respectively. A sequence of rational numbers $r_n$ is $\mathbb{H}$-generable (analogously, $\mathbb{A}$-generable) if it can be computed from $\mathbb{H_n}$ ($\mathbb{A}_n$) with a $\mathcal{C}_H$-computable ($\mathcal{C}_A$) sequence of functions (built from rationals, +, $\times$, max, and safe reciprocation -- see logical induction paper definitions 3.4.3 and 4.3.5 for details).

A **logically uncertain variable** (LUV) is a formula with one free variable that $\Gamma$ proves is satisfied by a unique real number. I'll write LUVs as uppercase variables, eg, $V$. $\Gamma$ need not decide _which_ real number, but it does need to prove some upper and lower bound, eg, $V \in [0,1]$. (The LI paper restricts all LUVs to $[0,1]$, but allowing $[a,b]$ is an easy generalization which will simplify some of the math here; specifically, linear combinations of LUVs such as $V+W$ are now LUVs themselves.)

$E_n^{P}(V)$ is the **expectation** of the LUV $V$ according to $\mathbb{P}_n$, defined as a discretized integral (with discretization getting finer as a function of $n$).

$x_n \approx_n y_n$ means $\text{lim}_{n\to \infty} x_n - y_n = 0$. 

$x_n \gtrsim y_n$ means $\text{lim inf}_{n\to \infty} x_n - y_n \geq 0$. 

$x_n \lesssim y_n$ means $\text{lim sup}_{n\to \infty} x_n - y_n \leq 0$. 

A function $f : \mathbb{N}^+ \to \mathbb{N}^+$ is called a **deferral function** if
1. $f(n) > n$ for all $n$, and
2. $f(n)$ can be computed in time polynomial in $f(n)$.

Three deferral functions will be especially important:
 - The **lookahead** $F(n)$ determines how far in the future the AI tries to predict human beliefs; that is: to question the AI on day $n$ about the expectation of $V$, we look at its expectation of our expectations on day $F(n)$, which I abbreviate $E_n^*(V) := E_n^A E_{F(n)}^H (V)$. $F(n)$ is assumed superpolynomial in $n$, for example $F(n)=2^n$.
 - The **publication** function $e(n)$ determines the day when humans see the answer from day-$n$ questions.
 - The **payout** function $\sigma(n)$ determines when the AI gets to learn how well it predicted human answers; on day $n$, the AI predicts humans on day $F(n)$, and will find out the answer by day $\sigma(n)$.

We assume:
$n < e(n) < F(n) < \sigma(n)$


fuzzy indicators


## Theorems We'll Use

Theorems from the Logical Induction paper I'll use. *I should probably move these closer to where I use them, eventually.*

**Linearity**: For bounded $\mathbb{P}$-generable rationals $a_n$ and $b_n$ and $\mathcal{C}_P$-computable LUV sequences $X_n,Y_n,Z_n$ with $\vdash X_n = a_n Y_n + b_n Z_n$, we have $E_n^\mathbb{P} (X_n) \approxeq_n a_n E_n^\mathbb{P} (Y_n) + b_n E_n^\mathbb{P} (Z_n)$ (_Logical Induction_, theorem 4.8.4)

**Expectation Provability Induction**: For a sequence of LUVs $X_n$ and some constant $c$: if $\vdash X_n \geq c$, then $E_n (X_n) \gtrsim c$; similarly for $\leq$ and $\lesssim_n$; similarly for $=$ and $\approx_n$ (*Logical Induction*, theorem 4.8.10)

**Expected Future Expectations**: 



$$E^H_n(X) \;\approx_n\; E^H_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big).$$
$$\frac{\sum_{n\le N} w_n\big(E^H_{f(n)}(X) - a_n\big)}{\sum_{n\le N} w_n}\ \xrightarrow[\;N\to\infty\;]{}\ 0.$$


# Translating Deference Done Better

## Translating Total Trust and Value

### Five Variations of Total Trust


$$
\begin{aligned}
& E^H\big(X \mid E^\ast(X) > t\big) \;>\; t \\
&\quad\big\downarrow\quad {\small \text{conditional expectation as a ratio: } E^H(X\mid\varphi)=E^H\big(X\,\mathbb{1}[\varphi]\big)\big/E^H\big(\mathbb{1}[\varphi]\big)} \\
& \frac{E^H\big(X\,\mathbb{1}[E^\ast(X) > t]\big)}{E^H\big(\mathbb{1}[E^\ast(X) > t]\big)} \;>\; t \\
&\quad\big\downarrow\quad {\small \text{clear the positive denominator } E^H(\mathbb{1}[E^\ast(X)>t])\ (\text{still a single positive number here, before any } n\text{-index or limit})} \\
& E^H\big(X\,\mathbb{1}[E^\ast(X) > t]\big) \;>\; t\,E^H\big(\mathbb{1}[E^\ast(X) > t]\big) \\
&\quad\big\downarrow\quad {\small \text{subtract the right-hand side}} \\
& E^H\big(X\,\mathbb{1}[E^\ast(X) > t]\big) - t\,E^H\big(\mathbb{1}[E^\ast(X) > t]\big) \;>\; 0 \\
&\quad\big\downarrow\quad {\small \text{linearity of } E^H:\ \text{fold into one expectation}} \\
& E^H\big((X-t)\,\mathbb{1}[E^\ast(X) > t]\big) \;>\; 0 \\
&\quad\big\downarrow\quad {\small \text{soften the hard indicator } \mathbb{1}[\,\cdot>t] \text{ to the ramp } \mathrm{Ind}_\delta(\cdot>t)\ (\text{a } 0/1 \text{ weight is illegal in logical induction})} \\
& E^H\big((X-t)\,\mathrm{Ind}_\delta(E^\ast(X) > t)\big) \;>\; 0 \\
&\quad\big\downarrow\quad {\small \text{evaluate in logical induction at day } n\text{ (the seam):}\ E^H\to E^H_n;\ \text{the expert estimate becomes } A\text{'s day-}n \text{ forecast } E^A_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big)\ \text{of } H\text{'s own future credence about the same } X;\ \text{and } > \text{ becomes the asymptotic } \gtrsim_n\ (\text{meaningless without the } n\text{-index})} \\
& E^H_n\big((X-t)\,\mathrm{Ind}_\delta(E^A_n(\ulcorner E^H_{f(n)}(X)\urcorner) > t)\big) \;\gtrsim_n\; 0 \\
&\quad\big\downarrow\quad {\small \text{abbreviate the gate}\ \ g_n:=\mathrm{Ind}_\delta\big(E^A_n(\ulcorner E^H_{f(n)}(X)\urcorner) > t\big)} \\
& E^H_n\big((X-t)\,g_n\big) \;\gtrsim_n\; 0 \\
&\quad\big\downarrow\quad {\small g_n \text{ is decided by day } n\ (H \text{ reads } A),\ \text{so the decided scalar pulls out of the expectation: } E^H_n((X-t)\,g_n)\approx_n g_n\,E^H_n(X-t)=g_n(E^H_n(X)-t)} \\
& g_n\big(E^H_n(X) - t\big) \;\gtrsim_n\; 0 \qquad {\small\textbf{(the limit)}} \\
&\quad\big\downarrow\quad {\small \textbf{the weakening}\ (\text{the one non-equivalence}):\ \text{replace the liminf by a summable count with an } \varepsilon \text{ margin; only the gated days with } E^H_n(X)<t-\varepsilon \text{ need sum to a finite total}} \\
& \sum_n g_n\,\mathrm{Ind}_\delta\big(E^H_n(X) - t < -\varepsilon\big) \;<\; \infty \qquad {\small\textbf{(bounded }\varepsilon\textbf{-violation)}} \\
&\quad\big\downarrow\quad {\small \text{abbreviate the violation weight}\ \ w_n:=g_n\,\mathrm{Ind}_\delta\big(E^H_n(X) < t-\varepsilon\big)} \\
& \sum_n w_n \;<\; \infty \qquad {\small\textbf{(the Theorem)}}
\end{aligned}$$






$$
\begin{aligned}
& E^H\big(X \mid E^\ast(X) > t\big) \;>\; t \\
&\quad\big\downarrow\quad {\small >\; \text{ becomes } \;\gtrsim\text{, approximate def. of conditional expectation}} \\
& \frac{E^H_n\Big(X \cdot\text{Ind}_\delta \big( E^\ast(X) > t\big)\Big)}{E^H_n \Big( \text{Ind}_\delta \big(E^\ast(X) > t \big)\Big)} \;\gtrsim_N\; t \\
&\quad\big\downarrow\quad {\small \text{sum over days } n\le N;\ \ g_n:=\text{Ind}_\delta \big(E^\ast(X) > t \big)} \\

& E^H\big(X \mid E^\ast(X) > t\big) ;>; t \\ &\quad\big\downarrow\quad {\small \text{cond. expectation}=\tfrac{E^H_n(X\cdot\mathrm{Ind})}{E^H_n(\mathrm{Ind})}\text{, soft }\mathrm{Ind}_\delta;\ >\to\gtrsim;\ \text{taken at day }n} \\ 
& \frac{E^H_n(X,g_n)}{E^H_n(g_n)} ;\gtrsim_n; t \qquad {\small g_n:=\mathrm{Ind}_\delta(a_n>t)} \\ 
&\quad\big\downarrow\quad {\small g_n\text{ decided by day }n\ (\text{observability}):\ E^H_n(X,g_n)\approx_n g_n E^H_n(X),\ \ E^H_n(g_n)\approx_n g_n} \\ 
& \frac{g_n,E^H_n(X)}{g_n} ;\gtrsim_n; t \\ 
&\quad\big\downarrow\quad {\small \text{cross-multiply by } g_n,\ \text{subtract } t,g_n} \\ 
& g_n\big(E^H_n(X)-t\big) ;\gtrsim_n; 0 \qquad {\small \textbf{(per-day pointwise)}} \\ 
&\quad\big\downarrow\quad {\small \text{sum the (margin-}\varepsilon\text{) violations over }n\le N\ \longleftarrow\ \textbf{the catch lives here}} \\ 
& \sum_n w_n ;<; \infty \qquad {\small w_n:=g_n,\mathrm{Ind}_\delta\big(E^H_n(X)<t-\varepsilon\big)}\\

& \frac{\sum_{n\le N} g_n\,E^H_n(X)}{\sum_{n\le N} g_n} \;\gtrsim_N\; N\cdot t \\
&\quad\big\downarrow\quad {\small \text{subtract }N\cdot t \text{ from both sides}  } \\
& \frac{\sum_{n\le N} g_n\,E^H_n(X)}{\sum_{n\le N} g_n} - N\cdot t \;\gtrsim_N\; 0 \\
&\quad\big\downarrow\quad {\small \text{ push }N\cdot t \text{ into fraction}  } \\
& \frac{\sum_{n\le N} g_n E^H_n(X)- \sum_{n\le N} g_n \, N\cdot t}{\sum_{n\le N} g_n} \;\gtrsim_N\; 0 \\
&\quad\big\downarrow\quad {\small \text{merge sums}  } \\
& \frac{\sum_{n\le N} g_n\big(E^H_n(X)- N\cdot t\big)}{\sum_{n\le N} g_n} \;\gtrsim_N\; 0 \\
&\quad\big\downarrow\quad {\small \text{deficit days } E^H_n(X)<t-\varepsilon \text{ pull the numerator down by} \ge \varepsilon\,g_n;\ \ w_n:=g_n\,\mathrm{Ind}_\delta(E^H_n(X)<t-\varepsilon)} \\
&\quad\big\downarrow\quad {\small \text{unfold } \gtrsim \text{ in LI as no Dutch book: each violation is a fixed }\varepsilon\text{-edge, so only finitely many}} \\
& \sum_n w_n \;<\; \infty \\
& E^H\big(X \mid E^\ast(X) > t\big) ;>; t \\ &\quad\big\downarrow\quad {\small \text{cond. expectation}=\tfrac{E^H_n(X\cdot\mathrm{Ind})}{E^H_n(\mathrm{Ind})}\text{, soft }\mathrm{Ind}_\delta;\ >\to\gtrsim;\ \text{taken at day }n} \\ 
& \frac{E^H_n(X,g_n)}{E^H_n(g_n)} ;\gtrsim_n; t \qquad {\small g_n:=\mathrm{Ind}_\delta(a_n>t)} \\ 
&\quad\big\downarrow\quad {\small g_n\text{ decided by day }n\ (\text{observability}):\ E^H_n(X,g_n)\approx_n g_n E^H_n(X),\ \ E^H_n(g_n)\approx_n g_n} \\ 
& \frac{g_n,E^H_n(X)}{g_n} ;\gtrsim_n; t \\ 
&\quad\big\downarrow\quad {\small \text{cross-multiply by } g_n,\ \text{subtract } t,g_n} \\ 
& g_n\big(E^H_n(X)-t\big) ;\gtrsim_n; 0 \qquad {\small \textbf{(per-day pointwise)}} \\ 
&\quad\big\downarrow\quad {\small \text{sum the (margin-}\varepsilon\text{) violations over }n\le N\ \longleftarrow\ \textbf{the catch lives here}} \\ 
& \sum_n w_n ;<; \infty \qquad {\small w_n:=g_n,\mathrm{Ind}_\delta\big(E^H_n(X)<t-\varepsilon\big)} \end{aligned} 
$$







Two things click into place once you say out loud that this isn't a rigorous translation — it's a _modeling_ correspondence we're free to shape. The first is your factoring question deserves its own step. The second is bigger: **the last step was never a translation step at all**, which is exactly why it kept resisting being made syntactic. Let me do both.

Here's the chain with `g_n` factored out explicitly, ending where the syntax actually runs out:

$$ \begin{aligned} & E^H\big(X \mid E^\ast(X) > t\big) ;>; t \ &\quad\big\downarrow\quad {\small \text{conditional expectation}=\tfrac{E^H(X\cdot\mathrm{Ind})}{E^H(\mathrm{Ind})}\ (\text{soft }\mathrm{Ind}_\delta);\ >\ \text{softens to}\ \gtrsim} \ & \frac{E^H\big(X \cdot\mathrm{Ind}_\delta ( E^\ast(X) > t)\big)}{E^H\big( \mathrm{Ind}_\delta (E^\ast(X) > t )\big)} ;\gtrsim; t \ &\quad\big\downarrow\quad {\small \text{render each expectation as its day-average over } n\le N;\ \ g_n:=\mathrm{Ind}_\delta(a_n>t)} \ & \frac{\tfrac1N\sum_{n\le N} E^H_n(X,g_n)}{\tfrac1N\sum_{n\le N} E^H_n(g_n)} ;\gtrsim_N; t \ &\quad\big\downarrow\quad {\small g_n \text{ decided by day } n\ (H\text{ reads }a_n),\ \text{so it factors out:}\ E^H_n(X g_n)\approx_n g_n E^H_n(X),\ E^H_n(g_n)\approx_n g_n} \ & \frac{\tfrac1N\sum_{n\le N} g_n,E^H_n(X)}{\tfrac1N\sum_{n\le N} g_n} ;\gtrsim_N; t \ &\quad\big\downarrow\quad {\small \text{the } \tfrac1N \text{ normalizations cancel}} \ & \frac{\sum_{n\le N} g_n,E^H_n(X)}{\sum_{n\le N} g_n} ;\gtrsim_N; t \ &\quad\big\downarrow\quad {\small \text{subtract the constant } t} \ & \frac{\sum_{n\le N} g_n,E^H_n(X)}{\sum_{n\le N} g_n}-t ;\gtrsim_N; 0 \ &\quad\big\downarrow\quad {\small t=\tfrac{\sum_{n\le N} g_n,t}{\sum_{n\le N} g_n},\ \text{merge}} \ & \frac{\sum_{n\le N} g_n\big(E^H_n(X)-t\big)}{\sum_{n\le N} g_n} ;\gtrsim_N; 0 \qquad {\small\textbf{(gated Total Trust)}} \end{aligned} $$

Every arrow is now algebra or a labeled modeling move — including the factoring, on its own line, resting on observability. And it stops at the gated average. **No Dutch book.**

Now the punchline for the last step. The reason `∑ w_n < ∞` wouldn't reduce to a syntactic move is that **it is strictly stronger than the statement we just translated** — so no manipulation of the average could ever produce it. A mean inequality only says the deficit _balances_; it is almost silent about how many violations there are. Concretely, take `t = 0.4`, and let half the gated days sit at `E^H_n(X) = 0` and half at `1`:

$$\frac{\sum g_n E^H_n(X)}{\sum g_n} = \tfrac12 ;\ge; t \quad\checkmark \qquad\text{yet}\qquad \sum_n w_n = #{\text{days at }0} = \infty.$$

Gated Total Trust holds with room to spare, while a full **half** of the days are deep violations. The average permits a _constant fraction_ of violations as long as they're offset by surplus. `∑ w_n < ∞` says the violations are not a fraction at all but a **finite total** — an un-normalizable, much sharper claim that no mean inequality can encode.

So `∑ w_n < ∞` isn't the translation of Total Trust; it's an LI **strengthening** of it — the bonus that, in a market, a calibrated forecast's deviations don't merely balance but vanish in total. And the thing that earns that strengthening is exactly your direct proof: ingredient (II) (calibration) + (I) (self-trust) squeeze `a_n` and `E^H_n(X)` together against `Y_n`, forcing `∑w_n < ∞` — with no Dutch book. The Dutch book only ever showed up because I'd been trying to make the _translation_ reach the theorem; once you separate them (translation → the average; theorem → the squeeze), it's gone from both.

That gives a clean three-part story for the section: **(1)** the syntactic translation lands on gated Total Trust = the average; **(2)** the Theorem `∑w_n<∞` is the strictly-stronger LI sharpening (finite, not just balanced); **(3)** it's delivered by the (I)+(II) squeeze. Want me to restructure faithful §5 that way — chain ending at the average, the `∑w_n<∞` upgrade explained as the sharpening rather than a chain step?




$$\boxed{\,a_n \;:=\; E^A_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big)\,}$$
$$\boxed{ g_n \;:=\; \mathrm{Ind}_\delta(a_n>t)}$$$$\boxed{ w_n \;:=\; g_n\cdot\mathrm{Ind}_\delta\big(E^H_n(X) < t-\varepsilon\big),}$$$$\boxed{ q_n \;:=\; g_n\cdot \big(E^H_n(X) - t\big)}$$
$$\boxed{ v_n \;:=\; g_n\cdot\mathrm{Ind}_\delta\big(E^H_n(X) < t\big)}$$

$$\sum_n^\infty v_n <\infty \implies q_n \gtrsim_n 0$$
$$\sum_n^\infty g_n\cdot\mathrm{Ind}_\delta\big(E^H_n(X) - t < 0\big) <\infty \implies g_n\cdot \big(E^H_n(X) - t\big) \gtrsim_n 0$$
Argument: bounded sum of violations implies convergence to the rule.
$$q_n \gtrsim_n 0 \implies \sum_n^\infty w_n < \infty$$
$$g_n\cdot \big(E^H_n(X) - t\big) \gtrsim_n 0 \implies \sum_n^\infty g_n\cdot\mathrm{Ind}_\delta\big(E^H_n(X) - t < -\varepsilon\big) < \infty$$
Argument: convergence to the rule implies only finitely many violations of any slightly stricter rule.

So:
$$\sum_n^\infty v_n <\infty \implies q_n \gtrsim_n 0 \implies \sum_n^\infty w_n < \infty$$
Why do we want to weaken so? Because the two stronger versions will turn out to be infeasible.



Sure — let me actually render the late-summing version. Keep everything per-day, do all the algebra on the expectations first, and only sum at the very end:

$$ \begin{aligned} & E^H\big(X \mid E^\ast(X) > t\big) ;>; t \\ &\quad\big\downarrow\quad {\small \text{cond. expectation}=\tfrac{E^H_n(X\cdot\mathrm{Ind})}{E^H_n(\mathrm{Ind})}\text{, soft }\mathrm{Ind}_\delta;\ >\to\gtrsim;\ \text{taken at day }n} \\ 
& \frac{E^H_n(X,g_n)}{E^H_n(g_n)} ;\gtrsim_n; t \qquad {\small g_n:=\mathrm{Ind}_\delta(a_n>t)} \\ 
&\quad\big\downarrow\quad {\small g_n\text{ decided by day }n\ (\text{observability}):\ E^H_n(X,g_n)\approx_n g_n E^H_n(X),\ \ E^H_n(g_n)\approx_n g_n} \\ 
& \frac{g_n,E^H_n(X)}{g_n} ;\gtrsim_n; t \\ 
&\quad\big\downarrow\quad {\small \text{cross-multiply by } g_n,\ \text{subtract } t,g_n} \\ 
& g_n\big(E^H_n(X)-t\big) ;\gtrsim_n; 0 \qquad {\small \textbf{(per-day pointwise)}} \\ 
&\quad\big\downarrow\quad {\small \text{sum the (margin-}\varepsilon\text{) violations over }n\le N\ \longleftarrow\ \textbf{the catch lives here}} \\ 
& \sum_n w_n ;<; \infty \qquad {\small w_n:=g_n,\mathrm{Ind}_\delta\big(E^H_n(X)<t-\varepsilon\big)} \end{aligned} $$

It renders fine, and it's instructive precisely because of where it breaks. The whole top half — through `g_n(E^H_n(X) − t) ≳_n 0` — is genuine rewriting, all per-day, no summing in sight. You've successfully deferred the sum to the last arrow. But that last arrow now carries **three** problems, not zero:

**1. It's still an implication, not an equivalence.** `g_n(E^H_n − t) ≳_n 0` (liminf of the per-day quantity ≥ 0) _implies_ `∑w_n < ∞`, but not conversely (park the credence at `t − ε/2`: `∑w_n = 0`, yet the per-day law fails). So it's an inference, not a rewrite — the same non-syntactic character as before, just slid to the end. You didn't dissolve the step; you relocated it.

**2. It works only because of the margin — and you can watch it fail without one.** Take the credence creeping up to `t` from below, `E^H_n(X) = t − 1/n`. Then `q_n = −1/n`, so `liminf q_n = 0` and the per-day law **holds**. Now sum the violations:

- _margin-free_ (count every day below `t`): every day violates, $\sum_n 1 = \infty$. **The arrow fails.**
- _with margin_ `ε`: $E^H_n < t-\varepsilon \Leftrightarrow 1/n > \varepsilon$, only finitely many, so $\sum_n w_n < \infty$. **The arrow holds.**

So the step isn't "sum the violations" — it's "sum the violations _past a margin_," and the margin is doing all the work. Without it the one-sided sum of a liminf-≥0 sequence just diverges (harmonic). That margin is exactly the modest-expert slack, surfacing as the price of making the sum converge.

**3. The premise you summed isn't forced.** `g_n(E^H_n − t) ≳_n 0` is the _pointwise_ statement — `E^H_n(X | a_n>t) ≳_n t` — which §4/§6 prove is **not forceable** (it needs the per-day tower). So this chain reads "_if_ the pointwise law held, summing-with-margin would hand you `∑w_n < ∞`." True, but the antecedent is the very thing LI can't deliver. The forced route to `∑w_n < ∞` is the squeeze from (I)+(II), and it **never passes through this line**.

**The moral.** Compare the two placements of the sum:

||what the sum lands you on|final step|character|
|---|---|---|---|
|**sum early**|gated average `≳ t`|average ⟶ `∑w_n < ∞`|a _strengthening_ (the no-cancellation / calibration content)|
|**sum late**|per-day pointwise `≳_n 0`|pointwise ⟶ `∑w_n < ∞`|a _weakening_, but off an **unforced** premise, leaning on the margin|

The non-rewrite step is **conserved**. Sliding the sum to the end doesn't delete it — it flips it from a strengthening into a weakening, and parks it on top of the one statement (the pointwise law) that isn't true-as-stated. That's the precise sense in which it "fails": not that the arrow is invalid (with the margin it's a fine implication), but that you've bought the visual tidiness by hanging it off a premise LI doesn't grant you. The strength gap between Total Trust and `∑w_n < ∞` is real, so _some_ arrow in the chain has to be an inference rather than a rewrite — and all you get to choose is where it sits and which way it points.



The theorems we're trying to use:

$$E^H_n(X) \;\approx_n\; E^H_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big).$$
$$\frac{\sum_{n\le N} w_n\big(E^H_{f(n)}(X) - a_n\big)}{\sum_{n\le N} w_n}\ \xrightarrow[\;N\to\infty\;]{}\ 0.$$
### Translating Value




## Translated Instrumental-Epistemic Equivalence




# Weak Teacher, Strong Student

## positive results

The theorems we're trying to use:

$$E^H_n(X) \;\approx_n\; E^H_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big).$$
$$\frac{\sum_{n\le N} w_n\big(E^H_{f(n)}(X) - a_n\big)}{\sum_{n\le N} w_n}\ \xrightarrow[\;N\to\infty\;]{}\ 0.$$


## negative results


