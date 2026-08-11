# Simplifying the schedule condition with efficient computability

- **Date (last updated):** 2026-06-10
- **Created:** 2026-06-09
- **Messages:** 26
- **Conversation ID:** `77d293e5-49e2-46cc-ab42-2f3f74e67eb7`
- **Link:** https://claude.ai/chat/77d293e5-49e2-46cc-ab42-2f3f74e67eb7

---
## Human
*2026-06-09 00:42 UTC*

<details>
<summary>📎 Attachment: pasted content (14557 bytes)</summary>

```
\documentclass{article}
\usepackage{graphicx} % Required for inserting images
\usepackage{url}
\usepackage{hyperref}
\usepackage{titlesec}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{enumitem}
\usepackage{amsmath}
\usepackage{amsthm}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\DeclareMathOperator*{\argmin}{arg\,min}



\titleformat*{\section}{\LARGE\bfseries}
\titleformat*{\subsection}{\Large\bfseries}
\titleformat*{\subsubsection}{\large\bfseries}
\titleformat*{\paragraph}{\large\bfseries}
\titleformat*{\subparagraph}{\small\bfseries}

\title{Trust Between Universal Inductors}
\date{}
\begin{document}
\maketitle
\begin{sloppypar}

\subsection*{Motivation}

% Let $H$ be a \emph{universal inductor}, in the sense of a \href{https://arxiv.org/abs/1609.03543}{logical inductor} conditioned on bitstrings.\footnote{The basic construction is given in
% \href{https://www.lesswrong.com/posts/FnH2G832sWMySptp5}{this explanation of universal inductors} by Diffractor.} $H$ should be thought of as a bounded reasoner that represents evolving human opinions over time, constructed by conditioning on bitstring representations of empirical observations and proven theorems. Then, suppose another universal inductor $A$ is constructed as a strictly more computationally powerful reasoner that is set up to predict the future states of the human reasoner using good feedback about what those future states turn out to be. We then construct a new inductor $H^+$ by conditioning $H$ further on bitstrings representing outputs of $A$. This may be thought of as an attempt to leverage an AI's additional computational power to gain information about humanity's own trusted future beliefs. The following construction makes this setup concrete. [Summary of findings after finishing]


\subsection*{Construction}

\paragraph{Base reasoner.}
Take a propositional language $\mathcal{L}$ with sentence set $\mathcal{S}$ along with a
theory $\Gamma$ and a $\Gamma$-complete computable deductive process
$D_H=(D_H^t)_{t\ge1}$. Let $\mathcal{C}_H$ be a complexity class closed under
polynomial overhead \footnote{explanation of polynomial overhead} and let $H=(H_1,H_2,\ldots)$ be a \emph{universal inductor} over $D_H$ against $\mathcal{C}_H$. In other words, take a logical inductor $U$ over the empty deductive process with traders in $\mathcal{C}_H$, and then use Bayesian conditioning to define $H = U \mid D_H$. See \href{https://www.lesswrong.com/posts/FnH2G832sWMySptp5}{this explanation} by Diffractor for reference on the fundamental details of the universal inductor construction. $H$ is a market satisfying the logical induction
criterion against traders in $\mathcal{C}_H$. Each stage $H_t$ is a full probability measure over the worlds of $\mathcal{L}$, concentrated on the worlds propositionally consistent with $D_H^t$. Existence of such a
measure-valued inductor over an arbitrary computable deductive process is Lemma~\ref{lem:existence}.

\paragraph{Propositions and deferral.}
Choose a strictly increasing, $\mathcal{C}_H$-computable ``deferral" function
$F:\mathbb{N}^+\to\mathbb{N}^+$ with $F(n)>n+1$. Consider an effective enumeration
$P^{(0)},P^{(1)},\ldots$ of $\mathcal{S}$ where $P^{(n)}$ to be some $n$-th proposition of interest.

\paragraph{Threshold symbols.}
For each $n\ge1$ and $1\le k\le n$ introduce two fresh propositional symbols:
\begin{itemize}
  \item $\alpha_{n,k}$ which can be read as ``the contract for $P^{(n)}$ deferred to $F(n)$ has value at least $k/n$"
  \item $\beta_{n,k}$ which can be read as ``$A$'s published quote for that contract is at least $k/n$."
\end{itemize}
 Let $\mathcal{L}^\alpha:=\mathcal{L}\cup\{\alpha_{n,k}\}$ and
$\mathcal{L}^\beta:=\mathcal{L}\cup\{\beta_{n,k}\}$, with sentence sets
$\mathcal{S}^\alpha$ and $\mathcal{S}^\beta$ respectively, each extending $\mathcal{S}$. The $\alpha$ symbols allow $A$ to price
the future credences of $H^+$ while the $\beta$ symbols
encode $A$'s outputs for $H^+$ to condition on. Because each of these sets of symbols represents threshold sentences, that is claims that a value is at least $\frac{k}{n}$, they respect monotonicity axioms:
\[
\{\alpha_{n,k}\to\alpha_{n,k-1}\}\quad\text{and}\quad
\{\beta_{n,k}\to\beta_{n,k-1}\}\qquad(n\ge1,\ 2\le k\le n).
\]
Note that the readings of the symbols given above are glosses for our metalanguage, and are only baked into the inductors in the form of the monotonicity axioms. For a world $W$ consistent with these axioms each truth-set is an initial
segment, so we can define values as proportions of true threshold sentences:
\[
\mathrm{val}^\alpha_W(n):=\tfrac1n\#\{k:W(\alpha_{n,k})=1\},
\qquad
\mathrm{val}^\beta_W(n):=\tfrac1n\#\{k:W(\beta_{n,k})=1\}
\]
each taking the form $m/n$ for an integer $0\le m\le n$. Using these values, the addition of the threshold symbols to the language allows for the representation of a real-valued unknown rounded to the nearest $\frac{1}{n}$.

\paragraph{Contracts and quotes.}
Define the deferred contract $C_n$ and the quote readout $Q_n$ as affine combinations
\[
C_n:=\tfrac1n\sum_{k=1}^n\alpha_{n,k},
\qquad
Q_n:=\tfrac1n\sum_{k=1}^n\beta_{n,k},
\]
so $W(C_n)=\mathrm{val}^\alpha_W(n)$ and $W(Q_n)=\mathrm{val}^\beta_W(n)$
for consistent worlds $W$. Note that both $C_n$ and $Q_n$ are affine combinations of symbols
already in the markets used for convenience rather than separately traded objects. Write
\[
a_n:=A_n(C_n)=\tfrac1n\sum_k A_n(\alpha_{n,k})\in\mathbb{Q}\cap[0,1]
\]
for $A$'s published quote on the deferred contract and
\[
Y_n:=H^+_{F(n)}(P^{(n)})
\]
for the eventual credence of $H^+$ that the contract uses for settlement. 

\paragraph{A more powerful reasoner.}
Let $\mathcal{C}_A\supseteq\mathcal{C}_H$ be a complexity class closed under
polynomial overhead for which the map $n\mapsto Y_n$ is $\mathcal{C}_A$-computable
in the coupled system. More precisely, given $n$, an implementation in $\mathcal{C}_A$ can simulate the mutual construction up to stage $F(n)$ and output $Y_n$. Writing $R(t)$ for the per-stage runtime of the
implementation of $H^+$, we assume $\mathcal{C}_A$ contains $n\mapsto R(F(n))$. This is a significant idealizing assumption about the computational power of $A$ needed so that its deferred bets can eventually deductively resolve, but note that the simulation need not be practically implementable by the traders.

\paragraph{Timing.}
We now fix two $\mathcal{C}_A$-computable, strictly increasing schedules: a \emph{settlement} schedule $\sigma$ and an \emph{emission} schedule $e$, related by
\[
e(n)<F(n)<\sigma(n).
\]
Here $\sigma(n)$ is the stage by which $Y_n$ has been computed and the market for $C_n$ resolves, while $e(n)$ is the stage by which $A$'s quote $a_n$ on contract $n$ has been computed and published. 

[REPLACE AND CLARIFY THIS PARAGRAPH] We require $e$ to dominate the cost of producing each quote, so that the set of profiles published by any stage $t$ is computable within $\mathcal{C}_H$'s budget as a function of $t$; this is what lets $H^+$ condition on the published quotes (below). The gap between $\mathcal{C}_A$ and $\mathcal{C}_H$ is absorbed entirely into the growth of $e$: a quote that exercises the full power of $\mathcal{C}_A$ is published only at a correspondingly late stage $e(n)$, yet the published stream stays efficiently readable at every stage, since $H^+$ never has to predict a quote, only to recompute already-published ones. For instance one may take $\mathcal{C}_H=\mathrm{P}$, $\mathcal{C}_A=\mathrm{EXP}$, and $e,F,\sigma$ all exponential with $e(n)<F(n)<\sigma(n)$.

\paragraph{The inductor $A$.}
Let's now define $A$ and $H^+$ as two inductors that can see each other, constructed via recursion. For $0\le m\le n$ write the settling profile 
\[
\mathcal{A}_n(m):=\{\alpha_{n,k}:k\le m\}\cup\{\neg\alpha_{n,k}:k>m\}
\]
which should be read as ``$C_n$ is approximately equal to $\frac{m}{n}$.'' Let
\[
m_n^*:=\argmin_{0\le m\le n}\left|\tfrac mn-Y_n\right|
\]
with ties going to the lower $m$, i.e. the best approximation of the real-valued settlement $Y_n$. We therefore have
\[
\left|\tfrac{m_n^*}{n}-Y_n\right|\le\tfrac1{2n}
\]
because the grid $\{0,\frac1n,\frac2n,\ldots,1\}$ has spacing $\frac1n$, so every value in $[0,1]$ is within $\frac1{2n}$ of some grid point. Define the computable deductive process
$D_A$ over $\mathcal{L}^\alpha$ as one that, for each time step $t$, $D_A^t$ includes the $\alpha$-monotonicity axioms for $n\le t$ and the profile $\mathcal{A}_n(m_n^*)$ for each $n$ with $\sigma(n)\le t$.
Each $D_A^t$ is finite (axiom schemata and settlement profiles are finite at any finite stage) and consistent (distinct $n$ touch disjoint symbols for both axioms and profiles, settlements are initial segments respecting monotonicity). $D_A$ is
computable as part of the mutual construction, since $\sigma(n)>F(n)$ makes $Y_n$ available
before its settlement is required by $D_A$. Let $A=(A_1,A_2,\ldots)$ be a universal
inductor over $D_A$ against $\mathcal{C}_A$.

\paragraph{The inductor $H^+$.}
Similarly, define the quote profile
\[
\mathcal{B}_n(\ell):=\{\beta_{n,k}:k\le\ell\}\cup\{\neg\beta_{n,k}:k>\ell\}
\]
as a set of atoms representing a posted quote and let
\[
\ell_n^*:=\argmin_{0\le\ell\le n}\left|\tfrac\ell n-a_n\right|
\]
with ties going to the lower $\ell$. Then $\mathcal{B}_n(\ell_n^*)$ is the rounding of $A$'s quote to a grid with spacing $\frac{1}{n}$. Take the base inductor $H$ to be defined over the extended language $\mathcal{L}^\beta$, with the $\beta$-monotonicity axioms adjoined to $\Gamma$, so that it assigns credences to $A$'s quote atoms. Writing
\[
Q_A^{(t)}:=\bigwedge_{i\,:\,e(i)<t}\mathcal{B}_i(\ell_i^*)
\]
for the conjunction of those quote profiles \emph{published by time $t$}, define the augmented human inductor by conditioning,
\[
H^+:=H\mid Q_A,\qquad H^+_t(\cdot):=H_t\!\left(\,\cdot\mid Q_A^{(t)}\right).
\]

[REPLACE THIS PARAGRAPH] The sequence $t\mapsto Q_A^{(t)}$ is an efficiently computable deductive process: only the finitely many profiles with $e(i)<t$ appear by stage $t$, and because $e$ dominates each quote's production cost, all of them can be recomputed within $\mathcal{C}_H$'s budget as a function of $t$. By closure under conditioning (Garrabrant et al., Theorem 4.7.2), applied to this efficiently computable conditioning sequence, $H^+$ is again a universal inductor against traders in $\mathcal{C}_H$, now over $\Gamma$ together with the published quote profiles.

\subsection*{Results}
\paragraph{Existence and well-foundedness.}
The four sequences $(A_t),(H^+_t),(D_A^t),(Q_A^{(t)})$ are defined by one
recursion on $t$, and the schedule $e(n)<F(n)<\sigma(n)$ is exactly what makes the
dependencies strictly decreasing. $D_A^t$ depends on $H^+$ through values $H^+_{F(i)}$ for $i$ with $\sigma(i)\le t$, hence through stages $F(i)<\sigma(i)\le t$. The conditioning event $Q_A^{(t)}$ depends on $A$ only through quotes $a_i$ with $e(i)<t$, each of which is in turn determined by settlements that have already resolved, hence by stages strictly below $e(i)<t$. Neither market's stage-$t$ pricing
references the other's stage-$t$ pricing, so every stage-$t$ object is determined
by data from stages strictly below $t$. Lemma~\ref{lem:existence} carries out the recursion and
verifies the two markets satisfy their logical induction criteria.

\begin{lemma}[Existence]\label{lem:existence} Assume the computational idealization in the construction: the map
\[
n\mapsto Y_n:=H^+_{F(n)}(P^{(n)})
\]
is $\mathcal{C}_A$-computable in the mutually defined system, and
$e(n)<F(n)<\sigma(n)$ are $\mathcal{C}_A$-computable schedules by which $A$'s quote
on contract $n$ is published and $Y_n$ is computed, with $e$ dominating each
quote's production cost. Then the recursive construction of
\[
(A_t),\quad (H^+_t),\quad (D_A^t),\quad (Q_A^{(t)})
\]
is well-founded. Moreover, each $D_A^t$ is finite and
propositionally consistent, the conditioning sequence $t\mapsto Q_A^{(t)}$ is
efficiently computable and each $Q_A^{(t)}$ is consistent with $\Gamma$,
$A$ is a logical inductor over $D_A$ against
$\mathcal{C}_A$, and $H^+=H\mid Q_A$ is a logical inductor against
$\mathcal{C}_H$ by closure under conditioning (Garrabrant et al., Theorem 4.7.2)
applied to this efficiently computable sequence.
\end{lemma}
\paragraph{Limit calibration of $A$ to future $H^+$.} Placeholder intro
\begin{theorem}[Calibration] In the coupled system above,\[
a_n-Y_n\to 0.
\]
Equivalently,
\[
A_n(C_n)-H^+_{F(n)}(P^{(n)})\to 0.
\] 
\end{theorem}
\paragraph{Reflection principles for $H^+$ about $A$.} 
For a rational tolerance $\delta>0$ and a real-valued expression $X\in[0,1]$, define the one-sided continuous indicator
\[
\operatorname{Ind}_{\delta}(X>p) :=
\begin{cases}
0 & X\le p,\\[2pt]
\dfrac{X-p}{\delta} & p<X<p+\delta,\\[4pt]
1 & X\ge p+\delta.
\end{cases}
\]
Define $\operatorname{Ind}_{\delta}(X<p)$ analogously, i.e. with value 0 for $X$ at least $p$, value 1 for $X$ more than $\delta$ less than $p$, and linearly interpolated between 0 and 1 for $X$ at most $\delta$ less than $p$.

Recall that the quote readout (i.e. the price for the contract $C_n$ rounded to the $\frac{1}{n}$ grid) is defined as \[Q_n:=\frac1n\sum_{k=1}^n\beta_{n,k}\]

We use the standard extension of logical induction from sentence-prices to expectations of bounded finite logically uncertain variables (LUVs).\footnote{Definition 4.8.1 of Garrabrant et al.} In particular, any bounded rational-valued function of finitely many sentences can be expanded as a finite affine combination of conjunctions over their truth profiles, priced by linearity. The variables appearing below, such as $1(P^{(n)})\cdot \operatorname{Ind}_{\delta}(Q_n>p_n)$, depend only on the finite family of atoms $\{\beta_{n,k}:1\le k\le n\}$ together with the sentence $P^{(n)}$, and so are legitimate bounded finite LUVs.

\begin{theorem}[Transferred reflection]\label{thm:external-trust}
Let $(p_n)$ be a $\mathcal{C}_H$-computable sequence of rational probabilities in
$[0,1]$, and let $\delta>0$ be rational. Write $1(P^{(n)})$ for the $[0,1]$-LUV representing the truth value of $P^{(n)}$. Then
\[
H^+_n\!\left(
1(P^{(n)})\cdot \operatorname{Ind}_{\delta}(Q_n>p_n)
\right)
\gtrsim_n
p_n\,
H^+_n\!\left(
\operatorname{Ind}_{\delta}(Q_n>p_n)
\right).
\]
Similarly,
\[
H^+_n\!\left(
1(P^{(n)})\cdot \operatorname{Ind}_{\delta}(Q_n<p_n)
\right)
\lesssim_n
p_n\,
H^+_n\!\left(
\operatorname{Ind}_{\delta}(Q_n<p_n)
\right).
\]
\end{theorem}

% Nonconservativity / pull section to follow.

\end{sloppypar}
\end{document}
```

</details>

Right — the κ-with-budgets thing was overbuilt. The simplest move is to stop comparing a cost to a stage at all. State the hypothesis 4.7.2 actually consumes, directly, and let the one schedule `e` carry the load.
Two clauses, that's it:

* Ordering (all stages): `e(n) < F(n) < σ(n)` — published, read, settled. No cost term in sight.
* Efficiency (a property of `e`, not an inequality): `e` grows fast enough that the published stream `t ↦ Q_A^(t)` is efficiently computable in `t`. This is verbatim the hypothesis Closure Under Conditioning wants, so you're stating exactly what you'll use and nothing more.
Intuition in one line: the quotes are expensive to compute, so each is published on a lag; make the lag long enough that by any stage `t` only already-computed quotes have appeared — then reading the stream is cheap even though producing a quote isn't.
Why that's the whole condition: "the stream is e.c." is satisfiable for free, since you can always slow publication to match production. So you state it as a requirement on `e`, add one sentence that it's achievable (publish `a_n` only once its computation has finished; for P/EXP that forces `e` exponential), and push `S`, `T_A`, `κ`, `R(F(n))` into a footnote for any referee who wants the quantitative witness. None of those belong in the main statement.
The unifying idea survives intact and gets simpler: a single schedule `e` absorbs the entire C_A/C_H gap by being slow enough, and the only thing you assert about it is that it makes the conditioning stream efficiently computable. `e < F < σ` plus "`e` is chosen so the conditioning stream is e.c." — done.

Ok so make a natural language (i.e. not latex and not explicitly trying to write the paper) suggestion for what to change to move to the right assumptions for timing and computability


## Assistant
*2026-06-09 00:45 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson is asking for natural language suggestions on how to revise the assumptions around timing and computability in his "Trust Between Universal Inductors" paper, specifically addressing two paragraphs marked for replacement in the construction section.

His core insight is to simplify the framework: drop the "κ-with-budgets" approach and replace it with two clean clauses. The first establishes ordering across all stages—published before read before settled—without any cost term. The second reframes efficiency not as a cost-to-stage inequality but as a property of the emission function itself: that `e` grows fast enough to make the published stream efficiently computable as a function of time, which directly aligns with what Closure Under Conditioning requires. This way he's stating exactly what he needs and nothing more. I notice the memory context shifted — the bluntness instruction was removed, so I should dial back the adversarial tone while still maintaining explicit confidence levels on technical claims. Now I need to actually evaluate whether his proposal works: the setup involves $H^+$ and some construction with $H$, so I should check if the timing and computability argument holds up under scrutiny.

The crux is whether the conditioning sequence $Q_A^{(t)}$ qualifies as efficiently computable for Garrabrant et al.'s closure theorem to apply. I'm uncertain about the exact conditions in 4.7.2 — my recollection of the precise requirements around probability bounds and well-definedness of conditioning in logical inductors isn't reliable enough to confidently verify this without checking the source. So his insight is that the assumption should be cleanly separated from the justification: what you actually *need* is that the stream is efficiently computable, and the witness to that (publishing on a long lag) is separate scaffolding. That's good mathematical exposition. But I'm catching myself on a detail — when he says the published stream $t \mapsto Q_A^{(t)}$ is efficiently computable, is that precisely the right object for what 4.7.2 requires, or do I need to think more carefully about what the conditioning sequence actually is in this context? There's an important distinction between the deductive process being efficiently computable and the conditioning actually being well-defined — the first requires the sequence of sentences to be e.c., but the second requires $H_t(Q_A^{(t)}) > 0$ so the conditional credences don't blow up. The lemma handles consistency separately by asserting each $Q_A^{(t)}$ is consistent with $\Gamma$, which should prevent the worlds from being ruled out, but I need to verify whether consistency alone is sufficient for well-definedness. ght be incomplete. Let me think through this more carefully. The conditioning is on $Q_A^{(t)}$, which consists of settled atom profiles describing $A$'s actual quotes. These should be consistent with $\Gamma$ since the profiles respect monotonicity and $\Gamma$ only constrains them through monotonicity axioms. The real question is whether $H$ assigns positive probability to the true profile — a logical inductor doesn't necessarily assign positive probability to all consistent states, though at finite stages its prices on finite consistent boolean combinations might have some guarantees I'm not immediately recalling.

Rather than assert something I'm uncertain about, I should flag the well-definedness of conditioning as the key thing to verify. My confidence on the exact behavior of finite-stage logical inductor prices is low, so this is worth separating from the structural reorganization. But stepping back, his actual question is just asking for a natural language suggestion about what assumptions to change for timing and computability, so maybe this technical detail isn't the main point.

What matters more is giving him a clean editorial recommendation: confirm the structural move works, specify exactly what the two paragraphs should contain versus what goes to a footnote, and flag that the "two clauses" might be hiding a load-bearing assumption about well-definedness and positivity that he should check against section 4.7.2 before review. On the broader point about slowing publication to make the stream eventually consistent—there's a subtlety I'm noticing. Yes, slowing publication can make it e.c. as a function of time, but you also need the three schedules (F, σ, and e) to all be simultaneously satisfiable with the e.c. property while ensuring Y_n gets computed, and since he has total freedom in how fast these grow, there's room to work with. Actually, I need to reconsider whether recomputing from scratch is even necessary — the quotes could just be stored and read back, but the math works either way. If $H^+$ does recompute each $a_i$ from scratch at stage $t$, then for the largest published index $i$ (where $e(i) < t$), we have $i \approx \log t$, so the recomputation takes $\exp(i) \approx t$ steps, which is polynomial in the stage budget. The efficiency constraint is satisfied without needing to assume the quotes are cached, which is a nice robustness property of the construction.

Now I should map out how the two bracketed sections divide the work: the Timing paragraph introduces the three schedules with their ordering and operational meanings, states that $e$ is chosen to make the conditioning stream efficiently computable, and notes this is achievable by lagging publication behind production; the $H^+$ paragraph then simply invokes the existing result on efficiently computable conditioning sequences without re-deriving the cost accounting.

There's also a consistency issue to flag—the Existence lemma still frames things in terms of "$e$ dominating each quote's production cost," which is the old framing he wants to drop, so the lemma hypothesis needs to shift to "$e$ chosen so that the conditioning sequence is efficiently computable" to match the cleaned-up Timing paragraph.

Now looking at the "More powerful reasoner" paragraph—it assumes $\mathcal{C}_A$ contains $n \mapsto R(F(n))$, which is about $A$ being able to simulate $H^+$ to compute the settlement values $Y_n$. That's a separate requirement from the conditioning efficiency story, so it should stay, even though it was listed as something to push into a footnote. The $R(F(n))$ there is load-bearing for $D_A$ computability and plays a genuine role distinct from the conditioning narrative. I should flag that the two clauses he's identified are spot-on for the timing and computability axis, but I want to double-check whether 4.7.2's other requirements—specifically the well-definedness and consistency of the conditioning, which the Existence lemma already handles—are truly all that's needed beyond the emission condition, or if there's an additional constraint about the conditioned events staying bounded away from probability zero.

Actually, reconsidering this: the universal inductor framework is built on conditioning a logical inductor on a deductive process, and the whole appeal of UIs is that conditioning one on additional sentences yields another UI. If positivity were required, the framework would be more brittle than advertised. For deductive process conditioning specifically—where you're conditioning on sentences that become known and true within the process—the result should be robust without needing a positivity side-condition, since you're not conditioning on an arbitrary low-probability event but on facts that are actually settling as true.

But there's a key distinction: are the quote profiles being added to $H$'s deductive process $D_H$, or are they external information that $H$ conditions on? If the profiles aren't proven by $D_H$ itself—if $H$ never learns $A$'s quotes through its own deduction—then conditioning on them is genuine probabilistic conditioning, and positivity could become relevant. That seems to be the intended reading: $A$'s quotes are external to $H$'s deductive process, so $H^+$ incorporates them through real conditioning, which means positivity might actually matter here.

</details>

Your reorganization is right, and the reason it's right is worth saying out loud: the current draft states a *witness* (a cost-vs-stage inequality, the κ/budget bookkeeping) in a slot that should hold an *assumption*. The thing 4.7.2 actually consumes is a property of the conditioning stream — so name that property and stop. Everything else was you proving the property is achievable, which is justification, not hypothesis.

Here's how I'd have the two bracketed paragraphs divide labor.

**Timing paragraph.** Assert exactly two things. First, the ordering, for all $n$: $e(n) < F(n) < \sigma(n)$, with the one-line gloss — by $e(n)$ the quote is published, by $F(n)$ it's read into settlement, by $\sigma(n)$ the contract resolves. No cost term appears; it's purely an ordering of stages. Second, the efficiency clause, phrased as a property of $e$ and not as an inequality: $e$ is chosen so that the published stream $t \mapsto Q_A^{(t)}$ is efficiently computable in $t$. Then one sentence that this is free — publication can always lag behind production, and for the P/EXP instance that lag is exponential. The quantitative witnesses ($S$, $T_A$, κ, the per-stage runtime) go to a footnote for a referee who wants the bound realized. None belong in the statement.

**$H^+$ paragraph.** This shrinks to almost nothing. You stop re-deriving why the stream is cheap; you cite the Timing assumption that it's e.c., note the profiles are consistent with $\Gamma$, invoke closure under conditioning. The "only finitely many profiles by stage $t$, all recomputable within budget" derivation *was* the witness — it moves into the footnote you just created.

The intuition survives unchanged: quotes are expensive, so each is published on a lag; make the lag long enough that by any stage $t$ only already-finished quotes have surfaced, so reading the stream is cheap even though producing one isn't.

Three things downstream so the paper stays consistent:

1. **The Existence lemma still has the old framing.** Its hypothesis reads "$e$ dominating each quote's production cost." If the body drops the cost comparison, the lemma has to match — its clause on $e$ should become the same "chosen so the conditioning sequence is efficiently computable" wording. Otherwise you've stated the same assumption two incompatible ways and a referee will ask which is load-bearing. (Certain.)

2. **Don't over-prune $R(F(n))$.** It wears two hats. In the *More powerful reasoner* paragraph it does real work: it's why $A$ can simulate $H^+$ up to $F(n)$, hence why $Y_n$ is $\mathcal{C}_A$-computable at all, which the lemma also leans on. That stays in the main text. Only the runtime bookkeeping on the *conditioning/emission* side goes to the footnote. You listed $R(F(n))$ among the things to bury — make sure it's the right occurrence. (Certain.)

3. **The one I'd verify at the source before committing to "that's the whole condition."** Your two clauses are exactly right for the timing/computability axis. The open question is whether e.c. of the stream is genuinely *all* 4.7.2 wants beyond consistency. The specific worry: $Q_A^{(t)}$ is a conjunction that grows without bound in $t$, so $H_t(Q_A^{(t)})$ could tend to 0, and if 4.7.2 is stated for conditioning events bounded away from zero rather than for growing-deductive-process conditioning, e.c. won't supply that and you'd have a third clause, not a footnote. My honest read is it probably doesn't bite — UI-style conditioning on an efficiently computable deductive process is built precisely to absorb the growing-conjunction case, and your lemma's consistency-with-$\Gamma$ assertion is likely the operative side-condition. Call it ~35% that it needs anything. But I won't assert the exact hypotheses of 4.7.2 from memory, and this is the spot to pull the actual theorem and confirm it's the deductive-process flavor with e.c. + consistency as the full hypothesis set.

The first two are bookkeeping you can just do. The third is the only thing standing between your draft and a clean "$e < F < \sigma$ plus $e$ makes the stream e.c. — done."


## Human
*2026-06-09 01:03 UTC*

I want to be slightly more precise than this Define two new scheduling functions: a ``settlement" function $\sigma(n)$ representing the stage at which $Y_n$ is computed by $A$, causing the markets for $C_n$ to resolve and an ``emission" function $e(n)$ representing the stage by which $A$'s quote $a_n$ has been computed and published

especially for $e(n)$. computed by what?


## Assistant
*2026-06-09 01:06 UTC*

<details>
<summary>💭 Thinking</summary>

 The user is pushing back on the definition of the scheduling function $e(n)$ — specifically, they want clarity on who or what actually computes the quote $a_n$. The current phrasing about "the stage by which $A$'s quote has been computed and published" leaves it unclear whether $A$ itself is doing the computing or if something else is involved in the process.

So the answer is that $a_n = A_n(C_n)$ is computed by running the inductor $A$ up to stage $n$ and reading off its price for contract $C_n$. The cost of computing this quote is essentially the cost of running $A$'s market mechanism through stage $n$, which involves $A$'s deductive process and trader aggregation. But there's a subtlety here about what exactly the computational cost entails — whether it's just the per-stage pricing computation or if it includes the full deductive overhead that $A$ depends on. The mutual recursion between $A$ and $H^+$ is well-founded by the timing constraints. The key distinction the user wants is between the *cost of computing* $a_n$ — which happens within the coupled construction $\mathcal{C}_A$ when we run the inductor to stage $n$ — and the *publication* of that value, where the rounded profile $\mathcal{B}_n(\ell_n^*)$ becomes available to $H^+$'s conditioning stream at stage $e(n)$.

But looking at the user's candidate sentence more carefully, I notice they wrote "$Y_n$ is computed by $A$" for $\sigma(n)$, yet $Y_n = H^+_{F(n)}(P^{(n)})$ is actually a value of $H^+$, not $A$. So the imprecision runs deeper — the settlement function should clarify that $Y_n$ is a property of $H^+$, but its *settlement* (the stage where markets resolve) is what $A$ triggers. For $e(n)$, computing $a_n = A_n(C_n)$ is genuinely $A$'s own calculation, but it requires $A$ to have its deductive process $D_A^n$, which in turn depends on settlements $Y_i$ for all earlier contracts where $\sigma(i) \le n$. Each of those settlements requires simulating $H^+$ to stage $F(i)$, so the cost of computing $a_n$ bundles in all those prior $H^+$ simulations. The question is whether those settlements were already computed by the time the construction reaches stage $n$ — and in the well-founded recursion, they would have been.

So the marginal cost of computing $a_n$ at stage $n$ is just running $A$'s pricing one more step, but the total cost from scratch includes all the nested $H^+$ simulations. The precise answer is that $a_n$ is computed by running the inductor $A$ to stage $n$ within the coupled construction — it's a $\mathcal{C}_A$ computation that requires evaluating $A$'s market up to stage $n$, which depends on the relevant portions of $D_A^n$ and their $H^+$ simulations.

Rather than saying "$a_n$ has been computed and published" passively, I should say something like "the stage by which $A$'s stage-$n$ price $a_n = A_n(C_n)$ has been evaluated (a $\mathcal{C}_A$ computation requiring the coupled market $A$ — including the $H^+$-simulations feeding $D_A^n$ — to stage $n$) and its rounding posted to the conditioning stream."

But the user wants precision without a treatise, so I need a tight reformulation that explains the subtlety. Looking at the parallel between $\sigma$ and $e$: both are $\mathcal{C}_A$ computations within the coupled construction. For $\sigma(n)$, the object is an $H^+$ value obtained by simulating to stage $F(n)$. For $e(n)$, the object is an $A$ value obtained by running $A$ to stage $n$.

To compute $a_n = A_n(C_n)$, I need to construct $D_A^n$ (which requires settlements from the relevant $H^+$ simulations), run the logical-inductor algorithm over $n$ stages, then read off the price — all within $\mathcal{C}_A$. So the answer is: $a_n$ is computed by evaluating the inductor $A$ at stage $n$, which is a $\mathcal{C}_A$ computation because it folds in simulating $H^+$ to the relevant stages to build $D_A^n$.

There's an important subtlety here though: I need to flag a potential confusion between two different "computed" notions for $e(n)$. ow, so $e(n)$ needs to be large enough to actually run $A$ to stage $n$, which is a $\mathcal{C}_A$-scale computation (potentially exponential). This means $e(n)$ must be much larger than $n$ itself, and since we need $e(n) < F(n) < \sigma(n)$, all three schedules end up being exponentially large for the P/EXP case. The key distinction is between when $a_n$ is *defined* at $A$'s stage $n$ versus when it's actually *computed and published* into the stream at stage $e(n)$.

For $Y_n$, I need to be precise about what "computed by $A$" means. Technically $Y_n$ is $H^+$'s credence value, but in the construction $A$ simulates $H^+$ out to stage $F(n)$ to obtain it, so it's computed at $A$'s power level. The user's phrasing is a bit loose here—more accurately, $Y_n$ is computed *by the simulation that $A$ runs*, not directly by $A$ itself.

When $Y_n$ gets computed and fed into $A$'s deductive process $D_A$, the settlement profile $\mathcal{A}_n(m_n^*)$ is added, which causes the market atoms $\alpha_{n,k}$ in $A$'s language to resolve at stage $\sigma(n)$. So the causality is right: computing $Y_n$ triggers the market resolution. For clarity, I should say $\sigma(n)$ is the stage by which $A$ has computed $Y_n$ through its $H^+$ simulation.

For $e(n)$, the quote $a_n = A_n(C_n)$ is literally $A$'s stage-$n$ price on contract $C_n$, computed by running $A$ to stage $n$. The reason $e(n)$ is so much larger than $n$ is that running $A$ to stage $n$ itself requires $\mathcal{C}_A$ computation, which includes all the nested $H^+$ simulations that build up $D_A^n$. Now I need to check whether there's a circularity issue here.

To compute $a_n$, I run $A$ to stage $n$, which depends on $D_A^n$. That database contains settlements for all $\sigma(i) \le n$. Since $\sigma(i) > F(i) > i$, these settlements are for indices somewhat less than $n$. Each settlement needs $Y_i = H^+_{F(i)}(P^{(i)})$, which conditions on quotes published by stage $F(i)$ — meaning profiles with $e(j) < F(i)$. So computing $a_n$ requires $Y_i$ for $\sigma(i) \le n$, which requires $H^+$ to stage $F(i)$, which requires quotes $a_j$ with $e(j) < F(i)$. Since $e(j) < F(i) < \sigma(i) \le n$, the dependency chain bottoms out at earlier stages, so there's no circularity — the recursion is well-founded as the doc's existence argument shows.

For the response, I need to clarify what "computed by" means: $a_n = A_n(C_n)$ is computed by running the inductor $A$ to stage $n$, which is a $\mathcal{C}_A$ computation because building $D_A^n$ requires simulating $H^+$ to the relevant $F(i)$ stages. The key distinction is that $e(n)$ should track when $a_n$ has actually been evaluated and posted to the stream, not just when it's definitionally available at market stage $n$. I should tighten the $\sigma$ clause similarly for precision.

</details>

$a_n$ is computed by **$A$ itself** — it's literally $A$'s stage-$n$ price, $a_n = A_n(C_n)$. So unlike the $\sigma$ case there's no third party doing the computing; you run the market $A$ out to stage $n$ and read off the price on $C_n$. The reason $e(n)$ ends up enormous relative to $n$ is that "running $A$ to stage $n$" is a $\mathcal{C}_A$ computation: building $D_A^n$ folds in the settlements $\mathcal{A}_i(m_i^*)$ for every $i$ with $\sigma(i)\le n$, each of which required simulating $H^+$ up to $F(i)$. The expense is real, it's just hidden inside "evaluate $A_n$."

The precision worth adding is that "computed" is bundling three distinct moments, and you want $e(n)$ pinned to the right one:

- *defined*: $a_n = A_n(C_n)$ exists as a value at $A$'s market-stage $n$;
- *evaluated*: actually computing that value is the costly $\mathcal{C}_A$ step;
- *posted*: the rounding $\mathcal{B}_n(\ell_n^*)$ is placed into the stream $H^+$ conditions on.

$e(n)$ is the third moment (which dominates the second, since you post only once evaluation finishes). So the clean phrasing is something like: $e(n)$ is the stage by which $A$ has evaluated its quote $a_n = A_n(C_n)$ — by running its market to stage $n$, a $\mathcal{C}_A$ computation because $D_A^n$ carries the $H^+$-simulations feeding its settlements — and the rounded profile $\mathcal{B}_n(\ell_n^*)$ has been posted to the conditioning stream.

The mirror-image point, which is the one I'd actually flag: it's the **$\sigma$ clause**, not the $e$ clause, where "computed by $A$" is the loose attribution. $Y_n := H^+_{F(n)}(P^{(n)})$ is by definition a credence of $H^+$, not of $A$. What $A$ (at $\mathcal{C}_A$ power) does is *simulate* $H^+$ to stage $F(n)$ to obtain it; then the construction enters $\mathcal{A}_n(m_n^*)$ into $D_A$, which is what resolves the $\alpha$-market for $C_n$. So if you write "computed by $A$" for $\sigma$, gloss the mechanism as simulation — otherwise a reader will reasonably ask why an $H^+$ value is attributed to $A$.

Tightened, both clauses in parallel:

- $\sigma(n)$: the stage by which $A$ has obtained $Y_n = H^+_{F(n)}(P^{(n)})$, by simulating $H^+$ to stage $F(n)$, and the settlement $\mathcal{A}_n(m_n^*)$ has entered $D_A$, resolving the $C_n$ market.
- $e(n)$: the stage by which $A$ has evaluated its own quote $a_n = A_n(C_n)$, by running to stage $n$, and the rounded profile $\mathcal{B}_n(\ell_n^*)$ has been posted to the stream $H^+$ reads.

That makes the computing agent explicit in both (it's $A$, or $A$'s power level, throughout) while keeping the objects honestly distinct: $A$ simulating an $H^+$-value on the settlement side, $A$ pricing its own contract on the emission side. Everything above is read straight off your definitions, so I'm confident in it — no appeal to 4.7.2 or anything external.


## Human
*2026-06-09 01:27 UTC*

<details>
<summary>📎 Attachment: pasted content (8226 bytes)</summary>

```

\paragraph{Base reasoner.}
Take a propositional language $\mathcal{L}$ with sentence set $\mathcal{S}$ along with a
theory $\Gamma$ and a $\Gamma$-complete computable deductive process
$D_H=(D_H^t)_{t\ge1}$. Let $\mathcal{C}_H$ be a complexity class closed under
polynomial overhead \footnote{explanation of polynomial overhead} and let $H=(H_1,H_2,\ldots)$ be a \emph{universal inductor} over $D_H$ against $\mathcal{C}_H$. In other words, take a logical inductor $U$ over the empty deductive process with traders in $\mathcal{C}_H$, and then use Bayesian conditioning to define $H = U \mid D_H$. See \href{https://www.lesswrong.com/posts/FnH2G832sWMySptp5}{this explanation} by Diffractor for reference on the fundamental details of the universal inductor construction. $H$ is a market satisfying the logical induction
criterion against traders in $\mathcal{C}_H$. Each stage $H_t$ is a full probability measure over the worlds of $\mathcal{L}$, concentrated on the worlds propositionally consistent with $D_H^t$. Existence of such a
measure-valued inductor over an arbitrary computable deductive process is Lemma~\ref{lem:existence}.

\paragraph{Propositions and deferral.}
Choose a strictly increasing, $\mathcal{C}_H$-computable ``deferral" function
$F:\mathbb{N}^+\to\mathbb{N}^+$ with $F(n)>n+1$. Consider an effective enumeration
$P^{(0)},P^{(1)},\ldots$ of $\mathcal{S}$ where $P^{(n)}$ to be some $n$-th proposition of interest.

\paragraph{Threshold symbols.}
For each $n\ge1$ and $1\le k\le n$ introduce two fresh propositional symbols:
\begin{itemize}
  \item $\alpha_{n,k}$ which can be read as ``the contract for $P^{(n)}$ deferred to $F(n)$ has value at least $k/n$"
  \item $\beta_{n,k}$ which can be read as ``$A$'s published quote for that contract is at least $k/n$."
\end{itemize}
 Let $\mathcal{L}^\alpha:=\mathcal{L}\cup\{\alpha_{n,k}\}$ and
$\mathcal{L}^\beta:=\mathcal{L}\cup\{\beta_{n,k}\}$, with sentence sets
$\mathcal{S}^\alpha$ and $\mathcal{S}^\beta$ respectively, each extending $\mathcal{S}$. The $\alpha$ symbols allow $A$ to price
the future credences of $H^+$ while the $\beta$ symbols
encode $A$'s outputs for $H^+$ to condition on. Because each of these sets of symbols represents threshold sentences, that is claims that a value is at least $\frac{k}{n}$, they respect monotonicity axioms:
\[
\{\alpha_{n,k}\to\alpha_{n,k-1}\}\quad\text{and}\quad
\{\beta_{n,k}\to\beta_{n,k-1}\}\qquad(n\ge1,\ 2\le k\le n).
\]
Note that the readings of the symbols given above are glosses for our metalanguage, and are only baked into the inductors in the form of the monotonicity axioms. For a world $W$ consistent with these axioms each truth-set is an initial
segment, so we can define values as proportions of true threshold sentences:
\[
\mathrm{val}^\alpha_W(n):=\tfrac1n\#\{k:W(\alpha_{n,k})=1\},
\qquad
\mathrm{val}^\beta_W(n):=\tfrac1n\#\{k:W(\beta_{n,k})=1\}
\]
each taking the form $m/n$ for an integer $0\le m\le n$. Using these values, the addition of the threshold symbols to the language allows for the representation of a real-valued unknown rounded to the nearest $\frac{1}{n}$.

\paragraph{Contracts and quotes.}
Define the deferred contract $C_n$ and the quote readout $Q_n$ as affine combinations
\[
C_n:=\tfrac1n\sum_{k=1}^n\alpha_{n,k},
\qquad
Q_n:=\tfrac1n\sum_{k=1}^n\beta_{n,k},
\]
so $W(C_n)=\mathrm{val}^\alpha_W(n)$ and $W(Q_n)=\mathrm{val}^\beta_W(n)$
for consistent worlds $W$. Note that both $C_n$ and $Q_n$ are affine combinations of symbols
already in the markets used for convenience rather than separately traded objects. Write
\[
a_n:=A_n(C_n)=\tfrac1n\sum_k A_n(\alpha_{n,k})\in\mathbb{Q}\cap[0,1]
\]
for $A$'s published quote on the deferred contract and
\[
Y_n:=H^+_{F(n)}(P^{(n)})
\]
for the eventual credence of $H^+$ that the contract uses for settlement. 

\paragraph{A more powerful reasoner.}
Let $\mathcal{C}_A\supseteq\mathcal{C}_H$ be a complexity class closed under
polynomial overhead for which the map $n\mapsto Y_n$ is $\mathcal{C}_A$-computable
in the coupled system. More precisely, given $n$, an implementation in $\mathcal{C}_A$ can simulate the mutual construction up to stage $F(n)$ and output $Y_n$. Writing $R(t)$ for the per-stage runtime of the
implementation of $H^+$, we assume $\mathcal{C}_A$ contains $n\mapsto R(F(n))$. This is a significant idealizing assumption about the computational power of $A$ needed so that its deferred bets can eventually deductively resolve. Note, though, that the simulation need not be practically implementable by the traders.

\paragraph{Timing.}
Define two new scheduling functions: a ``settlement" function $\sigma(n)$ representing the stage at which $Y_n$ is computed by $A$, causing the markets for $C_n$ to resolve and an ``emission" function $e(n)$ representing the stage by which $A$'s quote $a_n$ has been computed and published. Assume both of these functions are $\mathcal{C}_A$-computable and strictly increasing from $\mathbb{N}^+$ to $\mathbb{N}^+$. Recall that $F(n)$ is the deferral function, used as the stage of $H^+$'s prices referred to by the contracts. Assume that these schedules are related by the following inequality:

\[
e(n)<F(n)<\sigma(n)
\]

In other words, quotes are always published before the stage that they refer to, which is before the stage at which the contracts are settled.  

\paragraph{The inductor $A$.}
Let's now define $A$ and $H^+$ as two inductors that can see each other, constructed via recursion. For $0\le m\le n$ write the settling profile 
\[
\mathcal{A}_n(m):=\{\alpha_{n,k}:k\le m\}\cup\{\neg\alpha_{n,k}:k>m\}
\]
which should be read as ``$C_n$ is approximately equal to $\frac{m}{n}$.'' Let
\[
m_n^*:=\argmin_{0\le m\le n}\left|\tfrac mn-Y_n\right|
\]
with ties going to the lower $m$, i.e. the best approximation of the real-valued settlement $Y_n$. We therefore have
\[
\left|\tfrac{m_n^*}{n}-Y_n\right|\le\tfrac1{2n}
\]
because the grid $\{0,\frac1n,\frac2n,\ldots,1\}$ has spacing $\frac1n$, so every value in $[0,1]$ is within $\frac1{2n}$ of some grid point. Define the computable deductive process
$D_A$ over $\mathcal{L}^\alpha$ as one that, for each time step $t$, $D_A^t$ includes the $\alpha$-monotonicity axioms for $n\le t$ and the profile $\mathcal{A}_n(m_n^*)$ for each $n$ with $\sigma(n)\le t$.
Each $D_A^t$ is finite (axiom schemata and settlement profiles are finite at any finite stage) and consistent (distinct $n$ touch disjoint symbols for both axioms and profiles, settlements are initial segments respecting monotonicity). $D_A$ is
computable as part of the mutual construction, since $\sigma(n)>F(n)$ makes $Y_n$ available
before its settlement is required by $D_A$. Let $A=(A_1,A_2,\ldots)$ be a universal
inductor over $D_A$ against $\mathcal{C}_A$.

\paragraph{The inductor $H^+$.}
Similarly, define the quote profile
\[
\mathcal{B}_n(\ell):=\{\beta_{n,k}:k\le\ell\}\cup\{\neg\beta_{n,k}:k>\ell\}
\]
as a set of atoms representing a posted quote and let
\[
\ell_n^*:=\argmin_{0\le\ell\le n}\left|\tfrac\ell n-a_n\right|
\]
with ties going to the lower $\ell$. Then $\mathcal{B}_n(\ell_n^*)$ is the rounding of $A$'s quote to a grid with spacing $\frac{1}{n}$. Take the base inductor $H$ to be defined over the extended language $\mathcal{L}^\beta$, with the $\beta$-monotonicity axioms adjoined to $\Gamma$, so that it assigns credences to $A$'s quote atoms. Writing
\[
Q_A^{(t)}:=\bigwedge_{i\,:\,e(i)<t}\mathcal{B}_i(\ell_i^*)
\]
for the conjunction of those quote profiles \emph{published by time $t$}, define the augmented human inductor by conditioning,
\[
H^+:=H\mid Q_A,\qquad H^+_t(\cdot):=H_t\!\left(\,\cdot\mid Q_A^{(t)}\right).
\]

[REPLACE THIS PARAGRAPH] The sequence $t\mapsto Q_A^{(t)}$ is an efficiently computable deductive process: only the finitely many profiles with $e(i)<t$ appear by stage $t$, and because $e$ dominates each quote's production cost, all of them can be recomputed within $\mathcal{C}_H$'s budget as a function of $t$. By closure under conditioning (Garrabrant et al., Theorem 4.7.2), applied to this efficiently computable conditioning sequence, $H^+$ is again a universal inductor against traders in $\mathcal{C}_H$, now over $\Gamma$ together with the published quote profiles.
```

</details>

Ok here's what i want, I want to be explicit about the relationship between n mapsto R(F(n)) and t mapsto Q_A^t. We can change the earlier a more powerful reasoner part to like n mapto cumulative run cost or something if that's better


## Assistant
*2026-06-09 01:27 UTC*


## Human
*2026-06-09 01:27 UTC*

<details>
<summary>📎 Attachment: pasted content (8226 bytes)</summary>

```

\paragraph{Base reasoner.}
Take a propositional language $\mathcal{L}$ with sentence set $\mathcal{S}$ along with a
theory $\Gamma$ and a $\Gamma$-complete computable deductive process
$D_H=(D_H^t)_{t\ge1}$. Let $\mathcal{C}_H$ be a complexity class closed under
polynomial overhead \footnote{explanation of polynomial overhead} and let $H=(H_1,H_2,\ldots)$ be a \emph{universal inductor} over $D_H$ against $\mathcal{C}_H$. In other words, take a logical inductor $U$ over the empty deductive process with traders in $\mathcal{C}_H$, and then use Bayesian conditioning to define $H = U \mid D_H$. See \href{https://www.lesswrong.com/posts/FnH2G832sWMySptp5}{this explanation} by Diffractor for reference on the fundamental details of the universal inductor construction. $H$ is a market satisfying the logical induction
criterion against traders in $\mathcal{C}_H$. Each stage $H_t$ is a full probability measure over the worlds of $\mathcal{L}$, concentrated on the worlds propositionally consistent with $D_H^t$. Existence of such a
measure-valued inductor over an arbitrary computable deductive process is Lemma~\ref{lem:existence}.

\paragraph{Propositions and deferral.}
Choose a strictly increasing, $\mathcal{C}_H$-computable ``deferral" function
$F:\mathbb{N}^+\to\mathbb{N}^+$ with $F(n)>n+1$. Consider an effective enumeration
$P^{(0)},P^{(1)},\ldots$ of $\mathcal{S}$ where $P^{(n)}$ to be some $n$-th proposition of interest.

\paragraph{Threshold symbols.}
For each $n\ge1$ and $1\le k\le n$ introduce two fresh propositional symbols:
\begin{itemize}
  \item $\alpha_{n,k}$ which can be read as ``the contract for $P^{(n)}$ deferred to $F(n)$ has value at least $k/n$"
  \item $\beta_{n,k}$ which can be read as ``$A$'s published quote for that contract is at least $k/n$."
\end{itemize}
 Let $\mathcal{L}^\alpha:=\mathcal{L}\cup\{\alpha_{n,k}\}$ and
$\mathcal{L}^\beta:=\mathcal{L}\cup\{\beta_{n,k}\}$, with sentence sets
$\mathcal{S}^\alpha$ and $\mathcal{S}^\beta$ respectively, each extending $\mathcal{S}$. The $\alpha$ symbols allow $A$ to price
the future credences of $H^+$ while the $\beta$ symbols
encode $A$'s outputs for $H^+$ to condition on. Because each of these sets of symbols represents threshold sentences, that is claims that a value is at least $\frac{k}{n}$, they respect monotonicity axioms:
\[
\{\alpha_{n,k}\to\alpha_{n,k-1}\}\quad\text{and}\quad
\{\beta_{n,k}\to\beta_{n,k-1}\}\qquad(n\ge1,\ 2\le k\le n).
\]
Note that the readings of the symbols given above are glosses for our metalanguage, and are only baked into the inductors in the form of the monotonicity axioms. For a world $W$ consistent with these axioms each truth-set is an initial
segment, so we can define values as proportions of true threshold sentences:
\[
\mathrm{val}^\alpha_W(n):=\tfrac1n\#\{k:W(\alpha_{n,k})=1\},
\qquad
\mathrm{val}^\beta_W(n):=\tfrac1n\#\{k:W(\beta_{n,k})=1\}
\]
each taking the form $m/n$ for an integer $0\le m\le n$. Using these values, the addition of the threshold symbols to the language allows for the representation of a real-valued unknown rounded to the nearest $\frac{1}{n}$.

\paragraph{Contracts and quotes.}
Define the deferred contract $C_n$ and the quote readout $Q_n$ as affine combinations
\[
C_n:=\tfrac1n\sum_{k=1}^n\alpha_{n,k},
\qquad
Q_n:=\tfrac1n\sum_{k=1}^n\beta_{n,k},
\]
so $W(C_n)=\mathrm{val}^\alpha_W(n)$ and $W(Q_n)=\mathrm{val}^\beta_W(n)$
for consistent worlds $W$. Note that both $C_n$ and $Q_n$ are affine combinations of symbols
already in the markets used for convenience rather than separately traded objects. Write
\[
a_n:=A_n(C_n)=\tfrac1n\sum_k A_n(\alpha_{n,k})\in\mathbb{Q}\cap[0,1]
\]
for $A$'s published quote on the deferred contract and
\[
Y_n:=H^+_{F(n)}(P^{(n)})
\]
for the eventual credence of $H^+$ that the contract uses for settlement. 

\paragraph{A more powerful reasoner.}
Let $\mathcal{C}_A\supseteq\mathcal{C}_H$ be a complexity class closed under
polynomial overhead for which the map $n\mapsto Y_n$ is $\mathcal{C}_A$-computable
in the coupled system. More precisely, given $n$, an implementation in $\mathcal{C}_A$ can simulate the mutual construction up to stage $F(n)$ and output $Y_n$. Writing $R(t)$ for the per-stage runtime of the
implementation of $H^+$, we assume $\mathcal{C}_A$ contains $n\mapsto R(F(n))$. This is a significant idealizing assumption about the computational power of $A$ needed so that its deferred bets can eventually deductively resolve. Note, though, that the simulation need not be practically implementable by the traders.

\paragraph{Timing.}
Define two new scheduling functions: a ``settlement" function $\sigma(n)$ representing the stage at which $Y_n$ is computed by $A$, causing the markets for $C_n$ to resolve and an ``emission" function $e(n)$ representing the stage by which $A$'s quote $a_n$ has been computed and published. Assume both of these functions are $\mathcal{C}_A$-computable and strictly increasing from $\mathbb{N}^+$ to $\mathbb{N}^+$. Recall that $F(n)$ is the deferral function, used as the stage of $H^+$'s prices referred to by the contracts. Assume that these schedules are related by the following inequality:

\[
e(n)<F(n)<\sigma(n)
\]

In other words, quotes are always published before the stage that they refer to, which is before the stage at which the contracts are settled.  

\paragraph{The inductor $A$.}
Let's now define $A$ and $H^+$ as two inductors that can see each other, constructed via recursion. For $0\le m\le n$ write the settling profile 
\[
\mathcal{A}_n(m):=\{\alpha_{n,k}:k\le m\}\cup\{\neg\alpha_{n,k}:k>m\}
\]
which should be read as ``$C_n$ is approximately equal to $\frac{m}{n}$.'' Let
\[
m_n^*:=\argmin_{0\le m\le n}\left|\tfrac mn-Y_n\right|
\]
with ties going to the lower $m$, i.e. the best approximation of the real-valued settlement $Y_n$. We therefore have
\[
\left|\tfrac{m_n^*}{n}-Y_n\right|\le\tfrac1{2n}
\]
because the grid $\{0,\frac1n,\frac2n,\ldots,1\}$ has spacing $\frac1n$, so every value in $[0,1]$ is within $\frac1{2n}$ of some grid point. Define the computable deductive process
$D_A$ over $\mathcal{L}^\alpha$ as one that, for each time step $t$, $D_A^t$ includes the $\alpha$-monotonicity axioms for $n\le t$ and the profile $\mathcal{A}_n(m_n^*)$ for each $n$ with $\sigma(n)\le t$.
Each $D_A^t$ is finite (axiom schemata and settlement profiles are finite at any finite stage) and consistent (distinct $n$ touch disjoint symbols for both axioms and profiles, settlements are initial segments respecting monotonicity). $D_A$ is
computable as part of the mutual construction, since $\sigma(n)>F(n)$ makes $Y_n$ available
before its settlement is required by $D_A$. Let $A=(A_1,A_2,\ldots)$ be a universal
inductor over $D_A$ against $\mathcal{C}_A$.

\paragraph{The inductor $H^+$.}
Similarly, define the quote profile
\[
\mathcal{B}_n(\ell):=\{\beta_{n,k}:k\le\ell\}\cup\{\neg\beta_{n,k}:k>\ell\}
\]
as a set of atoms representing a posted quote and let
\[
\ell_n^*:=\argmin_{0\le\ell\le n}\left|\tfrac\ell n-a_n\right|
\]
with ties going to the lower $\ell$. Then $\mathcal{B}_n(\ell_n^*)$ is the rounding of $A$'s quote to a grid with spacing $\frac{1}{n}$. Take the base inductor $H$ to be defined over the extended language $\mathcal{L}^\beta$, with the $\beta$-monotonicity axioms adjoined to $\Gamma$, so that it assigns credences to $A$'s quote atoms. Writing
\[
Q_A^{(t)}:=\bigwedge_{i\,:\,e(i)<t}\mathcal{B}_i(\ell_i^*)
\]
for the conjunction of those quote profiles \emph{published by time $t$}, define the augmented human inductor by conditioning,
\[
H^+:=H\mid Q_A,\qquad H^+_t(\cdot):=H_t\!\left(\,\cdot\mid Q_A^{(t)}\right).
\]

[REPLACE THIS PARAGRAPH] The sequence $t\mapsto Q_A^{(t)}$ is an efficiently computable deductive process: only the finitely many profiles with $e(i)<t$ appear by stage $t$, and because $e$ dominates each quote's production cost, all of them can be recomputed within $\mathcal{C}_H$'s budget as a function of $t$. By closure under conditioning (Garrabrant et al., Theorem 4.7.2), applied to this efficiently computable conditioning sequence, $H^+$ is again a universal inductor against traders in $\mathcal{C}_H$, now over $\Gamma$ together with the published quote profiles.
```

</details>

Ok here's what i want, I want to be explicit about the relationship between n mapsto R(F(n)) and t mapsto Q_A^t at the end of what I currently have. We can change the earlier a more powerful reasoner part to like n mapto cumulative run cost or something if that's better


## Assistant
*2026-06-09 01:31 UTC*

<details>
<summary>💭 Thinking</summary>

 I need to clarify the relationship between these two computability assumptions: the function mapping stage indices to runtimes of the stronger reasoner's implementation, which should live in $\mathcal{C}_A$, and the conditioning sequence that needs to be efficiently computable within $\mathcal{C}_H$. Actually, I need to clarify the definition of "efficiently computable" in the logical induction framework — it means a sequence where a single Turing machine can output the $n$-th element in time polynomial in $n$. The logical induction criterion then requires that no efficiently computable trader can exploit the market, and the market itself has some runtime $R(t)$ for producing stage-$t$ prices.

For $A$ to compute the output at stage $F(n)$, it needs to simulate $H^+$ up to that stage, which costs roughly $R(F(n))$ — so the assumption that $\mathcal{C}_A$ contains the function $n \mapsto R(F(n))$ captures $A$'s computational budget. Meanwhile, for $H^+$ to condition on $Q_A^{(t)}$, the conditioning sequence must itself be efficiently computable within $\mathcal{C}_H$'s constraints, but computing $Q_A^{(t)}$ requires knowing the quotes $a_i$ for all $e(i) < t$, which in turn requires running $A$ to stage $i$ — creating a tension between what $H^+$ needs to condition on and what it can afford to compute.

The circularity concern is whether this creates a cost blowup: $H^+$ at stage $t$ needs $Q_A^{(t)}$, which requires computing $a_i$ for $e(i) < t$, which requires simulating $H^+$ to stages $F(j)$ for $\sigma(j) \le i$. The key question is whether those stages $F(j)$ stay below $t$, and I'm working through the ordering constraints to verify this doesn't spiral.

The real tension emerges when I consider the cost model: computing $Q_A^{(t)}$ requires running $A$, which is expensive in $\mathcal{C}_A$, but $H^+$ only has a $\mathcal{C}_H$ budget where $\mathcal{C}_A \supsetneq \mathcal{C}_H$. So naively $H^+$ can't afford to compute $Q_A^{(t)}$ at all. The emission lag is supposed to resolve this tension, but I need to see how.

The key insight is that $Q_A^{(t)}$ only includes quotes $a_i$ where $e(i) < t$. Since the emission schedule $e$ is designed so that $e(i)$ bounds the cumulative cost of computing $a_i$, any quote in $Q_A^{(t)}$ costs at most $e(i) < t$ to compute. With at most $t$ such quotes (since $e$ is strictly increasing and $e(i) \geq i$), the total cost is bounded by $t^2$, which is polynomial in $t$. This polynomial overhead fits within $\mathcal{C}_H$ by assumption, so the conditioning step becomes feasible—the cost of each quote is "charged" to its emission stage, keeping everything within budget.

The explicit relationship Anson is after links two assumptions: first, $\mathcal{C}_A$ containing $n \mapsto R(F(n))$ ensures $A$ can afford to compute the quotes at all; second, the emission schedule $e$ is chosen so that $e(n)$ dominates the cumulative cost of producing $a_n$. This ensures the published stream is computable within $\mathcal{C}_H$'s budget because every quote published by stage $t$ was already cheap enough to have been computed by that stage.

The key insight is that $e(n)$ must dominate the cost of computing $a_n$, which is essentially the cost of simulating $H^+$ to the relevant stages plus $A$'s own market-making overhead. This domination is what transforms the fact that $Q_A^{(t)}$ embeds expensive $\mathcal{C}_A$ computations into the fact that $Q_A^{(t)}$ itself is computable in polynomial time, making it accessible to $\mathcal{C}_H$.

Now I'm clarifying whether $R$ should represent per-stage or cumulative runtime. The per-stage interpretation works fine because the cumulative cost to simulate $H^+$ to stage $F(n)$ is bounded by $F(n) \cdot R(F(n))$, which stays within $\mathcal{C}_A$ through polynomial overhead. Anson's suggestion to reframe the "more powerful reasoner" part in terms of cumulative run cost might be cleaner, since that's what actually matters for the argument.

The unifying object would be $\Lambda(n)$ — the total time to compute $a_n$ within the coupled construction, which includes running $A$ to stage $n$ and simulating $H^+$ to the necessary stages. Then the power assumption becomes that $\Lambda$ is $\mathcal{C}_A$-computable, meaning $A$ can afford to produce its own cost quotes. But I need to be more careful about what the "more powerful reasoner" assumption is actually doing here.

The key insight is that $A$ needs to compute $Y_n$ to build its deductive process $D_A$, since the settlements require those values — this is the "$A$ is powerful enough to simulate $H^+$" assumption. Meanwhile, the conditioning assumption for $H^+$ is different: it requires that the published quotes by stage $t$ are efficiently computable within $\mathcal{C}_H$. Both assumptions ultimately constrain the cost of running the coupled construction, with $R(F(n))$ bounding the $H^+$-simulation cost and the emission lag $e(n)$ needing to dominate the total cost of producing $a_n$. So the relationship Anson is trying to make explicit is that $e(n)$ must grow at least as fast as the cumulative cost of computing $a_n$, which is governed by the same $R(F(\cdot))$ quantity that appears in the "$A$ is powerful enough" assumption — the $\mathcal{C}_A$-affordability of $R(F(n))$ ensures $a_n$ is computable (making the construction well-defined), while the lag $e(n) \ge \Lambda(n)$ ensures the published stream is $\mathcal{C}_H$-cheap (so conditioning applies). These are two sides of the same cost constraint: one says $A$ can afford to compute it, the other says we wait long enough that $H^+$ only ever re-reads quotes whose cost was already absorbed into an earlier stage.

Now I'm verifying the inequality direction and the mechanism. The key is that at stage $t$, $H^+$ computes $Q_A^{(t)}$ by evaluating each $a_i$ where $e(i) < t$. Since each $a_i$ costs $\Lambda(i)$ to compute and $e(i) \ge \Lambda(i)$ by design, we have $e(i) < t \Rightarrow \Lambda(i) < t$, so every quote in the conjunction costs less than $t$. The number of such quotes is bounded by $t$ (since $e$ is strictly increasing), giving a total cost of roughly $t^2$ plus polynomial overhead, which stays within $\mathcal{C}_H$'s budget. So the critical choice is setting $e(n) \ge \Lambda(n)$ where $\Lambda(n)$ is the cumulative cost to produce $a_n$, and this cost is dominated by the $R(F(\cdot))$ simulations and $A$'s own market cost.

The two conditions that make this work are: first, $\Lambda$ must be $\mathcal{C}_A$-computable (meaning $A$ can actually produce its quotes), and second, the emission rule $e(n) \ge \Lambda(n)$ ensures we don't publish a quote before it's ready. This bridges the gap between $R(F(n))$ living in $\mathcal{C}_A$ and $Q_A^{(t)}$ being $\mathcal{C}_H$-cheap—the lag $e$ absorbs the entire cost difference. Now I'm checking whether the recomputation cost is calculated fresh at each stage or amortized across stages. Even with the redundant recomputation, each quote's cost stays bounded by $\Lambda(i) < t$, and summing across at most $t$ quotes gives $O(t^2)$ total—still polynomial. I'm also reconsidering Anson's point about introducing cumulative run cost upfront in the "more powerful reasoner" section, since what actually needs to be dominated by $e$ is the total cost of producing $a_n$, not just the per-stage runtime alone. Defining cumulative cost explicitly would let both assumptions reference it cleanly.

But there's a subtlety: should I fold $A$'s own market-making cost into the cumulative cost, or just the $H^+$-simulation cost? The total cost $\Lambda(n)$ includes both running $A$'s market against the traders and simulating $H^+$ to produce the necessary quotes—the simulation is usually the dominant piece due to the deep recursion, but $A$'s overhead is also there. For the cleanest statement, I should define $\Lambda(n)$ as the total time for the entire coupled construction to output $a_n$, then verify that $A$ can compute its own quotes within this bound.

The key insight is that both the map $n \mapsto Y_n$ and $a_n = A_n(C_n)$ are $\mathcal{C}_A$-computable in the coupled system—that's the core "power" assumption—with $\Lambda(n)$ being a $\mathcal{C}_A$-bounded runtime function.

Now I'm refactoring the presentation: define $\Lambda(n)$ as the cumulative time to compute $a_n$ in the coupled construction, assume it's $\mathcal{C}_A$-bounded, and then check the timing constraints. The emission condition becomes $e(n) \ge \Lambda(n)$ alongside the ordering $e(n) < F(n) < \sigma(n)$, which means $F$ must dominate $\Lambda$. Since all schedules are free parameters in $\mathcal{C}_A$, I can just set $e(n) = \Lambda(n)$ (or slightly above), then $F(n) > e(n)$, then $\sigma(n) > F(n)$—no conflict.

But wait, I need to be careful about what $\Lambda(n)$ actually includes. Computing $a_n = A_n(C_n)$ requires $D_A^n$, which contains settlements for $\sigma(j) \le n$. Since $\sigma(j) > F(j) > j$, this means $j < n$, so $\Lambda(n)$ only involves simulating $H^+$ to stages less than $n$, not to $F(n)$ itself. That's consistent with well-foundedness. The simulation to $F(n)$ is a separate, later requirement—it's needed for computing the settlement $Y_n$ that feeds into $\sigma(n)$, which happens much further down the timeline.

So there are really two distinct cost quantities here: one for computing $a_n$ (which governs when $e(n)$ fires), involving $H^+$ simulations to stages below $n$ and running $A$ to stage $n$, and another for computing $Y_n$ (which governs $\sigma(n)$), involving simulation to $F(n)$. The assumption that $\mathcal{C}_A$ contains $n \mapsto R(F(n))$ is specifically about the second cost—it's what makes the settlements computable and governs $\sigma$, not $e$.

Now I'm wondering whether $R(F(n))$ is even the right quantity for what Anson is asking about regarding the relationship between $n \mapsto R(F(n))$ and $t \mapsto Q_A^t$. The query $Q_A^{(t)}$ needs to be $\mathcal{C}_H$-computable and embeds computing $a_i$ for all $e(i) < t$. Each $a_i$ costs $\Lambda_e(i)$, which involves $H^+$ simulations to stages below $i$ and $A$'s market up to stage $i$.

Actually, $R(F(\cdot))$ does show up in $\Lambda_e$—when computing $a_i$, I need to simulate $H^+$ to $F(j)$ for all $j$ where $\sigma(j) \le i$, and since $F(j) < \sigma(j)$, these are all indices $j < i$. The cost of each such simulation is dominated by $R(F(j))$, so $\Lambda_e(i)$ is built from $R(F(j))$ terms for $j < i$. This means $R(F(\cdot))$ is the fundamental building block for both $\Lambda_\sigma$ and $\Lambda_e$.

I need to step back and figure out what level of detail Anson actually needs and how to present this cleanly, especially for the final paragraph where I should be explicit about how $n \mapsto R(F(n))$ (the $\mathcal{C}_A$ quantity) connects to everything.

Anson wants me to show how the cost function relates to the computability assumption, and he's open to refactoring the "more powerful reasoner" framing to use a cumulative run-cost function if it's cleaner. I think the best approach is to present two options with reasoning: either keep $R(F(n))$ and explain in the final paragraph how the emission schedule dominates the simulation costs so that every quote is fully computed before stage $t$, or replace it with a single cumulative cost function that's more direct. There's a crucial distinction I need to be precise about: the cost of computing the quotes themselves versus the cost of computing the settlements. The former drives the $Q_A^{(t)}$ bound, while the latter appears in the "more powerful reasoner" section. They're related through the settlement costs needed to run $A$ to stage $n$, where the dominant cost comes from the largest settlement within that range. I'm working through the cleanest way to present this without losing the technical accuracy.

The key insight is that I should define a single unified quantity—the total time for the entire coupled construction to run through producing quote $a_n$—and let that be the thing $e$ needs to dominate. This subsumes all the sub-computations: the $H^+$ simulations, running $A$ to stage $n$, everything. The $R(F(n))$ bound then becomes the witness that this total cost stays within $\mathcal{C}_A$, rather than the primary object of study. The emission condition is simply that $e(n)$ exceeds this total cost, and the relationship between $e$ and the $\mathcal{C}_A$-bounded cost determines what's publicly verifiable. The key constraint is that $D_A$ must be computable within the $\mathcal{C}_A$ budget, which means the settlement $Y_n$ needs to be available by stage $\sigma(n)$ at an affordable cost. This boils down to requiring $\sigma(n) > F(n)$ for ordering, plus ensuring that computing $Y_n$ up to stage $F(n)$ fits within $\mathcal{C}_A$—which is exactly the $R(F(n))$ assumption. So the precise requirement is that $D_A^t$ remains $\mathcal{C}_A$-computable as a function of $t$, with the settlement cost absorbed by the domination condition on $\sigma$.

I'm getting caught in the technical weeds here when what I should do is step back and present the recommendation cleanly: flag the one key subtlety about which cost function matters, give him the explicit relationship he's asking for, and frame it in natural language with minimal symbols since he's been asking for editorial guidance rather than LaTeX drafts.

The core insight is that the cumulative cost of producing each quote $\Lambda(n)$ is the $\mathcal{C}_A$-quantity that matters, and the single mechanism that converts the $\mathcal{C}_A/\mathcal{C}_H$ gap into mere lateness is the emission condition $e(n) \ge \Lambda(n)$. Once that's in place, the end-paragraph relationship becomes straightforward: $H^+$ never pays the expensive $\mathcal{C}_A$ cost because it never computes a quote before that quote has been published, so at any stage $t$ the quotes it's working with are only those whose full production finished earlier, making the total recomputation cost polynomial in $t$.

The subtlety worth flagging is that there are two distinct cost quantities here—the cost of computing settlements (which is $R(F(n))$ and governs $\sigma$) versus the cost of computing quotes (which is $\Lambda(n)$ and governs $e$)—and I should make sure he doesn't conflate them in his phrasing, even though they're related through the domination relationship.

</details>

The cleanest version does what you're gesturing at: collapse $R(F(n))$ into one cumulative-cost function and let *that* be the thing $e$ dominates. Then the relationship you want is a one-line consequence rather than a re-derivation — and it slots in exactly as the quantitative witness we'd agreed to footnote two turns ago, now spelled out.

**Define the cost once.** In "more powerful reasoner," instead of leading with the per-stage $R$, name the quantity that actually carries the load: let $\Lambda(n)$ be the total time the coupled construction takes to *emit* the quote $a_n$ — i.e. to run $A$ to stage $n$, which folds in every $H^+$-simulation that $D_A^n$ needs (the settlements $Y_j$ for $\sigma(j)\le n$). Assume $\Lambda$ is $\mathcal{C}_A$-bounded. Then $R(F(n))$ stops being a standalone assumption and becomes the *witness* for $\Lambda\in\mathcal{C}_A$: the deepest sub-computations are the cross-agent simulations to deferral stages, and since $R$ is increasing and $F(n)>n$, $R(F(n))$ dominates them up to polynomial overhead. So "$\mathcal{C}_A\ni n\mapsto R(F(n))$" demotes to a footnote on why $\Lambda$ is affordable.

**Emission condition becomes one line.** In Timing, alongside the ordering $e(n)<F(n)<\sigma(n)$, require $e(n)\ge\Lambda(n)$ — publish a quote no earlier than the stage by which its full computation has finished. No conflict with the ordering, since all three schedules are free to grow as fast as needed: pick $e\ge\Lambda$, then $F>e$, then $\sigma>F$.

**The end-paragraph relationship**, now purely a consequence you can state directly:

> The quotes are $\mathcal{C}_A$-expensive to produce — $\Lambda(n)$ may lie well outside $\mathcal{C}_H$ — but $H^+$ never pays that cost, because it never computes a quote before the quote is published, and $e(n)\ge\Lambda(n)$. Hence at any stage $t$ the conjunction $Q_A^{(t)}$ ranges only over quotes whose entire production finished at some stage $e(i)<t$, so $\Lambda(i)<t$ for each. Since $e$ is strictly increasing, at most $t-1$ indices satisfy $e(i)<t$, so recomputing all of them from scratch costs at most $\sum_{i:\,e(i)<t}\Lambda(i)<t^2$ — polynomial in $t$. With $\mathcal{C}_H$ closed under polynomial overhead, $t\mapsto Q_A^{(t)}$ is efficiently computable relative to $\mathcal{C}_H$, which is the hypothesis Theorem 4.7.2 consumes. The entire $\mathcal{C}_A/\mathcal{C}_H$ gap is absorbed into the lag $e$: it surfaces as lateness of publication, never as per-stage expense for $H^+$.

That's the explicit link — $R(F(n))$ (via $\Lambda$) is the $\mathcal{C}_A$ quantity, $e\ge\Lambda$ is the single mechanism converting it into a $\mathcal{C}_H$-cheap conditioning stream. The counting bound is a clean fact, ~90% confident as written.

**One subtlety, and it's the thing I'd be careful about (~85% it matters for your phrasing): don't fuse the two costs.** There are two distinct quantities and only one governs $e$.

- Cost of the *settlement* $Y_n$ = simulating $H^+$ all the way to $F(n)$. This is literally the $R(F(n))$ quantity, and it governs $\sigma$ and $D_A$'s computability — not $e$.
- Cost of the *quote* $a_n$ = running $A$ to stage $n$, which only reaches simulations to $F(j)<n$. This is $\Lambda(n)$, and it's what governs $e$ and hence $Q_A$.

They're related — $R(F(n))$ dominates $\Lambda(n)$, so the same $\mathcal{C}_A$ assumption covers both — but in the end-paragraph the operative cost is $\Lambda$ (quote production). If you define your single function as "cost to emit $a_n$," you're fine, because that *is* the quote cost. The trap is writing $e(n)\ge R(F(n))$: that's the settlement cost, the wrong quantity, and it would force $e$ larger than it needs to be (and muddy why $e<F<\sigma$ is even consistent). State $e$'s lower bound in terms of $\Lambda$, keep $R(F(n))$ on the $\sigma$/settlement side.


## Human
*2026-06-09 01:36 UTC*

Ok so let's redefine R as the total cost. Can you be really explicit about what the statement in a more powerful reasoner is and what the statement at the end about e is


## Assistant
*2026-06-09 01:38 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson wants me to be explicit about two key points now that we're redefining $R$ as the total cumulative cost instead of per-stage runtime. I need to clarify what assumption goes into the statement in "A more powerful reasoner" and what the emission condition is at the end regarding $e$. Since $R$ now represents total cost, it's taking on the role of what I was previously calling $\Lambda$, so I need to work out the precise relationships.

The critical decision is what $R(n)$ actually measures — whether it's the total cost to emit quote $a_n$ (running $A$ to stage $n$), which would govern $e$, or something broader that encompasses both the emission and settlement sides. If I go with the first option, the statement about $A$ being able to simulate $H^+$ to $F(n)$ for the settlement $Y_n$ would need separate treatment. I'm weighing whether to define $R$ narrowly for the emission side or more comprehensively.

Option 2 is cleaner: let $R(n)$ be the total cumulative cost to simulate the entire coupled construction through stage $n$. Then computing $a_n$ costs at most $R(n)$ (it's a stage-$n$ object), and computing $Y_n$ costs at most $R(F(n))$ (it's a stage-$F(n)$ object). This way both the settlement and emission sides are expressed through the same monotone function $R$, just evaluated at different stages — which seems to be what Anson is suggesting when he says to redefine $R$ as the total cost.

The key insight is that the coupled construction is well-founded: stage-$t$ objects depend only on earlier stages, so simulating through stage $t$ has a well-defined cumulative cost. Now the "more powerful reasoner" assumption becomes: $A$ is capable of running this simulation, specifically computing the settlements $Y_n$ it needs, which requires simulating to stage $F(n)$ at cost $R(F(n))$.

For the emission condition, since producing $a_n$ costs $R(n)$, we shouldn't publish before that: $e(n) \ge R(n)$. At stage $t$, the active contracts are those with $e(i) < t$, which means $R(i) < t$, giving us fewer than $t$ contracts to recompute — a quadratic cost that stays within $\mathcal{C}_H$.

The two sides now have a clean symmetry: settlements use $R(F(n))$ (the deferral stage), while emissions use $R(n)$ (the quote's own stage). This creates the constraint $R(n) \le e(n) < F(n)$, so we need $F(n) > R(n)$. Since $F$ is $\mathcal{C}_A$-computable and can grow arbitrarily fast, we can always choose $F$ large enough. We also need $\sigma(n) > F(n)$ and $\sigma(n) \ge R(F(n))$ to cover the cost of computing $Y_n$ at settlement.

The binding constraint turns out to be $\sigma(n) \ge R(F(n))$, which automatically implies $\sigma(n) > F(n)$ since the cumulative cost to stage $F(n)$ is at least $F(n)$ itself. So the cleanest way to state this is with the ordering $e < F < \sigma$ plus the explicit cost condition that $\mathcal{C}_A$ can compute $R(F(n))$ — that's the "more powerful reasoner" statement Anson asked for. So the key insight is that the assumption collapses to a single statement: $\mathcal{C}_A$ contains the map $n \mapsto R(F(n))$, where $R(t)$ is the total cumulative cost of simulating the coupled construction through stage $t$. Once we can afford that simulation cost, computing the settlements $Y_n$ follows automatically since they're just read off from the stage-$F(n)$ state—so the "more powerful reasoner" statement is really just saying that $A$ can afford to compute the settlements its own deductive process produces.

The timing constraint is tighter than the current draft suggests: we need $\sigma(n) \ge R(F(n))$ to ensure the settlement is available in time, not just $\sigma(n) > F(n)$. The latter only guarantees that $Y_n$ is *defined* as a stage-$F(n)$ object, but the actual *computation* of $Y_n$ requires the full cost $R(F(n))$ to have been paid by stage $\sigma(n)$. So the clean formulation is $\sigma(n) \ge R(F(n))$, which mirrors the $e(n) \ge R(n)$ condition perfectly: both ensure the relevant object is computed before its timestamp. This gives us a symmetric pair where $e(n) < F(n) < \sigma(n)$ sits consistently between the cost bounds, with $R(n) \le e(n)$ and $R(F(n)) \le \sigma(n)$ ensuring computability within budget.

For Anson's two specific points: the "more powerful reasoner" is really just the definition of $R$ as total cumulative cost plus the assumption that $\mathcal{C}_A$ can compute $R(F(n))$—that's what gives $A$ the power to settle contracts. And the "end about $e$" is the condition $e(n) \ge R(n)$ itself, which forces $Q_A$ to be $\mathcal{C}_H$-enumerable, with the consequence following directly from the counting argument. I'm deciding whether this should be strict inequality or just $\ge$ to keep the conditions as tight as possible.

There's also a subtle but important point about $\sigma(n)$: the current condition $\sigma(n) > F(n)$ only ensures $Y_n$ is defined by stage $\sigma(n)$, but for $D_A$ to be computable within budget, I actually need $\sigma(n) \ge R(F(n))$—dominating the cost, not just the stage. This is a genuine tightening of what's needed. The two conditions then form a matched pair: $e(n) \ge R(n)$ on the quote side and $\sigma(n) \ge R(F(n))$ on the settlement side, with the ordering $R(n) \le e(n) < F(n) < \sigma(n)$ all compatible since the schedules are free to grow.

</details>

First, pin down what $R$ now denotes, since both statements lean on it:

Let $R(t)$ be the total cost of simulating the coupled construction through stage $t$ — producing $A_1,\dots,A_t$ and $H^+_1,\dots,H^+_t$ together with the deductive processes feeding them. It's nondecreasing, and well-defined because the recursion is well-founded (every stage-$t$ object depends only on stages below $t$). The two objects you care about sit at known stages: the quote $a_n=A_n(C_n)$ is a stage-$n$ object, so computing it costs $R(n)$ (up to polynomial overhead for reading off the affine combination); the settlement $Y_n=H^+_{F(n)}(P^{(n)})$ is a stage-$F(n)$ object, so computing it costs $R(F(n))$. That's the whole trick to using one function — $a_n$ and $Y_n$ are the same simulation read at two different stages.

**Statement in "A more powerful reasoner."**

> We assume $\mathcal{C}_A$ contains the map $n\mapsto R(F(n))$.

That is the entire power assumption. Gloss to include: since $Y_n$ is read off the stage-$F(n)$ state of the simulation, this says exactly that $A$ can afford to compute the settlements its own deductive process $D_A$ requires; in particular $n\mapsto Y_n$ is $\mathcal{C}_A$-computable. You can delete the standalone "$n\mapsto Y_n$ is $\mathcal{C}_A$-computable" sentence now — it's a consequence, not a separate hypothesis.

This pairs with a condition on $\sigma$, and here's a correction to your current text (≈80% this is the right tightening): for $D_A$ to be computable *on schedule* you want

> $\sigma(n)\ge R(F(n))$,

not merely $\sigma(n)>F(n)$. The latter only makes $Y_n$ *defined* by stage $\sigma(n)$; computability of $D_A^{\sigma(n)}$ within budget needs $\sigma(n)$ to dominate the *cost* $R(F(n))$, not just clear the stage $F(n)$. Since $R(F(n))\ge F(n)$, the new condition subsumes the old, so it's a strict strengthening with no cost to consistency.

**Statement at the end (about $e$).**

> We require $e(n)\ge R(n)$.

A quote is published no earlier than the stage by which the simulation producing it has finished. The consequence — which is what 4.7.2 consumes:

> Because $e(n)\ge R(n)$, every quote in $Q_A^{(t)}$ — those with $e(i)<t$ — satisfies $R(i)\le e(i)<t$, so its full production cost lies below $t$. As $e$ is strictly increasing, fewer than $t$ indices satisfy $e(i)<t$, so recomputing the whole conjunction from scratch costs at most $\sum_{i:\,e(i)<t}R(i)<t^2$ — polynomial in $t$. With $\mathcal{C}_H$ closed under polynomial overhead, $t\mapsto Q_A^{(t)}$ is efficiently computable relative to $\mathcal{C}_H$, and closure under conditioning applies.

So the two statements are now a matched pair, both reading "publish/settle only after the producing simulation has run":

- emission (quote is a stage-$n$ object): $e(n)\ge R(n)$
- settlement (settlement is a stage-$F(n)$ object): $\sigma(n)\ge R(F(n))$

with the ordering $e(n)<F(n)<\sigma(n)$ dropping $F$ in between. All compatible, since the schedules are free to grow: $R(n)\le e(n)<F(n)<\sigma(n)$, and $\sigma(n)\ge R(F(n))\ge F(n)$ holds automatically. The single $R$ carries both because it's evaluated at $n$ for the quote and at $F(n)$ for the settlement — no second cost function needed.


## Human
*2026-06-09 01:44 UTC*

What is that really necessary i feel like i'm trying to pin this down but more conditions appear


## Assistant
*2026-06-09 01:47 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson's pushing back because I keep layering on extra conditions when he's trying to strip things down to what actually matters. He's right—I added $\sigma(n) \ge R(F(n))$ on top of the core constraint, and now he's questioning whether that's even necessary or if I'm just overcomplicating the picture. I need to be honest about whether that condition is load-bearing or just noise.

The real question is what computability of $D_A$ actually demands. For the construction to work, $D_A$ needs to be a computable function that maps each time $t$ to the corresponding deductive state $D_A^t$. But here's what I was conflating: the construction doesn't require $D_A$ to be computable *within some time budget*—it just needs to be total and computable. The logical inductor itself is computable, and the traders operate within their own constraints, but $D_A$ as a deductive process doesn't inherit a time bound from that. So the market itself just needs to be computable, not efficiently computable — that's a key distinction. The traders are the ones facing the efficiency constraint. For universal inductors and conditioning, the real question is whether the conditioned market $H^+$ still satisfies the inductor criterion against efficiently computable traders, which depends on the computational budget available to $D_A$ when it needs to simulate $H^+$.

The mutual recursion between $D_A$, $Y_n$, and the conditioning on $A$'s quotes is well-founded because each stage depends only on earlier stages, so everything terminates and is computable without needing an explicit budget condition. But when $H^+$ is conditioned on $Q_A$, closure under conditioning requires that the conditioning sequence itself be efficiently computable relative to $\mathcal{C}_H$ — that's where the cost bound $e(n) \ge R(n)$ becomes necessary.

Now I'm questioning whether the settlement side actually needs a budget condition at all. $A$ just needs to be a computable inductor over $D_A$ against $\mathcal{C}_A$, which means $D_A$ only needs to be computable (not efficiently computable), and well-foundedness already guarantees that. The ordering $\sigma(n) > F(n)$ ensures the values are available when needed, but that's still just about well-foundedness, not about computational cost. The real question is whether $A$ itself needs to be efficient, and if so, whether the $\mathcal{C}_A$ assumption about containing $n \mapsto R(F(n))$ is there to ensure $A$ can eventually resolve its deferred bets.

Actually, I think I'm conflating two different roles. The $\mathcal{C}_A$ assumption isn't really about $A$'s efficiency — it's about what traders can do. For the calibration theorem to work, there needs to be a trader in $\mathcal{C}_A$ that can exploit any miscalibration by $A$. That trader needs to compute the settlement $Y_n$ or at least understand the contract behavior well enough to profit from $A$'s errors. So $\mathcal{C}_A$ needs to be powerful enough to contain the traders that enforce calibration, not necessarily to make $A$ itself efficient.

But then the $\sigma(n) \ge R(F(n))$ condition I added might actually be redundant — since $D_A$ only needs to be computable (not efficiently), well-foundedness alone should guarantee that. The real constraint is probably just on the $H^+$ side of things. I'm questioning whether the market itself needs to be efficiently computable in the logical inductor framework, or just the traders. The definition requires a computable sequence of belief states, but I'm uncertain whether that extends to efficient computability for the market itself, or if that's only a requirement on the traders.

The key issue is understanding why the assumption that $R(F(n)) \in \mathcal{C}_A$ is necessary — the draft claims it's needed so deferred bets can eventually resolve deductively, but I'm trying to pin down whether this is actually essential or if it's addressing something more specific about the conditioning mechanism. doesn't actually need to compute $R(F(n))$ either — the trader just needs to identify when $a_n$ diverges from the settlement value and execute the arbitrage, which only requires knowing the contract structure and timing, both of which are $\mathcal{C}_A$-computable. So the real load-bearing constraint is just the emission lag condition on $H^+$, and the $R(F(n)) \in \mathcal{C}_A$ requirement might only be necessary for the calibration proof itself, not for the existence of the market. I'm realizing I'm not actually sure what the $\mathcal{C}_A \ni R(F(n))$ condition is doing in the proof, and I should be honest about that uncertainty rather than confidently asserting something I'm not confident about. The conditions keep appearing because I've been conflating different requirements, and I should give a clearer answer about what's actually necessary versus what I'm uncertain about. computable in a way that affects the reflection results? The key insight is that $H$ doesn't need to compute the quotes themselves — it just reads them from $Q_A$ and conditions on them. So the question becomes whether $D_A$ needs $R(F(n))$ to be $\mathcal{C}_A$-computable for the calibration enforcement to work, or if the schedules being $\mathcal{C}_A$-computable is sufficient.

I think the real constraint is interpretive: if $A$ is supposed to be a $\mathcal{C}_A$-bounded reasoner, then its deductive process — including simulating $H^+$ and settling trades — should stay within $\mathcal{C}_A$'s power. Otherwise the narrative breaks. But there's also a practical angle: if $H$ or some other trader needs to compute $A$'s prices, they'd need $A$'s computation to be $\mathcal{C}_A$-bounded so it's feasible for them to simulate.

Now, for $H^+$ to read the quotes at cost within $\mathcal{C}_H$, it has to recompute them... For $Q_A$ to be $\mathcal{C}_H$-e.c., $H^+$ needs to determine at stage $t$ which indices $i$ satisfy $e(i) < t$, which means $e$ itself must be $\mathcal{C}_H$-computable. The current draft assumes $e$ is $\mathcal{C}_A$-computable, but if $\mathcal{C}_A$ is strictly larger than $\mathcal{C}_H$, that's not sufficient. However, for simple schedules like $2^n$, computing $e(i)$ is actually cheap — the output is large but the computation time is polynomial in $i$, so checking $e(i) < t$ is feasible within $\mathcal{C}_H$'s constraints.

Now I'm stepping back to focus on what really matters for Anson: he's frustrated by proliferating conditions, and I should validate that frustration and clarify the minimal set. The key insight is that there's exactly one load-bearing budget condition — the one ensuring $Q_A$ is e.c. relative to $\mathcal{C}_H$ — because only the $H^+$ conditioning requires efficient computability. The $A$/settlement side needs only the ordering $F < \sigma$ plus plain computability, which well-foundedness already guarantees, so the condition $\sigma \ge R(F(n))$ is actually unnecessary and should be dropped.

But I'm uncertain about what $\mathcal{C}_A \ni R(F(n))$ is actually buying, and I should flag that Anson should check this against the downstream theorems (calibration, reflection) to see what they actually use. I'm also reconsidering whether the $A$-side really needs only computability or if it requires efficient computability — specifically, whether a universal inductor against $\mathcal{C}_A$ requires the deductive process $D_A$ to be efficiently computable, and I'm trying to recall what the logical inductor paper actually requires.

There's a distinction between a computable deductive process and an efficiently computable conditioning sequence that matters here, and I'm only about 70% confident that $D_A$ needs only the former rather than the latter. If $A$ as a universal inductor actually requires efficient computability, then you'd need $\sigma \ge R(F(n))$ symmetrically, which would undermine the suggestion to drop it. The real issue was that I wasn't clear on which computational standard applies to $A$'s side, so I defaulted to the stricter one and kept piling on conditions. The minimal setup is just the ordering $e < F < \sigma$ for well-foundedness, plus the single efficiency requirement on $e$ itself ($Q_A$ is $\mathcal{C}_H$-e.c., witnessed by $e \ge R$). The power assumption "$\mathcal{C}_A \ni R(F(n))$" stays as the statement that $A$ is capable enough to make $Y_n$ computable, but it's not a scheduling constraint—it doesn't force an inequality on $\sigma$. I should also acknowledge that his sense of chasing a moving target is a real signal the framing has a gap, and naming the conflation of standards is the useful fix rather than over-apologizing.

</details>

No — and you're right to push, because conditions multiplying is a symptom of a leak in the framing, not the territory actually getting more complicated. The leak is that I was applying one computability standard to two places that don't both need it.

The asymmetry is the whole resolution:

- **$H^+$'s conditioning needs *efficient* computability.** 4.7.2 demands $t \mapsto Q_A^{(t)}$ be e.c. relative to $\mathcal{C}_H$. Efficiency is a budget claim, so it genuinely requires a growth condition — that's the one place $e \ge R$ earns its keep, as the witness for "$Q_A$ is e.c."
- **$A$'s side needs only plain computability.** $D_A$ has to be a *computable* deductive process for $A$ to be a valid inductor — not an efficiently computable one. And plain computability of $t \mapsto D_A^t$ is already handed to you by well-foundedness: every $Y_n$ it references is a strictly-earlier-stage object, hence computable, full stop. The only job the schedule has on this side is to *order* the dependencies — $F(n) < \sigma(n)$, so the value exists before it's read. No cost-domination.

So $\sigma(n) \ge R(F(n))$ is **not** necessary — drop it. I imported the efficiency standard onto the settlement side, where only ordering plus plain computability live, and that's exactly the spurious condition you felt sprouting. $\sigma$ carries no cost term; just $F(n) < \sigma(n)$.

Pinned-down minimal set:

1. **Ordering:** $e(n) < F(n) < \sigma(n)$. Pure well-foundedness — each quantity computed before it's read. No costs anywhere.
2. **One efficiency clause:** $t \mapsto Q_A^{(t)}$ is efficiently computable relative to $\mathcal{C}_H$, witnessed by $e \ge R$ (the quantitative content from last turn). This is the *only* budget condition in the construction.
3. **Power assumption** (not a schedule inequality): $\mathcal{C}_A \ni n \mapsto R(F(n))$ — "$A$ can afford the simulation that defines its settlements." A one-time statement about $\mathcal{C}_A$, not an inequality between schedules. Its real job is to make $R$ a tame, $\mathcal{C}_A$-bounded function so that a dominating $e$ in (2) exists at all.

The one thing I'd verify before fully trusting "drop it" (≈70% as stated): that $A$-as-universal-inductor needs only a *computable* $D_A$, not an *efficiently computable* one. If Diffractor's conditioning for the UI actually requires the deductive process to be e.c., then the settlement side becomes symmetric to the emission side, you'd need $\sigma \ge R(F(n))$ after all, and the conditions weren't spurious — there really are two of them. That definitional fork is what decides between "one budget condition" and "two symmetric ones," and it lives in the UI construction, not anywhere I'd assert from memory. Confirm that single fact and you'll know which world you're in.


## Human
*2026-06-09 02:03 UTC*

<details>
<summary>📎 Attachment: pasted content (14355 bytes)</summary>

```
\documentclass{article}
\usepackage{graphicx} % Required for inserting images
\usepackage{url}
\usepackage{hyperref}
\usepackage{titlesec}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{enumitem}
\usepackage{amsmath}
\usepackage{amsthm}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\DeclareMathOperator*{\argmin}{arg\,min}



\titleformat*{\section}{\LARGE\bfseries}
\titleformat*{\subsection}{\Large\bfseries}
\titleformat*{\subsubsection}{\large\bfseries}
\titleformat*{\paragraph}{\large\bfseries}
\titleformat*{\subparagraph}{\small\bfseries}

\title{Trust Between Universal Inductors}
\date{}
\begin{document}
\maketitle
\begin{sloppypar}

\subsection*{Motivation}

% Let $H$ be a \emph{universal inductor}, in the sense of a \href{https://arxiv.org/abs/1609.03543}{logical inductor} conditioned on bitstrings.\footnote{The basic construction is given in
% \href{https://www.lesswrong.com/posts/FnH2G832sWMySptp5}{this explanation of universal inductors} by Diffractor.} $H$ should be thought of as a bounded reasoner that represents evolving human opinions over time, constructed by conditioning on bitstring representations of empirical observations and proven theorems. Then, suppose another universal inductor $A$ is constructed as a strictly more computationally powerful reasoner that is set up to predict the future states of the human reasoner using good feedback about what those future states turn out to be. We then construct a new inductor $H^+$ by conditioning $H$ further on bitstrings representing outputs of $A$. This may be thought of as an attempt to leverage an AI's additional computational power to gain information about humanity's own trusted future beliefs. The following construction makes this setup concrete. [Summary of findings after finishing]


\subsection*{Construction}

\paragraph{Base reasoner.}
Take a propositional language $\mathcal{L}$ with sentence set $\mathcal{S}$ along with a
theory $\Gamma$ and a $\Gamma$-complete computable deductive process
$D_H=(D_H^t)_{t\ge1}$. Let $\mathcal{C}_H$ be a complexity class closed under
polynomial overhead \footnote{explanation of polynomial overhead} and let $H=(H_1,H_2,\ldots)$ be a \emph{universal inductor} over $D_H$ against $\mathcal{C}_H$. In other words, take a logical inductor $U$ over the empty deductive process with traders in $\mathcal{C}_H$, and then use Bayesian conditioning to define $H = U \mid D_H$. See \href{https://www.lesswrong.com/posts/FnH2G832sWMySptp5}{Diffractor's explanation} for reference on the fundamental details of the universal inductor construction. $H$ is a market satisfying the logical induction
criterion against traders in $\mathcal{C}_H$. Each stage $H_t$ is a full probability measure over the worlds of $\mathcal{L}$, concentrated on the worlds propositionally consistent with $D_H^t$. Existence of such a
measure-valued inductor over an arbitrary computable deductive process is Lemma~\ref{lem:existence}.

\paragraph{Propositions and deferral.}
Choose a strictly increasing, $\mathcal{C}_H$-computable ``deferral" function
$F:\mathbb{N}^+\to\mathbb{N}^+$ with $F(n)>n+1$. Consider an effective enumeration
$P^{(0)},P^{(1)},\ldots$ of $\mathcal{S}$ where $P^{(n)}$ to be some $n$-th proposition of interest.

\paragraph{Threshold symbols.}
For each $n\ge1$ and $1\le k\le n$ introduce two fresh propositional symbols:
\begin{itemize}
  \item $\alpha_{n,k}$ which can be read as ``the contract for $P^{(n)}$ deferred to $F(n)$ has value at least $k/n$"
  \item $\beta_{n,k}$ which can be read as ``$A$'s published quote for that contract is at least $k/n$."
\end{itemize}
 Let $\mathcal{L}^\alpha:=\mathcal{L}\cup\{\alpha_{n,k}\}$ and
$\mathcal{L}^\beta:=\mathcal{L}\cup\{\beta_{n,k}\}$, with sentence sets
$\mathcal{S}^\alpha$ and $\mathcal{S}^\beta$ respectively, each extending $\mathcal{S}$. The $\alpha$ symbols allow $A$ to price
the future credences of $H^+$ while the $\beta$ symbols
encode $A$'s outputs for $H^+$ to condition on. Because each of these sets of symbols represents threshold sentences, that is claims that a value is at least $\frac{k}{n}$, they respect monotonicity axioms:
\[
\{\alpha_{n,k}\to\alpha_{n,k-1}\}\quad\text{and}\quad
\{\beta_{n,k}\to\beta_{n,k-1}\}\qquad(n\ge1,\ 2\le k\le n).
\]
Note that the readings of the symbols given above are glosses for our metalanguage, and are only baked into the inductors in the form of the monotonicity axioms. For a world $W$ consistent with these axioms each truth-set is an initial
segment, so we can define values as proportions of true threshold sentences:
\[
\mathrm{val}^\alpha_W(n):=\tfrac1n\#\{k:W(\alpha_{n,k})=1\},
\qquad
\mathrm{val}^\beta_W(n):=\tfrac1n\#\{k:W(\beta_{n,k})=1\}
\]
each taking the form $m/n$ for an integer $0\le m\le n$. Using these values, the addition of the threshold symbols to the language allows for the representation of a real-valued unknown rounded to the nearest $\frac{1}{n}$.

\paragraph{Contracts and quotes.}
Define the deferred contract $C_n$ and the quote readout $Q_n$ as affine combinations
\[
C_n:=\tfrac1n\sum_{k=1}^n\alpha_{n,k},
\qquad
Q_n:=\tfrac1n\sum_{k=1}^n\beta_{n,k},
\]
so $W(C_n)=\mathrm{val}^\alpha_W(n)$ and $W(Q_n)=\mathrm{val}^\beta_W(n)$
for consistent worlds $W$. Note that both $C_n$ and $Q_n$ are affine combinations of symbols
already in the markets used for convenience rather than separately traded objects. Write
\[
a_n:=A_n(C_n)=\tfrac1n\sum_k A_n(\alpha_{n,k})\in\mathbb{Q}\cap[0,1]
\]
for $A$'s published quote on the deferred contract and
\[
Y_n:=H^+_{F(n)}(P^{(n)})
\]
for the eventual credence of $H^+$ that the contract uses for settlement. 

\paragraph{A more powerful reasoner.}
Let $\mathcal{C}_A\supseteq\mathcal{C}_H$ be a complexity class closed under
polynomial overhead for which the map $n\mapsto Y_n$ is $\mathcal{C}_A$-computable
in the coupled system. More precisely, given $n$, an implementation in $\mathcal{C}_A$ can simulate the mutual construction up to stage $F(n)$ and output $Y_n$. Writing $R(t)$ for the total runtime of the
implementation of $H^+$, we assume $\mathcal{C}_A$ contains $n\mapsto R(F(n))$. This is a significant idealizing assumption about the computational power of $A$ needed so that its deferred bets can eventually deductively resolve. Note, though, that the simulation need not be practically implementable by the traders.

\paragraph{Timing.}
Define two new scheduling functions: a ``settlement" function $\sigma(n)$ representing the stage at which $Y_n$ is computed by $A$, causing the markets for $C_n$ to resolve and an ``emission" function $e(n)$ representing the stage by which $A$'s quote $a_n$ has been computed and published. Assume both of these functions are $\mathcal{C}_A$-computable and strictly increasing from $\mathbb{N}^+$ to $\mathbb{N}^+$. Recall that $F(n)$ is the deferral function, used as the stage of $H^+$'s prices referred to by the contracts. Assume that these schedules are related by the following inequality:

\[
e(n)<F(n)<\sigma(n)
\]

In other words, quotes are always published before the stage that they refer to, which is before the stage at which the contracts are settled.  

\paragraph{The inductor $A$.}
Let's now define $A$ and $H^+$ as two inductors that can see each other, constructed via recursion. For $0\le m\le n$ write the settling profile 
\[
\mathcal{A}_n(m):=\{\alpha_{n,k}:k\le m\}\cup\{\neg\alpha_{n,k}:k>m\}
\]
which should be read as ``$C_n$ is approximately equal to $\frac{m}{n}$.'' Let
\[
m_n^*:=\argmin_{0\le m\le n}\left|\tfrac mn-Y_n\right|
\]
with ties going to the lower $m$, i.e. the best approximation of the real-valued settlement $Y_n$. We therefore have
\[
\left|\tfrac{m_n^*}{n}-Y_n\right|\le\tfrac1{2n}
\]
because the grid $\{0,\frac1n,\frac2n,\ldots,1\}$ has spacing $\frac1n$, so every value in $[0,1]$ is within $\frac1{2n}$ of some grid point. Define the computable deductive process
$D_A$ over $\mathcal{L}^\alpha$ as one that, for each time step $t$, $D_A^t$ includes the $\alpha$-monotonicity axioms for $n\le t$ and the profile $\mathcal{A}_n(m_n^*)$ for each $n$ with $\sigma(n)\le t$.
Each $D_A^t$ is finite (axiom schemata and settlement profiles are finite at any finite stage) and consistent (distinct $n$ touch disjoint symbols for both axioms and profiles, settlements are initial segments respecting monotonicity). $D_A$ is
computable as part of the mutual construction, since $\sigma(n)>F(n)$ makes $Y_n$ available
before its settlement is required by $D_A$. Let $A=(A_1,A_2,\ldots)$ be a universal
inductor over $D_A$ against $\mathcal{C}_A$.

\paragraph{The inductor $H^+$.}
Similarly, define the quote profile
\[
\mathcal{B}_n(\ell):=\{\beta_{n,k}:k\le\ell\}\cup\{\neg\beta_{n,k}:k>\ell\}
\]
as a set of atoms representing a posted quote and let
\[
\ell_n^*:=\argmin_{0\le\ell\le n}\left|\tfrac\ell n-a_n\right|
\]
with ties going to the lower $\ell$. Then $\mathcal{B}_n(\ell_n^*)$ is the rounding of $A$'s quote to a grid with spacing $\frac{1}{n}$. Take the base inductor $H$ to be defined over the extended language $\mathcal{L}^\beta$, with the $\beta$-monotonicity axioms adjoined to $\Gamma$, so that it assigns credences to $A$'s quote atoms. Writing
\[
Q_A^{(t)}:=\bigwedge_{i\,:\,e(i)<t}\mathcal{B}_i(\ell_i^*)
\]
for the conjunction of those quote profiles \emph{published by time $t$}, define the augmented human inductor by conditioning,
\[
H^+:=H\mid Q_A,\qquad H^+_t(\cdot):=H_t\!\left(\,\cdot\mid Q_A^{(t)}\right).
\]

[REPLACE THIS PARAGRAPH] The sequence $t\mapsto Q_A^{(t)}$ is an efficiently computable deductive process: only the finitely many profiles with $e(i)<t$ appear by stage $t$, and because $e$ dominates each quote's production cost, all of them can be recomputed within $\mathcal{C}_H$'s budget as a function of $t$. By closure under conditioning (Garrabrant et al., Theorem 4.7.2), applied to this efficiently computable conditioning sequence, $H^+$ is again a universal inductor against traders in $\mathcal{C}_H$, now over $\Gamma$ together with the published quote profiles.

\paragraph{An assumption about cost}
In order for the conditioning described above to be legitimate, the sequence $t\mapsto Q_A^{(t)}$ must be efficiently computable. To ensure this, suppose that $e(n) \ge R(n)$ where 

\subsection*{Results}
\paragraph{Existence and well-foundedness.}
The four sequences $(A_t),(H^+_t),(D_A^t),(Q_A^{(t)})$ are defined by one
recursion on $t$, and the schedule $e(n)<F(n)<\sigma(n)$ is exactly what makes the
dependencies strictly decreasing. $D_A^t$ depends on $H^+$ through values $H^+_{F(i)}$ for $i$ with $\sigma(i)\le t$, hence through stages $F(i)<\sigma(i)\le t$. The conditioning event $Q_A^{(t)}$ depends on $A$ only through quotes $a_i$ with $e(i)<t$, each of which is in turn determined by settlements that have already resolved, hence by stages strictly below $e(i)<t$. Neither market's stage-$t$ pricing
references the other's stage-$t$ pricing, so every stage-$t$ object is determined
by data from stages strictly below $t$. Lemma~\ref{lem:existence} carries out the recursion and
verifies the two markets satisfy their logical induction criteria.

\begin{lemma}[Existence]\label{lem:existence} Assume the computational idealization in the construction: the map
\[
n\mapsto Y_n:=H^+_{F(n)}(P^{(n)})
\]
is $\mathcal{C}_A$-computable in the mutually defined system, and
$e(n)<F(n)<\sigma(n)$ are $\mathcal{C}_A$-computable schedules by which $A$'s quote
on contract $n$ is published and $Y_n$ is computed, with $e$ dominating each
quote's production cost. Then the recursive construction of
\[
(A_t),\quad (H^+_t),\quad (D_A^t),\quad (Q_A^{(t)})
\]
is well-founded. Moreover, each $D_A^t$ is finite and
propositionally consistent, the conditioning sequence $t\mapsto Q_A^{(t)}$ is
efficiently computable and each $Q_A^{(t)}$ is consistent with $\Gamma$,
$A$ is a logical inductor over $D_A$ against
$\mathcal{C}_A$, and $H^+=H\mid Q_A$ is a logical inductor against
$\mathcal{C}_H$ by closure under conditioning (Garrabrant et al., Theorem 4.7.2)
applied to this efficiently computable sequence.
\end{lemma}
\paragraph{Limit calibration of $A$ to future $H^+$.} Placeholder intro
\begin{theorem}[Calibration] In the coupled system above,\[
a_n-Y_n\to 0.
\]
Equivalently,
\[
A_n(C_n)-H^+_{F(n)}(P^{(n)})\to 0.
\] 
\end{theorem}
\paragraph{Reflection principles for $H^+$ about $A$.} 
For a rational tolerance $\delta>0$ and a real-valued expression $X\in[0,1]$, define the one-sided continuous indicator
\[
\operatorname{Ind}_{\delta}(X>p) :=
\begin{cases}
0 & X\le p,\\[2pt]
\dfrac{X-p}{\delta} & p<X<p+\delta,\\[4pt]
1 & X\ge p+\delta.
\end{cases}
\]
Define $\operatorname{Ind}_{\delta}(X<p)$ analogously, i.e. with value 0 for $X$ at least $p$, value 1 for $X$ more than $\delta$ less than $p$, and linearly interpolated between 0 and 1 for $X$ at most $\delta$ less than $p$.

Recall that the quote readout (i.e. the price for the contract $C_n$ rounded to the $\frac{1}{n}$ grid) is defined as \[Q_n:=\frac1n\sum_{k=1}^n\beta_{n,k}\]

We use the standard extension of logical induction from sentence-prices to expectations of bounded finite logically uncertain variables (LUVs).\footnote{Definition 4.8.1 of Garrabrant et al.} In particular, any bounded rational-valued function of finitely many sentences can be expanded as a finite affine combination of conjunctions over their truth profiles, priced by linearity. The variables appearing below, such as $1(P^{(n)})\cdot \operatorname{Ind}_{\delta}(Q_n>p_n)$, depend only on the finite family of atoms $\{\beta_{n,k}:1\le k\le n\}$ together with the sentence $P^{(n)}$, and so are legitimate bounded finite LUVs.

\begin{theorem}[Transferred reflection]\label{thm:external-trust}
Let $(p_n)$ be a $\mathcal{C}_H$-computable sequence of rational probabilities in
$[0,1]$, and let $\delta>0$ be rational. Write $1(P^{(n)})$ for the $[0,1]$-LUV representing the truth value of $P^{(n)}$. Then
\[
H^+_n\!\left(
1(P^{(n)})\cdot \operatorname{Ind}_{\delta}(Q_n>p_n)
\right)
\gtrsim_n
p_n\,
H^+_n\!\left(
\operatorname{Ind}_{\delta}(Q_n>p_n)
\right).
\]
Similarly,
\[
H^+_n\!\left(
1(P^{(n)})\cdot \operatorname{Ind}_{\delta}(Q_n<p_n)
\right)
\lesssim_n
p_n\,
H^+_n\!\left(
\operatorname{Ind}_{\delta}(Q_n<p_n)
\right).
\]
\end{theorem}

% Nonconservativity / pull section to follow.

\end{sloppypar}
\end{document}
```

</details>

https://www.lesswrong.com/posts/FnH2G832sWMySptp5/what-are-universal-inductors-again

This is what I currently have, thoughts?


## Assistant
*2026-06-09 02:07 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson has sent over the updated draft along with a link to Diffractor's post on universal inductors, and he's looking for feedback. This is the perfect opportunity to nail down that key question from before—whether the universal inductor construction needs the conditioning deductive process to be efficiently computable or just computable in principle. That distinction was the critical fork point determining whether we need $\sigma \ge R(F(n))$, and now he's provided the primary source to settle it.

I should actually fetch and read that post rather than keep speculating. Beyond that, there are several concrete issues in the draft I need to flag: the "An assumption about cost" paragraph cuts off mid-sentence after "where" with nothing following, there's now redundancy with both the old [REPLACE THIS PARAGRAPH] and the new cost paragraph both trying to handle the conditioning-efficiency question, and $R$ appears to have been redefined in a way that conflicts with what we discussed last turn about it representing the total cost of the coupled construction.

Looking more carefully at the definitions, there's a real mismatch: $R(t)$ is defined as the runtime of $H^+$ alone, but when we use $e(n) \ge R(n)$ as the emission condition, we're comparing the quote's production cost (which involves running $A$ including its market and the $H^+$-simulations feeding into it) against just the cost of running $H^+$ to stage $n$. That's not the right comparison—$R(n)$ should represent the total cost of the coupled construction through stage $n$, not just the $H^+$ portion.

Either I need to redefine $R$ as the coupled-construction cost so it actually bounds the quote's production, or use a different symbol for the quote-production cost in the emission condition. The coupled definition from before seems cleanest. It's possible Anson meant $R$ to be the coupled cost and just phrased it loosely as "$H^+$ implementation," but I should flag this inconsistency.

Now looking at where he's defining $R(n)$ in the cost paragraph—he's asking me to complete the "where..." clause. The real question is whether the cost of running $A$ to stage $n$ is actually dominated by the cost of running $H^+$ to some stage, since running $A$ requires simulating $H^+$ for certain settlements plus $A$'s own market cost.

If I define $R$ as just the $H^+$ runtime, that captures the simulation part of quote production but misses $A$'s own market-making cost. When $H^+$ recomputes quotes at each stage, it has to run $A$'s market computation too, and if that cost isn't bounded by the polynomial bound, the whole argument breaks. So $R$ really needs to include the coupled construction cost—both $H^+$ and $A$'s market cost together—not just $H^+$ alone.

The good news is that redefining $R$ as coupled cost works for both sides: for the quote condition $e(n) \ge R(n)$, it captures everything needed to build the quote, and for the settlement side $R(F(n))$, the coupled cost to stage $F(n)$ is exactly the work needed to produce $Y_n$ since $H^+$ to $F(n)$ requires $A$ to all earlier stages anyway. So the coupled-cost definition is consistent across both the emission and settlement conditions.

But there's a muddled inconsistency in the "more powerful reasoner" paragraph itself: it says "simulate the mutual construction up to stage $F(n)$" (which is the coupled view) but then defines $R(t)$ as just the runtime of $H^+$ (which is $H^+$-only). I should clarify that $R(t)$ should be the runtime of simulating the entire mutual construction to stage $t$, not just the $H^+$ piece, to match the language already in the paragraph about simulating the mutual construction.

The Existence Lemma still has several issues: it says $e$ dominates each quote's production cost and that the schedules are $\mathcal{C}_A$-computable, but I need to check whether $\sigma$ actually needs a cost bound (which depends on whether UI conditioning requires efficiency or just computability). Also, for $Q_A$ to be e.c. relative to $\mathcal{C}_H$, the schedule $e$ itself needs to be $\mathcal{C}_H$-computable so that $H^+$ can determine which quotes are published by stage $t$ within budget—not just $\mathcal{C}_A$-computable. There's also duplication between the old [REPLACE THIS PARAGRAPH] section and the new "An assumption about cost" paragraph that needs reconciling. I should fetch Diffractor's post to settle the open question about whether the UI conditioning requires efficiency or just computability, since that directly determines whether $\sigma$ needs a cost bound.

</details>

<details>
<summary>⚙️ Tool call: <code>web_fetch</code></summary>

```json
{
  "url": "https://www.lesswrong.com/posts/FnH2G832sWMySptp5/what-are-universal-inductors-again"
}
```

</details>

<details>
<summary>⚙️ Tool result: <code>web_fetch</code></summary>

```
---
meta-baggage: sentry-environment=production,sentry-release=2b4014ec25bd6b08a299ef96552f96481d3bc12e,sentry-public_key=1ab1949fc8d04608b43132f37bb2a1b0,sentry-trace_id=bc5b310c505526de92b930fde98d6e56,sentry-org_id=195791
meta-sentry-trace: bc5b310c505526de92b930fde98d6e56-eb828fb43360e3d8
meta-viewport: width=device-width, initial-scale=1
---


x



## [LW](https://www.lesswrong.com/)

Login

                      What are Universal Inductors, Again? — LessWrong

[Frontpage](https://www.lesswrong.com/posts/5conQhfa4rgb4SaWx/site-guide-personal-blogposts-vs-frontpage-posts)

# 17

# [What are Universal Inductors, Again?](https://www.lesswrong.com/posts/FnH2G832sWMySptp5/what-are-universal-inductors-again)

by [Diffractor](https://www.lesswrong.com/users/diffractor?from=post_header)

7th Nov 2018

[AI Alignment Forum](https://alignmentforum.org/posts/FnH2G832sWMySptp5/what-are-universal-inductors-again)

8 min read

[0](#comments)

# 17

# Ω 7

[Attention Conservation Notice: This just recaps an old result and patches a hole in it, it doesn't contain substantially new ideas.]

Universal Inductors can be thought of as logical inductors over bitstrings, which are notable because they can act as a logical inductor over any theory you want (PA, ZFC, 2nd order arithmetic), by fixing some efficiently computable function from bits to sentences in the language of your theory, conditioning the universal inductor (which is a probability distribution over infinite bitstrings) on the bits which correspond to proven theorems, and reading out the probability of other bits/sentences from the resulting conditional distribution. This trick works by Theorem 4.7.2 in the logical induction paper, "Closure Under Conditioning", which shows that conditioning the probabilities of a logical inductor on a sequence of non-inconsistent sentences, yields a logical inductor over a deductive process where all the conditionals are true.

Also, since they are a probability distribution over infinite bitstrings, it makes sense to think about them as having a probability measure over worlds (assignments of statements to true or false, for all statements) at all finite stages, instead of just in the limit.

However, in Scott's [old post about universal inductors](https://agentfoundations.org/item?id=941), their construction was never described.
> Note that a Universal Inductor corresponds to a Logical Inductor, but the associated Logical Inductor will not have finite support, and so will be different from the one constructed in the paper. Never the less, Universal Inductors can be shown to exist using a similar construction.

This post will give that construction. To begin with, a Universal Inductor must fulfill the following two properties:

First, it must be a distribution over infinite bitstrings, such that  Pn(σ) is computable for all n and all σ which are finite bitstrings. This gives the probability that an infinite bitstring starts with σ as a prefix.

Second, the theory is one where the nth atomic statement is of the form "the nth bit in this infinite bitstring is a 1", and Pn induces a function from these statements to probabilities, and the sequence of probability assignments must form a logical inductor over the empty deductive process. (ie, the inductor never sees any evidence of the form "this bit is a 1", it just runs forever without getting any feedback.)

To begin with, the supertrader construction from Section 5 of the [logical induction paper](https://intelligence.org/files/LogicalInduction.pdf) is the exact same. Traders look at the prices of boolean combinations of atomic statements, and use them in continuous functions to buy or sell shares in boolean combinations of atomic statements.

The interesting part is the construction of the space that we'll be finding a fixed-point in. At timestep n, there is a most-distant bit that has ever appeared in a boolean combination of bits that a trader has bought/sold shares in, or looked at the price of. This is bit f(n). If we assign prices to all bitstrings of length f(n), then the probability of any finite bitstring that is longer can be given by just using the uniform distribution on bits after that point. This corresponds to assigning 50/50 probability to all statements which are too large to have thought about them yet. Therefore, our space of interest is the 2f(n)−1 dimensional simplex of probability distributions over all bitstrings of length f(n).

Given a point in this space, it is possible to read out the probability of any particular boolean combination of bits by just summing up the probability on all f(n)-length bitstrings that fit that constraint, so we can determine the prices that the supertrader sees.

We can also assign all bitstrings but one to a basis vector for the space, by letting the basis vector for a bitstring be the vector pointing to the corresponding vertex of the simplex from its center. A purchase of one share in a boolean combination corresponds to the vector comprised of the sum of basis vectors that correspond to the bitstrings fulfilling the conditions of the boolean. Note that a purchase of the one bitstring we left out can be re-expressed as a purchase of 1 dollar and selling a share of all other bitstrings.

As a simple case of this re-expression, when f(n)=2, P(00)=1−P(01)−P(10)−P(11) (because it has to be a probability distribution), so the price of the purchase is the same. And as for the purchase, both purchases have the feature that they are worth 1 dollar if the world is 00 and 0 dollars if the world is something different.

Therefore, given a point →x in the simplex, the net purchase and selling of a bunch of different boolean combinations of bits can be broken down into a whole bunch of vectors, which sum up to give a net trade vector →t, and finding the point in the simplex that's closest to →x+→t is the output of the continuous function that we can then find the fixed-point of.

Now, given a fixed-point in the interior of the simplex, →t=0, so there is no net trade. Given a fixed-point on the boundary of the simplex, →t can be interpreted as being composed entirely of selling shares with a price of 0, which obviously has 0 or negative value, although this is quite nontrivial to show. Once this is proved, it then immediately follows that this process described above is a Universal Inductor.

From here on, we will simply take care of this last theorem to be shown.

**Theorem 1:**

*For all price vectors →x′ on the boundary of the simplex that are a fixed-point, the vector →v representing the net trade can be interpreted as being composed entirely of 0's for all components in which →x′ has a nonzero entry, and nonpositive for all components in which →x′ has a 0 entry.*

First, some notation will be laid out.

k:=2f(n)−1, and it is the dimension of the space the simplex is in. →x denotes the vector of length k that is the fixed-point, and →x′ denotes the unique "canonical interpretation" of this vector as a vector of length k+1 with nonnegative coordinates that sum to 1, which gives the probabilities of the various bitstrings. Similarly, →t denotes the vector of length k which corresponds to the net trade. Given a constant c, →c will denote a vector with all coordinates being c, with the length clear from context. Given a vector →z and coordinate a, with za being the value of the a'th coordinate of →z, →za is the vector that is 0 in all coordinates except for a, and za at the a'th coordinate.

To begin, note that, given →t, there are multiple possible vectors →t′ of length k+1 which give the net purchase of shares. As an example of this, when k=1, [0,1] and [−1,0] both correspond to the same trade, because buying a share 0f σ=1 is equivalent to selling a share of σ=0. We will show that →t has an interpretation as a vector →t′ which is 0 everywhere →x′ is positive, and nonpositive everywhere →x′ is 0, because this corresponds to the net trade being interpretable as buying no shares, and only selling shares of bitstrings with a price of 0, which cannot lead to any gain no matter which bitstring is the true one.

Now, we will fix our basis vectors for the space. Because →x is on the boundary of the simplex, →x′ must have at least one 0 entry. Fix that vertex that corresponds to that bitstring as the origin of the coordinate system, and let the basis be comprised of the set of unit vectors that point from the center of the simplex to the vertices that correspond to all the other bitstrings. This spans the space that the simplex is embedded in. Annoyingly, this is not an orthonormal basis, so computing the dot product will be more complicated. The dot product between any two different basis vectors is −1k+1 (hat tip to Vanessa from MIRIxDiscord)

We can start by asking the question "In this basis, what condition on a vector →z corresponds to being inside the simplex?" The condition is that there exist a c∈[0,1] s.t. [0,→z]+→c has all entries in [0,1] and the entries sum up to 1. Note that for →x specifically, by the way we have defined the basis, c=0.

Also, the coordinates for →x can be broken down into coordinates where →x has 0 entries, and coordinates where →x has positive entries. Therefore, given an arbitrary vector →z, it can be expressed as [→z0,→z+], where →z0 is the vector of coordinates where →xis 0, and →x+ is the vector of coordinates where →x is positive.

The proof strategy that will be used is dividing into cases, and showing that for all cases besides the ones that prove the theorem, there is an "allowable perturbation vector" →ϵ s.t. →x+→ϵ lies in the simplex, and →x+→t is closer to →x+→ϵ than it is to →x. This implies that →x is not a fixed-point, because it isn't the point closest to →x+→t, but →x is a fixed-point, so we have a contradiction. Note that →x+→t being closer to →x+→ϵ than to →x is equivalent to ||→t||>||→t−→ϵ||, which can be rewritten as ⟨→t,→t⟩>⟨→t,→t⟩−2⟨→t,→ϵ⟩+⟨→ϵ,→ϵ⟩ which can be rewritten as 2⟨→t,→ϵ⟩>⟨→ϵ,→ϵ⟩. This last statement will be the proof target in the following cases.

**Case 1:** *There is some pair of coordinates a, b, s.t xb>0, and ta>tb.*

Let →ϵ be s.t. ϵa=ϵ, ϵb=−ϵ, and all other coordinates are 0. Note that since xa<1 (because xb>0 and →x adds up to 1), and →ϵ adds up to 0, then for sufficiently small ϵ, [0,→x+→ϵ] has all entries lie in [0,1] and sums up to 1. Then c can be taken as 0, to yield that →x+→ϵ lies in the simplex.

Define →t∗ as →t=→ta+→tb+→t∗. Note that →t∗ is 0 at coordinates a and b.

 2⟨→t,→ϵ⟩=2(⟨→ta,→ϵa⟩+⟨→ta,→ϵb⟩+⟨→tb,→ϵa⟩+⟨→tb,→ϵb⟩+⟨→t∗,→ϵa⟩+⟨→t∗,→ϵb⟩)

Rewriting ⟨→t∗,→ϵa⟩+⟨→t∗,→ϵb⟩ as ∑i≠a,b(⟨→ti,→ϵa⟩+⟨→ti,→ϵb⟩) , and using the fact that the dot product between any two different basis vectors of our space is −1k+1, ⟨→ti,→ϵa⟩+⟨→ti,→ϵb⟩=−1k+1(ϵti−ϵti)=0, so ⟨→t∗,→ϵa⟩+⟨→t∗,→ϵb⟩=0.

Now, 2(⟨→ta,→ϵa⟩+⟨→ta,→ϵb⟩+⟨→tb,→ϵa⟩+⟨→tb,→ϵb⟩)=2(ϵta−−1k+1ϵta+−1k+1ϵtb−ϵtb)

 =2ϵ(1+1k+1)(ta−tb) and because ta>tb, 2⟨→t,→ϵ⟩=cϵ for some positive c.

A similar analysis applies to show ⟨→ϵ,→ϵ⟩=4ϵ2(1+1k+1)=dϵ2 for some positive d, and for sufficiently small ϵ, we get our desired result that 2⟨→t,→ϵ⟩>⟨→ϵ,→ϵ⟩.

Now, the elimination of this case shows that →t+ must have all entries equal some constant c, while →t0 must have all entries ≤c if it is nonempty. This produces three more exhaustive cases.

**Case 2:** →t+=→c, c *is positive.*

In this case, note that a purchase of all shares but one can be reinterpreted as buying 0 of all shares but one, and selling the remaining share. Therefore, this trade is equivalent to selling c shares in the probability-zero bitstring that we took as the origin, buying 0 of all shares with positive probability, and selling a non-negative amount of all shares with 0 probability (because →t0 has all entries ≤c). Theorem 1 follows.

**Case 3:** →t+=→c, c *is* 0.

This case immediately proves Theorem 1, because →t+=0, and →t0 is 0 or negative on all entries.

**Case 4:** →t+=→c, c *is negative.*

If we can show that this case is impossible, we will be done. Let a be some coordinate where →x is positive.

Let →ϵ be s.t. →ϵa=−2ϵ, and all other coordinates are −ϵ. Let c=ϵ. [0,→x+→ϵ]+→c has all terms lie in [0,1] for sufficiently small ϵ, because the −ϵ is canceled out when →c is added, and the −2ϵ is taken out of a positive term. Because →c has k+1 entries, →c sums up to (k+1)ϵ. →x sums up to 1, and →ϵ sums up to −(k+1)ϵ, so the resulting vector sums up to 1, and →x+→ϵ lies in the simplex.

2⟨→t,→ϵ⟩=2(⟨→ta,→ϵa⟩+⟨→ta,→ϵ∗⟩+⟨→t∗,→ϵa⟩+⟨→t∗,→ϵ∗⟩)

Now we will break down the dot products.

 ⟨→t∗,→ϵ∗⟩=∑i,j≠a⟨→ti,→ϵj⟩=∑i≠a(⟨→ti,→ϵi⟩+∑j≠i,a⟨→ti,→ϵj⟩)

 =∑i≠a(−ϵvi+∑j≠i,a(−ϵvi−1k+1))=−ϵ∑i≠a(vi−k−2k+1vi)=−ϵ(1−k−2k+1)∑i≠avi

 =−3ϵk+1∑i≠avi

And for the next pair,

⟨→ta,→ϵ∗⟩+⟨→t∗,→ϵa⟩=∑i≠a⟨→ta,→ϵi⟩+∑i≠a⟨→ti,→ϵa⟩=∑i≠a(−ϵ−1k+1ta)+∑i≠a(−2ϵ−1k+1ti)

 =ϵk+1(k−1)ta+2ϵk+1∑i≠ati

Note that the second term combines with the term from the first dot product we looked at to yield the following equation

 ⟨→ta,→ϵ∗⟩+⟨→t∗,→ϵa⟩+⟨→t∗,→ϵ∗⟩=ϵk+1(k−1)ta−ϵk+1∑i≠ati

Finally, because ⟨→ta,→ϵa⟩=−2ϵva, by grouping terms and factoring out ϵk+1, we get

 2⟨→t,→ϵ⟩=2ϵk+1(−2(k+1)ta+(k−1)ta−∑i≠ati)=2ϵk+1(−(k+3)ta−∑i≠ati)

and, because all coordinates in →t are negative, this equals cϵ for some positive constant c. By the same proof path,

 ⟨→ϵ,→ϵ⟩=ϵk+1(−(k+3)(−2ϵ)−(k−1)(−ϵ))=ϵ2k+1(3k+5)=dϵ2

For some positive constant d. Therefore, for sufficiently small ϵ, 2⟨→t,→ϵ⟩>⟨→ϵ,→ϵ⟩ and Case 4 is impossible, and the theorem follows because only Case 2 and 3 are left.

[0Comments](#comments)

0



# 17

# Ω 7



New Comment



Submit

[Moderation Log](https://www.lesswrong.com/moderation)



[View more](https://www.lesswrong.com/users/diffractor)

Curated and popular this week



18[Alignment Newsletter #32](https://www.lesswrong.com/posts/uHE9b4HWQjuqnFYqP/alignment-newsletter-32)
```

</details>

<details>
<summary>💭 Thinking</summary>

 I'm looking at the Diffractor post to understand how universal inductors work with bitstrings. The key insight is that you can construct a universal inductor over bitstrings by using an efficiently computable function to map bits to sentences, then conditioning on the bits that correspond to proven theorems—this approach relies on a closure property from the logical induction paper that ensures conditioning preserves the inductor's properties. The key insight is that the conditioning sequence for $Q_A$ must be efficiently computable—a standard requirement throughout the logical inductor framework. The critical question then becomes whether constructing $A$ as a universal inductor over $D_A$ requires $D_A$ itself to be efficiently computable or merely computable. From the post's framing, a universal inductor conditions on the bits corresponding to proven theorems in the deductive process, but the thinking cuts off before clarifying whether that deductive process needs to be efficiently computable. So the conditioning sequence itself needs to be efficiently computable — that's what preserves the logical inductor property under conditioning, since the criterion relies on efficiently computable traders. This means both the conditioning on $D_A$ and on $Q_A$ require their respective sequences to be e.c., which fits the universal-inductor pattern.

That flips my earlier conclusion: the settlement side isn't asymmetric after all. Computing the settlements $Y_n$ has cost $R(F(n))$, and for $D_A$ to be efficiently computable, that cost must fit within the budget by the time it's needed — so $\sigma(n) \ge R(F(n))$ is actually required. The two cost conditions are genuine and symmetric, not spurious. in the deductive process $D_A$. So conditioning on $D_A$ via 4.7.2 requires $D_A$ itself to be efficiently computable relative to $\mathcal{C}_A$, which means each settlement must fit within the budget at time $t$ — forcing $\sigma(n) \ge R(F(n))$ to hold. This resolves the symmetry question: both sides of the condition are genuinely necessary, not spurious. The source confirms this through the conditioning mechanism, so my earlier hesitation was the optimistic reading, but the math closes that off. to verify the exact statement of 4.7.2 from the LI paper itself, though fetching the full 70+ page PDF might be impractical. The Diffractor recap I'm working from does frame the UI construction around conditioning via 4.7.2 and mentions the efficiently computable function mapping, which supports my ~80% confidence that the conditioning sequence must be efficiently computable, but I'd want to confirm the precise hypothesis to be fully rigorous about whether $\sigma \ge R(F(n))$ is actually required. The LI criterion requires the market to be computable, but for the universal inductor property to hold against $\mathcal{C}_A$ traders, the conditioning itself needs to be e.c. relative to $\mathcal{C}_A$ — otherwise the proof of 4.7.2 breaks down when trying to construct corresponding e.c. traders. So I'm now about 80-85% confident that $D_A$ must be e.c., which means $\sigma(n) \ge R(F(n))$ is necessary after all. The settlement and emission sides are symmetric, giving us two cost conditions, and I was wrong to suggest dropping this constraint. Now I need to reconsider whether $e$ being $\mathcal{C}_H$-computable is compatible with $Q_A$ being e.c. relative to $\mathcal{C}_H$...

Actually, there's an important asymmetry here: $e$ is read by $H^+$ (the weaker reasoner), so it must be $\mathcal{C}_H$-computable for the emission side to work, whereas $\sigma$ is used by $A$ (the stronger reasoner) and can be $\mathcal{C}_A$-computable. Since $F$ is already specified as $\mathcal{C}_H$-computable and is read by both reasoners, I should flag that $e$ needs to be $\mathcal{C}_H$-computable in the draft, not just $\mathcal{C}_A$-computable, because that's what matters for $Q_A$ being e.c. relative to $\mathcal{C}_H$.

Now looking at the concrete issues with the draft: the "An assumption about cost" paragraph cuts off mid-sentence where it says "where " without finishing the definition of $R$. There's also a mismatch in how $R$ is defined — the current version says it's the total runtime of $H^+$ alone, but for the emission condition $e(n) \ge R(n)$ to properly bound the quote's production cost, $R$ should capture the cost of running the coupled system (both $A$ and $H^+$ together) through stage $n$, not just $H^+$ in isolation, since $H^+$-only runtime undercounts $A$'s market cost.

The bigger discovery is that there's genuine symmetry here: the settlement side also needs a cost bound. Since $A = U \mid D_A$ requires $D_A$ to be efficiently computable (by section 4.7.2), we need $\sigma(n) \ge R(F(n))$ to ensure that, mirroring the emission side's $e(n) \ge R(n)$. These aren't separate concerns — they're a matched pair of cost conditions, which is the clean structure the source actually supports.

On the implementation details: $e$ is read by the weak reasoner $H^+$ to form quotes, so it needs to be $\mathcal{C}_H$-computable, not just $\mathcal{C}_A$-computable as the draft currently states. Meanwhile $\sigma$ is used by $A$, so $\mathcal{C}_A$-computable is appropriate there. Also noticing that two paragraphs now cover overlapping ground — the old one about $e$ dominating production costs and the new assumption section — so one should be removed.

The Existence Lemma needs updating too: it should specify that $e$ is $\mathcal{C}_H$-computable, include the symmetric settlement condition if the efficiency requirement holds, and make the cost conditions explicit in the hypothesis rather than treating them as afterthoughts. The lemma should also assert that $D_A$ is efficiently computable, not just finite and consistent.

I should also verify the well-foundedness section is still sound — it looks good, actually. The ordering $e < F < \sigma$ gives us well-foundedness for free, and the cost bounds $e \ge R(n)$, $\sigma \ge R(F(n))$ form a separate efficiency layer on top. So there's a clean two-layer structure: ordering ensures existence via well-foundedness, and cost conditions ensure the conditioning is efficiently computable for both inductors.

Now I need to organize my feedback for him. The source-check result is the most important finding and changes my earlier tentative conclusion, so I'll lead with that. Then the $R$-definition fix, followed by the concrete loose ends like the cut-off paragraph, duplication, the lemma, and the $e \in \mathcal{C}_H$ issue. I'll mark confidence levels on the load-bearing claims, especially around the efficiency requirement and $\sigma$ symmetry, and be clear about the scope of $R$. This warrants a moderately detailed response.

I'm double-checking the coupling argument: $R$ needs to account for both $H^+$'s runtime and $A$'s market-making cost to stage $i$, not just $H^+$ alone. If $R$ only captured $H^+$'s recomputation time, it would miss $A$'s fixed-point finding and trader execution costs, which could be substantial. So the emission condition $e(n) \ge R(n)$ wouldn't actually guarantee the total cost stays under budget. The coupling is necessary—around 85% confident on this.

For the settlement side, using coupled $R(F(n))$ captures the full cost of running both systems up to stage $F(n)$, which is exactly what the paragraph already claims: "simulate the mutual construction up to stage $F(n)$." The power assumption then says $A$ can afford this coupled simulation, making everything internally consistent. The only wording fix needed is replacing "total runtime of the implementation of $H^+$" with "total runtime of simulating the mutual construction" to match what's actually being described.

On whether to fetch the LI paper for the exact 4.7.2 statement: I'll go with the Diffractor recap plus structural reasoning as the primary assessment—that gets us to about 80% confidence—and explicitly flag the exact theorem statement in 1609.03543 as the definitive check. I can offer to pull it if he wants certainty, but given the PDF is huge and the section is buried deep, it's more responsible to present what we have now and let him decide if he needs that level of verification.

</details>

I pulled the Diffractor post, and it resolves last turn's fork — against the optimistic branch I leaned toward. Headline first:

**The settlement side needs a cost bound too; $\sigma(n)\ge R(F(n))$ is necessary after all (~80%).** Diffractor builds a UI as a bitstring inductor over the *empty* deductive process and then recovers the inductor-over-$\Gamma$ by *conditioning*, and he explicitly routes that through Theorem 4.7.2. Conditioning a logical inductor on a sequence of non-inconsistent sentences yields a logical inductor over a deductive process in which all those conditionals hold. So your $A = U \mid D_A$ is itself an instance of closure-under-conditioning, exactly like $H^+ = H \mid Q_A$ — meaning whatever efficiency 4.7.2 demands of a conditioning sequence, it demands of $D_A$, not just of $Q_A$. And to output $D_A^t$ you must know each settled $m_n^*$, i.e. compute $Y_n$ (cost $R(F(n))$); for that to stay within budget as a function of $t$ you need $\sigma(n)\ge R(F(n))$, mirroring $e(n)\ge R(n)$ on the quote side. My "drop it" last turn was the branch the source closes off.

The upside: this is *why it stopped feeling pin-down-able*, and the resting point is clean, not a proliferation. Two layers, nothing more:

- **Ordering** $e<F<\sigma$ → recursion is well-founded (everything exists).
- **Cost**, one bound per conditioning → each conditioning is efficiently computable (both inductors valid): $e(n)\ge R(n)$ makes $Q_A$ e.c. so $H^+$ is a UI against $\mathcal{C}_H$; $\sigma(n)\ge R(F(n))$ makes $D_A$ e.c. so $A$ is a UI against $\mathcal{C}_A$.

Two cost conditions *because there are two conditionings* — a matched pair, quote at stage $n$, settlement at stage $F(n)$. It doesn't grow past this. The definitive check is the exact hypothesis of 4.7.2 in 1609.03543; the recap is consistent with e.c.-conditioning but doesn't state it verbatim, so that's the one thing left to confirm.

Concrete issues in the draft:

1. **"An assumption about cost" is cut off** — it ends "$e(n)\ge R(n)$ where " with nothing after, so the definition of $R$ (the crux) never lands.

2. **$R$ is defined too narrowly.** "More powerful reasoner" says "$R(t)$ = total runtime of the implementation of $H^+$." But the quote's production cost is running *$A$* to stage $n$ — $A$'s own market plus the $H^+$-sims feeding $D_A^n$ — and $H^+$-only runtime misses $A$'s market cost, which $H^+$ pays when it recomputes $a_i$ for $Q_A^{(t)}$. Define $R(t)$ = runtime to simulate the *coupled* construction through stage $t$, which is also the phrase you already use ("simulate the mutual construction up to stage $F(n)$"). Then one monotone $R$ does both: $R(n)$ bounds the quote, $R(F(n))$ bounds the settlement. The edit is just "implementation of $H^+$" → "the coupled system."

3. **$e$ should be $\mathcal{C}_H$-computable, not $\mathcal{C}_A$.** $H^+$ reads $e$ to decide which quotes are in $Q_A^{(t)}$; if it can't evaluate the publication schedule within its own budget, $Q_A$ isn't e.c. relative to $\mathcal{C}_H$ however cheap the quotes are. $\sigma$ is used by $A$, so $\mathcal{C}_A$ is fine there. (Your $F$ is already $\mathcal{C}_H$-computable for the same reason.) Split them in Timing: $e\in\mathcal{C}_H$, $\sigma\in\mathcal{C}_A$.

4. **Duplication.** The old [REPLACE THIS PARAGRAPH] (still saying "$e$ dominates each quote's production cost") and the new cost paragraph now do the same job. Collapse: in the $H^+$ paragraph just assert "$Q_A$ is e.c., so 4.7.2 applies," and put the witness (both bounds + the $<t^2$ counting argument) in the cost paragraph or a footnote. Delete the bracketed one.

5. **Existence lemma is stale.** It still says "$e$ dominating each quote's production cost" and "$e<F<\sigma$ are $\mathcal{C}_A$-computable." Update for $e\in\mathcal{C}_H$, both cost bounds, and — given point 1 — it should assert $D_A$ is *efficiently* computable, not just "finite and consistent," since that's now a load-bearing hypothesis rather than a freebie.

Want me to pull the 4.7.2 statement from the LI paper before you commit to adding $\sigma\ge R(F(n))$? It's the one piece that would move my ~80% on the symmetric structure to near-certain.


## Human
*2026-06-09 02:15 UTC*

No but what if A is just a logical inductor none of the other stuff requires conditioning A


## Assistant
*2026-06-09 02:21 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson's raising a crucial point—if $A$ is just a logical inductor rather than a universal inductor constructed through conditioning, then my argument about the closure-under-conditioning machinery breaks down. That means the settlement-side cost bound I derived wouldn't necessarily follow from the conditioning framework I was relying on.

Let me trace through what $A$ actually needs to accomplish: it prices contracts over the language, acts as a logical inductor against the trader set, and feeds its settlements back into the deductive process. The calibration result should follow directly from $A$ being a logical inductor with appropriate settlement behavior. The key question is whether the standard logical induction construction—which works for any computable deductive process—is sufficient here, or if I need the stronger universal inductor machinery.

The universal inductor approach (via conditioning) is really a specific technique to ensure the inductor is also a full probability measure over worlds at each finite stage, which is what the base reasoner construction needs for reading off credences and computing LUV expectations. A vanilla logical inductor just gives you price sequences, not a measure-valued object, so the paper uses universal inductors to get that extra structure.

But looking at what $A$ actually does in the construction — it just prices the contracts $C_n$ as affine combinations of sentences — that's something a plain logical inductor can handle. The calibration property follows from the LI criterion and the deductive process settling the contracts, not from $A$ being measure-valued. So Anson's point stands: $A$ doesn't need to be a universal inductor, just a regular logical inductor over $D_A$.

Now I'm wondering whether $H$ and $H^+$ actually need the measure-valued property either. $H^+$ assigns credences to sentences like $P^{(n)}$, which is just pricing — a vanilla logical inductor does that. The reflection theorems involve expectations of products of indicators, but a logical inductor's LUV extension handles pricing bounded finite LUVs and their affine combinations, which includes the conjunctions needed for those products. So maybe even the reflection machinery doesn't force $H^+$ to be measure-valued.

But then I see the real constraint: $H^+ = H \mid Q_A$ — $H^+$ is defined by conditioning $H$ on the quote profiles. Conditioning in the Bayesian sense requires $H$ to be an actual measure, since you can't do measure-theoretic conditioning on a vanilla logical inductor at finite stages. That's why the universal inductor structure is essential — it gives you a measure at each stage so you can define $H^+$ through proper conditioning.

The crucial difference is that $A$ never gets conditioned on anything. It's built directly as a logical inductor over the deductive process $D_A$, with settlements entering through the deductive machinery itself rather than through conditioning. So $A$ doesn't need to be measure-valued or universal — it just needs to be a standard logical inductor over a computable deductive process.

This means the conditioning theorem requirement drops away entirely from $A$'s side, and I'm back to the original existence question: does the Garrabrant et al. construction guarantee a logical inductor exists over any computable deductive process, and what exactly are the computational requirements on $D_A$? So the key question is whether the deductive process needs to be merely computable or efficiently computable. The LI construction runs traders at each stage $n$ against the deductive state $D_n$, so computing $D_n$ is part of the per-stage work. While the market itself only needs to be computable, I'm fairly confident the deductive process is required to be efficiently computable in the paper's framework — though I'm not entirely certain of the exact definition statement.

Anson's suggestion to use a plain LI instead of a universal one doesn't actually sidestep the efficiently computable requirement; it just shifts the question from whether 4.7.2-conditioning needs it to whether the base LI existence theorem does. The real issue is whether the base existence theorem has a weaker requirement on deductive processes than 4.7.2 has on conditioning sequences.

But looking at both framings — universal inductor conditioned on sentences from $D_A$ versus plain LI constructed directly over $D_A$ — the deductive process enters at the same rate at each stage $t$. So the computational requirement should be equivalent in both cases. The question then becomes whether the calibration theorem itself, independent of construction details, imposes an efficiently computable requirement on $D_A$ for the downstream results to hold. The core question is what the existence theorem actually requires of $D_A$ for $A$ to be a logical inductor. Anson's point cuts deeper though — he's noting that my conditioning argument specifically relied on the universal-inductor construction, and if $A$ is just a direct logical inductor, that conditioning theorem doesn't apply and my symmetry argument breaks down. The real question is whether the conclusion about $\sigma \ge R(F(n))$ still holds based on what the base existence theorem demands of $D_A$. The key question boils down to whether Garrabrant et al.'s existence theorem requires the deductive process to be efficiently computable or just computable—that single detail determines whether $\sigma \ge R(F(n))$ resurfaces or truly disappears. Anson's point is genuinely sharp and deserves credit; I should also verify whether $A$ needs to be measure-valued anywhere else, particularly in the reflection theorems, which appear to involve only $H^+$ expectations and the $\beta$ atoms, not $A$ itself. I'm weighing whether to fetch the full Logical Induction paper to verify the exact definition of "deductive process" and settle the computability question once and for all. The paper is quite long, so there's a risk of truncation, but the definition should appear early in the framework section where I'd have the best chance of capturing it cleanly. The PDF at intelligence.org/files/LogicalInduction.pdf appeared in my search results, so I can fetch that. It's a large file with truncation risk, but pinning down the exact definition of a deductive process seems worth one attempt. If the PDF doesn't yield what I need, I'll work with what I've already found and give my best assessment based on the context I have.

I'm torn between two memories: either the deductive process just needs to be computable, or it needs to be efficiently computable (polynomial time) so that the e.c. traders can interface with it. I'm genuinely uncertain—maybe 55/45 on this—so fetching the paper to check the actual definition and the existence theorem requirements would help settle it. Though I should also consider whether there's a cleaner conceptual argument that would resolve this without needing to dig into the paper.

Even if the deductive process only needs to be computable for the existence theorem, there's a separate question about whether the calibration result holds. The key insight is that the $\mathcal{C}_A$ trader can exploit miscalibration through the settlement, which becomes available via $D_A$ at stage $\sigma(n)$ regardless of computational cost—the trader doesn't pay for computing $Y_n$, so calibration might work with just $D_A$ computable. But there's a real subtlety: for $A$ to be a logical inductor, the market itself must be computable, and computing $A_n$ requires $D_A^n$. If $D_A^n$ takes super-polynomial time because $Y_n$ is expensive, then $A$ is still computable (just slow), so $A$ still qualifies as a logical inductor by the definition.

The runtime bound applies only to traders, not to the market itself, so a plain logical inductor over a merely-computable $D_A$ works fine—meaning $\sigma \ge R(F(n))$ isn't needed for $A$'s existence or for calibration. The cost only matters where efficiency is required, and on the market's side, that's not necessary if $A$ is a plain logical inductor and the existence theorem only demands computable $D$. Now I'm checking whether the logical induction criterion itself requires the market to be efficiently computable or just computable. The key insight is that the asymmetry stems from how each inductor is constructed: $A$ is built directly over $D_A$ (needing only computability), while $H^+$ must be conditioned from $H$ (requiring efficient computability of the conditioning sequence). This means $A$ avoids the $\sigma \ge R(F(n))$ constraint entirely, whereas $H^+$ inherently needs it. I should verify whether the base logical inductor actually requires e.c. deductive processes, since that's the crux of whether $A$ can stay plain—it's been a point where I've been uncertain. Rather than keep reasoning from memory, I should check the original paper directly, especially since Anson is grounding everything in sources. But his real question is sharper: he's claiming that $A$ doesn't need conditioning at all because nothing reads a measure off it, and that's exactly right—it removes the cost condition from the settlement side entirely.

So the move is to affirm that insight, explain why $A$ can be a plain logical inductor (the measure-valued property only matters where you condition, and you only condition $H$), and then identify the relocated crux: whether base logical inductor existence requires $D_A$ to be e.c. or just computable. The asymmetry would then be that base existence tolerates a computable market while conditioning needs e.c. for the trader reduction—which would drop the $\sigma \ge R(F(n))$ bound and leave only one cost constraint on $e$.

Let me fetch the logical induction paper to check the definitions of deductive process and the existence theorem's requirements.

</details>

This is the right question, and it cuts deeper than my symmetry argument. Let me check the base existence theorem's actual requirement rather than keep reasoning from memory, because the whole thing now hinges on it.

<details>
<summary>⚙️ Tool call: <code>web_fetch</code></summary>

```json
{
  "url": "https://intelligence.org/files/LogicalInduction.pdf",
  "web_fetch_pdf_extract_text": true,
  "text_content_token_limit": 42000
}
```

</details>

<details>
<summary>⚙️ Tool result: <code>web_fetch</code></summary>

```
Logical Induction
Scott Garrabrant, Tsvi Benson-Tilsen, Andrew Critch, Nate Soares, and Jessica Taylor
{scott,tsvi,critch,nate,jessica}@intelligence.org
Machine Intelligence Research Institute
Abstract
We present a computable algorithm that assigns probabilities to every logical
statement in a given formal language, and refines those probabilities over time.
For instance, if the language is Peano arithmetic, it assigns probabilities to
all arithmetical statements, including claims about the twin prime conjecture,
the outputs of long-running computations, and its own probabilities. We show
that our algorithm, an instance of what we call a logical inductor, satisfies
a number of intuitive desiderata, including: (1) it learns to predict patterns
of truth and falsehood in logical statements, often long before having the
resources to evaluate the statements, so long as the patterns can be written
down in polynomial time; (2) it learns to use appropriate statistical summaries
to predict sequences of statements whose truth values appear pseudorandom;
and (3) it learns to have accurate beliefs about its own current beliefs, in a
manner that avoids the standard paradoxes of self-reference. For example, if
a given computer program only ever produces outputs in a certain range, a
logical inductor learns this fact in a timely manner; and if late digits in the
decimal expansion of π are difficult to predict, then a logical inductor learns
to assign ≈ 10% probability to “the nth digit of π is a 7” for large n. Logical
inductors also learn to trust their future beliefs more than their current beliefs,
and their beliefs are coherent in the limit (whenever φ → ψ, P∞(φ) ≤ P∞(ψ),
and so on); and logical inductors strictly dominate the universal semimeasure
in the limit.
These properties and many others all follow from a single logical induction
criterion, which is motivated by a series of stock trading analogies. Roughly
speaking, each logical sentence φ is associated with a stock that is worth $1
per share if φ is true and nothing otherwise, and we interpret the belief-state
of a logically uncertain reasoner as a set of market prices, where Pn(φ) = 50%
means that on day n, shares of φ may be bought or sold from the reasoner for
50¢. The logical induction criterion says (very roughly) that there should not
be any polynomial-time computable trading strategy with finite risk tolerance
that earns unbounded profits in that market over time. This criterion bears
strong resemblance to the “no Dutch book” criteria that support both expected
utility theory (von Neumann and Morgenstern 1944) and Bayesian probability
theory (Ramsey 1931; de Finetti 1937).
Contents
1 Introduction 4
1.1 Desiderata for Reasoning under Logical Uncertainty . . . . . . . . . 5
1.2 Related Work . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 9
1.3 Overview . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 11
See https://intelligence.org/files/LogicalInductionAbridged.pdf for an abridged version of
this paper.
1
2 Notation 12
3 The Logical Induction Criterion 14
3.1 Markets . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 14
3.2 Deductive Processes . . . . . . . . . . . . . . . . . . . . . . . . . . . 15
3.3 Efficient Computability . . . . . . . . . . . . . . . . . . . . . . . . . 16
3.4 Traders . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 17
3.5 Exploitation . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 20
3.6 Main Result . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 20
4 Properties of Logical Inductors 21
4.1 Convergence and Coherence . . . . . . . . . . . . . . . . . . . . . . . 22
4.2 Timely Learning . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 24
4.3 Calibration and Unbiasedness . . . . . . . . . . . . . . . . . . . . . . 27
4.4 Learning Statistical Patterns . . . . . . . . . . . . . . . . . . . . . . 30
4.5 Learning Logical Relationships . . . . . . . . . . . . . . . . . . . . . 31
4.6 Non-Dogmatism . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 35
4.7 Conditionals . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 38
4.8 Expectations . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 39
4.9 Trust in Consistency . . . . . . . . . . . . . . . . . . . . . . . . . . . 42
4.10 Reasoning about Halting . . . . . . . . . . . . . . . . . . . . . . . . . 44
4.11 Introspection . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 45
4.12 Self-Trust . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 47
5 Construction 49
5.1 Constructing MarketMaker . . . . . . . . . . . . . . . . . . . . . . . 50
5.2 Constructing Budgeter . . . . . . . . . . . . . . . . . . . . . . . . . 52
5.3 Constructing TradingFirm . . . . . . . . . . . . . . . . . . . . . . . 54
5.4 Constructing LIA . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 57
5.5 Questions of Runtime and Convergence Rates . . . . . . . . . . . . . 57
6 Selected Proofs 58
6.1 Convergence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 58
6.2 Limit Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 60
6.3 Non-dogmatism . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 62
6.4 Learning Pseudorandom Frequencies . . . . . . . . . . . . . . . . . . 64
6.5 Provability Induction . . . . . . . . . . . . . . . . . . . . . . . . . . . 67
7 Discussion 67
7.1 Applications . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 67
7.2 Analysis . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 68
7.3 Variations . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 70
7.4 Open Questions . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 71
7.5 Acknowledgements . . . . . . . . . . . . . . . . . . . . . . . . . . . . 73
References 73
A Preliminaries 79
A.1 Organization of the Appendix . . . . . . . . . . . . . . . . . . . . . . 79
A.2 Expressible Features . . . . . . . . . . . . . . . . . . . . . . . . . . . 79
A.3 Definitions . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 81
B Convergence Proofs 82
B.1 Return on Investment . . . . . . . . . . . . . . . . . . . . . . . . . . 82
B.2 Affine Preemptive Learning . . . . . . . . . . . . . . . . . . . . . . . 88
B.3 Preemptive Learning . . . . . . . . . . . . . . . . . . . . . . . . . . . 91
B.4 Convergence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 92
B.5 Persistence of Affine Knowledge . . . . . . . . . . . . . . . . . . . . . 92
B.6 Persistence of Knowledge . . . . . . . . . . . . . . . . . . . . . . . . 95
2
C Coherence Proofs 95
C.1 Affine Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 95
C.2 Affine Provability Induction . . . . . . . . . . . . . . . . . . . . . . . 97
C.3 Provability Induction . . . . . . . . . . . . . . . . . . . . . . . . . . . 97
C.4 Belief in Finitistic Consistency . . . . . . . . . . . . . . . . . . . . . 97
C.5 Belief in the Consistency of a Stronger Theory . . . . . . . . . . . . 98
C.6 Disbelief in Inconsistent Theories . . . . . . . . . . . . . . . . . . . . 98
C.7 Learning of Halting Patterns . . . . . . . . . . . . . . . . . . . . . . 98
C.8 Learning of Provable Non-Halting Patterns . . . . . . . . . . . . . . 98
C.9 Learning not to Anticipate Halting . . . . . . . . . . . . . . . . . . . 98
C.10 Limit Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 99
C.11 Learning Exclusive-Exhaustive Relationships . . . . . . . . . . . . . 99
D Statistical Proofs 99
D.1 Affine Recurring Unbiasedness . . . . . . . . . . . . . . . . . . . . . 99
D.2 Recurring Unbiasedness . . . . . . . . . . . . . . . . . . . . . . . . . 102
D.3 Simple Calibration . . . . . . . . . . . . . . . . . . . . . . . . . . . . 102
D.4 Affine Unbiasedness From Feedback . . . . . . . . . . . . . . . . . . 103
D.5 Unbiasedness From Feedback . . . . . . . . . . . . . . . . . . . . . . 104
D.6 Learning Pseudorandom Affine Sequences . . . . . . . . . . . . . . . 105
D.7 Learning Varied Pseudorandom Frequencies . . . . . . . . . . . . . . 106
D.8 Learning Pseudorandom Frequencies . . . . . . . . . . . . . . . . . . 107
E Expectations Proofs 107
E.1 Consistent World LUV Approximation Lemma . . . . . . . . . . . . 107
E.2 Mesh Independence Lemma . . . . . . . . . . . . . . . . . . . . . . . 108
E.3 Expectation Preemptive Learning . . . . . . . . . . . . . . . . . . . . 109
E.4 Expectations Converge . . . . . . . . . . . . . . . . . . . . . . . . . . 110
E.5 Limiting Expectation Approximation Lemma . . . . . . . . . . . . . 110
E.6 Persistence of Expectation Knowledge . . . . . . . . . . . . . . . . . 110
E.7 Expectation Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . 111
E.8 Expectation Provability Induction . . . . . . . . . . . . . . . . . . . 111
E.9 Linearity of Expectation . . . . . . . . . . . . . . . . . . . . . . . . . 111
E.10 Expectations of Indicators . . . . . . . . . . . . . . . . . . . . . . . . 112
E.11 Expectation Recurring Unbiasedness . . . . . . . . . . . . . . . . . . 112
E.12 Expectation Unbiasedness From Feedback . . . . . . . . . . . . . . . 112
E.13 Learning Pseudorandom LUV Sequences . . . . . . . . . . . . . . . . 113
F Introspection and Self-Trust Proofs 113
F.1 Introspection . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 113
F.2 Paradox Resistance . . . . . . . . . . . . . . . . . . . . . . . . . . . . 114
F.3 Expectations of Probabilities . . . . . . . . . . . . . . . . . . . . . . 115
F.4 Iterated Expectations . . . . . . . . . . . . . . . . . . . . . . . . . . 115
F.5 Expected Future Expectations . . . . . . . . . . . . . . . . . . . . . 115
F.6 No Expected Net Update . . . . . . . . . . . . . . . . . . . . . . . . 116
F.7 No Expected Net Update under Conditionals . . . . . . . . . . . . . 116
F.8 Self-Trust . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 117
G Non-Dogmatism and Closure Proofs 118
G.1 Parametric Traders . . . . . . . . . . . . . . . . . . . . . . . . . . . . 118
G.2 Uniform Non-Dogmatism . . . . . . . . . . . . . . . . . . . . . . . . 119
G.3 Occam Bounds . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 122
G.4 Non-Dogmatism . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 123
G.5 Domination of the Universal Semimeasure . . . . . . . . . . . . . . . 123
G.6 Strict Domination of the Universal Semimeasure . . . . . . . . . . . 125
G.7 Closure under Finite Perturbations . . . . . . . . . . . . . . . . . . . 126
G.8 Conditionals on Theories . . . . . . . . . . . . . . . . . . . . . . . . . 127
3
1 Introduction
Every student of mathematics has experienced uncertainty about conjectures for
which there is “quite a bit of evidence”, such as the Riemann hypothesis or the twin
prime conjecture. Indeed, when Zhang (2014) proved a bound on the gap between
primes, we were tempted to increase our credence in the twin prime conjecture. But
how much evidence does this bound provide for the twin prime conjecture? Can we
quantify the degree to which it should increase our confidence?
The natural impulse is to appeal to probability theory in general and Bayes’
theorem in particular. Bayes’ theorem gives rules for how to use observations to
update empirical uncertainty about unknown events in the physical world. However,
probability theory lacks the tools to manage uncertainty about logical facts.
Consider encountering a computer connected to an input wire and an output
wire. If we know what algorithm the computer implements, then there are two
distinct ways to be uncertain about the output. We could be uncertain about the
input—maybe it’s determined by a coin toss we didn’t see. Alternatively, we could
be uncertain because we haven’t had the time to reason out what the program
does—perhaps it computes the parity of the 87,653rd digit in the decimal expansion
of π, and we don’t personally know whether it’s even or odd.
The first type of uncertainty is about empirical facts. No amount of thinking in
isolation will tell us whether the coin came up heads. To resolve empirical uncertainty
we must observe the coin, and then Bayes’ theorem gives a principled account of
how to update our beliefs.
The second type of uncertainty is about a logical fact, about what a known
computation will output when evaluated. In this case, reasoning in isolation can and
should change our beliefs: we can reduce our uncertainty by thinking more about π,
without making any new observations of the external world.
In any given practical scenario, reasoners usually experience a mix of both
empirical uncertainty (about how the world is) and logical uncertainty (about what
that implies). In this paper, we focus entirely on the problem of managing logical
uncertainty. Probability theory does not address this problem, because probabilitytheoretic reasoners cannot possess uncertainty about logical facts. For example,
let φ stand for the claim that the 87,653rd digit of π is a 7. If this claim is true,
then (1 + 1 = 2) ⇒ φ. But the laws of probability theory say that if A ⇒ B then
Pr(A) ≤ Pr(B). Thus, a perfect Bayesian must be at least as sure of φ as they are
that 1 + 1 = 2! Recognition of this problem dates at least back to Good (1950).
Many have proposed methods for relaxing the criterion Pr(A) ≤ Pr(B) until such
a time as the implication has been proven (see, e.g, the work of Hacking [1967] and
Christiano [2014]). But this leaves open the question of how probabilities should be
assigned before the implication is proven, and this brings us back to the search for a
principled method for managing uncertainty about logical facts when relationships
between them are suspected but unproven.
We propose a partial solution, which we call logical induction. Very roughly,
our setup works as follows. We consider reasoners that assign probabilities to
sentences written in some formal language and refine those probabilities over time.
Assuming the language is sufficiently expressive, these sentences can say things
like “Goldbach’s conjecture is true” or “the computation prg on input i produces
the output prg(i)=0”. The reasoner is given access to a slow deductive process
that emits theorems over time, and tasked with assigning probabilities in a manner
that outpaces deduction, e.g., by assigning high probabilities to sentences that are
eventually proven, and low probabilities to sentences that are eventually refuted,
well before they can be verified deductively. Logical inductors carry out this task in
a way that satisfies many desirable properties, including:
1. Their beliefs are logically consistent in the limit as time approaches infinity.
2. They learn to make their probabilities respect many different patterns in logic,
at a rate that outpaces deduction.
3. They learn to know what they know, and trust their future beliefs, while
avoiding paradoxes of self-reference.
4
These claims (and many others) will be made precise in Section 4.
A logical inductor is any sequence of probabilities that satisfies our logical
induction criterion, which works roughly as follows. We interpret a reasoner’s
probabilities as prices in a stock market, where the probability of φ is interpreted
as the price of a share that is worth $1 if φ is true, and $0 otherwise (similar to
Beygelzimer, Langford, and Pennock [2012]). We consider a collection of stock
traders who buy and sell shares at the market prices, and define a sense in which
traders can exploit markets that have irrational beliefs. The logical induction
criterion then says that it should not be possible to exploit the market prices using
any trading strategy that can be generated in polynomial-time.
Our main finding is a computable algorithm which satisfies the logical induction
criterion, plus proofs that a variety of different desiderata follow from this criterion.
The logical induction criterion can be seen as a weakening of the “no Dutch
book” criterion that Ramsey (1931) and de Finetti (1937) used to support standard
probability theory, which is analogous to the “no Dutch book” criterion that von
Neumann and Morgenstern (1944) used to support expected utility theory. Under
this interpretation, our criterion says (roughly) that a rational deductively limited
reasoner should have beliefs that can’t be exploited by any Dutch book strategy
constructed by an efficient (polynomial-time) algorithm. Because of the analogy, and
the variety of desirable properties that follow immediately from this one criterion,
we believe that the logical induction criterion captures a portion of what it means to
do good reasoning about logical facts in the face of deductive limitations. That said,
there are clear drawbacks to our algorithm: it does not use its resources efficiently;
it is not a decision-making algorithm (i.e., it does not “think about what to think
about”); and the properties above hold either asymptotically (with poor convergence
bounds) or in the limit. In other words, our algorithm gives a theoretically interesting
but ultimately impractical account of how to manage logical uncertainty.
1.1 Desiderata for Reasoning under Logical Uncertainty
For historical context, we now review a number of desiderata that have been
proposed in the literature as desirable features of “good reasoning” in the face of
logical uncertainty. A major obstacle in the study of logical uncertainty is that
it’s not clear what would count as a satisfactory solution. In lieu of a solution, a
common tactic is to list desiderata that intuition says a good reasoner should meet.
One can then examine them for patterns, relationships, and incompatibilities. A
multitude of desiderata have been proposed throughout the years; below, we have
collected a variety of them. Each is stated in its colloquial form; many will be stated
formally and studied thoroughly later in this paper.
Desideratum 1 (Computable Approximability). The method for assigning probabilities to logical claims (and refining them over time) should be computable.
(See Section 5 for our algorithm.)
A good method for refining beliefs about logic can never be entirely finished, because a
reasoner can always learn additional logical facts by thinking for longer. Nevertheless,
if the algorithm refining beliefs is going to have any hope of practicality, it should at
least be computable. This idea dates back at least to Good (1950), and has been
discussed in depth by Hacking (1967) and Eells (1990), among others.
Desideratum 1 may seem obvious, but it is not without its teeth. It rules out
certain proposals, such as that of Hutter et al. (2013), which has no computable
approximation (Sawin and Demski 2013).
Desideratum 2 (Coherence in the Limit). The belief state that the reasoner is
approximating better and better over time should be logically consistent.
(Discussed in Section 4.1.)
First formalized by Gaifman (1964), the idea of Desideratum 2 is that the belief
state that the reasoner is approximating—the beliefs they would have if they had
infinite time to think—should be internally consistent. This means that, in the limit
5
of reasoning, a reasoner should assign Pr(φ) ≤ Pr(ψ) whenever φ ⇒ ψ, and they
should assign probability 1 to all theorems and 0 to all contradictions, and so on.
Desideratum 3 (Approximate Coherence). The belief state of the reasoner should
be approximately coherent. For example, if the reasoner knows that two statements
are mutually exclusive, then it should assign probabilities to those sentences that sum
to no more than 1, even if it cannot yet prove either sentence.
(Discussed in sections 4.2 and 4.5.)
Being coherent in the limit is desirable, but good deductively limited reasoning
requires approximate coherence at finite times. Consider two claims about a particular computation prg, which takes a number n as input and produces a number
prg(n) as output. Assume the first claim says prg(7)=0, and the second says
prg(7)=1. Clearly, these claims are mutually exclusive, and once a reasoner realizes
this fact, they should assign probabilities to the two claims that sum to at most 1,
even before they can evaluate prg(7). Limit coherence does not guarantee this: a
reasoner could assign bad probabilities (say, 100% to both claims) right up until they
can evaluate prg(7), at which point they start assigning the correct probabilities.
Intuitively, a good reasoner should be able to recognize the mutual exclusivity before
they’ve proven either claim. In other words, a good reasoner’s beliefs should be
approximately coherent.
Desideratum 3 dates back to at least Good (1950), who proposes a weakening of
the condition of coherence that could apply to the belief states of limited reasoners.
Hacking (1967) proposes an alternative weakening, as do Garrabrant, Fallenstein,
et al. (2016).
Desideratum 4 (Learning of Statistical Patterns). In lieu of knowledge that bears
on a logical fact, a good reasoner should assign probabilities to that fact in accordance
with the rate at which similar claims are true. (Discussed in Section 4.4.)
For example, a good reasoner should assign probability ≈ 10% to the claim “the
nth digit of π is a 7” for large n (assuming there is no efficient way for a reasoner to
guess the digits of π for large n). This desideratum dates at least back to Savage
(1967), and seems clearly desirable. If a reasoner thought the 10100th digit of π
was almost surely a 9, but had no reason for believing this, we would be suspicious
of their reasoning methods. Desideratum 4 is difficult to state formally; for two
attempts, refer to Garrabrant, Benson-Tilsen, et al. (2016) and Garrabrant, Soares,
and Taylor (2016).
Desideratum 5 (Calibration). Good reasoners should be well-calibrated. That is,
among events that a reasoner says should occur with probability p, they should in
fact occur about p proportion of the time. (Discussed in Section 4.3.)
Calibration as a desirable property dates back to Pascal, and perhaps farther.
If things that a reasoner says should happen 30% of the time actually wind up
happening 80% of the time, then they aren’t particularly reliable.
Desideratum 6 (Non-Dogmatism). A good reasoner should not have extreme beliefs
about mathematical facts, unless those beliefs have a basis in proof.
(Discussed in Section 4.6.)
It would be worrying to see a mathematical reasoner place extreme confidence in
a mathematical proposition, without any proof to back up their belief. The virtue
of skepticism is particularly apparent in probability theory, where Bayes’ theorem
says that a probabilistic reasoner can never update away from “extreme” (0 or 1)
probabilities. Accordingly, Cromwell’s law (so named by the statistician Lindley
[1991]) says that a reasonable person should avoid extreme probabilities except
when applied to statements that are logically true or false. We are dealing with
logical uncertainty, so it is natural to extend Cromwell’s law to say that extreme
probabilities should also be avoided on logical statements, except in cases where
the statements have been proven true or false. In settings where reasoners are able
6
to update away from 0 or 1 probabilities, this means that a good reasoner’s beliefs
shouldn’t be “stuck” at probability 1 or 0 on statements that lack proofs or disproofs.
In the domain of logical uncertainty, Desideratum 6 can be traced back to Carnap
(1962, Sec. 53), and has been demanded by many, including Gaifman and Snir (1982)
and Hutter et al. (2013).
Desideratum 7 (Uniform Non-Dogmatism). A good reasoner should assign a nonzero probability to any computably enumerable consistent theory (viewed as a limit
of finite conjunctions). (Discussed in Section 4.6.)
For example the axioms of Peano arithmetic are computably enumerable, and if we
construct an ever-growing conjunction of these axioms, we can ask that the limit
of a reasoner’s credence in these conjunctions converge to a value bounded above
0, even though there are infinitely many conjuncts. The first formal statement of
Desideratum 7 that we know of is given by Demski (2012), though it is implicitly
assumed whenever asking for a set of beliefs that can reason accurately about
arbitrary arithmetical claims (as is done by, e.g., Savage [1967] and Hacking [1967]).
Desideratum 8 (Universal Inductivity). Given enough time to think, the beliefs of
a good reasoner should dominate the universal semimeasure.
(Discussed in Section 4.6.)
Good reasoning in general has been studied for quite some time, and reveals some
lessons that are useful for the study of good reasoning under deductive limitation.
Solomonoff (1964a, 1964b), Zvonkin and Levin (1970), and Li and Vitányi (1993) have
given a compelling formal treatment of good reasoning assuming logical omniscience
in the domain of sequence prediction, by describing an inductive process (known as
a universal semimeasure) with a number of nice properties, including (1) it assigns
non-zero prior probability to every computable sequence of observations; (2) it
assigns higher prior probability to simpler hypotheses; and (3) it predicts as well or
better than any computable predictor, modulo a constant amount of error. Alas,
universal semimeasures are uncomputable; nevertheless, they provide a formal model
of what it means to predict sequences well, and we can ask logically uncertain
reasoners to copy those successes. For example, we can ask that they would perform
as well as a universal semimeasure if given enough time to think.
Desideratum 9 (Approximate Bayesianism). The reasoner’s beliefs should admit
of some notion of conditional probabilities, which approximately satisfy both Bayes’
theorem and the other desiderata listed here. (Discussed in Section 4.7.)
Bayes’ rule gives a fairly satisfying account of how to manage empirical uncertainty
in principle (as argued extensively by Jaynes [2003]), where beliefs are updated by
conditioning a probability distribution. As discussed by Good (1950) and Glymour
(1980), creating a distribution that satisfies both coherence and Bayes’ theorem
requires logical omniscience. Still, we can ask that the approximation schemes
used by a limited agent be approximately Bayesian in some fashion, while retaining
whatever good properties the unconditional probabilities have.
Desideratum 10 (Introspection). If a good reasoner knows something, she should
also know that she knows it. (Discussed in Section 4.11.)
Proposed by Hintikka (1962), this desideratum is popular among epistemic logicians.
It is not completely clear that this is a desirable property. For instance, reasoners
should perhaps be allowed to have “implicit knowledge” (which they know without
knowing that they know it), and it’s not clear where the recursion should stop
(do you know that you know that you know that you know that 1 = 1?). This
desideratum has been formalized in many different ways; see Christiano et al. (2013)
and Campbell-Moore (2015) for a sample.
Desideratum 11 (Self-Trust). A good reasoner thinking about a hard problem
should expect that, in the future, her beliefs about the problem will be more accurate
than her current beliefs. (Discussed in Section 4.12.)
7
Stronger than self-knowledge is self-trust—a desideratum that dates at least back to
Hilbert (1902), when mathematicians searched for logics that placed confidence in
their own machinery. While Gödel, Kleene, and Rosser (1934) showed that strong
forms of self-trust are impossible in a formal proof setting, experience demonstrates
that human mathematicians are capable of trusting their future reasoning, relatively
well, most of the time. A method for managing logical uncertainty that achieves
this type of self-trust would be highly desirable.
Desideratum 12 (Approximate Inexploitability). It should not be possible to run
a Dutch book against a good reasoner in practice. (See Section 3 for our proposal.)
Expected utility theory and probability theory are both supported in part by “Dutch
book” arguments which say that an agent is rational if (and only if) there is no way
for a clever bookie to design a “Dutch book” which extracts arbitrary amounts of
money from the reasoner (von Neumann and Morgenstern 1944; de Finetti 1937).
As noted by Eells (1990), these constraints are implausibly strong: all it takes to
run a Dutch book according to de Finetti’s formulation is for the bookie to know a
logical fact that the reasoner does not know. Thus, to avoid being Dutch booked by
de Finetti’s formulation, a reasoner must be logically omniscient.
Hacking (1967) and Eells (1990) call for weakenings of the Dutch book constraints,
in the hopes that reasoners that are approximately inexploitable would do good
approximate reasoning. This idea is the cornerstone of our framework—in particular,
we consider reasoners that cannot be exploited in polynomial time, using a formalism
defined below. See Definition 3.0.1 for details.
Desideratum 13 (Gaifman Inductivity). Given a Π1 statement φ (i.e., a universal
generalization of the form “for every x, ψ”), as the set of examples the reasoner has
seen goes to “all examples”, the reasoner’s belief in φ should approach certainty.
(Discussed below.)
Proposed by Gaifman (1964), Desideratum 13 states that a reasoner should “generalize well”, in the sense that as they see more instances of a universal claim (such
as “for every x, ψ(x) is true”) they should eventually believe the universal with
probability 1. Desideratum 13 has been advocated by Hutter et al. (2013).
Desideratum 14 (Efficiency). The algorithm for assigning probabilities to logical
claims should run efficiently, and be usable in practice. (Discussed in Section 7.1.)
One goal of understanding “good reasoning” in the face of logical uncertainty is
to design algorithms for reasoning using limited computational resources. For
that, the algorithm for assigning probabilities to logical claims needs to be not
only computable, but efficient. Aaronson (2013) gives a compelling argument that
solutions to logical uncertainty require understanding complexity theory, and this
idea is closely related to the study of bounded rationality (Simon 1982) and efficient
meta-reasoning (Russell and Wefald 1991b).
Desideratum 15 (Decision Rationality). The algorithm for assigning probabilities
to logical claims should be able to target specific, decision-relevant claims, and
it should reason about those claims as efficiently as possible given the computing
resources available. (Discussed in Section 7.4.)
This desideratum dates at least back to Savage (1967), who asks for an extension to
probability theory that takes into account the costs of thinking. For a method of
reasoning under logical uncertainty to aid in the understanding of good bounded
reasoning, it must be possible for an agent to use the reasoning system to reason
efficiently about specific decision-relevant logical claims, using only enough resources
to refine the probabilities well enough for the right decision to become clear. This
desideratum blurs the line between decision-making and logical reasoning; see Russell
and Wefald (1991a) and Hay et al. (2012) for a discussion.
Desideratum 16 (Answers Counterpossible Questions). When asked questions
about contradictory states of affairs, a good reasoner should give reasonable answers.
(Discussed in Section 7.4.)
8
In logic, the principle of explosion says that from a contradiction, anything follows.
By contrast, when human mathematicians are asked counterpossible questions,
such as “what would follow from Fermat’s last theorem being false?”, they often
give reasonable answers, such as “then there would exist non-modular elliptic
curves”, rather than just saying “anything follows from a contradiction”. Soares and
Fallenstein (2015) point out that some deterministic decision-making algorithms
reason about counterpossible questions (“what would happen if my deterministic
algorithm had the output a vs b vs c?”). The topic of counterpossibilities has been
studied by philosophers including Cohen (1990), Vander Laan (2004), Brogaard
and Salerno (2007), Krakauer (2012), and Bjerring (2014), and it is reasonable to
hope that a good logically uncertain reasoner would give reasonable answers to
counterpossible questions.
Desideratum 17 (Use of Old Evidence). When a bounded reasoner comes up with
a new theory that neatly describes anomalies in the old theory, that old evidence
should count as evidence in favor of the new theory. (Discussed in Section 7.4.)
The problem of old evidence is a longstanding problem in probability theory (Glymour
1980). Roughly, the problem is that a perfect Bayesian reasoner always uses all
available evidence, and keeps score for all possible hypotheses at all times, so no
hypothesis ever gets a “boost” from old evidence. Human reasoners, by contrast,
have trouble thinking up good hypotheses, and when they do, those new hypotheses
often get a large boost by retrodicting old evidence. For example, the precession of
the perihelion of Mercury was known for quite some time before the development of
the theory of General Relativity, and could not be explained by Newtonian mechanics,
so it was counted as strong evidence in favor of Einstein’s theory. Garber (1983) and
Jeffrey (1983) have speculated that a solution to the problem of logical omniscience
would shed light on solutions to the problem of old evidence.
Our solution does not achieve all these desiderata. Doing so would be impossible;
Desiderata 1, 2, and 13 cannot be satisfied simultaneously. Further, Sawin and
Demski (2013) have shown that Desiderata 1, 6, 13, and a very weak form of 2
are incompatible; an ideal belief state that is non-dogmatic, Gaifman inductive,
and coherent in a weak sense has no computable approximation. Our algorithm is
computably approximable, approximately coherent, and non-dogmatic, so it cannot
satisfy 13. Our algorithm also fails to meet 14 and 15, because while our algorithm
is computable, it is purely inductive, and so it does not touch upon the decision
problem of thinking about what to think about and how to think about it with
minimal resource usage. As for 16 and 17, the case is interesting but unclear; we
give these topics some treatment in Section 7.
Our algorithm does satisfy desiderata 1 through 12. In fact, our algorithm is
designed to meet only 1 and 12, from which 2-11 will all be shown to follow. This is
evidence that our logical induction criterion captures a portion of what it means
to manage uncertainty about logical claims, analogous to how Bayesian probability
theory is supported in part by the fact that a host of good properties follow from a
single criterion (“don’t be exploitable by a Dutch book”). That said, there is ample
room to disagree about how well our algorithm achieves certain desiderata, e.g. when
the desiderata is met only in the asymptote, or with error terms that vanish only
slowly.
1.2 Related Work
The study of logical uncertainty is an old topic. It can be traced all the way back
to Bernoulli, who laid the foundations of statistics, and later Boole (1854), who
was interested in the unification of logic with probability from the start. Refer
to Hailperin (1996) for a historical account. Our algorithm assigns probabilities
to sentences of logic directly; this thread can be traced back through Łoś (1955)
and later Gaifman (1964), who developed the notion of coherence that we use in
this paper. More recently, that thread has been followed by Demski (2012), whose
framework we use, and Hutter et al. (2013), who define a probability distribution
9
on logical sentences that is quite desirable, but which admits of no computable
approximation (Sawin and Demski 2013).
The objective of our algorithm is to manage uncertainty about logical facts (such
as facts about mathematical conjectures or long-running computer programs). When
it comes to the problem of developing formal tools for manipulating uncertainty,
our methods are heavily inspired by Bayesian probability theory, and so can be
traced back to Pascal, who was followed by Bayes, Laplace, Kolmogorov (1950),
Savage (1954), Carnap (1962), and Jaynes (2003), and many others. Polya (1990)
was among the first in the literature to explicitly study the way that mathematicians
engage in plausible reasoning, which is tightly related to the object of our study.
We are interested in the subject of what it means to do “good reasoning” under
logical uncertainty. In this, our approach is quite similar to the approach of Ramsey
(1931), de Finetti (1937), von Neumann and Morgenstern (1944), Teller (1973),
Lewis (1999), and Joyce (1999), who each developed axiomatizations of rational
behavior and produced arguments supporting those axioms. In particular, they
each supported their proposals with Dutch book arguments, and those Dutch book
arguments were a key inspiration for our logical induction criterion.
The fact that using a coherent probability distribution requires logical omniscience
(and is therefore unsatisfactory when it comes to managing logical uncertainty) dates
at least back to Good (1950). Savage (1967) also recognized the problem, and stated a
number of formal desiderata that our solution in fact meets. Hacking (1967) addressed
the problem by discussing notions of approximate coherence and weakenings of the
Dutch book criteria. While his methods are ultimately unsatisfactory, our approach
is quite similar to his in spirit.
The flaw in Bayesian probability theory was also highlighted by Glymour (1980),
and dubbed the “problem of old evidence” by Garber (1983) in response to Glymor’s
criticism. Eells (1990) gave a lucid discussion of the problem, revealed flaws in
Garber’s arguments and in Hacking’s solution, and named a number of other
desiderata which our algorithm manages to satisfy. Refer to Zynda (1995) and
Sprenger (2015) for relevant philosophical discussion in the wake of Eells. Of note
is the treatment of Adams (1996), who uses logical deduction to reason about an
unknown probability distribution that satisfies certain logical axioms. Our approach
works in precisely the opposite direction: we use probabilistic methods to create an
approximate distribution where logical facts are the subject.
Straddling the boundary between philosophy and computer science, Aaronson
(2013) has made a compelling case that computational complexity must play a role
in answering questions about logical uncertainty. These arguments also provided
some inspiration for our approach, and roughly speaking, we weaken the Dutch book
criterion of standard probability theory by considering only exploitation strategies
that can be constructed by a polynomial-time machine. The study of logical
uncertainty is also tightly related to the study of bounded rationality (Simon 1982;
Russell and Wefald 1991a; Rubinstein 1998; Russell 2016).
Fagin and Halpern (1987) also straddled the boundary between philosophy and
computer science with early discussions of algorithms that manage uncertainty in the
face of resource limitations. (See also their discussions of uncertainty and knowledge
[Fagin et al. 1995; Halpern 2003].) This is a central topic in the field of artificial
intelligence (AI), where scientists and engineers have pursued many different paths
of research. The related work in this field is extensive, including (but not limited to)
work on probabilistic programming (Vajda 1972; McCallum, Schultz, and Singh 2009;
Wood, Meent, and Mansinghka 2014; De Raedt and Kimmig 2015); probabilistic
inductive logic programming (Muggleton and Watanabe 2014; De Raedt and Kersting
2008; De Raedt 2008; Kersting and De Raedt 2007); and meta-reasoning (Russell and
Wefald 1991b; Zilberstein 2008; Hay et al. 2012). The work most closely related to our
own is perhaps the work of Thimm (2013a) and others on reasoning using inconsistent
knowledge bases, a task which is analogous to constructing an approximately coherent
probability distribution. (See also Muiño [2011], Thimm [2013b], Potyka and Thimm
[2015], and Potyka [2015].) Our framework also bears some resemblance to the
Markov logic network framework of Richardson and Domingos (2006), in that both
algorithms are coherent in the limit. Where Markov logic networks are specialized
10
to individual restricted domains of discourse, our algorithm reasons about all logical
sentences. (See also Kok and Domingos [2005], Singla and Domingos [2005], Tran
and Davis [2008], Lowd and Domingos [2007], Mihalkova, Huynh, and Mooney [2007],
Wang and Domingos [2008], and Khot et al. [2015].)
In that regard, our algorithm draws significant inspiration from Solomonoff’s
theory of inductive inference (Solomonoff 1964a, 1964b) and the developments on
that theory made by Zvonkin and Levin (1970) and Li and Vitányi (1993). Indeed,
we view our algorithm as a Solomonoff-style approach to the problem of reasoning
under logical uncertainty, and as a result, our algorithm bears a strong resemblance
to many algorithms that are popular methods for practical statistics and machine
learning; refer to Opitz and Maclin (1999) and Dietterich (2000) for reviews of
popular and successful ensemble methods. Our approach is also similar in spirit
to the probabilistic numerics approach of Briol, Oates, Girolami, Osborne, and
Sejdinovic (2015), but where probabilistic numerics is concerned with algorithms
that give probabilistic answers to individual particular numerical questions, we are
concerned with algorithms that assign probabilities to all queries in a given formal
language. (See also [Briol, Oates, Girolami, and Osborne 2015; Hennig, Osborne,
and Girolami 2015].)
Finally, our method of interpreting beliefs as prices and using prediction markets
to generate reasonable beliefs bears heavy resemblance to the work of Beygelzimer,
Langford, and Pennock (2012) who use similar mechanisms to design a learning
algorithm that bets on events. Our results can be seen as an extension of that idea
to the case where the events are every sentence written in some formal language, in
a way that learns inductively to predict logical facts while avoiding the standard
paradoxes of self-reference.
The work sampled here is only a small sample of the related work, and it neglects
contributions from many other fields, including but not limited to epistemic logic
(Gärdenfors 1988; Meyer and Van Der Hoek 1995; Schlesinger 1985; Sowa 1999;
Guarino 1998), game theory (Rantala 1979; Hintikka 1979; Bacharach 1994; Lipman
1991; Battigalli and Bonanno 1999; Binmore 1992), paraconsistent logic (Blair and
Subrahmanian 1989; Priest 2002; Mortensen 2013; Fuhrmann 2013; Akama and
Costa 2016) and fuzzy logic (Klir and Yuan 1995; Yen and Langari 1999; Gerla
2013). The full history is too long and rich for us to do it justice here.
1.3 Overview
Our main result is a formalization of Desideratum 12 above, which we call the logical
induction criterion, along with a computable algorithm that meets the criterion,
plus proofs that formal versions of Desiderata 2-11 all follow from the criterion.
In Section 2 we define some notation. In Section 3 we state the logical induction
criterion and our main theorem, which says that there exists a computable logical
inductor. The logical induction criterion is motivated by a series of stock trading
analogies, which are also introduced in Section 3.
In Section 4 we discuss a number of properties that follow from this criterion, including properties that hold in the limit, properties that relate to pattern-recognition,
calibration properties, and properties that relate to self-knowledge and self-trust.
A computable logical inductor is described in Section 5. Very roughly, the idea
is that given any trader, it’s possible to construct market prices at which they make
no trades (because they think the prices are right); and given an enumeration of
traders, it’s possible to aggregate their trades into one “supertrader” (which takes
more and more traders into account each day); and thus it is possible to construct a
series of prices which is not exploitable by any trader in the enumeration.
In Section 6 we give a few selected proofs. In Section 7 we conclude with a
discussion of applications of logical inductors, variations on the logical induction
framework, speculation about what makes logical inductors tick, and directions for
future research. The remaining proofs can be found in the appendix.
11
2 Notation
This section defines notation used throughout the paper. The reader is invited to
skim it, or perhaps skip it entirely and use it only as a reference when needed.
Common sets and functions. The set of positive natural numbers is denoted by
N
+, where the superscript makes it clear that 0 is not included. We work with N+
instead of N
≥0 because we regularly consider initial segments of infinite sequences up
to and including the element at index n, and it will be convenient for those lists to
have length n. Sums written P
i≤n
(−) are understood to start at i = 1. We use R to
denote the set of real numbers, and Q to denote the set of rational numbers. When
considering continuous functions with range in Q, we use the subspace topology
on Q inherited from R. We use B to denote the set {0, 1} interpreted as Boolean
values. In particular, Boolean operations like ∧, ∨, ¬, → and ↔ are defined on B,
for example, (1 ∧ 1) = 1, ¬1 = 0, and so on.
We write Fin(X) for the set of all finite subsets of X, and XN
+
for all infinite
sequences with elements in X. In general, we use BA to denote the set of functions
with domain A and codomain B. We treat the expression f : A → B as equivalent
to f ∈ BA, i.e., both state that f is a function that takes inputs from the set A
and produces an output in the set B. We write f : A 7→ B to indicate that f is a
partial function from A to B. We denote equivalence of expressions that represent
functions by ≡, e.g., (x − 1)2 ≡ x
2 − 2x + 1. We write k − k1 for the `1 norm. When
A is an affine combination, kAk1 includes the trailing coefficient.
Logical sentences. We generally use the symbols φ, ψ, χ to denote well-formed
formulas in some language of propositional logic L (such as a theory of first order
logic; see below), which includes the basic logical connectives ¬, ∧, ∨, →, ↔, and
uses modus ponens as its rule of inference. We assume that L has been chosen so
that its sentences can be interpreted as claims about some class of mathematical
objects, such as natural numbers or computer programs. We commonly write S for
the set of all sentences in L, and Γ for a set of axioms from which to write proofs in
the language. We write Γ ` φ when φ can be proven from Γ via modus ponens.
We will write logical formulas inside quotes “−”, such as φ := “x = 3”. The
exception is after `, where we do not write quotes, in keeping with standard
conventions. We sometimes define sentences such as φ := “Goldbach’s conjecture”,
in which case it is understood that the English text could be expanded into a precise
arithmetical claim.
We use underlines to indicate when a symbol in a formula should be replaced
by the expression it stands for. For example, if n := 3, then φ := “x > n” means
φ = “x > 3”, and ψ := “φ → (x = n + 1)” means ψ = “x > 3 → (x = 3 + 1)”. If φ
and ψ denote formulas, then ¬φ denotes “¬(φ)” and φ ∧ ψ denotes “(φ) ∧ (ψ)” and
so on. For instance, if φ := “x > 3” then ¬φ denotes “¬(x > 3)”.
First order theories and prime sentences. We consider any theory in first
order logic (such as Peano Arithmetic, PA) as a set of axioms that includes the
axioms of first order logic, so that modus ponens is the only rule of inference needed
for proofs. As such, we view any first order theory as specified in a propositional
calculus (following Enderton [2001]) whose atoms are the so-called “prime” sentences
of first order logic, i.e., quantified sentences like “∃x: · · · ”, and atomic sentences like
“t1 = t2” and “R(t1, . . . , tn)” where the ti are closed terms. Thus, every first-order
sentence can be viewed as a Boolean combination of prime sentences with logical
connectives (viewing “∀x: · · · ” as shorthand for “¬∃x: ¬ · · · ”). For example, the
sentence
φ := “((1 + 1 = 2) ∧ (∀x: x > 0)) → (∃y : ∀z : (7 > 1 + 1) → (y + z > 2))”
is decomposed into “1 + 1 = 2”, “∃x: ¬(x > 0)” and “∃y : ∀z : (7 > 1 + 1) → (y +z >
2)”, where the leading “¬” in front of the second statement is factored out as a
Boolean operator. In particular, note that while (7 > 1 + 1) is a prime sentence,
it does not occur in the Boolean decomposition of φ into primes, since it occurs
12
within a quantifier. We choose this view because we will not always assume that the
theories we manipulate include the quantifier axioms of first-order logic.
Defining values by formulas. We often view a formula that is free in one variable
as a way of defining a particular number that satisfies that formula. For example,
given the formula X(ν) = “ν
2 = 9 ∧ ν > 0”, we would like to think of X as
representing the unique value “3”, in such a way that that we can then have “5X + 1”
refer to the number 16.
To formalize this, we use the following notational convention. Let X be a formula
free in one variable. We write X(x) for the formula resulting from substituting x for
the free variable of X. If
Γ ` ∃x∀y : X(y) → y = x,
then we say that X defines a unique value (via Γ), and we refer to that value as “the
value” of X. We will be careful in distinguishing between what Γ can prove about
X(ν) on the one hand, and the values of X(ν) in different models of Γ on the other.
If X1, . . . , Xk are all formulas free in one variable that define a unique value
(via Γ), then for any k-place relationship R, we write “R(X1, X2, . . . , Xk)” as an
abbreviation for
“∀x1x2 . . . xk : X1(x1) ∧ X2(x2) ∧ . . . ∧ Xk(xk) → R(x1, x2, . . . , xk)”.
For example, “Z = 2X + Y ” is shorthand for
“∀xyz : X(x) ∧ Y (y) ∧ Z(z) → z = 2x + y”.
This convention allows us to write concise expressions that describe relationships
between well-defined values, even when those values may be difficult or impossible
to determine via computation.
Representing computations. When we say a theory Γ in first order logic “can
represent computable functions”, we mean that its language is used to refer to
computer programs in such a way that Γ satisfies the representability theorem
for computable functions. This means that for every (total) computable function
f : N
+ → N+, there exists a Γ-formula γf with two free variables such that for all
n, y ∈ N
+,
y = f(n) if and only if Γ ` ∀ν : γf (n, ν) ↔ ν = y,
where “γf (n, ν)” stands, in the usual way, for the formula resulting from substituting
an encoding of n and the symbol ν for its free variables. In particular, note that
this condition requires Γ to be consistent.
When Γ can represent computable functions, we use “f(n)” as shorthand for the
formula “γf (n, ν)”. In particular, since “γf (n, ν)” is free in a single variable ν and
defines a unique value, we use “f(n)” by the above convention to write, e.g.,
“f(3) < g(3)”
as shorthand for
“∀xy : γf (3, x) ∧ γg(3, y) → x < y”.
In particular, note that writing down a sentence like “f(3) > 4” does not involve
computing the value f(3); it merely requires writing out the definition of γf . This
distinction is important when f has a very slow runtime.
Sequences. We denote infinite sequences using overlines, like x := (x1, x2, . . .),
where it is understood that xi denotes the ith element of x, for i ∈ N
+. To
define sequences of sentences compactly, we use parenthetical expressions such as
φ := (“n > 7”)n∈N+ , which defines the sequence
(“1 > 7”, “2 > 7”, “3 > 7”, . . .).
13
We define x≤n := (x1, . . . , xn). Given another element y, we abuse notation in the
usual way and define (x≤n, y) = (x1, . . . , xn, y) to be the list x≤n with y appended
at the end. We write () for the empty sequence.
A sequence x is called computable if there is a computable function f such that
f(n) = xn for all n ∈ N
+, in which case we say f computes x.
Asymptotics. Given any sequences x and y, we write
xn hn yn for limn→∞xn − yn = 0,
xn &n yn for lim inf
n→∞
xn − yn ≥ 0, and
xn .n yn for lim sup
n→∞
xn − yn ≤ 0.
3 The Logical Induction Criterion
In this section, we will develop a framework in which we can state the logical
induction criterion and a number of properties possessed by logical inductors. The
framework will culminate in the following definition, and a theorem saying that
computable logical inductors exist for every deductive process.
Definition 3.0.1 (The Logical Induction Criterion). A market P is said to
satisfy the logical induction criterion relative to a deductive process D if
there is no efficiently computable trader T that exploits P relative to D. A
market P meeting this criterion is called a logical inductor over D.
We will now define markets, deductive processes, efficient computability, traders,
and exploitation.
3.1 Markets
We will be concerned with methods for assigning values in the interval [0, 1] to
sentences of logic. We will variously interpret those values as prices, probabilities,
and truth values, depending on the context. Let L be a language of propositional
logic, and let S be the set of all sentences written in L. We then define:
Definition 3.1.1 (Valuation). A valuation is any function V : S → [0, 1]. We
refer to V(φ) as the value of φ according to V. A valuation is called rational if its
image is in Q.
First let us treat the case where we interpret the values as prices.
Definition 3.1.2 (Pricing). A pricing P : S → Q∩[0, 1] is any computable rational
valuation. If P(φ) = p we say that the price of a φ-share according to P is p, where
the intended interpretation is that a φ-share is worth $1 if φ is true.
Definition 3.1.3 (Market). A market P = (P1, P2, . . .) is a computable sequence of pricings Pi
: S → Q ∩ [0, 1].
We can visualize a market as a series of pricings that may change day by day. The
properties proven in Section 4 will apply to any market that satisfies the logical
induction criterion. Theorem 4.1.2 (Limit Coherence) will show that the prices of a
logical inductor can reasonably be interpreted as probabilities, so we will often speak
as if the prices in a market represent the beliefs of a reasoner, where Pn(φ) = 0.75 is
interpreted as saying that on day n, the reasoner assigns 75% probability to φ.
In fact, the logical inductor that we construct in Section 5 has the additional
property of being finite at every timestep, which means we can visualize it as a series
of finite belief states that a reasoner of interest writes down each day.
14
Definition 3.1.4 (Belief State). A belief state P : S → Q ∩ [0, 1] is a computable
rational valuation with finite support, where P(φ) is interpreted as the probability
of φ (which is 0 for all but finitely many φ).
We can visualize a belief state as a finite list of (φ, p) pairs, where the φ are unique
sentences and the p are rational-number probabilities, and P(φ) is defined to be p if
(φ, p) occurs in the list, and 0 otherwise.
Definition 3.1.5 (Computable Belief Sequence). A computable belief sequence
P = (P1, P2, . . .) is a computable sequence of belief states, interpreted as a reasoner’s
explicit beliefs about logic as they are refined over time.
We can visualize a computable belief sequence as a large spreadsheet where each
column is a belief state, and the rows are labeled by an enumeration of all logical
sentences. We can then imagine a reasoner of interest working on this spreadsheet,
by working on one column per day.
Philosophically, the reason for this setup is as follows. Most people know that
the sentence “1 + 1 is even” is true, and that the sentence “1 + 1 + 1 + 1 is even” is
true. But consider, is the following sentence true?
“1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 is even”
To answer, we must pause and count the ones. Since we wish to separate the
question of what a reasoner already knows from what they could infer using further
computing resources, we require that the reasoner write out their beliefs about logic
explicitly, and refine them day by day.
In this framework, we can visualize a reasoner as a person who computes the
belief sequence by filling in a large spreadsheet, always working on the nth column
on the nth day, by refining and extending her previous work as she learns new
facts and takes more sentences into account, while perhaps making use of computer
assistance. For example, a reasoner who has noticed that “1 + · · · + 1 is even” is
true iff the sentence has an even number of ones, might program her computer to
write 1 into as many of the true “1 + · · · + 1 is even” cells per day as it can before
resources run out. As another example, a reasoner who finds a bound on the prime
gap might go back and update her probability on the twin prime conjecture. In our
algorithm, the reasoner will have more and more computing power each day, with
which to construct her next belief state.
3.2 Deductive Processes
We are interested in the question of what it means for reasoners to assign “reasonable probabilities” to statements of logic. Roughly speaking, we will imagine
reasoners that have access to some formal deductive process, such as a community of
mathematicians who submit machine-checked proofs to an official curated database.
We will study reasoners that “outpace” this deductive process, e.g., by assigning
high probabilities to conjectures that will eventually be proven, and low probabilities
to conjectures that will eventually be disproven, well before the relevant proofs are
actually found.
Definition 3.2.1 (Deductive Process). A deductive process D : N
+ →
Fin(S) is a computable nested sequence D1 ⊆ D2 ⊆ D3 . . . of finite sets of
sentences. We write D∞ for the union S
n Dn.
This is a rather barren notion of “deduction”. We will consider cases where we
fix some theory Γ, and Dn is interpreted as the theorems proven up to and including
day n. In this case, D can be visualized as a slow process that reveals the knowledge
of Γ over time. Roughly speaking, we will mainly concern ourselves with the case
where D eventually rules out all and only the worlds that are inconsistent with Γ.
15
Definition 3.2.2 (World). A world is any truth assignment W : S → B. If
W(φ) = 1 we say that φ is true in W. If W(φ) = 0 we say that φ is false in W.
We write W for the set of all worlds.
Observe that worlds are valuations, and that they are not necessarily consistent.
This terminology is nonstandard; the term “world” is usually reserved for consistent
truth assignments. Logically uncertain reasoners cannot immediately tell which
truth assignments are inconsistent, because revealing inconsistencies requires time
and effort. We use the following notion of consistency:
Definition 3.2.3 (Propositional Consistency). A world W is called propositionally consistent, abbreviated p.c., if for all φ ∈ S, W(φ) is determined by Boolean
algebra from the truth values that W assigns to the prime sentences of φ. In other
words, W is p.c. if W(φ ∧ ψ) = W(φ) ∧ W(ψ), W(φ ∨ ψ) = W(φ) ∨ W(ψ), and so on.
Given a set of sentences D, we define PC(D) to be the set of all p.c. worlds where
W(φ) = 1 for all φ ∈ D. We refer to PC(D) as the set of worlds propositionally
consistent with D.
Given a set of sentences Γ interpreted as a theory, we will refer to PC(Γ) as the
set of worlds consistent with Γ, because in this case PC(Γ) is equal to the set of
all worlds W such that
Γ ∪ {φ | W(φ) = 1} ∪ {¬φ | W(φ) = 0} 0 ⊥.
Note that a limited reasoner won’t be able to tell whether a given world W is in
PC(Γ). A reasoner can computably check whether a restriction of W to a finite
domain is propositionally consistent with a finite set of sentences, but that’s about
it. Roughly speaking, the definition of exploitation (below) will say that a good
reasoner should perform well when measured on day n by worlds propositionally
consistent with Dn, and we ourselves will be interested in deductive processes that
pin down a particular theory Γ by propositional consistency:
Definition 3.2.4 (Γ-Complete). Given a theory Γ, we say that a deductive process
D is Γ-complete if
PC(D∞) = PC(Γ).
As a canonical example, let Dn be the set of all theorems of PA provable in at
most n characters.1 Then D is PA-complete, and a reasoner with access to D can
be interpreted as someone who on day n knows all PA-theorems provable in ≤ n
characters, who must manage her uncertainty about other mathematical facts.
3.3 Efficient Computability
We use the following notion of efficiency throughout the paper:
Definition 3.3.1 (Efficiently Computable). An infinite sequence x is called
efficiently computable, abbreviated e.c., if there is a computable function f
that outputs xn on input n, with runtime polynomial in n (i.e. in the length of
n written in unary).
Our framework is not wedded to this definition; stricter notions of efficiency (e.g.,
sequences that can be computed in O(n
2
) time) would yield “dumber” inductors
with better runtimes, and vice versa. We use the set of polynomial-time computable
functions because it has some closure properties that are convenient for our purposes.
1. Because PA is a first-order theory, and the only assumption we made about L is that
it is a propositional logic, note that the axioms of first-order logic—namely, specialization
and distribution—must be included as theorems in D.
16
3.4 Traders
Roughly speaking, traders are functions that see the day n and the history of market
prices up to and including day n, and then produce a series of buy and sell orders,
by executing a strategy that is continuous as a function of the market history.
A linear combination of sentences can be interpreted as a “market order”, where
3φ − 2ψ says to buy 3 shares of φ and sell 2 shares of ψ. Very roughly, a trading
strategy for day n will be a method for producing market orders where the coefficients
are not numbers but functions which depend (continuously) on the market prices
up to and including day n.
Definition 3.4.1 (Valuation Feature). A valuation feature α : [0, 1]S×N
+ → R
is a continuous function from valuation sequences to real numbers such that α(V)
depends only on the initial sequence V≤n for some n ∈ N
+ called the rank of the
feature, rank(α). For any m ≥ n, we define α(V≤m) in the natural way. We will
often deal with features that have range in [0, 1]; we call these [0, 1]-features.
We write F for the set of all features, Fn for the set of valuation features of
rank ≤ n, and define an F-progression α to be a sequence of features such that
αn ∈ Fn.
The following valuation features find the price of a sentence on a particular day:
Definition 3.4.2 (Price Feature). For each φ ∈ S and n ∈ N
+, we define a price
feature φ
∗n ∈ Fn by the formula
φ
∗n
(V) := Vn(φ).
We call these “price features” because they will almost always be applied to a market
P, in which case φ
∗n gives the price Pn(φ) of φ on day n as a function of P.
Very roughly, trading strategies will be linear combinations of sentences where the
coefficients are valuation features. The set of all valuation features is not computably
enumerable, so we define an expressible subset:
Definition 3.4.3 (Expressible Feature). An expressible feature ξ ∈ F is a
valuation feature expressible by an algebraic expression built from price features φ
∗n
for each n ∈ N
+ and φ ∈ S, rational numbers, addition, multiplication, max(−, −),
and a “safe reciprocation” function max(1, −)
−1
. See Appendix A.2 for more details
and examples. 2
We write EF for the set of all expressible features, EFn for the set of expressible
features of rank ≤ n, and define an EF-progression to be a sequence ξ such that
ξn ∈ EFn.
For those familiar with abstract algebra, note that for each n, EFn is a commutative ring. We will write 2 − φ
∗6
for the function V 7→ 2 − φ
∗6
(V) and so on, in the
usual way. For example, the feature
ξ := max(0, φ∗6 − ψ
∗7
)
checks whether the value of φ on day 6 is higher than the value of ψ on day 7. If so,
it returns the difference; otherwise, it returns 0. If ξ is applied to a market P, and
P6(φ) = 0.5 and P7(ψ) = 0.2, then ξ(P) = 0.3. Observe that rank(ξ) = 7, and that
ξ is continuous.
The reason for the continuity constraint on valuation features is as follows.
Traders will be allowed to use valuation features (which depend on the price history)
to decide how many shares of different sentences to buy and sell. This creates a
delicate situation, because we’ll be constructing a market that has prices which
2. In particular, expressible features are a generalization of arithmetic circuits. The
specific definition is somewhat arbitrary; what matters is that expressible features be (1)
continuous; (2) compactly specifiable in polynomial time; and (3) expressive enough to
identify a variety of inefficiencies in a market.
17
depend on the behavior of certain traders, creating a circular dependency where the
prices depend on trades that depend on the prices.
This circularity is related to classic paradoxes of self-trust. What should be the
price on a paradoxical sentence χ that says “I am true iff my price is less than 50
cents in this market”? If the price is less than 50¢, then χ pays out $1, and traders
can make a fortune buying χ. If the price is 50¢ or higher, then χ pays out $0, and
traders can make a fortune selling χ. If traders are allowed to have a discontinuous
trading strategy—buy χ if P(χ) < 0.5, sell χ otherwise—then there is no way to
find prices that clear the market.
Continuity breaks the circularity, by ensuring that if there’s a price where a
trader buys χ and a price where they sell χ then there’s a price in between where
they neither buy nor sell. In Section 5 we will see that this is sufficient to allow
stable prices to be found, and in Section 4.11 we will see that it is sufficient to
subvert the standard paradoxes of self-reference. The continuity constraint can be
interpreted as saying that the trader has only finite-precision access to the market
prices—they can see the prices, but there is some ε > 0 such that their behavior is
insensitive to an ε shift in prices.
We are almost ready to define trading strategies as a linear combination of
sentences with expressible features as coefficients. However, there is one more
complication. It will be convenient to record not only the amount of shares bought
and sold, but also the amount of cash spent or received. For example, consider again
the market order 3φ − 2ψ. If it is executed on day 7 in a market P, and P7(φ) = 0.4
and P7(ψ) = 0.3, then the cost is 3 · 40¢ − 2 · 30¢ = 60¢. We can record the whole
trade as an affine combination −0.6 + 3φ − 2ψ, which can be read as “the trader
spent 60 cents to buy 3 shares of φ and sell 2 shares of ψ”. Extending this idea to
the case where the coefficients are expressible features, we get the following notion:
Definition 3.4.4 (Trading Strategy). A trading strategy for day n, also called
an n-strategy, is an affine combination of the form
T = c + ξ1φ1 + · · · + ξkφk,
where φ1, . . . , φk are sentences, ξ1, . . . , ξk are expressible features of rank ≤ n, and
c = −
X
i
ξiφi
∗n
is a “cash term” recording the net cash flow when executing a transaction that buys
ξi shares of φi for each i at the prevailing market price. (Buying negative shares
is called “selling”.) We define T[1] to be c, and T[φ] to be the coefficient of φ in T,
which is 0 if φ 6∈ (φ1, . . . , φk).
An n-strategy T can be encoded by the tuples (φ1, . . . φk) and (ξ1, . . . ξk) because
the c term is determined by them. Explicitly, by linearity we have
T = ξ1 · (φ1 − φ1
∗n
) + · · · + ξk · (φk − φk
∗n
),
which means any n-strategy can be written as a linear combination of (φi − φi
∗n
)
terms, each of which means “buy one share of φi at the prevailing price”.
As an example, consider the following trading strategy for day 5:
h
(¬¬φ)
∗5 − φ
∗5
i
·

φ − φ
∗5

+
h
φ
∗5 − (¬¬φ)
∗5
i
·

¬¬φ − (¬¬φ)
∗5

.
This strategy compares the price of φ on day 5 to the price of ¬¬φ on day 5. If the
former is less expensive by δ, it purchases δ shares of φ at the prevailing prices, and
sells δ shares of ¬¬φ at the prevailing prices. Otherwise, it does the opposite. In
short, this strategy arbitrages φ against ¬¬φ, by buying the cheaper one and selling
the more expensive one.
We can now state the key definition of this section:
18
Definition 3.4.5 (Trader). A trader T is a sequence (T1, T2, . . .) where each
Tn is a trading strategy for day n.
We can visualize a trader as a person who gets to see the day n, think for a while,
and then produce a trading strategy for day n, which will observe the history of
market prices up to and including day n and execute a market order to buy and sell
different sentences at the prevailing market prices.
We will often consider the set of efficiently computable traders, which have to
produce their trading strategy in a time polynomial in n. We can visualize e.c.
traders as traders who are computationally limited: each day they get to think for
longer and longer—we can imagine them writing computer programs each morning
that assist them in their analysis of the market prices—but their total runtime may
only grow polynomially in n.
If s := Tn[φ] > 0, we say that T buys s shares of φ on day n, and if s < 0, we
say that T sells |s| shares of φ on day n. Similarly, if d := Tn[1] > 0, we say that T
receives d dollars on day n, and if d < 0, we say that T pays out |d| dollars on day n.
Each trade Tn has value zero according to Pn, regardless of what market P it is
executed in. Clever traders are the ones who make trades that are later revealed by
a deductive process D to have a high worth (e.g., by purchasing shares of provable
sentences when the price is low). As an example, a trader T with a basic grasp of
arithmetic and skepticism about some of the market P’s confident conjectures might
execute the following trade orders on day n:
Table 1: Visualizing markets and trades
Sentence Market prices Trade
φ :↔ 1 + 1 = 2 Pn(φ) = 90¢ Tn[φ] = 4 shares
ψ :↔ 1 + 1 6= 2 Pn(ψ) = 5¢ Tn[ψ] = −3 shares
χ :↔ “Goldbach’s conjecture” Pn(χ) = 98¢ Tn[χ] = −1 share
The net value of the shares bought and sold at these prices would be
4 · 90¢ − 3 · 5¢ − 1 · 98¢ = $2.47,
so if those three sentences were the only sentences bought and sold by Tn, Tn[1]
would be −2.47.
Trade strategies are a special case of affine combinations of sentences:
Definition 3.4.6 (Affine Combination). An F-combination A : S ∪ {1} → F is
an affine expression of the form
A := c + α1φ1 + · · · + αkφk,
where (φ1, . . . , φk) are sentences and (c, α1, . . . , αk) are in F. We define Rcombinations, Q-combinations, and EF-combinations analogously.
We write A[1] for the trailing coefficient c, and A[φ] for the coefficient of φ,
which is 0 if φ 6∈ (φ1, . . . , φk). The rank of A is defined to be the maximum rank
among all its coefficients. Given any valuation V, we abuse notation in the usual
way and define the value of A (according to V) linearly by:
V(A) := c + α1V(φ1) + · · · + αkV(φk).
An F-combination progression is a sequence A of affine combinations where An
has rank ≤ n. An EF-combination progression is defined similarly.
Note that a trade T is an F-combination, and the holdings T(P) from T against
P
P
is a Q-combination. We will use affine combinations to encode the net holdings
i≤n
Ti(P) of a trader after interacting with a market P, and later to encode linear
inequalities that hold between the truth values of different sentences.
19
3.5 Exploitation
We will now define exploitation, beginning with an example. Let L be the language
of PA, and D be a PA-complete deductive process. Consider a market P that assigns
Pn(“1 + 1 = 2”) = 0.5 for all n, and a trader who buys one share of “1 + 1 = 2” each
day. Imagine a reasoner behind the market obligated to buy and sell shares at the
listed prices, who is also obligated to pay out $1 to holders of φ-shares if and when
D says φ. Let t be the first day when “1 + 1 = 2” ∈ Dt. On each day, the reasoner
receives 50¢ from T, but after day t, the reasoner must pay $1 every day thereafter.
They lose 50¢ each day, and T gains 50¢ each day, despite the fact that T never
risked more than $t/2. In cases like these, we say that T exploits P.
With this example in mind, we define exploitation as follows:
Definition 3.5.1 (Exploitation). A trader T is said to exploit a valuation
sequence V relative to a deductive process D if the set of values
n
W
P
i≤n
Ti

V

 


n ∈ N
+, W ∈ PC(Dn)
o
is bounded below, but not bounded above.
Given a world W, the number W(
P
i≤n
Ti(P)) is the value of the trader’s net
holdings after interacting with the market P, where a share of φ is valued at $1 if φ
is true in W and $0 otherwise. The set {W(
P
i≤n
Ti(P)) | n ∈ N
+, W ∈ PC(Dn)} is
the set of all assessments of T’s net worth, across all time, according to worlds that
were propositionally consistent with D at the time. We informally call these plausible
assessments of the trader’s net worth. Using this terminology, Definition 3.5.1 says
that a trader exploits the market if their plausible net worth is bounded below, but
not above.
Roughly speaking, we can imagine that there is a person behind the market who
acts as a market maker, obligated to buy and sell shares at the listed prices. We
can imagine that anyone who sold a φ-share is obligated to pay $1 if and when D
says φ. Then, very roughly, a trader exploits the market if they are able to make
unbounded returns off of a finite investment.
This analogy is illustrative but incomplete—traders can exploit the market even
if they never purchase a sentence that appears in D. For example, let φ and ψ be
two sentences such that (φ ∨ ψ) is provable in PA, but such that neither φ nor ψ is
provable in PA. Consider a trader that bought 10 φ-shares at a price of 20¢ each, and
10 ψ-shares at a price of 30¢ each. Once D says (φ∨ψ), all remaining p.c. worlds will
agree that the portfolio −5 + 10φ + 10ψ has a value of at least +5, despite the fact
that neither φ nor ψ is ever proven. If the trader is allowed to keep buying φ and
ψ shares at those prices, they would exploit the market, despite the fact that they
never buy decidable sentences. In other words, our notion of exploitation rewards
traders for arbitrage, even if they arbitrage between sentences that never “pay out”.
3.6 Main Result
Recall the logical induction criterion:
Definition 3.0.1 (The Logical Induction Criterion). A market P is said to satisfy
the logical induction criterion relative to a deductive process D if there is no
efficiently computable trader T that exploits P relative to D. A market P meeting
this criterion is called a logical inductor over D.
We may now state our main result:
Theorem 3.6.1. For any deductive process D, there exists a computable belief
sequence P satisfying the logical induction criterion relative to D.
20
Proof. In Section 5, we show how to take an arbitrary deductive process D and
construct a computable belief sequence LIA. Theorem 5.4.2 shows that LIA is a
logical inductor relative to the given D.
Definition 3.6.2 (Logical Inductor over Γ). Given a theory Γ, a logical inductor
over a Γ-complete deductive process D is called a logical inductor over Γ.
Corollary 3.6.3. For any recursively axiomatizable theory Γ, there exists a computable belief sequence that is a logical inductor over Γ.
4 Properties of Logical Inductors
Here is an intuitive argument that logical inductors perform good reasoning under
logical uncertainty:
Consider any polynomial-time method for efficiently identifying patterns
in logic. If the market prices don’t learn to reflect that pattern, a clever
trader can use that pattern to exploit the market. Thus, a logical inductor
must learn to identify those patterns.
In this section, we will provide evidence supporting this intuitive argument, by
demonstrating a number of desirable properties possessed by logical inductors. The
properties that we demonstrate are broken into twelve categories:
1. Convergence and Coherence: In the limit, the prices of a logical inductor
describe a belief state which is fully logically consistent, and represents a
probability distribution over all consistent worlds.
2. Timely Learning: For any efficiently computable sequence of theorems, a
logical inductor learns to assign them high probability in a timely manner,
regardless of how difficult they are to prove. (And similarly for assigning low
probabilities to refutable statements.)
3. Calibration and Unbiasedness: Logical inductors are well-calibrated and,
given good feedback, unbiased.
4. Learning Statistical Patterns: If a sequence of sentences appears pseudorandom to all reasoners with the same runtime as the logical inductor, it learns
the appropriate statistical summary (assigning, e.g., 10% probability to the
claim “the nth digit of π is a 7” for large n, if digits of π are actually hard to
predict).
5. Learning Logical Relationships: Logical inductors inductively learn to
respect logical constraints that hold between different types of claims, such as
by ensuring that mutually exclusive sentences have probabilities summing to
at most 1.
6. Non-Dogmatism: The probability that a logical inductor assigns to an
independent sentence φ is bounded away from 0 and 1 in the limit, by an
amount dependent on the complexity of φ. In fact, logical inductors strictly
dominate the universal semimeasure in the limit. This means that we can
condition logical inductors on independent sentences, and when we do, they
perform empirical induction.
7. Conditionals: Given a logical inductor P, the market given by the conditional
probabilities P(− | ψ) is a logical inductor over D extended to include ψ. Thus,
when we condition logical inductors on new axioms, they continue to perform
logical induction.
8. Expectations: Logical inductors give rise to a well-behaved notion of the
expected value of a logically uncertain variable.
21
9. Trust in Consistency: If the theory Γ underlying a logical inductor’s deductive process is expressive enough to talk about itself, then the logical inductor
learns inductively to trust Γ.
10. Reasoning about Halting: If there’s an efficient method for generating
programs that halt, a logical inductor will learn in a timely manner that those
programs halt (often long before having the resources to evaluate them). If
there’s an efficient method for generating programs that don’t halt, a logical
inductor will at least learn not to expect them to halt for a very long time.
11. Introspection: Logical inductors “know what they know”, in that their
beliefs about their current probabilities and expectations are accurate.
12. Self-Trust: Logical inductors trust their future beliefs.
For the sake of brevity, proofs are deferred to Section 6 and the appendix. Some
example proofs are sketched in this section, by outlining discontinuous traders that
would exploit any market that lacked the desired property. The deferred proofs
define polynomial-time continuous traders that approximate those discontinuous
strategies.
In what follows, let L be a language of propositional logic; let S be the set of
sentences written in L; let Γ ⊂ S be a computably enumerable set of propositional
formulas written in L (such as PA, where the propositional variables are prime
sentences in first-order logic, as discussed in Section 2); and let P be a computable
logical inductor over Γ, i.e., a market satisfying the logical induction criterion
relative to some Γ-complete deductive process D. We assume in this section that Γ
is consistent.
Note that while the computable belief sequence LIA that we define has finite
support on each day, in this section we assume only that P is a market. We do this
because our results below hold in this more general case, and can be applied to LIA
as a special case.
In sections 4.8-4.12 we will assume that Γ can represent computable functions.
This assumption is not necessary until Section 4.8.
4.1 Convergence and Coherence
Firstly, the market prices of a logical inductor converge:
Theorem 4.1.1 (Convergence). The limit P∞ : S → [0, 1] defined by
P∞(φ) := limn→∞Pn(φ)
exists for all φ.
Proof sketch. (Proof in: 6.1 or B.4.)
Roughly speaking, if P never makes up its mind about φ, then it can be
exploited by a trader arbitraging shares of φ across different days. More
precisely, suppose by way of contradiction that the limit P∞(φ) does
not exist. Then for some p ∈ [0, 1] and ε > 0, we have Pn(φ) < p − ε
infinitely often and also Pn(φ) > p + ε infinitely often. A trader can wait
until Pn(φ) < p − ε and then buy a share in φ at the low market price of
Pn(φ). Then the trader waits until some later m such that Pm(φ) > p+ε,
and sells back the share in φ at the higher price. This trader makes a
total profit of 2ε every time Pn(φ) oscillates in this way, at no risk, and
therefore exploits P. Since P implements a logical inductor, this is not
possible; therefore the limit P∞(φ) must in fact exist.
This sketch showcases the main intuition for the convergence of P, but elides a
number of crucial details. In particular, the trader we have sketched makes use of
22
discontinuous trading functions, and so is not a well-formed trader. These details
are treated in Section 6.1.
Next, the limiting beliefs of a logical inductor represent a coherent probability
distribution:
Theorem 4.1.2 (Limit Coherence). P∞ is coherent, i.e., it gives rise to an internally
consistent probability measure Pr on the set PC(Γ) of all worlds consistent with Γ,
defined by the formula
Pr(W(φ) = 1) := P∞(φ).
In particular, if Γ contains the axioms of first-order logic, then P∞ defines a probability measure on the set of first-order completions of Γ.
Proof sketch. (Proof in: 6.2 or C.10.)
The limit P∞(φ) exists by the convergence theorem, so Pr is well-defined.
Gaifman (1964) shows that Pr defines a probability measure over PC(D∞)
so long as the following three implications hold for all sentences φ and ψ:
• If Γ ` φ, then P∞(φ) = 1,
• If Γ ` ¬φ, then P∞(φ) = 0,
• If Γ ` ¬(φ ∧ ψ), then P∞(φ ∨ ψ) = P∞(φ) + P∞(ψ).
Let us demonstrate each of these three properties.
First suppose that Γ ` φ, but P∞(φ) = 1−ε for some ε > 0. Then shares
of φ will be underpriced, as they are worth 1 in every consistent world,
but only cost 1 −ε. There is a trader who waits until φ is propositionally
provable from Dn, and until Pn(φ) has approximately converged, and
then starts buying shares of φ every day at the price Pn(φ). Since φ has
appeared in D, the shares immediately have a minimum plausible value
of $1. Thus the trader makes 1 − Pn(φ) ≈ ε profit every day, earning an
unbounded total value, contradicting the logical induction criterion. But
P cannot be exploited, so P∞(φ) must be 1.
Similarly, if Γ ` ¬φ but P∞(φ) = ε > 0, then a trader could exploit P by
selling off shares in φ for a profit of Pn(φ) ≈ ε each day.
Finally, suppose that Γ ` ¬(φ ∧ ψ), but for some ε > 0,
P∞(φ ∨ ψ) = P∞(φ) + P∞(ψ) ± ε.
Then there is a trader that waits until Pn has approximately converged
on these sentences, and until ¬(φ ∧ ψ) is propositionally provable from
Dn. At that point it’s a good deal to sell (buy) a share in φ ∨ ψ, and
buy (sell) a share in each of φ and ψ; the stocks will have values that
cancel out in every plausible world. Thus this trader makes a profit of
≈ ε from the price differential, and can then repeat the process. Thus,
they would exploit P. But this is impossible, so P∞ must be coherent.
Theorem 4.1.2 says that if P were allowed to run forever, and we interpreted its
prices as probabilities, then we would find its beliefs to be perfectly consistent. In
the limit, P assigns probability 1 to every theorem and 0 to every contradiction. On
independent sentences, its beliefs obey the constraints of probability theory; if φ
provably implies ψ, then the probability of ψ converges to a point no lower than the
limiting probability of φ, regardless of whether they are decidable. The resulting
probabilities correspond to a probability distribution over all possible ways that Γ
could be completed.
This justifies interpreting the market prices of a logical inductor as probabilities.
Logical inductors are not the first computable procedure for assigning probabilities
to sentences in a manner that is coherent in the limit; the algorithm of Demski
(2012) also has this property. The main appeal of logical induction is that their
beliefs become reasonable in a timely manner, outpacing the underlying deductive
process.
23
4.2 Timely Learning
It is not too difficult to define a reasoner that assigns probability 1 to all (and only)
the provable sentences, in the limit: simply assign probability 0 to all sentences, and
then enumerate all logical proofs, and assign probability 1 to the proven sentences.
The real trick is to recognize patterns in a timely manner, well before the sentences
can be proven by slow deduction.
Logical inductors learn to outpace deduction on any efficiently computable
sequence of provable statements.3 To illustrate, consider our canonical example
where Dn is the set of all theorems of PA provable in at most n characters, and
suppose φ is an e.c. sequence of theorems which are easy to generate but difficult to
prove. Let f(n) be the length of the shortest proof of φn, and assume that f is some
fast-growing function. At any given time n, the statement φn is ever further out
beyond Dn—it might take 1 day to prove φ1, 10 days to prove φ2, 100 days to prove
φ3, and so on. One might therefore expect that φn will also be “out of reach” for
Pn, and that we have to wait until a much later day close to f(n) before expecting
Pf(n)(φn) to be accurate. However, this is not the case! After some finite time N,
P will recognize the pattern and begin assigning high probability to φ in a timely
manner.
Theorem 4.2.1 (Provability Induction). Let φ be an e.c. sequence of theorems.
Then
Pn(φn) hn 1.
Furthermore, let ψ be an e.c. sequence of disprovable sentences. Then
Pn(ψn) hn 0.
Proof sketch. (Proof in: 6.5 or C.3.)
Consider a trader that acts as follows. First wait until the time a when
Pa(φa) drops below 1 − ε and buy a share of φa. Then wait until φa is
worth 1 in all worlds plausible at time f(a). Then repeat this process.
If Pn(φn) drops below 1 − ε infinitely often, then this trader makes ε
profit infinitely often, off of an initial investment of $1, and therefore
exploits the market. P is inexploitable, so Pn(φn) must converge to 1.
By a similar argument, Pn(ψn) must converge to 0.4
In other words, P will learn to start believing φn by day n at the latest, despite
the fact that φn won’t be deductively confirmed until day f(n), which is potentially
much later. In colloquial terms, if φ is a sequence of facts that can be generated
efficiently, then P inductively learns the pattern, and its belief in φ becomes accurate
faster than D can computationally verify the individual sentences.
For example, imagine that prg(n) is a program with fast-growing runtime, which
always outputs either 0, 1, or 2 for all n, but such that there is no proof of this in
the general case. Then
“∀x: prg(x) = 0 ∨ prg(x) = 1 ∨ prg(x) = 2”
is not provable. Now consider the sequence of statements
prg012 := “prg(n) = 0 ∨ prg(n) = 1 ∨ prg(n) = 2”
n∈N+
where each prg012n states that prg outputs a 0, 1, or 2 on that n in particular.
Each individual prg012n is provable (it can be proven by running prg on input
n), and prg012 is efficiently computable (because the sentences themselves can be
3. Recall that a sequence x is efficiently computable iff there exists a computable function
n 7→ xn with runtime polynomial in n.
4. The traders sketched here are optimized for ease of proof, not for efficiency—a clever
trader trying to profit from low prices on efficiently computable theorems would be able to
exploit the market faster than this.
24
written down quickly, even if prg is very difficult to evaluate). Thus, provability
induction says that any logical inductor will “learn the pattern” and start assigning
high probabilities to each individual prg012n no later than day n.
Imagine that D won’t determine the output of prg(n) until the f(n)th day, by
evaluating prg(n) in full. Provability induction says that P will eventually recognize
the pattern prg012 and start assigning high probability to prg012n no later than
the nth day, f(n) − n days before the evaluation finishes. This is true regardless of
the size of f(n), so if f is fast-growing, P will outpace D by an ever-growing margin.
Analogy: Ramanujan and Hardy. Imagine that the statements
φ are being output by an algorithm that uses heuristics to generate
mathematical facts without proofs, playing a role similar to the famously
brilliant, often-unrigorous mathematician Srinivasa Ramanujan. Then P
plays the historical role of the beliefs of the rigorous G.H. Hardy who
tries to verify those results according to a slow deductive process (D).
After Hardy (P) verifies enough of Ramanujan’s claims (φ≤n), he begins
to trust Ramanujan, even if the proofs of Ramanujan’s later conjectures
are incredibly long, putting them ever-further beyond Hardy’s current
abilities to rigorously verify them. In this story, Hardy’s inductive
reasoning (and Ramanujan’s also) outpaces his deductive reasoning.
This idiom of assigning the right probabilities to φn no later than day n will be
common throughout the paper, so we give it a name.
Definition 4.2.2 (Timely Manner). Let φ be an e.c. sequence of sentences, and p
be an e.c. sequence of rational numbers. We say that P assigns p to φ in a timely
manner if for every ε > 0, there exists a time N such that for all n > N,
|Pn(φn) − pn| < ε.
In other words, P assigns p to φ in a timely manner if
Pn(φn) hn pn.
Note that there are no requirements on how large N gets as a function of ε. As
such, when we say that P assigns probabilities p to φ in a timely manner, it may
take a very long time for convergence to occur. (See Section 5.5 for a discussion.)
As an example, imagine the reasoner who recognizes that sentences of the form
“1 + 1 +· · ·+ 1 is even” are true iff the number of ones is even. Let φ be the sequence
where φn is the version of that sentence with 2n ones. If the reasoner starts writing
a probability near 100% in the φn cell by day n at the latest, then intuitively, she
has begun incorporating the pattern into her beliefs, and we say that she is assigning
high probabilities to φ in a timely manner.
We can visualize ourselves as taking P’s belief states, sorting them by φ on one
axis and days on another, and then looking at the main diagonal of cells, to check
the probability of each φn on day n. Checking the nth sentence on the nth day is a
rather arbitrary choice, and we might hope that a good reasoner would assign high
probabilities to e.c. sequences of theorems at a faster rate than that. It is easy to
show that this is the case, by the closure properties of efficient computability. For
example, if φ is an e.c. sequence of theorems, then so are φ2n and φ2n+1, which each
enumerate half of φ at twice the speed, so by Theorem 4.2.1 (Provability Induction),
P will eventually learn to believe φ at a rate of at least two per day. Similarly, P
will learn to believe φ3n and φn2 and φ10n3+3 in a timely manner, and so on. Thus,
up to polynomial transformations, it doesn’t really matter which diagonal we check
when checking whether a logical inductor has begun “noticing a pattern”.
Furthermore, we will show that if P assigns the correct probability on the main
diagonal, then P also learns to keep them there:
25
Theorem 4.2.3 (Persistence of Knowledge). Let φ be an e.c. sequence of sentences,
and p be an e.c. sequence of rational-number probabilities. If P∞(φn) hn pn, then
sup
m≥n
|Pm(φn) − pn| hn 0.
Furthermore, if P∞(φn) .n pn, then
sup
m≥n
Pm(φn) .n pn,
and if P∞(φn) &n pn, then
inf
m≥n
Pm(φn) &n pn.
(Proof in: B.6.)
In other words, if P assigns p to φ in the limit, then P learns to assign probability
near pn to φn at all times m ≥ n. This theorem paired with the closure properties
of the set of efficiently computable sequences means that checking the probability of
φn on the nth day is a fine way to check whether P has begun recognizing a pattern
encoded by φ. As such, we invite the reader to be on the lookout for statements
of the form Pn(φn) as signs that P is recognizing a pattern, often in a way that
outpaces the underlying deductive process.
Theorems 4.2.1 (Provability Induction) and 4.2.3 (Persistence of Knowledge)
only apply when the pattern of limiting probabilities is itself efficiently computable.
For example, consider the sequence of sentences
πAeq7 := “π[Ack(n, n)] = 7”
n∈N+
where π[i] is the ith digit in the decimal expansion of π and Ack is the Ackermann
function. Each individual sentence is decidable, so the limiting probabilities are 0
for some πAeq7n and 1 for others. But that pattern of 1s and 0s is not efficiently
computable (assuming there is no efficient way to predict the Ackermann digits of
π), so provability induction has nothing to say on the topic.
In cases where the pattern of limiting probabilities are not e.c., we can still show
that if P is going to make its probabilities follow a certain pattern eventually, then it
learns to make its probabilities follow that pattern in a timely manner. For instance,
assume that each individual sentence πAeq7n (for n > 4) is going to spend a long
time sitting at 10% probability before eventually being resolved to either 1 or 0.
Then P will learn to assign Pn(πAeq7n) ≈ 0.1 in a timely manner:
Theorem 4.2.4 (Preemptive Learning). Let φ be an e.c. sequence of sentences.
Then
lim inf
n→∞
Pn(φn) = lim inf
n→∞
sup
m≥n
Pm(φn).
Furthermore,
lim sup
n→∞
Pn(φn) = lim sup
n→∞
inf
m≥n
Pm(φn).
(Proof in: B.3.)
Let’s unpack Theorem 4.2.4. The quantity supm≥n Pm(φn) is an upper bound
on the price Pm(φn) on or after day n, which we can interpret as the highest price
tag that that P will ever put on φn after we first start checking it on day n. We can
imagine a sequence of these values: On day n, we start watching φn. As time goes
on, its price travels up and down until eventually settling somewhere. This happens
for each n. The limit infimum of supm≥n Pm(φn) is the greatest lower bound p past
which a generic φn (for n large) will definitely be pushed after we started watching it.
Preemptive Learning says that if P always eventually pushes φn up to a probability
at least p, then it will learn to assign each φn a probability at least p in a timely
manner (and similarly for least upper bounds).
26
For example, if each individual πAeq7n is eventually recognized as a claim about
digits of π and placed at probability 10% for a long time before being resolved, then
P learns to assign it probability 10% on the main diagonal. In general, if P is going
to learn a pattern eventually, it learns it in a timely manner.
This leaves open the question of whether a logical inductor P is smart enough to
recognize that the πAeq7 should each have probability 10% before they are settled
(assuming the Ackermann digits of π are hard to predict). We will return to that
question in Section 4.4, but first, we examine the reverse question.
4.3 Calibration and Unbiasedness
Theorem 4.2.1 (Provability Induction) shows that logical inductors are good at
detecting patterns in what is provable. Next, we ask: when a logical inductor
learns a pattern, when must that pattern be real? In common parlance, a source of
probabilistic estimates is called well calibrated if among statements where it assigns
a probability near p, the estimates are correct with frequency roughly p.
In the case of reasoning under logical uncertainty, measuring calibration is not
easy. Consider the sequence clusters constructed from correlated clusters of size 1,
10, 100, 1000, . . . , where the truth value of each cluster is determined by the parity
of a late digit of π:
clusters1 :↔“π[Ack(1, 1)] is even”
clusters2 :↔ · · · :↔ clusters11 :↔“π[Ack(2, 2)] is even”
clusters12 :↔ · · · :↔ clusters111 :↔“π[Ack(3, 3)] is even”
clusters112 :↔ · · · :↔ clusters1111 :↔“π[Ack(4, 4)] is even”
and so on. A reasoner who can’t predict the parity of the Ackermann digits of π
should assign 50% (marginal) probability to any individual clustersn for n large. But
consider what happens if the 9th cluster turns out to be true, and the next billion
sentences are all true. A reasoner who assigned 50% to those billion sentences was
assigning the right probabilities, but their calibration is abysmal: on the billionth
day, they have assigned 50% probability a billion sentences that were overwhelmingly
true. And if the 12th cluster comes up false, then on the trillionth day, they have
assigned 50% probability to a trillion sentences that were overwhelmingly false! In
cases like these, the frequency of truth oscillates eternally, and the good reasoner
only appears well-calibrated on the rare days where it crosses 50%.
The natural way to correct for correlations such as these is to check P’s conditional
probabilities instead of its marginal probabilities. This doesn’t work very well in
our setting, because given a logical sentence φ, the quantity that we care about will
almost always be the marginal probability of φ. The reason we deal with sequences
is because that lets us show that φ has reasonable probabilities relative to various
related sentences. For example, if φ := “prg(32) = 17”, then we can use our theorems
to relate the probability of φ to the probability of the sequence (“prg(n) = 17”)n∈N+ ,
and to the sequence (“prg(32) = n”)n∈N+ , and to the sequence (“prg(n) > n”)n∈N+ ,
and so on, to show that φ eventually has reasonable beliefs about prg (hopefully
before P has the resources to simply evaluate prg on input 32). But at the end
of the day, we’ll want to reason about the marginal probability of φ itself. In this
case, approximately-well-calibrated conditional probabilities wouldn’t buy us much:
there are 2
n−1 possible truth assignments to the first n − 1 elements of φ, so if we
try to compute the marginal probability of φn from all the different conditional
probabilities, exponentially many small errors would render the answer useless.
Furthermore, intuitively, if φ is utterly unpredictable to P, then the probabilities
of all the different truth assignments to φ≤n−1 will go to 0 as n gets large, which
means the conditional probabilities won’t necessarily be reasonable. (In Section 4.4
will formalize a notion of pseudorandomness.)
Despite these difficulties, we can recover some good calibration properties on the
marginal probabilities if we either (a) restrict our consideration to sequences where
the average frequency of truth converges; or (b) look at subsequences of φ where P
27
has “good feedback” about the truth values of previous elements of the subsequence,
in a manner defined below.
To state our first calibration property, we will define two different sorts of
indicator functions that will prove useful in many different contexts.
Definition 4.3.1 (Theorem Indicator). Given a sentence φ, define ThmΓ(φ) to be
1 if Γ ` φ and 0 otherwise.
Definition 4.3.2 (Continuous Threshold Indicator). Let δ > 0 be a rational number,
and x and y be real numbers. We then define
Indδ(x > y) :=



0 if x ≤ y
x − y
δ
if y < x ≤ y + δ
1 if y + δ < x.
Notice that Indδ(x > y) has no false positives, and that it is linear in the region
between y and y + δ. We define Indδ(x < y) analogously, and we define
Indδ(a < x < b) := min(Indδ(x > a),Indδ(x < b)).
Observe that we can generalize this definition to the case where x and y are expressible
features, in which case Indδ(x > y) is an expressible [0, 1]-feature.
Now we can state our calibration theorem.
Theorem 4.3.3 (Recurring Calibration). Let φ be an e.c. sequence of decidable
sentences, a and b be rational numbers, δ be an e.c. sequence of positive rational
numbers, and suppose that P
n

Indδi(a < Pi(φi) < b)

i∈N+ = ∞. Then, if the
sequence
 P
i≤n
Indδi(a < Pi(φi) < b) · ThmΓ(φi)
P
i≤n
Indδi
(a < Pi(φi) < b)
!
n∈N+
converges, it converges to a point in [a, b]. Furthermore, if it diverges, it has a limit
point in [a, b]. (Proof in: D.3.)
Roughly, this says that if Pn(φn) ≈ 80% infinitely often, then if we look at the
subsequence where it’s 80%, the limiting frequency of truth on that subsequence is
80% (if it converges).
In colloquial terms, on subsequences where P says 80% and it makes sense to
talk about the frequency of truth, the frequency of truth is 80%, i.e., P isn’t seeing
shadows. If the frequency of truth diverges—as in the case with clusters—then P is
still well-calibrated infinitely often, but its calibration might still appear abysmal at
times (if they can’t predict the swings).
Note that calibration alone is not a very strong property: a reasoner can always
cheat to improve their calibration (i.e., by assigning probability 80% to things
that they’re sure are true, in order to bring up the average truth of their “80%”
predictions). What we really want is some notion of “unbiasedness”, which says that
there is no efficient method for detecting a predictable bias in a logical inductor’s
beliefs. This is something we can get on sequences where the limiting frequency of
truth converges, though again, if the limiting frequency of truth diverges, all we can
guarantee is a limit point.
Definition 4.3.4 (Divergent Weighting). A divergent weighting w ∈ [0, 1]N
+
is
an infinite sequence of real numbers in [0, 1], such that P
n wn = ∞.
Note that divergent weightings have codomain [0, 1] as opposed to {0, 1}, meaning
the weightings may single out fuzzy subsets of the sequence. For purposes of intuition,
imagine that w is a sequence of 0s and 1s, in which case each w can be interpreted as
a subsequence. The constraint that the wn sum to ∞ ensures that this subsequence
is infinite.
28
Definition 4.3.5 (Generable From P). A sequence of rational numbers q is called
generable from P if there exists an e.c. EF-progression q
† such that q
†
n
(P) = qn
for all n. In this case we say that q is P-generable. P-generable R-sequences,
Q-combination sequences, and R-combination sequences are defined analogously.
Divergent weightings generable from P are fuzzy subsequences that are allowed
to depend continuously (via expressible market features) on the market history.
For example, the sequence (Ind0.01(Pn(φn) > 0.5))n∈N+ is a P-generable sequence
that singles out all times n when Pn(φn) is greater than 50%. Note that the set of
P-generable divergent weightings is larger than the set of e.c. divergent weightings,
as the P-generable weightings are allowed to vary continuously with the market
prices.
Theorem 4.3.6 (Recurring Unbiasedness). Given an e.c. sequence of decidable
sentences φ and a P-generable divergent weighting w, the sequence
P
i≤n wi
· (Pi(φi) − ThmΓ(φi))
P
i≤n wi
has 0 as a limit point. In particular, if it converges, it converges to 0.
(Proof in: D.2.)
Letting w = (1, 1, . . .), this theorem says that the difference between the average
probability Pn(φn) and the average frequency of truth is 0 infinitely often (and 0
always, if the latter converges). Letting each wn be Indδ(a < Pn(φn) < b), we recover
Theorem 4.3.3 (Recurring Calibration). In general, the fraction in Theorem 4.3.6
can be interpreted as a measure of the “bias” of P on the fuzzy subsequence of φ
singled out by w. Then this theorem says that P is unbiased on all P-generable
subsequences where the frequency of truth converges (and unbiased infinitely often
on subsequences where it diverges). Thus, if an e.c. sequence of sentences can be
decomposed (by any P-generable weighting) into subsequences where the frequency
of truth converges, then P learns to assign probabilities such that there is no efficient
method for detecting a predictable bias in its beliefs.
However, not every sequence can be broken down into well-behaved subsequences
by a P-generable divergent weighting (if, for example, the truth values move “pseudorandomly” in correlated clusters, as in the case of clusters). In these cases, it
is natural to wonder whether there are any conditions where P will be unbiased
anyway. Below, we show that the bias converges to zero whenever the weighting w
is sparse enough that P can gather sufficient feedback about φn in between guesses:
Definition 4.3.7 (Deferral Function). A function f : N
+ → N+ is called a deferral
function if
1. f(n) > n for all n, and
2. f(n) can be computed in time polynomial in f(n), i.e., if there is some algorithm
and a polynomial function h such that for all n, the algorithm computes f(n)
within h(f(n)) steps.
If f is a deferral function, we say that f defers n to f(n).
Theorem 4.3.8 (Unbiasedness From Feedback). Let φ be any e.c. sequence of
decidable sentences, and w be any P-generable divergent weighting. If there exists a
strictly increasing deferral function f such that the support of w is contained in the
image of f and ThmΓ(φf(n)) is computable in O(f(n + 1)) time, then
P
i≤n wi
· (Pi(φi) − ThmΓ(φi))
P
i≤n wi
hn 0.
In this case, we say “w allows good feedback on φ”. (Proof in: D.5.)
29
In other words, P is unbiased on any subsequence of the data where a polynomialtime machine can figure out how the previous elements of the subsequence turned
out before P is forced to predict the next one. This is perhaps the best we can hope
for: On ill-behaved sequences such as clusters, where the frequency of truth diverges
and (most likely) no polynomial-time algorithm can predict the jumps, the Pn(φn)
might be pure guesswork.
So how well does P perform on sequences like clusters? To answer, we turn to the
question of how P behaves in the face of sequences that it finds utterly unpredictable.
4.4 Learning Statistical Patterns
Consider the digits in the decimal expansion of π. A good reasoner thinking about
the 101,000,000th digit of π, in lieu of any efficient method for predicting the digit
before they must make their prediction, should assign roughly 10% probability
to that digit being a 7. We will now show that logical inductors learn statistical
patterns of this form.
To formalize this claim, we need some way of formalizing the idea that a sequence
is “apparently random” to a reasoner. Intuitively, this notion must be defined
relative to a specific reasoner’s computational limitations. After all, the digits of
π are perfectly deterministic; they only appear random to a reasoner who lacks
the resources to compute them. Roughly speaking, we will define a sequence to be
pseudorandom (relative to P) if there is no e.c. way to single out any one subsequence
that is more likely true than any other subsequence, not even using expressions
written in terms of the market prices (by way of expressible features):
Definition 4.4.1 (Pseudorandom Sequence). Given a set S of divergent weightings
(Definition 4.3.4), a sequence φ of decidable sentences is called pseudorandom
with frequency p over S if, for all weightings w ∈ S,
limn→∞
P
i≤n wi
· ThmΓ(φi)
P
i≤n wi
exists and is equal to p.
Note that if the sequence φ is actually randomly generated (say, by adding (c1, c2, . . .)
to the language of Γ, and tossing a coin weighted with probability p towards heads for
each i, to determine whether to add ci or ¬ci as an axiom) then φ is pseudorandom
with frequency p almost surely.5 Now:
Theorem 4.4.2 (Learning Pseudorandom Frequencies). Let φ be an e.c. sequence
of decidable sentences. If φ is pseudorandom with frequency p over the set of all
P-generable divergent weightings, then
Pn(φn) hn p.
(Proof in: 6.4 or D.8.)
For example, consider again the sequence πAeq7 where the nth element says
that the Ack(n, n)th decimal digit of π is a 7. The individual πAeq7n statements
are easy to write down (i.e., efficiently computable), but each one is difficult to
decide. Assuming there’s no good way to predict the Ackermann digits of π using a
P-generable divergent weighting, P will assign probability 10% to each πAeq7n in a
timely manner, while it waits for the resources to determine whether the sentence is
true or false. Of course, on each individual πAeq7n, P’s probability will go to 0 or 1
eventually, i.e., limm→∞ Pm(πAeq7n) ∈ {0, 1}.
5. Note that actually adding randomness to Γ in this fashion is not allowed, because
we assumed that the axioms of Γ are recursively enumerable. It is possible to construct a
logical inductor that has access to a source of randomness, by adding one bit of randomness
to the market each day, but that topic is beyond the scope of this paper.
30
Theorem 4.4.2 still tells us nothing about how P handles clusters (defined above),
because the frequency of truth in that sequence diverges, so it does not count as
pseudorandom by the above definition. To handle this case we will weaken our
notion of pseudorandomness, so that it includes more sequences, yielding a stronger
theorem. We will do this by allowing sequences to count as pseudorandom so long
as the limiting frequency of truth converges on “independent subsequences” where
the n + 1st element of the subsequence doesn’t come until after the nth element can
be decided, as described below. Refer to Garrabrant, Soares, and Taylor (2016) for
a discussion of why this is a good way to broaden the set of sequences that count as
pseudorandom.
Definition 4.4.3 (f-Patient Divergent Weighting). Let f be a deferral function.
We say that a divergent weighting w is f-patient if there is some constant C such
that, for all n,
f
X
(n)
i=n
wi(P) ≤ C
In other words, w is f-patient if the weight it places between days n and f(n) is
bounded.
While we are at it, we will also strengthen Theorem 4.4.2 in three additional
ways: we will allow the probabilities on the sentences to vary with time, and with
the market prices, and we will generalize hn to &n and .n.
Definition 4.4.4 (Varied Pseudorandom Sequence). Given a deferral function
f, a set S of f-patient divergent weightings, an e.c. sequence φ of Γ-decidable
sentences, and a P-generable sequence p of rational probabilities, φ is called a pvaried pseudorandom sequence (relative to S) if, for all w ∈ S,
P
i≤n wi
· (pi − ThmΓ(φi))
P
i≤n wi
hn 0.
Furthermore, we can replace hn with &n or .n, in which case we say φ is varied
pseudorandom above p or varied pseudorandom below p, respectively.
Theorem 4.4.5 (Learning Varied Pseudorandom Frequencies). Given an e.c. sequence φ of Γ-decidable sentences and a P-generable sequence p of rational probabilities, if there exists some f such that φ is p-varied pseudorandom (relative to all
f-patient P-generable divergent weightings), then
Pn(φn) hn pn.
Furthermore, if φ is varied pseudorandom above or below p, then the hn may be
replaced with &n or .n (respectively). (Proof in: D.7.)
Thus we see that P does learn to assign marginal probabilities Pn(clustersn) ≈ 0.5,
assuming the Ackermann digits of π are actually difficult to predict. Note that while
Theorem 4.4.5 requires each pn to be rational, the fact that the theorem is generalized
to varied pseudorandom above/below sequences means that Theorem 4.4.5 is a strict
generalization of Theorem 4.4.2 (Learning Pseudorandom Frequencies).
In short, Theorem 4.4.5 shows that logical inductors reliably learn in a timely
manner to recognize appropriate statistical patterns, whenever those patterns (which
may vary over time and with the market prices) are the best available method for
predicting the sequence using P-generable methods.
4.5 Learning Logical Relationships
Most of the above properties discuss the ability of a logical inductor to recognize
patterns in a single sequence—for example, they recognize e.c. sequences of theorems
31
in a timely manner, and they fall back on the appropriate statistical summaries in
the face of pseudorandomness. We will now examine the ability of logical inductors
to learn relationships between sequences.
Let us return to the example of the computer program prg which outputs either
0, 1, or 2 on all inputs, but for which this cannot be proven in general by Γ.
Theorem 4.2.1 (Provability Induction) says that the pattern
prg012 := “prg(n) = 0 ∨ prg(n) = 1 ∨ prg(n) = 2”
n∈N+
will be learned, in the sense that P will assign each prg012n a probability near 1 in
a timely manner. But what about the following three individual sequences?
prg0 := “prg(n) = 0”
n∈N+
prg1 := “prg(n) = 1”
n∈N+
prg2 := “prg(n) = 2”
n∈N+
None of the three sequences is a sequence of only theorems, so provability induction
does not have much to say. If they are utterly pseudorandom relative to r, then
Theorem 4.4.5 (Learning Varied Pseudorandom Frequencies) says that P will fall
back on the appropriate statistical summary, but that tells us little in cases where
there are predictable non-conclusive patterns (e.g., if prg(i) is more likely to output
2 when helper(i) outputs 17). In fact, if P is doing good reasoning, the probabilities
on the (prg0n, prg1n, prg2n) triplet ought to shift, as P gains new knowledge about
related facts and updates its beliefs. How could we tell if those intermediate beliefs
were reasonable?
One way is to check their sum. If P believes that prg(i) ∈ {0, 1, 2} and it knows
how disjunction works, then it should be the case that whenever Pn(prg012t) ≈ 1,
Pn(prg0t)+Pn(prg1t)+Pn(prg2t) ≈ 1. And this is precisely the case. In fact, logical
inductors recognize mutual exclusion between efficiently computable tuples of any
size, in a timely manner:
Theorem 4.5.1 (Learning Exclusive-Exhaustive Relationships). Let φ1, . . . , φk be k
e.c. sequences of sentences, such that for all n, Γ proves that φ
1
n
, . . . , φk
n are exclusive
and exhaustive (i.e. exactly one of them is true). Then
Pn(φ
1
n
) + · · · + Pn(φ
k
n
) hn 1.
Proof sketch. (Proof in: C.11.)
Consider the trader that acts as follows. On day n, they check the prices
of φ
1
n
. . . φk
n
. If the sum of the prices is higher (lower) than 1 by some
fixed threshold ε > 0, they sell (buy) a share of each, wait until the
values of the shares are the same in every plausible world, and make a
profit of ε. (It is guaranteed that eventually, in every plausible world
exactly one of the shares will be valued at 1.) If the sum goes above 1 +ε
(below 1 − ε) on the main diagonal infinitely often, this trader exploits
P. Logical inductors are inexploitable, so it must be the case that the
sum of the prices goes to 1 along the main diagonal.
This theorem suggests that logical inductors are good at learning to assign
probabilities that respect logical relationships between related sentences. To show
that this is true in full generality, we will generalize Theorem 4.5.1 to any linear
inequalities that hold between the actual truth-values of different sentences.
First, we define the following convention:
Convention 4.5.2 (Constraint). An R-combination A can be viewed as a constraint, in which case we say that a valuation V satisfies the constraint if V(A) ≥ 0.
32
For example, the constraint
AND := −2 + φ + ψ
says that both φ and ψ are true, and it is satisfied by W iff W(φ) = W(ψ) = 1. As
another example, the pair of constraints
XOR := (1 − φ − ψ, φ + ψ − 1)
say that exactly one of φ and ψ is true, and are satisfied by P7 iff P7(φ) + P7(ψ) = 1.
Definition 4.5.3 (Bounded Combination Sequence). By BCS(P) (mnemonic:
bounded combination sequences) we denote the set of all P-generable Rcombination sequences A that are bounded, in the sense that there exists some
bound b such that kAnk1 ≤ b for all n, where k−k1 includes the trailing coefficient.
Theorem 4.5.4 (Affine Provability Induction). Let A ∈ BCS(P) and b ∈ R. If, for
all consistent worlds W ∈ PC(Γ) and all n ∈ N
+, it is the case that W(An) ≥ b,
then
Pn(An) &n b,
and similarly for = and hn, and for ≤ and .n. (Proof in: C.2.)
For example, consider the constraint sequence
A := 1 − prg0n − prg1n − prg2n

n∈N+
For all n and all consistent worlds W ∈ PC(Γ), the value W(An) is 0, so applying
Theorem 4.5.5 to A, we get that Pn(An) hn 0. By linearity, this means
Pn(prg0n) + Pn(prg1n) + Pn(prg2n) hn 1,
i.e., P learns that the three sequences are mutually exclusive and exhaustive in a
timely manner, regardless of how difficult prg is to evaluate. Affine Provability
Induction is a generalization of this idea, where the coefficients may vary (day by
day, and with the market prices).
We can push this idea further, as follows:
Theorem 4.5.5 (Affine Coherence). Let A ∈ BCS(P). Then
lim inf
n→∞
inf
W∈PC(Γ)
W(An) ≤ lim inf
n→∞
P∞(An) ≤ lim inf
n→∞
Pn(An),
and
lim sup
n→∞
Pn(An) ≤ lim sup
n→∞
P∞(An) ≤ lim sup
n→∞
sup
W∈PC(Γ)
W(An).
(Proof in: C.1.)
This theorem ties the ground truth on A, to the value of A in the limit, to the value
of A on the main diagonal. In words, it says that if all consistent worlds value An in
(a, b) for n large, then P∞ values An in (c, d) ⊆ (a, b) for n large (because P∞ is a
weighted mixture of all consistent worlds), and P learns to assign probabilities such
that Pn(An) ∈ (c, d) in a timely manner. In colloquial terms, P learns in a timely
manner to respect all linear inequalities that actually hold between sentences, so
long as those relationships can be enumerated in polynomial time.
For example, if helper(i)=err always implies prg(i)=0, P will learn this pattern,
and start assigning probabilities to Pn(“prg(n)=0”) which are no lower than those
of Pn(“helper(n)=err”). In general, if a series of sentences obey some complicated
linear inequalities, then so long as those constraints can be written down in polynomial
time, P will learn the pattern, and start assigning probabilities that respect those
constraints in a timely manner.
33
This doesn’t mean that P will assign the correct values (0 or 1) to each sentence
in a timely manner; that would be impossible for a deductively limited reasoner.
Rather, P’s probabilities will start satisfying the constraints in a timely manner. For
example, imagine a set of complex constraints holds between seven sequences, such
that exactly three sentences in each septuplet are true, but it’s difficult to tell which
three. Then P will learn this pattern, and start ensuring that its probabilities on
each septuplet sum to 3, even if it can’t yet assign particularly high probabilities to
the correct three.
If we watch an individual septuplet as P reasons, other constraints will push the
probabilities on those seven sentences up and down. One sentence might be refuted
and have its probability go to zero. Another might get a boost when P discovers
that it’s likely implied by a high-probability sentence. Another might take a hit
when P discovers it likely implies a low-probability sentence. Throughout all this,
Theorem 4.5.5 says that P will ensure that the seven probabilities always sum to ≈ 3.
P’s beliefs on any given day arise from this interplay of many constraints, inductively
learned.
Observe that Affine Coherence is a direct generalization of Theorem 4.2.1 (Provability Induction). One way to interpret this theorem is that it says that P is very
good at learning inductively to predict long-running computations. Given any e.c.
sequence of statements about the computation, if they are true then P learns to
believe them in a timely manner, and if they are false then P learns to disbelieve
them in a timely manner, and if they are related by logical constraints (such as by
exclusivity or implication) to some other e.c. sequence of statements, then P learns
to make its probabilities respect those constraints in a timely manner. This is one of
the main reasons why we think this class of algorithms deserves the name of “logical
inductor”.
Affine Coherence can also be interpreted as an approximate coherence condition
on the finite belief-states of P. It says that if a certain relationship among truth
values is going to hold in the future, then P learns to m
```

</details>

<details>
<summary>💭 Thinking</summary>

 I'm pulling out the critical definitions from the paper. Definition 3.2.1 establishes that a deductive process is a computable nested sequence of finite sentence sets—the key word being "computable," not "efficiently computable." Now I'm looking at Theorem 3.6.1, which appears to be the main result about deductive processes.

The theorem states that for any deductive process D, there exists a computable belief sequence P satisfying the logical induction criterion. This means the existence guarantee applies to any computable deductive process with no efficiency requirement on D itself.

Looking at the other definitions, I see that "efficiently computable" is specifically applied to traders and various sequences with polynomial runtime bounds, while the deductive process and market are just computable. The LI criterion itself prohibits efficiently computable traders from exploiting the market. So the distinction is clear: deductive processes need only be computable, traders must be efficiently computable, and the market is computable but not necessarily efficient.

This settles the question definitively—the deductive process doesn't require efficient computability. Now I'm considering how the universal inductor framing works with Diffractor building a logical inductor over an empty deductive process and then conditioning via the relevant theorem.

The conditioning theorem allows us to take a logical inductor P and form a new market from conditional probabilities P(− | ψ), which is itself a logical inductor over D extended with ψ. When we condition on a growing sequence of sentences, we get a logical inductor over a deductive process where all those conditionals hold true. This is the key mechanism for how the universal inductor handles the sequence of sentences—conditioning preserves the logical induction property across the extended deductive process.

Now I'm realizing that since deductive processes only need to be computable (not necessarily e.c.), we could sidestep the question of whether the conditioning sequence must be e.c. entirely. Instead of relying on closure-under-conditioning and worrying about what properties the conditioning sequence needs, we can view the universal inductor's deductive process as simply including the quote profiles directly. The deductive process remains computable, so the existence theorem still applies regardless of whether the sequence itself is e.c. The key insight is that conditioning an existing market differs fundamentally from constructing a fresh one. When I condition $H$ on $Q_A$, I'm reusing the market structure and taking conditional probabilities—and for theorem 4.7.2 to work, the conditioning sequence must be efficiently computable. The proof relies on showing that an e.c. trader exploiting the conditioned market corresponds to an e.c. trader exploiting the original market, which requires computing the conditioning event itself to preserve the e.c. property. So there's an asymmetry: building a LI over a deductive process only needs computability, but conditioning an existing LI requires efficient computability of the sequence.

Now applying this to Anson's construction: $A$ doesn't need to be a universal inductor (measure) if nothing actually reads a measure off it. Since $A$ only prices the affine combinations $C_n$ to produce prices $a_n = A_n(C_n)$, a plain logical inductor constructed directly via theorem 3.6.1 suffices. And that theorem works for any computable deductive process—well-foundedness guarantees $D_A$ is computable, so there's no efficiency requirement and no cost bound $\sigma \ge R(F(n))$.

The key insight: $H^+$ still needs the cost bound because it's defined by conditioning $H$ on $Q_A$, which is a measure-theoretic operation requiring $H$ itself to be a measure.

But now I'm questioning whether $H^+$ actually needs to be measure-valued at all. The reflection theorems use expectations like $H^+_n(1(P^{(n)}) \cdot \text{Ind}_\delta(Q_n > p_n))$, but plain logical inductors have the LUV extension too, so that doesn't force measure-valued-ness. The conditioning move feels natural from a Bayesian perspective, but I could construct $H^+$ fresh as a plain LI over the deductive process that includes the quote profiles instead.

If I go with fresh construction, then $H^+$ would only need computability of the quote-stream, not efficiency bounds, which means the cost bound $e \ge R(n)$ would disappear entirely. But the conceptual story of the paper is that $H^+$ represents humanity's beliefs updated on the AI's outputs, which suggests $H^+$ should be $H$ conditioned on the quotes rather than built from scratch.

The reflection results depend on this conditioning structure—the trust transferred to the AI comes from $H$'s prior credence about the relationship between the quote atoms ($\beta$) and outcomes, updated by conditioning on the realized quote values. A fresh inductor wouldn't have that inherited structure, so it wouldn't capture the same kind of trust transfer.

This means $H^+$ must be defined through conditioning the measure $H$, which requires $H$ to be measure-valued and triggers the cost bound requirement on the $H^+$ side. By contrast, $A$ is built fresh over its deductive system without conditioning anything, so it can be a plain inductor needing only computability—no cost bound needed there. The asymmetry is fundamental: one side inherits and updates prior beliefs, the other builds from scratch. ful and precise about confidence:

1. **Deductive processes need only be computable, not e.c.** — CONFIRMED from the source. Definition 3.2.1 specifies "a *computable* nested sequence," and Theorem 3.6.1 guarantees that for *any* deductive process D, there exists a computable belief sequence P satisfying the LI criterion. High confidence, ~98%.

2. **The market is computable, not e.c.; only traders are e.c.** — CONFIRMED. Definition 3.1.3 defines the market as a computable sequence, while Definition 3.3.1 and Definition 3.0.1 establish e.c. for traders/sequences. ~98%.

3. **$A$ can be a plain LI over $D_A$ (not a measure/UI), because nothing reads a measure off $A$ — only contract prices $a_n = A_n(C_n)$.** — This is Anson's key insight, and it holds: prices of affine combinations are defined for any market/LI. ~90%.

4. **$D_A$ is computable by well-foundedness, so $A$ exists via Theorem 3.6.1 with NO efficiency/cost requirement on $\sigma$. Hence $\sigma \ge R(F(n))$ is NOT needed; only ordering $F < \sigma$ is required.**

5. The remaining uncertainty centers on whether the conditioning of $H$ (which appears essential for the reflection and trust results) requires e.c. via Theorem 4.7.2 — I haven't yet confirmed the exact statement of 4.7.2 since the fetch ended at §4.5, so this inference is around 75% confident. But on the $H^+$ side, the cost bound is the conservative assumption anyway, so even if 4.7.2 turns out to need only computable, keeping the efficiency requirement is the safer choice.

The key insight for Anson is that the asymmetry resolves cleanly: $A$ is constructed fresh over its deductive process (settlements feed directly into $D_A$), so it benefits from the existence theorem in 3.6.1, which requires only a computable deductive process — no efficiency condition needed. $H^+$, by contrast, is $H$ conditioned on the quotes rather than built from scratch, which is why the trust and reflection results impose the stronger requirement.

This means there's only one cost bound to worry about: $e \ge R(n)$ on the conditioning side. I was wrong about the symmetry earlier — I mistakenly thought $A$ had to be conditioned too because of how Diffractor framed the UI, but it doesn't. The consequential simplification (dropping $\sigma \ge R(F(n))$) is now justified by the deductive-process definition itself.

I still need to verify the exact hypothesis in 4.7.2 about whether the conditioning sequence must be e.c., but that won't change the core action: $e \ge R(n)$ is the conservative, readily satisfiable condition on the side that genuinely needs it. Now I'm checking whether the measure-valued requirement — that $H$ maintains a full probability measure over worlds at each finite stage — creates any constraint on $A$ as well. The conditioning operation on $H$ requires it to be a full measure, which is why $H$ and $H^+$ must be universal inductors, whereas $A$ doesn't undergo conditioning so it can remain a plain logical inductor with finite support. Since $A$ operates over the $\alpha$-extended language and $H^+$ over the $\beta$ language, they're independent — $A$ prices $\alpha$ contracts without needing to assign credences to $\beta$ atoms, so the finite-support property poses no problems. Now I'm organizing the citations — all the key definitions and theorems come from the same section of the LI paper, so I'll reference them together and paraphrase rather than quote directly. I should also acknowledge that I haven't yet verified the exact e.c. requirement from section 4.7.2, but that doesn't affect the core conclusion since the bound I'm using is conservative anyway.

For the draft itself, the main change is simplifying the settlement side to drop the $\sigma$ constraint entirely and focus only on the ordering $F(n) < \sigma(n)$. But now I'm questioning whether the assumption that $R(F(n))$ lives in $\mathcal{C}_A$'s capability set is actually necessary — computing $Y_n$ just requires simulating $H^+$ to depth $F(n)$, which is computable regardless of what $\mathcal{C}_A$ can do. So I need to figure out what that assumption is really buying us, or whether it can be dropped entirely. that the LI exploitation definition at each stage $n$ measures the trader's net worth against worlds in $\text{PC}(D_n)$, and the settlement resolves once it enters $D_{\sigma(n)}$ — so $D_A$ just needs to be computable for the machinery to work. The $R(F(n)) \in \mathcal{C}_A$ assumption might actually serve a different purpose than what was originally stated, since the deductive resolution happens regardless of whether the settlement function is in $\mathcal{C}_A$.

But there's likely a subtle role lurking here: the cost bound $e \ge R(n)$ requires $R(n)$ to be dominated by some $\mathcal{C}_H$-computable schedule that $H^+$ can efficiently check (comparing $e(i) < t$ rather than computing $e(i)$ fully), and for such a dominating schedule to exist, $R$ needs to be bounded by a $\mathcal{C}_A$-computable function — which is what the power assumption ensures. So the residual role is keeping $R$ tame enough that a readable publication schedule exists, not about enabling the settlement resolution itself.

</details>

You're right, and the paper settles it — in your favor, against the symmetry I claimed last turn.

Two definitions do the work:

- A deductive process is required only to be *computable*. Definition 3.2.1 defines a deductive process as a computable nested sequence of finite sets of sentences — no efficiency qualifier. Efficiency (poly-time in $n$) is reserved for *traders* and for the various e.c. sequences, not for the process itself.
- The existence theorem carries no efficiency hypothesis on the process: for any deductive process, there exists a computable belief sequence satisfying the logical induction criterion relative to it (Theorem 3.6.1).

So if $A$ is built directly as a logical inductor over $D_A$ — not as a bitstring inductor *conditioned* on $D_A$ — then $A$ exists for *any computable* $D_A$, and well-foundedness already hands you computability of $D_A$ (each $Y_n$ is a strictly-earlier-stage object). No efficiency, no budget, no $\sigma \ge R(F(n))$. The settlement side collapses to pure ordering $F(n) < \sigma(n)$, which is exactly what you were pushing toward.

And nothing forces $A$ to be the measure-valued (universal) kind. The only output of $A$ that anything reads is the price $a_n = A_n(C_n)$ of an affine combination of $\alpha$-atoms — a plain market gives you that by linearity. The settlements enter through $A$'s *deductive process*, not by conditioning a prior. So $A$ can be a vanilla LIA-style inductor with finite support per day, built fresh. ✓

The asymmetry is real, and here's why I shouldn't have symmetrized it:

- **$A$ is built fresh** over $D_A$ → rides Theorem 3.6.1 → needs only $D_A$ computable.
- **$H^+$ is not built fresh** — it's $H$ *conditioned* on $Q_A$, and it has to be (~80% on this being the load-bearing reason): the transferred-trust results come from updating $H$'s prior joint beliefs about (quote, outcome), and a fresh inductor over $\Gamma$+quotes wouldn't carry $H$'s prior. Conditioning a *measure* is the operation — which is precisely why $H$ has to be a universal (measure-valued) inductor, since you can't measure-theoretically condition a finite-support belief state. And conditioning is the step that (via the trader reduction) wants the conditioning sequence efficiently computable, so the cost bound $e \ge R(n)$ lives there and only there.

So: one cost condition, on $e$. My "matched pair" last turn was wrong — I let Diffractor's "a UI just *is* a conditioned bitstring inductor" framing trick me into assuming $A$ must be conditioned too. It needn't be a UI at all, and the instant it's a plain LI, the conditioning theorem and its e.c. demand stop touching it.

Edits this implies:

- Settlement side: keep $F(n)<\sigma(n)$ only. Delete $\sigma \ge R(F(n))$, and revert the lemma's "$D_A$ efficiently computable" to "$D_A$ computable."
- "More powerful reasoner": $\mathcal{C}_A \ni R(F(n))$ is no longer doing existence work (well-foundedness handles that). Its surviving job is to keep $R$ a tame, $\mathcal{C}_A$-bounded function so a dominating publication schedule $e$ exists for the one cost bound. Restate it that way rather than "so the bets can resolve."
- $e$ side unchanged: $e \ge R(n)$, with $e$ readable by $H^+$ (so $e(i)<t$ is $\mathcal{C}_H$-decidable).

Honest gap: this pull stopped around §4.5, so I've confirmed the cheap side (deductive processes are merely computable → $A$ is fine) but not the verbatim hypothesis of 4.7.2 on the $H^+$ side. That changes no action — $e \ge R(n)$ is the conservative, free-to-satisfy condition, and the consequential simplification, dropping the $\sigma$ bound, is the one now nailed by Definition 3.2.1. Confidence that $A$-as-plain-LI is sound and $\sigma\ge R(F(n))$ can go: ~85%, anchored on those two definitions rather than on memory.


## Human
*2026-06-09 18:50 UTC*

So we are requiring that H's deductive process is computable right because we're conditioning U on it


## Assistant
*2026-06-09 18:54 UTC*

<details>
<summary>💭 Thinking</summary>

 I'm working through the specifics of how the base reasoner $H$ is constructed, particularly focusing on whether its deductive process $D_H$ needs to be computable. The setup involves taking a logical inductor over an empty deductive process with traders from $\mathcal{C}_H$, and I need to clarify what constraints this places on $D_H$. reckoning with a parallel structure: $H$ is defined by conditioning $U$ on $D_H$, just like $H^+$ is defined by conditioning $H$ on $Q_A$. So if $H^+$ requires $Q_A$ to be efficiently computable because of the conditioning operation, shouldn't $H$ require $D_H$ to be efficiently computable for the same reason? Yet the draft specifies only that $D_H$ is computable, not efficiently computable — so I'm wondering if there's a genuine gap in the reasoning or if "computable" is actually sufficient in this context.

Let me work through what the closure-under-conditioning theorem actually demands. When we condition $U$ on a sequence of sentences to get $H = U \mid D_H$, the conditioning sequence itself needs to satisfy certain properties for $H$ to qualify as a logical inductor.

The key question is whether this requires $D_H$ to be efficiently computable or just computable. The Diffractor construction takes the base bitstring inductor and conditions it on $D_H$, but I need to figure out if that's using the sequence-conditioning from 4.7.2 (which seems to require efficient computability) or if there's a separate notion of conditioning on a deductive process that might have weaker requirements. Wait, I need to double-check whether Theorem 4.7.2 actually requires efficient computability or just plain computability. I inferred the efficiency requirement from the trader-reduction argument, but I haven't actually verified it against the source material. There's also another angle to consider: in the LI paper, the deductive process itself is computable, and the base existence theorem works for any computable deductive process. When conditioning on a sequence of non-inconsistent sentences, the resulting logical inductor operates over an extended deductive process—so the question becomes whether that extended process needs to be efficiently computable or merely computable.

The crux is what 4.7.2's hypothesis actually demands. If it requires efficient computability of the conditioning sequence relative to the trader class, then both $H = U \mid D_H$ and $H^+ = H \mid Q_A$ would need their respective conditioning sequences to be efficiently computable. That would mean the draft's statement about "computable $D_H$" is too weak—it should specify "$\mathcal{C}_H$-computable" instead. But if 4.7.2 only requires plain computability, then the asymmetry between the two constructions might not hold as I thought.

The trader-reduction argument seems to hinge on whether constructing an efficiently computable trader $T$ from an efficiently computable trader $T'$ actually requires the conditioning sequence to be efficiently computable, or if plain computability suffices. I need to trace through that construction more carefully to see if my reasoning about the cost bounds was justified. The draft should specify that $D_H$ needs to be $\mathcal{C}_H$-computable (efficiently computable relative to the budget), not merely computable, precisely because we're conditioning $U$ on it — the same reasoning that applies to the conditioning sequence itself. Anson's question is pointing out this parallel, and the answer is that the computability requirement stems from conditioning, but conditioning demands efficient computability, not just plain computability. So the measure-valued property is actually what forces $D_H$ to be efficiently computable — since $H$ must be built by conditioning $U$ to get that universal property, and conditioning via 4.7.2 requires the conditioning sequence itself to be efficiently computable relative to $\mathcal{C}_H$. The draft's weaker "computable" requirement misses this constraint that flows from the measure-valued requirement on $H$.

The elegant part is that $D_H$ and $Q_A$ are structurally identical — both are conditioning sequences fed into 4.7.2, so whatever regularity 4.7.2 demands of one applies to the other. They're linked: if $Q_A$ needs efficient computability and the $e \ge R(n)$ bound, then $D_H$ must satisfy the same, and vice versa.

But there's a practical wrinkle: $D_H$ represents the human's actual deductive process — theorems proven incrementally, empirical observations accumulated over time. In principle it should be efficiently computable naturally, but when I think about what that means concretely — like enumerating PA theorems provable in at most $n$ characters — that requires checking all proofs up to length $n$, which is exponential in $n$. So the question becomes whether that's actually efficient enough for the framework's purposes. So either the conditioning requirement in 4.7.2 only demands computability rather than efficient computability, or there's a different mechanism at play — and the fact that Diffractor explicitly conditions on the proven-theorems deductive process (which is computable but not efficiently computable) suggests the former. Let me reconsider how the bitstring inductor $U$ itself is constructed in Diffractor's framework. when the conditioning event is only computable. The key insight is that in the LI framework, the deductive process $D$ is part of the world itself, not something the trader needs to compute—it's revealed over time as part of the environment. The trader is efficiently computable and interacts with market prices; the deductive process is given to everyone as part of the setup, so the trader doesn't need to compute it from scratch in polynomial time. This means exploitation is measured against the deductive process as an environmental feature, not as a computational burden on the trader.

For conditioning on $D_H$, the conditioned market $H = U \mid D_H$ is computable because computing each price $H_t$ requires computing $U_t$ (which is computable as a LI), computing $D_H^t$ (which is computable as a deductive process), and then the conditional—all of which are computable operations. So $H$ itself is a computable market and preserves the LI criterion. The remaining question is whether the trader reduction works: if an efficiently computable trader $T'$ exploits $H$, can we build an efficiently computable trader $T$ that exploits $U$? The issue is that $T$ needs to compute $D_H^t$ to convert $T'$'s strategy, and if computing the deductive process isn't polynomial-time, the reduction breaks down. Let me step back and be honest about what I actually know here. I don't have the exact statement of 4.7.2, and I've hit a real tension: the canonical deductive process (proven theorems up to n characters) is computable but doesn't seem to be poly-time e.c., yet Diffractor conditions on such processes. So either conditioning only requires computability, or there's something about the notion of "efficiently computable relative to $\mathcal{C}$" that I'm missing, or the deductive process is e.c. in some way I haven't grasped, or 4.7.2's hypothesis is just computability. The key insight is that Anson's logic holds: the requirement on $D_H$ comes from conditioning $U$ on it, just as the requirement on $Q_A$ comes from conditioning $H$ on it. They're the same kind of object — conditioning sequences for 4.7.2 — so whatever 4.7.2 demands, it demands of both identically. They're a linked pair. I should flag this genuine uncertainty rather than keep going in circles.

The real stakes are clear: if 4.7.2 only needs computable, then $Q_A$ only needs computable too, and the $e \ge R(n)$ cost bound drops entirely — the whole construction needs only ordering and computability, no cost conditions. If 4.7.2 needs e.c., then both $D_H$ and $Q_A$ need e.c. ($\mathcal{C}_H$-computable), and the bound stays. The genuinely useful answer is that Anson's question reveals $D_H$ and $Q_A$ are governed by the identical requirement, so the draft should state them consistently, and reading 4.7.2's hypothesis directly will determine which case holds.

This simplifies the mental model significantly: there's really one question (what does 4.7.2 require of a conditioning sequence?), and its answer cascades to $D_H$, $Q_A$, and whether the $e$ cost bound exists at all. Meanwhile $A$ is settled — it needs only computable $D_A$ since it's built fresh, not conditioned. I should fetch §4.7 to resolve this, but the PDF extraction is finicky and my last fetch stopped at §4.5 with a 42000 token limit. I could try again with a larger limit to reach §4.7, but web_fetch doesn't let me jump to a specific page, so I'd have to extract from the beginning again.

Actually, I'm noticing something decisive: the canonical deductive process the paper presents (PA theorems provable in ≤ n characters) is computable but not efficiently computable — finding all such theorems requires exponential time in n, not polynomial. Yet Diffractor explicitly conditions $U$ on exactly this kind of process to build UIs. If 4.7.2 required conditioning sequences to be efficiently computable, this wouldn't work, contradicting the paper's own framework. So 4.7.2 must allow merely-computable conditioning sequences, which means $Q_A$ needs only computable too, and the $e \ge R(n)$ cost bound I've been insisting on would drop entirely. Everything would reduce to ordering and computability, no cost conditions anywhere.

This is a big swing, so I should verify by fetching §4.7 to read the actual hypothesis of the conditioning theorem rather than assert it based on contextual evidence alone.

</details>

Good — this is the same conditioning move as $H^+ = H \mid Q_A$, just one level down. Let me confirm the exact hypothesis rather than reason from the trader-reduction again, because there's a clue in the paper that cuts against what I told you about $e$.

<details>
<summary>⚙️ Tool call: <code>web_fetch</code></summary>

```json
{
  "text_content_token_limit": 68000,
  "url": "https://intelligence.org/files/LogicalInduction.pdf",
  "web_fetch_pdf_extract_text": true
}
```

</details>

<details>
<summary>⚙️ Tool result: <code>web_fetch</code></summary>

```
Logical Induction
Scott Garrabrant, Tsvi Benson-Tilsen, Andrew Critch, Nate Soares, and Jessica Taylor
{scott,tsvi,critch,nate,jessica}@intelligence.org
Machine Intelligence Research Institute
Abstract
We present a computable algorithm that assigns probabilities to every logical
statement in a given formal language, and refines those probabilities over time.
For instance, if the language is Peano arithmetic, it assigns probabilities to
all arithmetical statements, including claims about the twin prime conjecture,
the outputs of long-running computations, and its own probabilities. We show
that our algorithm, an instance of what we call a logical inductor, satisfies
a number of intuitive desiderata, including: (1) it learns to predict patterns
of truth and falsehood in logical statements, often long before having the
resources to evaluate the statements, so long as the patterns can be written
down in polynomial time; (2) it learns to use appropriate statistical summaries
to predict sequences of statements whose truth values appear pseudorandom;
and (3) it learns to have accurate beliefs about its own current beliefs, in a
manner that avoids the standard paradoxes of self-reference. For example, if
a given computer program only ever produces outputs in a certain range, a
logical inductor learns this fact in a timely manner; and if late digits in the
decimal expansion of π are difficult to predict, then a logical inductor learns
to assign ≈ 10% probability to “the nth digit of π is a 7” for large n. Logical
inductors also learn to trust their future beliefs more than their current beliefs,
and their beliefs are coherent in the limit (whenever φ → ψ, P∞(φ) ≤ P∞(ψ),
and so on); and logical inductors strictly dominate the universal semimeasure
in the limit.
These properties and many others all follow from a single logical induction
criterion, which is motivated by a series of stock trading analogies. Roughly
speaking, each logical sentence φ is associated with a stock that is worth $1
per share if φ is true and nothing otherwise, and we interpret the belief-state
of a logically uncertain reasoner as a set of market prices, where Pn(φ) = 50%
means that on day n, shares of φ may be bought or sold from the reasoner for
50¢. The logical induction criterion says (very roughly) that there should not
be any polynomial-time computable trading strategy with finite risk tolerance
that earns unbounded profits in that market over time. This criterion bears
strong resemblance to the “no Dutch book” criteria that support both expected
utility theory (von Neumann and Morgenstern 1944) and Bayesian probability
theory (Ramsey 1931; de Finetti 1937).
Contents
1 Introduction 4
1.1 Desiderata for Reasoning under Logical Uncertainty . . . . . . . . . 5
1.2 Related Work . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 9
1.3 Overview . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 11
See https://intelligence.org/files/LogicalInductionAbridged.pdf for an abridged version of
this paper.
1
2 Notation 12
3 The Logical Induction Criterion 14
3.1 Markets . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 14
3.2 Deductive Processes . . . . . . . . . . . . . . . . . . . . . . . . . . . 15
3.3 Efficient Computability . . . . . . . . . . . . . . . . . . . . . . . . . 16
3.4 Traders . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 17
3.5 Exploitation . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 20
3.6 Main Result . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 20
4 Properties of Logical Inductors 21
4.1 Convergence and Coherence . . . . . . . . . . . . . . . . . . . . . . . 22
4.2 Timely Learning . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 24
4.3 Calibration and Unbiasedness . . . . . . . . . . . . . . . . . . . . . . 27
4.4 Learning Statistical Patterns . . . . . . . . . . . . . . . . . . . . . . 30
4.5 Learning Logical Relationships . . . . . . . . . . . . . . . . . . . . . 31
4.6 Non-Dogmatism . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 35
4.7 Conditionals . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 38
4.8 Expectations . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 39
4.9 Trust in Consistency . . . . . . . . . . . . . . . . . . . . . . . . . . . 42
4.10 Reasoning about Halting . . . . . . . . . . . . . . . . . . . . . . . . . 44
4.11 Introspection . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 45
4.12 Self-Trust . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 47
5 Construction 49
5.1 Constructing MarketMaker . . . . . . . . . . . . . . . . . . . . . . . 50
5.2 Constructing Budgeter . . . . . . . . . . . . . . . . . . . . . . . . . 52
5.3 Constructing TradingFirm . . . . . . . . . . . . . . . . . . . . . . . 54
5.4 Constructing LIA . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 57
5.5 Questions of Runtime and Convergence Rates . . . . . . . . . . . . . 57
6 Selected Proofs 58
6.1 Convergence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 58
6.2 Limit Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 60
6.3 Non-dogmatism . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 62
6.4 Learning Pseudorandom Frequencies . . . . . . . . . . . . . . . . . . 64
6.5 Provability Induction . . . . . . . . . . . . . . . . . . . . . . . . . . . 67
7 Discussion 67
7.1 Applications . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 67
7.2 Analysis . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 68
7.3 Variations . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 70
7.4 Open Questions . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 71
7.5 Acknowledgements . . . . . . . . . . . . . . . . . . . . . . . . . . . . 73
References 73
A Preliminaries 79
A.1 Organization of the Appendix . . . . . . . . . . . . . . . . . . . . . . 79
A.2 Expressible Features . . . . . . . . . . . . . . . . . . . . . . . . . . . 79
A.3 Definitions . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 81
B Convergence Proofs 82
B.1 Return on Investment . . . . . . . . . . . . . . . . . . . . . . . . . . 82
B.2 Affine Preemptive Learning . . . . . . . . . . . . . . . . . . . . . . . 88
B.3 Preemptive Learning . . . . . . . . . . . . . . . . . . . . . . . . . . . 91
B.4 Convergence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 92
B.5 Persistence of Affine Knowledge . . . . . . . . . . . . . . . . . . . . . 92
B.6 Persistence of Knowledge . . . . . . . . . . . . . . . . . . . . . . . . 95
2
C Coherence Proofs 95
C.1 Affine Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 95
C.2 Affine Provability Induction . . . . . . . . . . . . . . . . . . . . . . . 97
C.3 Provability Induction . . . . . . . . . . . . . . . . . . . . . . . . . . . 97
C.4 Belief in Finitistic Consistency . . . . . . . . . . . . . . . . . . . . . 97
C.5 Belief in the Consistency of a Stronger Theory . . . . . . . . . . . . 98
C.6 Disbelief in Inconsistent Theories . . . . . . . . . . . . . . . . . . . . 98
C.7 Learning of Halting Patterns . . . . . . . . . . . . . . . . . . . . . . 98
C.8 Learning of Provable Non-Halting Patterns . . . . . . . . . . . . . . 98
C.9 Learning not to Anticipate Halting . . . . . . . . . . . . . . . . . . . 98
C.10 Limit Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 99
C.11 Learning Exclusive-Exhaustive Relationships . . . . . . . . . . . . . 99
D Statistical Proofs 99
D.1 Affine Recurring Unbiasedness . . . . . . . . . . . . . . . . . . . . . 99
D.2 Recurring Unbiasedness . . . . . . . . . . . . . . . . . . . . . . . . . 102
D.3 Simple Calibration . . . . . . . . . . . . . . . . . . . . . . . . . . . . 102
D.4 Affine Unbiasedness From Feedback . . . . . . . . . . . . . . . . . . 103
D.5 Unbiasedness From Feedback . . . . . . . . . . . . . . . . . . . . . . 104
D.6 Learning Pseudorandom Affine Sequences . . . . . . . . . . . . . . . 105
D.7 Learning Varied Pseudorandom Frequencies . . . . . . . . . . . . . . 106
D.8 Learning Pseudorandom Frequencies . . . . . . . . . . . . . . . . . . 107
E Expectations Proofs 107
E.1 Consistent World LUV Approximation Lemma . . . . . . . . . . . . 107
E.2 Mesh Independence Lemma . . . . . . . . . . . . . . . . . . . . . . . 108
E.3 Expectation Preemptive Learning . . . . . . . . . . . . . . . . . . . . 109
E.4 Expectations Converge . . . . . . . . . . . . . . . . . . . . . . . . . . 110
E.5 Limiting Expectation Approximation Lemma . . . . . . . . . . . . . 110
E.6 Persistence of Expectation Knowledge . . . . . . . . . . . . . . . . . 110
E.7 Expectation Coherence . . . . . . . . . . . . . . . . . . . . . . . . . . 111
E.8 Expectation Provability Induction . . . . . . . . . . . . . . . . . . . 111
E.9 Linearity of Expectation . . . . . . . . . . . . . . . . . . . . . . . . . 111
E.10 Expectations of Indicators . . . . . . . . . . . . . . . . . . . . . . . . 112
E.11 Expectation Recurring Unbiasedness . . . . . . . . . . . . . . . . . . 112
E.12 Expectation Unbiasedness From Feedback . . . . . . . . . . . . . . . 112
E.13 Learning Pseudorandom LUV Sequences . . . . . . . . . . . . . . . . 113
F Introspection and Self-Trust Proofs 113
F.1 Introspection . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 113
F.2 Paradox Resistance . . . . . . . . . . . . . . . . . . . . . . . . . . . . 114
F.3 Expectations of Probabilities . . . . . . . . . . . . . . . . . . . . . . 115
F.4 Iterated Expectations . . . . . . . . . . . . . . . . . . . . . . . . . . 115
F.5 Expected Future Expectations . . . . . . . . . . . . . . . . . . . . . 115
F.6 No Expected Net Update . . . . . . . . . . . . . . . . . . . . . . . . 116
F.7 No Expected Net Update under Conditionals . . . . . . . . . . . . . 116
F.8 Self-Trust . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 117
G Non-Dogmatism and Closure Proofs 118
G.1 Parametric Traders . . . . . . . . . . . . . . . . . . . . . . . . . . . . 118
G.2 Uniform Non-Dogmatism . . . . . . . . . . . . . . . . . . . . . . . . 119
G.3 Occam Bounds . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 122
G.4 Non-Dogmatism . . . . . . . . . . . . . . . . . . . . . . . . . . . . . 123
G.5 Domination of the Universal Semimeasure . . . . . . . . . . . . . . . 123
G.6 Strict Domination of the Universal Semimeasure . . . . . . . . . . . 125
G.7 Closure under Finite Perturbations . . . . . . . . . . . . . . . . . . . 126
G.8 Conditionals on Theories . . . . . . . . . . . . . . . . . . . . . . . . . 127
3
1 Introduction
Every student of mathematics has experienced uncertainty about conjectures for
which there is “quite a bit of evidence”, such as the Riemann hypothesis or the twin
prime conjecture. Indeed, when Zhang (2014) proved a bound on the gap between
primes, we were tempted to increase our credence in the twin prime conjecture. But
how much evidence does this bound provide for the twin prime conjecture? Can we
quantify the degree to which it should increase our confidence?
The natural impulse is to appeal to probability theory in general and Bayes’
theorem in particular. Bayes’ theorem gives rules for how to use observations to
update empirical uncertainty about unknown events in the physical world. However,
probability theory lacks the tools to manage uncertainty about logical facts.
Consider encountering a computer connected to an input wire and an output
wire. If we know what algorithm the computer implements, then there are two
distinct ways to be uncertain about the output. We could be uncertain about the
input—maybe it’s determined by a coin toss we didn’t see. Alternatively, we could
be uncertain because we haven’t had the time to reason out what the program
does—perhaps it computes the parity of the 87,653rd digit in the decimal expansion
of π, and we don’t personally know whether it’s even or odd.
The first type of uncertainty is about empirical facts. No amount of thinking in
isolation will tell us whether the coin came up heads. To resolve empirical uncertainty
we must observe the coin, and then Bayes’ theorem gives a principled account of
how to update our beliefs.
The second type of uncertainty is about a logical fact, about what a known
computation will output when evaluated. In this case, reasoning in isolation can and
should change our beliefs: we can reduce our uncertainty by thinking more about π,
without making any new observations of the external world.
In any given practical scenario, reasoners usually experience a mix of both
empirical uncertainty (about how the world is) and logical uncertainty (about what
that implies). In this paper, we focus entirely on the problem of managing logical
uncertainty. Probability theory does not address this problem, because probabilitytheoretic reasoners cannot possess uncertainty about logical facts. For example,
let φ stand for the claim that the 87,653rd digit of π is a 7. If this claim is true,
then (1 + 1 = 2) ⇒ φ. But the laws of probability theory say that if A ⇒ B then
Pr(A) ≤ Pr(B). Thus, a perfect Bayesian must be at least as sure of φ as they are
that 1 + 1 = 2! Recognition of this problem dates at least back to Good (1950).
Many have proposed methods for relaxing the criterion Pr(A) ≤ Pr(B) until such
a time as the implication has been proven (see, e.g, the work of Hacking [1967] and
Christiano [2014]). But this leaves open the question of how probabilities should be
assigned before the implication is proven, and this brings us back to the search for a
principled method for managing uncertainty about logical facts when relationships
between them are suspected but unproven.
We propose a partial solution, which we call logical induction. Very roughly,
our setup works as follows. We consider reasoners that assign probabilities to
sentences written in some formal language and refine those probabilities over time.
Assuming the language is sufficiently expressive, these sentences can say things
like “Goldbach’s conjecture is true” or “the computation prg on input i produces
the output prg(i)=0”. The reasoner is given access to a slow deductive process
that emits theorems over time, and tasked with assigning probabilities in a manner
that outpaces deduction, e.g., by assigning high probabilities to sentences that are
eventually proven, and low probabilities to sentences that are eventually refuted,
well before they can be verified deductively. Logical inductors carry out this task in
a way that satisfies many desirable properties, including:
1. Their beliefs are logically consistent in the limit as time approaches infinity.
2. They learn to make their probabilities respect many different patterns in logic,
at a rate that outpaces deduction.
3. They learn to know what they know, and trust their future beliefs, while
avoiding paradoxes of self-reference.
4
These claims (and many others) will be made precise in Section 4.
A logical inductor is any sequence of probabilities that satisfies our logical
induction criterion, which works roughly as follows. We interpret a reasoner’s
probabilities as prices in a stock market, where the probability of φ is interpreted
as the price of a share that is worth $1 if φ is true, and $0 otherwise (similar to
Beygelzimer, Langford, and Pennock [2012]). We consider a collection of stock
traders who buy and sell shares at the market prices, and define a sense in which
traders can exploit markets that have irrational beliefs. The logical induction
criterion then says that it should not be possible to exploit the market prices using
any trading strategy that can be generated in polynomial-time.
Our main finding is a computable algorithm which satisfies the logical induction
criterion, plus proofs that a variety of different desiderata follow from this criterion.
The logical induction criterion can be seen as a weakening of the “no Dutch
book” criterion that Ramsey (1931) and de Finetti (1937) used to support standard
probability theory, which is analogous to the “no Dutch book” criterion that von
Neumann and Morgenstern (1944) used to support expected utility theory. Under
this interpretation, our criterion says (roughly) that a rational deductively limited
reasoner should have beliefs that can’t be exploited by any Dutch book strategy
constructed by an efficient (polynomial-time) algorithm. Because of the analogy, and
the variety of desirable properties that follow immediately from this one criterion,
we believe that the logical induction criterion captures a portion of what it means to
do good reasoning about logical facts in the face of deductive limitations. That said,
there are clear drawbacks to our algorithm: it does not use its resources efficiently;
it is not a decision-making algorithm (i.e., it does not “think about what to think
about”); and the properties above hold either asymptotically (with poor convergence
bounds) or in the limit. In other words, our algorithm gives a theoretically interesting
but ultimately impractical account of how to manage logical uncertainty.
1.1 Desiderata for Reasoning under Logical Uncertainty
For historical context, we now review a number of desiderata that have been
proposed in the literature as desirable features of “good reasoning” in the face of
logical uncertainty. A major obstacle in the study of logical uncertainty is that
it’s not clear what would count as a satisfactory solution. In lieu of a solution, a
common tactic is to list desiderata that intuition says a good reasoner should meet.
One can then examine them for patterns, relationships, and incompatibilities. A
multitude of desiderata have been proposed throughout the years; below, we have
collected a variety of them. Each is stated in its colloquial form; many will be stated
formally and studied thoroughly later in this paper.
Desideratum 1 (Computable Approximability). The method for assigning probabilities to logical claims (and refining them over time) should be computable.
(See Section 5 for our algorithm.)
A good method for refining beliefs about logic can never be entirely finished, because a
reasoner can always learn additional logical facts by thinking for longer. Nevertheless,
if the algorithm refining beliefs is going to have any hope of practicality, it should at
least be computable. This idea dates back at least to Good (1950), and has been
discussed in depth by Hacking (1967) and Eells (1990), among others.
Desideratum 1 may seem obvious, but it is not without its teeth. It rules out
certain proposals, such as that of Hutter et al. (2013), which has no computable
approximation (Sawin and Demski 2013).
Desideratum 2 (Coherence in the Limit). The belief state that the reasoner is
approximating better and better over time should be logically consistent.
(Discussed in Section 4.1.)
First formalized by Gaifman (1964), the idea of Desideratum 2 is that the belief
state that the reasoner is approximating—the beliefs they would have if they had
infinite time to think—should be internally consistent. This means that, in the limit
5
of reasoning, a reasoner should assign Pr(φ) ≤ Pr(ψ) whenever φ ⇒ ψ, and they
should assign probability 1 to all theorems and 0 to all contradictions, and so on.
Desideratum 3 (Approximate Coherence). The belief state of the reasoner should
be approximately coherent. For example, if the reasoner knows that two statements
are mutually exclusive, then it should assign probabilities to those sentences that sum
to no more than 1, even if it cannot yet prove either sentence.
(Discussed in sections 4.2 and 4.5.)
Being coherent in the limit is desirable, but good deductively limited reasoning
requires approximate coherence at finite times. Consider two claims about a particular computation prg, which takes a number n as input and produces a number
prg(n) as output. Assume the first claim says prg(7)=0, and the second says
prg(7)=1. Clearly, these claims are mutually exclusive, and once a reasoner realizes
this fact, they should assign probabilities to the two claims that sum to at most 1,
even before they can evaluate prg(7). Limit coherence does not guarantee this: a
reasoner could assign bad probabilities (say, 100% to both claims) right up until they
can evaluate prg(7), at which point they start assigning the correct probabilities.
Intuitively, a good reasoner should be able to recognize the mutual exclusivity before
they’ve proven either claim. In other words, a good reasoner’s beliefs should be
approximately coherent.
Desideratum 3 dates back to at least Good (1950), who proposes a weakening of
the condition of coherence that could apply to the belief states of limited reasoners.
Hacking (1967) proposes an alternative weakening, as do Garrabrant, Fallenstein,
et al. (2016).
Desideratum 4 (Learning of Statistical Patterns). In lieu of knowledge that bears
on a logical fact, a good reasoner should assign probabilities to that fact in accordance
with the rate at which similar claims are true. (Discussed in Section 4.4.)
For example, a good reasoner should assign probability ≈ 10% to the claim “the
nth digit of π is a 7” for large n (assuming there is no efficient way for a reasoner to
guess the digits of π for large n). This desideratum dates at least back to Savage
(1967), and seems clearly desirable. If a reasoner thought the 10100th digit of π
was almost surely a 9, but had no reason for believing this, we would be suspicious
of their reasoning methods. Desideratum 4 is difficult to state formally; for two
attempts, refer to Garrabrant, Benson-Tilsen, et al. (2016) and Garrabrant, Soares,
and Taylor (2016).
Desideratum 5 (Calibration). Good reasoners should be well-calibrated. That is,
among events that a reasoner says should occur with probability p, they should in
fact occur about p proportion of the time. (Discussed in Section 4.3.)
Calibration as a desirable property dates back to Pascal, and perhaps farther.
If things that a reasoner says should happen 30% of the time actually wind up
happening 80% of the time, then they aren’t particularly reliable.
Desideratum 6 (Non-Dogmatism). A good reasoner should not have extreme beliefs
about mathematical facts, unless those beliefs have a basis in proof.
(Discussed in Section 4.6.)
It would be worrying to see a mathematical reasoner place extreme confidence in
a mathematical proposition, without any proof to back up their belief. The virtue
of skepticism is particularly apparent in probability theory, where Bayes’ theorem
says that a probabilistic reasoner can never update away from “extreme” (0 or 1)
probabilities. Accordingly, Cromwell’s law (so named by the statistician Lindley
[1991]) says that a reasonable person should avoid extreme probabilities except
when applied to statements that are logically true or false. We are dealing with
logical uncertainty, so it is natural to extend Cromwell’s law to say that extreme
probabilities should also be avoided on logical statements, except in cases where
the statements have been proven true or false. In settings where reasoners are able
6
to update away from 0 or 1 probabilities, this means that a good reasoner’s beliefs
shouldn’t be “stuck” at probability 1 or 0 on statements that lack proofs or disproofs.
In the domain of logical uncertainty, Desideratum 6 can be traced back to Carnap
(1962, Sec. 53), and has been demanded by many, including Gaifman and Snir (1982)
and Hutter et al. (2013).
Desideratum 7 (Uniform Non-Dogmatism). A good reasoner should assign a nonzero probability to any computably enumerable consistent theory (viewed as a limit
of finite conjunctions). (Discussed in Section 4.6.)
For example the axioms of Peano arithmetic are computably enumerable, and if we
construct an ever-growing conjunction of these axioms, we can ask that the limit
of a reasoner’s credence in these conjunctions converge to a value bounded above
0, even though there are infinitely many conjuncts. The first formal statement of
Desideratum 7 that we know of is given by Demski (2012), though it is implicitly
assumed whenever asking for a set of beliefs that can reason accurately about
arbitrary arithmetical claims (as is done by, e.g., Savage [1967] and Hacking [1967]).
Desideratum 8 (Universal Inductivity). Given enough time to think, the beliefs of
a good reasoner should dominate the universal semimeasure.
(Discussed in Section 4.6.)
Good reasoning in general has been studied for quite some time, and reveals some
lessons that are useful for the study of good reasoning under deductive limitation.
Solomonoff (1964a, 1964b), Zvonkin and Levin (1970), and Li and Vitányi (1993) have
given a compelling formal treatment of good reasoning assuming logical omniscience
in the domain of sequence prediction, by describing an inductive process (known as
a universal semimeasure) with a number of nice properties, including (1) it assigns
non-zero prior probability to every computable sequence of observations; (2) it
assigns higher prior probability to simpler hypotheses; and (3) it predicts as well or
better than any computable predictor, modulo a constant amount of error. Alas,
universal semimeasures are uncomputable; nevertheless, they provide a formal model
of what it means to predict sequences well, and we can ask logically uncertain
reasoners to copy those successes. For example, we can ask that they would perform
as well as a universal semimeasure if given enough time to think.
Desideratum 9 (Approximate Bayesianism). The reasoner’s beliefs should admit
of some notion of conditional probabilities, which approximately satisfy both Bayes’
theorem and the other desiderata listed here. (Discussed in Section 4.7.)
Bayes’ rule gives a fairly satisfying account of how to manage empirical uncertainty
in principle (as argued extensively by Jaynes [2003]), where beliefs are updated by
conditioning a probability distribution. As discussed by Good (1950) and Glymour
(1980), creating a distribution that satisfies both coherence and Bayes’ theorem
requires logical omniscience. Still, we can ask that the approximation schemes
used by a limited agent be approximately Bayesian in some fashion, while retaining
whatever good properties the unconditional probabilities have.
Desideratum 10 (Introspection). If a good reasoner knows something, she should
also know that she knows it. (Discussed in Section 4.11.)
Proposed by Hintikka (1962), this desideratum is popular among epistemic logicians.
It is not completely clear that this is a desirable property. For instance, reasoners
should perhaps be allowed to have “implicit knowledge” (which they know without
knowing that they know it), and it’s not clear where the recursion should stop
(do you know that you know that you know that you know that 1 = 1?). This
desideratum has been formalized in many different ways; see Christiano et al. (2013)
and Campbell-Moore (2015) for a sample.
Desideratum 11 (Self-Trust). A good reasoner thinking about a hard problem
should expect that, in the future, her beliefs about the problem will be more accurate
than her current beliefs. (Discussed in Section 4.12.)
7
Stronger than self-knowledge is self-trust—a desideratum that dates at least back to
Hilbert (1902), when mathematicians searched for logics that placed confidence in
their own machinery. While Gödel, Kleene, and Rosser (1934) showed that strong
forms of self-trust are impossible in a formal proof setting, experience demonstrates
that human mathematicians are capable of trusting their future reasoning, relatively
well, most of the time. A method for managing logical uncertainty that achieves
this type of self-trust would be highly desirable.
Desideratum 12 (Approximate Inexploitability). It should not be possible to run
a Dutch book against a good reasoner in practice. (See Section 3 for our proposal.)
Expected utility theory and probability theory are both supported in part by “Dutch
book” arguments which say that an agent is rational if (and only if) there is no way
for a clever bookie to design a “Dutch book” which extracts arbitrary amounts of
money from the reasoner (von Neumann and Morgenstern 1944; de Finetti 1937).
As noted by Eells (1990), these constraints are implausibly strong: all it takes to
run a Dutch book according to de Finetti’s formulation is for the bookie to know a
logical fact that the reasoner does not know. Thus, to avoid being Dutch booked by
de Finetti’s formulation, a reasoner must be logically omniscient.
Hacking (1967) and Eells (1990) call for weakenings of the Dutch book constraints,
in the hopes that reasoners that are approximately inexploitable would do good
approximate reasoning. This idea is the cornerstone of our framework—in particular,
we consider reasoners that cannot be exploited in polynomial time, using a formalism
defined below. See Definition 3.0.1 for details.
Desideratum 13 (Gaifman Inductivity). Given a Π1 statement φ (i.e., a universal
generalization of the form “for every x, ψ”), as the set of examples the reasoner has
seen goes to “all examples”, the reasoner’s belief in φ should approach certainty.
(Discussed below.)
Proposed by Gaifman (1964), Desideratum 13 states that a reasoner should “generalize well”, in the sense that as they see more instances of a universal claim (such
as “for every x, ψ(x) is true”) they should eventually believe the universal with
probability 1. Desideratum 13 has been advocated by Hutter et al. (2013).
Desideratum 14 (Efficiency). The algorithm for assigning probabilities to logical
claims should run efficiently, and be usable in practice. (Discussed in Section 7.1.)
One goal of understanding “good reasoning” in the face of logical uncertainty is
to design algorithms for reasoning using limited computational resources. For
that, the algorithm for assigning probabilities to logical claims needs to be not
only computable, but efficient. Aaronson (2013) gives a compelling argument that
solutions to logical uncertainty require understanding complexity theory, and this
idea is closely related to the study of bounded rationality (Simon 1982) and efficient
meta-reasoning (Russell and Wefald 1991b).
Desideratum 15 (Decision Rationality). The algorithm for assigning probabilities
to logical claims should be able to target specific, decision-relevant claims, and
it should reason about those claims as efficiently as possible given the computing
resources available. (Discussed in Section 7.4.)
This desideratum dates at least back to Savage (1967), who asks for an extension to
probability theory that takes into account the costs of thinking. For a method of
reasoning under logical uncertainty to aid in the understanding of good bounded
reasoning, it must be possible for an agent to use the reasoning system to reason
efficiently about specific decision-relevant logical claims, using only enough resources
to refine the probabilities well enough for the right decision to become clear. This
desideratum blurs the line between decision-making and logical reasoning; see Russell
and Wefald (1991a) and Hay et al. (2012) for a discussion.
Desideratum 16 (Answers Counterpossible Questions). When asked questions
about contradictory states of affairs, a good reasoner should give reasonable answers.
(Discussed in Section 7.4.)
8
In logic, the principle of explosion says that from a contradiction, anything follows.
By contrast, when human mathematicians are asked counterpossible questions,
such as “what would follow from Fermat’s last theorem being false?”, they often
give reasonable answers, such as “then there would exist non-modular elliptic
curves”, rather than just saying “anything follows from a contradiction”. Soares and
Fallenstein (2015) point out that some deterministic decision-making algorithms
reason about counterpossible questions (“what would happen if my deterministic
algorithm had the output a vs b vs c?”). The topic of counterpossibilities has been
studied by philosophers including Cohen (1990), Vander Laan (2004), Brogaard
and Salerno (2007), Krakauer (2012), and Bjerring (2014), and it is reasonable to
hope that a good logically uncertain reasoner would give reasonable answers to
counterpossible questions.
Desideratum 17 (Use of Old Evidence). When a bounded reasoner comes up with
a new theory that neatly describes anomalies in the old theory, that old evidence
should count as evidence in favor of the new theory. (Discussed in Section 7.4.)
The problem of old evidence is a longstanding problem in probability theory (Glymour
1980). Roughly, the problem is that a perfect Bayesian reasoner always uses all
available evidence, and keeps score for all possible hypotheses at all times, so no
hypothesis ever gets a “boost” from old evidence. Human reasoners, by contrast,
have trouble thinking up good hypotheses, and when they do, those new hypotheses
often get a large boost by retrodicting old evidence. For example, the precession of
the perihelion of Mercury was known for quite some time before the development of
the theory of General Relativity, and could not be explained by Newtonian mechanics,
so it was counted as strong evidence in favor of Einstein’s theory. Garber (1983) and
Jeffrey (1983) have speculated that a solution to the problem of logical omniscience
would shed light on solutions to the problem of old evidence.
Our solution does not achieve all these desiderata. Doing so would be impossible;
Desiderata 1, 2, and 13 cannot be satisfied simultaneously. Further, Sawin and
Demski (2013) have shown that Desiderata 1, 6, 13, and a very weak form of 2
are incompatible; an ideal belief state that is non-dogmatic, Gaifman inductive,
and coherent in a weak sense has no computable approximation. Our algorithm is
computably approximable, approximately coherent, and non-dogmatic, so it cannot
satisfy 13. Our algorithm also fails to meet 14 and 15, because while our algorithm
is computable, it is purely inductive, and so it does not touch upon the decision
problem of thinking about what to think about and how to think about it with
minimal resource usage. As for 16 and 17, the case is interesting but unclear; we
give these topics some treatment in Section 7.
Our algorithm does satisfy desiderata 1 through 12. In fact, our algorithm is
designed to meet only 1 and 12, from which 2-11 will all be shown to follow. This is
evidence that our logical induction criterion captures a portion of what it means
to manage uncertainty about logical claims, analogous to how Bayesian probability
theory is supported in part by the fact that a host of good properties follow from a
single criterion (“don’t be exploitable by a Dutch book”). That said, there is ample
room to disagree about how well our algorithm achieves certain desiderata, e.g. when
the desiderata is met only in the asymptote, or with error terms that vanish only
slowly.
1.2 Related Work
The study of logical uncertainty is an old topic. It can be traced all the way back
to Bernoulli, who laid the foundations of statistics, and later Boole (1854), who
was interested in the unification of logic with probability from the start. Refer
to Hailperin (1996) for a historical account. Our algorithm assigns probabilities
to sentences of logic directly; this thread can be traced back through Łoś (1955)
and later Gaifman (1964), who developed the notion of coherence that we use in
this paper. More recently, that thread has been followed by Demski (2012), whose
framework we use, and Hutter et al. (2013), who define a probability distribution
9
on logical sentences that is quite desirable, but which admits of no computable
approximation (Sawin and Demski 2013).
The objective of our algorithm is to manage uncertainty about logical facts (such
as facts about mathematical conjectures or long-running computer programs). When
it comes to the problem of developing formal tools for manipulating uncertainty,
our methods are heavily inspired by Bayesian probability theory, and so can be
traced back to Pascal, who was followed by Bayes, Laplace, Kolmogorov (1950),
Savage (1954), Carnap (1962), and Jaynes (2003), and many others. Polya (1990)
was among the first in the literature to explicitly study the way that mathematicians
engage in plausible reasoning, which is tightly related to the object of our study.
We are interested in the subject of what it means to do “good reasoning” under
logical uncertainty. In this, our approach is quite similar to the approach of Ramsey
(1931), de Finetti (1937), von Neumann and Morgenstern (1944), Teller (1973),
Lewis (1999), and Joyce (1999), who each developed axiomatizations of rational
behavior and produced arguments supporting those axioms. In particular, they
each supported their proposals with Dutch book arguments, and those Dutch book
arguments were a key inspiration for our logical induction criterion.
The fact that using a coherent probability distribution requires logical omniscience
(and is therefore unsatisfactory when it comes to managing logical uncertainty) dates
at least back to Good (1950). Savage (1967) also recognized the problem, and stated a
number of formal desiderata that our solution in fact meets. Hacking (1967) addressed
the problem by discussing notions of approximate coherence and weakenings of the
Dutch book criteria. While his methods are ultimately unsatisfactory, our approach
is quite similar to his in spirit.
The flaw in Bayesian probability theory was also highlighted by Glymour (1980),
and dubbed the “problem of old evidence” by Garber (1983) in response to Glymor’s
criticism. Eells (1990) gave a lucid discussion of the problem, revealed flaws in
Garber’s arguments and in Hacking’s solution, and named a number of other
desiderata which our algorithm manages to satisfy. Refer to Zynda (1995) and
Sprenger (2015) for relevant philosophical discussion in the wake of Eells. Of note
is the treatment of Adams (1996), who uses logical deduction to reason about an
unknown probability distribution that satisfies certain logical axioms. Our approach
works in precisely the opposite direction: we use probabilistic methods to create an
approximate distribution where logical facts are the subject.
Straddling the boundary between philosophy and computer science, Aaronson
(2013) has made a compelling case that computational complexity must play a role
in answering questions about logical uncertainty. These arguments also provided
some inspiration for our approach, and roughly speaking, we weaken the Dutch book
criterion of standard probability theory by considering only exploitation strategies
that can be constructed by a polynomial-time machine. The study of logical
uncertainty is also tightly related to the study of bounded rationality (Simon 1982;
Russell and Wefald 1991a; Rubinstein 1998; Russell 2016).
Fagin and Halpern (1987) also straddled the boundary between philosophy and
computer science with early discussions of algorithms that manage uncertainty in the
face of resource limitations. (See also their discussions of uncertainty and knowledge
[Fagin et al. 1995; Halpern 2003].) This is a central topic in the field of artificial
intelligence (AI), where scientists and engineers have pursued many different paths
of research. The related work in this field is extensive, including (but not limited to)
work on probabilistic programming (Vajda 1972; McCallum, Schultz, and Singh 2009;
Wood, Meent, and Mansinghka 2014; De Raedt and Kimmig 2015); probabilistic
inductive logic programming (Muggleton and Watanabe 2014; De Raedt and Kersting
2008; De Raedt 2008; Kersting and De Raedt 2007); and meta-reasoning (Russell and
Wefald 1991b; Zilberstein 2008; Hay et al. 2012). The work most closely related to our
own is perhaps the work of Thimm (2013a) and others on reasoning using inconsistent
knowledge bases, a task which is analogous to constructing an approximately coherent
probability distribution. (See also Muiño [2011], Thimm [2013b], Potyka and Thimm
[2015], and Potyka [2015].) Our framework also bears some resemblance to the
Markov logic network framework of Richardson and Domingos (2006), in that both
algorithms are coherent in the limit. Where Markov logic networks are specialized
10
to individual restricted domains of discourse, our algorithm reasons about all logical
sentences. (See also Kok and Domingos [2005], Singla and Domingos [2005], Tran
and Davis [2008], Lowd and Domingos [2007], Mihalkova, Huynh, and Mooney [2007],
Wang and Domingos [2008], and Khot et al. [2015].)
In that regard, our algorithm draws significant inspiration from Solomonoff’s
theory of inductive inference (Solomonoff 1964a, 1964b) and the developments on
that theory made by Zvonkin and Levin (1970) and Li and Vitányi (1993). Indeed,
we view our algorithm as a Solomonoff-style approach to the problem of reasoning
under logical uncertainty, and as a result, our algorithm bears a strong resemblance
to many algorithms that are popular methods for practical statistics and machine
learning; refer to Opitz and Maclin (1999) and Dietterich (2000) for reviews of
popular and successful ensemble methods. Our approach is also similar in spirit
to the probabilistic numerics approach of Briol, Oates, Girolami, Osborne, and
Sejdinovic (2015), but where probabilistic numerics is concerned with algorithms
that give probabilistic answers to individual particular numerical questions, we are
concerned with algorithms that assign probabilities to all queries in a given formal
language. (See also [Briol, Oates, Girolami, and Osborne 2015; Hennig, Osborne,
and Girolami 2015].)
Finally, our method of interpreting beliefs as prices and using prediction markets
to generate reasonable beliefs bears heavy resemblance to the work of Beygelzimer,
Langford, and Pennock (2012) who use similar mechanisms to design a learning
algorithm that bets on events. Our results can be seen as an extension of that idea
to the case where the events are every sentence written in some formal language, in
a way that learns inductively to predict logical facts while avoiding the standard
paradoxes of self-reference.
The work sampled here is only a small sample of the related work, and it neglects
contributions from many other fields, including but not limited to epistemic logic
(Gärdenfors 1988; Meyer and Van Der Hoek 1995; Schlesinger 1985; Sowa 1999;
Guarino 1998), game theory (Rantala 1979; Hintikka 1979; Bacharach 1994; Lipman
1991; Battigalli and Bonanno 1999; Binmore 1992), paraconsistent logic (Blair and
Subrahmanian 1989; Priest 2002; Mortensen 2013; Fuhrmann 2013; Akama and
Costa 2016) and fuzzy logic (Klir and Yuan 1995; Yen and Langari 1999; Gerla
2013). The full history is too long and rich for us to do it justice here.
1.3 Overview
Our main result is a formalization of Desideratum 12 above, which we call the logical
induction criterion, along with a computable algorithm that meets the criterion,
plus proofs that formal versions of Desiderata 2-11 all follow from the criterion.
In Section 2 we define some notation. In Section 3 we state the logical induction
criterion and our main theorem, which says that there exists a computable logical
inductor. The logical induction criterion is motivated by a series of stock trading
analogies, which are also introduced in Section 3.
In Section 4 we discuss a number of properties that follow from this criterion, including properties that hold in the limit, properties that relate to pattern-recognition,
calibration properties, and properties that relate to self-knowledge and self-trust.
A computable logical inductor is described in Section 5. Very roughly, the idea
is that given any trader, it’s possible to construct market prices at which they make
no trades (because they think the prices are right); and given an enumeration of
traders, it’s possible to aggregate their trades into one “supertrader” (which takes
more and more traders into account each day); and thus it is possible to construct a
series of prices which is not exploitable by any trader in the enumeration.
In Section 6 we give a few selected proofs. In Section 7 we conclude with a
discussion of applications of logical inductors, variations on the logical induction
framework, speculation about what makes logical inductors tick, and directions for
future research. The remaining proofs can be found in the appendix.
11
2 Notation
This section defines notation used throughout the paper. The reader is invited to
skim it, or perhaps skip it entirely and use it only as a reference when needed.
Common sets and functions. The set of positive natural numbers is denoted by
N
+, where the superscript makes it clear that 0 is not included. We work with N+
instead of N
≥0 because we regularly consider initial segments of infinite sequences up
to and including the element at index n, and it will be convenient for those lists to
have length n. Sums written P
i≤n
(−) are understood to start at i = 1. We use R to
denote the set of real numbers, and Q to denote the set of rational numbers. When
considering continuous functions with range in Q, we use the subspace topology
on Q inherited from R. We use B to denote the set {0, 1} interpreted as Boolean
values. In particular, Boolean operations like ∧, ∨, ¬, → and ↔ are defined on B,
for example, (1 ∧ 1) = 1, ¬1 = 0, and so on.
We write Fin(X) for the set of all finite subsets of X, and XN
+
for all infinite
sequences with elements in X. In general, we use BA to denote the set of functions
with domain A and codomain B. We treat the expression f : A → B as equivalent
to f ∈ BA, i.e., both state that f is a function that takes inputs from the set A
and produces an output in the set B. We write f : A 7→ B to indicate that f is a
partial function from A to B. We denote equivalence of expressions that represent
functions by ≡, e.g., (x − 1)2 ≡ x
2 − 2x + 1. We write k − k1 for the `1 norm. When
A is an affine combination, kAk1 includes the trailing coefficient.
Logical sentences. We generally use the symbols φ, ψ, χ to denote well-formed
formulas in some language of propositional logic L (such as a theory of first order
logic; see below), which includes the basic logical connectives ¬, ∧, ∨, →, ↔, and
uses modus ponens as its rule of inference. We assume that L has been chosen so
that its sentences can be interpreted as claims about some class of mathematical
objects, such as natural numbers or computer programs. We commonly write S for
the set of all sentences in L, and Γ for a set of axioms from which to write proofs in
the language. We write Γ ` φ when φ can be proven from Γ via modus ponens.
We will write logical formulas inside quotes “−”, such as φ := “x = 3”. The
exception is after `, where we do not write quotes, in keeping with standard
conventions. We sometimes define sentences such as φ := “Goldbach’s conjecture”,
in which case it is understood that the English text could be expanded into a precise
arithmetical claim.
We use underlines to indicate when a symbol in a formula should be replaced
by the expression it stands for. For example, if n := 3, then φ := “x > n” means
φ = “x > 3”, and ψ := “φ → (x = n + 1)” means ψ = “x > 3 → (x = 3 + 1)”. If φ
and ψ denote formulas, then ¬φ denotes “¬(φ)” and φ ∧ ψ denotes “(φ) ∧ (ψ)” and
so on. For instance, if φ := “x > 3” then ¬φ denotes “¬(x > 3)”.
First order theories and prime sentences. We consider any theory in first
order logic (such as Peano Arithmetic, PA) as a set of axioms that includes the
axioms of first order logic, so that modus ponens is the only rule of inference needed
for proofs. As such, we view any first order theory as specified in a propositional
calculus (following Enderton [2001]) whose atoms are the so-called “prime” sentences
of first order logic, i.e., quantified sentences like “∃x: · · · ”, and atomic sentences like
“t1 = t2” and “R(t1, . . . , tn)” where the ti are closed terms. Thus, every first-order
sentence can be viewed as a Boolean combination of prime sentences with logical
connectives (viewing “∀x: · · · ” as shorthand for “¬∃x: ¬ · · · ”). For example, the
sentence
φ := “((1 + 1 = 2) ∧ (∀x: x > 0)) → (∃y : ∀z : (7 > 1 + 1) → (y + z > 2))”
is decomposed into “1 + 1 = 2”, “∃x: ¬(x > 0)” and “∃y : ∀z : (7 > 1 + 1) → (y +z >
2)”, where the leading “¬” in front of the second statement is factored out as a
Boolean operator. In particular, note that while (7 > 1 + 1) is a prime sentence,
it does not occur in the Boolean decomposition of φ into primes, since it occurs
12
within a quantifier. We choose this view because we will not always assume that the
theories we manipulate include the quantifier axioms of first-order logic.
Defining values by formulas. We often view a formula that is free in one variable
as a way of defining a particular number that satisfies that formula. For example,
given the formula X(ν) = “ν
2 = 9 ∧ ν > 0”, we would like to think of X as
representing the unique value “3”, in such a way that that we can then have “5X + 1”
refer to the number 16.
To formalize this, we use the following notational convention. Let X be a formula
free in one variable. We write X(x) for the formula resulting from substituting x for
the free variable of X. If
Γ ` ∃x∀y : X(y) → y = x,
then we say that X defines a unique value (via Γ), and we refer to that value as “the
value” of X. We will be careful in distinguishing between what Γ can prove about
X(ν) on the one hand, and the values of X(ν) in different models of Γ on the other.
If X1, . . . , Xk are all formulas free in one variable that define a unique value
(via Γ), then for any k-place relationship R, we write “R(X1, X2, . . . , Xk)” as an
abbreviation for
“∀x1x2 . . . xk : X1(x1) ∧ X2(x2) ∧ . . . ∧ Xk(xk) → R(x1, x2, . . . , xk)”.
For example, “Z = 2X + Y ” is shorthand for
“∀xyz : X(x) ∧ Y (y) ∧ Z(z) → z = 2x + y”.
This convention allows us to write concise expressions that describe relationships
between well-defined values, even when those values may be difficult or impossible
to determine via computation.
Representing computations. When we say a theory Γ in first order logic “can
represent computable functions”, we mean that its language is used to refer to
computer programs in such a way that Γ satisfies the representability theorem
for computable functions. This means that for every (total) computable function
f : N
+ → N+, there exists a Γ-formula γf with two free variables such that for all
n, y ∈ N
+,
y = f(n) if and only if Γ ` ∀ν : γf (n, ν) ↔ ν = y,
where “γf (n, ν)” stands, in the usual way, for the formula resulting from substituting
an encoding of n and the symbol ν for its free variables. In particular, note that
this condition requires Γ to be consistent.
When Γ can represent computable functions, we use “f(n)” as shorthand for the
formula “γf (n, ν)”. In particular, since “γf (n, ν)” is free in a single variable ν and
defines a unique value, we use “f(n)” by the above convention to write, e.g.,
“f(3) < g(3)”
as shorthand for
“∀xy : γf (3, x) ∧ γg(3, y) → x < y”.
In particular, note that writing down a sentence like “f(3) > 4” does not involve
computing the value f(3); it merely requires writing out the definition of γf . This
distinction is important when f has a very slow runtime.
Sequences. We denote infinite sequences using overlines, like x := (x1, x2, . . .),
where it is understood that xi denotes the ith element of x, for i ∈ N
+. To
define sequences of sentences compactly, we use parenthetical expressions such as
φ := (“n > 7”)n∈N+ , which defines the sequence
(“1 > 7”, “2 > 7”, “3 > 7”, . . .).
13
We define x≤n := (x1, . . . , xn). Given another element y, we abuse notation in the
usual way and define (x≤n, y) = (x1, . . . , xn, y) to be the list x≤n with y appended
at the end. We write () for the empty sequence.
A sequence x is called computable if there is a computable function f such that
f(n) = xn for all n ∈ N
+, in which case we say f computes x.
Asymptotics. Given any sequences x and y, we write
xn hn yn for limn→∞xn − yn = 0,
xn &n yn for lim inf
n→∞
xn − yn ≥ 0, and
xn .n yn for lim sup
n→∞
xn − yn ≤ 0.
3 The Logical Induction Criterion
In this section, we will develop a framework in which we can state the logical
induction criterion and a number of properties possessed by logical inductors. The
framework will culminate in the following definition, and a theorem saying that
computable logical inductors exist for every deductive process.
Definition 3.0.1 (The Logical Induction Criterion). A market P is said to
satisfy the logical induction criterion relative to a deductive process D if
there is no efficiently computable trader T that exploits P relative to D. A
market P meeting this criterion is called a logical inductor over D.
We will now define markets, deductive processes, efficient computability, traders,
and exploitation.
3.1 Markets
We will be concerned with methods for assigning values in the interval [0, 1] to
sentences of logic. We will variously interpret those values as prices, probabilities,
and truth values, depending on the context. Let L be a language of propositional
logic, and let S be the set of all sentences written in L. We then define:
Definition 3.1.1 (Valuation). A valuation is any function V : S → [0, 1]. We
refer to V(φ) as the value of φ according to V. A valuation is called rational if its
image is in Q.
First let us treat the case where we interpret the values as prices.
Definition 3.1.2 (Pricing). A pricing P : S → Q∩[0, 1] is any computable rational
valuation. If P(φ) = p we say that the price of a φ-share according to P is p, where
the intended interpretation is that a φ-share is worth $1 if φ is true.
Definition 3.1.3 (Market). A market P = (P1, P2, . . .) is a computable sequence of pricings Pi
: S → Q ∩ [0, 1].
We can visualize a market as a series of pricings that may change day by day. The
properties proven in Section 4 will apply to any market that satisfies the logical
induction criterion. Theorem 4.1.2 (Limit Coherence) will show that the prices of a
logical inductor can reasonably be interpreted as probabilities, so we will often speak
as if the prices in a market represent the beliefs of a reasoner, where Pn(φ) = 0.75 is
interpreted as saying that on day n, the reasoner assigns 75% probability to φ.
In fact, the logical inductor that we construct in Section 5 has the additional
property of being finite at every timestep, which means we can visualize it as a series
of finite belief states that a reasoner of interest writes down each day.
14
Definition 3.1.4 (Belief State). A belief state P : S → Q ∩ [0, 1] is a computable
rational valuation with finite support, where P(φ) is interpreted as the probability
of φ (which is 0 for all but finitely many φ).
We can visualize a belief state as a finite list of (φ, p) pairs, where the φ are unique
sentences and the p are rational-number probabilities, and P(φ) is defined to be p if
(φ, p) occurs in the list, and 0 otherwise.
Definition 3.1.5 (Computable Belief Sequence). A computable belief sequence
P = (P1, P2, . . .) is a computable sequence of belief states, interpreted as a reasoner’s
explicit beliefs about logic as they are refined over time.
We can visualize a computable belief sequence as a large spreadsheet where each
column is a belief state, and the rows are labeled by an enumeration of all logical
sentences. We can then imagine a reasoner of interest working on this spreadsheet,
by working on one column per day.
Philosophically, the reason for this setup is as follows. Most people know that
the sentence “1 + 1 is even” is true, and that the sentence “1 + 1 + 1 + 1 is even” is
true. But consider, is the following sentence true?
“1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 is even”
To answer, we must pause and count the ones. Since we wish to separate the
question of what a reasoner already knows from what they could infer using further
computing resources, we require that the reasoner write out their beliefs about logic
explicitly, and refine them day by day.
In this framework, we can visualize a reasoner as a person who computes the
belief sequence by filling in a large spreadsheet, always working on the nth column
on the nth day, by refining and extending her previous work as she learns new
facts and takes more sentences into account, while perhaps making use of computer
assistance. For example, a reasoner who has noticed that “1 + · · · + 1 is even” is
true iff the sentence has an even number of ones, might program her computer to
write 1 into as many of the true “1 + · · · + 1 is even” cells per day as it can before
resources run out. As another example, a reasoner who finds a bound on the prime
gap might go back and update her probability on the twin prime conjecture. In our
algorithm, the reasoner will have more and more computing power each day, with
which to construct her next belief state.
3.2 Deductive Processes
We are interested in the question of what it means for reasoners to assign “reasonable probabilities” to statements of logic. Roughly speaking, we will imagine
reasoners that have access to some formal deductive process, such as a community of
mathematicians who submit machine-checked proofs to an official curated database.
We will study reasoners that “outpace” this deductive process, e.g., by assigning
high probabilities to conjectures that will eventually be proven, and low probabilities
to conjectures that will eventually be disproven, well before the relevant proofs are
actually found.
Definition 3.2.1 (Deductive Process). A deductive process D : N
+ →
Fin(S) is a computable nested sequence D1 ⊆ D2 ⊆ D3 . . . of finite sets of
sentences. We write D∞ for the union S
n Dn.
This is a rather barren notion of “deduction”. We will consider cases where we
fix some theory Γ, and Dn is interpreted as the theorems proven up to and including
day n. In this case, D can be visualized as a slow process that reveals the knowledge
of Γ over time. Roughly speaking, we will mainly concern ourselves with the case
where D eventually rules out all and only the worlds that are inconsistent with Γ.
15
Definition 3.2.2 (World). A world is any truth assignment W : S → B. If
W(φ) = 1 we say that φ is true in W. If W(φ) = 0 we say that φ is false in W.
We write W for the set of all worlds.
Observe that worlds are valuations, and that they are not necessarily consistent.
This terminology is nonstandard; the term “world” is usually reserved for consistent
truth assignments. Logically uncertain reasoners cannot immediately tell which
truth assignments are inconsistent, because revealing inconsistencies requires time
and effort. We use the following notion of consistency:
Definition 3.2.3 (Propositional Consistency). A world W is called propositionally consistent, abbreviated p.c., if for all φ ∈ S, W(φ) is determined by Boolean
algebra from the truth values that W assigns to the prime sentences of φ. In other
words, W is p.c. if W(φ ∧ ψ) = W(φ) ∧ W(ψ), W(φ ∨ ψ) = W(φ) ∨ W(ψ), and so on.
Given a set of sentences D, we define PC(D) to be the set of all p.c. worlds where
W(φ) = 1 for all φ ∈ D. We refer to PC(D) as the set of worlds propositionally
consistent with D.
Given a set of sentences Γ interpreted as a theory, we will refer to PC(Γ) as the
set of worlds consistent with Γ, because in this case PC(Γ) is equal to the set of
all worlds W such that
Γ ∪ {φ | W(φ) = 1} ∪ {¬φ | W(φ) = 0} 0 ⊥.
Note that a limited reasoner won’t be able to tell whether a given world W is in
PC(Γ). A reasoner can computably check whether a restriction of W to a finite
domain is propositionally consistent with a finite set of sentences, but that’s about
it. Roughly speaking, the definition of exploitation (below) will say that a good
reasoner should perform well when measured on day n by worlds propositionally
consistent with Dn, and we ourselves will be interested in deductive processes that
pin down a particular theory Γ by propositional consistency:
Definition 3.2.4 (Γ-Complete). Given a theory Γ, we say that a deductive process
D is Γ-complete if
PC(D∞) = PC(Γ).
As a canonical example, let Dn be the set of all theorems of PA provable in at
most n characters.1 Then D is PA-complete, and a reasoner with access to D can
be interpreted as someone who on day n knows all PA-theorems provable in ≤ n
characters, who must manage her uncertainty about other mathematical facts.
3.3 Efficient Computability
We use the following notion of efficiency throughout the paper:
Definition 3.3.1 (Efficiently Computable). An infinite sequence x is called
efficiently computable, abbreviated e.c., if there is a computable function f
that outputs xn on input n, with runtime polynomial in n (i.e. in the length of
n written in unary).
Our framework is not wedded to this definition; stricter notions of efficiency (e.g.,
sequences that can be computed in O(n
2
) time) would yield “dumber” inductors
with better runtimes, and vice versa. We use the set of polynomial-time computable
functions because it has some closure properties that are convenient for our purposes.
1. Because PA is a first-order theory, and the only assumption we made about L is that
it is a propositional logic, note that the axioms of first-order logic—namely, specialization
and distribution—must be included as theorems in D.
16
3.4 Traders
Roughly speaking, traders are functions that see the day n and the history of market
prices up to and including day n, and then produce a series of buy and sell orders,
by executing a strategy that is continuous as a function of the market history.
A linear combination of sentences can be interpreted as a “market order”, where
3φ − 2ψ says to buy 3 shares of φ and sell 2 shares of ψ. Very roughly, a trading
strategy for day n will be a method for producing market orders where the coefficients
are not numbers but functions which depend (continuously) on the market prices
up to and including day n.
Definition 3.4.1 (Valuation Feature). A valuation feature α : [0, 1]S×N
+ → R
is a continuous function from valuation sequences to real numbers such that α(V)
depends only on the initial sequence V≤n for some n ∈ N
+ called the rank of the
feature, rank(α). For any m ≥ n, we define α(V≤m) in the natural way. We will
often deal with features that have range in [0, 1]; we call these [0, 1]-features.
We write F for the set of all features, Fn for the set of valuation features of
rank ≤ n, and define an F-progression α to be a sequence of features such that
αn ∈ Fn.
The following valuation features find the price of a sentence on a particular day:
Definition 3.4.2 (Price Feature). For each φ ∈ S and n ∈ N
+, we define a price
feature φ
∗n ∈ Fn by the formula
φ
∗n
(V) := Vn(φ).
We call these “price features” because they will almost always be applied to a market
P, in which case φ
∗n gives the price Pn(φ) of φ on day n as a function of P.
Very roughly, trading strategies will be linear combinations of sentences where the
coefficients are valuation features. The set of all valuation features is not computably
enumerable, so we define an expressible subset:
Definition 3.4.3 (Expressible Feature). An expressible feature ξ ∈ F is a
valuation feature expressible by an algebraic expression built from price features φ
∗n
for each n ∈ N
+ and φ ∈ S, rational numbers, addition, multiplication, max(−, −),
and a “safe reciprocation” function max(1, −)
−1
. See Appendix A.2 for more details
and examples. 2
We write EF for the set of all expressible features, EFn for the set of expressible
features of rank ≤ n, and define an EF-progression to be a sequence ξ such that
ξn ∈ EFn.
For those familiar with abstract algebra, note that for each n, EFn is a commutative ring. We will write 2 − φ
∗6
for the function V 7→ 2 − φ
∗6
(V) and so on, in the
usual way. For example, the feature
ξ := max(0, φ∗6 − ψ
∗7
)
checks whether the value of φ on day 6 is higher than the value of ψ on day 7. If so,
it returns the difference; otherwise, it returns 0. If ξ is applied to a market P, and
P6(φ) = 0.5 and P7(ψ) = 0.2, then ξ(P) = 0.3. Observe that rank(ξ) = 7, and that
ξ is continuous.
The reason for the continuity constraint on valuation features is as follows.
Traders will be allowed to use valuation features (which depend on the price history)
to decide how many shares of different sentences to buy and sell. This creates a
delicate situation, because we’ll be constructing a market that has prices which
2. In particular, expressible features are a generalization of arithmetic circuits. The
specific definition is somewhat arbitrary; what matters is that expressible features be (1)
continuous; (2) compactly specifiable in polynomial time; and (3) expressive enough to
identify a variety of inefficiencies in a market.
17
depend on the behavior of certain traders, creating a circular dependency where the
prices depend on trades that depend on the prices.
This circularity is related to classic paradoxes of self-trust. What should be the
price on a paradoxical sentence χ that says “I am true iff my price is less than 50
cents in this market”? If the price is less than 50¢, then χ pays out $1, and traders
can make a fortune buying χ. If the price is 50¢ or higher, then χ pays out $0, and
traders can make a fortune selling χ. If traders are allowed to have a discontinuous
trading strategy—buy χ if P(χ) < 0.5, sell χ otherwise—then there is no way to
find prices that clear the market.
Continuity breaks the circularity, by ensuring that if there’s a price where a
trader buys χ and a price where they sell χ then there’s a price in between where
they neither buy nor sell. In Section 5 we will see that this is sufficient to allow
stable prices to be found, and in Section 4.11 we will see that it is sufficient to
subvert the standard paradoxes of self-reference. The continuity constraint can be
interpreted as saying that the trader has only finite-precision access to the market
prices—they can see the prices, but there is some ε > 0 such that their behavior is
insensitive to an ε shift in prices.
We are almost ready to define trading strategies as a linear combination of
sentences with expressible features as coefficients. However, there is one more
complication. It will be convenient to record not only the amount of shares bought
and sold, but also the amount of cash spent or received. For example, consider again
the market order 3φ − 2ψ. If it is executed on day 7 in a market P, and P7(φ) = 0.4
and P7(ψ) = 0.3, then the cost is 3 · 40¢ − 2 · 30¢ = 60¢. We can record the whole
trade as an affine combination −0.6 + 3φ − 2ψ, which can be read as “the trader
spent 60 cents to buy 3 shares of φ and sell 2 shares of ψ”. Extending this idea to
the case where the coefficients are expressible features, we get the following notion:
Definition 3.4.4 (Trading Strategy). A trading strategy for day n, also called
an n-strategy, is an affine combination of the form
T = c + ξ1φ1 + · · · + ξkφk,
where φ1, . . . , φk are sentences, ξ1, . . . , ξk are expressible features of rank ≤ n, and
c = −
X
i
ξiφi
∗n
is a “cash term” recording the net cash flow when executing a transaction that buys
ξi shares of φi for each i at the prevailing market price. (Buying negative shares
is called “selling”.) We define T[1] to be c, and T[φ] to be the coefficient of φ in T,
which is 0 if φ 6∈ (φ1, . . . , φk).
An n-strategy T can be encoded by the tuples (φ1, . . . φk) and (ξ1, . . . ξk) because
the c term is determined by them. Explicitly, by linearity we have
T = ξ1 · (φ1 − φ1
∗n
) + · · · + ξk · (φk − φk
∗n
),
which means any n-strategy can be written as a linear combination of (φi − φi
∗n
)
terms, each of which means “buy one share of φi at the prevailing price”.
As an example, consider the following trading strategy for day 5:
h
(¬¬φ)
∗5 − φ
∗5
i
·

φ − φ
∗5

+
h
φ
∗5 − (¬¬φ)
∗5
i
·

¬¬φ − (¬¬φ)
∗5

.
This strategy compares the price of φ on day 5 to the price of ¬¬φ on day 5. If the
former is less expensive by δ, it purchases δ shares of φ at the prevailing prices, and
sells δ shares of ¬¬φ at the prevailing prices. Otherwise, it does the opposite. In
short, this strategy arbitrages φ against ¬¬φ, by buying the cheaper one and selling
the more expensive one.
We can now state the key definition of this section:
18
Definition 3.4.5 (Trader). A trader T is a sequence (T1, T2, . . .) where each
Tn is a trading strategy for day n.
We can visualize a trader as a person who gets to see the day n, think for a while,
and then produce a trading strategy for day n, which will observe the history of
market prices up to and including day n and execute a market order to buy and sell
different sentences at the prevailing market prices.
We will often consider the set of efficiently computable traders, which have to
produce their trading strategy in a time polynomial in n. We can visualize e.c.
traders as traders who are computationally limited: each day they get to think for
longer and longer—we can imagine them writing computer programs each morning
that assist them in their analysis of the market prices—but their total runtime may
only grow polynomially in n.
If s := Tn[φ] > 0, we say that T buys s shares of φ on day n, and if s < 0, we
say that T sells |s| shares of φ on day n. Similarly, if d := Tn[1] > 0, we say that T
receives d dollars on day n, and if d < 0, we say that T pays out |d| dollars on day n.
Each trade Tn has value zero according to Pn, regardless of what market P it is
executed in. Clever traders are the ones who make trades that are later revealed by
a deductive process D to have a high worth (e.g., by purchasing shares of provable
sentences when the price is low). As an example, a trader T with a basic grasp of
arithmetic and skepticism about some of the market P’s confident conjectures might
execute the following trade orders on day n:
Table 1: Visualizing markets and trades
Sentence Market prices Trade
φ :↔ 1 + 1 = 2 Pn(φ) = 90¢ Tn[φ] = 4 shares
ψ :↔ 1 + 1 6= 2 Pn(ψ) = 5¢ Tn[ψ] = −3 shares
χ :↔ “Goldbach’s conjecture” Pn(χ) = 98¢ Tn[χ] = −1 share
The net value of the shares bought and sold at these prices would be
4 · 90¢ − 3 · 5¢ − 1 · 98¢ = $2.47,
so if those three sentences were the only sentences bought and sold by Tn, Tn[1]
would be −2.47.
Trade strategies are a special case of affine combinations of sentences:
Definition 3.4.6 (Affine Combination). An F-combination A : S ∪ {1} → F is
an affine expression of the form
A := c + α1φ1 + · · · + αkφk,
where (φ1, . . . , φk) are sentences and (c, α1, . . . , αk) are in F. We define Rcombinations, Q-combinations, and EF-combinations analogously.
We write A[1] for the trailing coefficient c, and A[φ] for the coefficient of φ,
which is 0 if φ 6∈ (φ1, . . . , φk). The rank of A is defined to be the maximum rank
among all its coefficients. Given any valuation V, we abuse notation in the usual
way and define the value of A (according to V) linearly by:
V(A) := c + α1V(φ1) + · · · + αkV(φk).
An F-combination progression is a sequence A of affine combinations where An
has rank ≤ n. An EF-combination progression is defined similarly.
Note that a trade T is an F-combination, and the holdings T(P) from T against
P
P
is a Q-combination. We will use affine combinations to encode the net holdings
i≤n
Ti(P) of a trader after interacting with a market P, and later to encode linear
inequalities that hold between the truth values of different sentences.
19
3.5 Exploitation
We will now define exploitation, beginning with an example. Let L be the language
of PA, and D be a PA-complete deductive process. Consider a market P that assigns
Pn(“1 + 1 = 2”) = 0.5 for all n, and a trader who buys one share of “1 + 1 = 2” each
day. Imagine a reasoner behind the market obligated to buy and sell shares at the
listed prices, who is also obligated to pay out $1 to holders of φ-shares if and when
D says φ. Let t be the first day when “1 + 1 = 2” ∈ Dt. On each day, the reasoner
receives 50¢ from T, but after day t, the reasoner must pay $1 every day thereafter.
They lose 50¢ each day, and T gains 50¢ each day, despite the fact that T never
risked more than $t/2. In cases like these, we say that T exploits P.
With this example in mind, we define exploitation as follows:
Definition 3.5.1 (Exploitation). A trader T is said to exploit a valuation
sequence V relative to a deductive process D if the set of values
n
W
P
i≤n
Ti

V

 


n ∈ N
+, W ∈ PC(Dn)
o
is bounded below, but not bounded above.
Given a world W, the number W(
P
i≤n
Ti(P)) is the value of the trader’s net
holdings after interacting with the market P, where a share of φ is valued at $1 if φ
is true in W and $0 otherwise. The set {W(
P
i≤n
Ti(P)) | n ∈ N
+, W ∈ PC(Dn)} is
the set of all assessments of T’s net worth, across all time, according to worlds that
were propositionally consistent with D at the time. We informally call these plausible
assessments of the trader’s net worth. Using this terminology, Definition 3.5.1 says
that a trader exploits the market if their plausible net worth is bounded below, but
not above.
Roughly speaking, we can imagine that there is a person behind the market who
acts as a market maker, obligated to buy and sell shares at the listed prices. We
can imagine that anyone who sold a φ-share is obligated to pay $1 if and when D
says φ. Then, very roughly, a trader exploits the market if they are able to make
unbounded returns off of a finite investment.
This analogy is illustrative but incomplete—traders can exploit the market even
if they never purchase a sentence that appears in D. For example, let φ and ψ be
two sentences such that (φ ∨ ψ) is provable in PA, but such that neither φ nor ψ is
provable in PA. Consider a trader that bought 10 φ-shares at a price of 20¢ each, and
10 ψ-shares at a price of 30¢ each. Once D says (φ∨ψ), all remaining p.c. worlds will
agree that the portfolio −5 + 10φ + 10ψ has a value of at least +5, despite the fact
that neither φ nor ψ is ever proven. If the trader is allowed to keep buying φ and
ψ shares at those prices, they would exploit the market, despite the fact that they
never buy decidable sentences. In other words, our notion of exploitation rewards
traders for arbitrage, even if they arbitrage between sentences that never “pay out”.
3.6 Main Result
Recall the logical induction criterion:
Definition 3.0.1 (The Logical Induction Criterion). A market P is said to satisfy
the logical induction criterion relative to a deductive process D if there is no
efficiently computable trader T that exploits P relative to D. A market P meeting
this criterion is called a logical inductor over D.
We may now state our main result:
Theorem 3.6.1. For any deductive process D, there exists a computable belief
sequence P satisfying the logical induction criterion relative to D.
20
Proof. In Section 5, we show how to take an arbitrary deductive process D and
construct a computable belief sequence LIA. Theorem 5.4.2 shows that LIA is a
logical inductor relative to the given D.
Definition 3.6.2 (Logical Inductor over Γ). Given a theory Γ, a logical inductor
over a Γ-complete deductive process D is called a logical inductor over Γ.
Corollary 3.6.3. For any recursively axiomatizable theory Γ, there exists a computable belief sequence that is a logical inductor over Γ.
4 Properties of Logical Inductors
Here is an intuitive argument that logical inductors perform good reasoning under
logical uncertainty:
Consider any polynomial-time method for efficiently identifying patterns
in logic. If the market prices don’t learn to reflect that pattern, a clever
trader can use that pattern to exploit the market. Thus, a logical inductor
must learn to identify those patterns.
In this section, we will provide evidence supporting this intuitive argument, by
demonstrating a number of desirable properties possessed by logical inductors. The
properties that we demonstrate are broken into twelve categories:
1. Convergence and Coherence: In the limit, the prices of a logical inductor
describe a belief state which is fully logically consistent, and represents a
probability distribution over all consistent worlds.
2. Timely Learning: For any efficiently computable sequence of theorems, a
logical inductor learns to assign them high probability in a timely manner,
regardless of how difficult they are to prove. (And similarly for assigning low
probabilities to refutable statements.)
3. Calibration and Unbiasedness: Logical inductors are well-calibrated and,
given good feedback, unbiased.
4. Learning Statistical Patterns: If a sequence of sentences appears pseudorandom to all reasoners with the same runtime as the logical inductor, it learns
the appropriate statistical summary (assigning, e.g., 10% probability to the
claim “the nth digit of π is a 7” for large n, if digits of π are actually hard to
predict).
5. Learning Logical Relationships: Logical inductors inductively learn to
respect logical constraints that hold between different types of claims, such as
by ensuring that mutually exclusive sentences have probabilities summing to
at most 1.
6. Non-Dogmatism: The probability that a logical inductor assigns to an
independent sentence φ is bounded away from 0 and 1 in the limit, by an
amount dependent on the complexity of φ. In fact, logical inductors strictly
dominate the universal semimeasure in the limit. This means that we can
condition logical inductors on independent sentences, and when we do, they
perform empirical induction.
7. Conditionals: Given a logical inductor P, the market given by the conditional
probabilities P(− | ψ) is a logical inductor over D extended to include ψ. Thus,
when we condition logical inductors on new axioms, they continue to perform
logical induction.
8. Expectations: Logical inductors give rise to a well-behaved notion of the
expected value of a logically uncertain variable.
21
9. Trust in Consistency: If the theory Γ underlying a logical inductor’s deductive process is expressive enough to talk about itself, then the logical inductor
learns inductively to trust Γ.
10. Reasoning about Halting: If there’s an efficient method for generating
programs that halt, a logical inductor will learn in a timely manner that those
programs halt (often long before having the resources to evaluate them). If
there’s an efficient method for generating programs that don’t halt, a logical
inductor will at least learn not to expect them to halt for a very long time.
11. Introspection: Logical inductors “know what they know”, in that their
beliefs about their current probabilities and expectations are accurate.
12. Self-Trust: Logical inductors trust their future beliefs.
For the sake of brevity, proofs are deferred to Section 6 and the appendix. Some
example proofs are sketched in this section, by outlining discontinuous traders that
would exploit any market that lacked the desired property. The deferred proofs
define polynomial-time continuous traders that approximate those discontinuous
strategies.
In what follows, let L be a language of propositional logic; let S be the set of
sentences written in L; let Γ ⊂ S be a computably enumerable set of propositional
formulas written in L (such as PA, where the propositional variables are prime
sentences in first-order logic, as discussed in Section 2); and let P be a computable
logical inductor over Γ, i.e., a market satisfying the logical induction criterion
relative to some Γ-complete deductive process D. We assume in this section that Γ
is consistent.
Note that while the computable belief sequence LIA that we define has finite
support on each day, in this section we assume only that P is a market. We do this
because our results below hold in this more general case, and can be applied to LIA
as a special case.
In sections 4.8-4.12 we will assume that Γ can represent computable functions.
This assumption is not necessary until Section 4.8.
4.1 Convergence and Coherence
Firstly, the market prices of a logical inductor converge:
Theorem 4.1.1 (Convergence). The limit P∞ : S → [0, 1] defined by
P∞(φ) := limn→∞Pn(φ)
exists for all φ.
Proof sketch. (Proof in: 6.1 or B.4.)
Roughly speaking, if P never makes up its mind about φ, then it can be
exploited by a trader arbitraging shares of φ across different days. More
precisely, suppose by way of contradiction that the limit P∞(φ) does
not exist. Then for some p ∈ [0, 1] and ε > 0, we have Pn(φ) < p − ε
infinitely often and also Pn(φ) > p + ε infinitely often. A trader can wait
until Pn(φ) < p − ε and then buy a share in φ at the low market price of
Pn(φ). Then the trader waits until some later m such that Pm(φ) > p+ε,
and sells back the share in φ at the higher price. This trader makes a
total profit of 2ε every time Pn(φ) oscillates in this way, at no risk, and
therefore exploits P. Since P implements a logical inductor, this is not
possible; therefore the limit P∞(φ) must in fact exist.
This sketch showcases the main intuition for the convergence of P, but elides a
number of crucial details. In particular, the trader we have sketched makes use of
22
discontinuous trading functions, and so is not a well-formed trader. These details
are treated in Section 6.1.
Next, the limiting beliefs of a logical inductor represent a coherent probability
distribution:
Theorem 4.1.2 (Limit Coherence). P∞ is coherent, i.e., it gives rise to an internally
consistent probability measure Pr on the set PC(Γ) of all worlds consistent with Γ,
defined by the formula
Pr(W(φ) = 1) := P∞(φ).
In particular, if Γ contains the axioms of first-order logic, then P∞ defines a probability measure on the set of first-order completions of Γ.
Proof sketch. (Proof in: 6.2 or C.10.)
The limit P∞(φ) exists by the convergence theorem, so Pr is well-defined.
Gaifman (1964) shows that Pr defines a probability measure over PC(D∞)
so long as the following three implications hold for all sentences φ and ψ:
• If Γ ` φ, then P∞(φ) = 1,
• If Γ ` ¬φ, then P∞(φ) = 0,
• If Γ ` ¬(φ ∧ ψ), then P∞(φ ∨ ψ) = P∞(φ) + P∞(ψ).
Let us demonstrate each of these three properties.
First suppose that Γ ` φ, but P∞(φ) = 1−ε for some ε > 0. Then shares
of φ will be underpriced, as they are worth 1 in every consistent world,
but only cost 1 −ε. There is a trader who waits until φ is propositionally
provable from Dn, and until Pn(φ) has approximately converged, and
then starts buying shares of φ every day at the price Pn(φ). Since φ has
appeared in D, the shares immediately have a minimum plausible value
of $1. Thus the trader makes 1 − Pn(φ) ≈ ε profit every day, earning an
unbounded total value, contradicting the logical induction criterion. But
P cannot be exploited, so P∞(φ) must be 1.
Similarly, if Γ ` ¬φ but P∞(φ) = ε > 0, then a trader could exploit P by
selling off shares in φ for a profit of Pn(φ) ≈ ε each day.
Finally, suppose that Γ ` ¬(φ ∧ ψ), but for some ε > 0,
P∞(φ ∨ ψ) = P∞(φ) + P∞(ψ) ± ε.
Then there is a trader that waits until Pn has approximately converged
on these sentences, and until ¬(φ ∧ ψ) is propositionally provable from
Dn. At that point it’s a good deal to sell (buy) a share in φ ∨ ψ, and
buy (sell) a share in each of φ and ψ; the stocks will have values that
cancel out in every plausible world. Thus this trader makes a profit of
≈ ε from the price differential, and can then repeat the process. Thus,
they would exploit P. But this is impossible, so P∞ must be coherent.
Theorem 4.1.2 says that if P were allowed to run forever, and we interpreted its
prices as probabilities, then we would find its beliefs to be perfectly consistent. In
the limit, P assigns probability 1 to every theorem and 0 to every contradiction. On
independent sentences, its beliefs obey the constraints of probability theory; if φ
provably implies ψ, then the probability of ψ converges to a point no lower than the
limiting probability of φ, regardless of whether they are decidable. The resulting
probabilities correspond to a probability distribution over all possible ways that Γ
could be completed.
This justifies interpreting the market prices of a logical inductor as probabilities.
Logical inductors are not the first computable procedure for assigning probabilities
to sentences in a manner that is coherent in the limit; the algorithm of Demski
(2012) also has this property. The main appeal of logical induction is that their
beliefs become reasonable in a timely manner, outpacing the underlying deductive
process.
23
4.2 Timely Learning
It is not too difficult to define a reasoner that assigns probability 1 to all (and only)
the provable sentences, in the limit: simply assign probability 0 to all sentences, and
then enumerate all logical proofs, and assign probability 1 to the proven sentences.
The real trick is to recognize patterns in a timely manner, well before the sentences
can be proven by slow deduction.
Logical inductors learn to outpace deduction on any efficiently computable
sequence of provable statements.3 To illustrate, consider our canonical example
where Dn is the set of all theorems of PA provable in at most n characters, and
suppose φ is an e.c. sequence of theorems which are easy to generate but difficult to
prove. Let f(n) be the length of the shortest proof of φn, and assume that f is some
fast-growing function. At any given time n, the statement φn is ever further out
beyond Dn—it might take 1 day to prove φ1, 10 days to prove φ2, 100 days to prove
φ3, and so on. One might therefore expect that φn will also be “out of reach” for
Pn, and that we have to wait until a much later day close to f(n) before expecting
Pf(n)(φn) to be accurate. However, this is not the case! After some finite time N,
P will recognize the pattern and begin assigning high probability to φ in a timely
manner.
Theorem 4.2.1 (Provability Induction). Let φ be an e.c. sequence of theorems.
Then
Pn(φn) hn 1.
Furthermore, let ψ be an e.c. sequence of disprovable sentences. Then
Pn(ψn) hn 0.
Proof sketch. (Proof in: 6.5 or C.3.)
Consider a trader that acts as follows. First wait until the time a when
Pa(φa) drops below 1 − ε and buy a share of φa. Then wait until φa is
worth 1 in all worlds plausible at time f(a). Then repeat this process.
If Pn(φn) drops below 1 − ε infinitely often, then this trader makes ε
profit infinitely often, off of an initial investment of $1, and therefore
exploits the market. P is inexploitable, so Pn(φn) must converge to 1.
By a similar argument, Pn(ψn) must converge to 0.4
In other words, P will learn to start believing φn by day n at the latest, despite
the fact that φn won’t be deductively confirmed until day f(n), which is potentially
much later. In colloquial terms, if φ is a sequence of facts that can be generated
efficiently, then P inductively learns the pattern, and its belief in φ becomes accurate
faster than D can computationally verify the individual sentences.
For example, imagine that prg(n) is a program with fast-growing runtime, which
always outputs either 0, 1, or 2 for all n, but such that there is no proof of this in
the general case. Then
“∀x: prg(x) = 0 ∨ prg(x) = 1 ∨ prg(x) = 2”
is not provable. Now consider the sequence of statements
prg012 := “prg(n) = 0 ∨ prg(n) = 1 ∨ prg(n) = 2”
n∈N+
where each prg012n states that prg outputs a 0, 1, or 2 on that n in particular.
Each individual prg012n is provable (it can be proven by running prg on input
n), and prg012 is efficiently computable (because the sentences themselves can be
3. Recall that a sequence x is efficiently computable iff there exists a computable function
n 7→ xn with runtime polynomial in n.
4. The traders sketched here are optimized for ease of proof, not for efficiency—a clever
trader trying to profit from low prices on efficiently computable theorems would be able to
exploit the market faster than this.
24
written down quickly, even if prg is very difficult to evaluate). Thus, provability
induction says that any logical inductor will “learn the pattern” and start assigning
high probabilities to each individual prg012n no later than day n.
Imagine that D won’t determine the output of prg(n) until the f(n)th day, by
evaluating prg(n) in full. Provability induction says that P will eventually recognize
the pattern prg012 and start assigning high probability to prg012n no later than
the nth day, f(n) − n days before the evaluation finishes. This is true regardless of
the size of f(n), so if f is fast-growing, P will outpace D by an ever-growing margin.
Analogy: Ramanujan and Hardy. Imagine that the statements
φ are being output by an algorithm that uses heuristics to generate
mathematical facts without proofs, playing a role similar to the famously
brilliant, often-unrigorous mathematician Srinivasa Ramanujan. Then P
plays the historical role of the beliefs of the rigorous G.H. Hardy who
tries to verify those results according to a slow deductive process (D).
After Hardy (P) verifies enough of Ramanujan’s claims (φ≤n), he begins
to trust Ramanujan, even if the proofs of Ramanujan’s later conjectures
are incredibly long, putting them ever-further beyond Hardy’s current
abilities to rigorously verify them. In this story, Hardy’s inductive
reasoning (and Ramanujan’s also) outpaces his deductive reasoning.
This idiom of assigning the right probabilities to φn no later than day n will be
common throughout the paper, so we give it a name.
Definition 4.2.2 (Timely Manner). Let φ be an e.c. sequence of sentences, and p
be an e.c. sequence of rational numbers. We say that P assigns p to φ in a timely
manner if for every ε > 0, there exists a time N such that for all n > N,
|Pn(φn) − pn| < ε.
In other words, P assigns p to φ in a timely manner if
Pn(φn) hn pn.
Note that there are no requirements on how large N gets as a function of ε. As
such, when we say that P assigns probabilities p to φ in a timely manner, it may
take a very long time for convergence to occur. (See Section 5.5 for a discussion.)
As an example, imagine the reasoner who recognizes that sentences of the form
“1 + 1 +· · ·+ 1 is even” are true iff the number of ones is even. Let φ be the sequence
where φn is the version of that sentence with 2n ones. If the reasoner starts writing
a probability near 100% in the φn cell by day n at the latest, then intuitively, she
has begun incorporating the pattern into her beliefs, and we say that she is assigning
high probabilities to φ in a timely manner.
We can visualize ourselves as taking P’s belief states, sorting them by φ on one
axis and days on another, and then looking at the main diagonal of cells, to check
the probability of each φn on day n. Checking the nth sentence on the nth day is a
rather arbitrary choice, and we might hope that a good reasoner would assign high
probabilities to e.c. sequences of theorems at a faster rate than that. It is easy to
show that this is the case, by the closure properties of efficient computability. For
example, if φ is an e.c. sequence of theorems, then so are φ2n and φ2n+1, which each
enumerate half of φ at twice the speed, so by Theorem 4.2.1 (Provability Induction),
P will eventually learn to believe φ at a rate of at least two per day. Similarly, P
will learn to believe φ3n and φn2 and φ10n3+3 in a timely manner, and so on. Thus,
up to polynomial transformations, it doesn’t really matter which diagonal we check
when checking whether a logical inductor has begun “noticing a pattern”.
Furthermore, we will show that if P assigns the correct probability on the main
diagonal, then P also learns to keep them there:
25
Theorem 4.2.3 (Persistence of Knowledge). Let φ be an e.c. sequence of sentences,
and p be an e.c. sequence of rational-number probabilities. If P∞(φn) hn pn, then
sup
m≥n
|Pm(φn) − pn| hn 0.
Furthermore, if P∞(φn) .n pn, then
sup
m≥n
Pm(φn) .n pn,
and if P∞(φn) &n pn, then
inf
m≥n
Pm(φn) &n pn.
(Proof in: B.6.)
In other words, if P assigns p to φ in the limit, then P learns to assign probability
near pn to φn at all times m ≥ n. This theorem paired with the closure properties
of the set of efficiently computable sequences means that checking the probability of
φn on the nth day is a fine way to check whether P has begun recognizing a pattern
encoded by φ. As such, we invite the reader to be on the lookout for statements
of the form Pn(φn) as signs that P is recognizing a pattern, often in a way that
outpaces the underlying deductive process.
Theorems 4.2.1 (Provability Induction) and 4.2.3 (Persistence of Knowledge)
only apply when the pattern of limiting probabilities is itself efficiently computable.
For example, consider the sequence of sentences
πAeq7 := “π[Ack(n, n)] = 7”
n∈N+
where π[i] is the ith digit in the decimal expansion of π and Ack is the Ackermann
function. Each individual sentence is decidable, so the limiting probabilities are 0
for some πAeq7n and 1 for others. But that pattern of 1s and 0s is not efficiently
computable (assuming there is no efficient way to predict the Ackermann digits of
π), so provability induction has nothing to say on the topic.
In cases where the pattern of limiting probabilities are not e.c., we can still show
that if P is going to make its probabilities follow a certain pattern eventually, then it
learns to make its probabilities follow that pattern in a timely manner. For instance,
assume that each individual sentence πAeq7n (for n > 4) is going to spend a long
time sitting at 10% probability before eventually being resolved to either 1 or 0.
Then P will learn to assign Pn(πAeq7n) ≈ 0.1 in a timely manner:
Theorem 4.2.4 (Preemptive Learning). Let φ be an e.c. sequence of sentences.
Then
lim inf
n→∞
Pn(φn) = lim inf
n→∞
sup
m≥n
Pm(φn).
Furthermore,
lim sup
n→∞
Pn(φn) = lim sup
n→∞
inf
m≥n
Pm(φn).
(Proof in: B.3.)
Let’s unpack Theorem 4.2.4. The quantity supm≥n Pm(φn) is an upper bound
on the price Pm(φn) on or after day n, which we can interpret as the highest price
tag that that P will ever put on φn after we first start checking it on day n. We can
imagine a sequence of these values: On day n, we start watching φn. As time goes
on, its price travels up and down until eventually settling somewhere. This happens
for each n. The limit infimum of supm≥n Pm(φn) is the greatest lower bound p past
which a generic φn (for n large) will definitely be pushed after we started watching it.
Preemptive Learning says that if P always eventually pushes φn up to a probability
at least p, then it will learn to assign each φn a probability at least p in a timely
manner (and similarly for least upper bounds).
26
For example, if each individual πAeq7n is eventually recognized as a claim about
digits of π and placed at probability 10% for a long time before being resolved, then
P learns to assign it probability 10% on the main diagonal. In general, if P is going
to learn a pattern eventually, it learns it in a timely manner.
This leaves open the question of whether a logical inductor P is smart enough to
recognize that the πAeq7 should each have probability 10% before they are settled
(assuming the Ackermann digits of π are hard to predict). We will return to that
question in Section 4.4, but first, we examine the reverse question.
4.3 Calibration and Unbiasedness
Theorem 4.2.1 (Provability Induction) shows that logical inductors are good at
detecting patterns in what is provable. Next, we ask: when a logical inductor
learns a pattern, when must that pattern be real? In common parlance, a source of
probabilistic estimates is called well calibrated if among statements where it assigns
a probability near p, the estimates are correct with frequency roughly p.
In the case of reasoning under logical uncertainty, measuring calibration is not
easy. Consider the sequence clusters constructed from correlated clusters of size 1,
10, 100, 1000, . . . , where the truth value of each cluster is determined by the parity
of a late digit of π:
clusters1 :↔“π[Ack(1, 1)] is even”
clusters2 :↔ · · · :↔ clusters11 :↔“π[Ack(2, 2)] is even”
clusters12 :↔ · · · :↔ clusters111 :↔“π[Ack(3, 3)] is even”
clusters112 :↔ · · · :↔ clusters1111 :↔“π[Ack(4, 4)] is even”
and so on. A reasoner who can’t predict the parity of the Ackermann digits of π
should assign 50% (marginal) probability to any individual clustersn for n large. But
consider what happens if the 9th cluster turns out to be true, and the next billion
sentences are all true. A reasoner who assigned 50% to those billion sentences was
assigning the right probabilities, but their calibration is abysmal: on the billionth
day, they have assigned 50% probability a billion sentences that were overwhelmingly
true. And if the 12th cluster comes up false, then on the trillionth day, they have
assigned 50% probability to a trillion sentences that were overwhelmingly false! In
cases like these, the frequency of truth oscillates eternally, and the good reasoner
only appears well-calibrated on the rare days where it crosses 50%.
The natural way to correct for correlations such as these is to check P’s conditional
probabilities instead of its marginal probabilities. This doesn’t work very well in
our setting, because given a logical sentence φ, the quantity that we care about will
almost always be the marginal probability of φ. The reason we deal with sequences
is because that lets us show that φ has reasonable probabilities relative to various
related sentences. For example, if φ := “prg(32) = 17”, then we can use our theorems
to relate the probability of φ to the probability of the sequence (“prg(n) = 17”)n∈N+ ,
and to the sequence (“prg(32) = n”)n∈N+ , and to the sequence (“prg(n) > n”)n∈N+ ,
and so on, to show that φ eventually has reasonable beliefs about prg (hopefully
before P has the resources to simply evaluate prg on input 32). But at the end
of the day, we’ll want to reason about the marginal probability of φ itself. In this
case, approximately-well-calibrated conditional probabilities wouldn’t buy us much:
there are 2
n−1 possible truth assignments to the first n − 1 elements of φ, so if we
try to compute the marginal probability of φn from all the different conditional
probabilities, exponentially many small errors would render the answer useless.
Furthermore, intuitively, if φ is utterly unpredictable to P, then the probabilities
of all the different truth assignments to φ≤n−1 will go to 0 as n gets large, which
means the conditional probabilities won’t necessarily be reasonable. (In Section 4.4
will formalize a notion of pseudorandomness.)
Despite these difficulties, we can recover some good calibration properties on the
marginal probabilities if we either (a) restrict our consideration to sequences where
the average frequency of truth converges; or (b) look at subsequences of φ where P
27
has “good feedback” about the truth values of previous elements of the subsequence,
in a manner defined below.
To state our first calibration property, we will define two different sorts of
indicator functions that will prove useful in many different contexts.
Definition 4.3.1 (Theorem Indicator). Given a sentence φ, define ThmΓ(φ) to be
1 if Γ ` φ and 0 otherwise.
Definition 4.3.2 (Continuous Threshold Indicator). Let δ > 0 be a rational number,
and x and y be real numbers. We then define
Indδ(x > y) :=



0 if x ≤ y
x − y
δ
if y < x ≤ y + δ
1 if y + δ < x.
Notice that Indδ(x > y) has no false positives, and that it is linear in the region
between y and y + δ. We define Indδ(x < y) analogously, and we define
Indδ(a < x < b) := min(Indδ(x > a),Indδ(x < b)).
Observe that we can generalize this definition to the case where x and y are expressible
features, in which case Indδ(x > y) is an expressible [0, 1]-feature.
Now we can state our calibration theorem.
Theorem 4.3.3 (Recurring Calibration). Let φ be an e.c. sequence of decidable
sentences, a and b be rational numbers, δ be an e.c. sequence of positive rational
numbers, and suppose that P
n

Indδi(a < Pi(φi) < b)

i∈N+ = ∞. Then, if the
sequence
 P
i≤n
Indδi(a < Pi(φi) < b) · ThmΓ(φi)
P
i≤n
Indδi
(a < Pi(φi) < b)
!
n∈N+
converges, it converges to a point in [a, b]. Furthermore, if it diverges, it has a limit
point in [a, b]. (Proof in: D.3.)
Roughly, this says that if Pn(φn) ≈ 80% infinitely often, then if we look at the
subsequence where it’s 80%, the limiting frequency of truth on that subsequence is
80% (if it converges).
In colloquial terms, on subsequences where P says 80% and it makes sense to
talk about the frequency of truth, the frequency of truth is 80%, i.e., P isn’t seeing
shadows. If the frequency of truth diverges—as in the case with clusters—then P is
still well-calibrated infinitely often, but its calibration might still appear abysmal at
times (if they can’t predict the swings).
Note that calibration alone is not a very strong property: a reasoner can always
cheat to improve their calibration (i.e., by assigning probability 80% to things
that they’re sure are true, in order to bring up the average truth of their “80%”
predictions). What we really want is some notion of “unbiasedness”, which says that
there is no efficient method for detecting a predictable bias in a logical inductor’s
beliefs. This is something we can get on sequences where the limiting frequency of
truth converges, though again, if the limiting frequency of truth diverges, all we can
guarantee is a limit point.
Definition 4.3.4 (Divergent Weighting). A divergent weighting w ∈ [0, 1]N
+
is
an infinite sequence of real numbers in [0, 1], such that P
n wn = ∞.
Note that divergent weightings have codomain [0, 1] as opposed to {0, 1}, meaning
the weightings may single out fuzzy subsets of the sequence. For purposes of intuition,
imagine that w is a sequence of 0s and 1s, in which case each w can be interpreted as
a subsequence. The constraint that the wn sum to ∞ ensures that this subsequence
is infinite.
28
Definition 4.3.5 (Generable From P). A sequence of rational numbers q is called
generable from P if there exists an e.c. EF-progression q
† such that q
†
n
(P) = qn
for all n. In this case we say that q is P-generable. P-generable R-sequences,
Q-combination sequences, and R-combination sequences are defined analogously.
Divergent weightings generable from P are fuzzy subsequences that are allowed
to depend continuously (via expressible market features) on the market history.
For example, the sequence (Ind0.01(Pn(φn) > 0.5))n∈N+ is a P-generable sequence
that singles out all times n when Pn(φn) is greater than 50%. Note that the set of
P-generable divergent weightings is larger than the set of e.c. divergent weightings,
as the P-generable weightings are allowed to vary continuously with the market
prices.
Theorem 4.3.6 (Recurring Unbiasedness). Given an e.c. sequence of decidable
sentences φ and a P-generable divergent weighting w, the sequence
P
i≤n wi
· (Pi(φi) − ThmΓ(φi))
P
i≤n wi
has 0 as a limit point. In particular, if it converges, it converges to 0.
(Proof in: D.2.)
Letting w = (1, 1, . . .), this theorem says that the difference between the average
probability Pn(φn) and the average frequency of truth is 0 infinitely often (and 0
always, if the latter converges). Letting each wn be Indδ(a < Pn(φn) < b), we recover
Theorem 4.3.3 (Recurring Calibration). In general, the fraction in Theorem 4.3.6
can be interpreted as a measure of the “bias” of P on the fuzzy subsequence of φ
singled out by w. Then this theorem says that P is unbiased on all P-generable
subsequences where the frequency of truth converges (and unbiased infinitely often
on subsequences where it diverges). Thus, if an e.c. sequence of sentences can be
decomposed (by any P-generable weighting) into subsequences where the frequency
of truth converges, then P learns to assign probabilities such that there is no efficient
method for detecting a predictable bias in its beliefs.
However, not every sequence can be broken down into well-behaved subsequences
by a P-generable divergent weighting (if, for example, the truth values move “pseudorandomly” in correlated clusters, as in the case of clusters). In these cases, it
is natural to wonder whether there are any conditions where P will be unbiased
anyway. Below, we show that the bias converges to zero whenever the weighting w
is sparse enough that P can gather sufficient feedback about φn in between guesses:
Definition 4.3.7 (Deferral Function). A function f : N
+ → N+ is called a deferral
function if
1. f(n) > n for all n, and
2. f(n) can be computed in time polynomial in f(n), i.e., if there is some algorithm
and a polynomial function h such that for all n, the algorithm computes f(n)
within h(f(n)) steps.
If f is a deferral function, we say that f defers n to f(n).
Theorem 4.3.8 (Unbiasedness From Feedback). Let φ be any e.c. sequence of
decidable sentences, and w be any P-generable divergent weighting. If there exists a
strictly increasing deferral function f such that the support of w is contained in the
image of f and ThmΓ(φf(n)) is computable in O(f(n + 1)) time, then
P
i≤n wi
· (Pi(φi) − ThmΓ(φi))
P
i≤n wi
hn 0.
In this case, we say “w allows good feedback on φ”. (Proof in: D.5.)
29
In other words, P is unbiased on any subsequence of the data where a polynomialtime machine can figure out how the previous elements of the subsequence turned
out before P is forced to predict the next one. This is perhaps the best we can hope
for: On ill-behaved sequences such as clusters, where the frequency of truth diverges
and (most likely) no polynomial-time algorithm can predict the jumps, the Pn(φn)
might be pure guesswork.
So how well does P perform on sequences like clusters? To answer, we turn to the
question of how P behaves in the face of sequences that it finds utterly unpredictable.
4.4 Learning Statistical Patterns
Consider the digits in the decimal expansion of π. A good reasoner thinking about
the 101,000,000th digit of π, in lieu of any efficient method for predicting the digit
before they must make their prediction, should assign roughly 10% probability
to that digit being a 7. We will now show that logical inductors learn statistical
patterns of this form.
To formalize this claim, we need some way of formalizing the idea that a sequence
is “apparently random” to a reasoner. Intuitively, this notion must be defined
relative to a specific reasoner’s computational limitations. After all, the digits of
π are perfectly deterministic; they only appear random to a reasoner who lacks
the resources to compute them. Roughly speaking, we will define a sequence to be
pseudorandom (relative to P) if there is no e.c. way to single out any one subsequence
that is more likely true than any other subsequence, not even using expressions
written in terms of the market prices (by way of expressible features):
Definition 4.4.1 (Pseudorandom Sequence). Given a set S of divergent weightings
(Definition 4.3.4), a sequence φ of decidable sentences is called pseudorandom
with frequency p over S if, for all weightings w ∈ S,
limn→∞
P
i≤n wi
· ThmΓ(φi)
P
i≤n wi
exists and is equal to p.
Note that if the sequence φ is actually randomly generated (say, by adding (c1, c2, . . .)
to the language of Γ, and tossing a coin weighted with probability p towards heads for
each i, to determine whether to add ci or ¬ci as an axiom) then φ is pseudorandom
with frequency p almost surely.5 Now:
Theorem 4.4.2 (Learning Pseudorandom Frequencies). Let φ be an e.c. sequence
of decidable sentences. If φ is pseudorandom with frequency p over the set of all
P-generable divergent weightings, then
Pn(φn) hn p.
(Proof in: 6.4 or D.8.)
For example, consider again the sequence πAeq7 where the nth element says
that the Ack(n, n)th decimal digit of π is a 7. The individual πAeq7n statements
are easy to write down (i.e., efficiently computable), but each one is difficult to
decide. Assuming there’s no good way to predict the Ackermann digits of π using a
P-generable divergent weighting, P will assign probability 10% to each πAeq7n in a
timely manner, while it waits for the resources to determine whether the sentence is
true or false. Of course, on each individual πAeq7n, P’s probability will go to 0 or 1
eventually, i.e., limm→∞ Pm(πAeq7n) ∈ {0, 1}.
5. Note that actually adding randomness to Γ in this fashion is not allowed, because
we assumed that the axioms of Γ are recursively enumerable. It is possible to construct a
logical inductor that has access to a source of randomness, by adding one bit of randomness
to the market each day, but that topic is beyond the scope of this paper.
30
Theorem 4.4.2 still tells us nothing about how P handles clusters (defined above),
because the frequency of truth in that sequence diverges, so it does not count as
pseudorandom by the above definition. To handle this case we will weaken our
notion of pseudorandomness, so that it includes more sequences, yielding a stronger
theorem. We will do this by allowing sequences to count as pseudorandom so long
as the limiting frequency of truth converges on “independent subsequences” where
the n + 1st element of the subsequence doesn’t come until after the nth element can
be decided, as described below. Refer to Garrabrant, Soares, and Taylor (2016) for
a discussion of why this is a good way to broaden the set of sequences that count as
pseudorandom.
Definition 4.4.3 (f-Patient Divergent Weighting). Let f be a deferral function.
We say that a divergent weighting w is f-patient if there is some constant C such
that, for all n,
f
X
(n)
i=n
wi(P) ≤ C
In other words, w is f-patient if the weight it places between days n and f(n) is
bounded.
While we are at it, we will also strengthen Theorem 4.4.2 in three additional
ways: we will allow the probabilities on the sentences to vary with time, and with
the market prices, and we will generalize hn to &n and .n.
Definition 4.4.4 (Varied Pseudorandom Sequence). Given a deferral function
f, a set S of f-patient divergent weightings, an e.c. sequence φ of Γ-decidable
sentences, and a P-generable sequence p of rational probabilities, φ is called a pvaried pseudorandom sequence (relative to S) if, for all w ∈ S,
P
i≤n wi
· (pi − ThmΓ(φi))
P
i≤n wi
hn 0.
Furthermore, we can replace hn with &n or .n, in which case we say φ is varied
pseudorandom above p or varied pseudorandom below p, respectively.
Theorem 4.4.5 (Learning Varied Pseudorandom Frequencies). Given an e.c. sequence φ of Γ-decidable sentences and a P-generable sequence p of rational probabilities, if there exists some f such that φ is p-varied pseudorandom (relative to all
f-patient P-generable divergent weightings), then
Pn(φn) hn pn.
Furthermore, if φ is varied pseudorandom above or below p, then the hn may be
replaced with &n or .n (respectively). (Proof in: D.7.)
Thus we see that P does learn to assign marginal probabilities Pn(clustersn) ≈ 0.5,
assuming the Ackermann digits of π are actually difficult to predict. Note that while
Theorem 4.4.5 requires each pn to be rational, the fact that the theorem is generalized
to varied pseudorandom above/below sequences means that Theorem 4.4.5 is a strict
generalization of Theorem 4.4.2 (Learning Pseudorandom Frequencies).
In short, Theorem 4.4.5 shows that logical inductors reliably learn in a timely
manner to recognize appropriate statistical patterns, whenever those patterns (which
may vary over time and with the market prices) are the best available method for
predicting the sequence using P-generable methods.
4.5 Learning Logical Relationships
Most of the above properties discuss the ability of a logical inductor to recognize
patterns in a single sequence—for example, they recognize e.c. sequences of theorems
31
in a timely manner, and they fall back on the appropriate statistical summaries in
the face of pseudorandomness. We will now examine the ability of logical inductors
to learn relationships between sequences.
Let us return to the example of the computer program prg which outputs either
0, 1, or 2 on all inputs, but for which this cannot be proven in general by Γ.
Theorem 4.2.1 (Provability Induction) says that the pattern
prg012 := “prg(n) = 0 ∨ prg(n) = 1 ∨ prg(n) = 2”
n∈N+
will be learned, in the sense that P will assign each prg012n a probability near 1 in
a timely manner. But what about the following three individual sequences?
prg0 := “prg(n) = 0”
n∈N+
prg1 := “prg(n) = 1”
n∈N+
prg2 := “prg(n) = 2”
n∈N+
None of the three sequences is a sequence of only theorems, so provability induction
does not have much to say. If they are utterly pseudorandom relative to r, then
Theorem 4.4.5 (Learning Varied Pseudorandom Frequencies) says that P will fall
back on the appropriate statistical summary, but that tells us little in cases where
there are predictable non-conclusive patterns (e.g., if prg(i) is more likely to output
2 when helper(i) outputs 17). In fact, if P is doing good reasoning, the probabilities
on the (prg0n, prg1n, prg2n) triplet ought to shift, as P gains new knowledge about
related facts and updates its beliefs. How could we tell if those intermediate beliefs
were reasonable?
One way is to check their sum. If P believes that prg(i) ∈ {0, 1, 2} and it knows
how disjunction works, then it should be the case that whenever Pn(prg012t) ≈ 1,
Pn(prg0t)+Pn(prg1t)+Pn(prg2t) ≈ 1. And this is precisely the case. In fact, logical
inductors recognize mutual exclusion between efficiently computable tuples of any
size, in a timely manner:
Theorem 4.5.1 (Learning Exclusive-Exhaustive Relationships). Let φ1, . . . , φk be k
e.c. sequences of sentences, such that for all n, Γ proves that φ
1
n
, . . . , φk
n are exclusive
and exhaustive (i.e. exactly one of them is true). Then
Pn(φ
1
n
) + · · · + Pn(φ
k
n
) hn 1.
Proof sketch. (Proof in: C.11.)
Consider the trader that acts as follows. On day n, they check the prices
of φ
1
n
. . . φk
n
. If the sum of the prices is higher (lower) than 1 by some
fixed threshold ε > 0, they sell (buy) a share of each, wait until the
values of the shares are the same in every plausible world, and make a
profit of ε. (It is guaranteed that eventually, in every plausible world
exactly one of the shares will be valued at 1.) If the sum goes above 1 +ε
(below 1 − ε) on the main diagonal infinitely often, this trader exploits
P. Logical inductors are inexploitable, so it must be the case that the
sum of the prices goes to 1 along the main diagonal.
This theorem suggests that logical inductors are good at learning to assign
probabilities that respect logical relationships between related sentences. To show
that this is true in full generality, we will generalize Theorem 4.5.1 to any linear
inequalities that hold between the actual truth-values of different sentences.
First, we define the following convention:
Convention 4.5.2 (Constraint). An R-combination A can be viewed as a constraint, in which case we say that a valuation V satisfies the constraint if V(A) ≥ 0.
32
For example, the constraint
AND := −2 + φ + ψ
says that both φ and ψ are true, and it is satisfied by W iff W(φ) = W(ψ) = 1. As
another example, the pair of constraints
XOR := (1 − φ − ψ, φ + ψ − 1)
say that exactly one of φ and ψ is true, and are satisfied by P7 iff P7(φ) + P7(ψ) = 1.
Definition 4.5.3 (Bounded Combination Sequence). By BCS(P) (mnemonic:
bounded combination sequences) we denote the set of all P-generable Rcombination sequences A that are bounded, in the sense that there exists some
bound b such that kAnk1 ≤ b for all n, where k−k1 includes the trailing coefficient.
Theorem 4.5.4 (Affine Provability Induction). Let A ∈ BCS(P) and b ∈ R. If, for
all consistent worlds W ∈ PC(Γ) and all n ∈ N
+, it is the case that W(An) ≥ b,
then
Pn(An) &n b,
and similarly for = and hn, and for ≤ and .n. (Proof in: C.2.)
For example, consider the constraint sequence
A := 1 − prg0n − prg1n − prg2n

n∈N+
For all n and all consistent worlds W ∈ PC(Γ), the value W(An) is 0, so applying
Theorem 4.5.5 to A, we get that Pn(An) hn 0. By linearity, this means
Pn(prg0n) + Pn(prg1n) + Pn(prg2n) hn 1,
i.e., P learns that the three sequences are mutually exclusive and exhaustive in a
timely manner, regardless of how difficult prg is to evaluate. Affine Provability
Induction is a generalization of this idea, where the coefficients may vary (day by
day, and with the market prices).
We can push this idea further, as follows:
Theorem 4.5.5 (Affine Coherence). Let A ∈ BCS(P). Then
lim inf
n→∞
inf
W∈PC(Γ)
W(An) ≤ lim inf
n→∞
P∞(An) ≤ lim inf
n→∞
Pn(An),
and
lim sup
n→∞
Pn(An) ≤ lim sup
n→∞
P∞(An) ≤ lim sup
n→∞
sup
W∈PC(Γ)
W(An).
(Proof in: C.1.)
This theorem ties the ground truth on A, to the value of A in the limit, to the value
of A on the main diagonal. In words, it says that if all consistent worlds value An in
(a, b) for n large, then P∞ values An in (c, d) ⊆ (a, b) for n large (because P∞ is a
weighted mixture of all consistent worlds), and P learns to assign probabilities such
that Pn(An) ∈ (c, d) in a timely manner. In colloquial terms, P learns in a timely
manner to respect all linear inequalities that actually hold between sentences, so
long as those relationships can be enumerated in polynomial time.
For example, if helper(i)=err always implies prg(i)=0, P will learn this pattern,
and start assigning probabilities to Pn(“prg(n)=0”) which are no lower than those
of Pn(“helper(n)=err”). In general, if a series of sentences obey some complicated
linear inequalities, then so long as those constraints can be written down in polynomial
time, P will learn the pattern, and start assigning probabilities that respect those
constraints in a timely manner.
33
This doesn’t mean that P will assign the correct values (0 or 1) to each sentence
in a timely manner; that would be impossible for a deductively limited reasoner.
Rather, P’s probabilities will start satisfying the constraints in a timely manner. For
example, imagine a set of complex constraints holds between seven sequences, such
that exactly three sentences in each septuplet are true, but it’s difficult to tell which
three. Then P will learn this pattern, and start ensuring that its probabilities on
each septuplet sum to 3, even if it can’t yet assign particularly high probabilities to
the correct three.
If we watch an individual septuplet as P reasons, other constraints will push the
probabilities on those seven sentences up and down. One sentence might be refuted
and have its probability go to zero. Another might get a boost when P discovers
that it’s likely implied by a high-probability sentence. Another might take a hit
when P discovers it likely implies a low-probability sentence. Throughout all this,
Theorem 4.5.5 says that P will ensure that the seven probabilities always sum to ≈ 3.
P’s beliefs on any given day arise from this interplay of many constraints, inductively
learned.
Observe that Affine Coherence is a direct generalization of Theorem 4.2.1 (Provability Induction). One way to interpret this theorem is that it says that P is very
good at learning inductively to predict long-running computations. Given any e.c.
sequence of statements about the computation, if they are true then P learns to
believe them in a timely manner, and if they are false then P learns to disbelieve
them in a timely manner, and if they are related by logical constraints (such as by
exclusivity or implication) to some other e.c. sequence of statements, then P learns
to make its probabilities respect those constraints in a timely manner. This is one of
the main reasons why we think this class of algorithms deserves the name of “logical
inductor”.
Affine Coherence can also be interpreted as an approximate coherence condition
on the finite belief-states of P. It says that if a certain relationship among truth
values is going to hold in the future, then P learns to make that relationship hold
approximately in its probabilities, in a timely manner.6
In fact, we can use this idea to strengthen every theorem in sections 4.2-4.4, as
below. (Readers without interest in the strengthened theorems are invited to skip
to Section 4.6.)
Affine Strengthenings
Observe that Theorem 4.5.4 (Affine Provability Induction) is a strengthening of
Theorem 4.2.1 (Provability Induction).
Theorem 4.5.6 (Persistence of Affine Knowledge). Let A ∈ BCS(P). Then
lim inf
n→∞
inf
m≥n
Pm(An) = lim inf
n→∞
P∞(An)
and
lim sup
n→∞
sup
m≥n
Pm(An) = lim sup
n→∞
P∞(An).
(Proof in: B.5.)
To see that this is a generalization of Theorem 4.2.3 (Persistence of Knowledge), it
might help to first replace A with a sequence p of rational probabilities.
6. Another notion of approximate coherence goes by the name of “inductive coherence”
(Garrabrant, Fallenstein, et al. 2016). A reasoner is called inductively coherent if (1)
Pn(⊥) hn 0; (2) Pn(φn) converges whenever φ is efficiently computable and each φn
provably implies φn+1; and (3) for all efficiently computable sequences of provably mutually
exclusive and exhaustive triplets (φn, ψn, χn), Pn(φn)+Pn(ψn)+Pn(χn) hn 1. Garrabrant,
Fallenstein, et al. show that inductive coherence implies coherence in the limit, and argue
that this is a good notion of approximate coherence. Theorems 4.1.2 (Limit Coherence)
and 4.5.5 (Affine Coherence) imply inductive coherence, and indeed, logical induction is a
much stronger notion.
34
Theorem 4.5.7 (Affine Preemptive Learning). Let A ∈ BCS(P). Then
lim inf
n→∞
Pn(An) = lim inf
n→∞
sup
m≥n
Pm(An)
and
lim sup
n→∞
Pn(An) = lim sup
n→∞
inf
m≥n
Pm(An) .
(Proof in: B.2.)
Definition 4.5.8 (Determined via Γ). We say that a R-combination A is determined via Γ if, in all worlds W ∈ PC(Γ), the value W(A) is equal. Let ValΓ(A)
denote this value.
Similarly, a sequence A of R-combinations is said to be determined via Γ if An
is determined via Γ for all n.
Theorem 4.5.9 (Affine Recurring Unbiasedness). If A ∈ BCS(P) is determined via
Γ, and w is a P-generable divergent weighting,
P
i≤n wi
· (Pi(Ai) − ValΓ(Ai))
P
i≤n wi
has 0 as a limit point. In particular, if it converges, it converges to 0. (Proof in: D.1.)
Theorem 4.5.10 (Affine Unbiasedness from Feedback). Given A ∈ BCS(P) that is
determined via Γ, a strictly increasing deferral function f such that ValΓ(An) can be
computed in time O(f(n + 1)), and a P-generable divergent weighting w such that
the support of w is contained in the image of f,
P
i≤n wi
· (Pi(Ai) − ValΓ(Ai))
P
i≤n wi
hn 0.
In this case, we say “w allows good feedback on A”. (Proof in: D.4.)
Theorem 4.5.11 (Learning Pseudorandom Affine Sequences). Given a A ∈ BCS(P)
which is determined via Γ, if there exists deferral function f such that for any
P-generable f-patient divergent weighting w,
P
i≤n wi
· ValΓ(Ai)
P
i≤n wi
&n 0,
then
Pn(An) &n 0,
and similarly for hn, and .n. (Proof in: D.6.)
4.6 Non-Dogmatism
Cromwell’s rule says that a reasoner should not assign extreme probabilities (0
or 1) except when applied to statements that are logically true or false. The rule
was named by Lindley (1991), in light of the fact that Bayes’ theorem says that a
Bayesian reasoner can never update away from probabilities 0 or 1, and in reference
to the famous plea:
I beseech you, in the bowels of Christ, think it possible that you may be
mistaken. – Oliver Cromwell
35
The obvious generalization of Cromwell’s rule to a setting where a reasoner is
uncertain about logic is that they also should not assign extreme probabilities to
sentences that have not yet been proven or disproven. Logical inductors do not
satisfy this rule, as evidenced by the following theorem:
Theorem 4.6.1 (Closure under Finite Perturbations). Let P and P0 be markets
with Pn = P
0
n
for all but finitely many n. Then P is a logical inductor if and only if
P0is a logical inductor. (Proof in: G.7.)
This means that we can take a logical inductor, completely ruin its beliefs on the
23rd day (e.g., by setting P23(φ) = 0 for all φ), and it will still be a logical inductor.
Nevertheless, there is still a sense in which logical inductors are non-dogmatic, and
can “think it possible that they may be mistaken”:
Theorem 4.6.2 (Non-Dogmatism). If Γ 0 φ then P∞(φ) < 1, and if Γ 0 ¬φ then
P∞(φ) > 0.
Proof sketch. (Proof in: G.4.)
Consider a trader that watches φ and buys whenever it gets low, as
follows. The trader starts with $1. They spend their first 50 cents when
Pn(φ) < 1/2, purchasing one share. They spend their next 25 cents when
Pn(φ) < 1/4, purchasing another share. They keep waiting for Pn(φ) to
drop low enough that they can spend the next half of their initial wealth
to buy one more share. Because φ is independent, there always remains
at least one world W such that W(φ) = 1, so if Pn(φ) → 0 as n → ∞ then
their maximum plausible profits are $1 + $1 + $1 +. . . which diverges,
and they exploit the market. Thus, P∞(φ) must be bounded away from
zero.
In other words, if φ is independent from Γ, then P’s beliefs about φ won’t get stuck
converging to 0 or 1. By Theorem 4.6.1 (Closure under Finite Perturbations), P may
occasionally jump to unwarranted conclusions—believing with “100% certainty”, say,
that Euclid’s fifth postulate follows from the first four—but it always corrects these
errors, and eventually develops conservative beliefs about independent sentences.
Theorem 4.6.2 guarantees that P will be reasonable about independent sentences,
but it doesn’t guarantee reasonable beliefs about theories, because theories can
require infinitely many axioms. For example, let Γ be a theory of pure first-order
logic, and imagine that the language L has a free binary relation symbol “ ∈ ”.
Now consider the sequence ZFCaxioms of first-order axioms of Zermelo-Fraenkel
set theory (ZFC) which say to interpret “ ∈ ” in the set-theoretic way, and note
that ZFCaxioms is infinite. Each individual sentence ZFCaxiomsn is consistent with
first-order logic, but if P∞’s odds on each axiom were 50:50 and independent, then
it would say that the probability of them all being true simultaneously was zero.
Fortunately, for any computably enumerable sequence of sentences that are mutually
consistent, P∞ assigns positive probability to them all being simultaneously true.
Theorem 4.6.3 (Uniform Non-Dogmatism). For any computably enumerable sequence of sentences φ such that Γ ∪ φ is consistent, there is a constant ε > 0 such
that for all n,
P∞(φn) ≥ ε.
(Proof in: G.2.)
If φn is the conjunction of the first n axioms of ZFC, Theorem 4.6.3 shows that P∞
assigns positive probability to theories in which the symbol “∈” satisfies all axioms
of ZFC (assuming ZFC is consistent).
Reasoning about individual sentences again, we can put bounds on how far each
sentence φ is bounded away from 0 and 1, in terms of the prefix complexity κ(φ) of
36
φ, i.e., the length of the shortest prefix that causes a fixed universal Turing machine
to output φ.
7
Theorem 4.6.4 (Occam Bounds). There exists a fixed positive constant C such
that for any sentence φ with prefix complexity κ(φ), if Γ 0 ¬φ, then
P∞(φ) ≥ C2
−κ(φ)
,
and if Γ 0 φ, then
P∞(φ) ≤ 1 − C2
−κ(φ)
.
(Proof in: G.3.)
This means that if we add a sequence of constant symbols (c1, c2, . . .) not
mentioned in Γ to the language L, then P’s beliefs about statements involving those
constants will depend on the complexity of the claim. Roughly speaking, if you ask
after the probability of a claim like “c1 = 10 ∧ c2 = 7 ∧ . . . ∧ cn = −3” then the
answer will be no lower than the probability that a simplicity prior assigns to the
shortest program that outputs (10, 7, . . . , −3).
In fact, the probability may be a fair bit higher, if the claim is part of a
particularly simple sequence of sentences. In other words, logical inductors can be
used to reason about empirical uncertainty as well as logical uncertainty, by using
P∞ as a full-fledged sequence predictor:
Theorem 4.6.5 (Domination of the Universal Semimeasure). Let (b1, b2, . . .) be a
sequence of zero-arity predicate symbols in L not mentioned in Γ, and let σ≤n =
(σ1, . . . , σn) be any finite bitstring. Define
P∞(σ≤n) := P∞(“(b1 ↔ σ1 = 1) ∧ (b2 ↔ σ2 = 1) ∧ . . . ∧ (bn ↔ σn = 1)”),
such that, for example, P∞(01101) = P∞(“¬b1 ∧ b2 ∧ b3 ∧ ¬b4 ∧ b5”). Let M be a
universal continuous semimeasure. Then there is some positive constant C such that
for any finite bitstring σ≤n,
P∞(σ≤n) ≥ C · M(σ≤n).
(Proof in: G.5.)
In other words, logical inductors can be viewed as a computable approximation to a
normalized probability distribution that dominates the universal semimeasure. In
fact, this dominance is strict:
Theorem 4.6.6 (Strict Domination of the Universal Semimeasure). The universal
continuous semimeasure does not dominate P∞; that is, for any positive constant C
there is some finite bitstring σ≤n such that
P∞(σ≤n) > C · M(σ≤n).
(Proof in: G.6.)
In particular, by Theorem 4.6.3 (Uniform Non-Dogmatism), logical inductors assign
positive probability to the set of all completions of theories like PA and ZFC, whereas
universal semimeasures do not. This is why we can’t construct approximately
coherent beliefs about logic by fixing an enumeration of logical sentences and
conditioning a universal semimeasure on more axioms of Peano arithmetic each
7. We use prefix complexity (the length of the shortest prefix that causes a UTM to
output φ) instead of Kolmogorov complexity (the length of the shortest complete program
that causes a UTM to output φ) because it makes the proof slightly easier. (And, in the
opinion of the authors, prefix complexity is the more natural concept.) Both types of
complexity are defined relative to an arbitrary choice of universal Turing machine (UTM),
but our theorems hold for every logical inductor regardless of the choice of UTM, because
changing the UTM only amounts to changing the constant terms by some fixed amount.
37
day: the probabilities that the semimeasure assigns to those conjunctions must
go to zero, so the conditional probabilities may misbehave. (If this were not the
case, it would be possible to sample a complete extension of Peano arithmetic with
positive probability, because universal semimeasures are approximable from below;
but this is impossible. See the proof of Theorem 4.6.6 for details.) While P∞ is
limit-computable, it is not approximable from below, so it can and does outperform
the universal semimeasure when reasoning about arithmetical claims.
4.7 Conditionals
One way to interpret Theorem 4.6.5 (Domination of the Universal Semimeasure)
is that when we condition P∞ on independent sentences about which it knows
nothing, it performs empirical (scientific) induction. We will now show that when
we condition P, it also performs logical induction.
In probability theory, it is common to discuss conditional probabilities such as
Pr(A | B) := Pr(A ∧ B)/Pr(B) (for any B with Pr(B) > 0), where Pr(A | B) is
interpreted as the probability of A restricted to worlds where B is true. In the
domain of logical uncertainty, we can define conditional probabilities in the analogous
way:
Definition 4.7.1 (Conditional Probability). Let φ and ψ be sentences, and let V
be a valuation with V(ψ) > 0. Then we define
V(φ | ψ) := 
V(φ ∧ ψ)/V(ψ) if V(φ ∧ ψ) < V(ψ)
1 otherwise.
Given a valuation sequence V, we define
V(− | ψ) := (V1(− | ψ), V2(− | ψ), . . .).
Defining V(φ | ψ) to be 1 if V(ψ) = 0 is nonstandard, but convenient for our theorem
statements and proofs. The reader is welcome to ignore the conditional probabilities
in cases where V(ψ) = 0, or to justify our definition from the principle of explosion
(which says that from a contradiction, anything follows). This definition also caps
V(φ | ψ) at 1, which is necessary because there’s no guarantee that V knows that
φ ∧ ψ should have a lower probability than ψ. For example, if it takes P more than
17 days to learn how “∧” interacts with φ and ψ, then it might be the case that
P17(φ ∧ ψ) = 0.12 and P17(ψ) = 0.01, in which case the uncapped “conditional
probability” of φ ∧ ψ given ψ according to P17 would be twelve hundred percent.
This fact doesn’t exactly induce confidence in P(− | ψ). Nevertheless, we have
the following theorem:
Theorem 4.7.2 (Closure Under Conditioning). The sequence P(− | ψ) is a logical
inductor over Γ ∪ {ψ}. Furthermore, given any efficiently computable sequence ψ of
sentences, the sequence
(P1(− | ψ1), P2(− | ψ1 ∧ ψ2), P3(− | ψ1 ∧ ψ2 ∧ ψ3), . . .),
where the nth pricing is conditioned on the first n sentences in ψ, is a logical inductor
over Γ ∪ {ψi| i ∈ N
+}. (Proof in: G.8.)
In other words, if we condition logical inductors on logical sentences, the result
is still a logical inductor, and so the conditional probabilities of a logical inductor
continues to satisfy all the desirable properties satisfied by all logical inductors. This
also means that one can obtain a logical inductor for Peano arithmetic by starting
with a logical inductor over an empty theory, and conditioning it on PA.
With that idea in mind, we will now begin examining questions about logical
inductors that assume Γ can represent computable functions, such as questions
about P’s beliefs about Γ, computer programs, and itself.
38
4.8 Expectations
In probability theory, it is common to ask the expected (average) value of a variable
that takes on different values in different possible worlds. Emboldened by our success
with conditional probabilities, we will now define a notion of the expected values of
logical variables, and show that these are also fairly well-behaved. This machinery
will be useful later when we ask logical inductors for their beliefs about themselves.
We begin by defining a notion of logically uncertain variables, which play a
role analogous to the role of random variables in probability theory. For the sake
of brevity, we will restrict our attention to logically uncertain variables with their
value in [0, 1]; it is easy enough to extend this notion to a notion of arbitrary
bounded real-valued logically uncertain variables. (It does, however, require carrying
a variable’s bounds around everywhere, which makes the notation cumbersome.)
To define logically uncertain variables, we will need to assume that Γ is capable
of representing rational numbers and proving things about them. Later, we will
use expected values to construct sentences that talk about things like the expected
outputs of a computer program. Thus, in this section and in the remainder of
Section 4, we will assume that Γ can represent computable functions.
Definition 4.8.1 (Logically Uncertain Variable). A logically uncertain variable,
abbreviated LUV, is any formula X free in one variable that defines a unique value
via Γ, in the sense that
Γ ` ∃x: (X(x) ∧ ∀x
0
: X(x
0
) → x
0 = x).
We refer to that value as the value of X. If Γ proves that the value of X is in [0, 1],
we call X a [0, 1]-LUV.
Given a [0, 1]-LUV X and a consistent world W ∈ PC(Γ), the value of X in
W is defined to be
W(X) := sup {x ∈ [0, 1] | W(“X ≥ x”) = 1} .
In other words, W(X) is the supremum of values that do not exceed X according to
W. (This rather roundabout definition is necessary in cases where W assigns X a
non-standard value.)
We write U for the set of all [0, 1]-LUVs. When manipulating logically uncertain
variables, we use shorthand like “X < 0.5” for “∀x: X(x) → x < 0.5”. See Section 2
for details.
As an example, Half := “ν = 0.5” is a LUV, where the unique real number that
makes Half true is rather obvious. A more complicated LUV is
TwinPrime := “1 if the twin prime conjecture is true, 0 otherwise”;
this is a deterministic quantity (assuming Γ actually proves the twin prime conjecture
one way or the other), but it’s reasonable for a limited reasoner to be uncertain about
the value of that quantity. In general, if f : N
+ → [0, 1] is a computable function
then “f(7)” is a LUV, because “f(7)” is shorthand for the formula “γf (7, ν)”, where
γf is the predicate of Γ representing f.
With LUVs in hand, we can define a notion of P’s expected value for a LUV X
on day n with precision k. The obvious idea is to take the sum
lim
k→∞
k
X−1
i=0
i
k
Pn(“i/k < X ≤ (i + 1)/k”).
However, if Pn hasn’t yet figured out that X pins down a unique value, then it
might put high probability on X being in multiple different intervals, and the simple
integral of a [0, 1]-valued LUV could fall outside the [0, 1] interval. This is a nuisance
when we want to treat the expectations of [0, 1]-LUVs as other [0, 1]-LUVs, so instead,
we will define expectations using an analog of a cumulative distribution function. In
39
probability theory, the expectation of a [0, 1]-valued random variable V with density
function ρV is given by E(V ) = R 1
0
x· ρV (x)dx. We can rewrite this using integration
by parts as
E(V ) = Z 1
0
Pr(V > x)dx.
This motivates the following definition of expectations for LUVs:
Definition 4.8.2 (Expectation). For a given valuation V, we define the approximate expectation operator E
V
k
for V with precision k by
E
V
k
(X) :=
k
X−1
i=0
1
k
V(“X > i/k”).
where X is a [0, 1]-LUV.
This has the desirable property that E
V
k
(X) ∈ [0, 1], because V(−) ∈ [0, 1].
We will often want to take a limit of E
Pn
k
(X) as both k and n approach ∞. We
hereby make the fairly arbitrary choice to focus on the case k = n for simplicity,
adopting the shorthand
En := E
Pn
n
.
In other words, when we examine how a logical inductor’s expectations change
on a sequence of sentences over time, we will (arbitrarily) consider approximate
expectations that gain in precision at a rate of one unit per day.
We will now show that the expectation operator En possesses properties that
make it worthy of that name.
Theorem 4.8.3 (Expectations Converge). The limit E∞ : S → [0, 1] defined by
E∞(X) := limn→∞En(X)
exists for all X ∈ U. (Proof in: E.4.)
Note that E∞(X) might not be rational.
Because P∞ defines a probability measure over PC(Γ), E∞(X) is the average
value of W(X) across all consistent worlds (weighted by P∞). In other words, every
LUV X can be seen as a random variable with respect to the measure P∞, and E∞
acts as the standard expectation operator on P∞. Furthermore,
Theorem 4.8.4 (Linearity of Expectation). Let a, b be bounded P-generable sequences of rational numbers, and let X, Y , and Z be e.c. sequences of [0, 1]-LUVs.
If we have Γ ` Zn = anXn + bnYn for all n, then
anEn(Xn) + bnEn(Yn) hn En(Zn).
(Proof in: E.9.)
For our next result, we want a LUV which can be proven to take value 1 if φ is
true and 0 otherwise.
Definition 4.8.5 (Indicator LUV). For any sentence φ, we define its indicator
LUV by the formula
1(φ) := “(φ ∧ (ν = 1)) ∨ (¬φ ∧ (ν = 0))”.
Observe that 1(φ)(1) is equivalent to φ, and 1(φ)(0) is equivalent to ¬φ.
Theorem 4.8.6 (Expectations of Indicators). Let φ be an e.c. sequence of sentences.
Then
En(1(φn)) hn Pn(φn).
(Proof in: E.10.)
40
In colloquial terms, Theorem 4.8.6 says that a logical inductor learns that asking for
the expected value of 1(φ) is the same as asking for the probability of φ.
To further demonstrate that expectations work as expected, we will show that
they satisfy generalized versions of all theorems proven in sections 4.2-4.5. (Readers
without interest in the versions of those theorems for expectations are invited to
skip to Section 4.9.)
Collected Theorems for Expectations
Definition 4.8.7 (LUV Valuation). A LUV valuation is any function U : U → [0, 1].
Note that E
V
n and E
V
∞ are LUV valuations for any valuation V and n ∈ N
+, and
that every world W ∈ PC(Γ) is a LUV valuation.
Definition 4.8.8 (LUV Combination). An F-LUV-combination B : U∪{1} → F
is an affine expression of the form
B := c + α1X1 + · · · + αkXk,
where (X1, . . . , Xk) are [0, 1]-LUVs and (c, α1, . . . , αk) are in F. An EF-LUVcombination, an R-LUV-combination, and a Q-LUV-combination are defined similarly.
The following concepts are all defined analogously to how they are defined for
sentence combinations: B[1], B[X], rank(B), U(B) for any LUV valuation U, FLUV-combination progressions, EF-LUV-combination progressions, and
P-generable LUV-combination sequences. (See definitions 3.4.6 and 4.3.5 for details.)
Definition 4.8.9 (Bounded LUV-Combination Sequence). By BLCS(P) (mnemonic:
bounded LUV-combination sequences) we denote the set of all P-generable RLUV-combination sequences B that are bounded, in the sense that there exists some
bound b such that kBnk1 ≤ b for all n, where k−k1 includes the trailing coefficient.
Theorem 4.8.10 (Expectation Provability Induction). Let B ∈ BLCS(P) and
b ∈ R. If, for all consistent worlds W ∈ PC(Γ) and all n ∈ N
+, it is the case that
W(Bn) ≥ b, then
En(Bn) &n b,
and similarly for = and hn, and for ≤ and .n. (Proof in: E.8.)
Theorem 4.8.11 (Expectation Coherence). Let B ∈ BLCS(P). Then
lim inf
n→∞
inf
W∈PC(Γ)
W(Bn) ≤ lim inf
n→∞
E∞(Bn) ≤ lim inf
n→∞
En(Bn),
and
lim sup
n→∞
En(Bn) ≤ lim sup
n→∞
E∞(Bn) ≤ lim sup
n→∞
sup
W∈PC(Γ)
W(Bn).
(Proof in: E.7.)
Theorem 4.8.12 (Persistence of Expectation Knowledge). Let B ∈ BLCS(P).
Then
lim inf
n→∞
inf
m≥n
Em(Bn) = lim inf
n→∞
E∞(Bn)
and
lim sup
n→∞
sup
m≥n
Em(Bn) = lim sup
n→∞
E∞(Bn).
(Proof in: E.6.)
41
Theorem 4.8.13 (Expectation Preemptive Learning). Let B ∈ BLCS(P). Then
lim inf
n→∞
En(Bn) = lim inf
n→∞
sup
m≥n
Em(Bn)
and
lim sup
n→∞
En(Bn) = lim sup
n→∞
inf
m≥n
Em(Bn) .
(Proof in: E.3.)
Definition 4.8.14 (Determined via Γ (for LUV-Combinations)). We say that a
R-LUV-combination B is determined via Γ if, in all worlds W ∈ PC(Γ), the value
W(B) is equal. Let ValΓ(B) denote this value.
Similarly, a sequence B of R-LUV-combinations is said to be determined via Γ
if Bn is determined via Γ for all n.
Theorem 4.8.15 (Expectation Recurring Unbiasedness). If B ∈ BLCS(P) is determined via Γ, and w is a P-generable divergent weighting weighting such that the
support of w is contained in the image of f,
P
i≤n wi
· (Ei(Bi) − ValΓ(Bi))
P
i≤n wi
has 0 as a limit point. In particular, if it converges, it converges to 0.
Theorem 4.8.16 (Expectation Unbiasedness From Feedback). Given B ∈ BLCS(P)
that is determined via Γ, a strictly increasing deferral function f such that ValΓ(An)
can be computed in time O(f(n + 1)), and a P-generable divergent weighting w,
P
i≤n wi
· (Ei(Bi) − ValΓ(Bi))
P
i≤n wi
hn 0.
In this case, we say “w allows good feedback on B”. (Proof in: E.12.)
Theorem 4.8.17 (Learning Pseudorandom LUV Sequences). Given a B ∈ BLCS(P)
which is determined via Γ, if there exists a deferral function f such that for any
P-generable f-patient divergent weighting w,
P
i≤n wi
· ValΓ(Bi)
P
i≤n wi
&n 0,
then
En(Bn) &n 0.
(Proof in: E.13.)
4.9 Trust in Consistency
The theorems above all support the hypothesis that logical inductors develop reasonable beliefs about logic. One might then wonder what a logical inductor has to
say about some of the classic questions in meta-mathematics. For example, what
does a logical inductor over PA say about the consistency of Peano arithmetic?
Definition 4.9.1 (Consistency Statement). Given a recursively axiomatizable theory
Γ
0
, define the n-consistency statement of Γ
0
to be the formula with one free
variable ν such that
Con(Γ0)(ν) := “There is no proof of ⊥ from Γ
0 with ν or fewer symbols”,
42
written in L using a Gödel encoding. For instance, Con(PA)(“ Ack(10, 10)”) says
that any proof of ⊥ from PA requires at least Ack(10, 10) symbols.
We further define “Γ0is consistent” to be the universal generalization
“∀n: there is no proof of ⊥ from Γ
0
in n or fewer symbols”,
and “Γ0is inconsistent” for its negation.
Theorem 4.9.2 (Belief in Finitistic Consistency). Let f be any computable function.
Then
Pn(Con(Γ)(“f(n)”)) hn 1.
(Proof in: C.4.)
In other words, if Γ is in fact consistent, then P learns to trust it for arbitrary finite
amounts of time. For any fast-growing function f you can name, P eventually learns
to believe Γ is consistent for proofs of length at most f(n), by day n at the latest.
In colloquial terms, if we take a logical inductor over PA and show it a computable
function f that, on each input n, tries a new method for finding an inconsistency in
PA, then the logical inductor will stare at the function for a while and eventually
conclude that it’s not going to succeed (by learning to assign low probability to f(n)
proving ⊥ from PA by day n at the latest, regardless of how long f runs). That is
to say, a logical inductor over PA learns to trust Peano arithmetic inductively.
By the same mechanism, a logical inductor over Γ can learn inductively to
trust the consistency of any consistent theory, including consistent theories that are
stronger than Γ (in the sense that they can prove Γ consistent):
Theorem 4.9.3 (Belief in the Consistency of a Stronger Theory). Let Γ
0
be any
recursively axiomatizable consistent theory. Then
Pn(Con(Γ0)(“f(n)”)) hn 1.
(Proof in: C.5.)
For instance, a logical inductor over PA can learn inductively to trust the consistency
of ZFC for finite proofs of arbitrary length (assuming ZFC is in fact consistent).
These two theorems alone are unimpressive. Any algorithm that assumes consistency until proven otherwise can satisfy these theorems, and because every
inconsistent theory admits a finite proof of inconsistency, those naïve algorithms
will disbelieve any inconsistent theory eventually. But those algorithms will still
believe inconsistent theories for quite a long time, whereas logical inductors learn to
distrust inconsistent theories in a timely manner:
Theorem 4.9.4 (Disbelief in Inconsistent Theories). Let Γ0 be an e.c. sequence of
recursively axiomatizable inconsistent theories. Then
Pn(“Γ0
n
is inconsistent”) hn 1,
so
Pn(“Γ0
n
is consistent”) hn 0.
(Proof in: C.6.)
In other words, logical inductors learn in a timely manner to distrust inconsistent
theories that can be efficiently named, even if the shortest proofs of inconsistency
are very long.
Note that Theorem 4.9.2 (Belief in Finitistic Consistency) does not say
P∞(“Γ is consistent”)
is equal to 1, nor even that it’s particularly high. On the contrary, by Theorem 4.6.2
(Non-Dogmatism), the limiting probability on that sentence is bounded away from 0
43
and 1 (because both that sentence and its negation are consistent with Γ). Intuitively,
D never reveals evidence against the existence of non-standard numbers, so P
remains open to the possibility. This is important for Theorem 4.7.2 (Closure Under
Conditioning), which say that logical inductors can safely be conditioned on any
sequence of statements that are consistent with Γ, but it also means that P will
not give an affirmative answer to the question of whether PA is consistent in full
generality.
In colloquial terms, if you hand a logical inductor any particular computation,
it will tell you that that computation isn’t going to output a proof ⊥ from the
axioms of PA, but if you ask whether PA is consistent in general, it will start waxing
philosophical about non-standard numbers and independent sentences—not unlike a
human philosopher.
A reasonable objection here is that Theorem 4.9.2 (Belief in Finitistic Consistency) is not talking about the consistency of the Peano axioms, it’s talking about
computations that search for proofs of contradiction from PA. This is precisely
correct, and brings us to our next topic.
4.10 Reasoning about Halting
Consider the famous halting problem of Turing (1936). Turing proved that there is
no general algorithm for determining whether or not an arbitrary computation halts.
Let’s examine what happens when we confront logical inductors with the halting
problem.
Theorem 4.10.1 (Learning of Halting Patterns). Let m be an e.c. sequence of
Turing machines, and x be an e.c. sequence of bitstrings, such that mn halts on input
xn for all n. Then
Pn(“mn halts on input xn”) hn 1.
(Proof in: C.7.)
Note that the individual Turing machines do not need to have fast runtime. All
that is required is that the sequence m be efficiently computable, i.e., it must be
possible to write out the source code specifying mn in time polynomial in n. The
runtime of an individual mn is immaterial for our purposes. So long as the mn all
halt on the corresponding xn, P recognizes the pattern and learns to assign high
probability to “mn halts on input xn” no later than the nth day.
Of course, this is not so hard on its own—a function that assigns probability 1
to everything also satisfies this property. The real trick is separating the halting
machines from the non-halting ones. This is harder. It is easy enough to show that
P learns to recognize e.c. sequences of machines that provably fail to halt:
Theorem 4.10.2 (Learning of Provable Non-Halting Patterns). Let q be an e.c.
sequence of Turing machines, and y be an e.c. sequence of bitstrings, such that qn
provably fails to halt on input yn for all n. Then
Pn(“qn halts on input yn”) hn 0.
(Proof in: C.8.)
Of course, it’s not too difficult to disbelieve that the provably-halting machines will
halt; what makes the above theorem non-trivial is that P learns in a timely manner
to expect that those machines won’t halt. Together, the two theorems above say that
if there is any efficient method for generating computer programs that definitively
either halt or don’t (according to Γ) then P will learn the pattern.
The above two theorems only apply to cases where Γ can prove that the machine
either halts or doesn’t. The more interesting case is the one where a Turing
machine q fails to halt on input y, but Γ is not strong enough to prove this fact.
In this case, P∞’s probability of q halting on input y is positive, by Theorem 4.6.2
(Non-Dogmatism). Nevertheless, P still learns to stop expecting that those machines
will halt after any reasonable amount of time:
44
Theorem 4.10.3 (Learning not to Anticipate Halting). Let q be an e.c. sequence
of Turing machines, and let y be an e.c. sequence of bitstrings, such that qn does
not halt on input yn for any n. Let f be any computable function. Then
Pn(“qn halts on input yn within f(n) steps”) hn 0.
(Proof in: C.9.)
For example, let y be an enumeration of all bitstrings, and let q be the constant
sequence (q, q, . . .) where q is a Turing machine that does not halt on any input.
If Γ cannot prove this fact, then P will never be able to attain certainty about
claims that say q fails to halt, but by Theorem 4.10.3, it still learns to expect
that q will run longer than any computable function you can name. In colloquial
terms, while P won’t become certain that non-halting machines don’t halt (which is
impossible), it will put them in the “don’t hold your breath” category (along with
some long-running machines that do halt, of course).
These theorems can be interpreted as justifying the intuitions that many computer
scientists have long held towards the halting problem: It is impossible to tell whether
or not a Turing machine halts in full generality, but for large classes of well-behaved
computer programs (such as e.c. sequences of halting programs and provably nonhalting programs) it’s quite possible to develop reasonable and accurate beliefs. The
boundary between machines that compute fast-growing functions and machines that
never halt is difficult to distinguish, but even in those cases, it’s easy to learn to
stop expecting those machines to halt within any reasonable amount of time. (See
also the work of Calude and Stay [2008] for other formal results backing up this
intuition.)
One possible objection here is that the crux of the halting problem (and of the
Γ-trust problem) are not about making good predictions, they are about handling
diagonalization and paradoxes of self-reference. Gödel’s incompleteness theorem
constructs a sentence that says “there is no proof of this sentence from the axioms
of PA”, and Turing’s proof of the undecidability of the halting problem constructs a
machine which halts iff some other machine thinks it loops. P learning to trust Γ is
different altogether from P learning to trust itself. So let us turn to the topic of P’s
beliefs about P.
4.11 Introspection
Because we’re assuming Γ can represent computable functions, we can write sentences
describing the beliefs of P at different times. What happens when we ask P about
sentences that refer to itself?
For instance, consider a sentence ψ := “Pn(φ) > 0.7” for some specific n and
φ, where P’s beliefs about ψ should depend on what its beliefs about φ are on the
nth day. Will P figure this out and get the probabilities right on day n? For any
particular φ and n it’s hard to say, because it depends on whether P has learned
how ψ relates to P and φ yet. If however we take an e.c. sequence of ψ which all
say “φ will have probability greater than 0.7 on day n” with n varying, then we can
guarantee that P will learn the pattern, and start having accurate beliefs about its
own beliefs:
Theorem 4.11.1 (Introspection). Let φ be an e.c. sequence of sentences, and a,
b be P-generable sequences of probabilities. Then, for any e.c. sequence of positive
rationals δ → 0, there exists a sequence of positive rationals ε → 0 such that for all
n:
1. if Pn(φn) ∈ (an + δn, bn − δn), then
Pn(“an < Pn
(φn) < bn”) > 1 − εn,
2. if Pn(φn) ∈/ (an − δn, bn + δn), then
Pn(“an < Pn
(φn) < bn”) < εn.
45
(Proof in: F.1.)
In other words, for any pattern in P’s beliefs that can be efficiently written down
(such as “P’s probabilities on φ are between a and b on these days”), P learns to
believe the pattern if it’s true, and to disbelieve it if it’s false (with vanishing error).
At a first glance, this sort of self-reflection may seem to make logical inductors
vulnerable to paradox. For example, consider the sequence of sentences
χ0.5 := (“Pn(χ
0.5
n
) < 0.5”)n∈N+
such that χ
0.5
n
is true iff P assigns it a probability less than 50% on day n. Such a
sequence can be defined by Gödel’s diagonal lemma. These sentences are probabilistic
versions of the classic “liar sentence”, which has caused quite a ruckus in the setting
of formal logic (Grim 1991; McGee 1990; Glanzberg 2001; Gupta and Belnap 1993;
Eklund 2002). Because our setting is probabilistic, it’s perhaps most closely related
to the “unexpected hanging” paradox—χ
0.5
n
is true iff P thinks it is unlikely on day
n. How do logical inductors handle this sort of paradox?
Theorem 4.11.2 (Paradox Resistance). Fix a rational p ∈ (0, 1), and define an
e.c. sequence of “paradoxical sentences” χp satisfying
Γ ` χ
p
n ↔

Pn(χ
p
n
) < p
for all n. Then
limn→∞Pn(χ
p
n
) = p.
(Proof in: F.2.)
A logical inductor responds to paradoxical sentences χp by assigning probabilities
that converge on p. For example, if the sentences say “P will assign me a probability
less than 80% on day n”, then Pn (once it has learned the pattern) starts assigning
probabilities extremely close to 80%—so close that traders can’t tell if it’s slightly
above or slightly below. By Theorem 4.3.6 (Recurring Unbiasedness), the frequency
of truth in χ
p
≤n will have a limit point at 0.8 as n → ∞, and by the definition of
logical induction, there will be no efficiently expressible method for identifying a
bias in the price.
Let us spend a bit of time understanding this result. After day n, χ
0.8
n
is “easy”
to get right, at least for someone with enough computing power to compute Pn(χ
0.8
n
)
to the necessary precision (it will wind up very close to 0.8 for large n). Before day
n, we can interpret the probability of χ
0.8
n as the price of a share that’s going to pay
out $1 if the price on day n is less than 80¢, and $0 otherwise. What’s the value of
this share? Insofar as the price on day n is going to be low, the value is high; insofar
as the price is going to be high, the value is low. So what actually happens on the
nth day? Smart traders buy χ
0.8
n
if its price is lower than 80¢, and sell it if its price
is higher than 80¢. By the continuity constraints on the traders, each one has a
price at which they stop buying χ
0.8
n
, and Theorem 4.11.2 (Paradox Resistance) tells
us that the stable price exists extremely close to 80¢. Intuitively, it must be so close
that traders can’t tell which way it’s going to go, biased on the low side, so that it
looks 80% likely to be below and 20% likely to be above to any efficient inspection.
For if the probability seemed more than 80% likely to be below, traders would buy;
and if it seemed anymore than 20% likely to be above, traders would sell.
To visualize this, imagine that your friend owns a high-precision brain-scanner
and can read off your beliefs. Imagine they ask you what probability you assign
to the claim “you will assign probability <80% to this claim at precisely 10am
tomorrow”. As 10am approaches, what happens to your belief in this claim? If you
become extremely confident that it’s going to be true, then your confidence should
drop. But if you become fairly confident it’s going to be false, then your confidence
should spike. Thus, your probabilities should oscillate, pushing your belief so close
to 80% that you’re not quite sure which way the brain scanner will actually call it.
46
In response to a paradoxical claim, this is exactly how P behaves, once it’s learned
how the paradoxical sentences work.
Thus, logical inductors have reasonable beliefs about their own beliefs even in
the face of paradox. We can further show that logical inductors have “introspective
access” to their own beliefs and expectations, via the medium of logically uncertain
variables:
Theorem 4.11.3 (Expectations of Probabilities). Let φ be an efficiently computable
sequence of sentences. Then
Pn(φn) hn En(“Pn
(φn)”).
(Proof in: F.3.)
Theorem 4.11.4 (Iterated Expectations). Suppose X is an efficiently computable
sequence of LUVs. Then
En(Xn) hn En(“En(Xn)”).
(Proof in: F.4.)
Next, we turn our attention to the question of what a logical inductor believes
about its future beliefs.
4.12 Self-Trust
The coherence conditions of classical probability theory guarantee that a probabilistic
reasoner trusts their future beliefs, whenever their beliefs change in response to new
empirical observations. For example, if a reasoner Pr(−) knows that tomorrow they’ll
see some evidence e that will convince them that Miss Scarlet was the murderer,
then they already believe that she was the murderer today:
Pr(Scarlet) = Pr(Scarlet | e)Pr(e) + Pr(Scarlet | ¬e)Pr(¬e).
In colloquial terms, this says “my current beliefs are already a mixture of my expected
future beliefs, weighted by the probability of the evidence that I expect to see.”
Logical inductors obey similar coherence conditions with respect to their future
beliefs, with the difference being that a logical inductor updates its belief by gaining
more knowledge about logical facts, both by observing an ongoing process of deduction and by thinking for longer periods of time. Thus, the self-trust properties of a
logical inductor follow a slightly different pattern:
Theorem 4.12.1 (Expected Future Expectations). Let f be a deferral function (as
per Definition 4.3.7), and let X denote an e.c. sequence of [0, 1]-LUVs. Then
En(Xn) hn En(“Ef(n)
(Xn)”).
(Proof in: F.5.)
Roughly speaking, Theorem 4.12.1 says that a logical inductor’s current expectation
of X on day n is already equal to its expected value of X in f(n) days. In particular,
it learns in a timely manner to set its current expectations equal to its future
expectations on any LUV. In colloquial terms, once a logical inductor has figured
out how expectations work, it will never say “I currently believe that the X variables
have low values, but tomorrow I’m going to learn that they have high values”. Logical
inductors already expect today what they expect to expect tomorrow.
It follows immediately from theorems 4.12.1 (Expected Future Expectations)
and 4.8.6 (Expectations of Indicators) that the current beliefs of a logical inductor
are set, in a timely manner, to equal their future expected beliefs.
47
Theorem 4.12.2 (No Expected Net Update). Let f be a deferral function, and let
φ be an e.c. sequence of sentences. Then
Pn(φn) hn En(“Pf(n)
(φn)”).
(Proof in: F.6.)
In particular, if P knows that its future self is going to assign some sequence p of
probabilities to φ, then it starts assigning p to φ in a timely manner.
Theorem 4.12.1 (Expected Future Expectations) can be generalized to cases
where the LUV on day n is multiplied by an expressible feature:
Theorem 4.12.3 (No Expected Net Update under Conditionals). Let f be a
deferral function, and let X denote an e.c. sequence of [0, 1]-LUVs, and let w denote
a P-generable sequence of real numbers in [0, 1]. Then
En(“Xn · wf(n)
”) hn En(“Ef(n)(Xn) · wf(n)”).
(Proof in: F.7.)
To see why Theorem 4.12.3 is interesting, it helps to imagine the case where X is a
series of bundles of goods and services, and wn is Indδn(Ef(n)(Xn) > 0.7) for some
sequence of rational numbers δ → 0, as per Definition 4.3.2. This value is 1 if P will
expect the nth bundle to be worth more than 70¢ on day f(n), and 0 otherwise, and
intermediate if the case isn’t quite clear. Then
En

“Xn· Indδn

Ef(n)(Xn
) > 0.7

”

can be interpreted as P’s expected value of the bundle on day n, in cases where
P is going to think it’s worth at least 70¢ on day f(n). Now assume that
Indδn(Ef(n)(Xn)) > 0 and divide it out of both sides, in which case the theorem
roughly says
Enow(X | Elater(X) > 0.7) h Enow(Elater(X) | Elater(X) > 0.7),
which says that P’s expected value of the bundle now, given that it’s going to think
the bundle has a value of at least 70¢ later, is equal to whatever it expects to think
later, conditioned on thinking later that the bundle is worth at least 70¢.
Combining this idea with indicator functions, we get the following theorem:
Theorem 4.12.4 (Self-Trust). Let f be a deferral function, φ be an e.c. sequence of
sentences, δ be an e.c. sequence of positive rational numbers, and p be a P-generable
sequence of rational probabilities. Then
En

“1(φn) · Indδn

Pf(n)(φn) > pn

”

&n pn · En

“Indδn

Pf(n)(φn) > pn

”

.
(Proof in: F.8.)
Very roughly speaking, if we squint at Theorem 4.12.4, it says something like
Enow(φ | Plater(φ) > p) & p,
i.e., if we ask P what it would believe about φ now if it learned that it was going
to believe φ with probability at least p in the future, then it will answer with a
probability that is at least p.
As a matter of fact, Theorem 4.12.4 actually says something slightly weaker, which
is also more desirable. Let each φn be the self-referential sentence “Pf(n)(φn) < 0.5”
which says that the future Pf(n) will assign probability less than 0.5 to φn. Then,
48
conditional on Pf(n)(φn) ≥ 0.5, Pn should believe that the probability of φn is 0.
And indeed, this is what a logical inductor will do:
Pn

“φn ∧ (Pf(n)
(φn) ≥ 0.5)”hn 0,
by Theorem 4.2.3 (Persistence of Knowledge), because each of those conjunctions is
disprovable. This is why Theorem 4.12.4 uses continuous indicator functions: With
discrete conjunctions, the result would be undesirable (not to mention false).
What Theorem 4.12.4 says is that P attains self-trust of the “if in the future I
will believe x is very likely, then it must be because x is very likely” variety, while
retaining the ability to think it can outperform its future self’s beliefs when its future
self confronts paradoxes. In colloquial terms, if we ask “what’s your probability on
the paradoxical sentence φn given that your future self believes it with probability
exactly 0.5?” then P will answer “very low”, but if we ask “what’s your probability
on the paradoxical sentence φn given that your future self believes it with probability
extremely close to 0.5?” then P will answer “roughly 0.5.”
Still speaking roughly, this means that logical inductors trust their future beliefs
to be accurate and only change for good reasons. Theorem 4.12.4 says that if you
ask “what’s the probability of φ, given that in the future you’re going to believe it’s
more than 95% likely?” then you’ll get an answer that’s no less than 0.95, even if
the logical inductor currently thinks that φ is unlikely.
5 Construction
In this section, we show how given any deductive process D, we can construct a
computable belief sequence, called LIA, that satisfies the logical induction criterion
relative to D. Roughly speaking, LIA works by simulating an economy of traders
and using Brouwer’s fixed point theorem to set market prices such that no trader
can exploit the market relative to D.
We will build LIA from three subroutines called MarketMaker, Budgeter, and
TradingFirm. Intuitively, MarketMaker will be an algorithm that sets market prices
by anticipating what a single trader is about to do, Budgeter will be an algorithm
for altering a trader to stay within a certain budget, and TradingFirm will be an
algorithm that uses Budgeter to combine together an infinite sequence of carefully
chosen e.c. traders (via a sum calculable in finite time) into a single trader that
exploits a given market if any e.c. trader exploits that market. Then, LIA will work
by using MarketMaker to make a market not exploitable by TradingFirm and hence
not exploitable by any e.c. trader, thereby satisfying the logical induction criterion.
To begin, we will need a few basic data types for our subroutines to pass around:
Definition 5.0.1 (Belief History). An n-belief history P≤n = (P1, . . . , Pn) is a
finite list of belief states of length n.
Definition 5.0.2 (Strategy History). An n-strategy history T≤n = (T1, . . . , Tn)
is a finite list of trading strategies of length n, where Ti is an i-strategy.
Definition 5.0.3 (Support). For any valuation V we define
Support(V) := {φ ∈ S | V(φ) 6= 0},
and for any n-strategy Tn we define
Support(Tn) := {φ ∈ S | Tn[φ] 6≡ 0}.
Observe that for any belief state P and any n-strategy Tn, Support(P) and
Support(Tn) are computable from the finite lists representing P and Tn.
49
5.1 Constructing MarketMaker
Here we define the MarketMaker subroutine and establish its key properties. Intuitively, given any trader T as input, on each day n, MarketMaker looks at the
trading strategy Tn and the valuations P≤n−1 output by MarketMaker on previous
days. It then uses an approximate fixed point (guaranteed to exist by Brouwer’s
fixed point theorem) that sets prices Pn for that day such that when the trader’s
strategy Tn reacts to the prices, the resulting trade Tn(P≤n) earns at most a very
small positive amount of value in any world. Intuitively, the fixed point finds the
trader’s “fair prices”, such that they abstain from betting, except possibly to buy
sentences at a price very close to $1 or sell them at a price very close to $0, thereby
guaranteeing that very little value can be gained from the trade.
Lemma 5.1.1 (Fixed Point Lemma). Let Tn be any n-strategy, and let P≤n−1 be
any (n−1)-belief history. There exists a valuation V with Support(V) ⊆ Support(Tn)
such that
for all worlds W ∈ W: W(Tn(P≤n−1, V)) ≤ 0. (5.1.1)
Proof. We will use Brouwer’s fixed point theorem to find “prices” V such that Tn
only ever buys shares for $1 or sells them for $0, so it cannot make a profit in
any world. Intuitively, we do this by making a “price adjustment” mapping called
fix that moves prices toward 1 or 0 (respectively) as long as Tn would buy or sell
(respectively) any shares at those prices, and finding a fixed point of that mapping.
First, we let S
0 = Support(Tn) and focus on the set
V
0
:= {V | Support(V) ⊆ S0}.
Observe that V
0
is equal to the natural inclusion of the finite-dimensional cube [0, 1]S
0
in the space of all valuations V = [0, 1]S . We now define our “price adjustment”
function fix : V
0 → V0 as follows:
fix(V)(φ) := max(0, min(1, V(φ) + Tn(P≤n−1, V)[φ])).
This map has the odd property that it adds prices and trade volumes, but it does the
trick. Notice that fix is a function from the compact, convex space V
0
to itself, so if
it is continuous, it satisfies the antecedent of Brouwer’s fixed point theorem. Observe
that fix is in fact continuous, because trade strategies are continuous. Indeed, we
required that trade strategies be continuous for precisely this purpose. Thus, by
Brouwer’s fixed point theorem, fix has at least one fixed point V
fix that satisfies, for
all sentences φ ∈ S0,
V
fix(φ) = max(0, min(1, Vfix(φ) + Tn(P≤n−1, Vfix)[φ])).
Fix a world W and observe from this equation that if Tn buys some shares of
φ ∈ S0 at these prices, i.e. if Tn(P≤n−1, V
fix)[φ] > 0, then Vfix(φ) = 1, and in
particular, W(φ) − V
fix(φ) ≤ 0. Similarly, if Tn sells some shares of φ, i.e. if
Tn(P≤n−1, V
fix)[φ] < 0, then Vfix(φ) = 0, so W(φ) − Vfix(φ) ≥ 0. In either case, we
have
0 ≥ (W(φ) − V
fix(φ)) · Tn(P≤n−1, Vfix)[φ]
since the two factors always have opposite sign (or at least one factor is 0). Summing
over all φ, remembering that Tn(V≤n)[φ] = 0 for φ /∈ S0, gives
0 ≥
X
φ∈S
(W(φ) − V
fix(φ)) · Tn(P≤n−1, Vfix)[φ]
= W(Tn(P≤n, V
fix)) − Vfix(Tn(P≤n−1, Vfix))
since the values of the “cash” terms W(Tn(P≤n, V
fix)[1]) and Vfix(Tn(P≤n, Vfix)[1])
are by definition both equal to Tn(P≤n, V
fix)[1] and therefore cancel. But
V
fix(Tn(P≤n−1, Vfix)) = 0
50
by definition of a trading strategy, so for any world W, we have
0 ≥ W(Tn(P≤n−1, V
fix)).
Definition/Proposition 5.1.2 (MarketMaker). There exists a computable function, henceforth named MarketMaker, satisfying the following definition. Given
as input any n ∈ N
+, any n-strategy Tn, and any (n − 1)-belief history P≤n−1,
MarketMakern(Tn, P≤n−1) returns a belief state P with Support(P) ⊆ Support(Tn)
such that
for all worlds W ∈ W: W(Tn(P≤n−1, P)) ≤ 2
−n
. (5.1.2)
Proof. Essentially, we will find a rational approximation P to the fixed point V
fix in
the previous lemma, by brute force search. This requires some care, because the set
of all worlds is uncountably infinite.
First, given Tn and P≤n−1, let S
0
:= Support(Tn), V
0
:= {V | Support(V) ⊆ S0},
and take V
fix ∈ V0
satisfying (5.1.1). Let W0:= {W | Support(W) ⊆ S0}, and for
any world W, define W0 ∈ W0 by
W0(φ) := 
W(φ) if φ ∈ S0,
0 otherwise.
Observe that for any W ∈ W, the function V
0 → R given by
V 7→ W(Tn(P≤n−1, V)) = W0(Tn(P≤n−1, V))
is a continuous function of V that depends only on W0. Since the set W0is finite,
the function
V 7→ sup
W∈W
W(Tn(P≤n−1, V)) = max
W0∈W0 W0
(Tn(P≤n−1, V))
is the maximum of a finite number of continuous functions, and is therefore continuous.
Hence there is some neighborhood in V
0 around Vfix with image in (−∞, 2−n) ⊂ R.
By the density of rational points in V
0
, there is therefore some belief state P ∈ V0∩QS
satisfying (5.1.2), as needed.
It remains to show that such a P can in fact be found by brute force search. First,
recall that a belief state P is a rational-valued finite-support map from S to [0, 1],
and so can be represented by a finite list of pairs (φ, q) with φ ∈ S and q ∈ Q ∩ [0, 1].
Since S and [0, 1] ∩ Q are computably enumerable, so is the set of all belief states.
Thus, we can computably “search” though all possible Ps, so we need only
establish that given n, Tn, and P≤n−1 we can computably decide whether each
P in our search satisfies (5.1.2) until we find one. First note that the finite set
Support(Tn) can be computed by searching the expression specifying Tn for all the
sentences φ that occur within it. Moreover, equation (5.1.2) need only be be checked
for worlds W0 ∈ W0, since any other W returns the same value as its corresponding
W0. Now, for any fixed world W0 ∈ W0 and candidate P, we can compute each value
in the language of expressible features
W0(Tn(P≤n−1, P)) = Tn(P≤n−1, P)[1] + X
φ∈S0
W0(φ) · Tn(P≤n−1, P)[φ]
directly by evaluating the expressible features Tn[φ] on the given belief history
(P≤n−1, P), as φ ∈ S0 varies. Since W0is a finite set, we can do this for all
W0 with a finite computation. Thus, checking whether a belief state P satisfies
condition (5.1.2) is computably decidable, and a solution to (5.1.2) can therefore be
found by enumerating all belief states P and searching through them for the first
one that works.
51
Lemma 5.1.3 (MarketMaker Inexploitability). Let T be any trader. The sequence
of belief states P defined recursively by
Pn := MarketMakern(Tn, P≤n−1),
with base case P1 = MarketMaker(T1,()), is not exploited by T relative to any
deductive process D.
Proof. By the definition of MarketMaker, we have that for every n, the belief state
P = Pn satisfies equation (5.1.2), i.e.,
for all worlds W ∈ W and all n ∈ N
+: W(Tn(P)) ≤ 2−n
.
Hence by linearity of W, for all n ∈ N
+ we have:
W
P
i≤n
Ti(P)

=
X
i≤n
W(Ti(P)) ≤
X
i≤n
2
−i < 1.
Therefore, given any deductive process D,
sup nW
P
i≤n
Ti(P)
 


n ∈ N
+, W ∈ PC(Dn)
o
≤ 1 < ∞,
so T does not exploit P relative to D.
5.2 Constructing Budgeter
Here we introduce a subroutine for turning a trader with potentially infinite losses
into a trader that will never have less than −$b in any world W ∈ PC(Dn) on any
day n, for some bound b, in such a way that does not affect the trader if it wouldn’t
have fallen below −$b to begin with.
Definition/Proposition 5.2.1 (Budgeter). Given any deductive process D, there
exists a computable function, henceforth called BudgeterD, satisfying the following
definition. Given inputs n and b ∈ N
+, an n-strategy history T≤n, and an (n − 1)-
belief history P≤n−1, BudgeterD returns an n-strategy BudgeterD
n
(b, T≤n, P≤n−1),
such that
if: W
P
i≤m Ti(P≤i)

≤ −b for some m < n and W ∈ PC(Dm),
then: BudgeterD
n
(b, T≤n, P≤n−1) = 0,
else: BudgeterD
n
(b, T≤n, P≤n−1) = (5.2.1)
Tn · inf
W∈PC(Dn)

max

1,
−W(Tn)
b + W
P
i≤n−1
Ti(P≤i)





−1
.
Proof. Let S
0 =
S
i≤n
Support(Ti), W0 = {W | Support(W) ⊆ S0}, and for any
world W, write
W0(φ) := 
W(φ) if φ ∈ S0,
0 otherwise.
Now, observe that we can computably check the “if” statement in the function
definition. This is because W(
P
i≤m Ti(P≤i)) depends only on W0 ∈ W0
, a finite
set. We can check whether W0 ∈ PC(Dm) in finite time by checking whether
any assignment of truth values to the finite set of prime sentences occurring in
52
sentences of Dn yields the assignment W0 on Support(W0
). The set of sentences Dn
is computable given n, because D is computable by definition.
It remains to show that the “else” expression can be computed and returns an
n-trading strategy. First, the infimum can be computed over W0 ∈ W0 ∩ PC(Dn), a
finite set, since the values in the inf depend only on W0, and the inf operator itself can
be re-expressed in the language of expressible features using max and multiplication
by (−1). The values W0(Tn) and W0(
P
i≤n−1
Ti(P≤i)) are finite sums, and the
denominator b + W(
P
i≤n−1
Ti(P≤i)) is a fixed positive rational (so we can safely
multiply by its reciprocal). The remaining operations are all single-step evaluations
in the language of expressible valuation features, completing the proof.
Let us reflect on the meaning of these operations. The quantity b+W(
P
i<n Ti(P≤i))
is the amount of money the trader has available on day n according to W (assuming
they started with a budget of b), and −W(Tn) is the amount they’re going to lose
on day n according to W as a function of the upcoming prices, and so the infimum
above is the trader’s trade on day n scaled down such that they can’t overspend
their budget according to any world propositionally consistent with Dn.
Lemma 5.2.2 (Properties of Budgeter). Let T be any trader, and P be any sequence
of belief states. Given n and b, let Bb
n denote BudgeterD
n
(b, T≤n, P≤n−1). Then:
1. for all b, n ∈ N
+, if for all m ≤ n and W ∈ PC(Dm) we have
W
P
i≤m Ti(P)

> −b, then
B
b
n
(P) = Tn(P);
2. for all b, n ∈ N
+ and all W ∈ PC(Dn), we have
W
P
i≤n Bb
i
(P)

≥ −b;
3. If T exploits P relative to D, then so does B
b
for some b ∈ N
+.
Part 1.
Proof. Suppose that for some time step n, for all m ≤ n and all worlds W ∈ PC(Dm)
plausible at time m we have
W
P
i≤m Ti(P)

> −b,
so by linearity of W(−), we have in particular that
b + W
P
i≤n−1
Ti(P)

> −W

Tn(P)

.
Since n − 1 ≤ n, the LHS is positive, so we have
1 >
−W

Tn(P)

b + W
P
i≤n−1
Ti(P)
.
Therefore, by the definition of BudgeterD (and Ti(P) = Ti(P≤i)), since the “if”
clause doesn’t trigger by the assumption on the W
P
i≤m Ti(P)

for m < n,
B
b
n
(P) ≡ Tn(P) · inf
W∈PC(Dn)
1
,
max

1,
−W(Tn(P))
b + W
P
i≤n−1
Ti(P)



= Tn(P≤n) · inf
W∈PC(Dn)
1/1
= Tn(P)
as needed.
53
Part 2.
Proof. Suppose for a contradiction that for some n and some W ∈ PC(Dn),
W
P
i≤n Bb
i
(P)

< −b.
Assume that n is the least such day, and fix some such W ∈ PC(Dn). By
the minimality of n it must be that W(Bb
n
(P)) < 0, or else we would have
W
P
i≤n−1 Bb
i
(P)

< −b. Since Bb
n
(P) is a non-negative multiple of Tn(P), we
also have W(Tn(P)) < 0. However, since Bb
n 6≡ 0, from the definition of BudgeterD
we have
W

Bb
n

= W

Tn(P)

·
 
inf
W0∈PC(Dn)
1
,
max 1,
−W0(Tn(P))
b + W0(
P
i≤n−1
Ti(P))!!
≥ W

Tn(P)

· 1
,
max 1,
−W(Tn(P))
b + W(
P
i≤n−1
Ti(P))!
(since W

Tn(P)

< 0)
≥ W

Tn(P)

·
b + W(
P
i≤n−1
Ti(P))
−W(Tn(P))
since −W

Tn(P)

> 0 and Bb
n 6≡ 0 implies b + W(
P
i≤n−1
Ti(P)) > 0. Hence, this
= −b − W
P
i≤n
Ti(P)

.
Further, since Bb
n 6≡ 0, we have
for all j ≤ n − 1: W
P
i≤j
Ti(P)

> −b, which by Part 1 implies that
for all j ≤ n − 1: B
b
j
(P) = Tj (P), therefore
W(B
b
n
) ≥ −b − W
P
i≤n−1 Bb
i
(P)

, hence
W
P
i≤n Bb
i
(P)

≥ −b.
Part 3.
Proof. By definition of exploitation, the set
n
W
P
i≤n
Ti(P)
 


n ∈ N
+, W ∈ PC(Dn)
o
is unbounded above, and is strictly bounded below by some integer b. Then by Part
1, for all n we have Tn(P) = Bb
n
(P). Thus,
n
W
P
i≤n Bb
i
(P)
 


n ∈ N
+, W ∈ PC(Dn)
o
is unbounded above and bounded below, i.e., B
b
exploits P relative to D.
5.3 Constructing TradingFirm
Next we define TradingFirm, which combines an (enumerable) infinite sequence of
e.c. traders into a single “supertrader” that exploits a given belief sequence P relative
to D if any e.c. trader does. It does this by taking each e.c. trader, budgeting it,
and scaling its trades down so that traders later in the sequence carry less weight to
begin with.
To begin, we will need a computable sequence that includes every e.c. trader at
least once. The following trick is standard, but we include it here for completeness:
54
Proposition 5.3.1 (Redundant Enumeration of e.c. Traders). There exists a computable sequence (T
k
)k∈N+ of e.c. traders such that every e.c. trader occurs at least
once in the sequence.
Proof. Fix a computable enumeration of all ordered pairs (Mk, fk) where Mk is a
Turing machine and fk is a polynomial with coefficients in Z. We define a computable
function
ECT : {Turing machines} × {Integer polynomials} × (n ∈ N
+) → {n-strategies}
that runs as follows: ECT(M, f, n) first runs M(n) for up to f(n) time steps, and if
in that time M(n) halts and returns a valid n-strategy Tn, then ECT(M, f, n) returns
that strategy, otherwise it returns 0 (as an n-strategy). Observe that ECT(Mk, fk, −)
is always an e.c. trader, and that every e.c. trader occurs as ECT(Mk, fk, −) for
some k.
Definition/Proposition 5.3.2 (TradingFirm). Given any deductive process D,
there exists a computable function, henceforth called TradingFirmD, satisfying the
following definition. By Proposition 5.3.1, we fix a computable enumeration T
k
including every e.c. trader at least once, and let
S
k
n =

T
k
n
if n ≥ k
0 otherwise.
Given input n ∈ N
+ and an (n − 1)-belief history P≤n−1, TradingFirmD returns an
n-strategy given by
TradingFirmD
n
(P≤n−1) = X
k∈N+
X
b∈N+
2
−k−b
· BudgeterD
n
(b, Sk
≤n
, P≤n−1). (5.3.2)
Proof. We need only show that the infinite sum in equation (5.3.2) is equivalent to
a computable finite sum. Writing
B
b,k
n = BudgeterD
n
(b, Sk
≤n
, P≤n−1),
(an n-strategy), the sum on the RHS of (5.3.2) is equivalent to
X
k∈N+
X
b∈N+
2
−k−b
· B
b,k
n
.
Since S
k
n = 0 for k > n, we also have Bb,kn = 0 for k > n, so the sum is equivalent to
=
X
k≤n
X
b∈N+
2
−k−b
· B
b,k
n
.
Now, assume Cn is a positive integer such that P
i≤n
kS
k
i
(V)k1 < Cn for all k ≤ n
and any valuation sequence V (we will show below that such a Cn can be computed
from P≤n−1). Since the valuations W and P are always [0, 1]-valued, for any m ≤ n
the values W
P
i≤m S
k
i
(P≤m)

are bounded below by −
P
i≤m kS
k
i
(P≤m)k1 > −Cn.
By property 1 of BudgeterD (Lemma 5.2.2.1), Bb,k
n = S
k
n when b > Cn, so the sum
is equivalent to
=


X
k≤n
X
b≤Cn
2
−k−b
· B
b,k
n

 +


X
k≤n
X
b>Cn
2
−k−b
· S
k
n


=


X
k≤n
X
b≤Cn
2
−k−b
· B
b,k
n

 +


X
k≤n
2
−k−Cn · Sk
n


55
which is a finite sum of trading strategies, and hence is itself a trading strategy. Since
the Bb,k
n and the S
k
n are computable from P≤n−1, this finite sum is computable.
It remains to justify our assumption that integers Cn can be computed from
P≤n−1 with Cn >
P
i≤n
kS
k
i
(V)k1 for all k ≤ n and V. To see this, first consider
how to bound a single expressible feature ξ. We can show by induction on the
structure of ξ (see A.2) that, given constant bounds on the absolute value |ζ(V)| of
each subexpression ζ of ξ, we can compute a constant bound on |ξ(V)|; for example,
the bound on ζ · η is the product of the bound on ζ and the bound on η. Thus, given
a single trading strategy S
k
i
and any φ, we can compute a constant upper bound on
|S
k
i
[φ](V)| for all V. Since kS
k
i
(V)k1 ≤
P
φ∈Support(Sk
i
)
2|S
k
i
[φ](V)| and Support(S
k
i
)
is computable, we can bound each kS
k
i
(V)k1, and hence also P
i≤n
kS
k
i
(V)k1, as
needed.
Lemma 5.3.3 (Trading Firm Dominance). Let P be any sequence of belief states,
and D be a deductive process. If there exists any e.c. trader T that exploits P relative
to D, then the sequence

TradingFirmD
n
(P≤n−1)

n∈N+
also exploits P (relative to D).
Proof. Suppose that some e.c. trader exploits P. That trader occurs as T
k
for some
k in the enumeration used by TradingFirmD. First, we show that S
k
(from the
definition of TradingFirmD) also exploits P. It suffices to show that there exist
constants c1 ∈ R
+ and c2 ∈ R such that for all n ∈ N+ and W ∈ PC(Dn),
W
P
i≤n S
k
i
(P)

≥ c1 · W
P
i≤n
T
k
i
(P)

+ c2.
Taking c1 = 1 and c2 = −
P
i<k kT
k
i
(P)k1, where k · k1 denotes the `1 norm on
R-combinations of sentences, we have
W
P
i≤n S
k
i
(P)

≥ 1 · W
P
i≤n
T
k
i
(P)

−
P
i<k kT
k
i
(P)k1

,
so S
k
exploits P. By Lemma 5.2.2.3, we thus have that for some b ∈ N
+, the trader
B
b,k given by
B
b,k
n
:= BudgeterD
n
(b, Sk
≤n
, P≤n−1)
also exploits P.
Next, we show that the trader F given by
Fn := TradingFirmD
n
(P≤n−1)
exploits P. Again, it suffices to show that there exist constants c1 ∈ R
+ and c2 ∈ R
such that for all n ∈ N
+ and W ∈ PC(Dn),
W


X
i≤n
Fi

 ≥ c1 · W


X
i≤n
B
b,k
i

 + c2.
56
It will suffice to take c1 = 2−k−b and c2 = −2, because we have
W


X
i≤n
Fi

 − 2
−k−b
· W


X
i≤n
B
b,k
i


=
X
(k0,b0)6=(k,b)
2
−k
0−b0
· W


X
i≤n
B
b
0
,k0
i


≥
X
(k0,b0)6=(k,b)
2
−k
0−b0
· (−b
0
) ≥ −2
by Lemma 5.2.2.2, hence
W


X
i≤n
Fi

 ≥ 2
−k−b
· W


X
i≤n
B
b,k
i

 − 2.
Thus, F exploits P.
5.4 Constructing LIA
We are finally ready to build LIA. With the subroutines above, the idea is now fairly
simple: we pit MarketMaker and TradingFirm against each other in a recursion, and
MarketMaker wins. Imagine that on each day, TradingFirm outputs an ever-larger
mixture of traders, then MarketMaker carefully examines that mixture and outputs
a belief state on which that mixture makes at most a tiny amount of money on net.
Definition/Algorithm 5.4.1 (A Logical Induction Algorithm). Given a deductive
process D, define the computable belief sequence LIA = (LIA1, LIA2, . . .) recursively
by
LIAn := MarketMakern(TradingFirmD
n
(LIA≤n−1), LIA≤n−1),
beginning from the base case LIA≤0 := ().
Theorem 5.4.2 (LIA is a Logical Inductor). LIA satisfies the logical induction
criterion relative to D, i.e., LIA is not exploitable by any e.c. trader relative to the
deductive process D.
Proof. By Lemma 5.3.3, if any e.c. trader exploits LIA (relative to D), then so
does the trader F := (TradingFirmD
n
(LIA≤n−1))n∈N+ . By Lemma 5.1.3, F does not
exploit LIA. Therefore no e.c. trader exploits LIA.
5.5 Questions of Runtime and Convergence Rates
In this paper, we have optimized our definitions for the theoretical clarity of results
rather than for the efficiency of our algorithms. This leaves open many interesting
questions about the relationship between runtime and convergence rates of logical
inductors that have not been addressed here. Indeed, the runtime of LIA is underspecified because it depends heavily on the particular enumerations of traders and
rational numbers used in the definitions of TradingFirm and MarketMaker.
For logical inductors in general, there will be some tradeoff between the runtime
of Pn as a function of n and how quickly the values Pn(φ) converge to P∞(φ) as
n grows. Quantifying this tradeoff may be a fruitful source of interesting open
problems. Note, however, the following important constraint on the convergence
rate of any logical inductor, regardless of its implementation, which arises from the
halting problem:
57
Proposition 5.5.1 (Uncomputable Convergence Rates). Let P be a logical inductor
over a theory Γ that can represent computable functions, and suppose f : S ×Q+ → N
is a function such that for every sentence φ, if Γ ` φ then Pn(φ) > 1 − ε for all
n > f(φ, ε). Then f must be uncomputable.
Proof. Suppose for contradiction that such a computable f were given. We will
show that f could be used to computably determine whether Γ ` φ for an arbitrary
sentence φ, a task which is known to be impossible for a first-order theory that can
represent computable functions. (If we assumed further that Γ were sound as a
theory of the natural numbers, this would allow us to solve the halting problem by
letting φ be a sentence of the form “M halts”.)
Given a sentence φ, we run two searches in parallel. If we find that Γ ` φ, then
we return True. If we find that for some b, n ∈ N
+ we have
n > fφ, 1
b

and Pn(φ) ≤ 1 −
1
b
, (5.5.1)
then we return False. Both of these conditions are computably enumerable since f,
Pn, and verifying witnesses to Γ ` φ are computable functions.
Suppose first that Γ ` φ. Then by definition of f we have Pn(φ) > 1 −
1
b
for all
n > fφ, 1
b

, and hence we find a witness for Γ ` φ and return True. Now suppose
that Γ 0 φ. Then by Theorem 4.6.2 (Non-Dogmatism) we have that P∞(φ) < 1−ε for
some ε > 0, and hence for some b and all sufficiently large n we have Pn(φ) < 1−1/b.
Therefore 5.5.1 holds and we return False. Thus our search always halts and returns
a Boolean value that correctly indicates whether Γ ` φ.
6 Selected Proofs
In this section, we exhibit a few selected stand-alone proofs of certain key theorems.
These theorems hold for any P satisfying the logical induction criterion, which we
recall here:
Definition 3.0.1 (The Logical Induction Criterion). A market P is said to satisfy
the logical induction criterion relative to a deductive process D if there is no
efficiently computable trader T that exploits P relative to D. A market P meeting
this criterion is called a logical inductor over D.
Only our notation (Section 2), framework (Section 3), and continuous threshold
indicator (Definition 4.3.2) are needed to understand the results and proofs in this
section. Shorter proofs of these theorems can be found in the appendix, but those
rely on significantly more machinery.
6.1 Convergence
Recall Theorem 4.1.1 and the proof sketch given:
Theorem 4.1.1 (Convergence). The limit P∞ : S → [0, 1] defined by
P∞(φ) := limn→∞Pn(φ)
exists for all φ.
Proof sketch.
Roughly speaking, if P never makes up its mind about φ, then it can be
exploited by a trader arbitraging shares of φ across different days. More
precisely, suppose by way of contradiction that the limit P∞(φ) does
not exist. Then for some p ∈ [0, 1] and ε > 0, we have Pn(φ) < p − ε
infinitely often and also Pn(φ) > p + ε infinitely often. A trader can wait
until Pn(φ) < p − ε and then buy a share in φ at the low market price of
58
Pn(φ). Then the trader waits until some later m such that Pm(φ) > p+ε,
and sells back the share in φ at the higher price. This trader makes a
total profit of 2ε every time Pn(φ) oscillates in this way, at no risk, and
therefore exploits P. Since P implements a logical inductor, this is not
possible; therefore the limit P∞(φ) must in fact exist.
We will define a trader T that executes a strategy similar to this one, and hence
exploits the market P if limn→∞ Pn(φ) diverges. To do this, there are two technicalities we must deal with. First, the strategy outlined above uses a discontinuous
function of the market prices Pn(φ), and therefore is not permitted. This is relatively
easy to fix using the continuous indicator functions of Definition 4.3.2.
The second technicality is more subtle. Suppose we define our trader to buy
φ-shares whenever their price Pn(φ) is low, and sell them back whenever their price
is high. Then it is possible that the trader makes the following trades in sequence
against the market P: buy 10 φ-shares on consecutive days, then sell 10 φ-shares;
then buy 100 φ-shares consecutively, and then sell them off; then buy 1000 φ-shares,
then sell them off; and so on. Although this trader makes profit on each batch, it
always spends more on the next batch, taking larger and larger risks (relative to
the remaining plausible worlds). Then the plausible value of this trader’s holdings
will be unbounded below, and so it does not exploit P. In short, this trader is not
tracking its budget, and so may have unboundedly negative plausible net worth. We
will fix this problem by having our trader T track how many net φ-shares it has
bought, and not buying too many, thereby maintaining bounded risk. This will be
sufficient to prove the theorem.
Proof of Theorem 4.1.1. Suppose by way of contradiction that the limit P∞ does
not exist. Then, for some sentence φ and some rational numbers p ∈ [0, 1] and ε > 0,
we have that Pn(φ) < p − ε infinitely often and Pn(φ) > p + ε infinitely often. We
will show that P can be exploited by a trader T who buys below and sells above
these prices infinitely often, contrary to the logical induction criterion.
Definition of the trader T. We will define T recursively along with another
sequence of EF-combinations H (mnemonic: “holdings”) which tracks the sum of
the trader’s previous trades. Our base cases are
T1 := 0
H1 := 0.
For n > 1, we define a recurrence whereby T will buy some φ-shares whenever
φ
∗n < p−ε/2, up to (1 − Hn−1[φ]) shares when φ∗n < p−ε, and sells some φ-shares
whenever φ
∗n > p + ε/2, up to Hn−1 shares when φ∗n > p + ε:
Tn[φ] := (1 − Hn−1[φ]) · Indε/2(φ
∗n < p − ε/2)
− Hn−1[φ] · Indε/2(φ
∗n > p + ε/2),
Tn := Tn[φ] · (φ − φ
∗n
)
Hn := Hn−1 + Tn.
(6.1.1)
The trade coefficients T[φ] are chosen so that the number of φ-shares Hn[φ] that it
owns is always in [0, 1] (it never buys more than 1 − Hn−1[φ] and never sells more
than Hn−1[φ]). Observe that each Tn is a valid trading strategy for day n (see
Definition 3.4.4) because it is of the form ξ · (φ − φ
∗n).
To complete the definition, we must argue that T is efficiently computable. For
this, observe that the 3n + 2 definition (:=) equations defining T1, . . . , Tn above can
be written down in time polynomial in n. Thus, a combination of feature expressions
defining Tn from scratch can be written down in poly(n) time (indeed, the expression
is just a concatenation of n copies of the three “:=” equations written above, along
with the base cases), so T is efficiently computable.
59
Proof of exploitation. To show T exploits P over D, we must compute upper and
lower bounds on the set of plausible values W(Hn(P)) (since Hn =
P
i≤n
Tn) for
worlds W ∈ PC(Dn).
While proving exploitation, we leave the constant argument P implicit to reduce
clutter, writing, e.g., φ
∗i
for φ
∗i
(P) = Pi(φ), Tn[φ] for Tn[φ](P), and so on.
First, since each Ti[1] = −Ti[φ] · φ
∗i
, the trader’s “cash” held on day n is
Hn[1] = X
i≤n
Ti[1] = −
X
i≤n
Ti[φ] · φ
∗i
which we can regroup, to compare the prices φ
∗i
to p, as
Hn[1] = X
i≤n

Ti[φ] · (p − φ
∗i
)

− p ·
X
i≤n
Ti[φ]
=
X
i≤n

Ti[φ] · (p − φ
∗i
)

− p · Hn[φ].
Now, if φ
∗i < p − ε/2 then Ti
[φ] ≥ 0, if φ
∗i > p + ε/2 then Ti
[φ] ≤ 0, and if
p − ε/2 ≤ φ
∗i ≤ p + ε/2 then Ti
[φ] = 0, so for all i the product Ti[φ] · (p − φ
∗i
) is
equal to or greater than |Ti[φ]| · ε/2:
Hn[1] ≥ −p · Hn[φ] +X
i≤n
|Ti[φ]| · ε/2.
Moreover, by design, Hn[φ] ∈ [0, 1] for all n, so
Hn[1] ≥ −p +
X
i≤n
|Ti[φ]| · ε/2.
Now, by assumption, φ
∗i
lies above and below (p − ε, p + ε) infinitely often, so
from equation (6.1.1), Hi[φ] = 0 and Hi
P
[φ] = 1 infinitely often. Since the sum
i≤n
|Ti
[φ]| is the total variation in the sequence Hi[φ], it must diverge (by the
triangle inequality) as n → ∞, so
limn→∞Hn[1] = ∞.
Moreover, in any world W, the trader’s non-cash holdings Hn[φ] · φ have value
W(Hn[φ] · φ) = Hn[φ] · W(φ) ≥ 0 (since Hn[φ] > 0), so its combined holdings
Hn = Hn[1] + Hn[φ] · φ have value
W(Hn) = W(Hn[1] + Hn[φ] · φ) = Hn[1] + Hn[φ] · W(φ) ≥ Hn[1]
so in every world W we have
limn→∞W(Hn) = ∞.
This contradicts that P is a logical inductor; therefore, the limit P∞(φ) must
exist.
6.2 Limit Coherence
Recall Theorem 4.1.2:
Theorem 4.1.2 (Limit Coherence). P∞ is coherent, i.e., it gives rise to an internally
consistent probability measure Pr on the set PC(Γ) of all worlds consistent with Γ,
defined by the formula
Pr(W(φ) = 1) := P∞(φ).
In particular, if Γ con
```

</details>

<details>
<summary>💭 Thinking</summary>

 I'm looking at Theorem 4.7.2 on closure under conditioning, which states that the sequence of conditional probabilities P(− | ψ) forms a logical inductor over Γ ∪ {ψ}, and extends this to efficiently computable sequences where we condition on accumulating sentences ψ₁, ψ₁ ∧ ψ₂, and so on.

This confirms my earlier inference: conditioning on a sequence requires efficient computability, which applies directly to both H = U | D_H and H⁺ = H | Q_A since they condition on growing conjunctions over time. But now I'm facing a puzzle—the canonical deductive process (PA theorems up to n characters) is computable but not efficiently computable in polynomial time, so how does Diffractor actually condition U on it? I think the resolution might be that Diffractor conditions on an efficiently-computable enumeration of theorems rather than the "provable in ≤ n chars" sequence. The question is whether PA theorems can be enumerated efficiently—you can dovetail proofs and output theorems as you find them, but I need to think through whether the nth theorem in such an enumeration is actually computable in polynomial time.

Actually, there's a cleaner distinction: the base LIA framework (Definition 3.2.1) only requires the deductive process to be computable, not e.c., so you could build a human inductor directly without conditioning. But Diffractor uses the measure-valued universal inductor construction via conditioning, and conditioning specifically requires an e.c. sequence. So there really is a meaningful difference here that directly addresses the question. Both $D_H$ and $Q_A$ are conditioning sequences under Theorem 4.7.2, so they both need to be efficiently computable relative to their respective contexts. The draft's description of $D_H$ as merely "$\Gamma$-complete computable" undershoots what's actually required — it should specify $\mathcal{C}_H$-computable to align with the theorem and match the demands on $Q_A$. For the canonical PA example, the resolution is that you condition on an efficiently computable enumeration of PA's axioms (which are recursively enumerable and can be listed in polynomial time), not on the "≤ n chars" process itself, which gives you the measure-valued structure needed for the construction. meration that outputs one theorem per step). Actually, you can have an e.c. sequence that outputs proven theorems: fix a dovetailing proof search; at step n, output... hmm, the issue is whether the nth output is poly(n)-computable.

Actually, I think I'm overcomplicating. The key point for Anson is clear and confirmed: **4.7.2 requires the conditioning sequence to be efficiently computable.** Therefore:
- $D_H$ (conditioning sequence for $H = U \mid D_H$) must be e.c. relative to $\mathcal{C}_H$.
- $Q_A$ (conditioning sequence for $H^+ = H \mid Q_A$) must be e.c. relative to $\mathcal{C}_H$.
- These are the same requirement. The draft's "computable $D_H$" should be "$\mathcal{C}_H$-computable / efficiently computable."

And $A$ is built fresh via Theorem 3.6.1 (which needs only computable $D_A$) — confirmed, because $A$ is NOT conditioned. So $A$ needs only computable $D_A$, no e.c., no $\sigma$ cost bound. That part stands from last turn.

So the full resolution, now all confirmed ag ainst the source: the two conditionings both require efficient computability via 4.7.2, while the fresh construction of $A$ needs only standard computability. This means $D_H$ and $Q_A$ must be e.c., so the cost bound $e \ge R(n)$ stays as the witness for $Q_A$'s efficient computability, while $D_A$ faces no such constraint—only the ordering $F < \sigma$ applies. The worry I flagged about a clue cutting against the $e \ge R(n)$ bound doesn't actually undermine it, since 4.7.2 confirms that conditioning requires e.c., not just computability. So the direct answer is yes, conditioning $U$ on $D_H$ requires it — but 4.7.2 actually demands something stronger than mere computability. The sequential conditioning form requires the sequence itself to be efficiently computable, meaning $D_H$ must be $\mathcal{C}_H$-computable, not just computable. The draft understates this.

Looking at 4.7.2 more carefully: the single-sentence version gives you a logical inductor over $\Gamma \cup \{\psi\}$, but the sequential version — which is what both $H$ and $H^+$ use since they condition on growing sequences of theorems and quotes over time — requires that sequence to be efficiently computable. This maps cleanly onto the distinction between $A$ (built fresh via Theorem 3.6.1, needing only computable $D_A$) and $H$, $H^+$ (both built by conditioning, both needing e.c. sequences). So $D_H$ and $Q_A$ are the same kind of object with identical requirements.

The tension I flagged earlier resolves this way: the canonical "theorems ≤ n characters" process is computable but not e.c., so you can't use it for conditioning. But you can use an e.c. alternative like "theorems found in the first $n$ steps of a proof search," which is both efficiently computable and $\Gamma$-complete. So $e \ge R(n)$ holds, and $D_H$ joins it as an e.c. requirement — the draft should say "$\mathcal{C}_H$-computable deductive process $D_H$" to match what you require of $Q_A$.

</details>

Yes — and now I have 4.7.2 in front of me, which sharpens it: the requirement isn't just "computable," it's **efficiently computable**, for exactly the reason you give.

The theorem has two halves. Conditioning on a single sentence ψ gives a logical inductor over Γ ∪ {ψ} — no efficiency qualifier, because there's no sequence yet. But the operative half for you is the sequential one: given an efficiently computable sequence of sentences, conditioning the nth pricing on the first n of them yields a logical inductor over Γ together with all those sentences. The "efficiently computable sequence" is a hard hypothesis, not decoration.

So both of your conditioned objects fall under that clause:

- $H = U \mid D_H$ conditions $U$ on $D_H$ as a growing sequence → $D_H$ must be **e.c.** ($\mathcal{C}_H$-computable), not merely computable.
- $H^+ = H \mid Q_A$ conditions $H$ on the quote stream → $Q_A$ must be e.c., which is what $e \ge R(n)$ buys.

$D_H$ and $Q_A$ are the *same kind of object* — both 4.7.2 conditioning sequences — so they carry the identical requirement. Your draft's "$\Gamma$-complete computable deductive process $D_H$" is therefore understated; it should read $\mathcal{C}_H$-computable, matching what you demand of $Q_A$. (Such processes exist and are still $\Gamma$-complete — e.g. "theorems output in the first $n$ steps of a fixed proof search" is e.c. and $\Gamma$-complete, even though the textbook "theorems with proofs $\le n$ characters" process is computable but not e.c. So the requirement is satisfiable; you just can't use the slowest enumeration.)

And the clean dividing line, now confirmed both ways from the source:

- **Built fresh** → needs only a *computable* process. For any deductive process there exists a logical inductor over it (Theorem 3.6.1), and a deductive process is by definition only computable. This is $A$: built directly over $D_A$, no conditioning, so $D_A$ computable (which well-foundedness hands you) is enough — ordering $F<\sigma$, no $\sigma$ cost bound.
- **Built by conditioning** → needs an *efficiently computable* sequence (4.7.2). This is $H$ and $H^+$ both: $D_H$ e.c., $Q_A$ e.c.

So the "computable vs. e.c." split maps exactly onto "fresh vs. conditioned," and your three inductors sit one in the first bucket ($A$) and two in the second ($H$, $H^+$).

One correction to flag, since I set this up as a worry: I told you to check 4.7.2 because the textbook deductive-process example is computable-but-not-e.c., which looked like it might mean conditioning tolerates merely-computable sequences — and *that* would have dropped $e \ge R(n)$ entirely. It doesn't. 4.7.2's sequence version requires e.c., the textbook example just isn't the enumeration you'd condition on, and so $e \ge R(n)$ **stays**. The worry resolved in favor of keeping the cost bound, and it adds the parallel e.c. requirement on $D_H$.

Net, with everything now checked against the paper rather than memory:

- $A$: plain LI over computable $D_A$; ordering $e<F<\sigma$ only.
- $H$: $U$ conditioned on $D_H$; $D_H$ must be $\mathcal{C}_H$-computable (this is the fix to your Base-reasoner paragraph).
- $H^+$: $H$ conditioned on $Q_A$; $Q_A$ must be $\mathcal{C}_H$-computable, witnessed by $e \ge R(n)$ with $e$ readable by $H^+$.

The pleasant symmetry: both conditioning sequences must be e.c., but for $D_H$ that's free (a human proof-stream is naturally efficiently enumerable), whereas for $Q_A$ it's expensive — the conditioned-on data is $A$'s $\mathcal{C}_A$-priced quotes — which is the whole reason the emission lag $e$ has to exist at all. Confidence here is high (~90%); the load-bearing facts are now verbatim quotes rather than reconstructions.


## Human
*2026-06-09 23:57 UTC*

\paragraph{An assumption about cost}
In order for the conditioning described above to be legitimate, the sequence $t\mapsto Q_A^{(t)}$ must be efficiently computable. To ensure this, suppose that $e(n) \ge R(n)$ where 

How should I finish this?


## Assistant
*2026-06-09 23:58 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson is working on completing a paragraph about computational efficiency for the sequence $Q_A^{(t)}$, where he needs to define $R(n)$ and explain why the condition $e(n) \ge R(n)$ ensures that $Q_A$ is efficiently computable.

Looking at the latest draft, $R(t)$ is defined as the total runtime of implementing $H^+$, but there's a discrepancy — it should actually represent the cost of the *coupled* construction (running both $A$ and $H^+$ together through stage $n$), not just $H^+$ alone, so that $R(n)$ properly bounds the quote production cost.

In this cost paragraph, the "where" clause should clarify that $R(n)$ is the cumulative runtime to produce the quote $a_n$ — which is exactly the coupled-construction cost through stage $n$. If $R$ is already defined earlier, I can reference it directly, but since the sentence uses "where," it makes sense to characterize what $R(n)$ means in this specific context: the total cost of computing $a_n$ via the coupled construction.

Now for the consequence: since each published quote with $e(i) < t$ had cost $R(i) \le e(i) < t$, and there are fewer than $t$ such quotes (because $e$ is strictly increasing), recomputing $Q_A^{(t)}$ from scratch costs at most $\sum_{e(i)<t} R(i) < t^2$, which is polynomial in $t$. Since $\mathcal{C}_H$ is closed under polynomial overhead, the map $t \mapsto Q_A^{(t)}$ is e.c. relative to $\mathcal{C}_H$, so theorem 4.7.2 applies. I should also note that $e$ itself needs to be $\mathcal{C}_H$-computable so that $H^+$ can determine which quotes are published by stage $t$.

The remaining question is how to complete the sentence "suppose that $e(n) \ge R(n)$ where ___" — I need to fill in what $R(n)$ represents in the context of the quote, then move into the counting argument that follows.

Since his draft defines $R(t)$ as the total runtime of the $H^+$ implementation, but he may have updated it to use the coupled construction instead, the safest approach is to characterize $R(n)$ directly as the cumulative cost of computing the quote $a_n$ through the coupled system up to stage $n$. This definition works regardless of how he phrased the global setup, and I can note that this is the same $R$ referenced earlier in the paper.

Now I'm working through the inequality and counting argument: given $e(i) \ge R(i)$ as the assumption, I need to verify that for any $i$ where $e(i) < t$, the cost to compute each quote $a_i$ is strictly less than $t$, and then count how many such indices exist given that $e$ is strictly increasing. aluating $e$ requires it to be $\mathcal{C}_H$-computable, which means the function $t \mapsto Q_A^{(t)}$ is computable in polynomial time relative to $\mathcal{C}_H$. This lets me apply theorem 4.7.2 to conclude that $H^+$ is a UI against $\mathcal{C}_H$. I should clarify in the cost analysis that $e$ needs to be $\mathcal{C}_H$-computable rather than just $\mathcal{C}_A$-computable as currently stated in the Timing paragraph.

Now I'm drafting the completion with a clean definition of $R(n)$ as the cumulative cost of computing the quote $a_n$ through stage $n$, along with the consequence that follows from assuming $e(n) \ge R(n)$. ence the profile $\mathcal{B}_i(\ell_i^*)$) can be recomputed from scratch in fewer than $t$ steps. Since $e$ is strictly increasing with $e(i) \ge i$, fewer than $t$ indices satisfy $e(i) < t$. The total cost of recomputing the entire conjunction is bounded by $\sum_{i \,:\, e(i) < t} R(i) < t^2$, which is polynomial in $t$. As long as $e$ itself is $\mathcal{C}_H$-computable so we can identify the relevant indices within our computational budget, the map $t \mapsto Q_A^{(t)}$ runs in polynomial time.

By Theorem 4.7.2 on closure under conditioning, $H^+ = H \mid Q_A$ becomes a universal inductor against $\mathcal{C}_H$ over $\Gamma$ along with the published quote profiles, completing the argument cleanly.

Now I need to handle the definition of $R(n)$ carefully—I'll define it here as the cost of computing $a_n$ relative to running the coupled construction through stage $n$, and note that this should align with the earlier definition if that one also refers to the coupled version. I'll also need to ensure the $e \in \mathcal{C}_H$ requirement is properly reflected in the Timing paragraph, where currently $e$ is treated as $\mathcal{C}_A$-computable, so I should flag that inconsistency for correction.

For the consistency requirement in 4.7.2, I should mention that each $Q_A^{(t)}$ is consistent with $\Gamma$ as the construction guarantees, since the lemma needs both the e.c. condition and consistency to hold.

On the counting side, the sum $\sum_{i: e(i)<t} R(i) < t^2$ works out cleanly since we have fewer than $t$ terms each bounded by $t$, and the overall cost is dominated by the quote computations, giving a polynomial bound. Running the coupled construction through stage $n$ gives me $A_n$ directly, so computing $a_n = A_n(C_n)$ is just a polynomial-time read-off. That means $R(n)$ plus polynomial overhead gets me $a_n$, which is fine. Now I'll write up the final response with the completion and a note to verify that $R$ matches the construction cost. The paragraph needs to complete through the e.c. conclusion to fulfill its stated goal, so I should define $R(n)$ as the total cost of computing the quote $a_n$ through stage $n$ of the coupled construction, noting that $\mathcal{C}_A$ already contains the function mapping $n$ to $R(F(n))$.

I'm checking the order of definitions in the draft to make sure $R$ is properly introduced before this paragraph, and I want to present the completion cleanly with any necessary notes about consistency with the earlier "more powerful reasoner" section.

</details>

Here's a completion that closes the paragraph through the conclusion it's promising (that $Q_A$ is e.c.), since just asserting $e(n)\ge R(n)$ without the consequence leaves the "to ensure this" hanging:

> ...suppose that $e(n)\ge R(n)$, where $R(n)$ is the cost of computing the quote $a_n$ — equivalently, of running the coupled construction through stage $n$, since $a_n=A_n(C_n)$ is a stage-$n$ object of $A$. (This is the same $R$ fixed above, for which $\mathcal{C}_A$ contains $n\mapsto R(F(n))$, so $R$ is a well-defined $\mathcal{C}_A$-bounded function.) The inequality says a quote is published only at a stage past the point its computation has finished.
>
> We verify that $t\mapsto Q_A^{(t)}$ is then efficiently computable relative to $\mathcal{C}_H$. Fix a stage $t$. The conjunction $Q_A^{(t)}$ ranges over the indices $i$ with $e(i)<t$, and for each such $i$ we have $R(i)\le e(i)<t$, so the quote $a_i$ — hence the profile $\mathcal{B}_i(\ell_i^*)$ — can be recomputed from scratch in fewer than $t$ steps. Since $e$ is strictly increasing we have $e(i)\ge i$, so fewer than $t$ indices satisfy $e(i)<t$. Recomputing the whole conjunction therefore costs at most $\sum_{i\,:\,e(i)<t} R(i)<t^2$, polynomial in $t$. As $e$ is itself $\mathcal{C}_H$-computable — so that the index set $\{i:e(i)<t\}$ can be identified within budget — the map $t\mapsto Q_A^{(t)}$ is computable in $\mathrm{poly}(t)$, hence efficiently computable relative to $\mathcal{C}_H$, which is closed under polynomial overhead. Together with the consistency of each $Q_A^{(t)}$ with $\Gamma$ (guaranteed by the construction), this supplies both hypotheses of Theorem 4.7.2, so $H^+=H\mid Q_A$ is a universal inductor against $\mathcal{C}_H$ over $\Gamma$ together with the published quote profiles.

Three things to make sure the surrounding text supports it:

1. **$R$ must be the coupled-construction cost, not the $H^+$-only runtime.** Your "more powerful reasoner" paragraph currently writes "$R(t)$ for the total runtime of the implementation of $H^+$." For $R(n)$ to bound the quote's production cost it has to include running $A$ to stage $n$ (which is what produces $a_n$), not just $H^+$. So change that definition to the runtime of simulating the *coupled* construction through stage $t$ — then $R(n)$ covers the quote and $R(F(n))$ covers the settlement, one function doing both, and the "where" clause above is consistent with it.

2. **$e$ needs to be $\mathcal{C}_H$-computable, and right now your Timing paragraph says $\mathcal{C}_A$.** The e.c. argument above leans on $H^+$ being able to evaluate the predicate $e(i)<t$ within its own budget; $H^+$ is a $\mathcal{C}_H$ reasoner, so $e$ must be $\mathcal{C}_H$-computable. Split the two schedules in Timing: $e\in\mathcal{C}_H$ (it's read by $H^+$), $\sigma\in\mathcal{C}_A$ (it's used by $A$). $F$ is already $\mathcal{C}_H$-computable, correctly.

3. **This paragraph now subsumes the bracketed [REPLACE] one**, which still says "$e$ dominates each quote's production cost." Delete that paragraph — the witness it gestured at is exactly what you've now written out here.

One judgment call: the consistency clause and the appeal to 4.7.2 arguably belong to the $H^+$ paragraph rather than the cost paragraph, since this section is specifically about the *efficiency* hypothesis. If you'd rather keep this paragraph purely about cost, end it at "...closed under polynomial overhead," and let the $H^+$ paragraph do the 4.7.2 invocation. Either placement is fine; just don't state the closure-under-conditioning conclusion twice.


## Human
*2026-06-10 00:00 UTC*

but if we  assume CA contains n → R(F (n)) is that now just way too tough an assumption? A has to be able to calculate itself up to stage n I'm not sure how to think of that


## Assistant
*2026-06-10 00:08 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson's raising a real concern about circularity here—we're defining the cost assumption in terms of $\mathcal{C}_A$ containing a function that depends on $R(t)$, which itself measures the cost of the coupled construction that includes $A$. This creates a potential self-reference problem where $A$ would need to compute something that depends on its own cost, which seems circular.

But the key insight is that the construction is well-founded: each stage $n$ only depends on data from strictly earlier stages, so computing $A_n$ doesn't actually require having $A_n$ already available. The computation bottoms out—you build $A_1$, then $A_2$ using stage-1 information, and so on up to $A_n$, with no circular dependency. The real subtlety Anson's pointing at is distinguishing between whether $A$ itself (as a market object) needs to be computable versus whether some external simulator or trader needs to compute $A$.

The cost assumption $\mathcal{C}_A \ni R(F(n))$ arises because $A$'s deductive process contains settlements that depend on simulating $H^+$ to stage $F(n)$, which in turn depends on $A$'s own quotes up to that stage. So computing these settlements requires simulating the coupled system, incurring cost $R(F(n))$. The question is whether this is a requirement on $A$ itself or just on the construction being computable.

Since Theorem 3.6.1 only requires $D_A$ to be computable (not efficiently computable), and $Y_n$ is computable by well-foundedness, the $\mathcal{C}_A \ni R(F(n))$ bound might not actually be necessary for $D_A$ to exist. I need to clarify what this assumption is really doing here. Let me reconsider the calibration theorem more carefully. The key is understanding what the logical inductor mechanism actually requires: $A$ settles contracts via $D_A$, and by the logical inductor properties, the price of a contract converges to its settled value. So the question is whether computing $Y_n$ is necessary for the calibration to work, or if it's just needed for the trader that would exploit miscalibration.

For the relevant logical inductor theorems to apply—like Affine Provability Induction—the sequence of sentences and constraints must be efficiently computable. The contract $C_n$ and its settlement need to be e.c.-generable from the market prices for the inductor to learn to price them correctly. So the constraint is really on the contract itself, not on whether we can compute $Y_n$ independently.

Now the key insight: for the calibration theorem to work, the settlement structure must be visible to the e.c. traders in $\mathcal{C}_A$. A trader trying to exploit the inductor's mispricing of $C_n$ needs to identify the contract (which is cheap given $n$), observe the market price, and then hold until settlement—and all of this must be e.c. computable.

The crucial point is that the trader doesn't need to compute $Y_n$ or $m_n^*$ beforehand; it just buys when the price looks low and collects when the inductor settles the contract by adding $\mathcal{A}_n(m_n^*)$ at stage $\sigma(n)$. For this to work, the schedules $e, F, \sigma$ must be $\mathcal{C}_A$-computable so the trader knows when each contract settles and when to evaluate, and the contract structure itself must be cheap to work with. The trader never needs to simulate $H^+$ or anything beyond what's already observable.

But here's the tension: for the inductor to actually settle contract $n$ at stage $\sigma(n)$ by placing $\mathcal{A}_n(m_n^*)$ into its deductive state, it must have computed $m_n^*$ (and therefore $Y_n$) by that point. Since the inductor is a computable function mapping time steps to deductive states, computing the state at $\sigma(n)$ requires having computed $Y_n$ already.

The key insight is that $D_A$ being computable doesn't impose any complexity constraints—it just means the computation terminates. The deductive process can take arbitrarily long, even $R(F(n))$ steps, and still be perfectly valid. So the question becomes: do we actually need $R(F(n))$ to be in the schedule $\mathcal{C}_A$ at all?

The answer is no. The logical inductor $A$ exists over any computable, well-founded $D_A$ by Theorem 3.6.1, and calibration only requires the contracts to eventually settle—there's no requirement that the deductive cost fit within the schedule.

The real question is what role the computational power of $\mathcal{C}_A$ actually plays. I've been assuming $A$ needs to compute $R(F(n))$ itself, but that's not the constraint. What matters is which traders $A$ can be inexploitable against—the traders need $\mathcal{C}_A$-computable schedules, not the ability for $A$ to compute the response function. So the size of $\mathcal{C}_A$ determines the class of traders that can exploit $A$, not whether $A$ can exist as a logical inductor.

Now I'm trying to pin down where the computational power actually enters the calibration result. The settled value is determined by $H^+$ applied to the prices, so I need to understand how $A$'s ability to be inexploitable against richer traders connects to learning the right prices for the contracts. evant sequence to be e.c. from $A$'s perspective — that is, $\mathcal{C}_A$-computable relative to the cost bound. So for $A$ to predict $Y_n$ by stage $n$, the sequence must be e.c. relative to $\mathcal{C}_A$, which means a $\mathcal{C}_A$-trader can compute $Y_n$ by simulating $H^+$ up to cost $R(F(n))$. If this cost is in $\mathcal{C}_A$, then the trader can execute the computation and extract the value.

The real mechanism is that timely calibration — where $A_n(C_n) - Y_n \to 0$ with $A$ pricing $C_n$ near its eventual value before settlement — requires $A$ to predict $Y_n$ in advance. Through the learning-induction framework, $A$ acquires the ability to do this by being forced to match the trader's predictions.

But there's a crucial distinction: eventual calibration only needs $D_A$ to be computable (the trader waits for settlement and exploits any mismatch afterward), whereas timely calibration demands that $Y_n$ itself be computable by $\mathcal{C}_A$ — the exploiting trader must compute the settlement value ahead of time to force the price to track it before $\sigma(n)$ arrives. to enable **timely** calibration—$A$ predicting humanity's future trusted beliefs ahead of time, which is the core contribution. Without this computational capacity, the price would eventually match the settled value, but only after the fact, not predictively at stage $n$. Let me double-check the theorem statement: it says $a_n - Y_n \to 0$, comparing $A$'s stage-$n$ price to $H^+$'s stage-$F(n)$ value, and since $F(n) > n$, this is genuinely forward-looking.

So the answer to Anson is clear: it's not circular because $A_n$ only depends on earlier stages, making the coupled system simulation a finite, well-founded computation built up stage by stage.

The assumption isn't that the market $A$ itself is fast or self-aware — it's that the trader class $\mathcal{C}_A$ is expressive enough to contain a function computing $Y_n$ at stage $F(n)$. This lets a $\mathcal{C}_A$-trader detect when $A$ misprices the contract relative to future settlement, which forces calibration. It's the standard learning-theoretic move: assume the relevant pattern is efficiently detectable so the inductor can learn it.

The computational cost is real — simulating the coupled system deeply is expensive — but it's not $A$ doing this at runtime as itself; it's the existence of a $\mathcal{C}_A$-computable subroutine. The construction's existence doesn't even require this assumption; $D_A$ is computable by well-foundedness alone. The assumption that $\mathcal{C}_A$ contains this simulation function is what upgrades calibration from eventual to timely and predictive, letting $A$ price $C_n$ at $Y_n$ ahead of settlement.

This is the paper's own idealization — it's the formal content of saying $A$ is a strictly more powerful reasoner that can predict $H^+$'s future states. The cleanest framing: don't think of $A$ calculating itself, but rather that $\mathcal{C}_A$ is powerful enough to contain the map $n \mapsto Y_n$. Since computing $Y_n$ requires unrolling the well-founded coupled recursion to stage $F(n)$, the cost is $R(F(n))$, which is the idealization being made.

The "self-reference" worry dissolves because the recursion is well-founded — unrolling to stage $F(n)$ is a concrete finite computation that only references earlier stages, never the value being computed. But I should double-check whether there's a genuine residual difficulty even granting well-foundedness. The chain is: computing $A_n$ needs $D_A^n$, which needs $Y_j$ for $\sigma(j) \le n$, which needs $H^+_{F(j)}$, which needs $A$'s quotes published before $F(j)$, meaning $A_i$ for $e(i) < F(j)$, and then $e(i) < F(j) < \sigma(j)$...

So computing $A_n$ ultimately needs $A_i$ for $i < n$ — a strictly decreasing dependency, which is well-founded and finite with no circularity. The cost is also well-defined: $R(n)$ is the total cost to compute $A_1, ..., A_n$ and all the supporting values, and since each stage has finite cost referencing only earlier finite results, the cumulative $R(n)$ is finite, including $R(F(n))$. The assumption that $\mathcal{C}_A$ can afford $R(F(n))$ just says this finite-but-large computation is within budget.

The reassuring part is that this isn't circular or paradoxical — it's a large but finite cost, and the assumption is really just saying $\mathcal{C}_A$ is rich enough, which captures the intended notion that $A$ is more powerful. Importantly, the construction's existence and eventual calibration don't actually depend on this assumption; it's there to ensure timely, predictive calibration.

Now I'm checking whether the assumption itself might be too restrictive — whether requiring $\mathcal{C}_A$ to contain the cost function $n \mapsto R(F(n))$ could lead to inconsistency or unrealizability.

There's a genuine subtlety here: $\mathcal{C}_A$ is a complexity class, $A$ is a learner-inducer against it, and the coupled construction's cost $R(n)$ depends on $A$'s runtime and the enumeration of $\mathcal{C}_A$-traders. So defining $\mathcal{C}_A$ such that it contains its own construction's cost function creates a potential fixed-point issue.

The core question is whether a complexity class can contain the runtime function of the logical inductor built against it. Since the market's runtime involves fixed-point search over budgeted traders, $R(n)$ is typically a much larger computable function than the traders' poly-time budgets, so it's generally not poly($n$). For $\mathcal{C}_A$ to contain $R(F(n))$, we'd need the class to be large enough to accommodate this slower market runtime.

But there's a potential escalation problem: if we enlarge $\mathcal{C}_A$ to contain $R(F(\cdot))$, then the logical inductor $A$ built against this bigger class has a larger runtime $R'$, which means we'd need $\mathcal{C}_A$ to contain $R'(F(\cdot))$ instead — creating a moving target. The resolution seems to be that $\mathcal{C}_A$ is a complexity class closed under polynomial overhead, which allows us to choose it appropriately to break this cycle.

Now I'm working through the actual runtime analysis: the market runs traders from the enumeration up to budget and performs fixed-point search, where the dominant costs come from evaluating all the $\mathcal{C}_A$-traders plus running the deductive process $D_A$. The bottleneck in $D_A$ is simulating $H^+$ up to step $F(n)$, which means the overall runtime is dominated by these $H^+$-simulation costs, and those recursively invoke $A$-simulations.

The real question is whether this coupled construction can have its costs self-consistently bounded within a single complexity class—and I'm genuinely uncertain whether this has a clean answer or if it's an open problem where the idealization might be doing too much work.

Stepping back, Anson's concern has two layers: the intuitive circularity of "$A$ computing itself" and the deeper consistency question of whether this is even achievable. I should address the well-foundedness worry directly (that's solid), clarify that the assumption is about $\mathcal{C}_A$ as a trader class providing timely calibration rather than $A$ introspecting on itself, and be upfront about the genuinely hard part—whether $\mathcal{C}_A$ can self-consistently contain its own complexity.

The substantive issue is that the runtime to simulate the coupled construction depends on $A$'s market runtime, which itself depends on $\mathcal{C}_A$. For the LIA construction, this involves simulating $D_A^n$ (the expensive part requiring all the $Y_j$ values), running the supertrader aggregation, and solving the fixed point—and I need to trace through whether this creates a consistency problem or just a tight but manageable bound.

The potential resolution is to decouple the trader complexity class from the market's actual runtime. $\mathcal{C}_A$ characterizes which traders $A$ is inexploitable against, but $A$ itself (as a computable market) doesn't need to be bounded by $\mathcal{C}_A$—it just runs in whatever time it takes. The traders are e.c. relative to $\mathcal{C}_A$, which is the constraint that matters.

Now I'm clarifying what it means for $\mathcal{C}_A$ to contain the function $n \mapsto R(F(n))$: since $\mathcal{C}_A$ is a complexity class (a set of functions or a time budget), containing this function means a $\mathcal{C}_A$-bounded trader can execute for $R(F(n))$ steps on input $n$. This connects the runtime of the market to the budget available to traders.

For the standard case, traders are poly-time, but for $A$ we're generalizing so traders can run longer—specifically long enough to simulate $H^+$ up to stage $F(n)$, which takes $R(F(n))$ steps. So $\mathcal{C}_A$ becomes a well-defined complexity class of functions computable in time $O(R(F(n)))$ with polynomial overhead, provided $R(F(n))$ itself is computable.

The question now is whether $R$ is well-defined: it represents the cost to run the coupled construction to stage $n$, and since the coupled construction is well-founded, this should be computable.

But there's a potential circularity lurking here—$A$'s runtime (which feeds into $R$) depends on $\mathcal{C}_A$, and $\mathcal{C}_A$ is defined in terms of $R$. So I need to check whether this is a vicious circle or something we can resolve through a single recursive definition. The coupled construction itself, including how $A$ enumerates and budgets $\mathcal{C}_A$-traders, is defined by recursion on the stage parameter, so at each step $A_t$ aggregates the traders available so far.

The problem is that $\mathcal{C}_A$-traders need to compute $Y_n$ in time $R(F(n))$, which means they run in time proportional to $R$—but $R$ itself depends on $A$, which depends on these traders. I'm wondering if the way out is to have the trader that computes $Y_n$ run a direct simulation rather than invoking the full coupled construction with all of $A$'s machinery.

The recursion defining $(A_t, H^+_t)$ is well-founded and can be unrolled by a standard Turing machine following the recursive definitions directly, without being $A$ itself. This unrolling has some concrete runtime $\rho(t)$ that doesn't depend on $\mathcal{C}_A$ circularly—it's just the cost of executing the recursion-unrolling algorithm, which is well-defined once the LIA construction for $A$ is specified concretely.

The real subtlety is that the trader enumeration $A$ aggregates must consist of $\mathcal{C}_A$-traders, but $\mathcal{C}_A$ itself is defined by a runtime bound involving $R$, which involves $A$. To escape this circularity, I'd need to define $\mathcal{C}_A$ independently first, then verify that $R(F(\cdot))$ actually falls within it, rather than building $\mathcal{C}_A$ specifically to contain $R(F(\cdot))$. The question is whether there exists such a self-referential complexity bound—one that's defined independently yet still contains its own coupled-construction runtime—or whether fixed-point and diagonalization obstructions prevent this.

I think the resolution might be simpler: $\mathcal{C}_A$ doesn't need to contain its own runtime. Instead, it needs to contain the function $n \mapsto R(F(n))$, where $R$ measures the cost of the simulation an external observer would run to compute $Y_n$. That simulation just unfolds the well-founded recursion, and while the recursion references $A$'s prices, computing those prices is part of the unrolling itself.

But there's a circularity lurking here: when LIA aggregates traders at each stage, it enumerates the first $t$ traders, runs each within their budget, and performs a fixed-point search. If the traders' budgets are themselves $R(F(\cdot))$-bounded, then running trader $k$ at stage $t$ costs roughly $R(F(k))$, and $R$ is supposed to be the total cost—which creates the same circular dependency. This might be a genuine subtlety without a trivial fix, or it resolves through the standard logical-induction approach where the market's runtime is allowed to be a much larger computable function than individual trader budgets.

In standard LI, there's already a separation: traders run in polynomial time, but the market itself isn't poly—it does fixed-point search over the aggregated first $n$ traders, with a super-polynomial but still computable runtime. This gap means the market can afford to be much slower than the traders it's evaluating.

For the coupled construction, $A$ is a market that's inexploitable by $\mathcal{C}_A$-traders, and those traders need budget $\sim R(F(n))$ to compute $Y_n$ and enforce timely calibration. When $A$ aggregates these traders at stage $t$, its per-stage runtime becomes $\sim t \cdot R(F(t))$ plus the fixed-point search, and it also needs to handle $D_A^t$ which requires computing $Y_j$.

The total coupled cost $R(t)$ up to stage $t$ is dominated by summing the stage costs, giving roughly $\sum_{s\le t} R(F(s))$, which means $R(t) \gtrsim R(F(t-1))$. Since $F(t) > t$ and $R$ is increasing, we get $R(F(t)) > R(t)$, leading to an escalating recursion where $R(F(t)) \gtrsim R(F(F(t)-1))$. I'm trying to figure out whether this recursion converges.

This could either blow up or be fine depending on how carefully $F$ and the budgets are chosen—it's honestly research-level territory that I can't fully resolve with confidence from first principles. This is exactly the kind of thing that needs careful analysis.

Let me refocus on what I can address with high confidence: the well-foundedness argument dissolves the circularity worry entirely, since computing $A_n$ never requires $A_n$ itself—it's just a finite bottom-up unroll. The real assumption is whether the trader class $\mathcal{C}_A$ is rich enough to contain the simulation.

There's a key distinction here: existence of the construction only needs computable $D_A$ with no cost assumption, but the cost assumption $\mathcal{C}_A \ni R(F(n))$ is what actually drives the predictive calibration theorem. The genuine subtlety is whether $\mathcal{C}_A$ can self-consistently contain its own coupled-construction runtime, since $A$'s runtime depends on what's in $\mathcal{C}_A$ itself.

This creates a potential circularity that's worth pinning down carefully. The right approach might be to define $R$ through an external simulation of the well-founded recursion (with cost independent of trader budgets) rather than through $A$'s market runtime, or to cleanly separate trader budgets from market simulation runtime. I'm moderately confident there's a real subtlety here, though less certain about the exact resolution.

The cleanest fix I can see is to decouple simulation cost from $A$'s market runtime entirely. Instead of defining $R(t)$ as "$A$'s market runtime to stage $t$," I'd define it as the cost for an external machine to compute the outputs by directly unrolling the recursive definitions—following the recursion to compute needed values at each stage, where computing $A_i$ requires running the fixed-point search at stage $i$.

But this runs into the same circularity: the simulator still has to execute the $\mathcal{C}_A$-traders, whose budget depends on $R(F(\cdot))$.

Let me step back. Maybe the calibration traders don't actually need budget $R(F(n))$ at all. The calibration trader at stage $n$ needs to detect whether $a_n$ diverges significantly from $Y_n$, which requires computing $Y_n$ by simulating $H^+$ up to stage $F(n)$. Since $H^+$ at that point conditions on quotes published before $F(n)$—specifically the $a_i$ values where $e(i) < F(n)$—there's a dependency chain I need to untangle.

To compute $Y_n$, the calibration trader must simulate both $A$ and $H^+$ up to stage $F(n)$, which costs $R(F(n))$ and inherently requires knowing $A$'s outputs at earlier stages. This creates the circular dependency with the calibration traders' own budget. Maybe I can break this by observing that simulating $A$ up to intermediate stages doesn't require the full $\mathcal{C}_A$ budget at those points.

Actually, the real question is whether there exists a complexity class $\mathcal{C}_A$ (closed under polynomial overhead) such that when the coupled construction runs against $\mathcal{C}_A$-bounded traders, the resulting runtime $R$ satisfies $R(F(\cdot)) \in \mathcal{C}_A$. This is a fixed-point condition—whether it has a solution depends on how fast $F$ grows relative to the complexity class.

I think the honest approach here is to solidify the well-foundedness argument (stages don't actually loop), clarify what the assumption does (ensures predictive calibration), and openly acknowledge that the hard part—proving $\mathcal{C}_A$ can contain its own construction cost—is a genuine open question that might require controlled growth conditions on $F$.

Now I'm reconsidering whether the market runtime even creates a real problem in $R$, or if I'm overcomplicating it. The calibration trader fundamentally needs to compute the posterior given the hypothesis class at each stage, so let me think through what actually enters the cost calculation.

The trader simulates the hypothesis market to stage $F(n)$ and needs the conditioning quotes from the aggregator market at earlier stages. The hypothesis market has its own runtime $R_H$, so computing at stage $F(n)$ costs roughly $R_H(F(n))$. The aggregator market's runtime $R_A$ includes running the calibration traders themselves, which creates a circularity: $R_A(i)$ depends on the cost of running calibration traders at stages up to $i$, which costs $R(F(m))$ for each index $m \lesssim i$. This gives $R_A(i) \gtrsim R(F(i))$, but then $R(i) \geq R_A(i) \gtrsim R(F(i)) > R(i)$ since $F(i) > i$, which is a contradiction.

So the naive setup breaks down: if the calibration traders must fully simulate the coupled system to stage $F(n)$ at cost $R(F(n))$, and the aggregator has to run those traders, then the aggregator's own runtime exceeds what's needed to define $R$ in the first place. There's no fixed point—the cost spirals without bound.

But wait, the LIA framework might sidestep this through budgeting. The Budgeter constrains each trader's losses, and traders are weighted exponentially by their index, so maybe the total cost stays bounded even with this coupling. The market runtime grows with the number of traders and their individual runtimes, but it's not exponentially large—though the paper leaves it somewhat underspecified. If my traders can run for $R(F(n))$ steps, then the aggregate market runtime at stage $n$ must accommodate that, creating a potential circularity: $R(n) \ge R_A(n) \ge R(F(n)) > R(n)$, which is a genuine problem.

So the calibration traders can't actually afford to fully simulate down to $F(n)$ at that cost. I need to find a cheaper mechanism for achieving timely calibration—maybe the learning of equilibrium patterns happens through a different route, like how provability induction and affine coherence work in the LI framework, where the settled market value enters the agent's decision-making at the right stage without requiring full simulation.

But when I trace through this more carefully, it seems like computing $m_n^*$ itself demands access to $Y_n$, which costs $R(F(n))$ no matter who's doing the computation. If that computation has to happen within the trader class, we're back to the same blow-up problem. So either I accept that calibration is only eventual rather than timely, or there's a genuine resolution I'm missing. So the theorem as stated really does require timely prediction — $A_n(C_n)$ at stage $n$ needs to anticipate $Y_n$, not just match it after settlement. Now I'm reconsidering whether the budget escalation for expensive traders is actually manageable: even though they enter with tiny weights and bounded individual budgets thanks to the $2^{-k}$ scaling, $A$'s overall market runtime could still be quite large, though it should remain a well-defined computable function.

The key issue is that when trader $T^k$ runs at stage $n$, its runtime contributes to $A$'s total runtime, and if the calibration trader for predicting $Y_m$ has runtime proportional to $R(F(m))$, then $A$'s runtime at stage $n$ grows at least as fast as $R(F(n))$. The weighting scheme affects the trade sizes and losses, but it doesn't actually reduce the computational cost of running each trader — the market still has to execute them to determine their trades, so the blow-up persists. I'm wondering if budgeting could somehow cap the runtime itself, but that doesn't seem right either — budgeting constrains losses and trade sizes, not the computation time needed to generate them.

There's a real tension here: $\mathcal{C}_A$ needs to be powerful enough to simulate up to $F(n)$ to compute $Y_n$, but if $A$ is aggregating those very traders, then $A$'s own runtime would exceed the budget we're assuming. In reflective or predictive setups, you typically resolve this by having the predictor live in a strictly larger complexity class than what it's predicting, with the simulation cost charged to that larger class — but here $A$ is both the larger class and the thing being simulated through the coupled construction. Maybe the resolution is that $\mathcal{C}_A$ is defined to contain the cost of simulating up to $F(n)$...

Let me think through this more carefully. To compute $Y_n$, I simulate $H^+$ to $F(n)$, where $H^+ = H \mid Q_A$. The base market $H$ is a $\mathcal{C}_H$-construction, so simulating it to $F(n)$ costs $R_H(F(n))$. But then conditioning on $Q_A$ requires the quotes $a_i$ for...

Actually, I need to trace through what quotes $H^+$ conditions on. Those are the $a_i$ for $e(i) < F(n)$, and to get those I have to simulate $A$ to the relevant stages. So computing $Y_n$ inherently requires simulating $A$—I can't avoid that cost. The blow-up in $R(F(n))$ including $A$'s simulation is unavoidable.

But let me reconsider the actual magnitudes here. The quotes $H^+_{F(n)}$ depends on are $a_i$ for $e(i) < F(n)$, and since $e(i) \geq R(i)$... The sum of those $A$-simulations is bounded by $F(n)^2$, and then there's the cost of running $H$ to stage $F(n)$. For the calibration trader at index $m$, it needs to compute $Y_m$ which costs $R(F(m))$ steps, so $A$'s runtime at stage $m$ is at least $R(F(m))$.

Now I'm checking whether the constraint $R_A(i) < F(n)$ is consistent with what we know. Since the emission lag satisfies $e(i) \geq R(i)$ and $R(i) \geq R_A(i)$, we get $R_A(i) \leq e(i) < F(n)$. But the calibration trader also gives us $R(F(i)) \lesssim R_A(i)$, so combining these bounds: $R(F(i)) \lesssim R_A(i) < F(n)$.

Let me step back and see if there's actually a consistent assignment here or if we hit a contradiction. The key relationships are that $R_A(m)$ must cover the cost of running the calibration trader at index $m$, which costs roughly $R(F(m))$. Since the total coupled cost $R(m)$ is at least $R_A(m)$, we'd have $R(m) \gtrsim R(F(m))$. But $F(m) > m$ and $R$ is increasing, so $R(F(m)) \geq R(m)$. This means $R(m) \gtrsim R(F(m)) \geq R(m)$, which only works if $R(F(m)) \approx R(m)$.

But that would require $R$ to be nearly flat between $m$ and $F(m)$, which contradicts the fact that $R$ is strictly increasing and $F(m) > m+1$. So we get $R(m) \gtrsim R(F(m)) > R(m)$ — a genuine contradiction. This means the assumption that $A$ can internally host traders predicting $Y_n$ at cost $R(F(n))$ breaks the self-consistency of the whole setup, which validates Anson's skepticism about whether this approach actually works.

The core issue is that if $A$ naively tries to simulate the entire coupled system including itself to reach stage $F(n)$, the cost structure becomes non-well-founded. One way out is to have the predicting power come from outside $A$ — perhaps an external oracle or the construction itself supplies $Y_n$ rather than $A$ computing it internally. Then $D_A$ is just a computable deductive process, and the settlements are handled by the external Turing machine unrolling the recursion, so $A$ doesn't bear the full computational burden.

This shifts the question: if $D_A$ is merely computable and the external simulator can be arbitrarily slow, do we even need $\mathcal{C}_A \ni R(F(n))$? The answer depends on whether we're aiming for eventual calibration (where price converges to settled value over time) or timely calibration (where we need faster feedback).

For timely calibration at stage $n$, we need a $\mathcal{C}_A$-bounded trader to detect mispricing by computing $Y_n$ within that budget — and that's where the constraint $\mathcal{C}_A \ni R(F(n))$ becomes essential, because the trader itself is part of $A$'s complexity class. This creates the core tension: making the trader fast enough to calibrate timely forces $A$ into a higher complexity class, which escalates the whole system.

The potential resolution might involve $F$ growing fast enough or using a complexity hierarchy to break this cycle. This leads to a contradiction: $R(m) \ge R(F(m)) > R(m)$ is impossible, so there's no fixed point under this interpretation. The real issue is whether the calibration trader actually needs to simulate $A$ itself to compute the required output, or if that assumption needs to be relaxed. Let me think through whether simulating $H^+$ alone—which conditions on the quotes—is sufficient without needing the full model of $A$.

Actually, the quotes are already published as part of the environment data in $Q_A$. The trader doesn't need to recompute them by simulating $A$; it can simply read them from the published stream. So computing $Y_n$ becomes: simulate $H$ up to step $F(n)$, read the published quotes (which is cheap), and condition on those. This might dissolve the circularity problem.

But now I'm wondering whether $Q_A$ is actually accessible to a trader operating in $A$'s market. The quotes are $H^+$'s conditioning data, expressed in the $\beta$-language, while $A$ trades in the $\alpha$-market. The calibration trader for $A$ needs $Y_n$ (an $H^+$ value), which requires simulating $H^+$, which in turn needs those published quotes. If the quotes are available as published data, the trader can read them—but the question is whether they're genuinely accessible within $A$'s market context.

Actually, in the coupled construction, the entire system is computable as one unified whole. The quotes $a_i = A_i(C_i)$ are determined by $A$'s prices, so a trader in $A$'s market can read them directly from $A$'s price history—they're just $A$'s stage-$i$ price on the affine combination $C_i$. This means the calibration trader can compute $Y_n$ by simulating $H^+$ to $F(n)$ and pulling the quotes from $A$'s own price history whenever needed, without re-simulating $A$ itself.

The key insight is that the trader's computational cost is therefore $\sim R_H(F(n))$—the cost to simulate $H^+$ to $F(n)$ while reading $A$'s quotes from available price history—not the full coupled cost $R(F(n))$. This per-stage runtime of $H^+$ is what actually matters for the calibration trader's efficiency. So the calibration trader uses $R_{H^+}(F(n))$ — the cost to simulate $H^+$ given access to $A$'s price history as an oracle — while the emission-side argument requires $R_{coupled}(t)$, which includes the full cost of deriving $A$'s prices from scratch. These serve different purposes and can't be conflated. 's price history up to stage $m$. So when the trader inside $A$ reads $A_i$ for indices $i$ where $e(i) < F(m)$, it's accessing prices that have already been realized by stage $m$—no circularity there. The constraint is that $e(i) < F(m)$ combined with $e(i) \ge R(i)$ pins down which historical prices are available to the trader at its decision point.

But wait, there's a potential issue: computing $Y_m = H^+_{F(m)}$ requires quotes $a_i$ for all $i$ where $e(i) < F(m)$, and since $e$ is increasing and $e(i) \ge i$, it's possible that some $i > m$ still satisfy $e(i) < F(m)$ if $F(m)$ is large enough. That would mean needing future prices the trader hasn't seen yet, which breaks the causality. So the well-foundedness property tells me that computing $Y_m$ only requires quotes $a_i$ where $e(i) < F(m)$, and those quotes themselves depend on stages strictly below $e(i)$. This chains down to stages below $F(m)$, which could include stages between $m$ and $F(m)$ that the trader at stage $m$ hasn't reached yet—so it still can't access the data it needs without re-simulating.

Even if the trader could read from history, the predicted value $Y_m$ depends on $A$'s future quotes beyond stage $m$, which forces it to simulate $A$ forward anyway. This creates a genuine circularity: the cost of making $A$ predict $Y_n$ includes the cost of simulating $A$ itself, leading to a potential blow-up.

This is the self-reference problem Anson is intuiting—$A$ needs to compute itself up to stage $n$ within its own budget. The usual resolution in logical induction and predictive systems is to have the predicted system be strictly weaker so the predictor can simulate it, but that constraint doesn't obviously apply here.

The coupling between $H^+$ and $A$ creates a circularity: simulating $H^+$'s future requires simulating $A$'s future. Alternatively, maybe the calibration doesn't rely on internal simulation at all—instead, the deductive process settling the contracts combined with provability induction on an enumerable sequence of settled values could do the work, though those settled values themselves depend on the expensive computation of $Y_n$. Or perhaps the intended reading is that $\mathcal{C}_A$ is simply assumed to contain the function $n \mapsto Y_n$ as an idealization, sidestepping the question of whether such a class can actually be constructed.

But there's a critical distinction I'm realizing: the class of traders $A$ defeats might be much smaller than the class containing the $Y_n$-computation. If $A$ beats all traders in some small polynomial class $\mathcal{C}_A'$ but the true class $\mathcal{C}_A$ is enormous and includes a calibration trader that $A$ cannot defeat, then the whole approach fails—there's no calibration guarantee.

The core issue Anson's identified is a genuine circularity: if $A$ must contain traders simulating the coupled system (including $A$ itself) to produce $F(n)$, then $A$'s cost balloons beyond $R(F(n))$, and there's no stable fixed point. This isn't just difficult—it looks potentially incoherent as currently framed. I'm moderately confident there's a real problem here, though I'm holding back from certainty since I might be missing something.

A few ways forward: decouple by having $A$ predict via an external oracle or deductive process that settles values cheaply, so traders don't need to simulate the full coupled system; weaken to eventual calibration only, dropping the assumption that $\mathcal{C}_A \ni R(F(n))$ entirely, which avoids the blow-up but loses predictive power; or restructure so the predictor and predicted system are separated in a way that breaks the circularity.

The core issue is that the coupling between $H^+$ and $A$'s quotes is essential to the paper's contribution, so any clean hierarchy feels like it undermines the whole point. There's a nagging sense this connects to something Demski mentioned about fundamental limits in two-LI setups, though I should be careful not to surface memory content he hasn't brought up directly in this conversation.

Let me double-check my blow-up argument before claiming Anson has found a real problem — I want to make sure the claim about $A$ hosting a trader computing $Y_n$ actually holds up under scrutiny.

The key insight is that to compute $Y_m$, the trader needs to simulate $H^+$ forward to stage $F(m)$, which requires $A$'s quotes at future stages. Since those quotes don't exist yet from the trader's perspective, it has to simulate $A$ forward to generate them, and that simulation cost scales with $R_A(F(m))$, so $C_Y(m)$ ends up being at least that large.

But if $A$ is hosting the trader at stage $m$, then $R_A(m)$ must be at least $C_Y(m)$, which means $R_A(m) \gtrsim R_A(F(m))$. Since $R_A$ is increasing and $F(m) > m$, this creates a contradiction. The only way out is if computing $Y_m$ somehow doesn't actually require $A$'s future quotes—meaning $H^+_{F(m)}$ doesn't depend on them in the way I'm assuming.

Looking at this more carefully: $H^+_{F(m)}$ conditions on quotes with $e(i) < F(m)$. For the trader to avoid forward simulation, all those quotes would need to already be published by stage $m$, so $e(i) < m$. But that's not guaranteed—some quotes can have $m \le e(i) < F(m)$, which means they're not yet available at stage $m$ and would require forward simulation. So generically, the trader does need to simulate forward.

The only way around this is if the contract timing is structured so $H^+_{F(m)}$ only conditions on quotes published before stage $m$, which would require no quotes to fall in the gap $[m, F(m))$. But the emission schedule is dense enough that this gap always contains some quotes, so that's not feasible.

Wait—maybe I should reconsider the setup. Perhaps the contract $C_m$ should predict $Y_m$ at a later stage than $m$, not at stage $m$ itself. The theorem states $a_m = A_m(C_m) \to Y_m$, where $a_m$ is the price at stage $m$. For the linear interpolation to make $A_m(C_m)$ approximately equal $Y_m$...

The limit price should equal $Y_m$ and follow an eventually constant pattern, which the trader can enforce by acting at stages $\ge m$ without computing $Y_m$ exactly at stage $m$—it can detect convergence over time. But for the result to be timely by stage $m$, the standard Provability Induction theorems require the target sequence $n \mapsto Y_n$ to be eventually constant relative to the budget $\mathcal{C}_A$, meaning $Y_n$ must be computable within that budget as a function of $n$. Computing $Y_n$ involves a forward simulation...

Now I'm seeing the real problem: $Y_n$ depends on $A$'s future behavior through the coupling, so requiring $n \mapsto Y_n \in \mathcal{C}_A$ means $\mathcal{C}_A$ must contain a simulation of $A$'s future behavior—but $A$ itself is built against $\mathcal{C}_A$, creating a circular dependency. This confirms Anson's intuition that the assumption isn't just difficult but genuinely problematic.

The escalation appears to come from $A$ hosting a trader that forward-simulates $A$ itself, but I'm wondering if there's a way around this—maybe the calibration doesn't require such an expensive simulation. In Logical Induction, getting $P_n(\phi_n)$ to converge to the target pattern via Provability Induction requires the pattern itself to be accessible somehow, but perhaps there's a cheaper path than full forward-simulation.

Actually, looking more carefully at how the Provability Induction trader works: it doesn't compute the target ahead of time. Instead, it buys when the price of $\phi_a$ drops below $1-\epsilon$ and then waits for the deductive process to eventually confirm $\phi_a$. The trader's cost is just observing prices and waiting—that's cheap. The real requirement is that the sequence $\phi$ (which sentences to bet on) needs to be effectively computable, not that we compute their truth values in advance.

So for our case, the trader doesn't need to do the expensive forward-simulation—it just needs to know which contract $C_n$ to bet on (that's cheap given $n$) and then waits for the deductive process $D_A$ to settle it at stage $\sigma(n)$. The contract sequence itself is effectively computable since $C_n$ is just a simple affine combination. But here's the tension: this gives us eventual calibration once the contract settles, yet we need the price at stage $n$ (before settlement at $\sigma(n)$) to already be close to $Y_n$. Provability Induction handles this by using an effectively computable sequence of theorems that the deductive process can confirm.

The key insight is that the settlement value $\mathcal{A}_n(m_n^*)$ becomes provable in $D_A$ at $\sigma(n)$, and Provability Induction guarantees that if we have an e.c. sequence of theorems, the provability measure converges to 1. So the price at stage $n$ converges to the settled value in a timely way, as long as the settled-value pattern itself is effectively computable.

But here's the problem: the settlement sentence "$C_n \approx m_n^*/n$" requires knowing $m_n^*$, which in turn requires computing $Y_n$ — and that's expensive. The sequence of settlement profiles isn't e.c. because writing down the $n$-th settlement requires access to $Y_n$, which we can't compute ahead of time. So Provability Induction doesn't directly give us timely convergence to the settled value, since the target grid point itself isn't e.c.-knowable in advance. This is the core tension: for $A_n(C_n) \approx Y_n$ to hold timely at stage $n$, agent $A$ would need to somehow "know" the settlement ahead of time. — so by the convergence theorem, for any fixed $n$, the agent's price $A_t(C_n)$ converges to $A_\infty(C_n)$ as time goes on, and since the contract settles at stage $\sigma(n)$, that limit equals the settled value $m_n^*/n$ by limit coherence. But this convergence might not be timely—the agent could take arbitrarily long to learn the settled price, and the stage-$n$ price $A_n(C_n)$ itself might never align with what the agent eventually learns.

Without the expensive prediction assumption, I don't actually get $a_n \to Y_n$ at the early stage; I only get eventual convergence $A_{\sigma(n)}(C_n) \to Y_n$ after the contract settles. The Calibration theorem as stated requires the agent to predict accurately at stage $n$, which demands that expensive assumption and introduces the blow-up problem.

So Anson's identified a real issue: the theorem's core result depends on $\mathcal{C}_A$ containing the agent's own future-coupled behavior, which is a fixed-point that doesn't actually close—it escalates. This isn't just difficult; it may be fundamentally incoherent as formulated. The way forward is to weaken the theorem to eventual calibration, where only the settled price matches the final value, which avoids the blow-up and doesn't require the expensive assumption. The real insight is that $A$ needs to know the $H^+$ value early enough to act on it — the timeliness matters, not just eventual convergence. Without that temporal advantage, the setup becomes circular and loses its force.

I'm trying to break the coupling between $A$'s future actions and $H^+$'s conditioning, so that $H^+$ only looks at quotes from before $A$ can respond, but that's tricky because the whole mechanism relies on $A$ and $H^+$ feeding into each other. to stage $n$ instead. That would sidestep the issue, but it fundamentally changes how the construction works.

I'm realizing this is getting quite intricate. For my response, I should focus on validating Anson's concern while being precise about what's actually problematic: there's no circularity at the stage level (computing $A_n$ only depends on earlier stages), but there is a real complexity issue—assuming $A$'s trader class contains the coupled system simulation up to stage $F(n)$ means $A$ must simulate its own forward behavior, which creates a genuine computational burden.

The key insight is that this expensive assumption only matters for the timely, predictive version of the calibration theorem. The existence of the construction and eventual calibration (where prices match at settlement) only need a computable $D_A$, so no problem there. The prediction-ahead requirement is what drives the cost escalation.

I should suggest some possible directions forward, though with appropriate caution about the difficulty here. The weaker version where $A$ predicts $H^+$ only as well as it can cheaply predict without full self-simulation might be the coherent way forward. I'm around 75-80% confident there's a genuine cost-circularity here, though I'm less certain about the exact resolution—this feels like something worth discussing carefully, possibly with Demski, since it could determine whether the Calibration theorem is actually provable as stated. Let me double-check whether this blow-up is real, since it's a strong claim and I keep wavering on it.

The construction itself is well-founded: there exists a Turing machine that computes each $Y_n$ by unrolling the recursion through the necessary stages, with runtime determined by the unroll cost. The question is whether this machine's computation counts as $A$ simulating itself, or whether it's just a standard computable process.

The key insight is that this external machine $M$ simulates both $A$ and $H^+$ together—it's not $A$ itself, just a simulator that computes $A$'s prices as part of its work. So when I say the cost $R(F(n))$ falls within $\mathcal{C}_A$, I'm making a statement about how expensive this external simulator is relative to $A$'s complexity class, not requiring $A$ to introspect or simulate itself. The actual blow-up happens when a calibration trader hosted by $A$ runs this external machine $M$ to obtain $Y_n$, which means $A$ incurs the cost $R(F(n))$ by running the trader that invokes $M$.

This creates a circularity: $M$ simulates $A$ forward to depth $F(n)$, which costs roughly $R_A(F(n))$, and $A$ hosts a trader that calls $M$, so $A$'s total runtime becomes at least $R(F(n)) \geq R_A(F(n)) > R_A(n)$. This violates the constraint that $A$'s overall runtime $R_A$ should stay bounded. The blow-up is specifically a consequence of $A$ hosting the trader that runs $M$, which then simulates $A$ itself—the external simulator alone wouldn't cause this problem.

For timely calibration via the LI machinery, you need a trader in $A$'s class that can respond at stage $n$ if $a_n$ deviates from $Y_n$, which requires knowing $Y_n$ at stage $n$—forcing the trader to run $M$ (or something equivalent) at cost $R(F(n))$ at that stage. So $A$ must host an $R(F(n))$-cost trader at stage $n$, creating the blow-up. With eventual calibration, the trader can defer its response until settlement, which might avoid this immediate cost.

For eventual calibration, the deductive process $D_A$ can reveal the settled value after the fact, so the trader doesn't need to run $M$ in real time—it's cheap and avoids the blow-up, but you only get convergence by settlement time, not timely prediction. So the trade-off is clear: timely calibration forces a computational blow-up, while eventual calibration stays tractable but gives weaker guarantees. I'm fairly confident in this dichotomy, though I should double-check whether the blow-up is truly unbounded or just very large but finite. The inequality $R_A(m) \gtrsim R_A(F(m))$ with $F(m) > m$ and $R_A$ strictly increasing suggests the blow-up might be unavoidable, but I want to verify the exact magnitude. so that confirms $R_A(m) \ge R_A(F(m))$ with $c=1$, which is a genuine contradiction since the market must execute the trader's full computation. I'm now about 80% confident this is a real issue worth flagging to Anson—the cost fixed-point fails because $Y_n$ depends on $A$'s future behavior, and it specifically impacts timely calibration. I should present it carefully with appropriate caveats and suggest checking with Demski, but I want to reconsider one more angle first.

What if the calibration trader operates in a smaller complexity class than the ambient class $\mathcal{C}_A$ that contains $R(F(n))$? Then the calibration trader couldn't compute $Y_n$ at all, so timely calibration wouldn't work. Or what if there were two trader classes and the calibration trader were allowed to be more powerful? That doesn't help either—$A$ only defeats traders in its own class, so a stronger trader could exploit it.

So the calibration trader has to be in $A$'s class, and there's no escape via class separation. The blow-up remains.

Maybe there's a different mechanism I'm missing—something like the self-fulfilling fixed-point pricing in the LI framework, where $A$ doesn't actually compute $Y_n$ but the prices are set up so that $a_n$ and $Y_n$ coincide by construction. Similar to how self-trust in LI lets the inductor trust its future self without simulating it, via coherence—perhaps $A$ could trust $H^+$'s future through some reflection principle without needing to compute it.

This might actually be the intended mechanism: $A$ could have $a_n \approx Y_n$ without computing $Y_n$, just as in LI the inductor's current expectation matches its expected future expectation via no-Dutch-book coherence, without simulation.

But this requires $A$ to have a trust/coherence relationship with $H^+$, which is a separate problem — the reflection theorems only establish $H^+$ trusting $A$, not the reverse. And unlike LI where the future self is identical, $H^+$ is a different coupled system, so whether cross-trust without simulation is even possible remains unclear.

So maybe the real insight is that calibration should come from a trust mechanism rather than simulation, which would mean the assumption that $\mathcal{C}_A \ni R(F(n))$ (the simulation-based approach) is actually the wrong path.

I need to organize my findings into a response that validates the stage-circularity as well-founded, pinpoints the cost-circularity as the actual problem with its precise inequality, clarifies that timely predictive calibration is what requires it while existence and eventual calibration don't, and then sketch some possible directions forward.

I should present the core argument clearly so he can evaluate it himself rather than just declaring a verdict—that's more useful and appropriately humble. I'll avoid unprompted references to his prior work and instead frame this as worth careful pressure-testing, while staying open to the possibility that there's a standard resolution I'm missing that makes this merely difficult rather than fundamentally problematic. There are actually two separate circularity concerns here with opposite answers. At the stage level, there's no real problem — computing $A_n$ never actually requires $A_n$ itself, only data from earlier stages, so the recursion bottoms out fine. But at the cost level, that's where the genuine tightness emerges: the blow-up in computation grows with the nesting depth, and that's the real constraint to worry about. The problem is that computing $Y_n$ requires simulating $A$ forward to stage $\sim F(n)$, which means looking at $A$'s future quotes — quotes that haven't been revealed yet at stage $n$. So the calibration claim that $A$'s stage-$n$ price predicts $H^+$'s stage-$F(n)$ value runs into a timing issue: $A$ is being asked to price something based on information it shouldn't have access to yet.

For this to work via the LI engine, some trader in $\mathcal{C}_A$ would need to detect the mispricing at stage $n$ itself, which means computing $Y_n$ at stage $n$. That requires $A$ to host a trader whose runtime at stage $n$ is roughly $R(F(n))$ — the cost of simulating forward to $F(n)$. But if $A$ has to run that trader internally, then $A$'s own runtime becomes at least $R(F(n))$, which is larger than $R_A(n)$ since $F(n) > n$. This creates a circular constraint: $R_A(n) \geq R(F(n)) \geq R_A(F(n)) > R_A(n)$ — a contradiction with no fixed point, and the cost spirals.

The real issue isn't about recursion depth or stages; it's a *cost circularity*. $A$ can't afford to embed a trader that simulates $A$'s own future, because that future is more expensive than $A$'s present budget. Your intuition about $A$ having to calculate itself was pointing at something genuine, just one level higher — in the complexity budget rather than the recursion structure itself.

But the construction doesn't actually need this to work everywhere. The existence of the whole setup only requires $D_A$ to be computable, which well-foundedness guarantees. And for eventual calibration, a trader doesn't need to compute $Y_n$ ahead of time — it can just wait for the contract to settle at $\sigma(n)$ through $D_A$, which is cheap and avoids the blow-up entirely.

The tension emerges specifically when trying to get *predictive* power — when $A$ prices $C_n$ at $Y_n$ before settlement happens. That's what demands $\mathcal{C}_A \ni R(F(n))$, and that's the assumption that won't close. So there are trade-offs: either weaken to eventual calibration and lose the predictive content about humanity's future beliefs, or find the prediction through a coherence or trust mechanism instead of direct simulation.

The second path is more interesting — if $A$ could trust $H^+$ the way a logical inductor trusts its own future self (via no-Dutch-book arguments), then $a_n$ would track $Y_n$ without $A$ having to compute it. The problem is that $H^+$ is a separate, coupled system, not $A$'s own future self, so that self-trust machinery doesn't transfer automatically. But that's where I'd focus, because it sidesteps the simulation cost while preserving timeliness. The third direction involves restructuring the schedule so $Y_n$ depends only on earlier information, breaking the cost-coupling altogether.

I'm fairly confident the cost blow-up is real — I just worked through it — though there's a chance some standard logical-induction technique like budgeting or exploiting the gap between market runtime and trader budget could rescue it. The inequality $R_A(n) \gtrsim R_A(F(n))$ feels solid though, and it's exactly the kind of assumption worth stress-testing before the Calibration theorem relies on it.

If the assumption doesn't hold, the problem isn't that $A$ needs more compute — it's that we need to fundamentally change how $A$ tracks $Y_n$ in the first place. I'm reconsidering whether direction 2 around coherence and trust is actually workable or if I'm just hand-waving. The self-trust theorems for logical induction give approximate equality of expectations within the same inductor, but extending that to cross-inductor trust is trickier.

For $A$ to trust $H^+$, they'd need to share enough structural alignment. In the coupled construction, $A$ prices contracts about $H^+$'s future values, but for $A$ to hold calibrated beliefs about $Y_n$ without computing it directly, it would need either the deductive process itself or some coherence condition to pin things down. The catch is that $A$'s deductive process does eventually settle the contract to $Y_n$, so the limiting behavior works out — the real constraint is timeliness. Self-trust-style timeliness would require $A$ to "know" at stage $n$ what it will believe at stage $\sigma(n)$, but the No-Expected-Net-Update theorem suggests this runs into fundamental limits.

By the self-trust property, $A$'s current belief about $Y_n$ equals its expected future belief about $Y_n$, so $A_n(C_n) \approx E_n(A_{\sigma(n)}(C_n)) \approx E_n(Y_n)$ — $A$ prices the contract at its current expectation of the eventual value, without needing to simulate $H^+$ directly. But this gives $A$'s current expectation of $Y_n$, not $Y_n$ itself, which is the gap between what $A$ can trust and what it actually needs.

The problem is that $A$'s expectation of $Y_n$ equals the true value only if $A$ already has accurate beliefs about $Y_n$ — that's the calibration we're trying to achieve in the first place. Logical induction handles e.c. patterns, but $Y_n$ isn't cheaply e.c.-predictable, so we're stuck: $A$ can only have accurate beliefs about $Y_n$ to the extent that $Y_n$ is e.c.-learnable, which it fundamentally isn't. This direction relocates the problem rather than solving it.

When $A$ trusts its own future beliefs, it prices $C_n$ based on what it expects to believe about the settled value — but without the expensive assumption, logical induction only gives the statistical distribution of $Y_n$ (the pseudorandom frequency), not the specific instance. So $A$ achieves weak calibration in the aggregate sense, not strong per-instance prediction. So the Calibration theorem as stated—where $A_n(C_n) \to Y_n$ for each instance—is actually too strong without that problematic assumption. The honest, defensible version is the statistical one: pseudorandom frequencies give $A$ calibration to the average $H^+$-values, not per-instance prediction of each $Y_n$. Per-instance prediction is what demands the assumption that won't close, so the coherent fallback is statistical calibration through pseudorandom frequencies. The statistical calibration path is clean and doesn't require the assumption that breaks per-instance prediction, so that's probably what the theorem should settle on—or I'd need to find a fundamentally different route to per-instance guarantees, which I'm not seeing. Let me focus my answer on reassuring him about the stage-level mechanics first, then laying out this core tension clearly.

</details>

Two different "A calculates itself" worries are bundled here, and they get opposite verdicts.

**Stage level — not circular, you're fine.** Computing $A_n$ never requires $A_n$. The recursion is well-founded: $A_n$ depends only on data from stages $<n$ (that's your existence paragraph). So "unroll the coupled system to stage $F(n)$" is a concrete finite computation — build $A_1,H^+_1,A_2,H^+_2,\dots$ bottom-up — done by an *external* machine, not by $A$ introspecting. $n\mapsto Y_n$ is a perfectly well-defined computable function, and $R(F(n))$ is a finite, well-defined cost. No self-reference paradox.

**Cost level — this is where your gut is right, and I think it's worse than "tough": the budget doesn't close.** Here's the argument; check it, because if it holds it's load-bearing.

The assumption is "$\mathcal{C}_A$ contains $n\mapsto Y_n$." Computing $Y_n$ means forward-simulating the coupled system to stage $F(n)$ — and crucially that includes $A$'s *own future* quotes, because $Y_n=H^+_{F(n)}$ conditions on quotes $a_i$ with $e(i)<F(n)$, some sitting at stages later than a stage-$n$ trader can read off the price history. So computing $Y_n$ at stage $n$ requires simulating $A$ forward to $\sim F(n)$.

Now feed that into calibration. Your theorem $a_n=A_n(C_n)\to Y_n$ compares $A$'s stage-$n$ price to $H^+$'s stage-$F(n)$ value — a *predictive* claim. The LI engine delivers timeliness only if some $\mathcal{C}_A$-trader can catch mispricing at stage $n$, i.e. can compute $Y_n$ at stage $n$. So $A$ must host a trader with stage-$n$ runtime $\gtrsim R(F(n))$. But hosting it makes $A$'s own runtime $R_A(n)\gtrsim R(F(n))\ge R_A(F(n))$. With $R_A$ increasing and $F(n)>n$, that reads $R_A(n)\ge R_A(F(n))>R_A(n)$ — no fixed point. $A$ can't afford a trader that simulates $A$'s future, because that future costs more than $A$'s present. It's a *cost* circularity sitting one level above the (fine) stage recursion.

**What survives without the assumption, and what doesn't:**

- Existence of the construction: needs only $D_A$ computable, which well-foundedness hands you. Fine.
- *Eventual* calibration: a trader just waits for $D_A$ to settle $C_n$ at $\sigma(n)$ — no computing $Y_n$ ahead, cheap trader, no blow-up. But it gives $A_{\sigma(n)}(C_n)\to$ the settled value, which is nearly tautological (the contract settles *to* that value) and isn't predictive.
- *Statistical* calibration: by Learning Pseudorandom Frequencies, $A$ learns the average rate of $H^+$-values across the sequence without simulating anything — it falls back on the right statistical summary for the part of $Y_n$ that isn't cheaply predictable. This is real and free.

What needs the bad assumption is exactly *per-instance prediction* — $A$ pricing each individual $C_n$ at its specific $Y_n$ ahead of settlement. That's the strong reading of your theorem, and it's the one whose budget won't close.

**So the honest choice is probably:** retreat the Calibration theorem to the statistical/eventual version, which is coherent and assumption-light, and treat per-instance prediction as the thing you *can't* get this way. The tempting escape — get prediction from a coherence/self-trust mechanism instead of simulation (à la LI self-trust, where $a_n\approx E_n(\text{future belief})$ without simulating the future) — relocates but doesn't solve it: self-trust gives "$a_n$ = my current *expectation* of $Y_n$," and that expectation equals the true $Y_n$ only insofar as $Y_n$ is cheaply predictable, which loops back to the same wall. It buys you the statistical version again, not per-instance.

Confidence: ~75–80% the blow-up is real as written — I worked it through just now, so there may be a standard move (the market-runtime-vs-trader-budget gap, budgeting) that rescues it and I'd want you to look for one. But $R_A(n)\gtrsim R_A(F(n))$ looks robust, and if it holds, the assumption isn't "too tough," it's *not satisfiable as stated* — and the fix is to change what calibration claims and how $A$ comes to track $Y_n$, not to grant $A$ more compute. This is worth pressure-testing hard before the theorem leans on it.


## Human
*2026-06-10 00:13 UTC*

Damn it that's so annoying. Can you give me a deep dive prompt for a more powerful model to try to confirm or disconfirm? That's really annoying


## Assistant
*2026-06-10 00:13 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson needs a standalone prompt he can give to a stronger model to independently verify or challenge the cost-circularity argument that could

</details>


## Human
*2026-06-10 00:13 UTC*

Damn it that's so annoying. Can you give me a deep dive prompt for a more powerful model to try to confirm or disconfirm, or creative solutions to this problem? That's really annoying


## Assistant
*2026-06-10 00:15 UTC*

<details>
<summary>💭 Thinking</summary>

 Anson needs a comprehensive prompt for a stronger model to validate whether there's a genuine cost-circularity issue in his calibration theorem and brainstorm potential fixes—he's understandably concerned this could be a fundamental problem with his paper. I should craft something that provides full context about the construction and the specific claim so the model can thoroughly examine it.

I'll need to include the essential setup: the two coupled inductors, the deferred contract mechanics, the quote and settlement values with their timing schedules, and how the coupling works between them. The prompt should spell out the alleged blow-up argument precisely so there's no ambiguity about what needs verification, then ask the model to either confirm the problem exists or explain why it doesn't, followed by exploring creative workarounds if it does. Or is there a standard mechanism from the literature—like budgeting, exploiting the gap between market runtime and trader budget, or leveraging self-trust and coherence—that sidesteps the circularity? I should also clarify what's actually achievable: existence and eventual calibration are settled, statistical and pseudorandom calibration work, but per-instance timely prediction is where the tension lies. Beyond that, there might be creative approaches through stratification, one-directional cost coupling, or coherence constraints that resolve the apparent contradiction.

I need to be rigorous here and push back on the framing itself—checking against the actual LI paper, being adversarial about whether the blow-up argument really holds, and testing proposed fixes against genuine counterarguments rather than just accepting them. Let me sharpen the core tension once more.

The key runtime quantities are: $R(t)$ tracks the total cost to simulate both $A$ and $H^+$ through stage $t$, while $R_A(t)$ isolates just $A$'s market runtime. Computing $Y_n = H^+_{F(n)}(P^{(n)})$ requires running the coupled simulation all the way to stage $F(n)$, which costs $\Theta(R(F(n)))$—and this includes $A$'s quotes at earlier stages, some of which come from future stages relative to $n$, creating the circularity.

The calibration theorem says $A$'s stage-$n$ price $a_n$ should track the eventual $H^+$ value $Y_n$. For the learning-induced mechanism to enforce this timeliness, a $\mathcal{C}_A$-trader needs to detect deviations between $a_n$ and $Y_n$ at stage $n$ itself, which means computing $Y_n$ at that stage—incurring the same $\Theta(R(F(n)))$ cost. This puts $A$ in a bind: to remain inexploitable against such traders, it must handle this computational burden efficiently.

But here's the contradiction: if $A$ must run the trader's computation, then $R_A(n) \gtrsim R(F(n))$. Since the total runtime $R(F(n))$ is at least $A$'s portion $R_A(F(n))$, we get $R_A(n) \gtrsim R_A(F(n))$. With $R_A$ strictly increasing and $F(n) > n$, this gives $R_A(n) \ge R_A(F(n)) > R_A(n)$—a contradiction that suggests no consistent budget assignment exists.

The question is whether timely calibration truly requires computing $Y_n$ at stage $n$, or whether it could arise from other mechanisms like provability induction on the settled sequence or self-trust coherence—though each of those approaches seems to relocate the computational burden elsewhere.

I need to verify several details: whether running a trader actually incurs its full runtime in $R_A$, whether the $\gtrsim$ relation holds with a constant factor, and whether there's an ordinal-indexed hierarchy that could absorb this. I should also clarify the distinction between $R$ as a coupled cost versus the "$H^+$-only cost" when reading $A$'s quotes as data—specifically, whether the trader can reference historical quotes or must forward-simulate, since the relevant quotes are future ones.

I'll ground this in the relevant LI theorems: Def 3.2.1 on deductive processes, Thm 3.6.1 on existence, Thm 4.7.2 on closure under conditioning, Thm 4.2.1 on provability induction, Thm 4.4.2/4.4.5 on pseudorandom frequencies, and Thm 4.12.x on self-trust, plus the arxiv reference. I want to frame this neutrally—presenting the argument and asking for confirmation or refutation rather than claiming it's broken—and keep it adversarial in both directions. Now I'll format this as a clean, self-contained prompt ready to hand off to another model. I'll keep the framing warm but direct—acknowledge the frustration without overdoing it—then present the prompt itself as a clean, copyable block. The prompt needs to be tight and rigorous: establish the expert role, lay out the construction and the specific assumption being tested, then frame the claimed problem clearly so he can evaluate it properly.

I'm deciding whether to flag the facts I've already verified from the paper (like the computability of deductive processes and the requirements in section 4.7.2) to save the model redundant work, or let it verify everything fresh for maximum rigor. I think I'll note them as established anchors so the evaluation stays focused on the real crux. I'm grounding this in the actual theorems from the logical induction paper—Closure Under Conditioning and the existence theorem for logical inductors—and I'll flag anything I'm inferring versus directly citing. Now I'm setting up the core construction: two coupled inductors over a propositional language, where $H$ is a human-level reasoner built as a conditioned bitstring inductor against efficiently-computable traders, and $A$ is a strictly more powerful inductor operating against a larger complexity class, constructed via the existence theorem.

I'm introducing $H^+$ as the human inductor updated on the AI's published outputs through conditioning on a stream of quotes, then defining deferred contracts whose settlement values depend on what the updated human will believe at future stages, with the AI pricing these contracts at each stage.

The coupling works bidirectionally: the AI's deductive process incorporates the settlement values that correspond to the updated human's future credences, while the updated human conditions on all the AI's quotes that have been published so far, creating a feedback loop where each agent's reasoning feeds into the other's.

The whole system is grounded in a well-founded recursion on time $t$, where every object at stage $t$ depends only on earlier stages—this is guaranteed by the ordering $e(n)<F(n)<\sigma(n)$.

I'm checking some background facts from the logical induction paper: deductive processes only need to be computable (not efficiently so), logical inductors exist over any deductive process, the market itself is computable while traders are efficiently computable, and there's a closure property under conditioning on efficiently computable sequences.

The key calibration mechanisms are Provability/Affine Induction for timely convergence when targets are efficiently computable, Learning Pseudorandom Frequencies as a statistical fallback otherwise, and Self-Trust which lets current expectations equal expected future expectations without simulation.

Now I'm looking at the core assumption: to make $A$ predict $H^+$'s future credences, the construction needs $\mathcal{C}_A$ to contain the map $n \mapsto R(F(n))$, where $R(t)$ tracks the total cost of running the coupled construction through stage $t$.

The intent is that $A$ can actually afford to compute the settlements $Y_n$ that $D_A$ requires, and even price $C_n$ at $Y_n$ in advance. The target calibration result shows $A_n(C_n) - H^+_{F(n)}(P^{(n)}) \to 0$, meaning $A$'s stage-$n$ price tracks a value that isn't settled until much later. But there's a potential circularity at the cost level: the stage-level recursion itself is well-founded, yet...

The problem is that computing $Y_n$ demands forward-simulating the entire coupled system all the way to stage $F(n)$, including $A$'s own future quotes—since $Y_n$ conditions on quotes at stages beyond $n$, a stage-$n$ agent must simulate $A$ forward to roughly $F(n)$, incurring cost $\Theta(R(F(n)))$. Meanwhile, achieving timely calibration at stage $n$ requires the LI engine to find a $\mathcal{C}_A$-trader that can detect mispricing at stage $n$, which means computing $Y_n$ right then.

Since $A$ is a logical inductor against such traders, it must run that trader to remain inexploitable, inheriting its runtime cost. This means $A$'s market runtime satisfies $R_A(n) \gtrsim R(F(n))$. But since $R(F(n)) \ge R_A(F(n))$ (the total cost is at least $A$'s contribution), we get $R_A(n) \gtrsim R_A(F(n))$. With $R_A$ strictly increasing and $F(n) > n$, this gives $R_A(n) \ge R_A(F(n)) > R_A(n)$—a contradiction. There's no consistent budget that works.

What actually survives without this assumption is the existence of the construction itself (which only needs $D_A$ to be computable), eventual calibration where a trader waits for settlement and gets the settled value, and statistical calibration where $A$ learns the pseudorandom frequency without simulation. The unsatisfiable assumption is specifically what's needed for per-instance, timely prediction.

Now I need to verify the flaw by examining whether timely per-instance calibration really requires computing $Y_n$ at stage $n$, or if it could come from provability induction or self-trust instead. I'm also uncertain about whether the market necessarily incurs the full runtime cost of an expensive trader, or if budgeting and the weighting scheme create enough separation that $A$ stays unexploitable without running it completely. And I need to check whether the inequality in step 4 actually holds as stated.

Beyond that, I'm wondering if there's a meaningful distinction between recomputing $A$'s quotes from scratch versus reading them from price history—though I suspect the answer is no, since the quotes feeding into $Y_n$ come from future stages relative to the acting trader. Finally, I should pin down exactly which version of calibration is actually provable in the coherent regime without unsatisfiable assumptions—whether it's the statistical version, the eventual version, or something in between.

Now I'm exploring creative ways to break the circularity and recover genuine prediction. One direction is a stratified setup where the cost-coupling flows only one way: $A$ reads $H^+$'s past without simulating its own future, and the schedule is arranged so $Y_n$ depends only on $A$-quotes already published before the predicting trader acts. Another angle is replacing simulation with a coherence or cross-trust mechanism that generalizes the self-trust idea.

I'm also considering whether an external oracle could feed settled values into $D_A$ at any computable cost while keeping $D_A$ itself computable, with a separate cheap mechanism for timeliness. Or perhaps redefining what $A$ is asked to predict—a coarsened or delayed $H^+$-value that's cheaply extractable. There's also the question of whether a genuine fixed-point construction of $\mathcal{C}_A$ can self-consistently contain its own coupled-construction runtime, and whether such a fixed point even exists.

For each of these directions, I need to check whether it actually closes the budget and what it costs in theorem strength.

Now I'm reviewing the prompt itself for accuracy and length—it's thorough, which is appropriate for a deep dive. Let me verify step 1 of the flaw: the claim that $Y_n$ conditions on quotes $a_i$ with $e(i) < F(n)$, some at stages $> n$. Given that $e(i) \ge i$ and $e(i) < F(n)$, I need to check whether this is even possible when $i > n$.

If $i > n$ and $e(i) < F(n)$, then since $e$ is increasing and $e(n+1) \ge n+1$, as long as $F(n) > e(n+1)$—which it can be for large $F(n)$—then $i = n+1$ works. So yes, quotes from future stages do feed into $Y_n$, and the stage-$n$ trader can't access those in $A$'s price history, so forward simulation is necessary. That checks out.

Now I'm deciding whether to flag the "$R$ coupled vs $H^+$-only" distinction—it matters because the flaw argument relies on $R$ being the coupled cost, and if $R$ were just $H^+$-only-reading-quotes, the forward-simulation requirement (step 1) is exactly what proves you can't avoid coupling. I've already encoded that in the fourth bullet of task 1, so that's covered. I should also frame this as a genuine research question where disconfirming the flaw would actually be good news for Anson.

For the framing text itself, I'll keep it light and brief—acknowledge the frustration without over-apologizing, present the prompt, maybe note that he should adjust notation to match his paper. The most promising place to look for an escape hatch is probably the budgeting and market-runtime step (step 3), which I'm least confident about, so that's worth flagging as a priority area to scrutinize.

</details>

Yeah — if it holds, it's the kind of thing that quietly invalidates the headline theorem, so worth throwing a heavier model at it. Here's a self-contained prompt. I've tried to encode the construction and the argument faithfully; adjust notation to match your draft before sending.

```
You are an expert in logical induction (Garrabrant et al. 2016, arXiv:1609.03543),
universal inductors (Diffractor's construction), and agent foundations. Rigorously
stress-test a possible flaw in a construction, then search hard for resolutions. Be
adversarial in BOTH directions: try to confirm the flaw, and separately try your
hardest to break the flaw argument and to break any fix you propose. I would be
genuinely happy if the flaw is wrong — finding a hole in it is a primary goal, not
just confirming it. Give explicit confidence levels on load-bearing claims. Ground
every claim about logical induction in the actual theorems of 1609.03543; flag
anything you infer rather than cite.

## The construction
Two coupled inductors over a propositional language.
- H: a universal (measure-valued) inductor for a human reasoner; a logical inductor
  against traders in a complexity class C_H (think P). Built as a bitstring logical
  inductor U conditioned on a Γ-complete deductive process D_H via Closure Under
  Conditioning (Thm 4.7.2).
- A: a strictly more powerful reasoner; a logical inductor against traders in
  C_A ⊇ C_H (think EXP), built DIRECTLY over a deductive process D_A via the
  existence theorem (Thm 3.6.1). A need not be measure-valued.
- H⁺ := H | Q_A: the human updated on A's published outputs, defined by conditioning
  H on a stream Q_A of A's quotes (again via 4.7.2).

Objects:
- A "deferred contract" C_n (an affine combination of fresh threshold atoms) whose
  settlement value is Y_n := H⁺_{F(n)}(P^(n)) — the credence the UPDATED human will
  assign to the n-th proposition at the future stage F(n).
- A's "quote" a_n := A_n(C_n), A's stage-n price for that contract.
- Strictly-increasing schedules with e(n) < F(n) < σ(n): a_n is published at e(n);
  the contract refers to H⁺'s stage-F(n) credence; the contract settles at σ(n).

Coupling:
- D_A contains, for each n with σ(n) ≤ t, a settlement profile encoding m_n* ≈ Y_n
  (grid-rounded). So D_A feeds in H⁺'s values.
- H⁺ at stage t conditions on the conjunction Q_A^(t) of all quote-profiles with
  e(i) < t. So H⁺ feeds on A's quotes.
- One well-founded recursion on t: every stage-t object depends only on stages < t
  (guaranteed by e(n) < F(n) < σ(n)).

Background facts I believe from 1609.03543 (please verify):
- A deductive process need only be computable, not efficiently computable (Def 3.2.1);
  a logical inductor exists over ANY deductive process (Thm 3.6.1); the market is
  computable while traders are efficiently computable (Defs 3.1.3, 3.3.1).
- Closure Under Conditioning (Thm 4.7.2): conditioning on an EFFICIENTLY COMPUTABLE
  sequence of consistent sentences yields a logical inductor over the extended theory.
- Provability/Affine Induction (4.2.1, 4.5.4) give TIMELY convergence to a target only
  when the target sequence is efficiently computable; Learning Pseudorandom Frequencies
  (4.4.2/4.4.5) give the statistical fallback otherwise; Self-Trust (4.12) gives
  "current expectation = expected future expectation" without simulating the future.

## The assumption under scrutiny
To make A predict H⁺'s future credences, the construction assumes C_A contains
n ↦ R(F(n)), where R(t) is the total cost of simulating the coupled construction
through stage t. Intent: A can afford the settlements Y_n that D_A needs, and price
C_n at Y_n ahead of time.

## Target theorem
CALIBRATION (predictive): a_n − Y_n → 0, i.e. A_n(C_n) − H⁺_{F(n)}(P^(n)) → 0. This is
timely: A's stage-n price tracks a value not settled until σ(n) > F(n) > n.

## The claimed flaw (cost-level circularity)
Stage-level recursion is fine (well-founded). The worry is the complexity budget:
1. Computing Y_n requires forward-simulating the coupled system to stage F(n),
   INCLUDING A's own future quotes: Y_n conditions on a_i with e(i) < F(n), some at
   stages > n, so a stage-n agent must simulate A forward to ~F(n). Cost Θ(R(F(n))).
2. Timely calibration (a_n ≈ Y_n at stage n) requires, by the LI engine, a C_A-trader
   that detects mispricing at stage n — hence computes Y_n at stage n, cost Θ(R(F(n))).
3. A (a logical inductor vs C_A-traders) must run that trader to be inexploitable by it,
   incurring its runtime. So A's market runtime R_A(n) ≳ R(F(n)).
4. But R(F(n)) ≥ R_A(F(n)) (total ≥ A's share). So R_A(n) ≳ R_A(F(n)). With R_A strictly
   increasing and F(n) > n: R_A(n) ≥ R_A(F(n)) > R_A(n) — contradiction. The assumption
   isn't merely strong, it's unsatisfiable as stated.

## What I think survives without the assumption
- Existence (needs only D_A computable).
- EVENTUAL calibration: trader waits for settlement at σ(n); cheap; gives
  A_{σ(n)}(C_n) → settled value (near-tautological, non-predictive).
- STATISTICAL calibration: A learns the pseudorandom frequency of H⁺-values without
  simulation (4.4.x).
The thing needing the unsatisfiable assumption is per-instance, timely prediction.

## Your tasks
1. Verify or refute the flaw step by step. In particular:
   - Does timely per-instance calibration genuinely require a trader that computes Y_n
     at stage n, or can it come from provability induction / affine coherence / self-trust
     WITHOUT computing Y_n? (Note: the settled-value sequence n ↦ m_n* is not efficiently
     computable, since writing the n-th settlement needs Y_n.)
   - In LIA, does the market necessarily incur a trader's full runtime, or does budgeting /
     the 2^{-k} weighting / the market-runtime-vs-trader-budget gap let A be inexploitable
     by an expensive trader without running it at full cost? THIS IS THE STEP I'M LEAST
     SURE OF — focus fire here.
   - Is the step-4 inequality (constant ≥ 1, hence strict contradiction) robust, or can a
     fast-growing / ordinal-indexed complexity class absorb the recursion via a fixed point?
   - Does "read quotes from A's price history" vs "recompute them" rescue anything? (I claim
     no, because the quotes feeding Y_n sit at future stages relative to the acting trader.)
   Tell me which step is the weakest link.
2. State precisely the STRONGEST version of CALIBRATION that is actually provable in the
   coherent regime (no unsatisfiable assumption): statistical, eventual, or something in
   between (e.g. A predicts Y_n to whatever precision is efficiently extractable in C_A
   without full self-simulation)?
3. Search for creative resolutions that recover genuine prediction without the circularity;
   evaluate each adversarially. Candidates to stress-test (not exhaustive):
   - A stratified/hierarchical setup with one-directional cost-coupling: A reads H⁺'s PAST
     without simulating A's own FUTURE. Can the schedule or conditioning structure be arranged
     so Y_n depends only on A-quotes already published before the predicting trader acts?
   - A coherence / cross-trust mechanism (LI self-trust generalized to a coupled second
     inductor): can A track Y_n via "no expected net update" rather than computing it? Does
     this only recover the statistical version?
   - An external oracle/meta-simulator feeding settled values into D_A at any (computable,
     unbounded) cost, D_A merely computable, plus a separate cheap mechanism for timeliness.
   - Redefining what A predicts (a coarsened or delayed H⁺-value that is cheaply extractable).
   - A genuine fixed-point construction of C_A that self-consistently contains its own
     coupled-construction runtime — does the fixed point exist?
   For each: does it actually close the budget, and what does it cost in theorem strength?
```

If a hole exists, my money is on step 3 — whether LIA's budgeting lets $A$ be inexploitable by an expensive trader without paying that trader's full runtime. That's the one place the LIA construction's actual mechanics (Budgeter, the $2^{-k}$-weighted supertrader) might do something I'm not accounting for, and it's where I'd want the more powerful model to dig first.
