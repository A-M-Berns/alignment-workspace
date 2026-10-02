# Adversarial audit of fable-slop-notes.md against decision-problems-v2.md

Auditor conventions: every numbered verdict carries my own confidence mark — [checked] = explicit calculation performed here; [derived] = full argument given here; [reconstructed] = leans on an external formalism, source named; [guess] = conjecture. Verdicts: CONFIRMED / REFUTED / GAP. All Definition/Proposition/Theorem numbers refer to decision-problems-v2.md ("v2"). "Notes" = fable-slop-notes.md.
## Shared apparatus recomputed from v2 (used repeatedly)

**AMD miniature (v2 Proposition 5(c)).** One point $d$, two nested nodes. Node 1: $a \to$ leaf payoff 0, $b \to$ node 2. Node 2: $a \to$ payoff 4, $b \to$ payoff 1. Let $q := C(d)(a)$.

$$V(q) = q\cdot 0 + (1-q)\,[\,4q + 1\cdot(1-q)\,] = (1-q)(3q+1).$$

$V(0)=1$, $V(1)=0$, $V'(q) = 2-6q$, zero at $q=1/3$, $V(1/3) = (2/3)(2) = 4/3$. Matches v2's proof line "$\max_x(1-x)(3x+1) = 4/3$" and the stated optimum $C(d)(a)=\tfrac13$. [checked]

**Counterfactual Mugging $B_1$ (v2 Proposition 6).** Coordinates coin $\in\{H,T\}$, choice $\in \{\mathrm{pay},\mathrm{refuse},\bot\}$, transfer $\in\{0,1\}$; $r = -x\mathbf{1}[\mathrm{pay}] + y\mathbf{1}[\mathrm{transfer}]$, $0<x<y$. Fair coin; $T$: query $d$, pay $\to (T,\mathrm{pay},0)$, refuse $\to (T,\mathrm{refuse},0)$; $H$: query $d$ (hypothetically), pay $\to (H,\bot,1)$, refuse $\to (H,\bot,0)$. State at $d$: $P_s(T)=1$, $P_s(\mathrm{transfer}{=}0)=1$, $P_s(\mathrm{pay})=q_0$. With $q := C(d)(\mathrm{pay})$:

$$V_{B_1}(C) = \tfrac12(-xq) + \tfrac12(yq) = \tfrac12 q(y-x). \quad\text{[checked, matches v2]}$$

## A. §0 of the notes: the crux framing and the Prop-6/SSC contrast

### A1. "Prop 6 makes the no-doubt mugging masked-calibrated for every procedure" — CONFIRMED [checked], with an elided interior-$q_0$ caveat

Independent verification of Prop 6's masked claim (Def 9): choose self-model $m(\mathrm{pay}) = q_0$, full support iff $q_0\in(0,1)$. $C' = C[d\mapsto m]$. Conditioning $\nu_{B_1,C'}$ on $O_T = \{\text{coin}=T\}$: worlds $(T,\mathrm{pay},0)$ w.p. $q_0$, $(T,\mathrm{refuse},0)$ w.p. $1-q_0$. So $\nu_{C'}(T\mid O_T)=1 = P_s(T)$; $\nu_{C'}(\mathrm{transfer}{=}0\mid O_T)=1$; $\nu_{C'}(\mathrm{pay}\mid O_T)=q_0 = P_s(\mathrm{pay})$; $\nu_{C'}(\bot\mid O_T) = 0 = P_s(\bot)$. V-clause: $\mathbb{E}[r \mid \mathrm{pay}\wedge O_T] = -x = V_s(\mathrm{pay})$ (transfer $=0$ on $T$), $\mathbb{E}[r\mid \mathrm{refuse}\wedge O_T] = 0$. All match; the self-model $m$ is independent of $C$, so this works for EVERY $C$ — as Prop 6 says, "interior $q_0$; Appendix B for the boundary". The notes' §0 drops the interior caveat: harmless but should be carried.

### A2. Per-run and per-occurrence SSC both fail there — CONFIRMED [checked]

Both branches query $d$, so $\mathrm{occ}(d) = \mathrm{Leaves}$, $\mu(\mathrm{occ}(d)) = 1$, and $\#_d \equiv 1$. Per-run SSC (Def 13) demands $P_{s_d}(T) = \mu(\lambda \models T \mid \mathrm{occ}(d)) = \nu(T) = \tfrac12 \neq 1$. Per-occurrence: $\mathbb{E}[\#_d\mathbf{1}_T]/\mathbb{E}[\#_d] = \tfrac12 \neq 1$. Both senses fail for every $C$. So the notes' contrast (masked-OC for every procedure; SSC for none) is exactly right, and it is the formal skeleton of the "no-doubt mugging" dispute.

### A3. The crux framing — CONFIRMED as interpretation, with ONE ATTRIBUTION SLIP

- [scrubbed]
- [scrubbed]
- [scrubbed]
- [scrubbed]

## B. §1: strong vs weak SSC

### B1. Claim 1.1 (strong fairness closes the anthropic fork) — CONFIRMED [derived]

Setup: strong fairness = all nodes in each fiber $\{q: d_q = d\}$ have isomorphic labelled subtrees (labels = points, chance distributions, edge-actions, leaf (world, payoff) pairs). First: **no self-succession** — if a $d$-node sat below a $d$-node, a subtree would be isomorphic to a proper subtree of itself, impossible for finite trees (node-count strictly decreases). Hence $\#_d \le 1$ on every path, every $d$-node is minimal, and $\mathrm{occ}(d)$ is the disjoint union over $d$-nodes $q$ of the below-$q$ leaf events (this is Lemma 1's decomposition).

Let $\theta_d$ = the common downtree leaf-law (well-defined: isomorphic labelled subtrees + the same $C$ give identical laws; no $d$-nodes inside, so no dependence on how $d$ itself is answered below).

Per-run: $\mu(\lambda\models X \mid \mathrm{occ}(d)) = \dfrac{\sum_q \mu(\text{reach }q)\,\theta_d(X)}{\sum_q \mu(\text{reach }q)} = \theta_d(X)$.

Per-occurrence: $\#_d(\ell) = \sum_{q} \mathbf{1}[\ell \text{ below } q]$, so $\mathbb{E}[\#_d \mathbf{1}_{\lambda\models X}] = \sum_q \mu(\text{below } q \wedge X) = \sum_q R_q\,\theta_d(X)$, and $\mathbb{E}[\#_d] = \sum_q R_q$ (v2 states this identity after Theorem 1). Quotient: $\theta_d(X)$.

Both SSC senses reduce to the single equation $P_{s_d} = \theta_d$ (V-clauses identical by the same argument on payoffs, since isomorphic labels include payoffs). Under strong fairness the reduction is even simpler than the notes' computation ($\#_d \le 1$ makes per-occurrence literally equal per-run), but their computation is correct as written. The gloss — "the weights become irrelevant when every instance sees the same statistics" — is exactly what the algebra shows.

**Bonus finding (against a collapse argument, not the notes):** the claim that all nodes with the same subjective state have equivalent subtrees is FALSE as a general implication: AMD at $q=0$ has the same point (hence state) at both nodes, downtree laws both $\delta_{\text{payoff-1 leaf}}$ (weak node-SSC satisfied), yet the subtrees are non-isomorphic (nested). Subtree-equivalence must be imposed (the notes' strong fairness), not derived from statewise calibration. The notes' §1 makes this criticism implicitly; it deserves to be explicit.

### B2. Claim 1.2 (weak node-SSC misbehaves on AMD) — CONFIRMED [checked], one hygiene caveat

Weak node-SSC: for every decision node $q$, $P_{s_{d_q}} = \lambda_*\mu(\cdot\mid\text{reach }q)$, V-clause analogous. Both AMD nodes carry the same $d$, hence one state, hence the condition forces the two downtree laws equal. With $x := C(d)(a)$:

$$\theta_1 = x\,\delta_{w_0} + (1-x)\,\theta_2, \qquad \theta_2 = x\,\delta_{w_4} + (1-x)\,\delta_{w_1}.$$

$\theta_1(\{w_0\}) = x$, $\theta_2(\{w_0\}) = 0$, so $\theta_1 = \theta_2 \iff x = 0$, i.e. always-continue, value $V(0) = 1 < 4/3$. Weak node-SSC admits the unfair tree and selects a dominated procedure on it; strong fairness rejects it outright (nested $\Rightarrow$ non-isomorphic). All confirmed.

Hygiene caveat: the world-law route needs the three leaves to carry distinct worlds (Prop 5(c) specifies payoffs, not worlds). If leaves shared a world, the P-clause would be vacuous — but the V-clause still forces $x=0$: conditional payoff at node 1 is $(1-x)(3x+1)$, at node 2 is $3x+1$; with one state, equal iff $x(3x+1)=0$ iff $x=0$. The claim is robust either way.

### B3. Claim 1.3 (DAG collapse canonical under strong, not weak) — CONFIRMED [derived], one mis-gloss flagged

Under strong fairness, quotient decision nodes by point and chance nodes/leaves by labelled-subtree isomorphism. Well-defined: the fiber isomorphisms respect edge labels, so children of identified nodes are identified; each point appears once; unrolling from the root reproduces the tree up to isomorphism; the construction never consults $C$. Under weak node-SSC, two same-point nodes can have non-isomorphic subtrees whose downtree laws coincide under the ACTUAL $C$ only. Explicit witness: $C(d) = \delta_a$; node 1: $a \to (w,1)$, $b \to (w',0)$; node 2: $a \to (w,1)$, $b \to (w'',5)$; root chance $\tfrac12/\tfrac12$ routes to them. Downtree laws under $C$: both $\delta_w$ — weak-SSC-mergeable — but $V_B(C[d\mapsto b])$ = $\tfrac12(0)+\tfrac12(5)$ before merging vs $0$ or $5$ after (depending which version survives).

Mis-gloss: the notes say merging "changes the problem under every deviation, i.e. changes exactly what the tree carries beyond the extensional shadow (Remark 3.1)". The "i.e." is wrong: $\widehat B$ is the joint law for EVERY $C'$, deviations included, so the witness above changes the extensional shadow itself, not merely supra-shadow structure. The verdict (merging is a stipulation under weak, a theorem under strong) stands; the Remark-3.1 gloss should be cut or corrected.

### B4. §1 slogan + Smoking-Lesion relocation — computations CONFIRMED [checked]; dialectical use has a GAP

- (S3) lesion tree "chance $\ell$; query $d$; act $m$; chance $k\sim\mathrm{Bern}(\gamma_\ell)$; leaf $(\ell,m,k)$" (v2 §7.3): the two $d$-nodes' subtrees differ in chance labels ($\gamma_1 \neq \gamma_0$) AND leaf worlds ($\ell$-coordinate) — non-isomorphic — so the tree is strongly-unfair. [checked]
- Relocation of $d$ above the $\ell$-draw preserves the run law exactly: both trees induce $\ell \sim \mathrm{Bern}(\rho)$, $m \sim C(d)$ independent, $k \sim \mathrm{Bern}(\gamma_\ell)$; Fubini. Same extensional shadow, in fact. [checked]
- Same computation for the mugging: relocating $d$ above the coin in $B_1$ preserves the leaf law for every $C$ (two $d$-nodes on disjoint branches, draws independent of the coin). [checked]
- GAP (dialectical): the notes justify the lesion relocation by "$\ell \perp m$ AND $s_d$ does not know $\ell$", then say "the same device, applied to the coin in counterfactual mugging, is what puts the decision at the policy level ... [scrubbed] is the move everyone makes for the lesion." But in the no-doubt mugging the stipulated state has $P_s(T) = 1$ — the second conjunct of their own legitimacy condition FAILS. The value-preservation half carries over (it is $C$-independent); [scrubbed]. The parallel is weaker than advertised: relocation in the lesion respects the state; in the no-doubt mugging it overrides the state. The rhetorical point survives only as "relocation is value-preserving in both", which is true but not the announced symmetry.

### B5. §1 "consequence for the type" (observations redundant on fair trees) — GAP, substantive reading refutable as stated

Trivial reading (the node determines $O_d$): true — the node carries the point, which carries $O_d$.

Substantive reading (the type could drop $O$ from points on fair trees at no cost): has a hole. Counterexample scheme [derived]: two decision nodes on disjoint chance branches carrying points $d_1 = (s, O_1, A)$, $d_2 = (s, O_2, A)$ — SAME state (including $\mathrm{cf}$), DIFFERENT observations. Singleton fibers, so the tree is strongly fair. For both to be strictly calibrated, clause 1 forces $P_s(O_1) = P_s(O_2) = 1$, hence $\nu(O_1 \,\triangle\, O_2) = 0$: the observations must agree $\nu$-a.s. under the realized $C$, but may diverge off-path. Build the off-path divergence to carry different optimal answers (e.g. $b$-deviation at $d_2$ reaches a payoff-5 leaf in $O_2\setminus O_1$-worlds, at $d_1$ a payoff-0 leaf), and even limit calibration does not separate the states (the divergent events have vanishing limiting conditional probability, so Def 10's V-clause is silent). Then the optimum answers differently at $d_1, d_2$, and only $O$ distinguishes the points. Moreover the claim is circular as stated: dropping $O$ from the type merges $d_1, d_2$ into one point with non-isomorphic subtrees — the tree is then no longer fair — so "on fair trees $O$ is redundant" quantifies over a fairness notion whose extension depends on whether $O$ is in the type. Salvage: "on fair trees, observations distinct as events but $\nu$-a.s. equal are the only thing $O$ adds" — a much weaker statement. The gloss [scrubbed] is not licensed at the type level by fairness alone.

## C. §2: Cartesian-frame observability

### C1. The reconstructed definition — FAITHFUL [reconstructed against the local 11-eight-definitions file]

The sequence's conditional-policies definition: $V$ observable iff for all $f: V \to A$ there is $a_f \in A$ with $f(v(a_f\cdot e))\cdot e = a_f\cdot e$ for all $e$. For a two-cell partition $\{S, W\setminus S\}$ this is exactly: for all $a_0, a_1$ there is $a \in \mathrm{if}(S, a_0, a_1)$, i.e. $a\cdot e \in S \Rightarrow a\cdot e = a_0\cdot e$ and $a\cdot e \notin S \Rightarrow a\cdot e = a_1\cdot e$ — which is verbatim the notes' rendering. (The subset form appears inside the sequence's own proofs, "$a_2 \in \mathrm{if}(S_i, a_0, a_1)$".) No divergence.

### C2. Claim 2.1 (coin not observable in the mugging frame) — CONFIRMED [checked]

Frame: $A = \{\mathrm{pay}, \mathrm{refuse}\}$ (dispositions), $E = \{H, T\}$, $\mathrm{pay}\cdot H = (H, +y)$, $\mathrm{pay}\cdot T = (T, -x)$, $\mathrm{refuse}\cdot H = (H, 0)$, $\mathrm{refuse}\cdot T = (T, 0)$; $S$ = tails-worlds $= \{(T,-x), (T,0)\}$. Every action lands in $S$ under $e = T$ and outside $S$ under $e = H$ (the outcome records the coin), so "pay if $S$ else refuse" needs one $a$ with $a\cdot T = \mathrm{pay}\cdot T = (T,-x)$ AND $a\cdot H = \mathrm{refuse}\cdot H = (H,0)$:

| $a$ | $a\cdot T$ | want $(T,-x)$ | $a\cdot H$ | want $(H,0)$ |
|---|---|---|---|---|
| pay | $(T,-x)$ | yes | $(H,y)$ | **no** |
| refuse | $(T,0)$ | **no** | $(H,0)$ | yes |

Neither works: $S \notin \mathrm{Obs}$. Deleting Omega's coupling ($\mathrm{pay}\cdot H := (H,0)$): "pay if $S$ else refuse" is witnessed by $a = \mathrm{pay}$ (now $\mathrm{pay}\cdot H = (H,0) = \mathrm{refuse}\cdot H$); "refuse if $S$ else pay" by $a = \mathrm{refuse}$; constant $f$'s trivially. All four $f: V \to A$ witnessed, $S$ observable. Both halves of the claim verified. The identification "observability of the coin = absence of cross-branch coupling" is exactly what the two computations exhibit, [scrubbed].

### C3. Claim 2.2 — properly marked [guess]; plausible; direction-check

Direction sanity checks I ran: (i) fair two-branch tree with distinct points $d_1$ (on $o{=}1$) and $d_2$ (on $o{=}2$): deterministic procedures are pairs (answer at $d_1$, answer at $d_2$), so the conditional policy "$x$ if $o{=}1$ else $y$" is literally an element of the agent set — the partition is observable, matching fairness. (ii) The unfair mugging: coin unobservable (C2), matching unfairness. (iii) Warning for the eventual theorem: on the RELOCATED (fair) lesion tree the partition $\{\ell{=}1, \ell{=}0\}$ is NOT observable (the single-point agent set $\{a, b\}$ has no conditional policy), yet the tree is fair — so the equivalence must quantify only over the partitions serving as observations $O_d$ of queried points (the notes' scare-quoted "chance-determined 'observations'"), not over all chance partitions. As stated the claim survives (iii) only under that reading. Left open, as the notes honestly do; the sub-agent machinery they name as missing is indeed what "reach $q$ depends on earlier choices" requires.

### C4. §2 [scrubbed]

The factorization reading ("a chance event is a proper Observation iff the value function on policies factorizes across it") is correct for the mugging: $V$ couples the $T$-component of the policy to the $H$-branch payoff, so no factorization; deleting the coupling restores it. [derived] [scrubbed]

## D. §3: coherence, Kuhn, backward induction

### D1. Kuhn reconstruction + AMD behavioral/mixed computation — CONFIRMED [checked] with one WRONG ATTRIBUTION of hypothesis

- Kuhn's theorem as recalled (perfect recall $\Rightarrow$ behavioral and mixed strategies outcome-equivalent) is the standard statement. [reconstructed: standard game theory; consistent with v2's Piccione–Rubinstein citations]
- AMD arithmetic: pure policies are always-$a$ (value 0) and always-$b$ (value 1); a mixed strategy $p\,\delta_{\text{always-}a} + (1-p)\,\delta_{\text{always-}b}$ — one seed drawn per run, used at both nodes — has value $p\cdot 0 + (1-p)\cdot 1 = 1-p \le 1$; behavioral attains $4/3$. "Behavioral achieves 4/3, mixed at most 1": CONFIRMED [checked].
- **Flag: "Strong fairness implies perfect recall trivially (a point never recurs on a path)" is wrong as stated.** What no-recurrence gives is NO ABSENTMINDEDNESS, a strictly weaker property than perfect recall (perfect recall also requires remembering one's own past actions and past information; a fair tree can route two different past actions at $d_1$ into nodes of one later point). The conclusion the notes need survives anyway, by a different route: under no-absentmindedness $V_B$ is multiaffine in the tied variables (v2 Definition 21), so $\max_{\text{behavioral}} = \max_{\text{pure}}$ (vertex attainment) and $\max_{\text{mixed}} = \max_{\text{pure}}$ (a mixed value is an average of pure values); hence optimal values coincide, which is all Claims 3.2/5.1 consume. Full Kuhn outcome-equivalence (every mixed matched by a behavioral) fails under mere no-absentmindedness in general (forget-your-own-action example with four distinct leaf-worlds: mixed $\tfrac12(a,c)+\tfrac12(b,e)$ realizes a correlated leaf law no product can) — though THAT example is not strongly fair (strong fairness would force the two later subtrees to carry identical leaf labels, erasing the correlation's trace). Whether strong fairness restores full outcome-equivalence is open; the value-level statement is what is proved. Verdict: computations CONFIRMED; the "perfect recall" bridge is a misattribution — repair: "strong fairness implies no absentmindedness, and no absentmindedness already gives value-equivalence of behavioral and mixed optima via multiaffinity."
- Also flag: "mixed strategies (one draw of a pure policy — Q12's shared seed)" identifies mixed with shared-seed. Exact for one-point problems (the AMD); loose in general — Q12's shared seed draws per-point independently (correlation within a point's occurrences, none across points), whereas mixed strategies may correlate across points. Harmless here, worth a parenthesis.

### D2. Claim 3.1 (Definition 22 too weak under self-succession) — CONFIRMED [checked]; genuine v2-internal seam

Definition 22 verbatim quantifies over $a \in A_d$ — pure all-occurrence deviations only. At $q = \tfrac12$ on the AMD:

$$V(\tfrac12) = \tfrac12\cdot\tfrac52 = \tfrac54; \quad V(C[d\mapsto a]) = V(1) = 0 \le \tfrac54; \quad V(C[d\mapsto b]) = V(0) = 1 \le \tfrac54.$$

So $q=\tfrac12$ is $B$-coherent per Def 22. Mixed deviation $m(a) = \tfrac13$: $V(C[d\mapsto m]) = 4/3 > 5/4$. Not optimal, and not a best response over the simplex. Theorem 1 catches it: with full support, its condition needs $a$ and $b$ both in the argmax of $\sum_q R_q G_q(\cdot)$, i.e. $\partial V/\partial q = \sum_q R_q[G_q(a) - G_q(b)] = 0$; but $V'(\tfrac12) = -1 \neq 0$. All three computations verified.

v2-internal seam (task item): Def 6 (via change-log 23) defines $C[d\mapsto m]$ for mixed $m$ precisely because Def 9 consumes it; Def 22 then quantifies pure-only; Theorem 2 ties Def 22 to EDT+SSA only for DETERMINISTIC $C$. For stochastic $C$, Def 22 is strictly weaker than "no deviation improves" — the AMD at $q=\tfrac12$ is the witness — and v2's comment (i) after Def 22 ("the all-occurrences deviation is also the only well-typed deviation") elides that mixed all-occurrence deviations are equally well-typed. The notes' repair (quantify over $m \in \Delta(A_d)$, making coherence a best-response condition) is correct and costless for the deterministic regime Theorem 2 governs. Also verified: at the AMD optimum $q = 1/3$, both Theorem 1's condition ($V'(1/3) = 0$) and Def 22 ($0, 1 \le 4/3$) hold, as v2's comment (ii) says.

### D3. Claim 3.2 (fair + tremble-EDT $\Rightarrow$ optimal; backward induction) — GAP (directionally right; three holes, all fillable)

The intended theorem is the transposition of "in one-player extensive games, trembling-hand-perfect = backward-induction = optimal". Sanity instance [checked]: root query $d_1$ ($a \to$ query $d_2$; $b \to$ leaf 3); $d_2$: $a \to 4$, $b \to 0$. Bad pair $C = (b, b)$: value 3; strictly calibrated with a stipulated off-path state at $d_2$ promising 0 (off-path unconstrained), and $T_{\mathrm{EDT}}$ approves $b$ at $d_1$ ($3 > 0$). Under trembles the $\varepsilon$-calibrated state at $d_2$ has $V(a) \approx 4 > 0 \approx V(b)$, so $T_{\mathrm{EDT}}$ rejects $C$'s $b$ at $d_2$: not tremble-consistent. The optimal $(a,a)$ is. Mechanism as claimed.

Holes in the sketch as written:

1. **Type mismatch with Remark 3.12.** Tremble-consistency is defined for an ABSTRACT problem $\Sigma$: "for every sufficiently small $\varepsilon$ some instantiation $B_\varepsilon \in \Sigma$ is strictly calibrated for $C^\varepsilon$ and $T(C, B_\varepsilon)$ holds" — states are re-fitted per $\varepsilon$. Claim 3.2 applies it to a fixed concrete $B$. The fix is the reading v2 itself uses on five-and-ten: take $\Sigma_B$ = $B$'s tree with states freed; then "$B$ tremble-consistent" means the $\varepsilon$-recalibrated instantiations approve $C$. The notes' phrase "the limit-calibrated state at each node sees the true continuation values" compounds the slip: limit calibration is Definition 10 (fixed state equals the $\varepsilon\to 0$ limit), a different device from Remark 3.12's per-$\varepsilon$ recalibration, and v2's Remark 3.9 is explicit that Def 10 ALONE does not deliver the five-and-ten verdict. The sketch needs the Rem-3.12 device throughout. (Direct answer to the task's question: no, Remark 3.12 does not have the form Claim 3.2 assumes; the states-freed reading must be interposed.)
2. **Missing action-veridicality.** The sketch assumes "veridical labelling (Proposition 3's hypotheses at every point)" = subtree-veridicality + coverage. That identifies conditioning on $O_d$ with conditioning on reaching the fiber, but EDT conditions on the act-EVENT $a$; to equate $\mathbb{E}[r \mid a \wedge O_d]$ with the continuation value of DRAWING $a$ one needs action-veridicality and the only-via-the-draw clause — i.e. recording (Def 7), not just Prop 3's hypotheses. Fillable by strengthening the hypothesis.
3. **The induction step needs writing.** With fibers behaving as single nodes (isomorphic copies, summed reach — fine under B1's no-self-succession) and $\varepsilon$-calibrated states, $V_{s_d}(a) = \mathbb{E}_{\mu^\varepsilon}[r \mid a \wedge O_d]$ is the trembled continuation value; support $\subseteq$ argmax at every small $\varepsilon$ forces argmax of the limit (polynomials in $\varepsilon$, eventually-stable signs); leaves-up induction then yields optimality. I see no obstruction, but it is a proof to be written, not written.

Verdict: GAP, fillable; the headline "EDT = UDT on fair problems needs trembles, not just fairness" is correct and the without-trembles counterexample (off-path stipulation, my sanity instance) is genuine.

## E. §4: which EDT; dilution; shared seed

### E1. Claim 4.1 (tremble-EDT under independent redraws = Theorem 1 / CDT+SIA) — CONFIRMED [checked + derived]

General argument (better than instance-grade): under independent redraws, $\mu^\varepsilon$ is generated by independent draws at nodes plus chance; "reach $q$" involves only non-$q$ draws; so conditioning on "drew $a$ at $q$, having reached $q$" equals FORCING $a$ at $q$ with all other nodes on $C^\varepsilon$ — the conditional value is $G_q(C^\varepsilon, a)$ by definition, and $G_q(C^\varepsilon, a) \to G_q(C, a)$ (leaf probabilities polynomial in $\varepsilon$). Per-occurrence self-location weights $R_q/\mathbb{E}[\#_d]$ then reproduce Theorem 1's $\arg\max_a \sum_q R_q G_q(C, a)$ up to positive normalization. This is Appendix B's conjecture, instantiated; the notes mark it [checked on the $k$-fold mugging] — the underlying argument is general, so it deserves [derived], a strengthening not a correction.

$k$-fold mugging instance, concave case at $q = 1$ [checked]: structure — coin $\tfrac12$; $T$: one real query (pay costs $x$); $H$: $k$ simulation queries, transfer $y$ w.p. $b_j$, $j$ = number of paying draws. $R_{\text{real}} = \tfrac12$, $R_{\text{sim},i} = \tfrac12$ each, $\mathbb{E}[\#_d] = \tfrac{1+k}{2}$. With $b_j = \mathbf{1}[j \ge 1]$ at $q = 1$: $G_{\text{real}}(\mathrm{pay}) = -x$, $G_{\text{real}}(\mathrm{refuse}) = 0$; at a simulation node, the other $k-1$ draws all pay, so $b = 1$ either way: $G_{\text{sim}}(\mathrm{pay}) = G_{\text{sim}}(\mathrm{refuse}) = y$. $\sum_q R_q[G_q(\mathrm{pay}) - G_q(\mathrm{refuse})] = -x/2 = \partial V/\partial q\big|_{q=1}$ — Theorem 1's identity, concretely.

### E2. §4 dilution computations — CONFIRMED [checked]

$V(q) = \tfrac12\big({-}xq + y\,\mathbb{E}_{j\sim\mathrm{Bin}(k,q)}[b_j]\big)$.

- Linear $b_j = j/k$: $\mathbb{E}[b_j] = q$, $V = \tfrac12 q(y - x)$ — affine in $q$, slope independent of $k$: no dilution. ✓
- Concave $b_j = \mathbf{1}[j\ge 1]$: $\mathbb{E}[b_j] = 1 - (1-q)^k$, $\partial V/\partial q = \tfrac12(-x + yk(1-q)^{k-1})$; at $q = 1$ this is $-x/2$ ✓ (notes' value). $V$ concave in $q$ (second derivative $\le 0$), so the interior first-order point $(1-q)^{k-1} = x/(yk)$ is BOTH the Theorem-1-ratifiable rate and the optimum ✓ ("a decayed pay-rate, which here is also the optimum").
- Convex $b_j = \mathbf{1}[j = k]$: $\mathbb{E}[b_j] = q^k$, $\partial V/\partial q\big|_{q=1} = \tfrac12(ky - x)$ ✓. For $y < x < ky$: all-pay has positive derivative (support $\{\mathrm{pay}\}$ is in the argmax — Theorem-1-ratifiable) yet $V(1) = \tfrac12(y - x) < 0 = V(0)$ — ratifiable-not-optimal ✓ ("pay-when-you-shouldn't equilibrium").

All three curvature verdicts and both quoted derivative values check out. The moral (dilution's sign is the coupling's curvature, not a uniform $1/k$) is exactly what the computations show.

### E3. Claim 4.2 (shared seed + per-run = Theorem 2) and the 2×2 — CONFIRMED [derived], caveats on the "mixed" cells

Under shared-seed semantics the run draws one action per point; conditioning on "my instance's draw was $a$" conditions the seed, i.e. every $d$-node on the run answers $a$, other points' seeds untouched: the conditional run-law is $\mu_{B, C[d\mapsto a]}$ (deterministic-at-$d$, so shared vs independent coincide there). Per-run averaging gives $\mathbb{E}_{\mu_{C[d\mapsto a]}}[r \mid \mathrm{occ}(d)]$ — Theorem 2's evaluator after the SSA cancellation, whose argmax is $\arg\max_a V_B(C[d\mapsto a])$ (using Lemma 1's deviation-invariance of $\mu(\mathrm{occ}(d))$, whose proof — reach involves non-$d$ draws only — survives the seed change). So shared-seed/per-run = Def-22 coherence ✓. The two off-diagonal cells are asserted only as "mixed" (unspecified); fine as a table, but nothing is proved about them. The interpretive line — anthropic uncertainty buys updatelessness ONLY if my draw and the simulation's draw are the same draw — is exactly what E1 vs E3 jointly establish. CONFIRMED.

### E4. §4 "shared seed derives $\rho$" — GAP (right in spirit; skips an algebra enrichment)

"The seed for $d$ on this run is $a$" is an event on the RUN space, not (as Remark 4.2's $\rho$ requires) an event in $\mathcal{E}$: in Prop 6's algebra the $H$-branch worlds read choice $= \bot$ and record no seed. To hand $\rho_d(a)$ to $\mathrm{UDT}_{s^\circ,\rho}$ (whose prior is a probability on $\mathcal{E}$) one must enrich $\mathcal{E}$ with seed/disposition coordinates — a Prop-2-flavored lift, and exactly the "richness condition on the algebra" Remark 4.2 already flags (Remark 6.3, Q1). Same objection applies to Claim 5.1's "a recorded draw, hence an event": v2's Definition 3 types actions as pairwise-disjoint EVENTS of $\mathcal{E}$, so the relocated point's product-actions only exist if $\mathcal{E}$ carries would-pay-style coordinates. Both derivations of $\rho$ are real but conditional on the enrichment; the notes should say so.

### E5. §4 "the price" (shared seed collapses Prop 4 to affine) — CONFIRMED [checked]

Under shared seed all $k$ queries on a path return the one seed bit: the observable pattern $S \subseteq [k]$ degenerates to $\{\emptyset, [k]\}$, so realizable $q \mapsto \Pr(X)$ collapse from $\{\sum_j b_j\binom{k}{j}q^j(1-q)^{k-j}\}$ to $\{b_0(1-q) + b_1 q\}$ — Prop 4 at $k = 1$. Probing dies; Remark 5.4's Bernstein story (branching swallows labels in the limit) needs independent redraws. Trade-off correctly stated. ✓

## F. §5: repairs and "same problem"

### F1. Claim 5.1 (relocation = Definition 11 made structural; UDT = EDT at the root) — CONFIRMED in part [derived], GAP in part

- Relocated-root calibration = prior calibration: at a root point with $O = \top$, strict OC clause 1 reads $P_{s}(X) = \nu(X \mid \top) = \nu(X)$ — literally Def 11's clause — and the V-clauses match likewise. CONFIRMED [checked]. A clean observation.
- $\mathrm{UDT}_{s^\circ,\rho}(d) = \mathrm{EDT}(\hat d)$: exact for ONE-POINT problems (the mugging: $A_{\hat d} = A_d$, $\rho_d(a)$ = the root-draw event, $V_{s^\circ}(\rho_d(a))$ = the root state's conditional value of that action-event). For multi-point problems EDT at the root maximizes over JOINT policies while $\mathrm{UDT}_{s^\circ,\rho}(d)$ maximizes componentwise over $V_{s^\circ}(\rho_d(a))$, an $s^\circ$-average over the policies containing $a$ — these coincide only under extra conditions (independence across components in $s^\circ$, or a fixed-point/consistency argument). GAP as a general identity; fine on the worked examples.
- Value preservation "$V_{\tilde B}(\pi) = V_B(\pi)$": needs care [derived]. Deterministic policies: always preserved (the single root draw reproduces the deterministic answers; even the AMD preserves $a \mapsto 0$, $b \mapsto 1$). Mixed policies: preserved iff the original tree has no self-succession — on the AMD, relocation (one choice for the indistinguishable instances, drawn once) gives $V(q) = (1-q)\cdot 1$, killing the behavioral $4/3$; sup drops to $1$. For no-self-succession trees the relocated single product-draw restricted to any path has the same law as the original independent draws (each point met $\le$ once per path), so all mixed values are preserved and the optimum is too. The notes flag the AMD exclusion in their Q2, but Claim 5.1's headline equation should carry the no-self-succession hypothesis explicitly.
- "Under Claim 3.2, EDT at the relocated root is then the optimum": for the FULLY relocated tree this needs only the one-node case of Claim 3.2 — a single point whose $\varepsilon$-calibrated (or masked, interior) state sees the true value of each policy-action; EDT maximizes; optimum attained. That much is solid [derived]; it inherits none of D3's induction burden.

### F2. §5 "what Q3 should ask" ($B \sim B'$ iff equal value functions on shared policies; UDT invariant under $\sim$) — plausible, one elision

$T_{\mathrm{opt}}$ (v2 Def 18's optimality shape) is a function of $V_B$ alone, hence $\sim$-invariant — trivially true if "UDT" means $T_{\mathrm{opt}}$ [checked from Def 18]. The parameterized procedures $\mathrm{UDT}_{s^\circ,\rho}$ are NOT obviously $\sim$-invariant (their verdicts consult $s^\circ$ and $\rho$, which live on $\mathcal{E}$, not on $V_B$). The notes' sentence "UDT is precisely the theory invariant under $\sim$" silently means the optimality theory, and "precisely" (the converse: any $\sim$-invariant theory is UDT) is unargued. Also "$\sim$" needs the domain patch the notes themselves note (relocation changes the point set, so "shared points" does real work). Directionally fine; overstated by one word.

## G. §6: three realities; decay

### G1. Claim 6.1 (the three realities are one tree at the value level) — CONFIRMED at the value level [derived]; one distinction worth preserving

The collapsed one-node tree with $r = \tfrac12(y-x)\mathbf{1}[\mathrm{pay}]$, refuse $\mapsto 0$: EDT at any state with both acts live pays iff $y > x$, which is $V_{B_1}$'s optimality condition ✓. The three glosses (stipulated chance / self-location credence / caring weight) assign the same number $\tfrac12$ three names and the same value function results. Two qualifications: (i) marginalizing the coin's chance node into the payoff changes the concrete tree and its $\nu$ (no $H$-worlds afterward), so the readings ARE distinguishable at the calibration level even though not at the value level — which is not a defect of the claim but exactly where its own §6 then locates decay; (ii) [scrubbed]: the collapsed tree needs a disposition-bearing payoff or a multiverse world, no anthropics. Verdict: CONFIRMED with scope "at the level of the value function on policies".

### G2. §6 decay formalizations — arithmetic CONFIRMED [checked]

- Coupling-uncertainty threshold: $\pi\cdot\tfrac12(y-x) + (1-\pi)\cdot\tfrac12(-x) = \tfrac12(\pi y - x) > 0 \iff \pi > x/y$ ✓.
- Refuser self-confirmation: under BOTH hypotheses a refuser generates no transfers (coupling only moves money for payers), likelihood ratio 1, no update — the learning trap and the Frame Break's point stand ✓. The dilution reading's numbers are E2's ✓.
- The Frame Break's logical point (an argument that caring measure can fade and so realism cannot be held is invalidated if what fades is coupling-credence) is a correct observation of a hidden premise: the inconsistency argument needs the fading thing to be the branch-weight itself.

## H. §7: spoofers, counterlogicals, answers per sense

### H1. "All tree-representable predictors are spoofers" — CONFIRMED with caveat [derived]

Remark 5.1 (quoted accurately): branching on sampled draws is the ONLY internal inlet for $C$-dependence; label-dependence lives at the abstract level; Prop 4 bounds probing. Hence any concrete Omega is a query-based sampler ✓. Caveat: "each simulated instance is a consulted node off the observation" is not forced in general — a predictive query can be a routing node sitting above both observation-cells (Told-You-So's $d_5$ root) rather than a node inside the wrong branch; what is true is that a predictive query is never a recording instance of the point it samples (it fails subtree-veridicality or sits where the observation is undetermined). In the canonical Newcomblike trees (mugging $B_1$, TN V1/V2) the simulated instances are literally off-observation ✓. The anthropic conclusion ("with what probability am I being deluded" = self-location among $k{+}1$ instances, unavoidable inside the tree, avoidable only by relocation) follows ✓.

### H2. Counterlogical mugging — mostly CONFIRMED [derived]; one link is [guess]-grade

Representing the spoofed computation on an algebra of sentences modulo a weak theory (so the false digit-claim is $\ne \bot$) is consistent with v2's algebra-relativity and keeps Def 2's no-counterpossibles scope intact ✓. "The cases the formalism cannot represent [concretely] are the cases no tree can instantiate" ✓ — with the precision that v2 DOES host label-dependent Omegas abstractly (Def 14); the notes say "no concrete realization", which is the right statement. The identification "out-of-scope counterlogical residue = non-simulating label-dependent Omega" is asserted, not argued — it conflates two exclusions (counterpossible supposition; label-dependence) that coincide in this example but have no proven general relation. Downgrade that sentence to [guess].

### H3. Answers per calibration sense — table CONFIRMED

The table: 100%-know-your-branch with spoofing Omega — strict/masked OC admit it (A1; strict at the fixed point $q = q_0$), per-run and per-occurrence SSC reject it (A2), strong fairness rejects it (non-isomorphic subtrees) ✓ each entry recomputed above. "Spoofing is non-subtree-veridicality (Remark 3.3), the default; OC tolerates (Remark 3.4), SSC forbids unless the state accounts for it" — accurate readings ✓. [scrubbed]

## I. v2-internal findings (the seams the audit touched)

1. **Def 22 pure-only vs mixed elsewhere** — real seam; witness AMD $q{=}\tfrac12$ (D2). Repair: quantify over $m \in \Delta(A_d)$; Theorem 2 unaffected (deterministic hypothesis); comment (i)'s "only well-typed deviation" should say "only well-typed LOCUS of deviation" — the mixed deviations at that locus are well-typed too.
2. **Remark 3.12's type** — tremble-consistency is $\Sigma$-level with per-$\varepsilon$ re-instantiation; any concrete-$B$ use (notes' Claim 3.2) needs the states-freed $\Sigma_B$ reading spelled out (D3.1). Not an error in v2, but an affordance gap: the document never defines the concrete-problem form its own five-and-ten discussion gestures at.
3. **Prop 5 and Prop 6 say what the notes need** — Prop 5(c)'s numbers verified (shared apparatus); Prop 6's masked-for-every-procedure claim verified including the interior-$q_0$ boundary caveat (A1); Prop 6's two value formulas verified.
4. **No other wobble found** at the audited seams: Lemma 1's proof survives shared-seed semantics for the specific use in E3; Def 13's two normalizers behave as stated under strong fairness (B1); Def 8's clause-1/clause-2 interplay in A1 is as documented.

## J. What I could not settle

1. Claim 2.2's equivalence (fairness $\leftrightarrow$ CF-observability of the tree's observation-partitions in the deterministic-procedures frame): open, as the notes say; my (iii) in C3 pins the quantifier it must use.
2. Whether strong fairness restores FULL Kuhn outcome-equivalence (not just value-equivalence) — my erasure argument (D1) suggests yes for the correlation-trace reason, unproven.
3. Whether the B5 counterexample (same-state, $\nu$-a.s.-equal-but-divergent observations on a fair tree) can be closed by imposing recording at every point for every $C^\varepsilon$ — I did not find the proof or a countermodel.
4. The multi-point $\mathrm{UDT}_{s^\circ,\rho} = \mathrm{EDT}(\hat d)$ identity (F1) — open under which conditions on $s^\circ$.
5. The two "mixed" cells of the 2×2 (E3) — uncharacterized, as in the notes.


