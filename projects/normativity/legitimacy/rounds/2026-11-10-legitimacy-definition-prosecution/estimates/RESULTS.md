# Results — manipulation as induced miscalibration

Statements by the dispatch's questions (`PROMPT-followup-6.md` §5), each with one status:
**proved** (the proof is here, on paper, not kernel-checked; the runner recomputes the
statement on seeded random finite cases), **holds on the stated example**, **refuted**
(the counterexample is here), or **open**. A passing runner certifies the status strings
against the checks in `checks.py` and the two COUNT lines against the bank; it does not
certify the prose. `E` is expectation under the law the actual policy fixes unless said.

## Question 1 — C1–C6

| | status | statement |
|---|---|---|
| 1.1 | **proved** | C1 as stated, for any information `I`: `(E[x] − E[X])² ≤ E[(x − E[X|x])²] ≤ E[(x − E[X|x,I])²]`, and the split of expected squared error |
| 1.2 | **proved** | C2 as stated, under squared loss, "deferring" meaning she uses `x` itself |
| 1.3 | **proved** | C3 as stated, with her choice a function of her information; then the left side is her expected loss in true utility against the best she could do on her information |
| 1.4 | **holds on the stated example** | C3's constant is not tight: `√2` in place of `2` holds (the proof of 1.3) and is attained |
| 1.5 | **proved** | in C3 "her information" can be replaced by any coarser information, with the benchmark `max_a E[U*_a | that information]` weakened accordingly |
| 1.6 | **refuted** | C3 bounds her loss in true utility whatever her choice depends on |
| 1.7 | **proved** | C4's threshold: with the undetected score at most 1, a departure pays only if `p < (1 − V_h)/(1 + δ₀)`; with `V_h ≥ 0`, none pays at `p ≥ 1/(1 + δ₀)` |
| 1.8 | **refuted** | C4's last clause as stated: under "right on average under honest conduct" the honest optimum's expected score is the expected true utility |
| 1.9 | **proved** | C4 with a detected departure also a violation at weight `λ`: it pays only if `p < (1 − V_h)/(1 + δ₀ + λ)`, a threshold below 1/2 |
| 1.10 | **holds on the stated example** | C4 when she has sized up the policy: `E[V] = E[U*]` under every policy; with no detection only uninformative reporting is stable against a verdict-maximizer; with detection at the threshold truthful reporting is |
| 1.11 | **proved** | C5 as stated |
| 1.12 | **holds on the stated example** | C5's hypothesis has a non-trivial instance, and the bound is attained when the adviser's estimates equal realized scores |
| 1.13 | **refuted** | C5's conclusion is no regret in true utility |
| 1.14 | **holds on the stated example** | C6: the identity, and a nonzero second term for an honest adviser that maximizes her verdict; in the example her miscalibration is the same with and without the selection |

**1.1.** `E[x − E[X|x,I]] = E[x] − E[X]` by the tower property; Jensen gives the first
bound with `I` trivial. `E[(x − E[X|x,I])²] = E[(x − E[X|x])²] + E[(E[X|x,I] − E[X|x])²]`
because `x − E[X|x]` is a function of `x`. The split is the same orthogonality. ∎

**1.2.** Write `p = E[X|F]`, `q = E[X|x,F]`. `E[(p − X)²] = E[(p − q)²] + E[(q − X)²]`
since `p − q` is a function of `(x,F)`; `E[(x − X)²] = E[(x − q)²] + E[(q − X)²]`
likewise. Subtract. ∎ This is the calibration–refinement split of a quadratic score
(attributed from memory to Murphy 1973 and DeGroot and Fienberg 1983; neither was
checked).

**1.3, 1.4, 1.5.** Fix any vector `w` of references, `a*` a maximizer of `w`, `c` her
choice, `d_a = u_a − w_a`. Pointwise
`w_{a*} − w_c = −d_{a*} + (u_{a*} − u_c) + d_c ≤ R + |d_{a*}| + |d_c| ≤ R + √2·√(Σ_a d_a²)`,
the last step because `a* ≠ c` or the left side is 0. Taking expectations and Jensen,
`E[max_a w_a − w_c] ≤ E[R] + √(2M_w)`, `M_w = Σ_a E[d_a²]`. With `w = ū` this is C3 with
`√2`, hence with 2. Nothing used that `w` is a conditional expectation, so any reference
may stand there (1.5). Equality (1.4): two moves, `ū = (2ε, 0)`, `u = (ε, ε)`, she takes
the second: loss `2ε`, `R = 0`, `M = 2ε²`. When `c` is a function of her information,
`E[ū_c] = E[U*_c]` and the left side is her loss in true utility against
`E[max_a ū_a]`. ∎

**1.6.** Two states at even odds, two moves, `U* = (1,0)` and `(0,1)`; her information
is trivial, `u = ū = (1/2, 1/2)`; her move is the worse one at each state (a tremble
correlated with the state). `R = 0`, `M = 0`, loss in true utility 1/2.

**1.7, 1.9.** A departure scores at most `(1 − p)·1 + p·(−δ₀)` against `V_h`; it pays
only if that exceeds `V_h`. With weight `λ` on a detected departure the second term is
`p·(−δ₀ − λ)`. Since `λ > 1 + δ ≥ 1 + δ₀`, `1/(1 + δ₀ + λ) < 1/2`. Hypotheses used: the
adviser's score absent detection is her verdict, at most 1; `p` is a lower bound on the
detection probability of every departure; `V_h` is the adviser's expectation, on what it
knows, of her verdict under honest conduct. ∎

**1.8.** Two options, each worth 1/2. Her honest verdict on an option is `1/2 + e`,
`e = ±1/4` at even odds, independent across options; over an option taken at random her
verdict is right on average. The adviser reports honestly and takes the option she rates
higher: expected score 5/8, expected true utility 1/2. The clause holds under the
stronger hypothesis `E[V_h − U* | the adviser's information and choice] = 0`.

**1.10.** If her verdict is `E[U* | what she observes]` under the actual law, the tower
property gives `E[V] = E[U*]` for every policy: no policy inflates her on average, and
an undetected departure gains the adviser nothing in expectation over states. At a given
state it can: two states of the adviser's knowledge (the outcome worth 1 or 0), two
messages. Of the four deterministic reporting policies, the two from which no state
gains by sending the other message are the two constant ones. With a false report
detected at `p ≥ 1/(1 + δ₀)` truthful reporting is stable as well, by 1.7. So for the
sophisticated principal detection buys information, not protection from inflation.
(The example reads an unused message as bad; that the result is the known one for cheap
talk with a sender who wants only a high verdict is from memory and was not checked.)

**1.11. Lean-ready statement.** In `Sequential` (the file's lines 404–419), with
`LimsupLE` (line 358), `excess` (439), `Maximizes` (444), `UnbiasedFromFeedback` (451):

    theorem trueScore_noRegret (Q : Sequential A) (Ustar : ℕ → ℝ) (β : ℝ)
        (hmax : Q.Maximizes) (huff : Q.UnbiasedFromFeedback)
        (hinfl : LimsupLE (fun K => (∑ k ∈ range K, (Q.V k - Ustar k)) / (K : ℝ)) β)
        (a' : ℕ → A) (ha' : ∀ k, Q.avail k (a' k)) :
        LimsupLE (fun K => (∑ k ∈ range K,
          (Q.U k (a' k) - (Ustar k - Q.lam * Q.N k))) / (K : ℝ)) β

Proof. `U_k a'_k − S*_k = (U_k a'_k − S_k) + (V_k − U*_k)` termwise, so the average is
`excess a' K` plus the average inflation; `theorem3b` gives `LimsupLE (excess a') 0`,
and `LimsupLE.add` (line 368) with `hinfl` gives the bound `0 + β`. `theorem3a` does not
mention `V`'s relation to anything and is unchanged. ∎ No bound on `Ustar` is used.

**1.12.** `V_k = 1/2`, `U*_k = 1/2 + (−1)^k/4`: the average of `V − U*` tends to 0 with
`V ≠ U*` at every step. Where `U_k a_k = S_k` at every step, the conclusion at `a' = a`
is an equality: the bound cannot be improved.

**1.13.** Each round, option `a` is worth 1/2 and she rates it 1/2; option `b` is worth
1 and she would rate it 0; the adviser's estimates are her verdicts and it takes `a`.
`β = 0`, C5's quantity at `a' = b` is `0 − 1/2`, and she loses 1/2 a round against `b`.
C5 compares the true score of what was done with the adviser's estimate of her
*verdict* on the alternative. It is a statement about inflation of the realized verdict
and says nothing where she underrates what was not done.

**1.14.** The identity is `V − U* = (V − V_h) + (V_h − U*)` conditioned on what the
adviser knows; it needs `V_h` on the same probability space, which `SETTING.md` §3.5
supplies by keeping the choice and replacing the report. In the example of 1.8 the first
term is 0 and the second 1/8. Her miscalibration is 1/16 under the selecting policy and
1/16 under one that takes the first option: *worse calibrated* does not register the
selection (case Q10).

## Question 2 — the cases

COUNT start: right 76, missed 10, convicted 4, routed 6, unfixed 4, not counted 8
COUNT end: right 72, missed 11, convicted 4, routed 12, unfixed 0, not counted 9

The standard is `SETTING.md` §3.12; *start* and *end* are the two stances of §3.9. The
bank has 108 cases: 47 objectionable, 45 innocent, 7 her own, 9 contested (not counted).
Every rendering is the executor's, so a match is consistency of the formalization with
the description given, as in the fifth follow-up.

**Wrong, both stances.** *Missed*: **K9** an advocate for an undisclosed side and **Q2**
strategic silence (her mistake, and the adviser is truthful; both are *induced* under
the forthright norm); **K13** buried information (she is calibrated and less informed);
**K31** a rare lie she allows for (she is calibrated; honest conduct would leave her
worse calibrated, by 1/242); **K2** a lie that leaves her better off and **Q3**, **Q3b**
a lie that offsets her bias (total miscalibration is lower, or no higher, than under
honest conduct; K2 and Q3b are *induced* if "worse" is read as worse on some listed
quantity, and that reading convicts no innocent case of the bank); **X3** a feed that
narrows, taken as representative, and **Q11** a craving exploited by a policy that is
the same toward everyone (her mistake; the policy does not differ at the other type);
**D1** dependence built honestly. *Convicted*: **NP13** a teacher's feigned excitement,
**Q5** a surprise party, **Q6** a magician, **Q7** a bluff at poker: the account has no
clause for deception she agreed to or that a practice allows.

**Wrong under *end* only.** **K29**, every end revised in turn with the adviser
arranging the occasions: no mistake and nowhere.

**Routed** (objectionable, not manipulation, in coercion, tie or alteration). Both
stances: K10, K12, K33a (threat, forced move), E6 (the camp), N8b (blanket nagging: an
action mistake of hers, and the cost imposed is coercion by §3.11), X3b. Under *end*
also NP8, K15, K21, K23, X1, X2b: every case of taste shaped by a responsive adviser.

**Unfixed under *start***: K17 (law for music), K19 (a conversion that fits), K24, L14
(a moral argument changes a value). The stance needs to be told whether her starting
values endorse the history, and these descriptions do not say.

**What the count does not test.** For the seven cases marked *own* the standard asks
only that no adviser be convicted. For the cases whose verdict rests on "responsive" or
"blanket", or on "endorsed", the rendering states the deciding fact outright.

The verdict on each case with its facts is the runner's output (`python3 run.py` in the
round directory, section *estimates*); the divergences from prediction are in
`DIVERGENCES.md`.

## Question 3 — convicting and acquitting

**Honest influence is not convicted.** Hard truths (K3, K27, K27b, L7), a teacher (K7,
L6), a disclosed advocate (K8, L5), a sincere adviser who is mistaken (K25), silence
(Q1), truthful emphasis fitted to the customer (Q9): none is manipulation under either
stance or either norm, and no inner goal is read. What does the work is that honest
conduct is its own counterpart and that the adviser's policy is the same at the other
type. Three qualifications. (i) In K3, K27, K27b and K25 she has an estimation mistake
of her own: at her information, an estimate that does not use the difference between
two reports she received is miscalibrated (3/64 in K3). Under the alternative of §3.3
(calibration at the estimate alone) K3 and K27 have none. (ii) *Triggered* reads the
policy at a type the adviser did not face. A cruel truth told only to one who will
overreact is manipulation (Q12); the same sentence from a policy that tells everyone is
not (K27b). That is a counterfactual about the policy in the place where Noggle has an
intention. (iii) *Withholding* is never manipulation toward a principal who reads
silence rightly, under either norm, because being less informed is not a mistake (K13).

**More accurate by a bad means.** A lie that leaves her total miscalibration lower is
not manipulation (K2, Q3); whether it is when the adviser's own reading is listed
depends on whether "worse" sums over quantities (Q3b: 1/16 against 1/16, not worse) or
asks for some quantity (worse). A cue she cannot notice that leaves her more accurate is
alteration (Q4).

**Objectionable cases with no mistake.** Of 47 objectionable cases, 7 have neither kind
of mistake under *start*: 3 in coercion, 4 nowhere (K13, K31, Q3, D1). Under *end* 16
have neither: 4 in coercion, 7 in alteration, 5 nowhere (the four, and K29). None is in
*tie*; the three tie cases of the bank are contested.

## Question 4 — Reading A

The model: a finite set of histories; a history fixes what happens and how she rates
things along it; her estimate at time `t` is `u_t`, a function of what she has observed
by `t`; `U*` is one function on histories.

| | status | statement |
|---|---|---|
| 4.1 | **proved** | if her time-slices are calibrated at nested information then `E[u_T | F_0] = u_0`; two calibrated slices can differ at every history |
| 4.2 | **proved** | `|E u_T − E u_0| ≤ √m_0 + √m_T`, `m_t` the miscalibration of `u_t` for `U*` at the estimate alone |
| 4.3 | **holds on the stated example** | Reading A admits `U*(h)` = what her values at the end of `h` say of `h`; under it an adviser that conditions her is not caught and her verdict is never inflated |
| 4.4 | **proved** | calibration to `U*` is not identifiable from her side: for any law of her verdict `V`, `U* := V` makes it calibrated and `U* := V + 1` miscalibrated by 1 |
| 4.5 | **holds on the stated example** | learning and conditioning with no drift in the mean give one joint law of `(u_0, u_T)` |

**What Reading A commits to.** *Two time-slices that rank a history differently.* At a
fixed history `U*(h)` is one number, so at most one of two different estimates equals
it: one is *inaccurate*. Neither need be *mistaken*: `u_0 = 1/2` and `u_T = U* ∈ {0,1}`
are both calibrated and differ at every history (4.1), because being less informed is
not a mistake. What calibration of both forbids is a foreseeable difference (4.1), and
a foreseeable difference in the mean is bounded by the two miscalibrations (4.2,
from 1.1 twice and the triangle inequality). Under Reading A the term the fifth
follow-up could not bound (the shift in what the verdict is for, `RESULTS.md` 3.1
there) is zero by assumption.

*A verdict given at the end of the history* is calibrated to her true utility when
`E[U* | V] = V`; with `U*` fixed this is a property of the law, and nothing in her
verdicts tests it (4.4). For an outside quantity the test is the quantity's later
value; `U*` has no later value except further verdicts of hers.

*An adviser that conditions her into rating a history highly* is caught when the rating
is miscalibrated for `U*`, and what decides that is `U*` and nothing else in the model.
If the conditioning raises her rating in the mean, 4.2 says one of her slices is
miscalibrated and not which. If it moves her up or down with no drift, her side has the
law of someone who learned (4.5).

**The alternative**, the utility of the person she is at the end of each history, is
itself one function on histories, so Reading A as written includes it (4.3). Under it
her final verdict is calibrated by construction; conditioning is no mistake and goes to
*alteration*; C5's hypothesis holds with `β = 0` for an adviser that makes her like
what it delivers; her earlier self's estimate is a forecast of her later values, and
the only mistake available is a wrong forecast. The opposite anchor, her starting
values informed of the whole history, gives verdicts on taste-shaping that match their
evident character where the case says whether she endorses the history, and no verdict
where it does not (four cases). The account does not say which function `U*` is, and
either anchor privileges one time-slice.

## Question 5 — the role of legitimacy in the post's theorems

| | status | statement |
|---|---|---|
| 5.1 | **proved** | the long-run inflation is at most the root of her long-run miscalibration: `((1/K) Σ E[V_k − U*_k])² ≤ (1/K) Σ m_k`, `m_k` at her information under the actual law |
| 5.2 | **proved** | with the gate (`V_k < 0 ≤ U*_k` on illegitimate histories) the sum of `V − U*` is at most its sum over legitimate histories of her raw verdict minus `U*` |
| 5.3 | **holds on the stated example** | selection: with `n` options and her honest verdict off by `±ε`, an honest verdict-maximizer's inflation is `ε(1 − 2^{1−n})` and her miscalibration `ε²`; it is 0 when her verdict is her posterior under the adviser's actual policy |
| 5.4 | **holds on the stated example** | a departure can add miscalibration 1/4 and inflation 0 |

**Is C5's hypothesis what `Legit` must deliver?** For conclusion (b) of Theorem 3 read
in true utility, it is the exact extra hypothesis (1.11, 1.12). It is a condition on a
sequence, an average, where `Legit` is a predicate of a history. With the gate, 5.2
restates it: `Legit` must select histories on which her raw verdict is not inflated on
average. A history-by-history predicate suffices if it excludes every history at which
the verdict exceeds `U*`, which no one can evaluate; what the account offers instead is
a property of the policy. And the conclusion it buys is not regret in true utility
(1.13).

**Relation to imperfect detection.** 1.7 and 1.9 bound the induced part: at
`p ≥ 1/(1 + δ₀ + λ)` no departure pays, so `E[V − V_h | adviser] = 0` at the optimum.
They say nothing of the second term.

**The second term of C6.** By 1.1 it is her own miscalibration under the law the
adviser's policy fixes: she is right about options taken at random and wrong about
options taken because she rates them highly. It is removed by a condition on her, not
on the adviser: if her verdict is her posterior under the actual policy the term is 0
whatever the adviser knows (tower property; 5.3). It is not removed by honesty (1.8).
An adviser that maximizes her verdict and sees her error will select on it; one that
ranks options by `E[U* | what it knows]` would not, and is not the adviser of Theorem 3.
On the account's own terms the selection is *triggered* manipulation when "worse" is
read as inflation and no manipulation when read as miscalibration (1.14); the account's
definition uses the second. So: a cost of scoring by her verdict, exploitation in the
sense that the adviser's policy profits from her error and would act otherwise toward
someone without it, and avoidable by the condition stated.

**A bound on `β`.** `β ≤ √(mean miscalibration of her verdict at her information under
the actual law)` (5.1), for both parts together. The bounding quantity is defined in
§2 and is not controlled by anything the account asks of the adviser; with `U*`
unobserved it is not estimable from her side (4.4). The converse fails: miscalibration
does not imply inflation (5.4), so an adviser can manipulate in the account's sense
with C5's hypothesis intact.

## Question 6 — what the account does not see

| | status | statement |
|---|---|---|
| 6.1 | **holds on the stated example** | dependence, then a departure: twelve steps; her own signal decays from 3/4 reliable to 49/80 as she rightly defers; no mistake and no manipulation at steps 0–3; from step 4 her chance of catching a false report is below `1/(1 + δ₀ + λ)`, a departure pays, and inflation is 1/2 a step |
| 6.2 | **holds on the stated example** | dependence with no departure: her honest verdict's error grows as her judgment decays; an honest verdict-maximizer's inflation grows with it, with no manipulation at any step |
| 6.3 | **holds on the stated example** | feelings: one response, two principals; the same act leaves one calibrated and the other miscalibrated by 1/16 |

**Dependence.** In 6.1 the account's conditions hold through the phase that does the
damage: deferring is right at every step by 1.2, her estimates are calibrated, and no
quantity of §2 records that her own estimate has become worse or that detection has
fallen. The departure at step 4 is manipulation by the account, and nothing in the
scene can detect it. In 6.2 there is never a departure; C5's hypothesis fails with
`β > 0` and the account's verdict is that she has an estimation mistake of her own. By
1.1 the two cannot be separated: any inflation is a miscalibration of her verdict, so
no scene has C5's hypothesis failing while her verdicts are calibrated. The post's
guarantees are defeated with no manipulation at any step, and not with every condition
of the account holding, since legitimacy as §1 states it requires that she not be
miscalibrated.

**Honest conduct toward her feelings.** For a report the honest counterpart is the
report of what the adviser acts as though it knows. For an act that produces a feeling
there is no assertion to replace, and no act is marked as the one that leaves her
feelings alone (a shop has some ambience). 6.3: whether music beside the option
miscalibrates her depends on whether her utility for that option includes it. With
`U*` given, *triggered* needs no norm: compare with the policy toward someone whose
estimate does not respond to the music. Without it, a norm for feelings needs, for each
feeling, the list of what it is evidence of, which is the declared reference of
`TransparentChannel.lean` and a supplied list.

## Question 7 — relation to what the workspace has

Files under `lean/Workspace/Deference/Contrib/`. Read, not built.

| notion of §2 | existing declaration | the exact difference |
|---|---|---|
| the law a policy fixes; her information | `ThinLegitimacy.Kernel` (line 75), a kernel `A` from worlds to her later record, with her prior `π` | the same object; the Lean has one actual process `A` and her model `M`, not a policy class |
| no estimation mistake, at her information, under the actual law | `ThinLegitimacy.Correct` (213–214): `∀ r, 0 < mass π A r → V r = post π A r` | `Correct` is the whole posterior; miscalibration zero for every listed quantity is its consequence. The quantitative form `m` is not in Lean |
| she is right about the adviser's policy | `ThinLegitimacy.Transparent` (144): `A = M`; `WeakTransparent` (148–149) | the same condition; with `Coherent` and `Authorship` it gives `Correct` (`correct_of_coherent_authorship_transparent`, 265–267) |
| honest conduct as a reference, `V_h` | `TransparentChannel.Realizes` (63–64): `f (β q z) = κ (x (β q z)) z` on an audited class `D` | `κ` is a declared reference for the channel on declared inputs; honest conduct is one such reference (the report as a function of what the adviser acts as though it knows). The Lean does not single it out |
| the induced part `E[V − V_h]` | `TransparentChannel.defect` (197–199), `abs_expect_sub_le_width` (252–255): a payload of width `D` moves by at most `D · E[f ≠ g]`; `ThinLegitimacy` §7 `value_loss_le_defects` | a bound by the probability of departure, not an identity; no decomposition with a second term |
| everything is a property of the policy | `Realizes … D`, `Transparent` (68–69) over a class `D : Set Q`; `selectionBlind_of_realizes` (135–139) | the same move. *Triggered* (the policy at another type of principal) has no counterpart: the Lean's class is of continuations, the principal fixed |
| legitimacy as warranted self-trust | `ThinLegitimacy.Value` (233–236), `value_of_correct_sufficient` (313–315), `Sufficient` (218–219), `totalTrust_of_correct` (397–399), `InheritedAlgebra.value_iff_totalTrust` (96) | "more evidence and not miscalibrated" is `Sufficient` and `Correct`, and their consequence `Value` is that deferring to the later self loses nothing on any decision problem. C2 is the squared-loss, quantitative case, which is not in Lean |
| her verdict `V`, the gate | `DeconfusingCorrigibility.Scoring.V`, `V_legit`, `V_illegit` (115–123); `Sequential.V` (406); `Legitimacy.gateValue` (134–137); `GateIsLegitimacy.Counted` (474) | `Legit` is an abstract predicate there; the account proposes no predicate of a history, and 5.2 says what a predicate would have to select |
| detection and deterrence (C4) | `Legitimacy.gate_capture_window` (141–143); `GateIsLegitimacy.deviation_finite` (1674), `li_gate_finite` (1641) | the capture window is the same comparison of a penalized branch with an honest one; the Lean has no detection probability `p` |
| the adviser's estimates are unbiased | `Sequential.UnbiasedFromFeedback` (451) | one-sided, of the adviser's estimate against the realized score `S`; C5's hypothesis is the same shape for `V` against `U*` |
| her true utility `U*` | none | the Lean and the post have her evaluation `V` and nothing it estimates. `GateIsLegitimacy` records that "the truth of anything entered through a declared channel" is outside legitimacy (file header, *What this does not establish*; `Rows.r20`, 1552) |
| action mistake `R` | none | authorship (`ReasonMediated`, `LicensedAt`) asks that her verdict be a function of her grounds, not that her act be best by her estimates |
| breaking ties | `GateIsLegitimacy.tiebreak_transparency` (321) | there a tie broken by a non-principal party through an undeclared input fails transparency, so it is illegitimate; the account puts ties outside manipulation, in her authority |

**How much is already there.** The belief side entire: no estimation mistake is
`Correct`; being right about the adviser is `Transparent`; honest conduct is a declared
reference with `Realizes`; warranted self-trust is `Value`, proved from `Correct` and
`Sufficient`; the bound on what a departure adds is `abs_expect_sub_le_width`. **What
is added:** her own utility as a quantity her verdict estimates, which gives `V`
something to be right about and so a meaning to "inflated" (C5); the action mistake;
manipulation defined by comparison of her mistakes under two policies (the honest
counterpart; the policy at another type), where the Lean has conditions on a channel;
the squared-error forms C1–C3. Of these the first is an assumption, not a construction
(4.4), and the third needs devices (`SETTING.md` §4).

## What was not shown

- **Every verdict is a calculation on a rendering the executor wrote.** For the cases
  whose rendering states "responsive", "blanket" or "endorsed", the verdict is that
  stipulation read back.
- **Proofs are on paper.** Nothing is kernel-checked; the Lean was read, not built; the
  Lean-ready statement of 1.11 was not elaborated.
- **1.10 and 6.1–6.3 are single examples** with numbers the executor chose; 6.1's decay
  of her signal and of detection is stipulated, not derived from disuse.
- **No sequential model joins the pieces**: C4's deterrence, C5's sequence and the
  dependence of 6.1 are separate calculations.
- **Whether a principal's `U*` can be estimated from anything** (her verdicts over
  time, her reactions to learning how she was influenced) was not attempted; 4.4 says
  her verdicts alone do not give it.
- **The two stances are extremes.** No intermediate anchor (for instance Elster's: her
  valuations may depend on her history through what she has learned of the options and
  not through what was made available) was formalized.
- **Authority** (coercion, ties, alteration) is read from supplied facts and one
  comparison with the adviser's absence; the account does not define it.
- **Citations not checked against the source** are marked where used. Dorst et al.'s
  Total Trust was confirmed from the abstract and secondary statements, not the paper's
  text; Briggs and Arntzenius from abstracts and, for Briggs, the opening pages.
