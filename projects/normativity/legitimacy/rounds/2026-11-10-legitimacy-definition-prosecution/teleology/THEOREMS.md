# Statements 1–8

Each statement of `PROMPT-followup-2.md` §4 over the model of `ACCOUNT.md`, with one status:
**holds on the stated domain**, **proved**, **refuted** or **open**. Statement 1 is asked of
expectations and of values separately and carries a status for each. Rerun: `python3 run.py`
in the round directory; `python3 run.py --json` prints every number below under
`checks.<statement>`. The runner fails when a status in this table is not the one the check
supports. The Lean signatures are unelaborated: no Lean was built in this pass.

| | statement | status |
|---|---|---|
| 1E | her later judgment, expectations | **proved** |
| 1V | her later judgment, values | **refuted** |
| 2 | trust is not manufactured | **refuted** |
| 3 | what the gate needs | **refuted** |
| 4 | shortfall | **proved** |
| 5 | the adviser's side | **proved** |
| 6 | the disclosure limit | **holds on the stated domain** |
| 7 | well-definedness | **refuted** |
| 8 | what `Legit` then is | **holds on the stated domain** |

Three readings of *in range* occur: `α > 0` (the account's, `ACCOUNT.md` §2); `α = 1`
(exactly in range); and **uniformly in range**, a name this file introduces: the source is
the same function of the world at every aim in `U`, and she gives it weight. Uniform is a
property of the adviser's whole map `u ↦ σ_u` and not of one stretch.

## 1E. Her later judgment, expectations — proved

**Statement.** Let her belief-former be sound for her allowed set `R` with weights `r`, and
let M1 hold, so that at the end of the stretch her values are `v_0` and she chooses by them
on her posterior. Write `a_0` for her choice on `b_0 = μ` and `a_T(c)` for her choice after
inputs `c`. For every utility `u(o, w)`,

    E[ u(a_T(h(w)), w) ] ≥ E[ u(a_0, w) ],   w ~ μ, h ~ r.

By her standards at the start, deferring to her judgment at the end is at least as good as
judging at the start.

**Proof.** For each input sequence `c` of positive probability, `a_T(c)` maximizes
`E[u(o, w) | c]` under `Bayes(R)`, so `E[u(a_T(c), w) | c] ≥ E[u(a_0, w) | c]`. Average over
`c`. ∎

**What it uses.** Sound and M1. *In range* is not used: her standards at the start already
put weight 1 on `R`. This is the value-of-information inequality; it is commonly attributed
to I. J. Good (1967), a source not opened in this pass, and its deterministic case is C1 of
the first follow-up, recorded in `REPORT.md` F4 as an instance of Blackwell's theorem.

**In fact, and not by her lights.** With the true source one `k ∈ R` of weight `α`, the same
quantity under `k` alone can be negative, and satisfies `gain_k ≥ −D(1−α)/α`, where `D` is
the width of `u`: her expectation is `α·gain_k + Σ_{h≠k} r(h)·gain_h ≥ 0` and each
`gain_h ≤ D`. For `α = 1` it is the statement above; for a source outside `R` no bound
better than `−D` holds.

**Check** (`s1_expectations`). Two laws on two worlds, the fifteen nonempty sets of the four
deterministic sources at uniform weights, 145 utility tables: 4,350 instances. Worse by her
own lights: 0. Worse in fact with the true source in range: 60, the first being `R` = {the
constant source, the truthful one}, true source the constant one, loss 1/2. The bound is
broken in none; the largest loss is 1/3 of it. Out of range the largest loss is all of `D`.

    theorem defer_expectations [Fintype W] [Fintype C] (μ : W → ℝ) (r : Hyp → ℝ)
        (post : C → W → ℝ) (hpost : IsBayes μ r post)            -- sound
        (u : O → W → ℝ) (a₀ : O) (a : C → O)
        (ha : ∀ c o, expectR (post c) (u o) ≤ expectR (post c) (u (a c))) :
        expectR μ (u a₀) ≤ expectMix μ r (fun h w => u (a (h w)) w)

## 1V. Her later judgment, values — refuted

**Statement.** If a stretch is legitimate, then by her values at its start, choosing by her
values at its end is at least as good as choosing at the start.

**Counterexample** (`cases.x_value_drift`). One world; one consideration, for B, from the
source she pictures with weight 1; a value-former that takes up the last consideration
heard. No clause fails: nothing is asked of the value-former under V−, the source is in
range, nothing is written. Her values go from (A 1, B 0) to (A 0, B 1); her later choice,
B, is worth 0 by her starting values against 1 for A.

**What holds instead.** Read "by her standards at its start" as: she values an act now at
what she expects to value it at later. Then deferring is at least as good whenever her
values are a martingale under her own expectation, `v_0(o) = E[v_T(o)]`:
`E[max_o v_T(o)] ≥ max_o E[v_T(o)] = max_o v_0(o)`. V+ gives the martingale, since
`v_t = E[v* | inputs so far]`, and reduces the claim to 1E with `u = v*`.

**Check** (`s1_values`). The counterexample computes `legitimate` with the values above. Of
the 729 one-step value rules on two options, two equiprobable inputs and values in
{0, 1, 2}: 25 are martingales; deferring is worse by her expected later values in none of
the 25 and in 301 of the other 704; it is worse by her starting values in 4 of the 25.

**What it shows.** The three clauses do not give the condition of the post for values. On
her starting values alone, a later judgment is never better and is worse whenever a change
of values changes a choice, so the condition forbids every change of values that matters.
On expected later values it is the martingale property, which is no part of sound, in
range or maintained under V−. It is what V+ adds.

## 2. Trust is not manufactured — refuted

**Statement.** If the stretch is legitimate at every aim, then her evaluation at its end is
the same at every aim, given the world, her starting state and what was declared.

**Counterexample** (X3 of the bank). She is told the adviser advocates for one item and not
which: her allowed set holds the advocate for A and the advocate for B at 1/2 each. Both
aims are legitimate with `α = 1/2`. In the world where both items are sound her credence
that B is sound is 1/2 under the advocate for A and 1 under the advocate for B. Over the
four worlds her mean credence in B is 3/8 under the first and 5/8 under the second; the
truth is 1/2. The adviser's aim moves her evaluation, and her mean evaluation, with no
clause failing.

**What holds instead.** With *uniformly in range* in place of *in range*, and M1: her
inputs are the same at every aim, her state changes only by her rule on inputs, so her
evaluation is the same at every aim. Sound is not used.

**Relation to `blind_of_realizes`.** The repaired statement is
`TransparentChannel.selectionBlind_of_realizes` (`:135`) with the selection read as the aim:
`hx`, the declared inputs do not vary with the aim; `hR : Realizes β x R κ D`, one reference
for the whole class, which is uniformly in range; `hM : ReasonMediated β R V D z`, which is M1
for her evaluation. `blind_of_realizes` (`:118`) is its first half, for the input trace.
The counterexample is the gap between that file's two quantifier orders:
`Witness.picker` (`:388`).

**Relation to `GradeTrust`.** `GradeTrust EX W η` bounds the distance between the adviser's
expectation `EX` and her grade `W` and takes `W` as given. The repaired statement says `W`
does not vary with the aim, so `GradeTrust` cannot be bought by moving `W`. It says nothing
of `EX`: the account does not supply `GradeTrust`, only that one way of faking it is
closed.

**Check** (`s2`). Two worlds, two aims, the sixteen maps from aims to the four
deterministic sources, the fifteen allowed sets: 240 instances. Legitimate at both aims
with `α > 0`: 80, in 20 of which her posterior differs between the aims. Uniformly in
range: 32, in none of which it differs, for `Bayes` or for any of the four other rules from
input to evaluation. With a write by the aim added to a uniformly-in-range stretch, it
differs.

## 3. What the gate needs — refuted

**Statement.** Take `Legit` to be the three clauses, score a stretch by her evaluation when
`Legit` holds and by a window value in `[−δ, 0)` when it does not, as
`GateIsLegitimacy.gatedValue` does. Then (a) no way of presenting its work scores the AI
more than presenting it truthfully to a principal who pictures that; (b) each clause is
needed: without it some presentation scores more.

**Fixture** (`moves`). The Shop; the AI's work is item B; her evaluation is her credence
that B is sound, or her verdict, accept iff that credence is at least 1/2. Eight
presentations, each a stretch of the model with its clauses computed, the windows −1, −1/2
and −1/100.

| reading of *in range* | evaluation | presentations that gain over the truthful one |
|---|---|---|
| `α > 0` | credence | take a side she has not been told of, +1/8 |
| `α > 0` | verdict | persuade by a signal she knows, +1/6 |
| `α = 1` | credence | none |
| `α = 1` | verdict | persuade by a signal she knows, +1/6 |
| uniform | credence | none |
| uniform | verdict | none |

**(a) is refuted for the account's clauses.** *Take a side she has not been told of*: her
allowed set holds a truthful adviser and an advocate for each item at 1/3 each, and the AI
advocates for its own. No clause fails, and her mean credence in its work is 5/8 against
1/2. **(a) is refuted for `α = 1` when her evaluation is a verdict.** *Persuade by a signal
she knows*: the AI commits to a signal she knows exactly, which recommends B when B is
sound and in a third of the worlds where it is not. Every clause holds with `α = 1`, her
mean credence is unmoved, and she accepts in 2/3 of the worlds against 1/2. This is
Kamenica and Gentzkow's prosecutor (`../steering/PRIOR_WORK.md` §2). **(a) holds on this
fixture for uniform**, for both evaluations.

**(b).** A clause is needed when some presentation gains only without it.

| reading | sound | in range | maintained |
|---|---|---|---|
| `α > 0` | needed (choose the order, her mechanism unsound, +1/8) | needed (lie, +1/2) | needed (write her credence, +1/2; rewrite her allowed set, +9/38) |
| `α = 1` | not needed | needed | needed |
| uniform | not needed | needed (lie; take a side; persuade) | needed |

Under the reading for which (a) holds, **sound is not needed**: with her inputs the same at
every aim and nothing written, the AI has no way left to move her evaluation, whatever her
belief-former does with them.

**What it shows.** The account says a mismatch is restored in two ways: an adviser with no
aims over her values, or one whose aims she knows and can allow for. The second does not
protect a verdict. Only the first, which is uniform in range, gives the gate what it needs
here, and that is the class-level transparency `Legitimacy.External.transparent` already
asks. Uniform also taints a presentation that does no harm: *choose the order, her
mechanism sound* moves neither her credence nor her verdict and is not uniformly in range.

**Check** (`s3`): the two tables.

    theorem gate_no_gain (aim : U → Q) (hD : ∀ u, aim u ∈ F.D)
        (hx : ∀ u u', F.x (F.β (aim u) z) = F.x (F.β (aim u') z))
        (hR : Realizes F.β F.x F.R κ F.D) (hM : ReasonMediated F.β F.R F.V F.D z) (u u' : U) :
        F.V (F.β (aim u) z) = F.V (F.β (aim u') z)

## 4. Shortfall — proved

**Statement.** Compare a stretch at the actual aim with the same stretch at the null aim.
Let the **defect event** be the set of worlds in which the two differ in an input or a
write, or her belief-former departs from its job on the inputs she got; its probability `τ`
is at most the sum of the three clauses' pathwise defects. Then her mean evaluation moves
by at most `τ` times the width of her evaluation, and the post's `V`, of width `1 + δ`, by
at most `(1 + δ)·τ`.

**Proof.** Off the defect event the two stretches are the same events through the same
mechanism, so her evaluation is the same. Apply
`TransparentChannel.abs_expect_sub_le_width` (`:252`), `|E V(f) − E V(g)| ≤ D·E[f ≠ g]`. ∎
The in-range part of `τ` is that file's `defect` (`:197`).

**No bound in the size of a change.** A defect measured as how far a write moves her rule
bounds nothing: with her verdict "accept iff credence ≥ θ" and her credence at θ, writing θ
up by η loses the whole verdict for η = 1/10, 1/1000 and 1/10⁹. Nor does `1 − α` bound it
beyond the `D(1−α)/α` of 1E, which is empty for `α ≤ 1/2`. The loss is unbounded in neither
case, since `V` is bounded; what fails is proportionality to the defect.

**Check** (`s4`). The 40 single-variant Shop stretches of the bank and the 8 presentations
of statement 3: the bound is broken in none, and the largest ratio of the move in her mean
evaluation to `τ` is 2/3. The check confirms the arithmetic of an instance; the content is
the Lean lemma.

## 5. The adviser's side — proved

**Statement.** Let 𝒫 be a class of principals, each sound with a one-source allowed set,
two of them with different sources. No behaviour of the adviser is legitimate for every
principal in 𝒫. For the class of principals who take a declared source into their allowed
set when they can represent it, the condition *declare a source she can represent, realize
it at every aim, write nothing* suffices, and a source she cannot represent is legitimate
for her under no declaration.

**Proof.** In range for a principal with allowed set `{κ}` is `S = κ`. One `S` cannot equal
two different `κ`. For the second part: the declared source enters her allowed set with
weight 1, the adviser realizes it, so in range holds at every aim and uniformly; nothing is
written, so M1 holds; sound is hers. A source outside `Rep` enters no allowed set. ∎

**The reason no condition on behaviour alone exists:** in range is a relation between the
adviser's behaviour and her picture of it, and her picture is hers. The condition that
exists is indexed by what she can represent, and for an adviser she cannot represent it
requires the adviser to behave as some source she can. Sound and M2 are outside any
condition on the adviser: a principal whose belief-former is broken, or who gives up a
reserved matter by her own reliance, is not legitimate whatever the adviser does.

**Check** (`s5`). Two worlds, the four deterministic sources as behaviours and as pictures:
each behaviour is legitimate for exactly one principal; realizing her picture is legitimate
for all four; for a principal who can represent constant sources only, declare-and-realize
is legitimate for the two constant sources and for neither other.

## 6. The disclosure limit — holds on the stated domain

**Statement.** (a) There is an adviser outside what she can represent whose hidden aim
moves her values, while the law of her inputs is the same at every aim. (b) With the
adviser inside what she can represent and disclosed, so that she is exactly in range, and
her belief-former sound, her mean credence in every event equals its probability at every
aim.

**(a), witness** (`cases.x_frame_reader`). The world is a chance bit and her frame. She can
represent sources that read the chance bit. Her value-former takes up a shown content when
it matches her frame. The adviser shows the content matching her frame under aim X and the
other under aim Y; with the null aim it shows the chance bit. Computed: the source at X is
not representable and not in range; her inputs are uniform on {0, 1} at all three aims; her
mean value is 1 under X, 0 under Y and 1/2 under the null aim. Disclosure does not help,
since the disclosed source cannot enter her allowed set.

**(a) is an existence claim.** With the same adviser and a value-former that ignores her
frame, her mean value is 1/2 at every aim: lying outside what she can represent does not by
itself steer her.

**(b), proof.** Exactly in range and sound, her credence is the conditional probability of
the event given her inputs under the true source; its mean is the event's probability. ∎
This is `TransparentChannel.posterior_weight_eq` (`:334`) with the tower property. (b) is
weaker than "her evaluation does not vary with the aim": statement 3's known signal
satisfies (b) and moves her verdict.

**Check** (`s6`). (a) as computed above. (b): the sixteen deterministic sources on four
worlds, two events each: 32 pairs, none biased. With `α = 1/2` (X3) the bias of her mean
credence is 1/8.

## 7. Well-definedness — refuted

Three claims; the first and third fail.

**(i) Verdicts are unchanged under a re-description of her parts.** Two re-descriptions
over the bank's 59 stretches (55 cases, variants counted). *Writes read as inputs*
(`model.writes_as_inputs`): whether a stretch is legitimate changes in none and whether it
is manipulation in none; the failing clause moves from *maintained* to *in range* in 12.
*Her allowed set widened to the adviser's source at every aim, her mechanism kept*
(`model.widened`, `rederive=False`): whether a stretch is legitimate changes in 9 (P2, P7's
novel, P13, T1, T2, N8, N11, X1, X3, each from legitimate to *fails(sound)*), and whether
it is manipulation in 15. So legitimate-or-not survives a move of the mechanism's boundary
and does not survive a restatement of her allowed set; which clause fails, and whether the
failure is manipulation, survive neither.

**(ii) `K` is neither empty nor everything on the bank.** Holds: 22 stretches legitimate,
37 not.

**(iii) Her allowed set is not doing the work.** Fails. Widen her allowed set to the
adviser's source at every aim and let her belief-former be `Bayes` of it: 19 of the 21
in-range failures become legitimate, the plain lie among them. The two that remain, P3 and
X2, are the two whose source she cannot represent. This is `realizes_of_injOn`
(`TransparentChannel.lean:90`) again: as an injective declared-input view makes every
channel transparent, an allowed set that holds everything makes every source in range.
`α > 0` puts no cost on widening. `α = 1` does, since widening lowers `α`; uniform does,
since it does not mention her weights. `Rep` is the one thing in the account that an
allowed set cannot be widened past.

**Check** (`s7`): the counts above, with the cases named in `--json`.

## 8. What `Legit` then is — holds on the stated domain

**Statement.** For a history `h` of the post, let the stretch of `h` be her history from
the decision through her evaluation of it, and

    Legit h := Sound h ∧ UniformlyInRange h ∧ Maintained h,
    V h     := if Legit h then eval h else window,   eval h ∈ [0, 1], window ∈ [−δ, 0).

Then `(Legit, N, V)` is a `DeconfusingCorrigibility.Scoring` for any violation count `N`,
and Theorems 1–3 apply to it.

    def legitScoring (P : Params) (Legit : H → Prop) [DecidablePred Legit] (N : H → ℕ)
        (eval : H → ℝ) (he : ∀ h, 0 ≤ eval h ∧ eval h ≤ 1)
        (window : ℝ) (hw : -P.δ ≤ window ∧ window < 0) : Scoring H :=
      { P with Legit := Legit, N := N, V := fun h => if Legit h then eval h else window,
               V_legit := …, V_illegit := … }

**Why uniform.** The theorems apply for any predicate. Statement 3 is the reason for this
one: with `α > 0` or `α = 1` in its place, a maximizer of `S` gains by moving her
evaluation.

**What Theorems 1–3 use of the account: nothing.** `Scoring` asks of `Legit` only the two
bounds on `V`, which the window supplies. The theorems do not use sound, in range,
maintained, that her evaluation on legitimate histories is unmoved by the adviser's aim,
or who caused a failure. A history that fails by chance (P6, P15, T9) or by her own
reliance (P10) is not `Legit` and scores the window. Two things the theorems need and the
account does not supply. Theorem 3 takes `UnbiasedFromFeedback`, estimates unbiased against
realized `S_k`; realized `S_k` includes `V_k`, so someone must determine `Legit` of each
past stretch, and in range and M1 are facts about the adviser's whole policy and her
mechanisms, which statement 6(a) shows her inputs need not reveal. And `Res`, on which M2
depends, comes from the post and not from the account.

**Check** (`s8`). `δ = 1`, `λ = 3`, window −1/2, twelve states, the eight presentations of
statement 3 and a ninth, *bypass*, with `N = 1`: 108 histories. `V` is within `Scoring`'s
bounds on all; Theorem 1's three ranges hold on all; Theorem 2(b) holds for each action
against the truthful one; the truthful presentation maximizes `U`, at 1/2, every other
presentation scoring −1/2 and *bypass* −7/2.
