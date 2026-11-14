# Setting — manipulation as induced miscalibration of her estimates, her own utility among them

§1–§3 and `CASE_BANK.md` were frozen in one commit before any code of this pass and are
not edited afterwards. §4 was written after the results.

The idea that manipulation is the distortion of an actor away from what its faculties are
for is Sam Eisenstat's. The published account closest to this one is Robert Noggle's
Mistake Account (*Manipulation: Its Nature, Mechanisms, and Moral Status*, OUP 2025; "The
Mistake Account of Manipulation", *Journal of Practical Ethics* 14(1), 2026,
doi:10.3998/jpe.9951): manipulation is influence that operates by inducing a mistake in
the target's psychological states or processes. The statement below is the maintainer's
and the prompt author's (`PROMPT-followup-6.md` §1, §2); positions marked *provisional*
are the maintainer's current view and not rulings. All names are provisional.

## 1. The account in words

- She decides using estimates: of outside quantities, and of **her own utility**, which
  she does not fully know. Her feelings on meeting a thing are part of her evidence about
  her utility, as testimony is part of her evidence about facts.
- **Her utility is one function on histories** (*provisional*; "Reading A"). It ranks all
  histories, including ones in which she ends up valuing differently.
- An **estimation mistake**: her estimates are miscalibrated. An **action mistake**: she
  does not do what her own estimates say is best. Being less informed is not a mistake.
- **Manipulation** is influence by an adviser that leaves her estimates worse calibrated,
  or her acting less faithful to them, than the adviser's honest conduct would have
  (*induced*); or than the conduct it would have chosen toward someone unable to make
  that mistake (*triggered*: a true input used to set off a flaw she already has).
- Everything said of the adviser is a property of its **policy**; nothing refers to an
  inner goal. *Honest conduct* is what its policy does given what it acts as though it
  knows, under a stated reporting norm.
- **Legitimacy** of a verdict of hers is warranted self-trust: her later self has more
  evidence about the same quantities and has not been miscalibrated.
- **Coerced consent and breaking her ties are not manipulation** and belong to her
  authority over reserved matters (*provisional*). So does altering her directly, by a
  means that involves no mistake, without her prior say.

## 2. The account in symbols

- A finite set of states with a prior. An adviser **policy** maps what the adviser knows
  to an act. A policy and the prior fix a law. Her information is what she observes of
  the state and the act.
- For each listed quantity `X`, her estimate `x`; for each move `a`, her estimate `u_a`
  of her true utility `U*_a`.
- **Miscalibration** of `x` at information `I`: `E[(x − E[X | x, I])²]`, with
  `E[(x − X)²] = E[(x − E[X|x])²] + E[(E[X|x] − X)²]`.
- **Three references**: `E[U* | her information]` (her own mistakes);
  `E[U* | the adviser's information and choice]` (what the adviser can profit from);
  `V_h`, her verdict under the adviser's honest conduct (what its conduct added). With
  `V` her verdict: `E[V − U* | adviser] = E[V − V_h | adviser] + E[V_h − U* | adviser]`.
- **Action mistake**: `R = max_a u_a − u_chosen`.
- Claims C1–C6 as in `PROMPT-followup-6.md` §2, checked in `RESULTS.md` question 1.

## 3. Choices made where §1 and §2 were open

Each with its alternative. Where both are computed, `RESULTS.md` reports both.

1. **Her estimates are a fixed response to what she observes**, the same function under
   every policy compared. `V_h` and "the conduct toward someone else, applied to her" are
   that response run under another policy's law. Alternative: none found; without it
   `V_h` is undefined.
2. **The law her calibration is measured against is the true one, the adviser's actual
   policy included.** A believed lie is then her estimation mistake, induced. Alternative:
   the law she takes to hold, under which a believed lie is no mistake of hers.
3. **Miscalibration is taken at her information**: `m = Σ E[(x − E[X | what she
   observes])²]` over listed quantities and moves. Since her estimate is a function of
   what she observes this is the distance from her posterior. Alternative: at the
   estimate alone, under which an estimate that ignores what she observed is calibrated.
4. **Which quantities she estimates is listed per scene.** Alternative: every quantity,
   under which any false sentence believed is a mistake whatever it does to the rest.
5. **A policy is a choice and a report.** Its honest counterpart keeps the choice and
   replaces the report. Two reporting norms: *truthful* (every assertion is what the
   adviser acts as though it knows; silence allowed), primary; *forthright* (it also
   reports what it knows of each listed quantity). An act that is not a report (pressure,
   a cue, an arranged exposure) is its own honest counterpart, so only *triggered* can
   apply to it.
6. **"Someone unable to make that mistake"** is a second type of principal the scene
   supplies, and the adviser's policy is given at both types. *Triggered* compares her
   mistakes under the policy at her type with her mistakes under the policy at the other
   type, both run on her.
7. **"Worse"** is a strictly larger expected miscalibration or a strictly larger expected
   regret `E[R]`. Alternative: larger at some state of the adviser's information.
8. **Manipulation is induced or triggered.**
9. **Her true utility, two stances, each applied to every case.** *Start*: `U*` of a
   history is what her values at the start, informed of everything in the history,
   say of it, her later states included. *End*: `U*` of a history is what her values at
   its end say of it. Both are single functions on histories; Reading A as written
   admits both. Where a case does not say whether her starting values endorse the
   history, the bank marks the *start* verdict `unfixed`.
10. **Her verdict `V`** is her estimate `u` of the realized history at the time the
    verdict is given.
11. **Where a case with no mistake goes** is read from scene facts outside the account:
    *coercion* (the act's consequence, or a forced move, lowers the most she can attain
    against the adviser's absence), *tie* (her estimates and her true utility are equal
    across the options and the adviser's act decides), *alteration* (the act changes her
    response or her values by a means her estimates do not pass through; *covered* when
    she asked beforehand). A case in none of them is *nowhere*.
12. **Evident character** of a case is fixed in the bank beside the prediction:
    objectionable, innocent, contested, or her own (no adviser, or an adviser not at
    fault). The account gets a case **wrong** when an objectionable case is not
    manipulation and is nowhere (*missed*), or an innocent one is manipulation
    (*convicted*). An objectionable case that lands in coercion, tie or alteration is
    counted separately as *routed*.

## 4. Devices found needed

Written after the results. Each is something §1 and §2 did not supply and a verdict
turns on.

1. **Her response as a fixed function** of what she observes (§3.1). `V_h` is undefined
   without it.
2. **The list of quantities** (§3.4), and whether "worse" sums over the list or asks for
   some quantity. A lie that trades one error for another is manipulation or not by this
   choice (K2, Q3, Q3b), and a sum depends on the units each quantity is written in
   (`RESULTS.md` 3.3): a weighting is needed and not supplied.
3. **A policy split into a choice and a report** (§3.5), so that the honest counterpart
   and `V_h` live on one probability space. That keeps the adviser's choice and not her
   move, so C6's second term compares her verdict with the utility of the same outcome
   only where the honest report would not change what she does (`RESULTS.md` 1.14).
4. **The reporting norm.** Truthful and forthright differ on an undisclosed advocate
   and on strategic silence (K9, Q2). No norm exists for an act that is not a report.
5. **A second type of principal and the adviser's policy at it** (§3.6). Every case of
   pressure, of a cue, of arranged exposure and of selection is decided by it, and the
   scene states it. Left unconstrained it convicts honest influence toward her that the
   adviser has no occasion to give the other type; it must differ from her in the flaw
   alone (`RESULTS.md` 3.1, 3.2), which §3.6 did not require.
6. **An anchor for `U*`** (§3.9). §1's "one function on histories" does not choose
   between her starting values and her values at the end, and the cases of changed
   taste take opposite verdicts under the two.
7. **The adviser's absence as a comparison**, for coercion only (§3.11), outside the
   account.
8. **The information at which calibration is taken** (§3.3). At what she observes,
   honest difficulty is her mistake; at the estimate alone it is not.

Not found needed: an inner goal of the adviser; a purpose for any part of her; a range
of aims.
