# Paper reconciliation

Where this round's results sit in the generalized-Logical-Induction narrative,
and which of that narrative's intended steps they change.

The one-line answer: the round supplies **channel two** — force — nearly intact,
supplies the **deductive recovery** cleanly, and finds that the paper's intended
**channel one** creates a problem the round cannot yet solve. The generalized
assessment set and the constraint are the same object, so a safety theorem stated
over the generalized set is satisfied by construction for exactly the constraints
whose safety is in question.

## 1. Two models, one algorithm

**Model A**, which is what PR #38 built: the assessment set is `PC(D_t)`, and
`K_t` is an ambient constraint the enforcement trader pushes prices toward.
Safety asks whether enforcement loses too much in a world `D_t` still permits.

**Model B**, which the paper intends: `S_t = Π_t ∩ K_t`, the live worlds
`Ω_t^live` are the `{0,1}` vertices of that slice, and the generalized criterion
assesses exploitation over them.

**They are not different algorithms.** The market maker, the trading firm, the
budgeter and the enforcement trader are the same objects doing the same things in
both; the price sequence is identical. What differs is the **criterion** — which
worlds a trader's net worth is assessed in. That is the whole of the difference,
and it is worth stating plainly because it makes the choice between them an
editorial and conceptual decision rather than a mathematical fork.

**Generalized exploitation (Model B).** A trader `T` exploits `P` relative to a
live-world process `Ω^live` when

    { W( ∑_{i≤n} T_i(P) )  :  n ∈ ℕ,  W ∈ Ω_n^live }

is bounded below and not bounded above. Same shape as `def:exploitation`, with
`PC(D_n)` replaced.

**Which recovers ordinary Logical Induction.** Model A recovers it by making
`K_t` vacuous, which is the wrong direction for a generalization — deduction
stays primitive and the constraint is an add-on. Model B recovers it by making
`K_t` the deductive constraint, which is the right direction: deduction becomes
an instance. §3 proves the recovery.

## 2. The live-world lift

The source construction can be lifted off `PC(D_t)`. Reading the proofs for what
they actually use:

| source object | what it needs of the assessment set |
|---|---|
| `lem:mm` | **nothing** — it quantifies over all worlds, so any assessment set inherits its bound |
| `Budgeter` computability | finite on a finite support, and decidable uniformly in `n` |
| `lem:budgeter`.1 | the same |
| `lem:budgeter`.2 | **nested**: its induction needs a world live at `n` to have been live at `n-1` |
| `lem:budgeter`.3 | only the exploitation definition |
| `lem:tfdom` | `.2` and `.3` |

So the lift hypotheses are exactly three: the live-world process is **nested**,
**effectively presented and finite on finite supports**, and **nonempty**.
`PC(D_t)` is one instance. `test_live_worlds.LiftHypotheses` checks all three on
the deductive instance, including that an inconsistent stage is empty and must
therefore be refused upstream rather than passed to the construction.

This is a genuine lift and it is the paper step most clearly worth keeping. It is
**derived** — read off the source proofs — and not formalized here.

## 3. Deductive recovery

Take the canonical deductive constraint `K_t^D = conv( PC(D_t)|_Φ )`, the
coherence polytope of the stage. Then `S_t = Π_t ∩ K_t^D = K_t^D`, since the
coherence polytope is already propositionally coherent, and the `{0,1}` vertices
of `S_t` are exactly `PC(D_t)|_Φ`.

    Ω_t^live  =  PC(D_t)          and therefore     generalized criterion  =  LIC_D .

Checked at four stages of a three-sentence fragment with a negation relation, on
sets of sizes 4, 2, 2 and 1, so the equality is not holding because every set is
the same set (`test_live_worlds.DeductiveRecovery`). `test-supported` on the
displayed fragment; the general statement is immediate from the definitions once
`K_t^D` is defined as the convex hull, and is **derived**.

**What is recovered is the semantics, not the algorithm's use of `D`.** The
source still consumes `D` inside `Budgeter` and inside the definition of
exploitation. The correct sentence for the paper is therefore:

> traderization generalizes the **operative-force role** associated with
> deduction

and not "traderization replaces the deductive process". The round has said this
since its first pass and nothing here changes it.

## 4. The obstruction, and why two channels

The paper wants a reason finite prices cannot simply be required to satisfy the
constraint. There are now three independent ones, and they are of different
kinds.

1. **Existence.** A market maker additionally required to display `P_t ∈ K_t`
   must satisfy two demands at once, and they can be jointly infeasible — one
   sentence, `K = {P ≤ 1/2}`, an ordinary aggregate buying one share flat. Logical
   Induction's own maker is total; this one is not known to be, and here is not.
2. **Slack.** The actual maker's contract bounds the aggregate's cube maximum
   gain by `2^-n` rather than forcing it to zero, so what it delivers is
   conformance, not projection.
3. **Geometry.** For a region lying in no proper cube face and having empty
   relative interior, no continuous trader achieves exact membership against a
   positive disturbance budget.

So the two-channel split is defensible, and the clean statement is

    what counts as admissible   ≠   how finite prices are pushed toward admissibility.

**Adopt it.** It is the round's best candidate for the paper's central
integration result, and reason 1 is the strongest form of it: the two channels
are not merely convenient to separate, the collapsed version can fail to exist.

## 5. Where Model B breaks, and it is not small

Under Model B the live worlds are derived from `K_t`. The enforcement position is
the violation-weighted combination of `K_t`'s row normals, and the enforcement
inequality says that position is worth at least `∑_j β_j g_j² ≥ 0` **at every
point of `K_t`** — in particular at every live world.

So under Model B the enforcement liability is **identically zero, always**, and
the safety theorem is satisfied by construction.

That is not a strengthening. It is vacuity, and it is worst exactly where the
question matters. The witness: one sentence, `φ` settled true, a source demanding
`p(φ) ≤ 1/2`. Model A assesses the enforcement position in the still-plausible
world `W = 1` and finds it losing `5/8`, with an explicit ordinary trader that
exploits. Model B's live-world set is `{0}` — the settled-true world is not live,
because the constraint says so — and reports liability zero.
`test_live_worlds.DerivedLiveWorldsLaunderTheLiability` computes both.

**A constraint source can therefore discharge its own safety obligation by
declaring the worlds it loses money in inadmissible.** Any condition stated over
`Ω_t^live` alone cannot see this, because the set was chosen by the party the
condition is meant to bind.

## 6. What would fix it, and what is not yet proved

The fix has to anchor the assessment to something the source does not choose.
Three candidates, and only the first is available inside the framework:

**The deductive floor.** Keep `PC(D_t)` — or whatever the settled record forces —
as the *safety* assessment set, while `Ω_t^live` is the *semantic* one. Two sets,
two jobs: the reasoner is answerable to the live worlds, and the enforcement
channel is charged against the deductive floor. The round's existing safety
theorem is then exactly the Model A theorem, unchanged, and the exclusion depth
`d_t(W)` measures how far the semantics has moved from the floor.

**Eventual vindication.** The source may exclude a world only if the deductive
process eventually excludes it too. This bounds the liability, and it makes a
normative constraint a prediction — which costs the normativity line the
performance-independence of `Licensed`. Recorded as available and unattractive.

**Answerability.** Removals are recorded, challengeable and charged. Not a
theorem, and outside this round.

**Status: none of the three is proved to do the job.** The first is the natural
candidate and it is what the round's mathematics already supports, but stating it
as a condition requires saying which floor, and "whatever the settled record
forces" is not yet a defined object in the generalized setting — it is `D` under
another name, which reopens the question the generalization was meant to close.
This is the pass's principal blocker.

## 7. Coverage and Liability, reconstructed

The two names have jobs, and they are not the same job.

**Liability** is a condition on the force channel: the cumulative value of the
enforcement positions over the assessment set is bounded below by `-B`. It is
what the algebraic proof of non-exploitation consumes, and it is proved
sufficient with bound `1 + B`. This one is settled.

**Coverage** is a condition on the semantics: the live-world process may not
delete a realization merely to hide enforcement losses. Its job is **not** to
make the non-exploitation proof go through — the proof needs only bounded
liability. Its job is to make the generalized criterion *mean* something, by
stopping the assessment set from being chosen to satisfy it.

That is the distinction §VII of the dispatch suspected, and this round confirms
it by exhibiting exactly the failure Coverage is supposed to exclude. What it
does not supply is Coverage's statement.

Both names stay provisional and neither is identified with `coverage(Due)`; the
type mismatch recorded in `INTEGRATION_MAP.md` §3 is unchanged.

## 8. One paper or two

**One paper, with the force result as a self-contained module.** The reason is
theorem dependency, not length.

The force results — the compiler, the enforcement inequality, the conformance
modulus, the exactness case analysis, the existence asymmetry — mention no
criterion, no assessment set and no deductive process. They are statements about
a market maker's contract, a region and a price. They can be stated, proved and
read without any of the generalized-LI apparatus, and a reader wanting only
"how do I make a bounded reasoner respect a convex constraint" needs nothing else.

The safety result cannot be lifted out: it composes `lem:mm` and `lem:tfdom` with
a liability hypothesis, and §5 shows the assessment set it is stated over is the
whole difficulty. That coupling is what puts the two in one paper.

So: force as a module with its own statement of what it assumes about the market
maker; the generalized-LI paper consuming it, and carrying the live-world lift,
the recovery theorem, and whatever Coverage turns out to be.

## 9. The seven sentences

1. **The generalized object replacing deduction** is a time-indexed ambient
   admissibility constraint `K_t ⊆ P_t`, presented as a finite rational row
   system, with priceability required for the rows to be visible to trades.
2. **The live worlds** are the `{0,1}` vertices of the coherent admissible slice
   `S_t = Π_t ∩ K_t`.
3. **Finite prices cannot be required to obey it directly** for three reasons:
   the collapsed mechanism can fail to exist; the market maker's contract carries
   slack and gives conformance rather than projection; and exactness is
   geometrically unavailable for some regions.
4. **The enforcement trader** holds the violation-weighted combination of the row
   normals, which makes prices outside the region carry positive cube-maximum
   gain, so the market maker cannot display them beyond a declared tolerance.
5. **The theorem saying it remains a Logical Inductor** is: bounded cumulative
   enforcement liability over the assessment set implies no efficiently
   computable trader exploits, with plausible-net-worth bound `1 + B`.
6. **The additional condition preventing the generalized semantics from
   laundering losses** — *this is the one that fails.* The round can state the
   failure exactly, exhibit it, and name three candidate anchors, but it cannot
   yet state a condition that is both non-vacuous and shown to do the job.
7. **Ordinary deduction falls out** by taking `K_t^D` to be the coherence
   polytope of the stage, whereupon `Ω_t^live = PC(D_t)` and the generalized
   criterion is `LIC_D`.

Six of seven are precise. The sixth is not, and the reason is structural rather
than a gap in effort: the object that defines force and the object that defines
loss are the same object, and nothing inside the generalized framework separates
them.
