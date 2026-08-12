# What the new source corpus changed

**Status:** `ci-only`; human register for `prompts/2026-08-12-corpus-reconciliation/`.
The precise version, with paths, is `RECONCILIATION.md` beside this file.

A new bundle of source material for the deference line arrived on 11 August,
superseding the June bundle. It is six further weeks of work: a long audit of the
faithful-acceleration results, a per-result wiki replacing the old monolithic notes,
a closed triangle of implications between the three deference notions, a new
varying-question theorem, an attribution correction made the day the bundle was
packed, and a first sketch of a theory of legitimacy.

This round read it and asked what the workspace should now believe. The short
answer is that the corpus is much stronger than its predecessor on the half of the
program the workspace was not working on, corrects one thing the workspace was
saying, and — unexpectedly — turns out to have proved the same impossibility the
workspace proved, about a different object, without either side knowing.

## The one correction that lands on us

The workspace's ledger recorded "tower ⟹ Value" as an inherited result whose
hypotheses were *named rather than derived* — the ordinary situation for everything
inherited, and not alarming.

The corpus now says the **sharp** version of that arrow is refuted, not merely
unproved. There is a menu — every option worth nothing if you pick it and something
if you don't — on which the tower holds and Value fails. The step that breaks is the
expert vouching for its own pick, and on that menu no amount of vouching helps,
because picking a thing is what makes it worthless. So a restriction on which menus
Value is claimed over is not tidiness; it is required.

Two things stop this from being worse than it is. No Lean is wrong — the broken step
enters as an explicit hypothesis, which is exactly what named-hypothesis discipline
is for. And what we ported is not the sharp version: ours spreads weight over the
menu instead of committing to a single pick.

But — and this is where I first overstated it — that is a family resemblance, not a
match. The corpus's hedged construction spreads weight by a fixed margin; ours lets
the margin shrink away as time goes on. The corpus does report its hedged version as
surviving the punishing menu, and even that comes with caveats: the supporting lemma
is only proved modulo a step the corpus files as open, and the survival claim itself
is a same-session observation, unvetted and not machine-checked.

So the honest position is that we do not know whether our port survives that menu.
Not "probably fine because it's the hedged kind" — genuinely unknown, in both
directions. Settling it is filed as new work, and it should not start from the
assumption that we are safe.

## What is new and stays theirs

The corpus's best result says that if the question you are asking stays fixed, an
accelerator can be trusted no matter how stale its information is — it can never
have seen the human's data at all. The mechanism is nice: a market is never stale
to *itself*, so the trust test can be rebuilt out of the forecaster's own published
number. A companion result extends this to varying questions at the cost of a sparse
schedule.

Both are advances on the forward half of the program — can a slower reasoner safely
use a faster one — which is the half the workspace records as largely inherited and
does not compete on. They are recorded as source results and not adopted. Two
impossibility results in the same area killed themselves under verification, which
the corpus is careful to note is evidence *for* the positive statements, not neutral.

## The attribution correction

A conjecture the corpus had been attributing to a named researcher turns out to have
been formalized with its information structure backwards relative to what he
intended, and he disputes the construal. The corpus's refutations refute its own
construal; his conjecture is untouched and he still expects it to be true.

The workspace never carried this. Nothing here names the conjecture or repeats any
verdict resting on it. That is not luck — the line imported the corpus's Lean and its
audit rather than its narrative, and this repository does not name work after people
— but it is worth knowing that the exposure was checked rather than assumed.

The corpus's postmortem is worth reading on its own terms. Its diagnosis is that
vetting effort went where vetting was tractable (proofs) rather than where the risk
was (claims of the form "this formalizes his idea"), because those don't look like
theorems. The workspace has an analogous category and already labels it — the
Cartesian-frames document classes several of its own statements as "architectural
interpretation" for exactly this reason.

## The part that is actually interesting

The corpus contains a small kernel-checked artifact showing that two systems — one
where an advisor faithfully reports what the human would have concluded, one where
the human simply adopts whatever the advisor says — can produce **identical
records**. Every quote, every piece of feedback, perfect apparent agreement in both.
So no test applied to the record can tell them apart, and whether the advice was
legitimate is not a fact about what was written down.

The workspace proved the same thing about a different object. Two arrangements that
differ in *who is authorized* to act, but produce the same actual behaviour, are the
same object to any valuation that only sees behaviour. Same shape, different latent
variable: theirs is how much influence flowed, ours is who held the authority.

Theirs came first, by about six weeks — early July against our mid-August — and
neither derived the other, which is the only part that matters.

Both lines drew the same moral — the missing thing has to go into the structure, not
be recovered from the record — and then split on what to do about it. The corpus
notices that the advisor, unlike the human, is *able* to compute the counterfactual
"what would you have concluded without me", and proposes making it publish and stake
on that estimate. The workspace went the other way: don't try to detect it, build so
that failing to detect it doesn't matter, because predicting an authorization does
not confer it.

Here the workspace's own results have something to say about theirs. We proved that
certification can never converge to architectural authority — tighten the certificate
and the thing you are trying to reveal shrinks at the same rate. That argument turns
on authority being a fact about what an agent *can* do, invisible to any valuation.
Influence is not like that: it is a difference between two expectations, which is
precisely what a valuation sees. So our negative result does not sink their
certificate program, and the reason it doesn't is the cleanest evidence yet that
legitimacy and authority are genuinely two objects rather than one word.

## Does this get us closer to a corrigibility theorem?

Somewhat, and not in the way one would hope.

The long-standing blocker is that the workspace cannot yet *express* foreclosure —
an AI removing the human's later ability to correct it. Two things are missing: an
operation that reassigns authority at a later time, and an interface more than one
decision deep.

The Cartesian-frames round gave a candidate for what is lost when corrective agency
goes away, but frames have no time in them; that "later" frame is later only because
we said so. The corpus's sealed-sibling construction has the opposite profile: it is
genuinely a family indexed by *when* the advisor's channel was cut, so time is real
in it — but it contains no notion of authority at all, only of belief. And its
"ratchet" — influence that got in before the cut is inside the baseline forever, so
drift off the settling questions is permanent — is the right shape for foreclosure
while being about the wrong quantity.

So we now have two candidate objects failing on complementary axes, which is more
informative than either alone: whatever the right object is, it has to carry time
*and* authority at once, and nothing on the table does. The obvious next thought is
to graft one onto the other — frames indexed by time, or the sealed-deliberation
picture given a notion of who is entitled to act — and nobody has tried it, so
nothing here says it won't work. The ingenuity question stays open, better
specified.

No corrigibility theorem is ready to state, and the corpus does not make one ready.
Its legitimacy material is explicitly conjecture-grade, its author names the two
claims whose failure would sink it, and neither is proved.

## What should we work on next?

**1. Settle whether the punishing menu bites our port.** The corpus supplies an
exact finite menu on which the sharp form of tower ⟹ Value fails. Ours is a soft
form, but not the same soft form the corpus reports as surviving it, so nobody has
checked which side we are on. The check is small, mechanical, and decisive either
way — a necessity witness if it bites, a sharpening if it doesn't. It is the only
place the new corpus creates work that is both cheap and load-bearing, and it is the
difference between a ledger row that is honest and one that is merely not yet known
to be wrong. Filed as item 34, deliberately without a guess about which way it goes.

**2. Test whether legitimacy is a foreclosure notion or only looks like one.** The
sealed-sibling family is the first object anyone has put in front of this program
with a real time index. The question is whether its irreversibility — the ratchet —
survives being asked about *capability* rather than *belief*: can one build a case
where the human's endpoint is preserved and its ability to correct is gone, and the
mirror case? Two witnesses would settle whether these are one object or two, and
either answer moves the foreclosure question, which nothing else currently does.
This is an idea-shaped task, not a work order, and it belongs where it now sits.

**3. Nothing else.** The temptation is to chase the new positive results, and that
is the wrong move: they advance the half of the program the workspace explicitly
does not compete on, they are unvetted, and adopting them would buy narrative rather
than capability. The corpus's own recommendation is the reverse — it names this
repository's formalization as where future verdicts should be discharged. The work
that repays is on this side of that boundary.
