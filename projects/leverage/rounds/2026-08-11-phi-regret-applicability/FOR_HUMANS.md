# What the learning theorem can see

The closest online-learning theorem has been identified, but the current
repository representation misses one of its decisive hypotheses.

A repair here is a standing rule: given what was on the record before the next
response, and given a candidate response, either leave it alone or replace it
with a response that passes the legality check. The rule may behave differently
as the record grows. Blum and Mansour explicitly allow that kind of rule. Their
algorithm compares the learner with each standing rule while choosing a valid
response each round.

Two seams needed repair. First, the old replay reader could see the response
recorded at the current date. That is fine when auditing a completed transcript,
but an online learner has not chosen that response yet. The new adapter hides it
and gives each hypothetical candidate response to the repair rule explicitly.
Second, different occasions can offer different response sets. Simply pooling
all responses and making unavailable ones expensive is unsound: it can create
fake regret or let the learner choose an impossible response. The correct
encoding maps every pooled label back to an available response. Because every
repair also lands among available responses, the algorithm's stationary choice
puts no probability on unavailable labels. The before-and-after losses are then
exactly the original losses—if the pooled label set stays fixed.

That last condition fails in the implementation. A response carries the ID of
the obligation it closes, so three supposedly common response labels become new
values at every occasion. The pooled set has `3T+5` values by horizon `T`. The
source bound then becomes linear rather than sublinear. The needed repair is an
eight-label action vocabulary with occasion-specific ledger effects derived only
after a label is chosen.

The bridge depends on the deliberately frozen first experiment. Arrivals stay
fixed, guards consult the actual past, and exhausting an account cannot remove
future service. Under those conditions, changing one response changes only that
round's charge. If account exhaustion can change later service, one edit can
change charges for the rest of the run; the previous round's `2T` witness still
controls, and this theorem does not apply. Separate accounts alone do not fix
that.

The applicable bound also costs more than the preparation note predicted. The
source theorem pays for both the number of response labels and the number of
repair rules. It gives order `sqrt(T N log K)`, not `sqrt(T log K)`. The proposed
“exponential weights over nine repairs” baseline is therefore not the audited
algorithm.

Nothing here shows that a learner has low regret. It shows what must be run next
and why that run would be a genuine charge-regret test. The older replay reader
could infer charges from tariffs even though no table was named `charges`; the
new online boundary removes those tariffs before legality code runs. Ordinary
Python callbacks can still capture the original tariff from outside their
arguments, so the finite rule programs need an audit or a restricted rule
language. Low charge regret would mean the learner stops being
systematically outperformed by repairs its own historical reasons licensed. It
would not establish that those reasons are morally correct.
