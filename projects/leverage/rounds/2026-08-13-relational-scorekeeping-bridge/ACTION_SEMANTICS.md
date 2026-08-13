# Action semantics

Eight labels. For each: what it decodes to, what that does to the state, the
normative operation the name claims, and whether the two matched before this
pass.

| label | decoded move | state effect | normative reading | mismatch found | disposition |
|---|---|---|---|---|---|
| `hold` | none | none | decline to move | none | kept |
| `acknowledge` | `assert` the least **exposed** unacknowledged consequence | `ack[H]` gains it | taking up a burden that has been raised | the first pass decoded against *all* unacknowledged consequences, charging latent ones | **gated on exposure** |
| `vindicate` | `vindicate` the least live challenge | `vindications` gains `(H, content)` | discharging a justificatory burden by display | the first pass admitted a committive route, which transmits commitment and settles nothing about title | **restricted to permissive routes** |
| `suspend` | `suspend` the least precluded commitment | `suspensions` gains `(H, content)` | ceasing to rely on a content without retracting it | **decoded to `disavow`** — retraction, not suspension | **new move added** |
| `query` | `query` the least live-challenged content | `exposures` gains `(H, content)` | putting the question publicly | named `reopen`, and `query` was a no-op on state | **move given an effect; label renamed** |
| `defer` | `defer` to the least permitted testimonial source | `deferrals` gains the triple | inheriting entitlement from testimony | none | kept |
| `self-revise` | `revise_committive`, dropping the least rule | `practice[H]` loses it | changing one's own standards | none — it is in the alphabet precisely so the loss can be shown not to fall | kept |
| `disavow` | `disavow` the least acknowledgment | `ack[H]` loses it | retraction | none | kept |

## `suspend` — the one that was wrong

Suspending reliance on a content is not retracting it, and the difference is the
whole point of reified applicability: commitment to `a_rho` may stand while
entitlement to deploy it is defeated. Decoding `suspend` to `disavow` collapsed
exactly that distinction in theorem-facing code.

`suspend` is now its own move. It writes `suspensions`, leaves `ack` alone, and
the commitment stays attributable — `test_suspend_is_not_retraction`. Its effect
on entitlement is that a suspended content neither seeds nor propagates through
the entitlement closure. Its effect on the loss is that a precluded commitment
which has been suspended is no longer charged, **and only where the scorekeeper
reading the score takes the content to be blocked**, so the discount cannot be
self-awarded.

## `query` — real, but weaker than its old name claimed

With exposure gating, `query` writes an exposure and so has a genuine public
effect: it turns a latent consequence into a due burden, and the loss rises.
`test_query_has_a_real_public_effect_where_the_content_is_unraised`.

But the decoder selects it against a **live challenge**, and a challenge has
already exposed what it challenges. So at the position the comparator uses it, the
query changes nothing —
`test_and_is_redundant_on_a_content_a_challenge_already_raised`.

The name `reopen` therefore claimed more than the move does, and the label is now
`query`. The comparator formerly called `reopen_not_disavow` is
`query_not_disavow`, and its force is where it always was: in the substitution
**away from** `disavow`. Erasing the basis makes the challenge lapse; refusing to
erase keeps the commitment in force and the challenge live —
`test_the_comparators_force_is_the_refusal_to_disavow`.

## `vindicate` — not a terminal bit

A vindication is recorded as `(agent, content)` and suppresses the challenge. The
question is whether it survives a later defeater.

It does not survive in the sense that matters: the same display is **refused** once
a premise it rested on loses its title, so a learner cannot pre-emptively bank a
vindication against grounds it is about to lose —
`test_vindication_does_not_survive_the_premises_being_undercut`.

What is *not* implemented is retroactive reopening: a vindication already recorded
before an undercutter arrives stays recorded. Full nonmonotonic adjudication was
judged beyond the minimum this round's claims need, and the gap is named here
rather than papered over.
