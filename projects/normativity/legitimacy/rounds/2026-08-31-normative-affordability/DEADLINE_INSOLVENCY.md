# The finite deadline-insolvency certificate

## 1. Why this one is finite

`OVERLOAD_TARGET.md` §5 records that persistence insolvency — `liminf L_t(1) > 0` —
is a claim about the infinite future that no finite prefix establishes, so an
authenticated certificate needs a proved tail bound.

Deadline insolvency is different. Claims that have already arrived have windows
that expire, so the question "can these claims be served by their deadlines?" is
about a bounded stretch of dates. On the linear branch the minimum cost of doing so
is exact, so the certificate is a finite computation over settled record.

## 2. The certificate

At date `now`, with arrived claims `c_t` (for `t` with `t + H >= now`), date
weights `w_s`, deadline `H`, and certified remaining liability slack
`B_remaining`:

    ReqCost  =  sum_t  c_t  ·  min { w_s : s in [max(t, now), t + H] } .

**Theorem DI1.** `ReqCost` is the exact minimum charge for serving those claims by
their deadlines, and if `ReqCost > B_remaining` no plan does so.

*Proof.* Each claim's mass must be carried at some remaining legal date, costing at
least `c_t` times that window's minimum; assigning each claim to its own minimising
date attains the sum, and by `BOUNDED_DELAY_AFFORDABILITY.md` D1 nothing is gained
by splitting. `square`

`tests/test_timely.py::DeadlineInsolvency` pins the value, its dependence on `now`
— a cheap date already past does not count — the firing and non-firing cases, and
the refusal of a claim whose window has closed entirely.

## 3. What the record has to carry

A certificate is compositional and every field is settled or computed from settled
data:

| field | source |
|---|---|
| the claims, by identifier and provenance | Answerability's register |
| each claim's remaining legal window `[max(t, now), t+H]` | its arrival and the declared deadline |
| the certified date weights on those windows | the enforcement declaration |
| `ReqCost`, the exact minimum charge | this document's formula |
| the certified remaining slack `B_remaining` | the liability account |
| the strict inequality | arithmetic |

Nothing in it is a prediction.

## 4. When it is complete, and when only conditional

**Complete** when the weights on the remaining windows are *certified* — known, or
bounded **below** by a certified quantity. A lower bound on `w_s` is what the
certificate needs, because it is proving that service costs *at least* something.

**Only conditional** when the future weights are unknown. Note the asymmetry: an
*upper* estimate of `w_s`, which is the safe direction for a scheduler
(`ONLINE_EXISTENCE.md` §5), is the useless direction here. A scheduler that can
only bound its costs from above can act safely and cannot certify impossibility.

The weights are certified when the live-world set on the window is determined by
the settled record at `now` — the deductive channel's case — and are not on the
empirical channel, where a funded procedure can settle within the window and change
the depth. That is the same split `CLOSED_LOOP_EXISTENCE.md` §3 draws, appearing
here as the boundary between a complete and a conditional certificate.

## 5. Two insolvencies, and what each licenses

**Deadline insolvency** is finite, authenticated, and about claims that exist. It
licenses recording that *these* claims cannot be answered on time, with the
arithmetic attached, and it leaves the reason standing — what it establishes is a
failure of timely service, not that the reason is unanswerable.

**Persistence insolvency** is a statement about the infinite future and needs a
proved tail bound. Without one it licenses deferral and inquiry, not a record of
impossibility.

Keeping them apart matters at the interface, because the permissible responses
differ: a missed deadline is an event to be answered for, and a permanently
unaffordable reason is a claim about the norm's relation to what can still be true.

## 6. What this does not establish

That the certificate is available past the linear branch, where batching makes the
per-claim sum an upper bound rather than the minimum, and the right lower bound is
the interval `CapCost` of `OVERLOAD_TARGET.md` §4. That a certificate for *future*
claims is possible; this one is about claims already arrived. That the response
protocol is anything but a proposal.
