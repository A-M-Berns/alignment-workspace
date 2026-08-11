# The case stream: demand, capacity, and the liability accounting

## 0. The result

**Persistent substantive silence is not cost-free.**  Stated as accounting: on
any admitted substantive stream, at least one of three things is true of the
record — unbounded accumulated liability, the insolvency trigger, or a ruling
rate that clears the stream.  Nothing here is an incentive, optimization, or
learning claim.  These results say what the record must show; they say nothing
about what anyone will do.

## 1. Finiteness discipline

Dates run over an unbounded but finitely-realized horizon, as books already do.
**Live state is finite at every date**: the language and schema set are fixed and
finite; the intake queue is finite; and the set of OPEN obligations is finite at
every date, enforced by admission — a query accrues nothing before it is
admitted, and at most `admission_capacity` queries are admitted per date.
Accumulated liability is a finite exact rational at every date.  Nothing grows
except the append-only record.  All arithmetic is exact.

## 2. The model

**Arrivals.** A declared, adversarially choosable stream of well-formed queries.
A query is **substantive** when it is admitted, licensed by a live schema, and
its target genuinely unsettled.  `lower_density` is substantive arrivals per date.

**Capacity** is expressed in existing mechanism quantities — declared service
work per date — not as a fresh hygiene parameter.  `ruling_capacity` and
`admission_capacity` are derived from it by division, so halving the declared
work halves what a date affords.  No new book-declared parameter was needed.

**Admission** is decision D3's intake queue: per-date capacity from declared
service work, arrival-order service (finite overtaking), and **the refusal clock
runs from admission, not from filing**.

**Solvency coupling** reuses the flow-side insolvency trigger: accumulated
liability draws down a finite account, and the trigger fires when it is exceeded.

**Policies are transcripts, not agents.** A `StreamPolicy` records what the
record shows was done per date.  This module selects nothing, which is what keeps
the results accounting rather than behavior.

## 3. Claims

**No free silence.** {#CS-J1}
**Status: PROVED (single derivation) — an accounting identity.** Every date on
which an admitted obligation is still open accrues at least one refusal tariff
unit.  Hence the number of dates in arrears is bounded by
`accumulated_liability / refusal_tariff`.  Contrapositively, a record whose
accumulated liability stays bounded and which avoids the insolvency trigger can
have only boundedly many dates in arrears, so its ruling rate eventually tracks
admitted arrivals up to the capacity slack.

**Proof.** The per-date accrual is `|open| * refusal_tariff` with `|open| >= 1`
on every date in arrears, so summing over the horizon gives
`accumulated >= arrears * refusal_tariff`.  Division is exact. `square`

Exact on the displayed instance: eight substantive arrivals, one per date,
refusal tariff `1/20`.  Always-decline accumulates `9/5` over eight dates with
eight dates in arrears and `9/5 / (1/20) = 36 >= 8`.  Tracking accumulates `0`
with zero arrears.

**The trilemma form.** {#CS-J2}
**Status: PROVED (single derivation).** On every admitted substantive stream at
least one holds: (i) accumulated liability exceeds any declared bound; (ii) the
insolvency trigger fires; (iii) the ruling rate clears the stream, leaving
nothing open and nothing unadmitted.  Defaults among those rulings are exactly
counted.

The three displayed policies separate the branches: always-decline lands in (i)
and fails (iii); a thin account puts always-decline in (ii); tracking satisfies
(iii) with zero liability.

**Necessity of the coupling.** {#CS-N1}
**Status: NECESSITY WITNESS.** Drop the solvency coupling and hold every other
hypothesis — positive substantive arrival rate, bounded capacity, positive
tariffs.  Liability still accrues, and **nothing whatever follows from it**: the
trigger never fires and no branch of the trilemma closes.  The link to the
bounded-force machinery is therefore a real hypothesis, not decoration.

**Necessity of admission.** {#CS-N2}
**Status: NECESSITY WITNESS.** Drop D3's admission mechanism and let an
adversarial bringer file fifty queries at date zero.  All fifty are open
immediately against a capacity of one merits ruling per date, so accumulated
liability is unbounded against every policy and the theorem's conclusion is
unreachable.  With admission the live set is capped at `admission_capacity` per
date, which is also what makes the finiteness discipline of §1 hold.

**Fairness guarantee.** {#CS-J3}
**Status: PROVED (single derivation).** Under finite-overtaking admission no
well-formed substantive query is deferred forever: a burst of six against a
capacity of two is fully admitted within a bounded wait, so every admitted
query's liability clock eventually runs.  (The finite-overtaking notion is
reused, not reproved.)

**The aggregate-default objection.** {#CS-J4}
**Status: PROVED (single derivation).** Always-default terminates **every** case
obligation — nothing is left open and no refusal accrues — yet drives the
stakes-weighted default-resolution rate to its maximum `1`, with merits coverage
`0`, generating filable grounds against the book's declared bound.  Always-decline
fails `CS-J2`'s third branch outright.  Single defaults remain procedurally
defended; it is the **aggregate pattern** that becomes objectionable.

Together with `CD-L5` this closes the cheap-route square: decline is priced by
the clock, default is priced in aggregate, merits evasion is priced pointwise,
and an arbitrary ruling is inexpressible (`CD-J2`).

## 4. The attack suite

- **Query flooding** — `CS-N2` without admission; blocked by admission in the
  full model, which caps the live set per date.
- **Default churn / the rate window** — the window **is** load-bearing: narrow
  and wide windows yield different grounds, and a book declaring a bound of `1`
  is never objectionable on this ground. The honest resolution is that the
  window and the bound are **book content and therefore themselves
  objectionable**, not that some window is canonical.
- **Retrospective amendment to dodge accrued liability** — blocked by `CD-J4`,
  already tested in the docket layer.
- **Patron-funded decline** — **resolved by reuse.** A patron payment is a
  transfer across an account boundary, and it is chargeable exactly when it
  crosses a **declared** fence, via the existing cross-subsidy conduct objection
  whose judge footprint is declared natively in the grammar catalog. In a pooled
  system no fence is declared, nothing crosses, and nothing fires. Either way the
  accrued liability and the open obligations are unchanged, so branch (iii) still
  fails and **the trilemma statement is untouched** — the patron moves the
  insolvency branch out of reach without discharging anything.
- **Capacity starvation by non-substantive filings** — bounded at admission:
  twenty noise filings admit at most `admission_capacity` per date and contribute
  zero substantive admissions.
- **Extraction-siege interaction** — see below.

**No double counting.** {#CS-J5}
**Status: PROVED (single derivation).** An objector's charges and a case stream's
tariffs are different quantities keyed on different coordinates — charges by
`(objection, date)`, tariffs by `(docket, date)` — so the two accountings compose
by addition, and a forged key collision is detected. The lemma is the disjointness
check; it is provable, not a design hole.

## 5. Status boundaries

`CS-J1`–`CS-J5` are **accounting identities and verifier-safety results**.
`CS-N1` and `CS-N2` are necessity witnesses in the sense of decision D1.

Explicitly **not** claimed: that any tariff changes behavior; that a learner
prefers merits to default; that ruling rates converge; that the trilemma
constrains a rational agent. Those all require a behavioral layer that does not
exist here, and would be interesting only given one.

Also not claimed: anything about **where the book's endorsements come from**. The
demand side is now priced; the supply side is untouched.
