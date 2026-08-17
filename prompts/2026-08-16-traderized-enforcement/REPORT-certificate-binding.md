# Report — certificate binding

Answers to the dispatch's §XXV.

**1. Can I compute a verified certificate for one region and use it for another?**
No. The certificate carries the exact row presentation and `binds` reports the
mismatch. Before the repair, yes — and it was an undercharge, not a mislabel: a
certificate for `p ≥ 0` (aggregate honestly zero) funded `p ≥ ½` for nothing while
the emitted position lost `1/4` at the live world `p = 0`.

**2. Deduplicated for duplicated?** No. Duplicates change the emitted position, so
the presentation key preserves them.

**3. Reuse a later certificate earlier?** No. Live sets shrink — on the displayed
instance a date-5 certificate has aggregate `0` where date-0 has `1/2` — and both
the date and the live-world set are bound.

**4. Permute sentence coordinates?** No. The world vectors are unchanged and what
they mean is not; the support is part of the binding.

**5. Instantiate `verified=True` manually?** No. The initializer requires a
module-private witness and raises `TypeError` otherwise.

**6. Can an asserted bound produce an object claiming LI safety?** No.
`LiveDeficitClaim` is a separate type, refused by both funded entry points. It can
price a request, which is legitimate planning.

**7. What does "funded" mean?** A charge was computed and debited before the
position was constructed.

**8. What does "safety-certified" mean?** Funded, **and** the charge came from a
verified certificate bound to this exact date, support, row presentation and
live-world set — so the certified proposition is about the position that was
actually emitted.

**9. What bound may the holder quote?** The account's `lifetime_ceiling`, not its
initial capital, since bounded replenishment can raise the latter.

**10. Does the ledger identify what force consumed each charge?** Yes.
`OutflowEntry` carries label, cost, date, presentation key, assessment key,
certificate basis, verified status and remaining capital.

**11. Does relaxation ever strengthen force?** No, and it did. Requesting `1/2`
against an account affording `1/10` used to emit `1/10` — five times stronger than
asked for, spending the whole allowance. It now emits the request when affordable
and only ever loosens.

**12. Caps or true reservations?** **Caps.** `Σ_e B_e ≤ B` and `spent_e ≤ B_e`
both hold; capital promised and unspent is still available to unallocated charges.
Sufficient for the safety theorem; the prose says cap. Ring-fencing is reserved to
the maintainer.

**13. Is an automatically satisfied row nonvacuous?** No — the two concepts no
longer share a boolean. `automatically_satisfied` asks the first question by name;
`is_nonvacuous` returns `False` there, because the promise is true and empty.

**14. Is depth monotonicity necessary for safety?** **No**, and the prose said it
was. It is helpful and neither necessary nor sufficient: not sufficient because
non-increasing is not summable, not necessary because pressure or tolerance can
compensate for a depth that rises.

**15. Is the affine example one global endorsement or hand-built stages?** One
global functional, `c = ½B + ¼C + Σ_j 2^-(j+2)A_j` at `r = 3/4`, with each stage
proved to be its restriction. Closed forms `m_t = 3/4 − 2^-(t+2)` and
`D_t = 2^-(t+2)`, and the cost series sums to `9/8` exactly. The finite fixtures
now test the formulas rather than standing in for them.

**16. Does the original statics admit that endorsement type?** Yes by the stated
theory — `NL-SI-A2` and `NL-SI-A5` state endorsements as rows `⟪c,x⟫ ≥ r` with
rational `c`. But **every displayed instance in the source is sentence-shaped**,
so this is an unexercised part of the interface rather than an extension of it.
The distinction is load-bearing, because a sentence-shaped endorsement provably
cannot generate the trajectory.

**17. All-dates theorems versus finite witnesses?**
*All-dates*: the closed forms and the cost series; the horizon proposition; the
account theorem; the positive-floor corollary; the binding invariants.
*Finite witnesses*: every trajectory, and the presentation table's displayed
instances.

## §XIX verdict against the seven conditions

1. safety-bearing force from an unverified claim — **prevented** (type refusal);
2. bound to exact presentation — **yes**;
3. bound to correct support — **yes**;
4. bound to correct date and assessment state — **yes**;
5. spend before emission — **yes**, and `compile_safe_force` orders feasibility,
   certification, charge, debit, position;
6. exhaustion policy cannot bypass the spend — **yes**; quarantine and refusal
   leave the account untouched, relaxation spends what it emits;
7. quoted `B` is the enforced lifetime ceiling — **yes**.

So the verdict stands as **safety implemented at the emission path**, now with
the certificate binding that the phrase was previously outrunning.

## What did not survive this pass

Four things. The unbound certificate (substitution attack, now a regression).
`relax` strengthening an affordable request. "Reservation" as a description of
what allocations do. And "non-increasing depth is necessary", which the full-cost
correction had already falsified and the prose had not caught up with.
