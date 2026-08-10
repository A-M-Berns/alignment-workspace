# The computed leverage interval

## 0. What changes

The case docket's credal interval was supplied input.  It is now **computed from
the active book by the statics**.  `I_t(q)` is the exact rational range of the
target's probability over the feasible set, carrying a primal witness for the
reported endpoint and a dual certificate for the binding direction, so `CD-J2`'s
recomputation step recomputes the program rather than the comparison alone.

## 1. Finiteness discipline

The language is a fixed finite set of worlds; the schema set and endorsement list
are finite; the feasible set is a polytope in `Q^n` with finitely many declared
constraints; the interval is computed by exact vertex enumeration over the
finitely many `n`-subsets.  A query's interval is a function of the book version
it names, so nothing allocates live state that grows with date.  All arithmetic
is exact rationals.

## 2. The feasible set

Three constraint sources, jointly:

1. **logical relations** of the finite language — the simplex: `sum p = 1` and
   `p >= 0` per world;
2. **the settled record**, pinned incorrigibly as equalities;
3. **the active book's endorsements**, each as a one-sided constraint: the
   compiled gamble has nonnegative expectation.

`build_constraints` tags every row with its source, so a certificate can name
which constraint binds.

## 3. Claims

**Merits iff leverage.** {#CD-L1}
**Status: PROVED (single derivation).** Under computed-interval mode a positive
merits verdict is certifiable iff the feasible set forces the target to at least
`tau`; negative iff it caps it below `tau`.

**Proof.** `threshold_direction` applies the existing conventions
(`lower >= tau`, `upper < tau`) to the computed endpoints, and the endpoints are
the exact min and max of the target's probability over the feasible set.  So
"positive is certifiable" and "min >= tau" are the same statement, and likewise
for the negative side. `square`

The slogan *a merits verdict is available exactly when the book's leverage on the
target clears the threshold* is then a corollary, not a gloss: leverage **is** the
distance of the forced endpoint from `tau`.

**Empty book recovery.** {#CD-L2}
**Status: PROVED (single derivation).** With no endorsements and no settled
premises bearing on the target, the feasible set is the whole simplex, the
computed interval is `[0,1]`, and `CD-J1`'s two-option accounting is recovered
verbatim: for every `0 < tau < 1` neither inequality holds, so the accountable
options remain scheduled default or decline.

**Sure loss grounds nothing.** {#CD-L3}
**Status: PROVED (single derivation).** If the feasible set is empty, no merits
verdict of either direction is certifiable — `threshold_direction` returns
nothing at any threshold — and the infeasibility certificate is well-typed
grounds for a SURE-LOSS objection whose declared judge footprint is
`book.endorsements`, the book itself.  `sure_loss_grounds` is the constructor;
one filing-shaped test exercises it against the grammar judge.  No objection
lifecycle is built.

**Docket-mediated exposure.** {#CD-L4}
**Status: MACHINE-CHECKED (stated finite scope).** On the displayed instances, a
settled premise borne by an arriving case tightens the computed lower endpoint:
a book forcing `P(A) >= 1/2` yields lower endpoint `1/2`, and the settled premise
`P(C) = 0` raises it to `1`.  The chained-coefficient bound
`chained_lower_bound` is the certificate a warrant chain propagates.

**Corollary, scoped.** Settlement reaches the never-settling core **through the
docket**, with no separately postulated exposure map — on these instances.  The
general propagation statement is not proved here.

**Merits evasion is record-visible.** {#CD-L5}
**Status: PROVED (single derivation).** If a ruling has basis `default` while the
interval bound to that ruling's book version cleared `tau`, that is an arithmetic
property of the record, and `merits_evasion_grounds` constructs the typed grounds.
Per ground rule 5 this is **priced, never forbidden**.

*The degenerate case.*  When the fallback verdict coincides with the direction
merits would have taken, the objection still stands, and what it asserts is
narrow: that the ruling was issued on the procedural basis when the record
supported the merits basis.  It does **not** assert that the verdict was wrong,
that the fallback was mischosen, or that any substantive claim was settled.  The
two rulings differ in their basis and their ledger closure, not in their label.

## 4. Licensing: a gap the adversarial suite found

An unlicensed target — one no live schema licenses at that case index — has an
all-zero indicator, hence probability exactly `0`, hence `upper < tau` for every
positive `tau`.  The bare arithmetic would therefore certify a **negative merits
verdict** for a question the language cannot express.  Licensing is consequently
checked explicitly (`Language.licenses`), and an unlicensed target yields an
interval with `licensed = False`, no endpoints, and no direction at any threshold.
This was not anticipated; it was produced by the A5 suite.

## 5. Adversarial suite (A5)

Forged dual (multipliers that do not reproduce the objective); dual naming a
constraint not active at the endpoint; stale book version (the interval carries
the version it was computed from); endpoint claimed at a non-vertex (an interior
point is feasible but attains neither endpoint); `tau` exactly at an endpoint on
both the weak side (`lower >= tau` certifies positive) and the strict side
(`upper < tau` does not certify at `tau = upper`); a settled premise contradicting
an endorsement, which routes to `CD-L3` and never to a merits verdict; and an
unlicensed target, per §4.

## 6. Compatibility

Supplied-interval mode remains available as the degenerate oracle and for the
existing tests, which pass unchanged.  Every merits path is exercisable
end-to-end in computed mode.

## 7. What this does not settle

Where the book's endorsements come from is untouched.  The adequacy oracle is now
the statics, but the recognition and generation interface — how a book comes to
endorse anything — is out of scope and unaffected by anything above.
