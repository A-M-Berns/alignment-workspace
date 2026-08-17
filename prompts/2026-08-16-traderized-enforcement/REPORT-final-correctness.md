# Report — final correctness

## §XVI: is the mechanism research-stable?

1. **Core force theorem stable?** Yes. `lean-proved`, unchanged across five
   passes.
2. **Safety accounting theorem stable?** Yes. The full-cost charge, the horizon
   proposition, and the positive-floor corollary all survived this pass without a
   counterexample.
3. **Safe public API request-bound?** Yes, now on all four identities.
   `compile_safe_force` computes the certificate from the region it enforces;
   `compile_funded_force` takes the live worlds so it can check the fourth.
4. **Semantic boundary explicit?** Yes — `NORMATIVE_SAFETY.md` §7b. Certification
   is relative to the supplied assessment state and does not authenticate it.
5. **A natural safe finite trajectory?** Yes — the sentence-shaped endorsement
   vindicated after two dates, run end to end through the public API.
6. **The derived forever-unvindicated affine trajectory?** Yes — one global
   functional, closed forms `m_t = 3/4 − 2^-(t+2)`, `D_t = 2^-(t+2)`, series
   `9/8`, also run end to end.
7. **Presentation dependence honestly represented?** Yes, and corrected again:
   identity is the **multiset** of exact rows. Permutation invariance is derived;
   duplication and redundancy are real and billed.
8. **Remaining open questions downstream?** Yes.

**Verdict: mechanism/application layer stabilized; remaining work belongs to the
generalized-LI lift and the upstream normative-semantic compiler.**

## What this pass found

**One real hole.** `binds` checked date, support and presentation — three of the
four identities the certificate carries. With all three held fixed, a certificate
computed against the narrow live set `{A = 1}` (aggregate `0`) funded a request
assessed against `{A = 0, A = 1}` (aggregate `1/2`) for nothing. Closed, with the
account verified untouched on rejection.

**One claim of mine that was wrong.** Row order does not change the emitted force.
The position `Σ_j β_j g_j(P)·c_j` and the aggregate `sup_ω Σ_j d_j(ω)` are sums
over rows at uniform intensity, so permutation permutes summands — checked across
all six permutations of a three-row system. The presentation key now canonicalizes
order and keeps multiplicity. My previous report's "both the date and the
live-world set are bound" was also wrong for the lower-level path, and is the same
error as the hole above.

**One evidence upgrade.** The affine trajectory is `derived`, not `witness`: the
closed forms hold at every `t` and the series converges in closed form. Finite
fixtures now test that the implementation agrees with the formulas.

**One scope confirmation.** `NL-SI-A2`'s proof reads *"For an endorsed row
`c . x >= r`"* with `c` unrestricted, and `S` an intersection of half-spaces. So
affine endorsement rows are inside the existing interface — an unexercised part of
it, not a broadening. The claim stands as written.

## The next frontier

Not another API prosecution. In order:

1. **Formalize the live-world Budgeter/TradingFirm lift.** The single conditional
   between bounded enforcement liability and generalized-LI nonexploitability, and
   the only remaining gap in the paper spine.
2. **`PRIORITIES.md` item 39.** Derive `C_t` from the actual normative record.
   That turns the settlement/core instance into the full application, and it is
   the arrow §7b says the force layer cannot supply.
3. **Item 46**, presentation semantics, which is a constitutional question and not
   a blocker for Option A.

Items 40 (necessity), 43 (exact-and-safe compiler), 44 (support removal) and 45
remain open and are genuinely downstream.

## Reserved to the maintainer

Unchanged from the previous passes, plus ring-fencing versus caps. Nothing in this
pass added a reserved item.
