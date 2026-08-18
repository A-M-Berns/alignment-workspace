# Final consistency and API-hardening pass

Continue on PR #38. A **final consistency, source-integration and API-hardening
pass**; do not reopen the research architecture unless a new contradiction is
found. The architecture to preserve: `C_t ⊆ Δ(Ω_t)` semantic, `Ω_t^live` by
support, `K_t = π_t(C_t)` price-visible, the two channels reconnecting through
enforcement liability over the live-world process.

**Correct the Model A / Model B algorithm claim.** "Same algorithm, different
criterion" is not generally correct: ordinary Budgeter and TradingFirm are built
relative to `PC(D_t)`, and a generalized construction assessed against
`Ω_t^live` must use a Budgeter parameterized by that process. Distinguish
`TF^D + E` from `TF^live + E`; they need not generate the same aggregate or price
sequence, and coincide in the deductive case because `C^D = Δ(PC(D))` gives
`Ω^live = PC(D)`.

**State the live-world lift as the central generalized-LI theorem**, with exact
hypotheses — nested, nonempty, uniformly effectively presented — and an audit of
which source step consumes which: Budgeter computability, Budgeter safety, the
monotonic step, domination, TradingFirm, the final LIA step. Say precisely what
"effectively presented" means. It may stay `derived`, but its statement must be
unambiguous for a later formalization.

**Repair the preservation theorem to consume the lifted construction**, in two
steps — a generalized TradingFirm dominance theorem, then enforcement
preservation conditional on it — with the proof composition explicit and the
`1 + B` normalization's dependence on the source's budget convention stated. The
living note must say the preservation theorem is conditional on the lift.

**Remove the stale deductive-recovery theorem** derived from `K^D`, add the
projection counterexample as the reason it was false, and leave exactly one
current semantic-recovery theorem.

**Run a safety-claim audit** for four superseded claims: safety holds exactly when
no live world is excluded; persistent exclusion implies exploitation; the
withdrawn `Σ C_t max_j d_j` condition; and the market checking deductive
consistency of sources.

**Clean `PROSECUTION.md`** — attack count, W13's withdrawn condition, W15's
overstatement, the stale "What lands" naming W20 as deepest, and exactness claims
that do not distinguish proved, test-supported and conjectural levels. End with
landed / withdrawn / open.

**Fix the integration map** around the final architecture, replacing "safe
exactly when rows do not exclude live worlds" with bounded cumulative liability
and its sufficient routes, claiming no necessity.

**Fix the wiki exactness story**: settlement pinning on a cube face is enforceable,
the strictly internal lower-dimensional relation is the hard case, and
face-solidity is conjectural.

**Harden `force_api`**: the denominator-4 grid nonemptiness screen is unsound —
`K = {p = 1/3}` is nonempty and misses every grid point — so remove it and require
a documented feasibility precondition or certificate. Keep responsibilities typed.

**Fix the living note's evidence levels**, including the five/six declarations
typo, and expose only stable guarantees.

**Audit the legality claim** against the source's requirements: computability,
continuity, row availability, dependence on declared quantities, whether the
efficient-computability exemption suffices, and whether a source-side wrapper is
needed. State the premise behind "every theorem about the market maker survives".

**Decide the machine-readable home** of traderized force without silently creating
two meanings of "current Normativity interface".

**Make item 39 the exact downstream target**, with acceptance criteria naming the
fixture, the generated constraint, feasibility, the row presentation, the trade,
conformance, the liability calculation, and the settlement/provenance/answerability
statement.

**Rebuild the paper spine and theorem map**, run the search-based stale-claim
audit, add the required regressions, and rewrite the PR body.

Success is twelve statements simultaneously true and uncontradicted by any current
file; if a counterexample breaks one, preserve it and report the exact failed
statement.
