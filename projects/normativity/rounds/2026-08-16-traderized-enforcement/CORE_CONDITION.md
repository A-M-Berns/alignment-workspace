# The core condition, compiled

The settlement interface's enforcement clause does not ask for membership. `P1`
asks that a reference be *deep* in the endorsed region: writing `P` for the
post-settlement simplex and `S` for the endorsed region inside it,

    q + theta (P - q)  contained in  S .

The round's first pass reached membership and stopped there, which left the
constrained market maker holding the one demand traderization had not met. It
meets it, and the reason is already in the interface: `NL-SI-A2` proves the
admissible references form a polytope with one explicit rational row per
endorsement,

    (1 - theta) <c, q>  >=  r - theta * m_c ,     m_c = min over vertices of <c, .> .

A rational row is exactly what the constraint-to-trade compiler consumes. So the
depth condition is not a different kind of demand; it is a different row.

## 1. The one precondition: priceability

A credal state's coordinates are worlds; a market's are sentences. An
endorsement `<c, q> >= r` compiles only if its value is a functional of what the
market displays — that is, if `c` is a combination of the indicators of priced
sentences,

    c = sum_s a_s * indicator(s)      so that      <c, q> = sum_s a_s * P(s) .

Call an endorsement satisfying this **priceable**. An unpriceable one names a
constraint whose violation the market cannot see, and no trading strategy can
respond to it — this is a limit on the constraint source, not on the mechanism,
and a differently-built force mechanism reading only prices would face it too.
`core.priceable_coefficients` solves for `a` exactly and returns nothing when
there is no solution; `compile_core_row` then declines rather than enforcing
something else.

## 2. The worked compilation

Take the interface's own displayed instance: three worlds, sentences `A`, `B`,
`C` true at exactly one world each, and the endorsement that the first world
carries probability at least `1/2`.

**Endorsement.** `c` = the indicator of `A` over the plausible worlds, `r = 1/2`.

**Maximal coefficient.** `NL-SI-A5`'s closed form `(M - r)/(M - m)` gives
`(1 - 1/2)/(1 - 0) = 1/2`. `core.maximal_theta` recomputes it from the vertices
and agrees.

**Priceability.** `c` is the indicator of a priced sentence, so `a = e_A`.

**Vertex minimum.** `m_c = min over plausible worlds of <c, w> = 0`.

**The row.** At `theta = 1/4`: `(1 - 1/4) * P(A) >= 1/2 - (1/4) * 0`, that is
`(3/4) P(A) >= 1/2`, that is `P(A) >= 2/3`.

**The trader.** The row joins the simplex rows and the compiler produces the
violation-proportional position on it, which is a legal day-`n` strategy by the
same argument as every other row.

**The check.** Every contract-feasible price at slack zero satisfies the core
condition — verified against the *definition*, walking each shrunk vertex, not
against the row that produced it. At `theta = 1/2`, the maximum the instance
supports, exactly one price survives: `(1, 0, 0)`, which is the reference
`NL-SI-A5` says attains the maximum. `test_core` runs all of it, and separately
confirms that the compiled row and the definition agree pointwise over the
simplex grid at three coefficients.

## 3. What this answers

**Does the core condition have a traderized implementation?** Yes, for priceable
endorsements, with no new machinery: the interface's own polytope is the
compiler's input.

**What intensity does a declared `theta_min` need?** The core rows are rows like
any other, so `ForceDeclaration` applies unchanged: against an ordinary volume
bound `C_t` and market slack `ε_t`, intensity `(ε_t + C_t)/δ_t²` buys row
violations at most `δ_t`. Conformance is to the *depth* condition, at a declared
tolerance, rather than to membership.

**Does this recover the constrained market maker's role?** For `P1`, yes — and
with the existence advantage of `FORCE_INTERFACE.md` §2, which the constrained
version does not have. It does not recover `P2`, `P3`, or the breach stack, and
those were never force.

**What is left at the constitutional layer?** Choosing `theta_min` and
defending it; keeping it satisfiable as the record grows, which is `D1` and which
`NL-SI-A4` proves no finite family of per-date checks decides; declaring the
endorsements; and running the per-date feasibility program that decides whether
any admissible reference exists at all.

**Can `P1` be stated as a demand on a force implementation rather than on a
market maker?** Yes, and that is the reformulation this round proposes: `P1`
becomes a required guarantee of whatever signs the force contract, with the
region being the admissible-reference polytope and the tolerance being declared.
The clause stops naming a mechanism and starts naming an obligation, which is
what lets two implementations be compared at all.

## 4. What it does not answer

Whether the endorsements a normative practice actually produces are priceable.
The instance here is priceable because its endorsement is about a sentence the
market prices; an endorsement about a world-property no priced sentence tracks is
not, and the round exhibits the failure but not its frequency.

Whether the compiled depth condition is what `theta_min` should mean once the
force mechanism, rather than the engine, is the respondent. The interface
certifies `theta_min` of an engine; here it would be certified of a declaration.
That is a change of respondent and it is reserved.
