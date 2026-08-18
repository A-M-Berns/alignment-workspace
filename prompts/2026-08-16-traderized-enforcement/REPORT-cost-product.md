# Report — the cost product

Answers to the dispatch's §XXVI.

**1. What exact quantity does a date of normative force cost?**
`q_t = (ε_t + C_t^{vol}) · D_t / δ_t`, with `D_t = sup_{ω ∈ Ω_t^live} Σ_j d_{t,j}(ω)`.
Three factors, none privileged.

**2. Is the cost a property of `K_t` or of its row presentation?**
Of the presentation. `k` duplicate rows scale position and charge by `k`;
rescaling by `λ` scales them by `λ²`; a redundant non-duplicate row changes the
emitted force while leaving the admissible set fixed.

**3. If presentation-dependent, is that intentional?**
It is now a declared choice — **Option A**, presentation is part of the force
request — rather than an unnoticed property. `PRIORITIES.md` item 46 holds the
three alternatives.

**4. Are scalar rescaling and duplication neutral under the installed compiler?**
Rescaling yes, at a matched actual conformance target; it is a genuine
reparametrization. Duplication no: at matched conformance the position and
realized liability agree and the charge does not, because the certificate sums the
same deficit once per copy. The previous claim of neutrality for both tested a
compiler retuned by `1/k`, which the installed `ForceDeclaration` does not do.

**5. What is a mathematically invariant notion of meaningful force?**
`δ_t ≤ α·V_max` with `V_max = r − Σ_i min(c_i, 0)`, the largest violation the row
can attain in the cube. `δ ≤ 1` is not invariant and is no longer used as one.

**6. Does positive exclusion depth itself need to decay?**
**No.** This was the round's error. Depth fixed at `1/2` with tolerance fixed at
`1`, against pressure `2^-t`, sums to under `1` forever.

**7. What combinations make indefinite force affordable?**
Any that make the product summable: depth decays, pressure decays, tolerance
loosens, or a mixture. The account runs out only when depth and pressure are both
floored and the tolerance is capped, and then after at most `B·δ̄/(cd)` dates.

**8. Can the public safe-force API emit force without paying?**
No. `compile_funded_force` pays before constructing the position; the unaffordable
path returns `None` or raises. `compile_force` remains available, promises
conformance only, and returns a different type carrying no charge.

**9. What certifies that the deficit bound covers all live worlds?**
`LiveDeficitCertificate`. `by_enumeration` walks the live worlds and is the only
constructor producing `verified = True`; `asserted` requires a stated reason and
is carried through marked unverified.

**10. Sharp or rowwise aggregate?**
Sharp, `sup_ω Σ_j`, by default. The rowwise `Σ_j sup_ω` is also computed and is
larger — a clean factor of two on two rows pinning one price from opposite sides,
which cannot be violated together at any world.

**11. What does an endorsement allocation reserve, and what does it limit?**
Both admission and spending. It consumes global capital at admission, so
admissions are finitely many; and `spend` refuses a labelled charge that would
take an endorsement past its own reservation. Choice 2 of the dispatch's §XI,
implemented whole rather than half.

**12. Can capital be replenished?**
Only against a lifetime ceiling declared at construction, which defaults to the
initial capital, so the default account refuses. There is no `add_capital`. The
bound a caller may quote is the ceiling.

**13. What happens when force is unaffordable?**
The caller's declared policy: refuse, quarantine, or relax to the tightest
affordable tolerance. Weakening the declared core minimum remains ineffective.

**14. Do the motivating statics exhibit a safe never-vindicated trajectory?**
**Yes, but not from every endorsement shape.** Sentence-indicator endorsements
hold their depth and then jump to zero in one step — no gradual closure is
available from them. An affine priceable endorsement whose demand sits at the
value settlement approaches is never vindicated, admits a positive core minimum at
every date, has halving depth, and converges. So the answer is affirmative with a
substantive restriction on the kind of normative content covered.

**15. Which safety statements are theorems and which are witnesses?**
Theorems: the per-date liability ceiling; the horizon-quantifier proposition
(§13a, now written out); the account theorem; the positive-floor corollary; the
presentation table; the sharp/rowwise inequality. Witnesses: every trajectory —
the vindicated one, the abstract stipulated one, the statics-generated one, the
persistent-depth/decaying-pressure one, the bounded-liability failure, and the
fresh-endorsement laundering.

## §XXVII status

**Safety implemented at the emission path.** The intended call path cannot emit a
safety-certified position without computing or asserting the live-world charge,
paying the global account, and respecting the exhaustion behaviour. What is *not*
claimed: that bounded liability is necessary; that the charge is tight; that
presentation-independent cost exists; and any statement that unresolved normative
disagreement must decay.

The earned statement is the summability of the certified cost:

    Σ_t (ε_t + C_t^{vol})·D_t/δ_t < ∞ .

## §XXV — the paper verdict is unchanged

Nothing in this pass touched the generalized construction. Generalized-LI paper:
available conditional on formalizing the live-world Budgeter/TradingFirm lift.
Traderized-force mechanism: conformance established; safety preservation
established conditional on bounded liability. Normativity application: the outflow
protocol succeeds, with the cost product rather than depth decay as its content.

## What did not survive this pass

Three claims of the eighth pass: the depth-only impossibility theorem; invariance
of the certificate under duplication; and `δ ≤ 1` as a presentation-independent
notion of meaningful force. All three are withdrawn in place with their
counterexamples kept as regressions.
