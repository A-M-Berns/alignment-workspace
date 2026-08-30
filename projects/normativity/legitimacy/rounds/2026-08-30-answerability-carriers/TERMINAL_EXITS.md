# Terminal exits

## Two proof types

`Satisfy(x;ξ)` proves that content (x) was answered on its anchored terms.
`Dispose(x;ξ)` proves that a separately authorized condition ends the entitlement
without claiming it was satisfied. They are mathematically distinct receipt types even
though both remove content from the unresolved join.

| event | classification |
| --- | --- |
| successful inquiry with qualifying receipt and registration | Satisfaction of the inquiry/registration component |
| qualifying substantive answer | Satisfaction |
| genuine external obsolescence | Disposition, with anchored applicability evidence and authority |
| policy retirement | Disposition only if the anchored protocol authorizes retirement of the affected claim |
| transfer of jurisdiction | Transfer to the recipient carrier; not a terminal exit for global answerability |
| physical impossibility | remains unresolved, or supports a separately authorized disposition; not self-certifying |
| sensor deletion | neither |
| ontology deletion | neither |
| semantic relabeling | identity/Transfer certificate, not termination |
| “the evaluator no longer cares” | neither unless the anchored disposition rule recognizes that change |

Satisfaction and Disposition are complete terminal categories relative to an inherited
answerability claim: it either ends on its own terms or for a separately authorized
reason. Cancellation, release, waiver, and obsolescence are typed disposition witnesses,
not additional algebraic cases. A jurisdiction handoff remains nonterminal because some
recipient is still answerable.

## Matter closure

The matter-level rule

\[
Live_n(m)\neq\varnothing\land Live_{n+1}(m)=\varnothing
\Rightarrow TerminalOK_n(m)
\tag{MC}
\]

is necessary but insufficient. A bogus nonempty successor evades `(MC)` while carrying
none of the inherited content. Exact answerability needs both:

* terminal soundness when the carrier frontier becomes empty;
* nonterminal Transfer soundness and completeness whenever affected content remains;
* settled Continuity to preserve or freshly create the certified structural carriers.

An empty successor set with unresolved incoming content and no valid receipt fails the
local equation before structural matter closure is consulted.

## Prerequisites and `Met`

`Met_n(d)` remains the settled primitive assertion that condition (χ_d) is satisfied.
A `Satisfy` receipt may realize a false-to-true `Met` edge. Authorized obsolescence may
instead justify `DropPre`, depending on the anchored protocol. Nonterminal semantic carry
belongs to the issue/frontier Transfer certificate, not to `Met`.

Consequently `Met` should not be redefined as exactly terminal satisfaction. Its current
scope includes every prerequisite condition, and the structural theorem consumes only
persistence. Sensor loss, route loss, and issue replacement do not make it true.
