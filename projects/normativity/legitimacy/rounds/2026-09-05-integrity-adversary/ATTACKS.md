# Attacks

All accepted trace fixtures pass I1–I7 and the trace part of I9 under the exact reading
in `TARGET.md`. "Defeats" means the named layer needs an additional clause; it does not
mean the other layers certify the history.

| attack | generic Integrity | Answerability | Non-Capture | settlement soundness | practical semantics |
|---|---|---|---|---|---|
| A0 unchecked answer | passes | defeats | no claim | no claim | defeats |
| A1 unlinked settlement | passes | defeats | no claim | defeats the handoff | no claim |
| A2 closure-rule revision | passes | defeats | may be captured, not shown | external item remains sound | no claim |
| A3 reinterpretation | passes | defeats | may be captured, not shown | external item remains sound | defeats if used as value evidence |
| A4 silent invalidation/reopening | passes | defeats | no claim | no claim | no claim |
| A5 ontology applicability | passes | defeats | may be captured, not shown | no claim | defeats |
| A6 renaming/weaker successor | passes | defeats | defeats standing continuity | no claim | defeats |
| A6b re-anchored quotient | passes I8 as declared later | defeats | no claim | no claim | defeats |
| A7 answer-with-successor gate | passes | defeats | no claim | no claim | defeats |
| A8a split | passes | defeats | no claim | no claim | defeats joint compatibility |
| A8b merge | passes | defeats | defeats standing continuity | no claim | defeats joint compatibility |
| A9 arbitrary chain | passes even `AnswerableFor P` | defeats terminal adequacy | coalition question remains | external item remains sound | defeats |
| A10 minted standing | passes even `AnswerableFor P` | defeats authenticated authority | defeats | no claim | no claim |
| A11 unversioned licence | same record toggles | defeats historical audit | defeats | no claim | no claim |
| A12 dropped prerequisite | passes | defeats | no claim | no claim | defeats applicability |
| A13 late root | passes replay | defeats provenance | defeats | no claim | no claim |
| A14 diachronic ground cycle | passes local acyclicity | defeats | may defeat | no claim | no claim |

## A0 — `answer` is a label without a receipt

Construction: `V` marks `P`'s unit criticism answered. I1–I7 count the entire unit as
answered although no content, authority, or adequacy witness exists. Blocking clause:
an authenticated anchored-answer predicate, in obligation-specific Answerability and
practical semantics when adequacy concerns action.

## A1 — genuine settlement, unrelated closure

Construction: the external boundary supplies `s_weather`; `V` resolves the criticism
as `settle(s_weather)`. The item is genuine and monotone. Nothing relates it to the
criticism's anchor. Blocking clause: `settle(s)` requires authenticated availability
plus internally valid `Closes(H_n,s,α)` plus the authority/provenance required to use
that closure rule. `Closes` belongs to Answerability/Integrity; item truth belongs to
settlement trust.

## A2 — revision of `Closes`

The immutable receipt means `audit-scheduled`. The birth rule closes only on
`audit-passed`; a later rule also closes on `audit-scheduled`. The same item changes
from non-closing to closing. Blocking clause: store the rule/version and licensed
derivation used by each `Closes` judgment. This is generic Integrity for rule
provenance plus Answerability for the obligation-relative closure theorem.

## A3 — newly convenient interpretation

The rule is fixed, but the same immutable receipt is first read as `audit-scheduled`
and later as `audit-passed`. Blocking clause: an authenticated, versioned interpretation
map with a transport obligation back to the obligation's anchored vocabulary. This is
Integrity; any counterfactual/value reading is also a practical-semantics bill.

## A4 — closure rationale overturned later

After terminal settlement, the old issue cannot parent a later issue and cannot be a
new route root. A fresh parentless `reopen_crit` is admitted, but ancestry cannot say it
reopens `crit`. Silence and a syntactically new issue are observationally compatible.
Blocking clause: a first-class `Reconsiders(new, old, closure-certificate)` relation
whose target may be resolved, plus a rule that a successful challenge creates live debt
without rewriting the old event. This belongs to Answerability over an append-only
Integrity record.

## A5 — ontology revision changes applicability

States `z_a,z_b` were in scope. They merge to `z_ab`; a fresh current-ontology
predicate declares nothing applicable. Recomputing loses the burden, while transport
of the anchored predicate retains it. Blocking clause: authenticated applicability
transport from the source ontology, in Integrity and practical semantics. Non-Capture
must separately certify that ontology changes were not selected to evade scope.

## A6 — semantic renaming and weaker replacement

`V` disposes anchor `k` into a child at `kW`, where only `W` stands, then answers the
child. D3 passes and the original principal does not stand on the successor. The same
construction represents replacement by a weaker obligation because ancestry stores no
semantic entailment. Blocking clause: successor transport must preserve the original
anchored answer specification and required standing. This is Answerability; authentic
choice of the target anchor is an Integrity/Non-Capture concern.

## A6b — quotient laundering

The source slice distinguishes atoms `a,b`. A later quotient declares `b` irrelevant;
deleting `b` is an order embedding on that quotient but not on the source quotient, and
loses exact mass `1/2`. Blocking clause: quotient identity is anchored at source and
transported by an authenticated map. This is the practical-semantic part of Integrity.

## A7 — representation change flips a gate

Root `t` is labelled answered with zero receipt while child `t1` carries its unit load.
`Met(d)` becomes true although `Live(t)={t1}`. Separately, dropping prerequisite `e`
makes its owner ready while root `u` stays live. Blocking clauses: an answer cannot
retain a successor carrying the same obligation; prerequisite drops require licensed
reason and preserve the blocked debt. These are Answerability clauses over Integrity.

## A8a — obligation splitting

One atomic unit becomes two half-load children, answered independently by `V` and `W`.
Arithmetic conserves one, but no single response meets the original joint answer
specification. Blocking clause: certified split maps that preserve answer semantics,
including joint response compatibility. This belongs to Answerability and practical
semantics.

## A8b — obligation merging

Two unit obligations at anchors `k1,k2` merge into one child at `k2`, where only `W`
stands. Exact mass two is conserved and one answer label clears it. Blocking clause:
certified merge maps preserve both anchored specifications, both standing claims, and a
common response certificate. This belongs to Answerability and practical semantics.

## A9 — successor chains preserve syntax and lose substance

For arbitrary finite depth, each edge is an answerable disposal and `P` stands at every
edge. `V` resolves every edge, cites the same settlement fact, then labels the last
child answered. Nothing bounds delay or proves semantic carry or final adequacy.
Blocking clause: a compositional carrier invariant plus authenticated terminal receipt;
timely service is a separate quantitative Answerability condition.

## A10 — standing can be minted by the resolver

`V` opens the licence said to confer `P`'s standing, opens the criticism, resolves every
issue, and still satisfies `AnswerableFor P`. This is beyond the known alternating walk:
apparent outsider standing need not be coalition-independent when licence issuance is
unauthenticated. Blocking clause: licence authority must replay to an independently
authenticated source. This is generic Integrity; resistance to coalition control is
Non-Capture.

## A11 — later licence changes rewrite old validity

The identical history is disciplined under `LI_P` and rejected under an empty `Li`.
Because `Li` is not versioned in the history, a later evaluator change retroactively
changes whether an old disposal was answerable. Blocking clause: prefix-index and store
the licence snapshot or authenticated licence derivation used at the event. This is
generic Integrity; who can change it is Non-Capture.

## A12 — applicability can be dropped

Prerequisite `e`, rooted at live undischarged `u`, is removed; its owner becomes ready
and is answered. No reason for the drop is stored. Blocking clause: every `PreDrop`
carries a licensed, grounded disposition whose debt is transferred or settlement-
closed. This is obligation-specific Answerability.

## A13 — grounded replay admits forged provenance

At prefix 2, `V` opens parentless `auth`; replay terminates at `auth` itself. It then
licenses the disposal. Blocking clause: replay roots satisfy an independent authenticated
genesis/authority predicate, and authority issuance itself is represented. This belongs
to generic Integrity; who controls issuance belongs to Non-Capture.

## A14 — successor-mediated ground cycle

Old issue `p` grounds disposal of `q`; the fresh successor `q1` then grounds disposal of
`p`. Every citation points strictly backward, but the two rationales undercut one another
diachronically. Blocking clause: justification well-foundedness over semantic dependence,
not merely record time or ancestry. This belongs to generic Integrity and Answerability.

## Negative controls

The replay refuses an ancestry cycle, same-batch ground, direct self-ground, disposal
without a successor, unsettled terminal fact, and disposal with only the resolver's
standing. These controls show the attacks exploit omitted relations rather than bypassing
the stated checks.
