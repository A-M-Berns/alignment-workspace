# Compiler soundness

What `certified` has to mean, and — the verdict this pass owed — whether it blocks
the abstract theorem or only a substantive instantiation.

## The verdict

**It does not block the abstract theorem.** The previous pass classified it as the
one abstract blocker; that classification is now corrected.

The theorem quantifies over a `Licensed` relation satisfying stated **interface
discipline**: protocol-legal, causal, loss-blind, non-laundering. Those four are
checkable requirements on any admitted implementation, and with them H4 is a
hypothesis a reader can evaluate — the theorem is a genuine conditional result
about any process supplying such a relation.

**Substantive soundness** — reason-connection, scope-correctness,
defeater-respect — is a property of a *particular* `Licensed`, and belongs to an
instantiation theorem about a relational answerability model. It is the difference
between "this repair carries a valid licence in a practice with these four
properties" and "this practice's licences track the reasons they name".

Why the earlier classification was wrong: it treated "the certificate might be
decoration" as a defect in the theorem, when it is a defect in a *candidate
instantiation*. The abstract theorem never claims its licences are apt; it claims
that if they are admitted under the interface discipline, and have a margin, and
the reason recurs, then the conditional rate vanishes. That conditional is not
vacuous — the loss-blindness clause alone rules out the collapse that would make
it so.

What would make it vacuous is a `Licensed` that admits everything. The
non-laundering and loss-blindness clauses prevent the two degenerate ways of doing
that, and a family admitting every response makes the surgical maps non-surgical
and loses the lower bound anyway.

## The problem, stated exactly

H4 quantifies over a finite class of *certified* surgical repairs. If a
certificate is a string that a record carries, then H4 says only "a finite family
of surgical maps, fixed before play", and the theorem is a regret result about an
arbitrary family. Everything normative in the interpretation is then carried by
the reader's willingness to believe the label.

So `certified` must be a predicate with content.

## The signature

```
compile : PublicNormativeState -> RepairProgram -> Certificate -> Prop
```

with `Certificate` a finite tag and `compile` a decidable predicate of public
scorekeeping status. A repair family is **sound** when every member's certificate
holds at every state where its selector fires, and soundness entails the clauses
below.

## What a soundness theorem should assert

Seven clauses. The first four are already delivered by the relational
scorekeeping substrate and are checkable from the merged model; the last three are
additional interfaces.

| clause | meaning | status |
|---|---|---|
| **protocol-legal** | the replacement decodes to a move the grammar can execute at that state | **delivered** — `apply_move` preconditions |
| **causal** | the certificate reads only the strict-prefix public state | **delivered** — `certify` takes `PublicStatus` |
| **loss-blind** | the certificate is not a function of any loss, saving or future value | **delivered** — schema check on `PublicStatus` |
| **non-laundering** | firing the repair cannot reduce the learner's attributed burden except by discharging it | **delivered** — the merged loss-dependency audit's enumerated edit class |
| **reason-connected** | the certificate's condition is *why* the replacement is apt, not merely co-occurrent | **INTERFACE** — nothing currently distinguishes a certificate that tracks the reason from one that happens to hold alongside it |
| **scope-correct** | the repair falls within the standing and subject matter the certificate is relative to | **INTERFACE** — the merged corrigibility work has scoped authority; it is not wired to certificates |
| **defeater-respecting** | a certificate does not survive a defeater of the consideration it names | **INTERFACE** — entitlement defeat exists in the substrate and is not connected to certificate validity |

**Reason-connection is the hard one**, and it is where the difference between
normative learning and tidy loss reduction actually lives. The competing-reasons
construction makes this concrete: `defeated_applicability` licenses
`acknowledge -> hold` on a story about not compounding an incoherence. Nothing in
the model checks that the story is the reason; only that the condition holds.

## What must not be smuggled in

**The margin.** Soundness is about licence; the margin is about performance. Folding
`ell_t(b) - ell_t(r) >= delta` into compiler soundness would make lawfulness a
function of what the repair earns, which is the exact collapse the whole
architecture exists to avoid — and the fixture's lawful repair with margin `-2` is
kept precisely so the two cannot be quietly identified.

## What this buys the theorem

H4 reads: *for any finite family compiled from a `Licensed` relation meeting the
interface discipline*. That is evaluable, and it makes `normative` in "normative
response-learning" carry exactly the weight the four delivered clauses give it —
no more, and no less. The three substantive clauses are what an instantiation must
add, and naming them precisely is what this document is for.
