# Compiler soundness

What `certified` has to mean before the crown jewel's H4 is more than a label.
This is the one item that blocks the **abstract** theorem, and it is why.

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

With a soundness predicate, H4 reads: *for any finite family sound at every state
where its selectors fire*. That is a hypothesis a reader can evaluate, and it makes
`normative` in "normative learning" carry the weight the four delivered clauses
plus the three interfaces give it — no more, and no less.
