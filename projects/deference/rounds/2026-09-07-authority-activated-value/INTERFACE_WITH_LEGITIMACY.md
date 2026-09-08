# Interface with the legitimacy machinery

**Status:** `ci-only`.  Every ingredient of `AUTHORITY_ACTIVATED_VALUE.md` mapped to
the existing Integrity / Legitimate Evolution objects, with the one question per row
that matters: is a new primitive needed?

## 1. Ingredient map

| ingredient | existing object | file | new? |
|---|---|---|---|
| occurrence `o_n` | `Occ`, an element of `Boundary.exposed` | `OccurrenceIntegrity.lean` | no |
| evaluation requirement `r_n` | `anchor o_n : Req`, one value of the content type | same | no — a value, not a constructor |
| immutable identity / anchor | `anchor : Occ → Req` fixed for the whole segment; accounts are `Program _ _ (anchor o)` by type | same | no |
| designated slot `s_n` | a component of the anchor value; enforced by `AnswerOK` reading the history position | `Protocol.AnswerOK` | no |
| the actual future session `e_n` | the answer event at `receipt.event`, in `h_m` | `AnswerReceipt` | no |
| value vector `V_n` | the payload of `h_m` at `receipt.event` | history (external data) | no — the history already carries event content |
| adequacy *[corrected]* | `AnswerOK h r w` at `EvalReq` is `SessionOK` at the prefix; `Bind` and authorship are a derived predicate over the receipt's `event` and the history's payload there, since `AnswerOK` is evaluated at the strict prefix and cannot see the event | `Protocol.AnswerOK` + `AnswerReceipt.event` | no — a derived predicate, not a protocol change |
| authority of the answer | `Authority`: fresh event, prior grounds, warrant in force at a strict prefix | `OccurrenceIntegrity.Authority` | no |
| rescheduling / re-representation / representatives / tools | `LocalLaw` with its own `Authority`; `Program.combine` | same | no |
| `C_n` (account part) | `Program.activated := decide (fates = {answered})` | `AuthorityActivation.lean` | a **definition** over existing data |
| `C_n` (lineage part) | `LegitimateForSegment Γ_n` — the existing `Evolution` with `AllStates (OpenAtFor Γ_n)` | `AuthorityActivation.lean` | a **projection** of `LegitimateSegment` |
| `closed ≠ answered` | `Fate.closed`, `Fate.answered` distinct constructors; no theorem identifies them | `OccurrenceIntegrity.lean` | no |
| first answer binds | `livePorts_subst` (only live leaves move) | same; `fates_subst_of_terminal` here | corollary |
| receipts persist | `terminals_le_subst`; `Conservation.receipts` | `LegitimateEvolution.lean` | no |
| propagation is occurrence-local | `Step.propagate` is a `dif` on `o`'s own account | `Step.propagate_congr`, `Segment.propagate_congr` here | corollary |
| epistemic neutrality | `Neutral` = payload-blind process part × total binding | `AuthorityActivation.lean` | an abstract two-field structure, not a protocol field |
| P-authorship | — | — | **EXT**, typed as the meaning of `ProcessCert` |

**Verdict on question 1.**  An authoritative future evaluation *is* a propagated
account of an anchored evaluation occurrence whose terminal fate is a single
authenticated answer receipt.  No `ContinuationWarrant` or `AuthorityLineage`
primitive is needed: the lineage is the account (its `combine` nodes are the
authorized transformations, its leaf is the answer, and every node carries an
`Authority`), and continuation of authority is `LegitimateForSegment` on the
concerns relevant to the occurrence.  The construction is exact: `C_n` is a
`Bool`-valued function of `(O_m.account o_n, the segment, the openness data)`.

## 2. What must be anchored and what may evolve (question 2)

Anchored, because it is the `anchor` value: occurrence identity, principal role,
matter identity, candidate identities `Q_n`, designated slot, output type.  Everything
else — the principal's epistemic state, deliberation, representatives, tools,
informational assistance, and even the slot and the matter's representation — evolves
by authorized `LocalLaw`, recorded in the account, under a warrant in force at a strict
prefix.

**Must `Q_n` be fixed at `n`?**  For the first theorem, yes, in this sense: the
securities `U_{n,a}` are indexed by `a ∈ Q_n` at day `n`, and a security needs a
settlement.  A candidate the future session did not evaluate has no payload and must
void the whole menu (common activation), so a change of the candidate *set* is a
different evaluation, i.e. a fresh occurrence.  What may evolve is the *semantics* of
a candidate identity — what "candidate `a`" refers to at `m` — by an authorized
re-representation law whose `ofChildren` map is the typed semantic transport.  This is
the distinction the prompt asks for: **semantic transport is a `LocalLaw` on the
account; changing the candidate is a new occurrence.**  Whether the transport is
faithful is the faithful-semantic-preservation question and is **EXT** here.

## 3. Adequacy factoring (question 3)

`AUTHORITY_ACTIVATED_VALUE.md` §3.  The factorization
`Cert(V) ≃ ProcessCert × Bind(V)` with `Bind` total gives
`Neutral.certifiable_iff` (**LEAN**): certifiability is payload-independent.  The
countermodel that this excludes is fixture **B**.  The theorem is trivial as
mathematics and is stated because its *negation* is the natural mistake: a
certificate that reads the payload "to check it looks unmanipulated" is a selection
on the payload.

## 4. Where non-capture lives (question 4)

Three contracts, three escape routes:

| contract | escape route it closes | existing home |
|---|---|---|
| Integrity | evasion by revision (rewriting, re-anchoring, self-minted authority) | `Evolution` + `Conservation` |
| Robust Openness | evasion by exclusion (routes removed, standing lost, concern delayed) | `RobustOpenActual` at every state |
| Authorship / process soundness | evasion by substitution of the evaluator's conclusion (the answer is `A`-authored through `P`) | **none** — `ProcessCert`'s meaning, **EXT** |

The wiki's Integrity page glosses Non-Capture as "could the process improperly control
what was *able* to enter, challenge, or evaluate it?"  That covers *who can evaluate*
(standing, routes), which is Robust Openness.  It does not cover *what the evaluator
concludes*, which is authorship.  So "Non-Capture contract" as a name for the Robust
Openness bill is **narrower than the phrase suggests but not wrong**: it names
capture of access, not capture of content.  The September checkpoint's Layer III,
"counterfactual non-capture (open)", is the nearest existing slot for the authorship
contract.

**Recommendation.**  Do not rename.  The evidence supports one sentence on the
Openness page and one on the Legitimacy page saying that Robust Openness is the
access half of non-capture and that the authorship half is a separate external
contract consumed by deference, not a conjunct of legitimacy.  That is the minimal
wiki edit this round makes.

## 5. Global versus occurrence-local legitimacy (question 5)

*[corrected]* `LegitimateForSegment Γ'` below is **scope-local in openness over global
Integrity**: it still carries an `Evolution` propagating every occurrence.  The
occurrence-local object is `OccurrenceLocalIntegrity.LocalLegit`
(`../2026-09-07-reason-mediated-authorship/ACTIVATION_COMPOSITION.md` §4), a projection of
`LegitimateForSegment` that keeps only this occurrence's account trace and the openness
snapshots; an unrelated occurrence's Integrity failure leaves it inhabited
(`Witness.unrelated_integrity_failure`).  The text below is kept as the record of the
first projection step.

The consumer needs, for one occurrence: its propagated account (Integrity) and
openness on the concerns relevant to it.  Both project:

- **Integrity projects exactly.**  `Step.propagate S step account o ho` is a `dif` on
  `o ∈ A.exposed` that reads only `account o`; `Segment.propagate_congr` (**LEAN**)
  shows the propagated account of `o` at the end depends only on `o`'s account at the
  start and the certificate.  Other occurrences' accounts are irrelevant even when
  they share a port, because a replacement is indexed by the port, not by the
  occurrence.
- **Openness projects by monotonicity.**  `OpenAt sem O = ∀ c, …` implies
  `OpenAtFor Γ' sem O = ∀ c ∈ Γ', …` (`OpenAtFor.of_openAt`), and
  `LegitimateSegment.project` (**LEAN**) turns a global certificate into a local one
  with the *same* evolution (`project_evolution` is `rfl`).  Local certificates
  compose (`LegitimateForSegment.trans`) and carry conservation
  (`LegitimateForSegment.conservation`).

So `LegitimateFor(o_n, Γ_n; O_n, O_m)` is exactly the prompt's guess: **the propagated
account lineage of `o_n` plus Robust Openness for `Γ_n` at every state**, and it is a
projection of the existing proof-relevant segment, not a second theory.

**Global legitimacy is harmless as a sufficient condition and brittle as a
hypothesis.**  `Witness.unrelated_failure` (**LEAN**; fixture **H**): a trajectory on
which concern `0` (the evaluation's) is open at every state and concern `1`
(unrelated) is routeless at the middle state.  `LegitimateForSegment {0}` is inhabited
(`Witness.legLocal`); `AllStates (OpenAt semTwo)` is refuted.  Under the global
hypothesis `C_n = 0` and the evaluation is void because of a debt elsewhere.  The
local certificate is the correct consumer hypothesis.  Nothing is duplicated: the
global certificate is the local one at `Γ' = Γ`.

What the local form gives up: the Legitimacy page's "endpoint relation
`Legitimate O₀ O₁`" is scope-free.  A deference consumer that wants the endpoint
relation should take `Nonempty (LegitimateForSegment Γ_n …)`; this round does not
add that alias, since nothing consumes it yet.

## 6. Designated-session semantics (question 6)

| question | answer | evidence |
|---|---|---|
| does the first valid answer bind? | yes: an answer leaf is not live, and only live leaves move | `fates_subst_of_terminal`, `activated_subst` (**LEAN**) |
| exactly one answer slot? | the anchor names one slot; the occurrence has one account; `activated` demands exactly one answer leaf | definition |
| multiple receipts? | a second receipt needs a second live port, which needs a split law; two answer leaves under one occurrence do not activate | `activated` demands `{answered}` exactly; fixture **C** |
| valid rescheduling? | an authorized unary law with a child at `s'`; transparent to activation; visible in the account | `combine_zero_fates` |
| no answer appears? | the leaf is `live`; not activated | `live_not_activated` |
| settlement-backed closure, no answer? | the leaf is `closed`; not activated | `close_not_activated`; `Witness.closed_not_activated` |

The semantics `answered → activated`, `closed → none`, `live → none` follows from the
three-fate calculus with no addition; the only choice made is "exactly one", which
excludes the cherry-picking route that a split-and-answer-twice account would open.

## 7. Operational realizability (question 7)

`AUTHORITY_ACTIVATED_VALUE.md` §7.  The verifier is `decide` on the bundle; soundness
is that the bundle is the Lean term.  Completeness is the availability contract:
that the ecosystem produces a bundle.  It is filed, not proved.

## 8. What would force a new primitive

- **Many-to-one aggregation** (two evaluation occurrences whose joint answer is one
  vector): `LocalLaw` is unary in the parent, recorded as an extension in
  `OccurrenceIntegrity.lean`.  Not needed for one occurrence per menu.
- **A payload-bearing receipt**: if one wanted `V` in the account rather than in the
  history.  Not needed: the event index plus an append-only history is enough, and
  moving the payload into the receipt would duplicate history data.
- **A scope-bearing endpoint relation** on the Legitimacy page.  Not needed until a
  consumer wants the endpoint form.
