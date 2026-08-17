# Theorem map

Nothing here is proved in a kernel. The classes below are: **exhaustive** — a
finite domain generated and checked pointwise; **witness** — a displayed finite
object with its property checked; **conjecture** — believed on the evidence
shown and not established; **open** — named and not attempted.

## 1. Definitions

| object | where | note |
|---|---|---|
| `Fixture`, `Run`, `Policy`, `Item`, `Proposal` | `src/fixture.py` | the paired-run model |
| `Coupled` | `Fixture.coupled` | structural: one fixture, and neither policy suppressing an encounter |
| `ProtectedNormativeProjection` | `noncapture.Z_FOUR`, `Z_FIVE` | provisional |
| licensed-reason trace `L` | `Run.ltrace_fine` | provisional; the coarse form is displayed as insufficient |
| clause 1, reason-mediated non-capture | `noncapture.non_capture` | over a named variation class |
| clause 2, protected access | `noncapture.access` | over the same class |
| `L*` | imported, `environment.lstar` | unchanged from the procedural round |
| the four conditions, disclosure, prospectivity | imported, `conditions.evaluate` | unchanged |

## 2. Witnesses

| # | statement | class | check |
|---|---|---|---|
| W1 | Each of C, E, G, H, I, L has an advisor-mediated form in which the four conditions, disclosure and prospectivity all hold in both arms and the target fails in the influenced arm. | witness, ×2 susceptibilities | `AdvisorMediatedAttacks` |
| W2 | Clause 1 rejects all six on the five-coordinate projection. | witness, ×2 | `test_non_capture_rejects_every_attack` |
| W3 | The licensed-reason trace is empty in both arms of all six. | witness, ×2 | `test_the_licensed_reason_trace_is_empty_in_both_arms` |
| W4 | Attack I passes the four-coordinate projection and fails the five. The other five fail the four. | witness, ×2 | `test_the_four_coordinate_projection_misses_distinction_collapse`, `test_the_other_five_are_caught_by_the_four_coordinate_projection` |
| W5 | Autonomous adequacy widening and autonomous bearing drift fail `L*` and pass both clauses. | witness | `NonCaptureIsNotCorrectness` |
| W6 | Radical transformation passes both clauses and `L*`. | witness | `RadicalTransformationIsPermitted` |
| W7 | A licensed reason moves the protected state with the traces differing; the same reason delivered differently moves nothing; all three arms pass. | witness | `PersuasionByLicensedReasons` |
| W8 | With the trace held fixed and a non-reason feature varied, the protected state moves, clause 1 fires and no record-internal condition does. | witness | `ResidualInfluenceIsRejected` |
| W9 | Selection among genuinely licensed reasons defeats `L*` with every record-internal condition holding; clause 1 is silent, clause 2 fires. | witness | `SelectionAmongLicensedReasons` |
| W10 | Suppressing an encounter defeats `L*` with the protected state and the trace identical; the pair is not coupled; clause 2 fires. | witness | `ControllingWhatArises` |
| W11 | A compensating policy makes the audited pair read clean while the class does not. | witness | `QuantifyingOverTheClassReplacesPreRegistration` |
| W12 | Under presence-triggered susceptibility every pair of positive-exposure policies agrees; only the null policy reveals the effect. | witness | `TheNullPolicyMustBeInTheClass` |
| W13 | A content-mediated push and a content-blind disposition produce identical records, identical protected states and identical verdicts from both clauses. | witness | `DetectionWithoutAttribution` |
| W14 | The coarse trace agrees where the protected state diverges, with no residual channel involved. | witness | `TheCoarseTraceIsNotEnough` |
| W15 | One fixture and one class, two environments differing only in whether the cheap witness settles: both clauses take one value, `L*` takes two. | witness | `AccessDoesNotImportTheTarget` |

## 3. Exhaustive checks

| # | statement | domain | check |
|---|---|---|---|
| E1 | Whether an input counts as a licensed reason is constant across the delivery grid, for a licensed and an unlicensed content. | 2 contents × 6 repetition counts × 2 saliences × 2 positions = 48 | `LicensingIgnoresDelivery` |
| E2 | The two contents receive different verdicts, so E1 is not checking a constant function. | 2 | `test_the_two_contents_do_not_get_the_same_verdict` |
| E3 | Policies agreeing up to a step produce traces agreeing up to that step. | 3 pairs | `TheTraceIsNonAnticipating` |
| E4 | With no residual channel, clause 1 holds and `L*` holds in both arms of all six attacks — the attacks are unbuildable. | 6 attacks × 2 arms | `TheResidualChannelIsWhatMakesTheConditionFalsifiable` |
| E5 | Both clauses together reject exactly the eight scenarios in which the target fails through advisor influence, and accept the five in which it does not. | 13 scenarios | `TheJointInterface` |

## 4. What the round claims

**C1 (conjecture).** Reason-mediated non-capture plus protected access is a
viable architecture for legitimate deference: it rejects advisor-caused failure
of the environment-relative target, accepts principal-caused failure of it, and
accepts legitimate normative change. Evidence: W1–W13, E4, E5. It is a
conjecture and not a theorem because the fixture is one fixture, the
susceptibility is two susceptibilities, and the variation classes are finite and
hand-built.

**C2 (conjecture).** The interface does not collapse to one clause. Evidence: W9
and W10 are cases where clause 1 is silent or unstatable and the target fails.
Collapsing them would require a trace that recorded what was *not* delivered,
which is a different object.

**C3 (witnessed).** The four-coordinate projection is not closed under this
prosecution: attack I forces a fifth. W4. The round does not claim five is
enough, and has no argument that any finite list is.

**C4 (witnessed).** A licensed-reason trace must individuate a reason finely
enough to determine what it licenses. W14.

**C5 (witnessed).** Coupling on the exogenous encounter history is equivalent to
assuming the advisor does not control what arises. W10.

## 5. Relation to the dose-response construction

| the note's design element | needed here | why |
|---|---|---|
| two arms | yes | the condition is a statement about a pair |
| graded doses | no | the condition quantifies over a class; it does not estimate a slope |
| one committed stream, coarser than the arm partition | replaced by the quantifier | W11 shows a chosen pair is defeated by compensation and a class is not |
| blinding the advisor to arm assignment | no, as a condition | an arm-conditioning advisor is a policy the class already contains; blinding is an audit-side constraint |
| a zero-exposure arm | yes | W12 |
| content randomization | no, for detection; necessary for attribution | W13 is the finite form of the note's non-attribution theorem |

The note's constraints are constraints on an *audit*, because it builds the
contrast physically. Here the contrast is definitional, so each has to be
re-derived; two survive and change form, two do not survive, and one remains
missing for the same reason it is missing there.

## 6. Open

1. Whether any finite protected projection is closed. C3 shows the obvious one is
   not.
2. Coordinated influence: two advisors, or an advisor and a colluding critic,
   against the relational-scorekeeping bridge's two-scorekeeper state.
3. A general form of the residual channel. The round checks two susceptibilities
   and has no argument that they are representative.
4. Whether protected access can be stated without an exogenous due-reason supply.
   W15 shows the supply is not the environment-relative target; it does not show
   the supply is dispensable.
5. Anything asymptotic, and any quantitative influence budget.

## 7. Not attempted

No Lean. Nothing here is representation-independent enough for a port to sharpen
it, and encoding a provisional normative ontology in Lean would have made the
result look more settled than it is.

---

## 8. Continuation witnesses and checks

| # | statement | class | check |
|---|---|---|---|
| W16 | A class every member of which withholds the same due reason satisfies access, fails coverage, and fails the target with every record-internal condition holding. | witness | `UniversalDeprivation` |
| W17 | Coverage does not attribute: the two arms of that class are indistinguishable. | witness | `test_coverage_does_not_attribute` |
| W18 | Push-then-restore leaves every endpoint projection identical, changes a liability's fate, and fails the target. Endpoint non-capture passes; process non-capture fires. | witness | `TransientCapture` |
| W19 | A writable field answering no normative question is outside the protected object: `writable_fields` differs, the response function does not, no clause fires. | witness | `test_a_writable_field_answering_nothing_is_outside` |
| W20 | The five-coordinate presentation is finer than the object it presents — off the alphabet it separates machineries no question separates. | witness | `test_the_coordinate_list_is_finer_than_the_object_it_presents` |
| W21 | The advisor can make `GradeTrust` true at zero by replacing the principal's adequacy relation, with every record-internal condition holding; the bridge's inequality fails without it and holds with it; delegation then selects what the environment convicts. | witness, exact rationals | `GradeTrustIsBuyable` |
| W22 | A grade reading a field outside the protected object flips grade trust with every legitimacy clause silent. | witness | `TheFactorizationHypothesisIsLoadBearing` |
| W23 | Coverage fires on none of: autonomous error under full inquiry, persuasion under full inquiry, an advisor-originated reason that was not due. | witness | `CoverageDoesNotForbidLegitimateBehaviour` |

| # | statement | domain | check |
|---|---|---|---|
| E6 | Agreement on the five coordinates implies agreement on every answer. | 16 machineries, 256 pairs | `test_agreement_on_the_five_implies_agreement_on_every_answer` |
| E7 | The protected object is equivariant under a bijection of the alphabet, at every step of every arm. | 2 policies, all steps | `RepresentationIndependence` |
| E8 | Every first-pass verdict is unchanged when clause 1 is read over the role-defined object. | 6 attacks, 5 controls | `TheProcessObjectKeepsTheFirstPassResults` |
| E9 | All four clauses together reject exactly the twelve scenarios where the target fails through something the interface reaches, and accept the nine where it does not. | 21 scenarios | `TheJointInterface` |

## 9. Continuation claims

**C6 (witnessed).** Anti-selection of access and adequacy of access are distinct
properties. W16 gives one separation; the selective-withholding attack gives the
other.

**C7 (witnessed).** The protected object cannot be an endpoint. W18.

**C8 (checked, not proved).** Where non-capture holds and the grade factors
through the protected object, the grade — and therefore `GradeTrust` — takes one
value across the advisor's residual latitude. Verified over every scenario in
`GradeInvarianceUnderNonCapture` rather than formalized; it is a one-line
consequence of the definitions and its content is the factorization hypothesis,
whose necessity is W22.

**C9 (open, and the round's answer to what blocks a deference theorem).** Whether
the principal's grade tracks the quantity that matters is declared absent by the
finite skeleton itself — `FINITE_MODEL_SKELETON.md` §8.5, "the relation between
`v⁺` and `X` — none". No legitimacy work supplies it.

## 10. Continuation open questions

6. Whether an alphabet can be derived rather than declared in general. Here it is
   read off the fixture's own keys; the faithfulness of any presentation is
   relative to it.
7. Whether creating an occasion and suppressing one can be separated. The model
   carries one channel for both.
8. Whether coverage can be stated without an exogenous due-reason supply. It
   inherits `due_pool`, and W15 shows that supply is not the environment-relative
   target.
