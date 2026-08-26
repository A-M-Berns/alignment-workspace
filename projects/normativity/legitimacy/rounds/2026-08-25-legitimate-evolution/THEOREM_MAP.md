# What is claimed, and on what

Classes are `AGENTS.md`'s, plus `DEFINITION` for a stipulation and `AXIOM` for a
substantive input the mathematics does not supply. **Nothing here is registered
and nothing is Lean-checked**, so no entry is above `test-supported`.

## Withdrawn

| # | claim | why |
|---|---|---|
| W1 | *The legitimate frontier is the raw lifecycle intersected with a derivability set.* | **Refuted.** `office.rogue_revocation`: an act with no legitimate authority revokes a norm and the norm leaves the frontier. The persistence theorem reported no violation, because its hypothesis was "no exercise acts on it". The previous branch established *persistent until something changes it* |
| W2 | *A recursively derivable licence is what legitimacy of an exercise requires.* | **Insufficient.** `office.unauthorized_scope`: impeccable grounds, impeccable provenance, an authority used outside its domain, admitted. `Permit` is the repair |
| W3 | *Challenge survival is the right modal test.* | **Over-refuses.** `office.persuasion`: an edit that would not have happened but for an argument was scored dependent on it |
| W4 | *Unique issuance is an axiom worth separating from lineage existence.* | **Dissolved.** Occurrence identity makes it free; the two-issuer register has no analogue to build |
| W5 | *Pre-state-blindness is the realization condition.* | **Generalized.** The defect is reading state the record does not **declare**, not reading the pre-state. A schema may read the whole pre-state if the edit declares what it read |
| W6 | *`affected` and `parents` are two fields of the abstract interface.* | **Narrowed.** Grounds are always authorities and what an act disposes constrains nothing, so one field went away with the succession calculus |

## The theorems

| # | claim | class | check |
|---|---|---|---|
| 1 | **G1, finite grounding.** Every legitimate occurrence has a finite tree: leaves in `G`, internal nodes accepted edits, historical index strictly decreasing | DERIVED | `thm_finite_grounding` on eleven constitutions and ten records |
| 2 | **G1 is not an unfolding.** Drop **H3** and an edit grounded in an occurrence nobody issued is applied, and what it issues has no tree | COUNTEREXAMPLE | `test_finite_grounding_fails_when_grounding_is_dropped` |
| 3 | **G2, no self-ratification.** No accepted edit is grounded in what it issues | DERIVED | `thm_no_self_ratification` |
| 4 | **G3, no laundering.** An occurrence a rejected edit proposed never becomes legitimate, however often it is used downstream | DERIVED | `thm_no_laundering`; `office.laundering` |
| 5 | **G3 rests on freshness.** Break **H2** and the theorem's premise is unavailable | COUNTEREXAMPLE | `test_no_laundering_fails_when_freshness_is_dropped` |
| 6 | **Identical content is not poisoned.** A later clean act adopts what a rejected act proposed; two occurrences, one content | FINITE-TEST-SUPPORTED | `office.readoption` |
| 7 | **G4, hidden-state noninterference.** Same declared view, same legitimate state | DERIVED | `thm_noninterference`, with a positive control and two negative pairs |
| 8 | **G4 fails two ways and they are different.** A hidden variable deciding admission; a hidden read changing the effect | COUNTEREXAMPLE | `office.hidden_admission_pair`; `cases.partial_effect_pair` |
| 9 | **G5, persistence until a valid edit disposes it** | DERIVED | `thm_persistence` on every process, including the rogue-revocation attack |
| 10 | **G6, content unconstrained.** Relabelling changes nothing legitimate | DEFINITION abstractly; FINITE-TEST-SUPPORTED on a record | relabelling `C14` |
| 11 | **`Auth` and `Norm` partition one legitimate state** | DEFINITION + FINITE-TEST-SUPPORTED | every process |
| 12 | **Audit contexts retract.** Later evidence invalidates an old edit and everything grounded in what it issued, with no historical rule changing | FINITE-TEST-SUPPORTED | `office.audit_discovery` |
| 13 | **And restore.** A stricter audit context can leave *more* in force, because the edit it invalidates was a repeal. The previous branch met this as the challenge operator's non-monotonicity | FINITE-TEST-SUPPORTED | `office.audit_restores` |
| 14 | **Soundness suffices for recognition and not for enforcement.** A missed valid issuance is conservative; a missed valid repeal leaves an obsolete norm in force | FINITE-TEST-SUPPORTED | `office.repealable`, both directions |

## The realization

| # | claim | class | check |
|---|---|---|---|
| 15 | A Reflective Integrity record proposes an edit sequence satisfying **H1-H4**, from RI §§12.3, 13, 15.2, 17 and the identifier scheme | DERIVED; **argued, not mechanized** | `structural_violations` empty on ten records |
| 16 | It satisfies **H5** where its schemas read only declared inputs, and not otherwise | COUNTEREXAMPLE | `cases.partial_effect_pair` |
| 17 | **H4 is thin in the realization**: `PAuth` carries no domain, so `permit` is the identity except where a `PProto` ground supplies `covers` | DEFINITION, named rather than hidden | `ri_frame` docstring; `office.unauthorized_scope` is where H4 bites |
| 18 | Every Carroll discrimination survives the compression: `C10`, `C11`, `C22`, `C23` refused under audit; `C7b`, `C14`, `C33` accepted | FINITE-TEST-SUPPORTED | `RI_CASES` |
| 19 | A constitution and its gazette satisfy every hypothesis and run every theorem, importing `replay` and nothing else | FINITE-TEST-SUPPORTED, by parsing imports | `test_the_constitution_model_imports_nothing_of_ours_but_replay` |
| 20 | The headline module names no architectural type | FINITE-TEST-SUPPORTED, by reading it | `test_the_headline_module_names_no_architecture` |

## The consumers

| # | claim | class | check |
|---|---|---|---|
| 21 | The deference premise is `o in Auth(L(alpha, t))`; the kernel cannot state it because `W` carries no index | PROPOSAL + SOURCE-REPRODUCTION | `DelegationBridge.lean:52`; `FUTURE_AGENT_SPEC.md` |
| 22 | The enforcement premise is `Norm(L(alpha, t))` and the lifetime it induces | PROPOSAL + FINITE-TEST-SUPPORTED | `cases.force_bearing` |
| 23 | A legitimate norm can be unenforceable; the enforcement API's own exhaustion behaviour says so | SOURCE-REPRODUCTION | `force_api.compile_safe_force` docstring |
| 24 | Entitled, accountable and serviceable remain three independent interfaces | DEFINITION | the process carries no liability field and no holder field |
| 25 | The corrigibility theorem is statable and one hypothesis has no formal object | SOURCE-REPRODUCTION | `ReachableCorrectiveControl.lean:926,1051` |

## Open

| # | statement | class |
|---|---|---|
| 26 | **Recognition transport is an axiom**, and now carries four parameters: base, authorization semantics, threat class, audit context | AXIOM — stated, not hidden |
| 27 | **Coverage is undischarged.** `depends` is supplied from outside; a record's own episodes cover by construction, which is the ceiling on self-certification | OPEN — the largest hole, and it survived every reformulation this round tried |
| 28 | **Bounded-lifetime liability.** Level I bounds the total across all norms and all time; nothing bounds one norm over its own lifetime | OPEN — `PRIORITIES.md` item 69 |
| 29 | Whether `Permit` needs internal structure, or stays an opaque parameter. The interface requires it be consulted and says nothing about what it should say | OPEN |
| 30 | Whether Reflective Integrity should carry jurisdiction on an authority. The abstraction exposes that it does not | OPEN — new, and a defect in the architecture rather than in the interface |
| 31 | Whether `A` can come to be *entitled* to the provenance judgments | OPEN — the epistemic lifting problem |
| 32 | A Lean port of `Occ`, `Edit`, the replay, H1-H6 and G1-G6 | OPEN — deliberately not attempted; now the recommended next step |

## What no entry above claims

That the hypotheses are correct. The substantive normative content sits in
`Permit` and `ProvOK`, which are parameters the interface does not constrain, and
what is proved is structural.

That the theorems are deep. G3 and G5 are short; the ontology did their work, and
the defence is that they were false or missing before, that each fails when its
hypothesis is dropped, and that G1 and G4 are genuine inductions over the edit
history.

That the account layer has been re-examined. It left the headline in the previous
pass and this pass did not put it back or test it further.

That the realization is proved. Entry 15 is a paper argument from Reflective
Integrity's statements, checked on finite records, and those statements are
themselves unregistered.
