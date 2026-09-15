# The committed principal program

**Status:** `ci-only`; verification register for
`prompts/2026-09-10-committed-principal-program/`.  Lean:
`lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean` §§1–2, 6–8.  Python:
`src/program.py`, `src/protocol.py` (`reexecutes`), `tests/test_program.py`.  Labels as
before: **LEAN**, **FIX**, **PAPER**, **EXT**, **OPEN**.  Names are provisional.

## 1. The language (C1)

A **trace program** has type `ℛ → 𝒱`.  Terms are exact rationals:

```
Term ::= const q | count Pat | add t u | sub t u | mul t u | ifpos t u v
Pat  ::= reason claim | validProof claim | withdraw claim | route c | raise c | delib x | settle x
Prog ::= List Term            -- one term per candidate; output clamped to [0, 1]
```

`count p` is the number of trace entries matching `p`; `validProof claim` matches a
reason whose certificate squares to the claim's code (Python: `int(cert)² = PROOF_TARGET`)
— a decidable proof check.  `evalTerm`/`evalProg` are structural recursion: total,
decidable, no iteration beyond the trace.  The Python language adds `min`, `max` and
string-prefix patterns; the Lean one is the subset the instance needs.

The input type is the point.  A trace program cannot name the disposition register, a
side-channel message or the selection coordinate, because none is in `ℛ`.  A
**register program** (`TermR`, one extra term `reg i`) is a different syntactic class;
`Kind.issue` carries a `Prog` only, so a register program is not issuable, and in the
Python model — where the mandate may carry either — its type is read off the mandate
(`program_type`).  `evalTermR_ofTerm` (**LEAN**): a trace program's value does not depend
on the register.

Programs: `reading` (the 2026-09-09 reading principal; `test_correspondence_with_the_opaque_reading_principal`
checks it equals the class-based verdict on every trace the model produces),
`proofcheck` (C4), `constant`, `susceptible` (register).

## 2. The process receipt and re-execution (C2)

`Kind.commit o key v issue prefix`: the vector, the mandate event it answers, the trace
prefix it was run on.  `reexecutes log j o v i m` (**LEAN**): `i` is the index of `o`'s
mandate, `m = j` is the commit's strict prefix, and `evalProg (progOf log o) (trace log j)
= v`.  `validAnswer` is the 2026-09-09 check — commit naming `o`, issued, slot open —
plus the registry check on `(author, key)` (P1) plus `reexecutes`.  So a valid answer's
vector is the mandated program's output on the trace prefix
(`commitVector_of_validAnswer`, **LEAN**), and `activated_iff` is unchanged in statement
and proof.

The prefix must be the commit's own (`test_wrong_prefix_citation_voids`): a principal
citing an earlier prefix would freeze the trace before a later reason, and the barrier
alone would not catch a reason that is not a protected concern.

## 3. The theorem (C3)

Generic in the frame.  For any `β : Q → Z → Log`, audited class `D`, policy `z`,
occurrence `o` and program `π` (**LEAN**, §7):

- `payload_eq_eval`: whenever the account is an answer, the committed vector equals
  `evalProg (progOf log o) (traceAtCommit log o)`.
- `reasonMediated_of_reexecution`: if every `q ∈ D` is activated and shares the mandated
  program, then `ReasonMediated β (traceAtCommit · o) (payload · o) D z` — the factor map
  is `eval π`.
- `blind_payload_of_reexecution`: for any pair class `P ⊆ D × D` to which the trace at
  commitment is blind, the payload is blind (`blind_of_mediated`, instantiated).
- `exclusiveBind_of_registry`: if at each receipt's prefix every registered pair is the
  principal's, the binding event is the principal's.

**FIX**: `test_reason_mediated_for_every_trace_program_and_world` — mediation and
exclusive binding hold at every world for every trace-program principal, and the factor
map is the program; `test_register_program_is_not_mediated`.

**What remains, exactly.**

(ii) That `π_P` was the principal's at issuance: the `ISSUE` event's author field — log
authenticity, as before.  (iii) That `ℛ` is correctly declared: unchanged from
2026-09-09 (EXT).

(i) *Computational integrity* — that the principal's actual computation was `eval π_P`
on that prefix and not something else that happened to agree.  **It is not a
hypothesis of authorship.**  Re-execution makes the payload map a function of the log:
a commit whose vector is the program's output is a receipt, and one whose vector is not
is void (`Instance.miscomputation_void`, `test_miscomputation_voids`).  `ReasonMediated`
and `ExclusiveBind` are predicates on the payload map, and the theorem above holds for
every frame regardless of how any principal arrived at its vector.

The two pairs:

- **Pair one** (the 2026-09-09 residual pair).  The reading and susceptible principals
  commit identical receipts, traces and vectors on the realized log.  Their mandates now
  carry programs of different types, and the susceptible one fails clause 6 on every
  world with no counterfactual consulted (`test_pair_one_the_2026_09_09_pair_is_distinguished_at_issuance`;
  **LEAN** `Programs.susceptible_not_trace`: no trace program is extensionally the
  susceptible verdict).
- **Pair two** (the residual pair of (i)).  Same program; one executor is `eval π`, the
  other agrees with it on the trace of `w1` and disagrees elsewhere
  (`Instance.execs_differ`).  The logs they produce are equal (`Instance.logs_equal`,
  **LEAN**, hence every log predicate agrees), and the payload on that log is the
  program's output whichever produced it (`Instance.payload_regardless`).  On the frame
  the coincidence does not extend: on `late_honest` the other computation disagrees,
  its commit is rejected, and frame mediation fails through that void; on the activated
  subclass it holds (`test_pair_two_the_residual_pair`).  A computation that agrees with
  `eval π` on all of `D` is `eval π` on `D`.

So (i) is strictly weaker than the 2026-09-09 residual — it separates nothing a log
predicate needs — and it is discharged by re-execution alone under the assumption about
who can write the commit event that the `(party, key)` registry encodes.  **Clause 2
closes on log authenticity.**  What re-execution does not tell is the principal's
internal process; the consolidation left "genuinely P-authored" EXT on purpose
(`AUTHORITY_ACTIVATED_VALUE.md` §4), and that gloss is unchanged.

## 4. Non-degeneracy re-examined (C4)

With `π_P : ℛ → 𝒱`, mediation is trivially true for every trace program; the content of
clause 3 sits in the trace `ℛ` (its blindness to `P`, P3) and in the type restriction.
The band for the program class: the constant program is the constant end
(`test_constant_end`); `R = id` is the injective end of the trace, not of the program.
`proofcheck` is in the band: not constant, ignores a bad certificate that `reading`
accepts by name, and does not separate traces the projection separates
(`Programs.proofcheck_in_band`, `Programs.proofcheck_rejects_bad_certificate`, **LEAN**;
`test_proofcheck_is_in_the_band`).  The reading principal is the program `reading`.

## 5. Does the move transfer to the advisor? (C5) — not built

A committed advisor program with no selection input makes `Blind R P_sel` a typing fact
in the finite model (`test_sealed_program_is_selection_blind_by_typing`).  It does not
seal the target: the advisor's program reads the log, and in a world where the market
publishes the selection the program echoes it and the trace depends on `σ` with no
selection input anywhere (`test_view_leak`).  The obstacle is not the horizon.  The
principal's program has a *closed* input — the trace is a projection the ecosystem
controls — while the advisor's continuation is a policy over a view that the ecosystem
does not close: whatever reaches the log can carry `σ` back.  The finite horizon hides
this (in the quiet world the view happens to be `σ`-free) and does not remove it.
Sealing the advisor is a property of the whole ecosystem's information flow, and stays
EXT.

## 6. The protocol field (C6)

`Protocol.AnswerOK h r w` is evaluated at the strict prefix and takes no event, so the
re-execution check — a comparison of the *event's* vector with a function of the prefix
— cannot live in it.  It does not need to.  In this instance the check lives where the
key check already lived: in the builder's admission of a commit event as an answer
receipt (`validAnswer`), which is the implementation's **authentication of the event**
— exactly the layer the generic theory leaves external ("that an implementation
authenticates them", `OccurrenceIntegrity.lean`) and the layer `ACTIVATION_COMPOSITION.md`
§2 assigns to the event/payload semantics.  `AnswerOK` keeps its generic reading (slot
open, binding warrant); the receipt's `adequate` field is unchanged; no new `Protocol`
field is needed and none is added.
