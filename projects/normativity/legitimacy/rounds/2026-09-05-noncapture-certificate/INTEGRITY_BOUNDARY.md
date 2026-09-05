# Integrity and settlement boundary

Status: proposed typing, supported by exact separating fixtures.

Integrity constrains a realized history: authenticated entries, preserved identities,
recorded provenance, replayable standing, faithful transfer, and settlement-backed
terminal discharge. Non-Capture compares that history with externally supplied
alternatives and asks whether coverage and protected standing survive the declared
interventions. A trajectory can record every admitted item faithfully while controlling
which challenges can be admitted; it then has Integrity and fails Non-Capture.

The settlement engine supplies authenticated items through a domain-relative trusted
boundary. The internal reasoner supplies `Closes(H,s,alpha)`: under the rules and reasons
in force at `H`, settlement item `s` suffices to close obligation `alpha`. Integrity
requires the item, closure judgment, authority, and provenance to be recorded without
laundering. Neither the settlement engine nor a settlement item decides `Closes`.

The phrase “settlement cannot be delayed or suppressed” has three typings:

- generation and delivery independent of the assessed process: an ambient settlement-
  interface assumption;
- faithful recording after delivery: Integrity;
- persistence of access under interventions: Non-Capture only when the application puts
  that access inside `Adeq` or names settlement-channel interventions in `J`.

There is no standalone settlement-timing clause in the minimal Non-Capture certificate.
`SETTLEMENT` holds route adequacy and standing fixed while settlement arrives at times
`3`, `30`, or never. At horizon `10`, terminal-discharge availability differs and Robust
Openness is unchanged. Thus timing is load-bearing for Answerability's terminal fate but
not for the Robust Openness conclusion. If settlement is the sole registration route,
suppressing it instead falsifies `(Ra)`, `(Rb)`, or `(Rc)` through `Adeq`; the existing
route clauses already expose that failure.

`EVALUATOR` holds the Non-Capture certificate and Robust Openness while changing the
closure protocol from anchored to captured. Evaluator fidelity therefore belongs to
Integrity's semantic-authentication input or the separate practical-semantics bill. If
the process can control whether evaluation is reachable, that reachability can be made a
coverage route and tested by the same Non-Capture interface; the correctness of the
evaluation remains external.

Later cognition that rejects an earlier `Closes` judgment should add a reconsideration
or reopening obligation with ancestry to the earlier closure rationale. Nothing in this
round proves that rule or retroactively changes the settlement item.
