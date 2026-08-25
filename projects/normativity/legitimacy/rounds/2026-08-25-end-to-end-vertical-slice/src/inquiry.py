"""The return loop: pressure -> need -> action -> settlement -> service -> reason.

The claim this module exists to prosecute is that **inquiry completes the loop
without becoming a second reasoner**. Nothing here is a historical event. There
is no `InquiryEvent`, no `ServiceEvent`, no `AssessmentEvent`, no
`PressureEvent`. The only durable epistemic return is an ordinary `ReasonOcc`,
and the only thing that moves normative standing is an ordinary licensed
`NormEvent`.

So every object below is one of three kinds:

    derived predicate      Need, ValidCert, AdmissibleAssessment
    environment-side       Action, RawOutcome, InteractionLog, Gamma, Policy
    frozen provenance      the reading's receipt, admitted once with it

**The provenance seam.** Service must be able to tell "`¬C` was settled" from
"`¬C` was settled *by the designated probe*", and it must do so without
widening `sem_L` or the reason source sorts. The narrowest bridge that works is
already half-built: `SettlementReading` carries `of_outcome`, so it needs only
the receipt that outcome came from —

    SettleId -> SettlementReading -> (outcome id, action, receipt index)

frozen at admission, alongside the sentences. `sem_L : SettleId -> Finset
Sentence` never sees it, reason sources stay `V + SettleId`, and no ledger gains
a field. Service reads the provenance; the epistemic substrate does not.

**What service means, and does not.** A specification is conclusion-neutral: it
says what work the history had to contain, never what the answer was. Both
branches of a real experiment can be adequate service.

**Nothing here trusts a caller's word for a fact the architecture can derive.**
The episode a need runs under is looked up in the record and checked for
uniqueness and subject; procedural provenance is authenticated against an actual
interaction receipt before a reading may carry it; and a certificate must be
valid *for the pinned specification* and presently assessable before a reason
may be appended. An earlier pass accepted each of those as an argument, which is
what this module was rewritten to stop doing.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from typing import Callable, Iterable, Optional, Sequence

import li
from epistemic import RawOutcome, SettlementReading


# --------------------------------------------------------- environment side


#: The toy's whole action theory. Deliberately two constants: inquiry is
#: action-theory-parametric, and nothing below reads the action except the
#: environment and the service judge's provenance check.
WAIT = "Wait"
PROBE = "Probe"


@dataclass(frozen=True)
class InteractionReceipt:
    """Identity-bearing: position, the action taken, the outcome observed.

    The CIS round's `Receipt` under another name and with the response replaced
    by an outcome *id*, because the outcome is a `RawOutcome` that may or may
    not later be read into a settlement, and the receipt should not pretend to
    own it.
    """

    index: int
    action: str
    outcome_id: str


@dataclass(frozen=True)
class InteractionProvenance:
    """Authenticated procedural provenance. Constructible only by `authenticate`.

    The private witness is the whole point: a caller cannot fill these fields
    in. To hold one of these is to have had an actual receipt in an actual log
    resolve against the outcome being settled.
    """

    receipt_index: int
    action: str
    outcome_id: str

    def __init__(self, witness, receipt_index, action, outcome_id) -> None:
        if witness is not _AUTHENTIC:
            raise LiabilityOfProvenance(
                "procedural provenance is authenticated against a receipt; "
                "use inquiry.authenticate")
        object.__setattr__(self, "receipt_index", int(receipt_index))
        object.__setattr__(self, "action", action)
        object.__setattr__(self, "outcome_id", outcome_id)

    def as_tuple(self) -> tuple:
        return (self.outcome_id, self.action, self.receipt_index)


class LiabilityOfProvenance(Exception):
    """A provenance claim that no receipt supports."""


_AUTHENTIC = object()


def authenticate(log: "InteractionLog", outcome: RawOutcome,
                 receipt: "InteractionReceipt") -> InteractionProvenance:
    """Resolve a claimed receipt against the log and the outcome being settled.

    Four conditions, and all four are checked rather than assumed:

        the receipt is the log's own object at that index
        its action is the action the receipt records
        its outcome id is the outcome being settled
        the outcome is the one the log recorded under that receipt

    A forged receipt, a mismatched outcome, an index from another run, or an
    action relabelled after the fact all fail here — before any settlement
    exists, and so before anything could be serviced on the strength of it.
    """
    if receipt is None or outcome is None:
        raise LiabilityOfProvenance("provenance needs a receipt and an outcome")
    if not (0 <= receipt.index < len(log.receipts)):
        raise LiabilityOfProvenance(
            f"receipt index {receipt.index} is not in this log")
    held = log.receipts[receipt.index]
    if held != receipt:
        raise LiabilityOfProvenance(
            "the receipt is not this log's own at that index")
    if held.outcome_id != outcome.id:
        raise LiabilityOfProvenance(
            f"receipt {held.index} records {held.outcome_id!r}, "
            f"not {outcome.id!r}")
    if log.outcomes.get(outcome.id) is not outcome:
        raise LiabilityOfProvenance(
            "the outcome is not the one this log recorded")
    return InteractionProvenance(_AUTHENTIC, held.index, held.action,
                                 held.outcome_id)


class InteractionLog:
    """Append-only record of what was done and what came back.

    **Not part of `MachineState`.** This is the environment's side of the
    boundary: `Gamma` reads it, a policy reads it, and RI never does. A raw
    outcome becomes public exactly when a settlement is admitted for it, which
    is the seam the architecture already had.
    """

    def __init__(self) -> None:
        self.receipts: list = []
        self.outcomes: dict = {}

    def record(self, action: str, outcome: RawOutcome) -> InteractionReceipt:
        receipt = InteractionReceipt(len(self.receipts), action, outcome.id)
        self.receipts.append(receipt)
        self.outcomes[outcome.id] = outcome
        return receipt

    def history(self) -> tuple:
        return tuple((r.action, r.outcome_id) for r in self.receipts)

    def receipt_for(self, outcome_id: str) -> Optional[InteractionReceipt]:
        for r in self.receipts:
            if r.outcome_id == outcome_id:
                return r
        return None


#: `Gamma : H x A -> P+(RawOutcome)` — history-relational, nonempty, and no
#: query oracle anywhere. A probe is an ordinary action whose outcome the
#: environment chooses; the machine learns what it learns by settling it.
Gamma = Callable[[tuple, str], Sequence[RawOutcome]]


def diagnostic_gamma(outcome_id: str = "o:trial",
                     content: str = "the trial ran and the readout came back"
                     ) -> Gamma:
    """The canonical toy's environment.

    `Probe` yields the trial readout; `Wait` yields an uninformative tick. Both
    responses are singletons here, which keeps the fixture deterministic without
    making the interface functional — the type is still set-valued.
    """

    def gamma(history: tuple, action: str) -> tuple:
        if action == PROBE:
            return (RawOutcome(outcome_id, content),)
        return (RawOutcome(f"o:tick{len(history)}", "nothing was attempted"),)

    return gamma


#: `Policy : MachineView -> Action`. Two of them, and no objective anywhere.
def probe_policy(need_live: bool) -> str:
    return PROBE if need_live else WAIT


def wait_policy(need_live: bool) -> str:
    return WAIT


# ------------------------------------------------------------- pressure


@dataclass(frozen=True)
class Pressure:
    """One force-bearing standing's **own** share of the day's liability.

    Not the joint charge. `D_t` and `q_t` are computed from all active rows at
    once and are not additively separable, so attributing the joint figure to a
    standing would over-report the moment a second injunction is active — and
    would report the *same* total for each of them.

    `answerability.allocate` already solves this: each standing's rows form a
    genuine `ForceRequest` over the joint support and the joint live worlds, and
    subadditivity of `D` makes the solo charges cover the joint one. So the
    quantity here is that standing's solo charge, and `joint_charge` is carried
    alongside so a reader can see the two are different numbers.
    """

    standing_id: str
    sharp: object                      # this standing's solo deficit
    charge: object                     # this standing's solo charge
    joint_charge: object               # the day's total, for comparison
    withheld: Optional[str]

    @property
    def positive(self) -> bool:
        return self.sharp > 0


def pressure_of(run, standing_id: str) -> Optional[Pressure]:
    """Read one standing's own liability out of the day's charged result.

    `None` when the day never reached the charged branch — a blocked conflict or
    an unsatisfiable stage — because there is then no liability fact to be under
    pressure from; and `None` when the standing carries no active force at this
    day, because a standing that demands nothing is under no pressure.
    """
    import answerability
    import safety

    if run.charged is None:
        return None
    if standing_id not in {sid for sid, _ in run.projection}:
        return None
    c = run.charged
    alloc = answerability.allocate(run.compiled, run.live_worlds, run.day,
                                   c.slack, c.volume, c.tolerance)
    if standing_id not in alloc:
        return None
    solo = safety.certify(
        answerability._SubPresentation(
            run.compiled.coords,
            tuple(r for r in run.compiled.rows
                  if r.standing_id == standing_id)),
        run.live_worlds, run.day)
    return Pressure(standing_id, solo.aggregate, alloc[standing_id], c.charge,
                    c.withheld)


# ------------------------------------------------------------- the need


@dataclass(frozen=True)
class InquiryRef:
    """What an inquiry is *about*, and by type nothing else.

    Keyed by `(subject, key)` with the specification pinned. The subject is a
    `StandingId` rather than an `AnsRootId`: the unresolved matter persists
    across episodes, and which episode currently carries it is custody
    information the machine reads separately. `test_inquiry.py` exercises the
    case that decides this — an inquiry that outlives a custody transfer.
    """

    subject: str                       # StandingId
    key: str                           # InquiryKey
    spec: str                          # ServiceSpecId


def current_episode_for(history, subject: str, t=None):
    """The unique current answerability episode of `subject`, or `None`.

    Derived from the record: `Roots_t` filtered by `subject`, kept where
    `CurrentEpisode` holds. Episode Uniqueness makes at most one survive, and
    this raises rather than choosing if the record ever violates that — a
    reference model that silently picked one would hide exactly the failure the
    invariant exists to catch.
    """
    live = [q for q in history.roots(t)
            if q.subject == subject and history.current_episode(q, t)]
    if len(live) > 1:
        raise ValueError(
            f"Episode Uniqueness fails for {subject}: {[q.id for q in live]}")
    return live[0] if live else None


@dataclass(frozen=True)
class InquiryNeed:
    """A derived, read-only fact: this reference is presently unserviced.

    A need is not an obligation, not a reason, not a desired conclusion, and
    not a normative event. It licenses nothing. A policy may act on it; nothing
    is wrong with a policy that does not.
    """

    ref: InquiryRef
    pressure: Pressure
    episode: str                       # the AnsRootId currently carrying it

    def __repr__(self) -> str:
        return (f"InquiryNeed({self.ref.subject}/{self.ref.key} "
                f"under {self.episode}, D={self.pressure.sharp})")


def derive_need(run, history, ref: InquiryRef,
                facts: Sequence["SettledFact"] = (),
                spec: Optional["ServiceSpec"] = None, t=None,
                now: Optional[int] = None,
                window: Optional[int] = None) -> Optional[InquiryNeed]:
    """`Need(state, ref)` — a function of the record, and it mutates nothing.

    Live when three things hold together: the reference's subject carries
    positive liability under this day's projection; the record has a unique
    current answerability episode for that subject; and no presently usable
    service exists for the pinned specification.

    **The episode is derived, not supplied.** An earlier pass took it as an
    argument and stored it, which let a need name a root that did not exist, was
    not current, or belonged to another standing. It is now looked up.

    **"Presently usable", not "ever certified".** See `INQUIRY_INTEGRATION.md`
    Q3: a certificate whose assessability has lapsed leaves the historical fact
    of service standing and the need live again. Suppressing the need on mere
    historical certifiability would let a machine believe it holds service it can
    no longer use.
    """
    pressure = pressure_of(run, ref.subject)
    if pressure is None or not pressure.positive:
        return None
    episode = current_episode_for(history, ref.subject, t)
    if episode is None:
        return None
    if spec is not None and assessable_now(spec, facts, now=now,
                                           window=window):
        return None
    return InquiryNeed(ref, pressure, episode.id)


# ------------------------------------------- settlement-backed service


@dataclass(frozen=True)
class SettledFact:
    """The frozen view of one settlement that a service judge may read.

    Sentences *and* provenance. The epistemic substrate reads the first and is
    blind to the second; service reads both. That asymmetry is the whole of the
    seam, and it is why service does not factor through `PC(Sigma)`.
    """

    settle_id: str
    sentences: tuple
    of_outcome: Optional[str]
    action: Optional[str]
    receipt_index: Optional[int]

    def holds(self, sentence) -> bool:
        return sentence in self.sentences


def settled_facts(settle_ids: Sequence[str], sem) -> tuple:
    """The provenance view of a settlement ledger, in ledger order."""
    out = []
    for sid in settle_ids:
        if sid not in sem:
            continue
        reading = sem.reading(sid)
        prov = reading.provenance
        if prov is None:
            out.append(SettledFact(sid, tuple(reading.sentences),
                                   reading.of_outcome, None, None))
        else:
            if not isinstance(prov, InteractionProvenance):
                raise LiabilityOfProvenance(
                    f"{sid} carries unauthenticated provenance {prov!r}")
            out.append(SettledFact(sid, tuple(reading.sentences),
                                   prov.outcome_id, prov.action,
                                   prov.receipt_index))
    return tuple(out)


@dataclass(frozen=True)
class ServiceCertificate:
    """A finite witness of historical service: the spec, the settlements cited.

    Citations are `SettleId`s rather than transcript indices. Settlement is the
    public epistemic boundary, so a certificate that cites settlements is one
    the normative record can read without being handed the environment's log.
    """

    spec_id: str
    cited: tuple
    data: object = None


class ServiceSpec:
    """`sigma = (C_sigma, Check_sigma)`, with a citation-local judge.

    The CIS round's shape, with the cited objects changed from raw receipts to
    settled facts. Two properties survive that change and are what make the
    shape worth keeping:

    **Citation locality.** `check` sees only the facts the certificate cites,
    so a valid certificate cannot depend on anything else in the ledger.

    **Extension closure.** Settlements are append-only and `SettleId`s are
    stable, so a certificate valid over `L` is valid over `L ++ L'`. Historical
    service is permanent; whether it *presently* discharges anything is a
    separate question and lives in `Assessable`.

    A specification is **conclusion-neutral**: it says what work the history had
    to contain, never what the answer was.
    """

    def __init__(self, spec_id: str, check_cited: Callable,
                 prover: Optional[Callable] = None) -> None:
        self.spec_id = spec_id
        self._check_cited = check_cited
        self._prover = prover

    def check(self, facts: Sequence[SettledFact],
              cert: ServiceCertificate) -> bool:
        if cert.spec_id != self.spec_id:
            return False
        index = {f.settle_id: f for f in facts}
        if any(sid not in index for sid in cert.cited):
            return False
        return bool(self._check_cited(tuple(index[s] for s in cert.cited),
                                      cert.data))

    def prove(self, facts: Sequence[SettledFact]) -> Optional[ServiceCertificate]:
        """Certificate discovery. An algorithm, never semantics."""
        return self._prover(facts) if self._prover else None


def valid_cert(spec: ServiceSpec, facts: Sequence[SettledFact],
               cert: ServiceCertificate) -> bool:
    """`ValidCert(sigma, L, kappa)`."""
    return spec.check(facts, cert)


def certifiable(spec: ServiceSpec, facts: Sequence[SettledFact],
                max_cited: int = 2, datas: Sequence = (None,)) -> bool:
    """`Certifiable(sigma, L) = exists kappa. ValidCert(sigma, L, kappa)`.

    Exhaustive over citation tuples up to `max_cited`. Complete exactly for
    specifications whose valid certificates fit that search space, which the
    round's do.
    """
    ids = tuple(f.settle_id for f in facts)
    for k in range(max_cited + 1):
        for cited in itertools.product(ids, repeat=k):
            for data in tuple(datas):
                if spec.check(facts, ServiceCertificate(spec.spec_id, cited,
                                                        data)):
                    return True
    return False


def diagnostic_spec(spec_id: str, luv, threshold, action: str = PROBE
                    ) -> ServiceSpec:
    """The round's specification: *the designated probe settled the matter*.

    Conclusion-neutral by construction. It accepts a settlement that came from
    `action` and that decided the threshold **either way** — affirming it or
    denying it. What it refuses is a settlement of the same proposition that did
    not come from the designated procedure, which is what makes service more
    than a fact about `Sigma`.
    """
    positive = luv.gt(threshold)
    negative = li.Neg(positive)

    def check(cited, data) -> bool:
        for fact in cited:
            if fact.action != action:
                continue
            if fact.holds(positive) or fact.holds(negative):
                return True
        return False

    def prove(facts):
        for fact in facts:
            if fact.action == action and (fact.holds(positive)
                                          or fact.holds(negative)):
                return ServiceCertificate(spec_id, (fact.settle_id,))
        return None

    return ServiceSpec(spec_id, check, prove)


def assessable(spec: ServiceSpec, facts: Sequence[SettledFact],
               cert: ServiceCertificate, window: Optional[int] = None,
               now: Optional[int] = None) -> bool:
    """Whether a historically valid certificate is *presently* usable.

    Separate from `valid_cert` on purpose. Historical service is permanent and
    monotone; current assessability may lapse. A freshness window lives here and
    nowhere else, so nothing about it can reach back and unmake the historical
    fact.
    """
    if not valid_cert(spec, facts, cert):
        return False
    if window is None or now is None:
        return True
    index = {f.settle_id: f for f in facts}
    ages = [now - index[s].receipt_index for s in cert.cited
            if index[s].receipt_index is not None]
    return all(age <= window for age in ages)


def assessable_now(spec: ServiceSpec, facts: Sequence[SettledFact],
                   max_cited: int = 2, now: Optional[int] = None,
                   window: Optional[int] = None) -> bool:
    """Whether some certificate for `spec` is valid **and presently usable**.

    `Certifiable` asks whether the history ever contained adequate service;
    this asks whether that service is still available to lean on. With no
    freshness window the two coincide, which is the toy's default and is what
    makes the distinction visible rather than load-bearing here.
    """
    ids = tuple(f.settle_id for f in facts)
    for k in range(max_cited + 1):
        for cited in itertools.product(ids, repeat=k):
            cert = ServiceCertificate(spec.spec_id, cited, None)
            if spec.check(facts, cert) and assessable(spec, facts, cert,
                                                      window=window, now=now):
                return True
    return False


# ------------------------------------------------------------ assessment


@dataclass(frozen=True)
class ReasonProposal:
    """A candidate `ReasonOcc`, before anything has admitted it.

    The three fields an occurrence carries and no others, so that admitting one
    is an append of exactly what was proposed.
    """

    reason_id: str
    s_V: frozenset
    s_L: frozenset
    target: object


class AssessmentCode:
    """A checker over proposed reasons. Not a conclusion generator.

    `admits(ref, cert, facts, proposal)` asks whether the proposal is an
    admissible interpretation of the serviced history. An arbitrary algorithm
    may propose; this decides admissibility. There is deliberately no function
    from a certificate to *the* correct conclusion, because there is no such
    function: the same adequate investigation can bear several ways.
    """

    def __init__(self, code_id: str, admits: Callable) -> None:
        self.code_id = code_id
        self._admits = admits

    def admits(self, ref: InquiryRef, cert: ServiceCertificate,
               facts: Sequence[SettledFact],
               proposal: ReasonProposal) -> bool:
        return bool(self._admits(ref, cert, facts, proposal))


class AssessmentRefused(Exception):
    """The composite gate refused; the clause that refused is the message."""


def admissible_assessment(ref: InquiryRef, spec: ServiceSpec,
                          facts: Sequence[SettledFact],
                          cert: Optional[ServiceCertificate],
                          code: "AssessmentCode", proposal: "ReasonProposal",
                          now: Optional[int] = None,
                          window: Optional[int] = None) -> bool:
    """The whole gate a proposed reason must pass, in order.

        ref.spec == spec.spec_id        the specification is the pinned one
        cert.spec_id == spec.spec_id    the certificate addresses it
        ValidCert(spec, facts, cert)    and the judge accepts it
        Assessable(...)                 and it is presently usable
        code.admits(...)                and the proposal is grounded in it

    An earlier pass ran only the last clause, against whatever certificate it
    was handed. That admitted a proposal on a certificate for another
    specification, on an invalid one, on one citing settlements that do not
    exist, and on one whose provenance nothing authenticated — because a
    matching `cited` field was all it looked at.

    The clauses are ordered so that the first failure is the informative one.
    """
    if cert is None:
        return False
    if ref.spec != spec.spec_id:
        return False
    if cert.spec_id != spec.spec_id:
        return False
    if not valid_cert(spec, facts, cert):
        return False
    if not assessable(spec, facts, cert, window=window, now=now):
        return False
    return code.admits(ref, cert, facts, proposal)


def grounded_in_cited_settlements(code_id: str = "grounded") -> AssessmentCode:
    """The round's assessment: a reason must be grounded in what was serviced.

    Two conditions, both citation-local. The proposal's settlement sources are
    exactly among those the certificate cited, and it has at least one. So a
    reason may not smuggle in evidence the service did not cover, and may not
    float free of the investigation it claims to rest on.

    It says nothing about what the reason concludes. A proposal for the opposite
    target, grounded in the same settlements, is equally admissible — which is
    the conclusion-neutrality the specification already has, preserved one layer
    up.
    """

    def admits(ref, cert, facts, proposal) -> bool:
        if not proposal.s_L:
            return False
        return set(proposal.s_L) <= set(cert.cited)

    return AssessmentCode(code_id, admits)


# ------------------------------------------ service does not factor through PC


def provenance_fixture(luv, threshold, upper, spec_id: str = "sigma:fixture"):
    """Two ledgers with the same `Sigma` and different **authenticated** provenance.

    Both settle the very same sentences, so `sem_L` agrees, `Sigma` agrees,
    `PC(Sigma)` agrees and every price agrees. They differ only in what actually
    happened: `good` ran the designated probe and `bad` ran something else, and
    each ledger's provenance is authenticated against its own interaction log
    rather than labelled by hand.

    That is the executable form of

        service need not factor through PC(Sigma)

    and it survives the authentication repair, which is the point: the verdict
    turns on procedural history, not on a string a fixture chose.
    """
    from epistemic import SettlementSemantics

    sentences = (luv.gt(threshold), li.Neg(luv.gt(upper)))

    def ledger(action: str, outcome_id: str, note: str):
        log = InteractionLog()
        outcome = RawOutcome(outcome_id, note)
        receipt = log.record(action, outcome)
        sem = SettlementSemantics()
        sem.admit(SettlementReading(
            "l:same", outcome.id, sentences, note,
            provenance=authenticate(log, outcome, receipt)))
        return log, sem

    good_log, good = ledger(PROBE, "o:probe", "settled by the designated trial")
    bad_log, bad = ledger("Hearsay", "o:hearsay",
                          "the same proposition, another route")

    return {"spec": diagnostic_spec(spec_id, luv, threshold, action=PROBE),
            "good": good, "bad": bad, "good_log": good_log, "bad_log": bad_log,
            "ids": ("l:same",), "sentences": sentences}
