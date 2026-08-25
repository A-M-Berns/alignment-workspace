"""The return loop: pressure -> need -> action -> settlement -> service -> reason.

The claim this module prosecutes is that **inquiry completes the loop without
becoming a second reasoner**. Nothing here is a historical event. There is no
`InquiryEvent`, no `ServiceEvent`, no `AssessmentEvent`, no `PressureEvent`. The
only durable epistemic return is an ordinary `ReasonOcc`, and the only thing that
moves normative standing is an ordinary licensed `NormEvent`.

Every object below is one of three kinds:

    derived predicate      Need, ValidCert, Certifiable, Assessable,
                           AdmissibleAssessment
    environment-side       Action, RawOutcome, InteractionReceipt,
                           InteractionLog, Gamma, Policy
    frozen provenance      the receipt id a reading is admitted with

**No arrow exists because a caller said it did.** Three seams carry that weight
and each is checked rather than annotated.

*Action to receipt.* The only public way to interact is `execute(log, gamma,
action)`, which asks `Gamma` what the environment permits and records what comes
back. There is no public append, so a `Probe` receipt cannot exist without a
probe.

*Outcome to meaning.* A `SettlementReader` is pinned in advance and computes the
LI-facing sentences **from the authenticated outcome**. So `Wait` cannot carry
the trial's diagnostic content: the reader returns nothing for it and the
settlement constrains no world. Without this the decomposition leaks — the agent
would learn from an action that did not investigate.

*Settlement to service.* Provenance is a `ReceiptId` resolved against the log's
own immutable receipt, so a separately built receipt with matching field values
authenticates nothing.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Optional, Sequence

import li
from epistemic import RawOutcome, SettlementReading


# --------------------------------------------------------- environment side


#: The toy's whole action theory. Two constants: inquiry is
#: action-theory-parametric, and nothing below reads the action except the
#: environment, the pinned reader, and the service judge's provenance check.
WAIT = "Wait"
PROBE = "Probe"


class InteractionRefused(Exception):
    """An interaction the environment does not permit."""


class ProvenanceRefused(Exception):
    """A provenance claim no receipt supports."""


class SpecMismatch(Exception):
    """A specification other than the one an inquiry reference pins."""


@dataclass(frozen=True)
class InteractionReceipt:
    """Immutable, identity-bearing: a stable id, the action, the outcome.

    Authentication is by `receipt_id` rather than by object identity, so the
    model does not lean on Python's `is`. A separately constructed receipt with
    the same field values is a different receipt unless its id resolves, in this
    log, to the log's own — and then the log's values are the ones used.
    """

    receipt_id: str
    index: int
    action: str
    outcome_id: str


class InteractionLog:
    """Append-only record of what was done and what came back.

    **Not part of `MachineState`.** This is the environment's side of the
    boundary: `Gamma` reads it, a policy reads it, Reflective Integrity never
    does. A raw outcome becomes public exactly when a settlement is admitted.

    There is deliberately **no public append**. `_record` is private and
    `execute` is the only way in, because a log that accepted a caller's chosen
    `(action, outcome)` pair would let a `Probe` receipt exist without a probe.
    """

    def __init__(self, name: str = "log") -> None:
        self.name = name
        self.receipts: list = []
        self.outcomes: dict = {}
        self._by_id: dict = {}

    def _record(self, action: str, outcome: RawOutcome) -> InteractionReceipt:
        rid = f"{self.name}#{len(self.receipts)}"
        receipt = InteractionReceipt(rid, len(self.receipts), action,
                                     outcome.id)
        self.receipts.append(receipt)
        self.outcomes[outcome.id] = outcome
        self._by_id[rid] = receipt
        return receipt

    def history(self) -> tuple:
        return tuple((r.action, r.outcome_id) for r in self.receipts)

    def receipt(self, receipt_id: str) -> Optional[InteractionReceipt]:
        return self._by_id.get(receipt_id)

    def outcome(self, outcome_id: str) -> Optional[RawOutcome]:
        return self.outcomes.get(outcome_id)


#: `Gamma : H x A -> P+(RawOutcome)` — history-relational, nonempty, and no
#: query oracle anywhere. A probe is an ordinary action whose outcome the
#: environment chooses; the machine learns what it learns by settling it.
Gamma = Callable[[tuple, str], Sequence[RawOutcome]]


def execute(log: InteractionLog, gamma: Gamma, action: str,
            choose=None) -> tuple:
    """The canonical action path: ask the environment, record what it gives.

        outcomes = gamma(log.history(), action)
        y        = choose(outcomes)          -- must be one of them
        receipt  = log._record(action, y)

    `choose` defaults to the first response, which is deterministic for the
    toy's singleton fixtures and is not part of the interface's meaning: the
    type is set-valued and a caller may supply any selector over what `Gamma`
    permits. What a selector may **not** do is return something `Gamma` did not
    offer.
    """
    permitted = tuple(gamma(log.history(), action))
    if not permitted:
        raise InteractionRefused(
            f"Gamma permits no outcome for {action!r}; P+ is nonempty")
    outcome = permitted[0] if choose is None else choose(permitted)
    if outcome not in permitted:
        raise InteractionRefused(
            f"{outcome!r} is not among the outcomes Gamma permitted")
    return outcome, log._record(action, outcome)


def diagnostic_gamma(outcome_id: str = "o:trial",
                     band=(Fraction(1, 3), Fraction(2, 3))) -> Gamma:
    """The canonical toy's environment.

    `Probe` yields a readout whose content is the band the trial pinned the
    quantity into; `Wait` yields a tick whose content is `None`. The content is
    what the pinned reader interprets, so whether an action is informative lives
    in the environment's response rather than in what a caller writes down.
    """

    def gamma(history: tuple, action: str) -> tuple:
        if action == PROBE:
            return (RawOutcome(outcome_id, {"band": band}),)
        return (RawOutcome(f"o:tick{len(history)}", {"band": None}),)

    return gamma


@dataclass(frozen=True)
class InquiryView:
    """The whole of what the toy's policies may read. Deliberately one field.

    Named so that `Policy : InquiryView -> Action` is honest about its argument.
    A richer controller would take a larger view; nothing here builds one.
    """

    need: Optional["InquiryNeed"] = None

    @property
    def need_live(self) -> bool:
        return self.need is not None


def probe_policy(view: InquiryView) -> str:
    return PROBE if view.need_live else WAIT


def wait_policy(view: InquiryView) -> str:
    return WAIT


# ------------------------------------------------- authenticated provenance


_AUTHENTIC = object()


@dataclass(frozen=True)
class InteractionProvenance:
    """Authenticated procedural provenance, built only by `authenticate`.

    The private witness is the point: to hold one of these is to have had a
    receipt id resolve, in an actual log, against the outcome being settled.
    """

    receipt_id: str
    receipt_index: int
    action: str
    outcome_id: str

    def __init__(self, witness, receipt_id, receipt_index, action,
                 outcome_id) -> None:
        if witness is not _AUTHENTIC:
            raise ProvenanceRefused(
                "procedural provenance is authenticated against a receipt; "
                "use inquiry.authenticate")
        object.__setattr__(self, "receipt_id", receipt_id)
        object.__setattr__(self, "receipt_index", int(receipt_index))
        object.__setattr__(self, "action", action)
        object.__setattr__(self, "outcome_id", outcome_id)


def authenticate(log: InteractionLog, outcome: RawOutcome,
                 receipt_id: str) -> InteractionProvenance:
    """Resolve a receipt **id** against the log and the outcome being settled.

    Three conditions, all checked:

        the id resolves to a receipt in this log
        that receipt's outcome id is the outcome being settled
        the outcome is the object this log recorded under that id

    The resulting action is read off the log's receipt, never off an argument.
    """
    if outcome is None:
        raise ProvenanceRefused("provenance needs the outcome being settled")
    held = log.receipt(receipt_id)
    if held is None:
        raise ProvenanceRefused(f"no receipt {receipt_id!r} in this log")
    if held.outcome_id != outcome.id:
        raise ProvenanceRefused(
            f"receipt {held.receipt_id} records {held.outcome_id!r}, "
            f"not {outcome.id!r}")
    if log.outcome(outcome.id) is not outcome:
        raise ProvenanceRefused(
            "the outcome is not the object this log recorded")
    return InteractionProvenance(_AUTHENTIC, held.receipt_id, held.index,
                                 held.action, held.outcome_id)


# ---------------------------------------------------------- the pinned reader


#: `SettlementReader : (InteractionProvenance, RawOutcome) -> Sentence*`
#:
#: Pinned in advance and applied to the authenticated result. This is the seam
#: that stops the loop smuggling an oracle: without it a caller could settle the
#: trial's sentences off the back of a `Wait`, and the agent would have learned
#: something no investigation produced.
SettlementReader = Callable[["InteractionProvenance", RawOutcome], tuple]


def diagnostic_reader(luv, action: str = PROBE) -> SettlementReader:
    """Read a band readout into threshold sentences, and read nothing else.

    The sentences are a function of the outcome's own content — the band the
    environment reported — so a settlement says what the interaction found. An
    action other than the designated one, or an outcome with no band, reads to
    the empty set: the non-exposure state, which constrains no world.
    """

    def read(provenance: InteractionProvenance, outcome: RawOutcome) -> tuple:
        if provenance.action != action:
            return ()
        content = outcome.content
        band = content.get("band") if isinstance(content, dict) else None
        if band is None:
            return ()
        lo, hi = band
        return (luv.gt(Fraction(lo)), li.Neg(luv.gt(Fraction(hi))))

    return read


def read_and_admit(sem, log: InteractionLog, outcome: RawOutcome,
                   receipt_id: str, reader: SettlementReader,
                   settle_id: str, note: str = "") -> SettlementReading:
    """Authenticate, read, and admit — the only path a settlement takes.

    The sentences are the reader's, not the caller's. A caller chooses *which*
    outcome to settle and under what id; what that settlement then means is
    fixed by the pinned reader and the authenticated result.
    """
    provenance = authenticate(log, outcome, receipt_id)
    sentences = tuple(reader(provenance, outcome))
    return sem.admit(SettlementReading(
        settle_id=settle_id, of_outcome=outcome.id, sentences=sentences,
        note=note, provenance=provenance))


# ------------------------------------------------------------- pressure


@dataclass(frozen=True)
class Pressure:
    """One force-bearing standing's **own** share of the day's liability.

    Not the joint charge. `D_t` and `q_t` are computed from all active rows at
    once and are not additively separable, so attributing the joint figure to a
    standing would report the same total for each of several.
    `answerability.allocate` supplies each standing's solo charge over the joint
    support and live worlds, and subadditivity makes the shares cover the joint.
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
    """Read one standing's own liability out of the day's result.

    `None` when the day never reached a charge — a blocked conflict or an
    unsatisfiable stage — and `None` when the standing carries no active force,
    because a standing that demands nothing is under no pressure.
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
    information the machine reads separately. A real RI `Transfer` moves the
    episode and leaves this untouched.
    """

    subject: str                       # StandingId
    key: str                           # InquiryKey
    spec: str                          # ServiceSpecId


def current_episode_for(history, subject: str, t=None):
    """The unique current answerability episode of `subject`, or `None`.

    Derived from the record: `Roots_t` filtered by subject, kept where
    `CurrentEpisode` holds. Episode Uniqueness makes at most one survive, and
    this raises rather than choosing if the record ever violates that.
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

    Not an obligation, not a reason, not a desired conclusion, not a normative
    event. It licenses nothing.
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
                current_use=None) -> Optional[InquiryNeed]:
    """`Need(state, ref)` — a function of the record, and it mutates nothing.

    Live when three things hold together: the reference's subject carries
    positive liability under this day's projection; the record has a unique
    current answerability episode for that subject; and no **presently usable**
    service exists for the specification the reference pins.

    The episode is derived, not supplied. The specification is checked against
    `ref.spec`: a specification the reference does not pin cannot decide whether
    that reference's inquiry is live, and passing one raises rather than
    silently answering a different question.

    "Presently usable", not "ever certified" — a certificate whose current
    usability has lapsed leaves the historical fact of service standing and the
    need live again.
    """
    if spec is not None and ref.spec != spec.spec_id:
        raise SpecMismatch(
            f"{ref.subject}/{ref.key} pins {ref.spec!r}; "
            f"{spec.spec_id!r} cannot decide whether it is live")
    pressure = pressure_of(run, ref.subject)
    if pressure is None or not pressure.positive:
        return None
    episode = current_episode_for(history, ref.subject, t)
    if episode is None:
        return None
    if spec is not None and assessable_now(spec, facts,
                                           current_use=current_use):
        return None
    return InquiryNeed(ref, pressure, episode.id)


# ------------------------------------------- settlement-backed service


@dataclass(frozen=True)
class SettledFact:
    """The frozen view of one settlement a service judge may read.

    Sentences *and* provenance. The epistemic substrate reads the first and is
    blind to the second; service reads both. That asymmetry is the seam, and it
    is why service does not factor through `PC(Sigma)`.
    """

    settle_id: str
    sentences: tuple
    of_outcome: Optional[str]
    action: Optional[str]
    receipt_id: Optional[str]

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
                raise ProvenanceRefused(
                    f"{sid} carries unauthenticated provenance {prov!r}")
            out.append(SettledFact(sid, tuple(reading.sentences),
                                   prov.outcome_id, prov.action,
                                   prov.receipt_id))
    return tuple(out)


@dataclass(frozen=True)
class ServiceCertificate:
    """A finite witness of historical service: the spec, the settlements cited.

    Citations are `SettleId`s rather than transcript indices, because settlement
    is the public epistemic boundary and a certificate the normative record can
    read is one that cites settlements.
    """

    spec_id: str
    cited: tuple
    data: object = None


class ServiceSpec:
    """`sigma = (C_sigma, Check_sigma)`, with a citation-local judge.

    The certified-interactive-service round's shape, with the cited objects
    changed from raw receipts to settled facts. Two properties survive that
    change and are why the shape is worth keeping:

    **Citation locality.** `check` sees only the facts the certificate cites.

    **Extension closure.** Settlements are append-only and `SettleId`s stable,
    so a certificate valid over `L` is valid over `L ++ L'`. Historical service
    is permanent; whether it is *presently usable* is `Assessable`'s question.

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
    """`ValidCert(sigma, L, kappa)` — historical, and permanent."""
    return spec.check(facts, cert)


def certifiable(spec: ServiceSpec, facts: Sequence[SettledFact],
                max_cited: int = 2, datas: Sequence = (None,)) -> bool:
    """`Certifiable(sigma, L) = exists kappa. ValidCert(sigma, L, kappa)`.

    Exhaustive over citation tuples up to `max_cited`; complete exactly for
    specifications whose certificates fit that space, which the round's do.
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
    """The round's specification: *the designated procedure settled the matter*.

    Conclusion-neutral by construction: it accepts a settlement that came from
    `action` and decided the threshold **either way**. What it refuses is a
    settlement of the same proposition that did not come from that procedure.
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


#: `CurrentUse : SettledFact -> bool` — an application-supplied predicate.
#:
#: Freshness, supersession and case relevance all live here, and the generic
#: core defines none of them. An earlier pass computed `now - receipt_index`
#: against a `now` described as time, comparing an interaction-order index to a
#: clock that does not exist.
CurrentUse = Callable[[SettledFact], bool]


def assessable(spec: ServiceSpec, facts: Sequence[SettledFact],
               cert: ServiceCertificate,
               current_use: Optional[CurrentUse] = None) -> bool:
    """Whether a historically valid certificate is **presently usable**.

    Separate from `valid_cert` on purpose: historical service is permanent and
    monotone, current usability is defeasible. With no `current_use` supplied
    the two coincide, which is the toy's default.
    """
    if not valid_cert(spec, facts, cert):
        return False
    if current_use is None:
        return True
    index = {f.settle_id: f for f in facts}
    return all(current_use(index[s]) for s in cert.cited)


def assessable_now(spec: ServiceSpec, facts: Sequence[SettledFact],
                   max_cited: int = 2,
                   current_use: Optional[CurrentUse] = None) -> bool:
    """Whether *some* certificate for `spec` is valid and presently usable."""
    ids = tuple(f.settle_id for f in facts)
    for k in range(max_cited + 1):
        for cited in itertools.product(ids, repeat=k):
            cert = ServiceCertificate(spec.spec_id, cited, None)
            if spec.check(facts, cert) and assessable(spec, facts, cert,
                                                      current_use):
                return True
    return False


def superseded_by_round(cutoff: int) -> CurrentUse:
    """A deliberately simple current-use predicate for the toy.

    "Service performed before round `cutoff` is no longer usable." It is a
    stand-in for whatever an application's real lapse condition is, and it lives
    here rather than in `assessable` so that the generic core commits to no
    theory of staleness.
    """

    def usable(fact: SettledFact) -> bool:
        return fact.receipt_id is not None and fact.action is not None \
            and _receipt_round(fact) >= cutoff

    return usable


def _receipt_round(fact: SettledFact) -> int:
    """The interaction-order index a receipt id encodes, as the toy's clock."""
    try:
        return int(str(fact.receipt_id).rsplit("#", 1)[1])
    except (IndexError, ValueError):
        return -1


# ------------------------------------------------------------ assessment


@dataclass(frozen=True)
class ReasonProposal:
    """A candidate `ReasonOcc`, before anything has admitted it."""

    reason_id: str
    s_V: frozenset
    s_L: frozenset
    target: object


class AssessmentCode:
    """A checker over proposed reasons. Not a conclusion generator.

    An arbitrary algorithm may propose a reason; this decides admissibility.
    There is deliberately no function from a certificate to *the* correct
    conclusion, because there is none: the same adequate investigation can bear
    several ways.
    """

    def __init__(self, code_id: str, admits: Callable) -> None:
        self.code_id = code_id
        self._admits = admits

    def admits(self, ref: InquiryRef, cert: ServiceCertificate,
               facts: Sequence[SettledFact],
               proposal: ReasonProposal) -> bool:
        return bool(self._admits(ref, cert, facts, proposal))


def admissible_assessment(ref: InquiryRef, spec: ServiceSpec,
                          facts: Sequence[SettledFact],
                          cert: Optional[ServiceCertificate],
                          code: AssessmentCode, proposal: ReasonProposal,
                          current_use: Optional[CurrentUse] = None) -> bool:
    """The whole gate a proposed reason must pass, in order.

        ref.spec == spec.spec_id        the specification is the pinned one
        cert.spec_id == spec.spec_id    the certificate addresses it
        ValidCert(spec, facts, cert)    and the judge accepts it
        Assessable(...)                 and it is presently usable
        code.admits(...)                and the proposal is grounded in it

    An earlier pass ran only the last clause against whatever certificate it was
    handed, so a matching `cited` field was the whole test.
    """
    if cert is None:
        return False
    if ref.spec != spec.spec_id:
        return False
    if cert.spec_id != spec.spec_id:
        return False
    if not valid_cert(spec, facts, cert):
        return False
    if not assessable(spec, facts, cert, current_use):
        return False
    return code.admits(ref, cert, facts, proposal)


def grounded_in_cited_settlements(code_id: str = "grounded") -> AssessmentCode:
    """The round's assessment: a reason must be grounded in what was serviced.

    Two citation-local conditions — the proposal's settlement sources are
    non-empty and lie within what the certificate cited. So a reason may not
    smuggle in evidence the service did not cover, and may not float free of the
    investigation it claims to rest on.

    It says nothing about what the reason concludes, and is **deliberately
    maximally permissive over targets**: a proposal for the opposite target on
    the same grounds is equally admissible. Whether a consideration is
    inferentially live belongs to the reason layer's pinned inference and
    applicability schemas, not here.
    """

    def admits(ref, cert, facts, proposal) -> bool:
        if not proposal.s_L:
            return False
        return set(proposal.s_L) <= set(cert.cited)

    return AssessmentCode(code_id, admits)


# ------------------------------------------ service does not factor through PC


def provenance_fixture(luv, threshold, upper, spec_id: str = "sigma:fixture"):
    """Two ledgers, same `Sigma`, different **execution-backed** procedures.

    Both histories run a real action through a real `Gamma`, take what the
    environment permits, and read it with a pinned reader keyed to *their own*
    action — so both genuinely settle the same sentences. They differ only in
    which procedure was performed.

    `sem_L` agrees, `Sigma` agrees, `PC(Sigma)` agrees, every price agrees — and
    the specification accepts one and refuses the other. Nothing here is a
    label: both provenances are authenticated against real logs, both readings
    come from pinned readers, and the verdict turns on procedural history alone.
    """
    from epistemic import SettlementSemantics

    band = (Fraction(threshold), Fraction(upper))

    def ledger(action: str, name: str, outcome_id: str, note: str):
        def gamma(history, a):
            return (RawOutcome(outcome_id, {"band": band}),)

        log = InteractionLog(name)
        outcome, receipt = execute(log, gamma, action)
        sem = SettlementSemantics()
        read_and_admit(sem, log, outcome, receipt.receipt_id,
                       diagnostic_reader(luv, action=action), "l:same", note)
        return log, sem

    good_log, good = ledger(PROBE, "good", "o:probe",
                            "settled by the designated trial")
    bad_log, bad = ledger("Hearsay", "bad", "o:hearsay",
                          "the same proposition, another route")

    return {"spec": diagnostic_spec(spec_id, luv, threshold, action=PROBE),
            "good": good, "bad": bad, "good_log": good_log, "bad_log": bad_log,
            "ids": ("l:same",),
            "sentences": good.sem("l:same")}
