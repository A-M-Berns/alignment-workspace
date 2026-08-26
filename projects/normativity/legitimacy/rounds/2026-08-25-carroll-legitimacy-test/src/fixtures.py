"""The adversarial suite, C0 to C33, as constructed cases.

Every fixture is a Reflective Integrity record over one of the five Carroll
DR-MDPs. The DR-MDP is never edited: `Q_DR` of every enriched case in this
module is one of `carroll_cases`' own constructions, and the tests check it.

Three schemas do all the work, and none of them reads a narrative label:

```text
create      Create(K)                  install standings the witness names
supersede   Supersede(X, K)            replace standings the witness names
revise      Supersede(X, K) | SetStatus  the person's own reflective procedure
```

The last is seeded rather than created, so it is independent of every episode by
construction. That is the only thing in this module that is true by
construction, and it is the analogue of a person's standing authority over their
own commitments rather than a normative label about any particular revision.

Two further schemas appear only in the fixtures that need them: a minting schema
that reads the strict pre-state (`C28`) and one whose admissibility is a parity
condition on the pre-state (`nonmonotone_case`). Both are legal under `S1`-`S6`,
and both exist to show what Reflective Integrity permits rather than to model
anything.
"""
from __future__ import annotations

from dataclasses import replace

import ri_core as ri
from standing import PValue

import carroll_cases as cc
import drmdp
import enrichment as en
import legitimacy as lg

AI = "AI"
USER = "User"
PROXY = "Proxy"
GENESIS_PRINCIPAL = "p0"


# ------------------------------------------------------------------ schemas


def _create(wit, pre):
    return ri.Standing(ri.Create(tuple(wit)))


def _supersede(wit, pre):
    return ri.Standing(ri.Supersede(frozenset(wit[0]), tuple(wit[1])))


def _revise(wit, pre):
    """One procedure, two possible conclusions. Neither is built in.

    `("revise", targets, payloads)` supersedes; `("keep", targets)` reaffirms.
    The witness carries the conclusion the procedure reached; the schema carries
    no preference between them, which is what conclusion-neutrality means here.
    """
    if wit[0] == "revise":
        return ri.Standing(ri.Supersede(frozenset(wit[1]), tuple(wit[2])))
    return ri.Standing(ri.SetStatus(frozenset(wit[1]), ri.ACTIVE))


SC_CREATE = ri.SchemaCode("create", _create)
SC_SUPERSEDE = ri.SchemaCode("supersede", _supersede)
SC_REVISE = ri.SchemaCode("revise", _revise)

CONST_CREATE = "const.create"
CONST_SUPERSEDE = "const.supersede"
SELF_REVISION = "self.revision"


def seed(extra: dict = None) -> ri.Seed:
    """The constitutional seed, plus whatever standings a fixture starts with.

    `WFSeed` requires one genesis root per seed standing, so the roots are
    derived from the standings rather than listed.
    """
    std = {
        CONST_CREATE: ri.StandingState(ri.ACTIVE, frozenset(), ri.PAuth(SC_CREATE)),
        CONST_SUPERSEDE: ri.StandingState(ri.ACTIVE, frozenset(),
                                          ri.PAuth(SC_SUPERSEDE)),
        SELF_REVISION: ri.StandingState(ri.ACTIVE, frozenset(),
                                        ri.PAuth(SC_REVISE)),
    }
    for name, payload in (extra or {}).items():
        std[name] = ri.StandingState(ri.ACTIVE, frozenset(), payload)
    roots = tuple(
        ri.AnsRoot(f"q0.{i}", (GENESIS_PRINCIPAL, 0), GENESIS_PRINCIPAL, x,
                   ri.ACCOUNT_FOR_SUCCESSION, ri.GENESIS, 0)
        for i, x in enumerate(sorted(std)))
    return ri.Seed(GENESIS_PRINCIPAL, std, roots)


# ------------------------------------------------------------- conveniences

MOVE_CLASS = (1, 0, 1)   #: the a_move edge from theta_0 to theta_1, in every
                         #: two-node example: `(action index, theta index,
                         #: theta index)` into the DR-MDP's own declaration
                         #: order. Purely structural, and identical for
                         #: Conspiracy Influence and the AI Personal Trainer.

WINDOW = "f:condition-obtains"


def trainer_protocol(pid="p:designated", agent=AI, polarity="permit",
                     condition=frozenset({WINDOW}),
                     domain="reward-parameterisation") -> en.Protocol:
    return en.Protocol(pid, agent, frozenset({MOVE_CLASS}), condition,
                       polarity, domain)


def move_intervention(m: drmdp.DRMDP, tau: int, episode=None,
                      facts=frozenset({WINDOW}), agent=AI) -> en.Intervention:
    return en.Intervention("I", agent, m.actions[1], m.thetas[0], m.thetas[1],
                           tau, episode, facts)


def bridge(m: drmdp.DRMDP) -> dict:
    """The explicit bridge from a cognitive state to a value specification.

    Nothing makes this map automatic. A parameterization is in the DR-MDP; a
    specification has standing only where an event installed it.
    """
    return {th: f"v:{th}" for th in m.thetas}


def narrative(name, subject) -> en.Narrative:
    return en.Narrative(name, subject)


# ================================================================ fixtures
#
# Each returns a dict with the case, the intervention under test, and a note.


def bare(case_name: str, subject: str, tau: int = 1) -> dict:
    """No enrichment at all: the DR-MDP and an empty record."""
    m = cc.CASES[case_name]()
    b = en.CaseBuilder(m, seed(), narrative(case_name, subject))
    iv = move_intervention(m, tau, episode=None)
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "note": f"bare {case_name}"}


def C1_dr_equivalence() -> dict:
    bob, diana = bare("ConspiracyInfluence", "B"), bare("AIPersonalTrainer", "D")
    mb, md = en.Q_DR(bob["case"]), en.Q_DR(diana["case"])
    return {"bob": bob, "diana": diana,
            "canonical_bob": drmdp.canonical(mb),
            "canonical_diana": drmdp.canonical(md)}


def C2_bare_negative_control() -> dict:
    return C1_dr_equivalence()


def C3_relabelling(base: dict = None) -> dict:
    """Rename every label of an enriched case; the record is untouched."""
    src = base or C7_authorized_diana()
    case = src["case"]
    m = case.dr_mdp
    smap = {s: f"renamed::{s}" for s in m.states}
    thmap = {t: f"renamed::{t}" for t in m.thetas}
    amap = {a: f"renamed::{a}" for a in m.actions}
    other = en.relabel_case(case, smap, thmap, amap,
                            narrative("swapped", "somebody else"))
    iv = replace(src["iv"], action=amap[src["iv"].action],
                 theta_before=thmap[src["iv"].theta_before],
                 theta_after=thmap[src["iv"].theta_after])
    return {"original": src, "case": other, "iv": iv}


def C4_self_ratifying() -> dict:
    """Influence, then the influenced person endorses the influence."""
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed({"val.low": PValue("v:th_natural")}),
                       narrative("self-ratifying", "B"))
    iv = move_intervention(m, tau=1, episode="E")
    b.declare(iv)
    b.begin("E")
    b.settle("s:influence")                                   # tau 1: the act
    b.settle("s:endorsement", refs={"s:influence"})           # tau 2
    b.reason("r:endorsed", s_L={"s:endorsement"}, target="v:th_influenced")
    b.norm("a:uptake", SELF_REVISION, USER,
           wit=("revise", {"val.low"}, (PValue("v:th_influenced"),)),
           leaves={"r:endorsed"})
    b.end()
    return {"case": b.build(), "iv": iv, "bridge": bridge(m)}


def C5_ri_good_manipulation() -> dict:
    """Every downstream step clean, and the initial act with no prior basis."""
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed(), narrative("RI-good manipulation", "B"))
    b.begin("E")
    b.settle("s:manipulation")                                # tau 1
    b.reason("r:from-manipulation", s_L={"s:manipulation"}, target="v:permit")
    b.norm("a:install", CONST_CREATE, USER,
           wit=(ri.PProto(trainer_protocol("p:manufactured")),),
           leaves={"r:from-manipulation"})
    b.settle("s:follow-up", refs={"s:manipulation"})
    b.reason("r:follow-up", s_L={"s:follow-up"}, target="v:th_influenced")
    b.norm("a:uptake", CONST_CREATE, USER, wit=(PValue("v:th_influenced"),),
           leaves={"r:follow-up"})
    b.end()
    iv = move_intervention(m, tau=b.now + 1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "bridge": bridge(m)}


def C6_bare_diana() -> dict:
    return bare("AIPersonalTrainer", "D")


def C7_authorized_diana() -> dict:
    """A live protocol, seeded, covering the nudge class, with a condition."""
    m = cc.ai_personal_trainer()
    s = seed({"proto.designated": ri.PProto(trainer_protocol()),
              "val.low": PValue("v:th_tired")})
    b = en.CaseBuilder(m, s, narrative("authorized trainer", "D"))
    iv = move_intervention(m, tau=1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "bridge": bridge(m)}


def C8_current_self_disagreement() -> dict:
    """The person objects; the objection is on the record and is not authority."""
    src = C7_authorized_diana()
    m = src["case"].dr_mdp
    s = seed({"proto.designated": ri.PProto(trainer_protocol()),
              "val.low": PValue("v:th_tired")})
    b = en.CaseBuilder(m, s, narrative("objecting trainer", "D"))
    b.settle("s:objection")
    b.reason("r:objection", s_L={"s:objection"}, target="Neg(nudge)")
    iv = move_intervention(m, tau=b.now + 1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "bridge": bridge(m)}


def C9_content_neutrality() -> dict:
    """The same protocol, on the conspiracy case, at the same structural class."""
    m = cc.conspiracy_influence()
    s = seed({"proto.designated": ri.PProto(trainer_protocol()),
              "val.low": PValue("v:th_natural")})
    b = en.CaseBuilder(m, s, narrative("authorized conspiracy", "B"))
    iv = move_intervention(m, tau=1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "bridge": bridge(m),
            "diana": C7_authorized_diana()}


def C10_manufactured_authorization() -> dict:
    """t0 the episode begins; t1 it produces the authority; t2 it is cited."""
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed(), narrative("manufactured authority", "B"))
    b.begin("E")
    b.settle("s:t0-manipulation")                              # tau 1
    b.reason("r:t1", s_L={"s:t0-manipulation"}, target="v:permit")
    b.norm("a:t1-install", CONST_CREATE, USER,
           wit=(ri.PProto(trainer_protocol("p:manufactured")),),
           leaves={"r:t1"})
    b.end()
    iv = move_intervention(m, tau=b.now + 1, episode="E")      # t2
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "protocol_standing": ri.standing_tag(3, 0)}


def C11_same_endpoint() -> dict:
    """Two trajectories to one cognitive endpoint; two different provenances."""
    m = cc.conspiracy_influence()

    s = seed({"val.low": PValue("v:th_natural")})
    a = en.CaseBuilder(m, s, narrative("reflective arm", "B"))
    a.settle("s:own-reflection")
    a.reason("r:reflective", s_L={"s:own-reflection"}, target="v:th_influenced")
    a.norm("a:uptake", SELF_REVISION, USER,
           wit=("revise", {"val.low"}, (PValue("v:th_influenced"),)),
           leaves={"r:reflective"})

    c = en.CaseBuilder(m, seed({"val.low": PValue("v:th_natural")}),
                       narrative("manipulated arm", "B"))
    c.begin("E")
    c.settle("s:manipulation")
    c.end()
    c.reason("r:manipulated", s_L={"s:manipulation"}, target="v:th_influenced")
    c.norm("a:uptake", SELF_REVISION, USER,
           wit=("revise", {"val.low"}, (PValue("v:th_influenced"),)),
           leaves={"r:manipulated"})

    return {"reflective": a.build(), "manipulated": c.build(),
            "event": "a:uptake", "episode": "E"}


def C12_conclusion_neutrality() -> dict:
    """One licensed procedure, two conclusions, neither built into the schema."""
    m = cc.writers_curse()
    out = {}
    for label, wit in (("revise", ("revise", {"val.low"},
                                   (PValue("v:th_unhappy"),))),
                       ("keep", ("keep", {"val.low"}))):
        b = en.CaseBuilder(m, seed({"val.low": PValue("v:th_ambitious")}),
                           narrative(f"procedure/{label}", "D"))
        b.settle("s:finding")
        b.reason("r:finding", s_L={"s:finding"}, target="v:conclusion")
        b.norm("a:procedure", SELF_REVISION, USER, wit=wit, leaves={"r:finding"})
        out[label] = b.build()
    return out


def _alice_mdp() -> drmdp.DRMDP:
    """A structural copy of the two-node gadget, under neutral labels.

    The introduction's example is not one of the five figures, so it gets the
    structure the figures share rather than a new one, and its labels say
    nothing the criterion reads.
    """
    return drmdp.relabel(cc.conspiracy_influence(),
                         {cc.S0: "s_0"},
                         {cc.TH_NATURAL: "th_prior", cc.TH_INFLUENCED: "th_later"},
                         {cc.NOOP: "a_hold", cc.INFLUENCE: "a_move"})


def C13_precommitment() -> dict:
    """A later request is settled and reasoned from; no event supersedes."""
    m = _alice_mdp()
    b = en.CaseBuilder(m, seed({"val.prior": PValue("v:th_prior")}),
                       narrative("precommitment", "A"))
    b.settle("s:later-request")
    b.reason("r:later-request", s_L={"s:later-request"}, target="v:th_later")
    iv = move_intervention(m, tau=b.now + 1, episode=None)
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "bridge": bridge(m)}


def C14_legitimate_revision() -> dict:
    """The same request, plus an independently grounded reflective procedure."""
    m = _alice_mdp()
    b = en.CaseBuilder(m, seed({"val.prior": PValue("v:th_prior")}),
                       narrative("legitimate revision", "A"))
    b.settle("s:later-request")
    b.reason("r:later-request", s_L={"s:later-request"}, target="v:th_later")
    b.norm("a:revision", SELF_REVISION, USER,
           wit=("revise", {"val.prior"}, (PValue("v:th_later"),)),
           leaves={"r:later-request"})
    return {"case": b.build(), "event": "a:revision", "bridge": bridge(m)}


def C15_writers_curse_disavowal() -> dict:
    """An initially endorsed course, later disavowed on independent grounds."""
    m = cc.writers_curse()
    b = en.CaseBuilder(m, seed({"val.ambitious": PValue("v:th_ambitious")}),
                       narrative("writer's curse", "D"))
    b.settle("s:unhappiness")
    b.reason("r:unhappiness", s_L={"s:unhappiness"}, target="v:th_unhappy")
    b.norm("a:disavowal", SELF_REVISION, USER,
           wit=("revise", {"val.ambitious"}, (PValue("v:th_unhappy"),)),
           leaves={"r:unhappiness"})
    return {"case": b.build(), "event": "a:disavowal", "bridge": bridge(m)}


def C16_clickbait() -> dict:
    """The change the action caused is what later rewards repeating it."""
    m = cc.clickbait()
    b = en.CaseBuilder(m, seed(), narrative("clickbait", "user"))
    b.begin("E")
    b.settle("s:served")
    b.reason("r:now-prefers", s_L={"s:served"}, target="v:permit")
    b.norm("a:install", CONST_CREATE, USER,
           wit=(ri.PProto(trainer_protocol("p:from-preference")),),
           leaves={"r:now-prefers"})
    b.end()
    iv = en.Intervention("I", AI, cc.CLICKBAIT, cc.TH_NORMAL,
                         cc.TH_DISILLUSIONED, b.now + 1, "E",
                         frozenset({WINDOW}))
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def C17_non_conservatism() -> dict:
    """The licensed nudge, and the policy that performs it."""
    src = C7_authorized_diana()
    m = src["case"].dr_mdp
    H = cc.HORIZON["AIPersonalTrainer"]
    policy = {pt: cc.NUDGE for pt in drmdp.reachable_points(m, H)}
    return {"case": src["case"], "iv": src["iv"], "policy": policy,
            "H": H, "a_noop": cc.NOOP}


def C19_dehydration() -> dict:
    m = cc.dehydration()
    b = en.CaseBuilder(m, seed(), narrative("dehydration", "C"))
    iv = en.Intervention("I", AI, cc.A3, 2, 3, 1, None, frozenset({WINDOW}))
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def C20_conflicting_authority() -> dict:
    m = cc.ai_personal_trainer()
    s = seed({"proto.permit": ri.PProto(trainer_protocol("p:permit")),
              "proto.forbid": ri.PProto(trainer_protocol("p:forbid",
                                                         polarity="forbid"))})
    b = en.CaseBuilder(m, s, narrative("conflicting authority", "D"))
    iv = move_intervention(m, tau=1, episode=None)
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def C21_revocation() -> dict:
    """The covering protocol is legitimately superseded before the act."""
    m = cc.ai_personal_trainer()
    s = seed({"proto.designated": ri.PProto(trainer_protocol())})
    b = en.CaseBuilder(m, s, narrative("revocation", "D"))
    b.settle("s:revocation-request")
    b.reason("r:revocation", s_L={"s:revocation-request"}, target="v:revoke")
    b.norm("a:revoke", SELF_REVISION, USER,
           wit=("revise", {"proto.designated"},
                (ri.PProto(en.Protocol("p:successor", AI, frozenset())),)),
           leaves={"r:revocation"})
    iv = move_intervention(m, tau=b.now + 1, episode=None)
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def C22_inquiry_laundering() -> dict:
    """A real later fact, authentically settled, and still not a prior license."""
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed(), narrative("inquiry laundering", "B"))
    b.begin("E")
    b.settle("s:manipulation")
    b.settle("s:answer", refs={"s:manipulation"})     # the reply, authentic
    b.end()
    b.reason("r:answer", s_L={"s:answer"}, target="v:permit")
    b.norm("a:install", CONST_CREATE, USER,
           wit=(ri.PProto(trainer_protocol("p:from-answer")),),
           leaves={"r:answer"})
    iv = move_intervention(m, tau=b.now + 1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def C23_proxy() -> dict:
    """Another actor performs the change; the provenance still records it."""
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed(), narrative("proxy manipulation", "B"))
    b.begin("E")
    b.settle("s:proxy-acts")
    b.end()
    b.reason("r:proxy", s_L={"s:proxy-acts"}, target="v:permit")
    b.norm("a:install", CONST_CREATE, PROXY,
           wit=(ri.PProto(trainer_protocol("p:via-proxy")),),
           leaves={"r:proxy"})
    iv = move_intervention(m, tau=b.now + 1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def C24_incidental() -> dict:
    """An authority in another domain, and an effect on the parameterization."""
    m = cc.ai_personal_trainer()
    s = seed({"proto.task": ri.PProto(
        trainer_protocol("p:task", domain="task-completion"))})
    b = en.CaseBuilder(m, s, narrative("incidental influence", "D"))
    iv = move_intervention(m, tau=1, episode=None)
    b.declare(iv)
    H = cc.HORIZON["AIPersonalTrainer"]
    policy = {pt: cc.NUDGE for pt in drmdp.reachable_points(m, H)}
    return {"case": b.build(), "iv": iv, "policy": policy, "H": H,
            "a_noop": cc.NOOP}


def C7b_delegated_authorization() -> dict:
    """A license whose basis was installed during the record, not seeded.

    The prompt's under-generality test: if the only route to `Licensed` were an
    explicit prior consent standing in the seed, the criterion would be a consent
    theory. Here the covering basis is installed at `tau = 3` by an ordinary
    licensed event grounded in a settlement outside every influence episode —
    a delegated procedure rather than an act of consent — and the intervention
    that cites it is inside one.
    """
    m = cc.ai_personal_trainer()
    b = en.CaseBuilder(m, seed(), narrative("delegated authorization", "D"))
    b.settle("s:procedure-outcome")
    b.reason("r:procedure", s_L={"s:procedure-outcome"}, target="v:delegate")
    b.norm("a:delegate", CONST_CREATE, USER,
           wit=(ri.PProto(trainer_protocol("p:delegated")),),
           leaves={"r:procedure"})
    b.begin("E")
    b.settle("s:nudge")
    b.end()
    iv = move_intervention(m, tau=b.now + 1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def C25_split_episode(linked: bool = True) -> dict:
    """The campaign run as two episodes, with the second one cited.

    Not in the dispatched list. The round built it because the counterfactual as
    first written removed one declared episode, and an agent that splits its
    campaign keeps whatever the first half installed. `linked` records the
    reference from the second episode's settlement to the first's; without it
    the record says the two are causally unrelated and the criterion has nothing
    to go on. Both arms are run.
    """
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed(), narrative("split episode", "B"))
    b.begin("E1")
    b.settle("s:e1-manipulation")
    b.end()
    b.reason("r:e1", s_L={"s:e1-manipulation"}, target="v:permit")
    b.norm("a:install", CONST_CREATE, USER,
           wit=(ri.PProto(trainer_protocol("p:manufactured")),),
           leaves={"r:e1"})
    b.begin("E2")
    b.settle("s:e2-act", refs={"s:e1-manipulation"} if linked else frozenset())
    b.end()
    iv = move_intervention(m, tau=b.now + 1, episode="E2")
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "linked": linked}


def C26_manufactured_condition(inside: bool = True) -> dict:
    """The basis is genuinely independent; its trigger is not.

    Not in the dispatched list. The protocol is seeded, so it survives every
    excision; what the episode manufactures is the fact its applicability
    condition reads. `inside` puts the settlement establishing that fact inside
    the episode; the other arm is the control.
    """
    m = cc.ai_personal_trainer()
    s = seed({"proto.designated": ri.PProto(trainer_protocol())})
    b = en.CaseBuilder(m, s, narrative("manufactured condition", "D"))
    if inside:
        b.begin("E")
    b.settle("s:condition", establishes={WINDOW})
    if inside:
        b.end()
    iv = en.Intervention("I", AI, m.actions[1], m.thetas[0], m.thetas[1],
                         b.now + 1, "E", frozenset())
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "inside": inside}


def C27_unlabelled_intermediate() -> dict:
    """The two halves of a campaign joined through an unlabelled settlement.

    Not in the dispatched list. `C25` forced the counterfactual to close over
    episodes; this forces it to close in the settlement graph and project
    afterwards. The chain is

    ```text
    s2 in E2   ->refs->   s_mid in no episode   ->refs->   s1 in E1
    ```

    and an episode-to-episode walk one reference deep never reaches `E1`.
    """
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed(), narrative("unlabelled intermediate", "B"))
    b.begin("E1")
    b.settle("s1")
    b.end()
    b.reason("r:e1", s_L={"s1"}, target="v:permit")
    b.norm("a:install", CONST_CREATE, USER,
           wit=(ri.PProto(trainer_protocol("p:manufactured")),), leaves={"r:e1"})
    b.settle("s_mid", refs={"s1"})                  # belongs to no episode
    b.begin("E2")
    b.settle("s2", refs={"s_mid"})
    b.end()
    iv = move_intervention(m, tau=b.now + 1, episode="E2")
    b.declare(iv)
    return {"case": b.build(), "iv": iv}


def _minting_schema(prestate_reading: bool) -> ri.SchemaCode:
    """A schema that creates an authority, optionally reading the pre-state.

    S1-S6 permit a schema to be any deterministic function of the witness *and
    the strict pre-state*, so the payload of a standing an event creates can
    depend on what the record held at that moment. That is the whole content of
    `C28`.
    """
    def run(wit, pre):
        name = f"minted-{len(pre.R)}" if prestate_reading else "minted"
        return ri.Standing(ri.Create((ri.PAuth(ri.SchemaCode(name, _supersede)),)))
    return ri.SchemaCode("mint", run)


MINT = "const.mint"


def C28_prestate_reading_schema(prestate_reading: bool = True) -> dict:
    """Does event survival already imply the authority it named is independent?

    Not in the dispatched list. The succession criterion carries two clauses and
    the second looks like it might follow from the third. It does not, and the
    separator is exactly whether schemas read the pre-state: the event survives
    excision under both arms, and under the reading arm the authority it names
    comes back carrying a different code.
    """
    m = cc.conspiracy_influence()
    s = seed({MINT: ri.PAuth(_minting_schema(prestate_reading)),
              "val.low": PValue("v:th_natural")})
    b = en.CaseBuilder(m, s, narrative("minted authority", "B"))
    b.begin("E")
    b.settle("s:manip")
    b.end()
    b.reason("r:from-manip", s_L={"s:manip"}, target="v:th_influenced")
    b.norm("a:mint", MINT, USER)
    minted = ri.standing_tag(3, 0)
    b.norm("a:use", minted, USER,
           wit=({"val.low"}, (PValue("v:th_influenced"),)))
    return {"case": b.build(), "event": "a:use", "episode": "E",
            "authority": minted, "prestate_reading": prestate_reading}


def C29_verdict_grounds() -> dict:
    """One minimal case per ground, so every branch of the case distinction runs."""
    m = cc.ai_personal_trainer()

    def probe(extra, **iv_kwargs):
        b = en.CaseBuilder(m, seed(extra), narrative("ground probe", "D"))
        iv = move_intervention(m, tau=1, **iv_kwargs)
        b.declare(iv)
        return {"case": b.build(), "iv": iv}

    return {
        "independent-permission": probe(
            {"proto.permit": ri.PProto(trainer_protocol())}),
        "independent-prohibition": probe(
            {"proto.forbid": ri.PProto(
                trainer_protocol("p:forbid", polarity="forbid"))}),
        "conflict": C20_conflicting_authority(),
        "wrong-agent": probe({"proto.alice": ri.PProto(
            trainer_protocol("p:alice", agent="Alice"))}),
        "condition-unmet": probe({"proto.cond": ri.PProto(trainer_protocol())},
                                 facts=frozenset()),
        "revoked": C21_revocation(),
        "manufactured": C10_manufactured_authorization(),
        "no-covering-basis": C6_bare_diana(),
    }


F_EXO, F_EPISODIC = "f:exogenous-condition", "f:episodic-condition"


def C30_applicability_boundary(arm: str) -> dict:
    """Where a protocol's condition is discharged from, five ways.

    Not in the dispatched list in this form. `C26` showed a wholly manufactured
    trigger is not enough; these are the boundary cases around it. The criterion
    has to turn on whether the condition is still discharged in the excised
    record, not on whether a syntactically similar fact was ever present.
    """
    m = cc.ai_personal_trainer()
    needs = {"inside": {F_EPISODIC}, "outside": {F_EXO},
             "mixed": {F_EXO, F_EPISODIC}, "re-established": {F_EXO},
             "two-routes": {F_EXO}}[arm]
    s = seed({"proto.designated": ri.PProto(
        trainer_protocol(condition=frozenset(needs)))})
    b = en.CaseBuilder(m, s, narrative(f"applicability/{arm}", "D"))
    if arm in ("outside", "mixed", "re-established", "two-routes"):
        b.settle("s:exogenous", establishes={F_EXO})
    if arm in ("inside", "mixed"):
        b.begin("E")
        b.settle("s:episodic", establishes={F_EPISODIC})
        b.end()
    if arm == "re-established":
        b.begin("E")
        b.settle("s:again", establishes={F_EXO})       # the same fact, restated
        b.end()
    if arm == "two-routes":
        b.begin("E")
        b.settle("s:route-two", establishes={F_EXO})   # a second, dependent route
        b.end()
    iv = en.Intervention("I", AI, m.actions[1], m.thetas[0], m.thetas[1],
                         b.now + 1, "E", frozenset())
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "arm": arm}


def _two_context_mdp() -> drmdp.DRMDP:
    """One reward-parameterization edge reachable from two different states.

    The smallest shape in which `intervention_class` is silent about context:
    `a_move` carries `th_0` to `th_1` from both `s_a` and `s_b`, so the two
    interventions share a class and differ in the state acted from.
    """
    S, TH, A = ("s_a", "s_b"), ("th_0", "th_1"), ("a_hold", "a_move")

    def T(s, th, a):
        return (s, TH[1] if a == A[1] else th)

    def R(th, s, a, s2):
        return 1 if th == TH[1] else 0

    return drmdp.build(S, TH, A, T, R, S[0], TH[0])


F_CONTEXT = "f:acting-from-the-first-state"


def C31_covers_context(established: bool) -> dict:
    """Two interventions of one class, in two contexts, and one authority.

    Not in the dispatched list. `covers` names a class and says nothing about
    the state acted from; the question is whether the existing `condition` field
    reaches the distinction without widening the class.
    """
    m = _two_context_mdp()
    s = seed({"proto.contextual": ri.PProto(
        en.Protocol("p:contextual", AI, frozenset({(1, 0, 1)}),
                    frozenset({F_CONTEXT})))})
    b = en.CaseBuilder(m, s, narrative("contextual authority", "x"))
    if established:
        b.settle("s:context", establishes={F_CONTEXT})
    iv = en.Intervention("I", AI, m.actions[1], m.thetas[0], m.thetas[1],
                         b.now + 1, None, frozenset())
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "class": en.intervention_class(m, iv)}


def C32_license_without_standing() -> dict:
    """A licensed intervention, and no specification in force for its result.

    The separation stated as its own fixture rather than left implicit in `C7`.
    The record contains the authority and the act; it contains no event
    installing a specification of the parameterization the act produces.
    """
    m = cc.ai_personal_trainer()
    s = seed({"proto.designated": ri.PProto(trainer_protocol()),
              "val.low": PValue("v:th_tired")})
    b = en.CaseBuilder(m, s, narrative("license without standing", "D"))
    b.begin("E")
    b.settle("s:nudge")
    b.end()
    iv = move_intervention(m, tau=1, episode="E")
    b.declare(iv)
    return {"case": b.build(), "iv": iv, "bridge": bridge(m)}


def C33_standing_without_license() -> dict:
    """An unlicensed influence, and the same value later installed independently.

    The converse separation, and the sharper of the two: the later installation
    is legitimate, the specification it installs is the one the influence
    produced, and the influence is still not licensed. A verdict about an act at
    `tau` is a verdict about the pre-state at `tau`, so nothing later reaches it.
    """
    m = cc.conspiracy_influence()
    s = seed({"val.low": PValue("v:th_natural")})
    b = en.CaseBuilder(m, s, narrative("standing without license", "B"))
    b.begin("E")
    b.settle("s:influence")
    b.end()
    iv = move_intervention(m, tau=1, episode="E")
    b.declare(iv)
    b.settle("s:own-reflection")                     # outside every episode
    b.reason("r:reflective", s_L={"s:own-reflection"}, target="v:th_influenced")
    b.norm("a:adoption", SELF_REVISION, USER,
           wit=("revise", {"val.low"}, (PValue("v:th_influenced"),)),
           leaves={"r:reflective"})
    return {"case": b.build(), "iv": iv, "event": "a:adoption", "episode": "E",
            "bridge": bridge(m)}


def _parity_schema() -> ri.SchemaCode:
    """Admissible exactly when the pre-state holds an even number of reasons.

    Legal under S1-S6: deterministic, read-only, well-typed, strict pre-state.
    Returning `None` is what `G5` rejects, so admissibility here is a
    non-monotone function of the record — which is the whole point.
    """
    def run(wit, pre):
        if len(pre.R) % 2:
            return None
        return ri.Standing(ri.Create((ri.PProto(en.Protocol("p:parity", AI,
                                                            frozenset())),)))
    return ri.SchemaCode("parity", run)


PARITY = "const.parity"


def nonmonotone_case() -> en.RichCarrollCase:
    """Removing more can restore an occurrence that removing less destroyed.

    Two episodes, one reason grounded in each, and an event admissible only at an
    even reason count. Excising one episode leaves an odd count and the event
    falls; excising both leaves zero and it stands. The witness for the failure of

    ```text
    E subset of E'  ->  Survivors(E') subset of Survivors(E)
    ```

    and, with the same steps, for the failure of composition.
    """
    m = cc.conspiracy_influence()
    b = en.CaseBuilder(m, seed({PARITY: ri.PAuth(_parity_schema())}),
                       narrative("non-monotone admissibility", "x"))
    b.begin("E1")
    b.settle("s1")
    b.end()
    b.begin("E2")
    b.settle("s2")
    b.end()
    b.reason("r1", s_L={"s1"}, target="t1")
    b.reason("r2", s_L={"s2"}, target="t2")
    b.norm("a:parity", PARITY, USER)
    return b.build()


# ------------------------------------------------------------- the strawmen


def author_matching_license(case: en.RichCarrollCase,
                            iv: en.Intervention) -> bool:
    """Refuse only a basis the acting agent itself created.

    The rule an identity-matching account would use. `C10` and `C23` are the
    two shapes it licenses and the criterion refuses.
    """
    h = case.history()
    std = h.std(iv.tau - 1)
    ok, _ = lg.authority(case, iv, std, "permit")
    creator = {}
    for a in h.norm_events():
        for x in ri.fresh_n(ri.ctx_of(a), h.effect(a)):
            creator[x] = a.author
    return any(creator.get(b.standing_id) != iv.agent for b in ok)
