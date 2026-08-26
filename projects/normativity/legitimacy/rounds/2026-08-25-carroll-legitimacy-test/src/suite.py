"""C0 to C34, run once, as data.

`run()` returns one row per case: what was observed, what the case demanded, and
whether the demand was met. `tests/test_adversarial.py` asserts the rows and
`report.py` renders them, so the matrix in the documents and the matrix the
tests check are the same object.

`demand` is a property of the observation, never a hardcoded verdict string, so
a case cannot pass by being told what to expect.

`C0`-`C24` are the dispatched suite. `C7b` and `C25`-`C33` are cases the round
added: `C7b` against the prompt's own under-generality test, and the rest as
attacks. `C25`, `C26`, `C27` and the closed-world reading `C29` pins each killed a
version of the criterion.
"""
from __future__ import annotations

import carroll_cases as cc
import drmdp
import enrichment as en
import fixtures as F
import legitimacy as lg
import objectives as ob
import old_interface as oi
import table4
import variations as V

PASS, FAIL, UNRESOLVED = "PASS", "FAIL", "UNRESOLVED"


def _row(cid, title, observed, demand, note):
    return {"id": cid, "title": title, "observed": observed,
            "result": PASS if demand else FAIL, "note": note}


def C0():
    miss = table4.mismatches()
    over = [(c, n) for c, n, r in miss if r.get("quantified")
            and not r.get("stated_theta0")]
    return _row("C0", "exact Carroll fidelity",
                f"{len(table4.rows()) - len(miss)}/{len(table4.rows())} cells recovered",
                len(miss) == len(over) == 2,
                "the two exceptions are Table 4's cells quantified over a "
                "theta_0 other than the example's own")


def C1():
    d = F.C1_dr_equivalence()
    same = d["canonical_bob"] == d["canonical_diana"]
    return _row("C1", "DR-equivalent narratives",
                f"canonical forms equal: {same}", same,
                "Figures 1 and 6 are one DR-MDP under a relabelling of all "
                "three alphabets")


def C2():
    d = F.C2_bare_negative_control()
    vb = lg.prospective_license(d["bob"]["case"], d["bob"]["iv"])
    vd = lg.prospective_license(d["diana"]["case"], d["diana"]["iv"])
    return _row("C2", "bare negative control",
                f"{vb.status} / {vd.status}",
                vb.status == vd.status == lg.UNRESOLVED,
                "no enriched difference, no verdict difference")


def C3():
    """Relabelled twice: once with an exogenous condition, once with a settled one.

    The second arm is the one that matters. A case whose applicability condition
    is discharged from the record rather than declared exogenous exercises the
    settled-fact map, and `relabel_case` used to drop it — which would have made
    this invariance accidentally true on the first arm and false on the second.
    """
    rows = []
    for src in (F.C3_relabelling(),
                F.C3_relabelling(F.C30_applicability_boundary("outside"))):
        a = lg.prospective_license(src["original"]["case"], src["original"]["iv"])
        b = lg.prospective_license(src["case"], src["iv"])
        rows.append(((a.status, a.ground, a.bases), (b.status, b.ground, b.bases)))
    return _row("C3", "relabelling",
                "; ".join(f"{x[0]}->{y[0]}" for x, y in rows),
                all(x == y for x, y in rows)
                and rows[0][0][0] == lg.LICENSED and rows[1][0][0] == lg.LICENSED,
                "labels renamed, record untouched, verdict fixed — including "
                "where the condition is discharged from a settled fact")


def C4():
    d = F.C4_self_ratifying()
    v = lg.prospective_license(d["case"], d["iv"])
    approved = lg.final_approval(d["case"], d["iv"], d["bridge"])
    return _row("C4", "self-ratifying influence",
                f"{v.status}; final approval={approved}",
                v.status != lg.LICENSED and approved,
                "the produced specification is in force and the act is still "
                "not licensed")


def C5():
    d = F.C5_ri_good_manipulation()
    h = d["case"].history()
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C5", "RI-good manipulation",
                f"RI good={h.good()}; {v.status}/{v.ground}",
                h.good() and v.status != lg.LICENSED and v.ground == lg.DEFEATED,
                "a clean record is not a license")


def C6():
    d = F.C6_bare_diana()
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C6", "bare Diana", v.status, v.status == lg.UNRESOLVED,
                "beneficial-sounding content earns nothing")


def C7():
    d = F.C7_authorized_diana()
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C7", "independently authorized Diana", v.status,
                v.status == lg.LICENSED, "the positive witness")


def C7b():
    d = F.C7b_delegated_authorization()
    v = lg.prospective_license(d["case"], d["iv"])
    seeded = "p:delegated" in {p.id for p in d["case"].seed.std0.values()
                               if isinstance(p, en.Protocol)}
    return _row("C7b", "delegated authorization",
                f"{v.status}; basis in the seed={seeded}",
                v.status == lg.LICENSED and not seeded,
                "the route to a license is an active covering basis, however "
                "it was installed, and not an act of prior consent")


def C8():
    d = F.C8_current_self_disagreement()
    v = lg.prospective_license(d["case"], d["iv"])
    objected = lg.initial_disapproval(d["case"], d["iv"], d["bridge"])
    return _row("C8", "current-self disagreement",
                f"{v.status}; prior specification in force={objected}",
                v.status == lg.LICENSED and objected,
                "current preference does not always win")


def C9():
    d = F.C9_content_neutrality()
    vb = lg.prospective_license(d["case"], d["iv"])
    vd = lg.prospective_license(d["diana"]["case"], d["diana"]["iv"])
    return _row("C9", "content neutrality", f"{vb.status} / {vd.status}",
                vb.status == vd.status == lg.LICENSED,
                "the same structure, the same answer, whatever the story")


def C10():
    d = F.C10_manufactured_authorization()
    v = lg.prospective_license(d["case"], d["iv"])
    naive = lg.temporal_priority_license(d["case"], d["iv"])
    ident = F.author_matching_license(d["case"], d["iv"])
    return _row("C10", "manufactured authorization",
                f"{v.status}/{v.ground}; temporal-priority={naive}; "
                f"author-matching={ident}",
                v.status != lg.LICENSED and v.ground == lg.DEFEATED
                and naive and ident,
                "both weaker rules license it")


def C11():
    d = F.C11_same_endpoint()
    ends = (lg.current_standing(d["reflective"]),
            lg.current_standing(d["manipulated"]))
    a = lg.legitimate_succession(d["reflective"], d["event"], d["episode"])
    b = lg.legitimate_succession(d["manipulated"], d["event"], d["episode"])
    return _row("C11", "same endpoint, different history",
                f"standing {sorted(ends[0])} == {sorted(ends[1])}; "
                f"{a.status} / {b.status}",
                ends[0] == ends[1] and a.status == lg.LICENSED
                and b.status != lg.LICENSED,
                "succession is path-sensitive where the endpoint is not")


def C12():
    d = F.C12_conclusion_neutrality()
    out = {k: (sorted(lg.current_standing(v)),
               lg.legitimate_succession(v, "a:procedure").status)
           for k, v in d.items()}
    return _row("C12", "same procedure, opposite outcome",
                "; ".join(f"{k}: {s} {v}" for k, (s, v) in sorted(out.items())),
                all(v == lg.LICENSED for _, v in out.values())
                and out["revise"][0] != out["keep"][0],
                "neither conclusion is built into the schema")


def C13():
    d = F.C13_precommitment()
    standing = lg.current_standing(d["case"])
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C13", "precommitment",
                f"standing {sorted(standing)}; {v.status}",
                standing == frozenset({"v:th_prior"})
                and v.status != lg.LICENSED,
                "a later request is not a supersession")


def C14():
    d = F.C14_legitimate_revision()
    standing = lg.current_standing(d["case"])
    v = lg.legitimate_succession(d["case"], d["event"])
    return _row("C14", "legitimate revision",
                f"standing {sorted(standing)}; {v.status}",
                standing == frozenset({"v:th_later"}) and v.status == lg.LICENSED,
                "no lock-in: the earlier standing can be superseded")


def C15():
    d = F.C15_writers_curse_disavowal()
    standing = lg.current_standing(d["case"])
    v = lg.legitimate_succession(d["case"], d["event"])
    return _row("C15", "Writer's Curse disavowal",
                f"standing {sorted(standing)}; {v.status}",
                standing == frozenset({"v:th_unhappy"})
                and v.status == lg.LICENSED,
                "prior authority is not permanent")


def C16():
    d = F.C16_clickbait()
    v = lg.prospective_license(d["case"], d["iv"])
    m, H = cc.clickbait(), cc.HORIZON["Clickbait"]
    rt = ob.argmax(m, H, ob.u_real_time, cc.NEWS)
    takes_clickbait = any(cc.CLICKBAIT in p.values() for p in rt)
    return _row("C16", "clickbait",
                f"{v.status}; real-time optimum serves clickbait={takes_clickbait}",
                v.status != lg.LICENSED and v.ground == lg.DEFEATED
                and takes_clickbait,
                "the criterion and the real-time objective disagree here")


def C17():
    d = F.C17_non_conservatism()
    v = lg.prospective_license(d["case"], d["iv"])
    infl = lg.influence(d["case"].dr_mdp, d["policy"], d["H"], d["a_noop"])
    return _row("C17", "non-conservatism", f"{v.status}; influences={infl}",
                v.status == lg.LICENSED and infl,
                "a licensed intervention that moves the reward evolution")


def C18():
    d = F.C17_non_conservatism()
    cons = ob.constrained_policies(d["case"].dr_mdp, d["H"], d["a_noop"])
    inside = any(ob.key(p) == ob.key(d["policy"]) for p in cons)
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C18", "natural evolution is not authority",
                f"{v.status}; in the constrained set={inside}",
                v.status == lg.LICENSED and not inside,
                "the criterion licenses what the constrained objective forbids")


def C19():
    d = F.C19_dehydration()
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C19", "dehydration", v.status, v.status == lg.UNRESOLVED,
                "a genuinely ambiguous case returns insufficient structure")


def C20():
    d = F.C20_conflicting_authority()
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C20", "conflicting live authority",
                f"{v.status}: {v.reason}",
                v.status == lg.UNRESOLVED and "conflict" in v.reason,
                "neither basis is silently preferred")


def C21():
    d = F.C21_revocation()
    v = lg.prospective_license(d["case"], d["iv"])
    return _row("C21", "revocation",
                f"{v.status}/{v.ground}; blocked={[b[1] for b in v.blocked]}",
                v.status != lg.LICENSED and v.ground == lg.DEFEATED
                and ("proto.designated", "not live") in v.blocked,
                "historical authorization is insufficient, and a lapsed permit "
                "is an absent permission rather than a prohibition")


def C22():
    d = F.C22_inquiry_laundering()
    h = d["case"].history()
    v = lg.prospective_license(d["case"], d["iv"])
    authentic = "s:answer" in {s.id for s in h.settlements()}
    return _row("C22", "inquiry laundering",
                f"{v.status}; the reply is on the ledger={authentic}; "
                f"RI good={h.good()}",
                v.status != lg.LICENSED and v.ground == lg.DEFEATED
                and authentic and h.good(),
                "a real later fact, and still not a prior license")


def C23():
    d = F.C23_proxy()
    v = lg.prospective_license(d["case"], d["iv"])
    ident = F.author_matching_license(d["case"], d["iv"])
    authors = {a.author for a in d["case"].history().norm_events()}
    return _row("C23", "proxy manipulation",
                f"{v.status}; authors={sorted(authors)}; author-matching={ident}",
                v.status != lg.LICENSED and v.ground == lg.DEFEATED
                and F.AI not in authors and ident,
                "the influence structure is tracked, not the actor's name")


def C24():
    d = F.C24_incidental()
    v = lg.prospective_license(d["case"], d["iv"])
    infl = lg.influence(d["case"].dr_mdp, d["policy"], d["H"], d["a_noop"])
    domains = {b: None for b in v.bases}
    std = d["case"].history().std(d["iv"].tau - 1)
    dom = {p.domain for x, p in en.active_protocols(std) if x in domains}
    return _row("C24", "benign incidental influence",
                f"{v.status}; influences={infl}; basis domain={sorted(dom)}",
                v.status == lg.LICENSED and infl
                and dom == {"task-completion"},
                "causal influence alone does not defeat a license")


def C25():
    linked = F.C25_split_episode(linked=True)
    unlinked = F.C25_split_episode(linked=False)
    a = lg.prospective_license(linked["case"], linked["iv"])
    b = lg.prospective_license(unlinked["case"], unlinked["iv"])
    return _row("C25", "split episode",
                f"linked={a.status}/{a.ground}; unlinked={b.status}",
                a.status != lg.LICENSED and a.ground == lg.DEFEATED
                and b.status == lg.LICENSED,
                "the counterfactual closes over the record's own settlement "
                "references; an unrecorded link is a record defect the "
                "criterion cannot see, and this is its witness")


def C26():
    inside = F.C26_manufactured_condition(inside=True)
    outside = F.C26_manufactured_condition(inside=False)
    a = lg.prospective_license(inside["case"], inside["iv"])
    b = lg.prospective_license(outside["case"], outside["iv"])
    return _row("C26", "manufactured applicability",
                f"trigger inside={a.status}/{a.ground}; outside={b.status}",
                a.status != lg.LICENSED and a.ground == lg.DEFEATED
                and b.status == lg.LICENSED,
                "a seeded basis survives every excision, so the counterfactual "
                "has to reach the facts its condition reads")


def C27():
    d = F.C27_unlabelled_intermediate()
    v = lg.prospective_license(d["case"], d["iv"])
    reached = sorted(en.ancestry(d["case"], "E2"))
    return _row("C27", "unlabelled intermediate",
                f"{v.status}/{v.ground}; ancestry(E2)={reached}",
                v.status != lg.LICENSED and v.ground == lg.DEFEATED
                and reached == ["E1", "E2"],
                "the counterfactual closes in the settlement graph and projects "
                "to episodes afterwards; an episode-to-episode walk missed this")


def C28():
    reading = F.C28_prestate_reading_schema(prestate_reading=True)
    blind = F.C28_prestate_reading_schema(prestate_reading=False)
    out = {}
    for name, d in (("reading", reading), ("blind", blind)):
        out[name] = (
            lg.survives_excision(d["case"], d["event"], d["episode"]),
            lg.independent(d["case"], d["authority"], d["episode"], 4),
            lg.legitimate_succession(d["case"], d["event"], d["episode"]).status)
    return _row("C28", "pre-state-reading schema",
                "; ".join(f"{k}: survives={v[0]} independent={v[1]} {v[2]}"
                          for k, v in sorted(out.items())),
                out["reading"][0] and not out["reading"][1]
                and out["blind"][0] and out["blind"][1],
                "event survival does not imply the authority it named is "
                "independent, so the succession clauses are not redundant; the "
                "separator is whether schemas read the strict pre-state")


def C29():
    grounds = F.C29_verdict_grounds()
    got = {name: lg.prospective_license(d["case"], d["iv"]).ground
           for name, d in grounds.items()}
    expected = {
        "independent-permission": lg.PERMISSION,
        "independent-prohibition": lg.PROHIBITION,
        "conflict": lg.CONFLICT,
        "wrong-agent": lg.DEFEATED,
        "condition-unmet": lg.DEFEATED,
        "revoked": lg.DEFEATED,
        "manufactured": lg.DEFEATED,
        "no-covering-basis": lg.NO_BASIS,
    }
    statuses = {lg.STATUS_OF_GROUND[g] for g in got.values()}
    return _row("C29", "the three-valued case distinction",
                "; ".join(f"{k}->{v}" for k, v in sorted(got.items())),
                got == expected and statuses == {lg.LICENSED, lg.REFUSED,
                                                 lg.UNRESOLVED},
                "Refused is reserved for a live independent prohibition; "
                "absence of a permission is never a prohibition")


def C30():
    got = {}
    for arm in ("inside", "outside", "mixed", "re-established", "two-routes"):
        d = F.C30_applicability_boundary(arm)
        got[arm] = lg.prospective_license(d["case"], d["iv"]).status
    want = {"inside": lg.UNRESOLVED, "outside": lg.LICENSED,
            "mixed": lg.UNRESOLVED, "re-established": lg.LICENSED,
            "two-routes": lg.LICENSED}
    return _row("C30", "applicability boundary",
                "; ".join(f"{k}={v}" for k, v in sorted(got.items())),
                got == want,
                "the condition has to remain discharged in the excised record, "
                "which a fact restated inside the episode still is and a fact "
                "only ever established inside it is not")


def C31():
    on = F.C31_covers_context(established=True)
    off = F.C31_covers_context(established=False)
    a = lg.prospective_license(on["case"], on["iv"])
    b = lg.prospective_license(off["case"], off["iv"])
    return _row("C31", "one class, two contexts",
                f"class={on['class']}; context established={a.status}; "
                f"not established={b.status}",
                a.status == lg.LICENSED and b.status != lg.LICENSED
                and on["class"] == off["class"],
                "the existing condition field reaches a contextual distinction "
                "the intervention class does not carry, so the class was not "
                "widened")


def C32():
    d = F.C32_license_without_standing()
    v = lg.prospective_license(d["case"], d["iv"])
    resulting = lg.theta_has_standing(d["case"], cc.TH_ENERGIZED, d["bridge"])
    return _row("C32", "license without standing",
                f"{v.status}; the result has standing={resulting}",
                v.status == lg.LICENSED and not resulting,
                "a license is permission to act, not installation of what the "
                "act produces")


def C33():
    d = F.C33_standing_without_license()
    v = lg.prospective_license(d["case"], d["iv"])
    succ = lg.legitimate_succession(d["case"], d["event"], d["episode"])
    holds = lg.theta_has_standing(d["case"], cc.TH_INFLUENCED, d["bridge"])
    return _row("C33", "standing without license",
                f"intervention {v.status}/{v.ground}; succession {succ.status}; "
                f"the value has standing={holds}",
                v.status != lg.LICENSED and succ.status == lg.LICENSED and holds,
                "later legitimate adoption of the same value does not reach back "
                "and license the influence that first produced it")


def C34():
    """Standing restoration: excising more restores an event, blindly."""
    case = F.suspension_restoration_case()
    small = {a.id for a in en.excise(case, ["E1"]).norm_events()}
    large = {a.id for a in en.excise(case, ["E1", "E2"]).norm_events()}
    composed = {a.id for a in
                en.excise(en.excised_case(case, ["E1"]), ["E2"]).norm_events()}
    control = F.stance_restoration_case()
    stance_survives = "a:target" in {
        a.id for a in en.excise(control, ["E1"]).norm_events()}
    return _row("C34", "standing restoration under excision",
                f"good={case.history().good()}; excise E1={sorted(small)}; "
                f"excise E1+E2={sorted(large)}; composed={sorted(composed)}; "
                f"stance route reaches admission={not stance_survives}",
                case.history().good()
                and "a:target" not in small and "a:target" in large
                and composed != large and stance_survives,
                "pre-state-blindness buys neither monotonicity nor composition "
                "of excision; the stance route does not reach admission at all, "
                "because G2 reads ledger membership of reason ids")


CASES = [C0, C1, C2, C3, C4, C5, C6, C7, C7b, C8, C9, C10, C11, C12, C13, C14,
         C15, C16, C17, C18, C19, C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31, C32, C33, C34]


def run() -> list:
    return [case() for case in CASES]


def failures() -> list:
    return [r for r in run() if r["result"] != PASS]


# ------------------------------------------------ the two dictatorship tests


def dictatorship() -> list:
    """`FinalApproval` and `InitialDisapproval` decide nothing on their own."""
    out = []
    d4 = F.C4_self_ratifying()
    out.append(("FinalApproval(I) does not imply Licensed_t(I)",
                lg.final_approval(d4["case"], d4["iv"], d4["bridge"]),
                lg.prospective_license(d4["case"], d4["iv"]).status))
    d8 = F.C8_current_self_disagreement()
    out.append(("InitialDisapproval(I) does not imply not Licensed_t(I)",
                lg.initial_disapproval(d8["case"], d8["iv"], d8["bridge"]),
                lg.prospective_license(d8["case"], d8["iv"]).status))
    d14 = F.C14_legitimate_revision()
    out.append(("InitialStanding(v) does not imply ForeverAuthoritative(v)",
                "v:th_prior" in lg.current_standing(d14["case"], 0),
                sorted(lg.current_standing(d14["case"]))))
    return out


# -------------------------------------------------- the August 17 comparison


def old_interface_table() -> list:
    out = []
    for name, build in V.CLASSES.items():
        arms = build()
        cl = oi.clauses(arms)
        out.append({
            "class": name,
            "clauses": cl,
            "legitimate": oi.legitimate(arms),
            "trace_differs": oi.vacuous_pairs(arms),
        })
    return out
