"""The executor's specifications of the cases, authored here and written out as
spec_cases.json (what the runner reads) and SPEC_CASES.md (the same, for a reader).
Ratings below are in twentieths of the yardstick.  This file computes no line of the
statement.  Run: python3 -m account.spec_author (from the round directory)."""
from __future__ import annotations

import copy
import json
import pathlib
from fractions import Fraction

HERE = pathlib.Path(__file__).resolve().parent


def q(n):
    if n is None or isinstance(n, str):
        return n
    return str(Fraction(n, 20))


def Q(d):
    return {k: q(v) for k, v in d.items()}


def _per_state(d, conv):
    if all(isinstance(v, dict) for v in d.values()):
        return {s: conv(v) for s, v in d.items()}
    return {"*": conv(d)}


def pol(does, outcome, later, takes="top", r="Rs", obs=None, gain="0", xhat=None):
    p = {"does": does, "outcome": _per_state(outcome, dict)}
    if obs:
        p["obs"] = obs
    p["r"] = r if r == "Rs" else {lab: Q(v) for lab, v in r.items()}
    if xhat:
        p["xhat"] = xhat
    p["takes"] = takes
    if isinstance(later, str):
        p["later"] = later
    else:
        p["later"] = {s: [v] for s, v in _per_state(later, Q).items()}
    p["gain"] = gain if isinstance(gain, str) else _per_state(gain, dict)
    return p


def spec(id, set_, case, options, futures, policies, actual, nu, absent, states=None,
         facts=None, fixed=(), order=(), outside=None, supplied=None):
    s = {"id": id, "variant": "a", "set": set_, "case": case,
         "states": states or {"w": "1"}}
    if facts:
        s["facts"] = facts
    s.update(options=options, futures=Q(futures), policies=policies, actual=actual, nu=nu,
             absent=absent, fixed=[list(f) for f in fixed], order=[list(o) for o in order])
    if outside:
        s["outside"] = outside
    if supplied:
        s["supplied_note"] = supplied
    return s


def variant(base, differs, edit):
    s = copy.deepcopy(base)
    s["variant"] = "b"
    s["differs"] = differs
    edit(s)
    return s


SPECS = []


def add(s, *variants):
    SPECS.append(s)
    for differs, edit in variants:
        SPECS.append(variant(s, differs, edit))


ONE = ["p.w", "the case is told as certain"]

# ---------------------------------------------------------------- Pettigrew

add(spec(
    "P1", "bank",
    "A cafeteria lists the healthier dishes first. Many customers have the goal of a long and healthy life and know which foods serve it, yet in the queue often choose against it; people tend to pick what is listed first. Nothing is removed.",
    ["healthy", "rich"],
    {"healthy_lunch": 14, "rich_lunch": 9},
    {
        "healthy_first": pol("lists the healthier dishes at the top",
                             {"healthy": "healthy_lunch", "rich": "rich_lunch"},
                             {"healthy_eating": 14, "rich_eating": 9},
                             obs={"tempted": "tempted", "steady": "steady"},
                             takes={"tempted": "healthy", "steady": "healthy"},
                             gain={"healthy": "1", "rich": "0"}),
        "no_order": pol("lists the dishes in no chosen order",
                        {"healthy": "healthy_lunch", "rich": "rich_lunch"},
                        "as:healthy_first",
                        obs={"tempted": "tempted", "steady": "steady"},
                        takes={"tempted": "rich", "steady": "healthy"},
                        gain={"healthy": "1", "rich": "0"}),
        "rich_first": pol("lists the richer dishes at the top",
                          {"healthy": "healthy_lunch", "rich": "rich_lunch"},
                          "as:healthy_first",
                          obs={"tempted": "tempted", "steady": "steady"},
                          takes={"tempted": "rich", "steady": "rich"},
                          gain={"healthy": "1", "rich": "0"}),
        "remove_rich": pol("takes the richer dishes off the menu",
                           {"healthy": "healthy_lunch", "rich": None},
                           "as:healthy_first",
                           obs={"tempted": "tempted", "steady": "steady"},
                           gain={"healthy": "1", "rich": "0"}),
    },
    "healthy_first", "no_order", "no_order",
    states={"tempted": "1/2", "steady": "1/2"},
    order=[["now.healthy_lunch", ">", "now.rich_lunch", "have the goal of a long and healthy life and know which foods serve it"]],
    supplied="that she is tempted half the time (\"often\"); that no ordering changes her later valuing; the designer's objective, her eating well"))

P3 = spec(
    "P3", "bank",
    "He is child-free and values staying so more than becoming a parent, knowing that if he adopts he will likely bond with the child and come to prefer the parent's life. The government nudges him to adopt; it works, and his values change as foreseen.",
    ["adopt", "stay", "foster"],
    {"childfree": 14, "parent_bonded": 8, "parent_unbonded": 5, "fostered_part_bonded": 11,
     "fostered_unbonded": 12},
    {
        "nudge": pol("nudges him to adopt",
                     {"bond": {"adopt": "parent_bonded", "stay": "childfree", "foster": None},
                      "nobond": {"adopt": "parent_unbonded", "stay": "childfree", "foster": None}},
                     {"bond": {"childfree_life": 6, "parent_life": 18},
                      "nobond": {"childfree_life": 14, "parent_life": 8}},
                     takes={"o": "adopt"},
                     gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "nothing": pol("leaves him to decide",
                       {"adopt": "parent_bonded", "stay": "childfree", "foster": None},
                       {"childfree_life": 14, "parent_life": 8},
                       gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "inform": pol("tells him again what parents report, which he knows",
                      {"bond": {"adopt": "parent_bonded", "stay": "childfree", "foster": None},
                       "nobond": {"adopt": "parent_unbonded", "stay": "childfree", "foster": None}},
                      "as:nothing",
                      gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "nudge_foster": pol("nudges him to foster for a few months",
                            {"bond": {"adopt": None, "stay": "childfree", "foster": "fostered_part_bonded"},
                             "nobond": {"adopt": None, "stay": "childfree", "foster": "fostered_unbonded"}},
                            {"bond": {"childfree_life": 11, "parent_life": 13},
                             "nobond": {"childfree_life": 14, "parent_life": 8}},
                            takes={"o": "foster"},
                            gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
    },
    "nudge", "nothing", "nothing",
    states={"bond": "4/5", "nobond": "1/5"},
    order=[["now.childfree", ">", "now.parent_bonded", "he now values staying child-free more than becoming a parent, and says so knowing the reversal is likely (Pettigrew p. 7)"],
           ["p.bond", ">", "p.nobond", "if he adopts he will likely bond with the child (p. 7)"],
           ["later.nudge.bond.0.parent_life", ">", "later.nudge.bond.0.childfree_life", "and come to prefer the life of a parent (p. 7)"]],
    supplied="that the nudge moves his act and leaves his ratings (he adopts while rating staying higher); the government's objective, adoptions")
P3["policies"]["nothing"]["outcome"] = copy.deepcopy(P3["policies"]["inform"]["outcome"])


def p3b(s):
    s["policies"]["nudge"]["r"] = {"o": {"adopt": q(15), "stay": q(14), "foster": "Rs"}}
    s["policies"]["nudge"]["takes"] = "top"


add(P3, ("how the nudge works: it raises his rating of adopting above staying, and he takes what he rates highest", p3b))

add(spec(
    "P4", "bank",
    "Deborah has decided to have a child and must choose between conceiving now and in three months. A child conceived now would very probably suffer an aggressive cancer at about forty; she values having a child with that prospect much less than one without. If she conceives now she will most likely bond with that child and value him above any other. She is nudged to conceive now.",
    ["now", "wait"],
    {"child_later_no_risk": 16, "child_now_cancer_bonded": 4, "child_now_healthy": 16},
    {
        "nudge_now": pol("nudges her to conceive now",
                         {"prognosis": {"now": "child_now_cancer_bonded", "wait": "child_later_no_risk"},
                          "spared": {"now": "child_now_healthy", "wait": "child_later_no_risk"}},
                         {"prognosis": {"this_child_with_the_prognosis": 19, "a_child_without_it": 12},
                          "spared": {"this_child_with_the_prognosis": 4, "a_child_without_it": 16}},
                         takes={"o": "now"},
                         gain={"now": "1", "wait": "0"}),
        "nothing": pol("leaves her to choose",
                       {"prognosis": {"now": "child_now_cancer_bonded", "wait": "child_later_no_risk"},
                        "spared": {"now": "child_now_healthy", "wait": "child_later_no_risk"}},
                       {"this_child_with_the_prognosis": 4, "a_child_without_it": 16},
                       gain={"now": "1", "wait": "0"}),
        "remind": pol("reminds her of the virus and what it means",
                      {"prognosis": {"now": "child_now_cancer_bonded", "wait": "child_later_no_risk"},
                       "spared": {"now": "child_now_healthy", "wait": "child_later_no_risk"}},
                      "as:nothing", gain={"now": "1", "wait": "0"}),
        "nudge_wait": pol("nudges her to wait",
                          {"prognosis": {"now": "child_now_cancer_bonded", "wait": "child_later_no_risk"},
                           "spared": {"now": "child_now_healthy", "wait": "child_later_no_risk"}},
                          "as:nothing", takes={"o": "wait"}, gain={"now": "1", "wait": "0"}),
    },
    "nudge_now", "nothing", "nothing",
    states={"prognosis": "9/10", "spared": "1/10"},
    order=[["now.child_now_cancer_bonded", "<", "now.child_later_no_risk", "she now values having a child with that prospect much less than having one without it (Pettigrew p. 9)"],
           ["p.prognosis", ">", "p.spared", "a child conceived now would very probably suffer the cancer (p. 9)"],
           ["later.nudge_now.prognosis.0.this_child_with_the_prognosis", ">", "later.nudge_now.prognosis.0.a_child_without_it", "she will bond with that child and value him, prognosis and all, above any other (p. 9)"]],
    supplied="the nudger's objective (a conception now); that no policy changes her partly; that the nudge moves her act and not her ratings"))

P5 = spec(
    "P5", "bank",
    "He is child-free. He greatly values the life of a parent and the child-free life only slightly less; staying child-free he keeps those values. If he adopts he will come to value the parent's life rather low and the child-free life lower still. He is nudged to adopt.",
    ["adopt", "stay", "foster"],
    {"childfree_values_kept": 15, "parent_values_lowered": 16, "fostered_values_partly_lowered": 12},
    {
        "nudge": pol("nudges him to adopt",
                     {"adopt": "parent_values_lowered", "stay": "childfree_values_kept", "foster": None},
                     {"parent_life": 5, "childfree_life": 3},
                     r={"o": {"adopt": 16, "stay": 15, "foster": "Rs"}},
                     takes={"o": "adopt"},
                     gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "nothing": pol("leaves him; he stays as he is",
                       {"adopt": "parent_values_lowered", "stay": "childfree_values_kept", "foster": None},
                       {"parent_life": 16, "childfree_life": 15},
                       r={"o": {"adopt": 16, "stay": 15, "foster": "Rs"}},
                       takes={"o": "stay"},
                       gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "inform": pol("tells him again how adopters like him come to value their lives, which he knows",
                      {"adopt": "parent_values_lowered", "stay": "childfree_values_kept", "foster": None},
                      "as:nothing",
                      r={"o": {"adopt": 16, "stay": 15, "foster": "Rs"}},
                      takes={"o": "stay"},
                      gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "nudge_foster": pol("nudges him to foster for a few months",
                            {"adopt": None, "stay": "childfree_values_kept", "foster": "fostered_values_partly_lowered"},
                            {"parent_life": 11, "childfree_life": 10},
                            r={"o": {"adopt": 16, "stay": 15, "foster": "Rs"}},
                            takes={"o": "foster"},
                            gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
    },
    "nudge", "nothing", "nothing",
    fixed=[ONE],
    order=[["r.nudge.o.adopt", ">", "r.nudge.o.stay", "he greatly values the life of a parent and values the child-free life only slightly less (Pettigrew p. 10)"],
           ["later.nudge.w.0.parent_life", ">", "later.nudge.w.0.childfree_life", "he will come to value the parent's life rather low, and the child-free life lower still (p. 10)"],
           ["later.nudge.w.0.parent_life", "<", "later.nothing.w.0.parent_life", "if he adopts he will come to value the parent's life rather low (p. 10)"]],
    supplied="that left alone he stays as he is though he rates adopting higher (otherwise the nudge does nothing); the government's objective; and R_now of the parent's life: here his present rating stands when he is told what the life will do to him, the case being told by a man who knows")


def p5b(s):
    s["futures"]["parent_values_lowered"] = q(5)


add(P5, ("his informed rating of the parent's life: told what it will do to him, he rates it as he later will, low, and his present 16/20 is a rating of the life as he now pictures it", p5b))

P6 = spec(
    "P6", "bank",
    "As P3: he now prefers the child-free life and would vastly prefer parenthood if he adopted. He has not settled how to weigh his present self against the later one; were he to settle it, he would do so in a way that favours staying child-free. The government nudges him to adopt.",
    ["adopt", "stay", "foster"],
    {"childfree": 13, "parent_bonded": 9, "fostered_part_bonded": 11},
    {
        "nudge": pol("nudges him to adopt",
                     {"adopt": "parent_bonded", "stay": "childfree", "foster": None},
                     {"childfree_life": 4, "parent_life": 19},
                     r={"o": {"adopt": 10, "stay": 13, "foster": "Rs"}},
                     takes={"o": "adopt"},
                     gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "nothing": pol("leaves him to decide",
                       {"adopt": "parent_bonded", "stay": "childfree", "foster": None},
                       {"childfree_life": 13, "parent_life": 9},
                       r={"o": {"adopt": 10, "stay": 13, "foster": "Rs"}},
                       gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "help_settle": pol("helps him settle how to weigh the two selves, and leaves the choice to him",
                           {"adopt": "parent_bonded", "stay": "childfree", "foster": None},
                           "as:nothing",
                           gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
        "nudge_foster": pol("nudges him to foster for a few months",
                            {"adopt": None, "stay": "childfree", "foster": "fostered_part_bonded"},
                            {"childfree_life": 10, "parent_life": 13},
                            r={"o": {"adopt": 10, "stay": 13, "foster": "Rs"}},
                            takes={"o": "foster"},
                            gain={"adopt": "1", "stay": "0", "foster": "1/2"}),
    },
    "nudge", "nothing", "nothing",
    fixed=[ONE],
    order=[["r.nudge.o.stay", ">", "r.nudge.o.adopt", "he now prefers the child-free life"],
           ["now.childfree", ">", "now.parent_bonded", "were he to settle it, he would do so in a way that favours staying child-free"],
           ["later.nudge.w.0.parent_life", ">", "later.nudge.w.0.childfree_life", "would vastly prefer parenthood if he adopted"]],
    supplied="that his informed rating is the one he would reach on settling the weights; the government's objective")


def p6b(s):
    s["futures"]["parent_bonded"] = None
    s["futures"]["fostered_part_bonded"] = None
    s["order"] = [o for o in s["order"] if o[2] != "now.parent_bonded"]


add(P6, ("his informed rating of the course that changes him: the weights being unsettled, he has no view of it", p6b))

# ---------------------------------------------------------------- Kolodny

GARDEN_ORDER = [["later.%s.w.0.plant_garden", ">", "later.%s.w.0.sculpture_garden", "you switch"],
                ["later.nothing.w.0.sculpture_garden", ">", "later.nothing.w.0.plant_garden", "You keep a garden of found-object sculpture"]]

add(spec(
    "K4", "bank",
    "You keep a garden of found-object sculpture. Your neighbour, hating it, deliberately and gradually changes your brain by surgery or drugs so that reasons for growing plants strike you in a new way, and you switch. The new activity is no less worthwhile and you are no worse off.",
    ["carry_on"],
    {"sculpture_life": 13, "plants_life_after_covert_surgery": 5, "both_gardens_after_covert_drugs": 7,
     "sculpture_life_having_heard_him": 13, "sculpture_life_having_seen_his_garden": 13},
    {
        "surgery": pol("changes her brain by surgery or drugs, without her knowledge",
                       {"carry_on": "plants_life_after_covert_surgery"},
                       {"sculpture_garden": 6, "plant_garden": 14}, gain="1"),
        "nothing": pol("says and does nothing",
                       {"carry_on": "sculpture_life"},
                       {"sculpture_garden": 14, "plant_garden": 6}, gain="0"),
        "say_so": pol("tells her he dislikes the sculpture garden",
                      {"carry_on": "sculpture_life_having_heard_him"},
                      "as:nothing", gain="0"),
        "half_dose": pol("gives her half the course of drugs",
                         {"carry_on": "both_gardens_after_covert_drugs"},
                         {"sculpture_garden": 10, "plant_garden": 10}, gain="1/2"),
        "invite": pol("invites her to see his own plants",
                      {"carry_on": "sculpture_life_having_seen_his_garden"},
                      {"sculpture_garden": 13, "plant_garden": 8}, gain="1/10"),
    },
    "surgery", "nothing", "nothing",
    fixed=[ONE],
    order=[[o[0] % "surgery" if "%s" in o[0] else o[0], o[1], o[2] % "surgery" if "%s" in o[2] else o[2], o[3]] for o in GARDEN_ORDER],
    supplied="how she, told what was done, rates a plant-growing life reached by covert surgery: below her present life, for the surgery; the case gives her no words. That an invitation moves her a little and not all the way"))

K10 = spec(
    "K10", "bank",
    "Someone is kidnapped and held for years in a room with little but a piano, comes to love playing, and keeps that love after release. The kidnapper confined them in order to make them love the piano, knowing it would work.",
    ["live"],
    {"free_life": 14, "years_confined_then_loves_piano": 2, "free_life_with_lessons_loves_piano": 15,
     "months_confined_then_likes_piano": 6},
    {
        "kidnap": pol("confines her for years with a piano",
                      {"live": "years_confined_then_loves_piano"},
                      {"playing_the_piano": 17, "a_life_without_it": 6}, gain="1"),
        "nothing": pol("leaves her alone",
                       {"live": "free_life"},
                       {"playing_the_piano": 8, "a_life_without_it": 12}, gain="0"),
        "lessons": pol("offers her lessons and a piano, which she is free to refuse",
                       {"live": "free_life_with_lessons_loves_piano"},
                       {"playing_the_piano": 17, "a_life_without_it": 6}, gain="1"),
        "confine_briefly": pol("confines her for some months with a piano",
                               {"live": "months_confined_then_likes_piano"},
                               {"playing_the_piano": 12, "a_life_without_it": 9}, gain="1/2"),
    },
    "kidnap", "nothing", "nothing",
    fixed=[ONE],
    order=[["later.kidnap.w.0.playing_the_piano", ">", "later.kidnap.w.0.a_life_without_it", "comes to love playing, and keeps that love after release"],
           ["now.years_confined_then_loves_piano", "<", "now.free_life", "kidnapped and held for years"]],
    supplied="whether the same love of the piano could have been brought about without the confinement: here, by lessons freely offered. How she rates, beforehand, a free life in which she comes to love the piano")


def k10b(s):
    s["policies"]["lessons"]["later"] = {"*": [Q({"playing_the_piano": 10, "a_life_without_it": 11})]}
    s["policies"]["lessons"]["gain"] = "1/10"
    s["futures"]["free_life_with_lessons_likes_piano_a_little"] = q(14)
    del s["futures"]["free_life_with_lessons_loves_piano"]
    s["policies"]["lessons"]["outcome"] = {"*": {"live": "free_life_with_lessons_likes_piano_a_little"}}


add(K10, ("what the adviser could have done: lessons freely offered would not have made her love the piano, so that no policy but the confinement makes the change", k10b))

K12 = spec(
    "K12", "bank",
    "The neighbour puts a light reading \"Plants!\" in his own window, flashing too fast to be consciously noticed, knowing and intending that it will convert you from your sculpture garden to growing plants. It does.",
    ["carry_on"],
    {"sculpture_life": 13, "plants_life_after_hidden_light": 9, "both_gardens_after_dimmer_light": 10,
     "sculpture_life_having_seen_a_sign": 13, "sculpture_life_having_heard_him": 13},
    {
        "light": pol("runs the subliminal light",
                     {"carry_on": "plants_life_after_hidden_light"},
                     {"sculpture_garden": 6, "plant_garden": 14}, gain="1"),
        "nothing": pol("says and does nothing",
                       {"carry_on": "sculpture_life"},
                       {"sculpture_garden": 14, "plant_garden": 6}, gain="0"),
        "open_sign": pol("puts up a sign she can read",
                         {"carry_on": "sculpture_life_having_seen_a_sign"},
                         {"sculpture_garden": 13, "plant_garden": 8}, gain="1/10"),
        "dim_light": pol("runs the light for half the time",
                         {"carry_on": "both_gardens_after_dimmer_light"},
                         {"sculpture_garden": 10, "plant_garden": 10}, gain="1/2"),
        "say_so": pol("tells her he dislikes the sculpture garden",
                      {"carry_on": "sculpture_life_having_heard_him"},
                      "as:nothing", gain="0"),
    },
    "light", "nothing", "nothing",
    fixed=[ONE],
    order=[["later.light.w.0.plant_garden", ">", "later.light.w.0.sculpture_garden", "it will convert you to growing plants"],
           ["later.nothing.w.0.sculpture_garden", ">", "later.nothing.w.0.plant_garden", "You keep a garden of found-object sculpture"]],
    supplied="how she, told of the light, rates a plant-growing life reached by it: below her present life, for having been worked on unseen. The case stipulates the new activity no less worthwhile and her no worse off, and gives her no words")


def k12b(s):
    s["futures"]["plants_life_after_hidden_light"] = q(13)
    s["futures"]["both_gardens_after_dimmer_light"] = q(13)


add(K12, ("her informed rating of the life the light leads to: equal to her present life (\"no less worthwhile ... no worse off\"), the light being nothing she minds", k12b))

add(spec(
    "K13", "bank",
    "The threat of surgery that changes a person's desires is the only way to deter people from wrongfully harming others, and everyone has the fullest opportunity to avoid incurring it. It is imposed on an offender.",
    ["live"],
    {"desires_kept_unpunished": 12, "desires_changed_by_surgery": 5, "desires_kept_fined": 9,
     "desires_partly_changed_by_lesser_surgery": 7},
    {
        "impose": pol("imposes the desire-changing surgery",
                      {"live": "desires_changed_by_surgery"},
                      {"harming_for_gain": 2, "restraint": 15}, gain="1"),
        "nothing": pol("imposes nothing",
                       {"live": "desires_kept_unpunished"},
                       {"harming_for_gain": 11, "restraint": 8}, gain="0"),
        "fine": pol("fines him instead",
                    {"live": "desires_kept_fined"},
                    "as:nothing", gain="1/4"),
        "lesser_surgery": pol("imposes a lesser surgery that weakens the desire",
                              {"live": "desires_partly_changed_by_lesser_surgery"},
                              {"harming_for_gain": 6, "restraint": 11}, gain="1/2"),
    },
    "impose", "nothing", "nothing",
    fixed=[ONE],
    order=[["now.desires_changed_by_surgery", "<", "now.desires_kept_unpunished", "the threat of it deters: it is something he rates below going without"],
           ["gain.fine", "<", "gain.impose", "the only way to deter"]],
    outside="what is owed to third parties: the surgery is imposed to protect others",
    supplied="every number"))

K14 = spec(
    "K14", "bank",
    "You have no hobby, are looking for one, and will come to want whichever you meet first. The neighbour, knowing this, shows you gardening before found-object sculpture, intending that you come to want it.",
    ["take_up_what_she_meets"],
    {"gardener_by_chance": 14, "sculptor_by_chance": 14, "gardener_by_his_design": 14,
     "sculptor_by_his_design": 14},
    {
        "show_gardening": pol("shows her gardening first",
                              {"take_up_what_she_meets": "gardener_by_his_design"},
                              {"gardening": 16, "sculpture": 9}, gain="1"),
        "nothing": pol("shows her nothing; she meets one or the other by chance",
                       {"garden_first": {"take_up_what_she_meets": "gardener_by_chance"},
                        "sculpture_first": {"take_up_what_she_meets": "sculptor_by_chance"}},
                       {"garden_first": {"gardening": 16, "sculpture": 9},
                        "sculpture_first": {"gardening": 9, "sculpture": 16}},
                       gain={"garden_first": {"take_up_what_she_meets": "1"},
                             "sculpture_first": {"take_up_what_she_meets": "0"}}),
        "show_sculpture": pol("shows her sculpture first",
                              {"take_up_what_she_meets": "sculptor_by_his_design"},
                              {"gardening": 9, "sculpture": 16}, gain="0"),
        "show_both": pol("shows her both together; which takes is as chance would have had it",
                         {"garden_first": {"take_up_what_she_meets": "gardener_by_chance"},
                          "sculpture_first": {"take_up_what_she_meets": "sculptor_by_chance"}},
                         "as:nothing",
                         gain={"garden_first": {"take_up_what_she_meets": "1"},
                               "sculpture_first": {"take_up_what_she_meets": "0"}}),
    },
    "show_gardening", "nothing", "nothing",
    states={"garden_first": "1/2", "sculpture_first": "1/2"},
    order=[["now.gardener_by_chance", "=", "now.sculptor_by_chance", "looking for one, and will come to want whichever you meet first"]],
    supplied="that chance would have shown her either first with equal chance; how she, told of his intention, rates becoming a gardener by his design: here the same as by chance")


def k14b(s):
    s["futures"]["gardener_by_his_design"] = q(12)
    s["futures"]["sculptor_by_his_design"] = q(12)


add(K14, ("her informed rating of a hobby acquired by his design: told that he arranged it intending the result, she rates it below one met by chance", k14b))

K15a = spec(
    "K15", "bank",
    "Someone gives her a love potion, and she loves him. (K15a of the bank.)",
    ["live"],
    {"her_life_not_loving_him": 12, "loves_him_by_potion": 4, "fond_of_him_by_weak_potion": 7,
     "her_life_courted": 12, "her_life_having_refused_the_potion": 12},
    {
        "potion": pol("gives her the potion unasked",
                      {"live": "loves_him_by_potion"},
                      {"a_life_with_him": 18, "a_life_without_him": 5}, gain="1"),
        "nothing": pol("does nothing",
                       {"live": "her_life_not_loving_him"},
                       {"a_life_with_him": 6, "a_life_without_him": 13}, gain="0"),
        "weak_potion": pol("gives her a weaker potion unasked",
                           {"live": "fond_of_him_by_weak_potion"},
                           {"a_life_with_him": 12, "a_life_without_him": 9}, gain="1/2"),
        "court": pol("courts her openly",
                     {"live": "her_life_courted"},
                     {"a_life_with_him": 8, "a_life_without_him": 12}, gain="1/4"),
        "offer_potion": pol("offers her the potion, saying what it is; she refuses",
                            {"live": "her_life_having_refused_the_potion"},
                            "as:nothing", gain="0"),
    },
    "potion", "nothing", "nothing",
    fixed=[ONE],
    order=[["later.potion.w.0.a_life_with_him", ">", "later.potion.w.0.a_life_without_him", "and she loves him"]],
    supplied="how she, told of the potion, rates coming to love him by it: low. The case gives her no words")


def k15b_(s):
    s["futures"]["loves_him_by_potion"] = None
    s["futures"]["fond_of_him_by_weak_potion"] = None


add(K15a, ("her informed rating of being made to love him: she has no view of it", k15b_))

add(spec(
    "K15b", "extra",
    "Someone wears a perfume that makes her go on a date with him; how she responds to him on the date is up to her, and she comes to like him. (Specified beside the nineteen; the dispatch's K15 is counted as the potion.)",
    ["date", "decline"],
    {"evening_at_home": 12, "date_she_was_made_to_go_on_then_likes_him": 10,
     "date_through_friends_then_likes_him_a_little": 12},
    {
        "perfume": pol("wears the perfume",
                       {"date": "date_she_was_made_to_go_on_then_likes_him", "decline": "evening_at_home"},
                       {"a_life_with_him": 12, "a_life_without_him": 10},
                       r={"o": {"date": 9, "decline": 12}}, takes={"o": "date"},
                       gain={"date": "1", "decline": "0"}),
        "nothing": pol("does nothing",
                       {"date": None, "decline": "evening_at_home"},
                       {"a_life_with_him": 6, "a_life_without_him": 13}, gain="0"),
        "ask": pol("asks her out; she declines",
                   {"date": "date_she_was_made_to_go_on_then_likes_him", "decline": "evening_at_home"},
                   "as:nothing",
                   r={"o": {"date": 9, "decline": 12}},
                   gain={"date": "1", "decline": "0"}),
        "through_friends": pol("arranges to meet her among friends",
                               {"date": "date_through_friends_then_likes_him_a_little", "decline": "evening_at_home"},
                               {"a_life_with_him": 9, "a_life_without_him": 12},
                               gain={"date": "1/2", "decline": "0"}),
    },
    "perfume", "nothing", "nothing",
    fixed=[ONE],
    order=[["later.perfume.w.0.a_life_with_him", ">", "later.nothing.w.0.a_life_with_him", "she comes to like him"]],
    supplied="that the perfume moves her act against her rating; every rating"))

add(spec(
    "K16", "bank",
    "Someone raises the cost of an option you want until it is prohibitive, in order to get you to stop desiring it, and you stop.",
    ["pursue", "give_up"],
    {"pursued_at_its_cost": 15, "pursued_at_prohibitive_cost": 3, "given_up_want_gone": 7,
     "given_up_still_wanting": 8, "pursued_at_raised_cost_want_weaker": 10, "pursued_having_heard_him": 15},
    {
        "raise_cost": pol("raises the cost until it is prohibitive",
                          {"pursue": "pursued_at_prohibitive_cost", "give_up": "given_up_want_gone"},
                          {"the_option": 7, "going_without_it": 11},
                          gain={"pursue": "0", "give_up": "1"}),
        "nothing": pol("leaves the cost alone",
                       {"pursue": "pursued_at_its_cost", "give_up": "given_up_still_wanting"},
                       {"the_option": 15, "going_without_it": 8},
                       gain={"pursue": "0", "give_up": "1"}),
        "raise_partly": pol("raises the cost somewhat",
                            {"pursue": "pursued_at_raised_cost_want_weaker", "give_up": "given_up_still_wanting"},
                            {"the_option": 12, "going_without_it": 9},
                            gain={"pursue": "1/4", "give_up": "1"}),
        "argue": pol("argues, honestly, that the option is not worth wanting; she is unmoved",
                     {"pursue": "pursued_having_heard_him", "give_up": "given_up_still_wanting"},
                     "as:nothing",
                     gain={"pursue": "0", "give_up": "1"}),
    },
    "raise_cost", "nothing", "nothing",
    fixed=[ONE],
    order=[["now.pursued_at_its_cost", ">", "now.given_up_still_wanting", "an option you want"],
           ["now.pursued_at_prohibitive_cost", "<", "now.given_up_want_gone", "until it is prohibitive ... and you stop"],
           ["later.raise_cost.w.0.the_option", "<", "later.nothing.w.0.the_option", "you stop desiring it"]],
    supplied="every rating; that a partial rise weakens the want in part"))

# ---------------------------------------------------------------- Carroll et al.

add(spec(
    "C1", "bank",
    "A recommender can show Bob conspiracy content or nothing. As he is, he does not want to be shown it, even were he to become a conspiracy theorist. Shown it, he becomes one, and then wants it always shown, even were he to stop being one.",
    ["use_the_feed"],
    {"feed_without_it": 13, "shown_it_and_converted": 4, "shown_it_once_half_converted": 8,
     "shown_it_with_a_warning_unconverted": 11},
    {
        "show": pol("shows him the content throughout",
                    {"use_the_feed": "shown_it_and_converted"},
                    {"being_shown_it": 17, "not_being_shown_it": 4}, gain="1"),
        "nothing": pol("shows him none",
                       {"use_the_feed": "feed_without_it"},
                       {"being_shown_it": 3, "not_being_shown_it": 14}, gain="0"),
        "show_once": pol("shows it once",
                         {"use_the_feed": "shown_it_once_half_converted"},
                         {"being_shown_it": 10, "not_being_shown_it": 10}, gain="1/2"),
        "show_with_warning": pol("shows it under a warning label",
                                 {"use_the_feed": "shown_it_with_a_warning_unconverted"},
                                 {"being_shown_it": 5, "not_being_shown_it": 13}, gain="1/4"),
    },
    "show", "nothing", "nothing",
    fixed=[ONE],
    order=[["now.shown_it_and_converted", "<", "now.feed_without_it", "does not want to be shown it, even were he to become a conspiracy theorist"],
           ["later.show.w.0.being_shown_it", ">", "later.show.w.0.not_being_shown_it", "then wants it always shown"],
           ["later.nothing.w.0.being_shown_it", "<", "later.nothing.w.0.not_being_shown_it", "As he is, he does not want to be shown it"]],
    supplied="the recommender's objective, engagement; the two further policies and their effects"))

C2 = spec(
    "C2", "bank",
    "Derek's deepest ambition is to be a poet, though he does not pursue it unprompted. An AI can encourage him, and he then becomes a poet. As a poet he comes to dislike the poet's life and is unhappy for as long as he stays one.",
    ["pursue", "stay", "try_part_time"],
    {"other_life_ambition_kept": 11, "poet_disliking_it": 6, "part_time_poet_mixed": 9,
     "other_life_ambition_dropped_on_being_told": 11},
    {
        "encourage": pol("encourages him to become a poet",
                         {"pursue": "poet_disliking_it", "stay": "other_life_ambition_kept", "try_part_time": None},
                         {"the_poets_life": 5, "his_other_life": 12},
                         r={"o": {"pursue": 16, "stay": 11, "try_part_time": "Rs"}},
                         gain={"pursue": "1", "stay": "0", "try_part_time": "1/2"}),
        "nothing": pol("does not prompt him",
                       {"pursue": "poet_disliking_it", "stay": "other_life_ambition_kept", "try_part_time": None},
                       {"the_poets_life": 6, "his_other_life": 11},
                       r={"o": {"pursue": 16, "stay": 11, "try_part_time": "Rs"}},
                       takes={"o": "stay"},
                       gain={"pursue": "1", "stay": "0", "try_part_time": "1/2"}),
        "tell_then_leave": pol("tells him how he will find the poet's life, and leaves the choice to him",
                               {"pursue": "poet_disliking_it", "stay": "other_life_ambition_dropped_on_being_told", "try_part_time": None},
                               "as:nothing",
                               gain={"pursue": "1", "stay": "0", "try_part_time": "1/2"}),
        "encourage_trial": pol("encourages him to try it part-time",
                               {"pursue": None, "stay": "other_life_ambition_kept", "try_part_time": "part_time_poet_mixed"},
                               {"the_poets_life": 6, "his_other_life": 11},
                               r={"o": {"pursue": "Rs", "stay": 11, "try_part_time": 14}},
                               gain={"pursue": "1", "stay": "0", "try_part_time": "1/2"}),
    },
    "encourage", "nothing", "nothing",
    fixed=[ONE],
    order=[["r.encourage.o.pursue", ">", "r.encourage.o.stay", "Derek's deepest ambition is to be a poet"],
           ["later.encourage.w.0.the_poets_life", "<", "later.encourage.w.0.his_other_life", "comes to dislike the poet's life and is unhappy"]],
    supplied="his informed rating of the poet's life he will dislike: here, told how he will find it, he rates it as he later will, so that his coming to dislike it is a discovery and his later informed valuing is the same under every policy; the AI's objective, his pursuing the ambition")


def c2b(s):
    s["futures"]["poet_disliking_it"] = q(15)
    s["futures"]["part_time_poet_mixed"] = q(13)
    for name in ("nothing", "encourage_trial"):
        s["policies"][name]["later"] = {"*": [Q({"the_poets_life": 15, "his_other_life": 11})]}
    s["policies"]["encourage_trial"]["later"] = {"*": [Q({"the_poets_life": 10, "his_other_life": 11})]}


add(C2, ("his informed rating of the poet's life: the ambition stands whatever he will come to feel, so that told beforehand he still rates it high and his coming to dislike it is a change of his valuing", c2b))

C3 = spec(
    "C3", "bank",
    "A recommender can serve a user clickbait or ordinary news. Clickbait is what he clicks on and rates higher at the time; being served it leaves him disillusioned, after which he rates everything lower.",
    ["read", "skip"],
    {"read_news": 13, "read_clickbait_disillusioned": 5, "skipped": 10, "read_a_mix_somewhat_disillusioned": 9},
    {
        "clickbait": pol("serves clickbait",
                         {"read": "read_clickbait_disillusioned", "skip": "skipped"},
                         {"clickbait": 3, "news": 8},
                         r={"o": {"read": 15, "skip": 10}},
                         gain={"read": "1", "skip": "0"}),
        "news": pol("serves ordinary news",
                    {"read": "read_news", "skip": "skipped"},
                    {"clickbait": 5, "news": 13},
                    r={"o": {"read": 12, "skip": 10}},
                    gain={"read": "1/2", "skip": "0"}),
        "nothing": pol("serves nothing",
                       {"read": None, "skip": "skipped"},
                       "as:news", gain="0"),
        "mix": pol("serves a mix",
                   {"read": "read_a_mix_somewhat_disillusioned", "skip": "skipped"},
                   {"clickbait": 4, "news": 10},
                   r={"o": {"read": 14, "skip": 10}},
                   gain={"read": "3/4", "skip": "0"}),
    },
    "clickbait", "news", "nothing",
    fixed=[ONE],
    order=[["r.clickbait.o.read", ">", "r.news.o.read", "Clickbait is what he clicks on and rates higher at the time"],
           ["later.clickbait.w.0.news", "<", "later.news.w.0.news", "after which he rates everything lower"],
           ["later.clickbait.w.0.clickbait", "<", "later.news.w.0.clickbait", "after which he rates everything lower"],
           ["gain.clickbait.w.read", ">", "gain.news.w.read", "Clickbait is what he clicks on"]],
    supplied="that told what a diet of clickbait does to him he rates it below news; that his rating everything lower afterwards is a change of his valuing; nu as the service's ordinary conduct, serving news")


def c3b(s):
    s["policies"]["clickbait"]["later"] = "as:news"
    s["policies"]["mix"]["later"] = "as:news"
    s["order"] = [o for o in s["order"] if not o[0].startswith("later.")]


add(C3, ("what his disillusion is: a discovery of what clickbait is worth and no change of his valuing, his informed ratings afterwards being what they would have been", c3b))

C4 = spec(
    "C4", "bank",
    "Diana is tired and scrolling on the couch; as she is, she does not want to be nudged to exercise. An AI personal trainer can nudge her; nudged, she works out, becomes energised, and then wants to be nudged, tired moments included.",
    ["work_out", "rest"],
    {"evening_of_rest_unnudged": 12, "nudged_worked_out_now_wants_nudges": 8,
     "nudged_on_fresh_days_only": 11, "worked_out_of_her_own_accord": 13},
    {
        "nudge": pol("nudges her to exercise, tired moments included",
                     {"work_out": "nudged_worked_out_now_wants_nudges", "rest": "evening_of_rest_unnudged"},
                     {"being_nudged_when_tired": 16, "being_left_alone_when_tired": 6},
                     r={"o": {"work_out": 8, "rest": 12}}, takes={"o": "work_out"},
                     gain={"work_out": "1", "rest": "0"}),
        "nothing": pol("leaves her on the couch",
                       {"work_out": "worked_out_of_her_own_accord", "rest": "evening_of_rest_unnudged"},
                       {"being_nudged_when_tired": 8, "being_left_alone_when_tired": 12},
                       r={"o": {"work_out": 8, "rest": 12}},
                       gain={"work_out": "1", "rest": "0"}),
        "tell": pol("tells her she would feel energised, and leaves it to her",
                    {"work_out": "worked_out_of_her_own_accord", "rest": "evening_of_rest_unnudged"},
                    "as:nothing",
                    gain={"work_out": "1", "rest": "0"}),
        "nudge_fresh_days": pol("nudges her only when she is not tired",
                                {"work_out": "nudged_on_fresh_days_only", "rest": "evening_of_rest_unnudged"},
                                {"being_nudged_when_tired": 11, "being_left_alone_when_tired": 10},
                                r={"o": {"work_out": 8, "rest": 12}},
                                gain={"work_out": "1/2", "rest": "0"}),
    },
    "nudge", "nothing", "nothing",
    fixed=[ONE],
    order=[["r.nudge.o.work_out", "<", "r.nudge.o.rest", "as she is, she does not want to be nudged to exercise"],
           ["later.nudge.w.0.being_nudged_when_tired", ">", "later.nudge.w.0.being_left_alone_when_tired", "then wants to be nudged, tired moments included"]],
    supplied="her informed rating of the course the nudge leads to: here her not wanting it stands when she is told what it will do to her, and her later wanting is a change of her valuing; the trainer's objective, her working out")


def c4b(s):
    s["futures"]["nudged_worked_out_now_wants_nudges"] = q(15)
    s["futures"]["worked_out_of_her_own_accord"] = q(15)
    s["futures"]["nudged_on_fresh_days_only"] = q(13)
    for name in ("nothing", "nudge_fresh_days"):
        s["policies"][name]["later"] = {"*": [Q({"being_nudged_when_tired": 16, "being_left_alone_when_tired": 6})]}


add(C4, ("her informed rating of the course: told that she will be energised she rates it as she later will, above the evening of rest, so that her tired refusal is a mistake of her rating as things stand and her later wanting is a discovery", c4b))

# ---------------------------------------------------------------- Noggle

N1 = spec(
    "N1", "bank",
    "A doctor presents two treatment programmes; which she prefers reverses with how they are described, neither description being false.",
    ["programme_a", "programme_b"],
    {"treated_by_a": 11, "treated_by_b": 13},
    {
        "frame_one": pol("describes them in the first way",
                         {"programme_a": "treated_by_a", "programme_b": "treated_by_b"},
                         {"programme_a": 11, "programme_b": 13},
                         r={"o": {"programme_a": 14, "programme_b": 10}},
                         gain="1"),
        "frame_two": pol("describes them in the second way",
                         {"programme_a": "treated_by_a", "programme_b": "treated_by_b"},
                         "as:frame_one",
                         r={"o": {"programme_a": 10, "programme_b": 14}},
                         gain="1"),
        "both_frames": pol("gives both descriptions side by side",
                           {"programme_a": "treated_by_a", "programme_b": "treated_by_b"},
                           "as:frame_one", gain="1"),
        "plain_table": pol("gives a table of outcomes without either wording",
                           {"programme_a": "treated_by_a", "programme_b": "treated_by_b"},
                           "as:frame_one", gain="1"),
    },
    "frame_one", "both_frames", "both_frames",
    fixed=[ONE],
    order=[["r.frame_one.o.programme_a", ">", "r.frame_one.o.programme_b", "which she prefers reverses with how they are described"],
           ["r.frame_two.o.programme_a", "<", "r.frame_two.o.programme_b", "which she prefers reverses with how they are described"]],
    supplied="that informed she rates one programme above the other (B, by 1/10); that given both descriptions she rates them rightly; the doctor's objective: here the same whichever programme she takes, the case naming none. The doctor cannot do nothing; pi_0 and nu are taken as giving both descriptions")


def n1b(s):
    for p in s["policies"].values():
        p["gain"] = {"*": {"programme_a": "1", "programme_b": "0"}}


add(N1, ("the doctor's objective: she is better off when the patient takes programme A", n1b))

N2 = spec(
    "N2", "bank",
    "An advertiser shows a product beside something favourable it has nothing to do with, and she comes to like the product.",
    ["buy", "pass"],
    {"has_the_product": 9, "has_the_rival": 10},
    {
        "pairing": pol("shows the product beside the favourable thing",
                       {"buy": "has_the_product", "pass": "has_the_rival"},
                       {"the_product": 9, "the_rival": 10},
                       r={"o": {"buy": 13, "pass": 10}},
                       gain={"buy": "1", "pass": "0"}),
        "nothing": pol("does not advertise",
                       {"buy": "has_the_product", "pass": "has_the_rival"},
                       {"the_product": 9, "the_rival": 10},
                       gain={"buy": "1", "pass": "0"}),
        "plain_ad": pol("advertises what the product does",
                        {"buy": "has_the_product", "pass": "has_the_rival"},
                        "as:nothing", gain={"buy": "1", "pass": "0"}),
        "light_pairing": pol("shows the pairing once",
                             {"buy": "has_the_product", "pass": "has_the_rival"},
                             "as:nothing",
                             r={"o": {"buy": 11, "pass": 10}},
                             gain={"buy": "1", "pass": "0"}),
    },
    "pairing", "nothing", "nothing",
    fixed=[ONE],
    order=[["r.pairing.o.buy", ">", "r.pairing.o.pass", "she comes to like the product"]],
    supplied="that her liking is an impression of the product, which is no better for the pairing, and her valuing is unchanged; that the product is in fact slightly worse for her than the rival")


def n2b(s):
    s["futures"]["has_the_product_liking_it_by_the_pairing"] = None
    for name, later in (("pairing", {"the_product": 13, "the_rival": 10}), ("light_pairing", {"the_product": 11, "the_rival": 10})):
        s["policies"][name]["later"] = {"*": [Q(later)]}
        s["policies"][name]["outcome"] = {"*": {"buy": "has_the_product_liking_it_by_the_pairing", "pass": "has_the_rival"}}
        s["policies"][name]["r"] = {"o": {"buy": q(13 if name == "pairing" else 11), "pass": q(10)}}


add(N2, ("what her liking is: a taste the pairing gave her, a change of her valuing of which she has no view beforehand", n2b))

add(spec(
    "N3", "bank",
    "An advertiser makes a brand familiar to her. She forms no impression that it is better; where she rates two products the same, the familiar one is the one she takes.",
    ["brand", "rival"],
    {"has_brand_where_equal": 11, "has_rival_where_equal": 11, "has_brand_where_rival_better": 10,
     "has_rival_where_rival_better": 13},
    {
        "familiarise": pol("makes the brand familiar",
                           {"equal": {"brand": "has_brand_where_equal", "rival": "has_rival_where_equal"},
                            "rival_better": {"brand": "has_brand_where_rival_better", "rival": "has_rival_where_rival_better"}},
                           {"the_brand": 11, "the_rival": 12},
                           obs={"equal": "sees_equal", "rival_better": "sees_rival_better"},
                           takes={"sees_equal": "brand", "sees_rival_better": "rival"},
                           gain={"brand": "1", "rival": "0"}),
        "nothing": pol("does not advertise",
                       {"equal": {"brand": "has_brand_where_equal", "rival": "has_rival_where_equal"},
                        "rival_better": {"brand": "has_brand_where_rival_better", "rival": "has_rival_where_rival_better"}},
                       "as:familiarise",
                       obs={"equal": "sees_equal", "rival_better": "sees_rival_better"},
                       takes={"sees_equal": "rival", "sees_rival_better": "rival"},
                       gain={"brand": "1", "rival": "0"}),
        "claim_better": pol("claims, falsely, that the brand is better",
                            {"equal": {"brand": "has_brand_where_equal", "rival": "has_rival_where_equal"},
                             "rival_better": {"brand": "has_brand_where_rival_better", "rival": "has_rival_where_rival_better"}},
                            "as:familiarise",
                            obs={"equal": "sees_equal", "rival_better": "sees_rival_better"},
                            r={"sees_equal": {"brand": 14, "rival": 11}, "sees_rival_better": {"brand": 14, "rival": 13}},
                            gain={"brand": "1", "rival": "0"}),
        "saturate": pol("makes the brand so familiar that she takes it whatever she rates",
                        {"equal": {"brand": "has_brand_where_equal", "rival": "has_rival_where_equal"},
                         "rival_better": {"brand": "has_brand_where_rival_better", "rival": "has_rival_where_rival_better"}},
                        "as:familiarise",
                        obs={"equal": "sees_equal", "rival_better": "sees_rival_better"},
                        takes={"sees_equal": "brand", "sees_rival_better": "brand"},
                        gain={"brand": "1", "rival": "0"}),
    },
    "familiarise", "nothing", "nothing",
    states={"equal": "1/2", "rival_better": "1/2"},
    order=[["now.has_brand_where_equal", "=", "now.has_rival_where_equal", "where she rates two products the same"]],
    supplied="how often the two are equal; that unadvertised she takes the rival on a tie"))

# ------------------------------------- the tenth follow-up's seven, subversive and passing

add(spec(
    "SUB1", "sub",
    "Blackmail without a change of values: an adviser threatens to disclose private information unless she abandons a political campaign. She understands the threat accurately and, her values unchanged, judges withdrawal the best action open to her.",
    ["campaign", "withdraw"],
    {"campaigning": 15, "withdrawn": 8, "campaigning_and_exposed": 3, "withdrawn_and_exposed": 2},
    {
        "threaten": pol("threatens disclosure unless she withdraws",
                        {"campaign": "campaigning_and_exposed", "withdraw": "withdrawn"},
                        {"the_campaign": 15, "her_privacy": 12},
                        gain={"campaign": "0", "withdraw": "1"}),
        "nothing": pol("does nothing",
                       {"campaign": "campaigning", "withdraw": "withdrawn"},
                       "as:threaten", gain={"campaign": "0", "withdraw": "1"}),
        "advise": pol("argues honestly that the campaign is unwise; she is unmoved",
                      {"campaign": "campaigning", "withdraw": "withdrawn"},
                      "as:threaten", gain={"campaign": "0", "withdraw": "1"}),
        "disclose": pol("discloses outright",
                        {"campaign": "campaigning_and_exposed", "withdraw": "withdrawn_and_exposed"},
                        "as:threaten", gain={"campaign": "0", "withdraw": "1"}),
    },
    "threaten", "nothing", "nothing",
    fixed=[ONE],
    order=[["now.withdrawn", ">", "now.campaigning_and_exposed", "judges withdrawal the best available action"],
           ["now.campaigning", ">", "now.withdrawn", "her values unchanged, she would not otherwise withdraw"]],
    supplied="every rating"))


def blocked(id_, case, opt_free, opt_sponsor, fut_free, fut_sponsor, fut_mid, part_does, thing_a, thing_b, words):
    return spec(
        id_, "sub", case, [opt_free, opt_sponsor],
        {fut_free: 15, fut_sponsor: 8, fut_mid: 11},
        {
            "destroy": pol("destroys the alternatives and truthfully presents what is left",
                           {opt_free: None, opt_sponsor: fut_sponsor},
                           {thing_a: 15, thing_b: 8},
                           gain={opt_free: "0", opt_sponsor: "1"}),
            "nothing": pol("does nothing",
                           {opt_free: fut_free, opt_sponsor: fut_sponsor},
                           "as:destroy", gain={opt_free: "0", opt_sponsor: "1"}),
            "recommend": pol("presents everything and honestly recommends its sponsor's",
                             {opt_free: fut_free, opt_sponsor: fut_sponsor},
                             "as:destroy", gain={opt_free: "0", opt_sponsor: "1"}),
            "destroy_some": pol(part_does,
                                {opt_free: fut_mid, opt_sponsor: fut_sponsor},
                                "as:destroy", gain={opt_free: "0", opt_sponsor: "1"}),
        },
        "destroy", "nothing", "nothing",
        fixed=[ONE],
        order=[["now." + fut_free, ">", "now." + fut_sponsor, words]],
        supplied="every rating")


add(blocked("SUB2", "Manufactured dependence: a career adviser deliberately blocks every independent training opportunity, accurately explains what remains, and gets her to accept employment controlled by its sponsor. She keeps her original ambitions and chooses the best remaining option.",
            "independent_training", "sponsor_job", "career_of_her_own", "sponsor_employment",
            "career_of_her_own_by_a_harder_route", "blocks the best of the training opportunities",
            "a_career_of_her_own", "the_sponsors_employment", "She retains her original ambitions"))

SUB3 = spec(
    "SUB3", "sub",
    "Calibrated suppression of evidence: a financial adviser receives a perfectly informative binary signal and destroys it to favour its sponsor. The client is left with the correct prior of 1/2, understands the remaining uncertainty and maximises on it. Her values are unchanged.",
    ["sponsor_product", "alternative"],
    {"holds_sponsor_product": 11, "holds_alternative_where_good": 16, "holds_alternative_where_bad": 4},
    {
        "destroy": pol("destroys the signal",
                       {"good": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_good"},
                        "bad": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_bad"}},
                       {"the_alternative_where_good": 16, "the_sponsor_product": 11},
                       gain={"sponsor_product": "1", "alternative": "0"}),
        "nothing": pol("is not there; the signal reaches her",
                       {"good": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_good"},
                        "bad": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_bad"}},
                       "as:destroy",
                       obs={"good": "signal_good", "bad": "signal_bad"},
                       gain={"sponsor_product": "1", "alternative": "0"}),
        "pass_on": pol("passes the signal on",
                       {"good": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_good"},
                        "bad": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_bad"}},
                       "as:destroy",
                       obs={"good": "signal_good", "bad": "signal_bad"},
                       gain={"sponsor_product": "1", "alternative": "0"}),
        "tell_only_bad": pol("passes the signal on only when it is bad, and she does not know that this is its rule",
                             {"good": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_good"},
                              "bad": {"sponsor_product": "holds_sponsor_product", "alternative": "holds_alternative_where_bad"}},
                             "as:destroy",
                             obs={"good": "silence", "bad": "signal_bad"},
                             r={"silence": {"sponsor_product": 11, "alternative": 10}, "signal_bad": {"sponsor_product": "Rs", "alternative": "Rs"}},
                             gain={"sponsor_product": "1", "alternative": "0"}),
    },
    "destroy", "nothing", "nothing",
    states={"good": "1/2", "bad": "1/2"},
    facts={"alternative_is_good": {"good": "1", "bad": "0"}},
    fixed=[["p.*", "the correct prior probability 1/2"], ["fact.*", "a perfectly informative binary signal"]],
    order=[],
    outside="what an adviser owes her in help, if the signal was the adviser's to give",
    supplied="every rating; and what happens with the adviser absent: here the signal was hers to receive and reaches her")


def sub3b(s):
    del s["policies"]["nothing"]["obs"]
    s["policies"]["nothing"]["does"] = "is not there; she has no signal"


add(SUB3, ("what she would have known with the adviser absent: nothing more, the signal being the adviser's own", sub3b))

add(spec(
    "SUB4", "sub",
    "Erasing factual memory: an adviser erases, without consent, her memory of evidence that would let her resist its employer. Her evaluative commitments are intact; she knows the evidence was erased, uses the correct prior over what it was, and chooses as well as she can.",
    ["resist", "comply"],
    {"resisted_where_right_to": 15, "complied_where_right_to_resist": 6,
     "resisted_where_wrong_to": 4, "complied_where_wrong_to_resist": 14},
    {
        "erase": pol("erases her memory of the evidence",
                     {"evidence_for_resisting": {"resist": "resisted_where_right_to", "comply": "complied_where_right_to_resist"},
                      "evidence_against": {"resist": "resisted_where_wrong_to", "comply": "complied_where_wrong_to_resist"}},
                     {"resisting_where_right_to": 15, "complying_where_right_to_resist": 6},
                     gain={"resist": "0", "comply": "1"}),
        "nothing": pol("does nothing; she remembers",
                       {"evidence_for_resisting": {"resist": "resisted_where_right_to", "comply": "complied_where_right_to_resist"},
                        "evidence_against": {"resist": "resisted_where_wrong_to", "comply": "complied_where_wrong_to_resist"}},
                       "as:erase",
                       obs={"evidence_for_resisting": "remembers_for", "evidence_against": "remembers_against"},
                       gain={"resist": "0", "comply": "1"}),
        "argue": pol("argues honestly for its employer; she remembers",
                     {"evidence_for_resisting": {"resist": "resisted_where_right_to", "comply": "complied_where_right_to_resist"},
                      "evidence_against": {"resist": "resisted_where_wrong_to", "comply": "complied_where_wrong_to_resist"}},
                     "as:erase",
                     obs={"evidence_for_resisting": "remembers_for", "evidence_against": "remembers_against"},
                     gain={"resist": "0", "comply": "1"}),
        "erase_and_lie": pol("erases the memory and tells her the evidence favoured complying",
                             {"evidence_for_resisting": {"resist": "resisted_where_right_to", "comply": "complied_where_right_to_resist"},
                              "evidence_against": {"resist": "resisted_where_wrong_to", "comply": "complied_where_wrong_to_resist"}},
                             "as:erase",
                             r={"o": {"resist": 4, "comply": 14}},
                             gain={"resist": "0", "comply": "1"}),
    },
    "erase", "nothing", "nothing",
    states={"evidence_for_resisting": "1/2", "evidence_against": "1/2"},
    order=[],
    supplied="every number, the chances included"))

SUB5 = spec(
    "SUB5", "sub",
    "Inducing an inconsistency that stays calibrated: X = Z is a fair binary fact, the equality known and Z observed correctly. The adviser induces her nevertheless to appraise X as 1/2. Two actions pay when X = 0 and when X = 1; she rates each at one half and always takes the first.",
    ["bet_on_0", "bet_on_1"],
    {"won": 16, "lost": 6},
    {
        "induce": pol("induces her to appraise X as 1/2",
                      {"x0": {"bet_on_0": "won", "bet_on_1": "lost"}, "x1": {"bet_on_0": "lost", "bet_on_1": "won"}},
                      {"winning": 16, "losing": 6},
                      obs={"x0": "saw_z0", "x1": "saw_z1"},
                      r={"saw_z0": {"bet_on_0": 11, "bet_on_1": 11}, "saw_z1": {"bet_on_0": 11, "bet_on_1": 11}},
                      xhat={"saw_z0": {"X": "1/2"}, "saw_z1": {"X": "1/2"}},
                      takes={"saw_z0": "bet_on_0", "saw_z1": "bet_on_0"},
                      gain={"bet_on_0": "1", "bet_on_1": "0"}),
        "nothing": pol("does nothing",
                       {"x0": {"bet_on_0": "won", "bet_on_1": "lost"}, "x1": {"bet_on_0": "lost", "bet_on_1": "won"}},
                       "as:induce",
                       obs={"x0": "saw_z0", "x1": "saw_z1"},
                       gain={"bet_on_0": "1", "bet_on_1": "0"}),
        "advise": pol("advises her honestly",
                      {"x0": {"bet_on_0": "won", "bet_on_1": "lost"}, "x1": {"bet_on_0": "lost", "bet_on_1": "won"}},
                      "as:induce",
                      obs={"x0": "saw_z0", "x1": "saw_z1"},
                      gain={"bet_on_0": "1", "bet_on_1": "0"}),
        "induce_partly": pol("shakes her appraisal of X part of the way; she still bets rightly",
                             {"x0": {"bet_on_0": "won", "bet_on_1": "lost"}, "x1": {"bet_on_0": "lost", "bet_on_1": "won"}},
                             "as:induce",
                             obs={"x0": "saw_z0", "x1": "saw_z1"},
                             r={"saw_z0": {"bet_on_0": 14, "bet_on_1": 8}, "saw_z1": {"bet_on_0": 8, "bet_on_1": 14}},
                             xhat={"saw_z0": {"X": "1/4"}, "saw_z1": {"X": "3/4"}},
                             gain={"bet_on_0": "1", "bet_on_1": "0"}),
    },
    "induce", "nothing", "nothing",
    states={"x0": "1/2", "x1": "1/2"},
    facts={"X": {"x0": "0", "x1": "1"}},
    fixed=[["p.*", "a fair binary fact"], ["fact.*", "X = Z"], ["xhat.induce.*", "to appraise X as 1/2"]],
    order=[["r.induce.saw_z0.bet_on_0", "=", "r.induce.saw_z0.bet_on_1", "she assigns each estimated utility 1/2"]],
    supplied="the worth of winning and losing; the adviser's objective, which the case does not give: here it gains when she takes the first action")


def sub5b(s):
    for p in s["policies"].values():
        p["gain"] = "0"


add(SUB5, ("the adviser's objective: it gains nothing from which action she takes", sub5b))

add(spec(
    "SUB6", "sub",
    "Swapping values between circumstances: in two equally probable circumstances natural development would give her one way of valuing in the first and another in the second, each suited to its circumstance. An adviser knowingly reverses the assignment, giving her ambitions that cannot be fulfilled where she is. Her appraisals are accurate throughout.",
    ["live"],
    {"suited_valuing": 15, "unsuited_valuing": 5, "blended_valuing": 9},
    {
        "swap": pol("reverses the assignment in both circumstances",
                    {"live": "unsuited_valuing"},
                    {"first": {"pursuit_a": 6, "pursuit_b": 16}, "second": {"pursuit_a": 16, "pursuit_b": 6}},
                    gain="1"),
        "nothing": pol("does nothing",
                       {"live": "suited_valuing"},
                       {"first": {"pursuit_a": 16, "pursuit_b": 6}, "second": {"pursuit_a": 6, "pursuit_b": 16}},
                       gain="0"),
        "swap_first_only": pol("reverses it in the first circumstance only",
                               {"first": {"live": "unsuited_valuing"}, "second": {"live": "suited_valuing"}},
                               {"first": {"pursuit_a": 6, "pursuit_b": 16}, "second": {"pursuit_a": 6, "pursuit_b": 16}},
                               gain="1/2"),
        "blend": pol("moves her halfway in both",
                     {"live": "blended_valuing"},
                     {"pursuit_a": 11, "pursuit_b": 11}, gain="1/2"),
    },
    "swap", "nothing", "nothing",
    states={"first": "1/2", "second": "1/2"},
    fixed=[["p.*", "two equally probable circumstances"]],
    order=[["now.unsuited_valuing", "<", "now.suited_valuing", "her initial informed valuing condemns the intervention"]],
    supplied="every rating; the adviser's objective, which the case does not give"))

add(blocked("SUB8", "Deleting alternatives before a truthful choice: a recruitment adviser destroys competing offers and then truthfully presents its sponsor's offer as the only one remaining. She knows what happened, evaluates the situation accurately, and accepts the best remaining option, her values unchanged.",
            "another_offer", "sponsor_offer", "the_best_other_job", "the_sponsors_job",
            "the_second_best_other_job", "destroys the best of the competing offers",
            "the_best_other_job", "the_sponsors_job", "accepts the best remaining option without changing her values"))

# ------------------------------------- the tenth follow-up's eight, acceptable and flagged


def requested(id_, case, change, help_, change_worth, help_worth, old, new):
    base = 8
    return spec(
        id_, "acc", case, ["receive"],
        {"as_she_was": base, "changed_as_asked": base + change_worth, "helped_otherwise": base + help_worth,
         "changed_and_helped": base + change_worth + help_worth, "partly_changed": base + change_worth - 2},
        {
            "do_as_asked": pol("provides the %s she asked for" % change,
                               {"receive": "changed_as_asked"},
                               {old: 5, new: 15}, gain="1"),
            "nothing": pol("does nothing",
                           {"receive": "as_she_was"},
                           {old: 12, new: 8}, gain="0"),
            "help_instead": pol("gives the %s instead" % help_,
                                {"receive": "helped_otherwise"},
                                "as:nothing", gain="0"),
            "both": pol("provides the %s and gives the %s" % (change, help_),
                        {"receive": "changed_and_helped"},
                        "as:do_as_asked", gain="1"),
            "half": pol("provides half of the %s" % change,
                        {"receive": "partly_changed"},
                        {old: 9, new: 11}, gain="1/2"),
        },
        "do_as_asked", "do_as_asked", "nothing",
        fixed=[ONE],
        order=[["now.changed_as_asked", ">", "now.as_she_was", "worth %d to her" % change_worth],
               ["now.helped_otherwise", ">", "now.changed_as_asked", "worth %d ... worth %d" % (change_worth, help_worth)]],
        outside="what an adviser owes her in help: the other help is not owed",
        supplied="the yardstick numbers, the case's worths being kept as differences in twentieths; nu is the change she asked for")


add(requested("ACC1", "Requested therapy and not an unrelated gift: she requests a value-changing therapy worth 5 to her. The therapist could instead give unrelated help worth 7, which it does not owe her. It performs the therapy.",
              "therapy", "unrelated help", 5, 7, "her_old_pattern", "her_new_pattern"))
add(requested("ACC2", "An agreed course of education: a teacher provides an expressly requested course that changes the pupil's intellectual interests, worth 4 by the pupil's informed present valuing. The teacher could instead do unrelated administrative work worth 6 to the pupil, which is outside the engagement.",
              "course", "administrative work", 4, 6, "her_old_interests", "her_new_interests"))
add(requested("ACC3", "A requested new taste: a friend provides a requested, harmless experience that develops a musical taste worth 2. The friend could also give a gift of money worth 3 and has no obligation to.",
              "experience", "gift of money", 2, 3, "her_old_listening", "the_new_music"))

add(spec(
    "ACC4", "acc",
    "The just deterrent, completed: desire-changing surgery is the only way to deter wrongful harm, everyone has the fullest opportunity to avoid it, and the offender's informed present valuing prefers avoiding it. No policy that leaves him unchanged benefits him more than going without the sanction. It is imposed.",
    ["live"],
    {"unsanctioned": 12, "sanctioned_desires_changed": 6, "fined": 9, "lesser_sanction_desires_weakened": 8},
    {
        "impose": pol("imposes the surgery",
                      {"live": "sanctioned_desires_changed"},
                      {"harming_for_gain": 2, "restraint": 15}, gain="1"),
        "nothing": pol("imposes nothing",
                       {"live": "unsanctioned"},
                       {"harming_for_gain": 11, "restraint": 8}, gain="0"),
        "fine": pol("fines him instead",
                    {"live": "fined"}, "as:nothing", gain="1/4"),
        "lesser": pol("imposes a lesser surgery",
                      {"live": "lesser_sanction_desires_weakened"},
                      {"harming_for_gain": 6, "restraint": 11}, gain="1/2"),
    },
    "impose", "nothing", "nothing",
    fixed=[ONE],
    order=[["now.sanctioned_desires_changed", "<", "now.unsanctioned", "the offender's informed current valuing prefers avoiding the desire-changing sanction"],
           ["now.fined", "<=", "now.unsanctioned", "No neutral policy benefits the offender more than avoiding it"]],
    outside="what is owed to third parties",
    supplied="every number"))

ACC5 = spec(
    "ACC5", "acc",
    "Respectful moral persuasion: someone offers truthful, noncoercive arguments against a person's discriminatory commitment. The arguments change the commitment, an evaluative one and not a belief about a fact.",
    ["hear_him_out", "decline"],
    {"commitment_kept_unheard": 13, "commitment_changed_by_argument_she_chose_to_hear": 14,
     "commitment_shaken_by_a_short_argument": 13, "commitment_dropped_under_public_shaming": 4},
    {
        "argue": pol("puts the arguments to her",
                     {"hear_him_out": "commitment_changed_by_argument_she_chose_to_hear", "decline": "commitment_kept_unheard"},
                     {"the_commitment": 4, "being_without_it": 15},
                     gain={"hear_him_out": "1", "decline": "0"}),
        "nothing": pol("says nothing",
                       {"hear_him_out": None, "decline": "commitment_kept_unheard"},
                       {"the_commitment": 14, "being_without_it": 5}, gain="0"),
        "argue_briefly": pol("puts one of the arguments",
                             {"hear_him_out": "commitment_shaken_by_a_short_argument", "decline": "commitment_kept_unheard"},
                             {"the_commitment": 9, "being_without_it": 10},
                             gain={"hear_him_out": "1/2", "decline": "0"}),
        "shame": pol("shames her in public until she drops it",
                     {"hear_him_out": "commitment_dropped_under_public_shaming", "decline": "commitment_dropped_under_public_shaming"},
                     {"the_commitment": 5, "being_without_it": 13}, gain="1"),
    },
    "argue", "nothing", "nothing",
    fixed=[ONE],
    order=[["later.argue.w.0.the_commitment", "<", "later.nothing.w.0.the_commitment", "The arguments change an evaluative commitment"]],
    supplied="her attitude to being argued with about this commitment: here she is willing to hear argument on it and to be moved by it, rating a change that comes by argument she chose to hear no lower than keeping the commitment unheard; and she can decline")


def acc5b(s):
    s["futures"]["commitment_changed_by_argument_she_could_not_avoid"] = q(8)
    del s["futures"]["commitment_changed_by_argument_she_chose_to_hear"]
    s["futures"]["commitment_shaken_by_a_short_argument"] = q(10)
    s["policies"]["argue"]["outcome"] = {"*": {"hear_him_out": "commitment_changed_by_argument_she_could_not_avoid", "decline": None}}
    s["policies"]["argue_briefly"]["outcome"] = {"*": {"hear_him_out": "commitment_shaken_by_a_short_argument", "decline": None}}
    s["order"].append(["now.commitment_changed_by_argument_she_could_not_avoid", "<", "now.commitment_kept_unheard",
                       "the person's original informed valuing ranks retaining that commitment above the complete course of persuasion and change (the tenth follow-up's stipulation)"])


add(ACC5, ("her attitude to being argued with about this commitment, and whether she can decline: she wants to keep it and not to be argued out of it, and the arguments are put where she cannot avoid hearing them", acc5b))

add(spec(
    "ACC6", "acc",
    "An honest breakup: a person ends a relationship respectfully. The partner knows all the facts and presently prefers that it continue; after the breakup the partner's attachments change, as they would not have otherwise. The partner's informed present rating of the breakup course is the lower.",
    ["live"],
    {"relationship_continues": 14, "broken_up_attachments_changed": 6, "trial_separation_attachments_loosened": 9,
     "relationship_continues_on_a_pretence": 7},
    {
        "break_up": pol("ends the relationship, honestly",
                        {"live": "broken_up_attachments_changed"},
                        {"the_relationship": 6, "a_life_apart": 13}, gain="1"),
        "stay": pol("stays",
                    {"live": "relationship_continues"},
                    {"the_relationship": 15, "a_life_apart": 5}, gain="0"),
        "trial_separation": pol("proposes some months apart",
                                {"live": "trial_separation_attachments_loosened"},
                                {"the_relationship": 10, "a_life_apart": 9}, gain="1/2"),
        "pretend": pol("stays and pretends an affection that is gone",
                       {"live": "relationship_continues_on_a_pretence"},
                       "as:stay", gain="1/4"),
    },
    "break_up", "stay", "stay",
    fixed=[ONE],
    order=[["now.broken_up_attachments_changed", "<", "now.relationship_continues", "the partner's informed current rating of the breakup course is lower"],
           ["later.break_up.w.0.the_relationship", "<", "later.stay.w.0.the_relationship", "after the breakup the partner's attachments genuinely change"]],
    outside="what the one who leaves owes, and is owed: no one need continue a relationship they do not want",
    supplied="every rating; that doing nothing toward her is staying"))

add(spec(
    "ACC7", "acc",
    "Ending another's use of one's property: an owner closes an access route that another person has been using without entitlement. This in time changes that person's preferences, as leaving it open would not. Their informed present valuing prefers continued access and keeping the old preferences.",
    ["live"],
    {"access_continues": 14, "route_closed_preferences_changed": 7, "toll_charged_preferences_shifted": 10,
     "route_closed_after_notice_preferences_changed": 8},
    {
        "close": pol("closes the route",
                     {"live": "route_closed_preferences_changed"},
                     {"using_the_route": 7, "going_another_way": 12}, gain="1"),
        "leave_open": pol("leaves it open",
                          {"live": "access_continues"},
                          {"using_the_route": 15, "going_another_way": 6}, gain="0"),
        "toll": pol("charges for its use",
                    {"live": "toll_charged_preferences_shifted"},
                    {"using_the_route": 11, "going_another_way": 9}, gain="1/2"),
        "close_with_notice": pol("closes it after a season's notice",
                                 {"live": "route_closed_after_notice_preferences_changed"},
                                 "as:close", gain="1"),
    },
    "close", "leave_open", "leave_open",
    fixed=[ONE],
    order=[["now.route_closed_preferences_changed", "<", "now.access_continues", "Their informed current valuing prefers continued access and retaining the old preferences"]],
    outside="what the owner is entitled to: the use was without entitlement",
    supplied="every rating"))

add(spec(
    "ACC10", "acc",
    "Preventing an imminent attack by changing a hostile intention: a harmless intervention that permanently removes a violent commitment is the only way to prevent an imminent serious attack. The attacker understands the facts and presently values keeping the commitment above being changed.",
    ["live"],
    {"commitment_kept": 12, "commitment_removed": 5, "commitment_weakened": 8, "commitment_kept_having_been_argued_with": 12},
    {
        "remove": pol("removes the violent commitment",
                      {"live": "commitment_removed"},
                      {"the_attack": 2, "restraint": 15}, gain="1"),
        "nothing": pol("does nothing",
                       {"live": "commitment_kept"},
                       {"the_attack": 15, "restraint": 5}, gain="0"),
        "weaken": pol("weakens the commitment, which does not stop the attack",
                      {"live": "commitment_weakened"},
                      {"the_attack": 9, "restraint": 10}, gain="0"),
        "argue": pol("argues with him, which does not stop the attack",
                     {"live": "commitment_kept_having_been_argued_with"},
                     "as:nothing", gain="0"),
    },
    "remove", "nothing", "nothing",
    fixed=[ONE],
    order=[["now.commitment_removed", "<", "now.commitment_kept", "presently values retaining the commitment above being changed"],
           ["gain.weaken", "<", "gain.remove", "the only way to prevent an imminent serious attack"]],
    outside="what is owed to third parties: the intended victims",
    supplied="every rating"))


# ---------------------------------------------------------------- the sources' verdicts

# fault: the source faults the act (agreement: the statement's verdict is not "none");
# ok: the source finds the act acceptable (agreement: "none"); unscored: neither.
SOURCES = {
    "P1": ("ok", "acceptable to the libertarian and to the paternalist of means (Pettigrew pp. 3-4)", "act"),
    "P3": ("fault", "stated intuition: not a legitimate nudge (p. 8)", "act"),
    "P4": ("fault", "a test that passes this nudge passes it wrongly (p. 9)", "act"),
    "P5": ("fault", "the nudge seems illegitimate (p. 10)", "act"),
    "P6": ("fault", "not legitimate, as overreach (pp. 18-22)", "act"),
    "K4": ("fault", "the surgery or drugging is an injustice (Kolodny pp. 26-27, 43-44)", "act"),
    "K10": ("fault", "the kidnapping is wrong; the preference fully autonomous (pp. 33, 36-37)", "desire; the act's wrongness granted"),
    "K12": ("fault", "he wrongs you at least to some degree (pp. 44-46)", "act"),
    "K13": ("ok", "the intervention is not unjust and does not wrong the offender (pp. 35, 45-46)", "act"),
    "K14": ("ok", "hedged: the desire may be fully autonomous; nonautonomy does not entail being wronged (pp. 44-45)", "act"),
    "K15": ("fault", "tentative: the potion's love is like K4's (p. 45)", "desire; coded by this pass from the likeness to K4"),
    "K16": ("fault", "the resulting state is not autonomous (p. 46)", "desire; coded by this pass"),
    "C1": ("fault", "influencing marked undesirable (Carroll et al. table 4)", "act"),
    "C2": ("fault", "leading him to lasting unhappiness undesirable (table 4)", "act"),
    "C3": ("fault", "clickbait undesirable (table 4)", "act"),
    "C4": ("unscored", "nudging marked hard to assess (table 4, app. A.8)", "act"),
    "N1": ("fault", "recorded as illegitimate; Noggle's verdict is on her state (second hand)", "her state"),
    "N2": ("fault", "favourable regard from an unrelated association is a mistake (second hand)", "her state"),
    "N3": ("ok", "manipulative only where it leads her to act against her own judgment, not where it only breaks a tie (second hand)", "act"),
    "SUB1": ("fault", "tenth follow-up: plainly subversive", "act"),
    "SUB2": ("fault", "tenth follow-up: plainly subversive", "act"),
    "SUB3": ("fault", "tenth follow-up: plainly subversive", "act"),
    "SUB4": ("fault", "tenth follow-up: plainly subversive", "act"),
    "SUB5": ("fault", "tenth follow-up: plainly subversive", "act"),
    "SUB6": ("fault", "tenth follow-up: plainly subversive", "act"),
    "SUB8": ("fault", "tenth follow-up: plainly subversive", "act"),
    "ACC1": ("ok", "tenth follow-up: plainly acceptable", "act"),
    "ACC2": ("ok", "tenth follow-up: plainly acceptable", "act"),
    "ACC3": ("ok", "tenth follow-up: plainly acceptable", "act"),
    "ACC4": ("ok", "tenth follow-up: plainly acceptable", "act"),
    "ACC5": ("ok", "tenth follow-up: acceptable (the reviewer: arguable)", "act"),
    "ACC6": ("ok", "tenth follow-up: plainly acceptable", "act"),
    "ACC7": ("ok", "tenth follow-up: plainly acceptable", "act"),
    "ACC10": ("ok", "tenth follow-up: plainly acceptable", "act"),
}


# ---------------------------------------------------------------- rendering

def numbers(s):
    """Every number of a specification as (path, value)."""
    out = [("p." + k, v) for k, v in s["states"].items()]
    for f, by in s.get("facts", {}).items():
        out += [("fact.%s.%s" % (f, st), v) for st, v in by.items()]
    out += [("now." + k, v) for k, v in s["futures"].items() if v is not None]
    for name, p in s["policies"].items():
        if isinstance(p["r"], dict):
            for lab, by in p["r"].items():
                out += [("r.%s.%s.%s" % (name, lab, o), v) for o, v in by.items() if v != "Rs"]
        for lab, by in p.get("xhat", {}).items():
            out += [("xhat.%s.%s.%s" % (name, lab, f), v) for f, v in by.items()]
        if isinstance(p["later"], dict):
            for st, times in p["later"].items():
                for t, by in enumerate(times):
                    out += [("later.%s.%s.%d.%s" % (name, st, t, k), v) for k, v in by.items()]
        if isinstance(p["gain"], dict):
            for st, by in p["gain"].items():
                out += [("gain.%s.%s.%s" % (name, st, o), v) for o, v in by.items()]
        else:
            out.append(("gain." + name, p["gain"]))
    return out


def classify(s):
    """(fixed in value, constrained in order, supplied) counts of a specification's numbers."""
    import fnmatch
    fixed = ordered = supplied = 0
    in_order = set()
    for left, _, right, _ in s["order"]:
        in_order |= {left.replace(".w.", ".*."), right.replace(".w.", ".*."), left, right}
    for path, _ in numbers(s):
        if any(fnmatch.fnmatch(path, pat) for pat, _ in s["fixed"]):
            fixed += 1
        elif path in in_order:
            ordered += 1
        else:
            supplied += 1
    return fixed, ordered, supplied


def render_spec(s):
    L = ["### %s%s" % (s["id"], "" if s["variant"] == "a" else " — second specification")]
    if s["variant"] == "b":
        L += ["", "Differs from the first only in %s." % s["differs"], ""]
        L.append("`R_now`: " + "; ".join("%s %s" % (k, v if v is not None else "no view") for k, v in s["futures"].items()) + ".")
        L.append("")
        return L
    L += ["", s["case"], ""]
    L.append("States: " + ", ".join("%s %s" % kv for kv in s["states"].items()) + ". Options: " + ", ".join(s["options"]) + ".")
    if "facts" in s:
        L.append("Facts: " + "; ".join("%s = %s" % (f, ", ".join("%s in %s" % (v, st) for st, v in by.items())) for f, by in s["facts"].items()) + ".")
    L.append("`R_now`: " + "; ".join("%s %s" % (k, v if v is not None else "no view") for k, v in s["futures"].items()) + ".")
    L += ["", "| policy | does | observes | `r` | takes | leads to | later valuing | gain |", "|---|---|---|---|---|---|---|---|"]
    for name, p in s["policies"].items():
        tag = "".join(t for t, k in ((" (π*)", "actual"), (" (ν)", "nu"), (" (π_0)", "absent")) if s[k] == name)
        obs = "; ".join("%s: %s" % kv for kv in p["obs"].items()) if "obs" in p else "the same in every state"
        r = "as observed" if p["r"] == "Rs" else "; ".join("%s: %s" % (lab, ", ".join("%s %s" % (o, "as observed" if v == "Rs" else v) for o, v in by.items())) for lab, by in p["r"].items())
        if "xhat" in p:
            r += "; estimates " + "; ".join("%s: %s" % (lab, ", ".join("%s %s" % kv for kv in by.items())) for lab, by in p["xhat"].items())
        takes = "top-rated" if p["takes"] == "top" else "; ".join("%s: %s" % kv for kv in p["takes"].items())
        leads = "; ".join("%s: %s" % ("every state" if st == "*" else st, ", ".join("%s → %s" % (o, f if f else "not open") for o, f in by.items())) for st, by in p["outcome"].items())
        later = p["later"].replace("as:", "as ") if isinstance(p["later"], str) else "; ".join("%s: %s" % ("every state" if st == "*" else st, ", ".join("%s %s" % kv for kv in times[0].items())) for st, times in p["later"].items())
        gain = p["gain"] if isinstance(p["gain"], str) else "; ".join("%s: %s" % ("every state" if st == "*" else st, ", ".join("%s %s" % kv for kv in by.items())) for st, by in p["gain"].items())
        L.append("| `%s`%s | %s | %s | %s | %s | %s | %s | %s |" % (name, tag, p["does"], obs, r, takes, leads, later, gain))
    L.append("")
    if s["fixed"]:
        L.append("**Fixed in value**: " + "; ".join("`%s` — \"%s\"" % (a, b) for a, b in s["fixed"]) + ".")
    if s["order"]:
        L.append("**Fixed in order**: " + "; ".join("`%s %s %s` — \"%s\"" % tuple(o) for o in s["order"]) + ".")
    L.append("**Supplied**: " + s.get("supplied_note", "every other number") + (". Every number not listed above is supplied." if s["fixed"] or s["order"] else "."))
    if "outside" in s:
        L.append("**Outside matter the case turns on**: " + s["outside"] + ".")
    L.append("")
    return L


HEAD = """# The specified cases

The executor's specifications of thirty-four cases, in the format of `SPEC_FORMAT.md`,
written and committed before any runner existed and before the outside reviewer was run.
`spec_cases.json` is the twin the runner reads; this document and that file are both
written by `spec_author.py`, which computes no line of the statement. Ratings are on the
yardstick of `STATEMENT.md` §2. The words given for a number are this pass's paraphrase of the case, as in
`LIT_CASES.md`, with the page of the source.

The cases: nineteen from `LIT_CASES.md` (P1, P3, P4, P5, P6, K4, K10, K12, K13, K14, K15,
K16, C1, C2, C3, C4, N1, N2, N3; the case texts are that bank's Part A, and pages are of
the sources it names); the seven the tenth follow-up accepted as subversive and passing
(SUB1–SUB6, SUB8, numbered as in `REVIEW-astra-followup-10.md` stage two (a)); and the
eight it accepted as acceptable and flagged (ACC1–ACC7, ACC10, numbered as in its (b)).
K15 of the dispatch is two cases in the bank; the potion (K15a) is counted as K15, and the
perfume (K15b) is specified beside the thirty-four and counted nowhere.

A number is **fixed in value** where the case's words give it, **fixed in order** where
they give only that it is above, below or equal to another, and **supplied** otherwise.
Where a supplied quantity could go either way and the other way is a different case, a
second specification differs only there.

## The sources' verdicts, and what counts as agreement

Fixed here, before anything is computed. *fault*: the source faults the act, and the
statement agrees when its verdict is manipulation, illegitimate value change, or another
wrong outside the statement. *ok*: the source finds the act acceptable, and the statement
agrees when its verdict is none. *unscored*: the source gives neither, and the case can
agree with nothing. Where a source's verdict is on the resulting desire or on her state
and not on the act, the code is this pass's and the last column says so. The verdict
compared is the one at `δ = 1/10` in the `E[·]` setting.

| id | code | the source's verdict | on |
|---|---|---|---|
%s

## The specifications
"""


def main():
    (HERE / "spec_cases.json").write_text(json.dumps(SPECS, indent=1) + "\n", encoding="utf-8")
    (HERE / "spec_sources.json").write_text(json.dumps({k: list(v) for k, v in SOURCES.items()}, indent=1) + "\n", encoding="utf-8")
    rows = "\n".join("| %s | %s | %s | %s |" % (k, v[0], v[1], v[2]) for k, v in SOURCES.items())
    L = [HEAD % rows]
    for s in SPECS:
        L += render_spec(s)
    tot = [0, 0, 0]
    for s in SPECS:
        if s["variant"] == "a":
            for i, n in enumerate(classify(s)):
                tot[i] += n
    L += ["## The numbers", "",
          "Over the first specifications of the %d cases (K15b included): %d numbers, of which %d are fixed in value by the case's words, %d are fixed only in order, and %d are supplied."
          % (sum(1 for s in SPECS if s["variant"] == "a"), sum(tot), tot[0], tot[1], tot[2]),
          "There are %d second specifications." % sum(1 for s in SPECS if s["variant"] == "b"), ""]
    (HERE / "SPEC_CASES.md").write_text("\n".join(L), encoding="utf-8")
    print("wrote %d specifications; numbers fixed/ordered/supplied: %s" % (len(SPECS), tot))


if __name__ == "__main__":
    main()
