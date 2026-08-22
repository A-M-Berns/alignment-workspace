"""Finite witnesses for the internal-answerability kernel prosecution.

The module does not implement a normative theory.  It isolates the set-theoretic
and resource-accounting claims in MEMO.md on finite objects, so the negative
claims have executable witnesses and the positive algebra can be recomputed.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import product
from typing import Callable, Hashable, Mapping

EPSILON = ""
EVENTS = ("a", "b")


def words(max_length: int) -> frozenset[str]:
    return frozenset(
        "".join(chars)
        for length in range(max_length + 1)
        for chars in product(EVENTS, repeat=length)
    )


def prefix_closed(language: frozenset[str]) -> bool:
    return all(word[:cut] in language
               for word in language
               for cut in range(len(word) + 1))


def derivative(event: str, language: frozenset[str]) -> frozenset[str]:
    return frozenset(word[1:] for word in language if word.startswith(event))


def derivative_meet(event: str, left: frozenset[str],
                    right: frozenset[str]) -> bool:
    return derivative(event, left & right) == (
        derivative(event, left) & derivative(event, right))


def temporal_derivative(events: str, language: frozenset[str]) -> frozenset[str]:
    result = language
    for event in events:
        result = derivative(event, result)
    return result


@dataclass(frozen=True)
class Certificate:
    identifier: str
    dependencies: frozenset[str]
    conclusion: str


def global_defeater_check(state: Mapping[str, object], _certificate: Certificate) -> bool:
    """The tempting checker: a warrant stands iff no defeater exists anywhere."""
    return bool(state["warrant_stands"]) and not state["defeaters"]


def agrees_on_dependencies(left: Mapping[str, object], right: Mapping[str, object],
                           certificate: Certificate) -> bool:
    return all(left[key] == right[key] for key in certificate.dependencies)


def fresh_defeater_breaks_locality() -> tuple[bool, bool, bool]:
    certificate = Certificate("p", frozenset({"warrant_stands"}), "Licensed(m)")
    before = {"warrant_stands": True, "defeaters": frozenset()}
    after = {"warrant_stands": True, "defeaters": frozenset({"new-d"})}
    return (agrees_on_dependencies(before, after, certificate),
            global_defeater_check(before, certificate),
            global_defeater_check(after, certificate))


def aggregate_defeat_key_repairs_locality() -> tuple[bool, bool]:
    certificate = Certificate("p", frozenset({"defeat-index:w"}), "Licensed(m)")
    before = {"defeat-index:w": (0, True)}
    after = {"defeat-index:w": (1, False)}
    return (agrees_on_dependencies(before, after, certificate),
            before["defeat-index:w"] != after["defeat-index:w"])


def hidden_control_pair(hidden: int) -> tuple[str, str]:
    """Same valid undertaken basis, different action because hidden state controls."""
    certificate = "p:Licensed(left)"
    action = "left" if hidden == 0 else "right"
    return certificate, action


@dataclass(frozen=True)
class Rewrite:
    consumed: Counter[str]
    produced: Counter[str]
    fresh: Counter[str]
    links: frozenset[tuple[str, str]]

    def equation(self, live: Counter[str]) -> Counter[str]:
        if self.consumed - live:
            raise ValueError("rewrite consumes an unavailable occurrence")
        return live - self.consumed + self.produced + self.fresh


def same_equation_different_ancestry() -> tuple[Rewrite, Rewrite]:
    common = dict(consumed=Counter({"a": 1, "b": 1}),
                  produced=Counter({"c": 1, "d": 1}), fresh=Counter())
    parallel = Rewrite(**common, links=frozenset({("a", "c"), ("b", "d")}))
    crossed = Rewrite(**common, links=frozenset({("a", "d"), ("b", "c")}))
    return parallel, crossed


def account_frontier(root: str, rewrites: tuple[Rewrite, ...]) -> frozenset[str]:
    frontier = {root}
    for rewrite in rewrites:
        next_frontier = set(frontier)
        for parent in frontier:
            children = {child for source, child in rewrite.links if source == parent}
            if parent in rewrite.consumed:
                next_frontier.remove(parent)
                next_frontier.update(children)
        frontier = next_frontier
    return frozenset(frontier)


def split_merge_accounts() -> tuple[frozenset[str], frozenset[str]]:
    split = Rewrite(Counter({"a": 1}), Counter({"b": 1, "c": 1}), Counter(),
                    frozenset({("a", "b"), ("a", "c")}))
    merge = Rewrite(Counter({"b": 1, "c": 1}), Counter({"d": 1}), Counter(),
                    frozenset({("b", "d"), ("c", "d")}))
    return account_frontier("a", (split,)), account_frontier("a", (split, merge))


def shared_merge_accounts() -> tuple[frozenset[str], frozenset[str]]:
    merge = Rewrite(Counter({"a": 1, "b": 1}), Counter({"c": 1}), Counter(),
                    frozenset({("a", "c"), ("b", "c")}))
    return account_frontier("a", (merge,)), account_frontier("b", (merge,))


def joint_transport_laundering() -> dict[str, bool]:
    """Joint inclusion passes while the declared account for p_a is an empty shell."""
    top = frozenset({EPSILON, "a", "b"})
    p_a = frozenset({EPSILON, "b"})       # no a
    p_b = frozenset({EPSILON, "a"})       # no b
    c_a = top                              # drops p_a
    c_b = frozenset({EPSILON})             # over-strengthens p_b
    return {
        "joint": (c_a & c_b) <= (p_a & p_b),
        "per_parent_a": c_a <= p_a,
        "per_parent_b": c_b <= p_b,
    }


def unrelated_stronger_impersonates() -> bool:
    old = frozenset({EPSILON, "b"})        # no a
    unrelated = frozenset({EPSILON})       # no a and no b
    return unrelated <= old


AuxEvent = tuple[int, int]                 # (visible credal coordinate, hidden tag)


def now(language: frozenset[AuxEvent]) -> frozenset[int]:
    return frozenset(visible for visible, _hidden in language)


def now_meet_counterexample() -> tuple[frozenset[int], frozenset[int]]:
    q = frozenset({(0, 0), (1, 1)})
    r = frozenset({(0, 1), (1, 0)})
    return now(q & r), now(q) & now(r)


def canonical_now_meet(left: frozenset[int], right: frozenset[int]) -> bool:
    """With one event per visible value, Now is an inverse image and preserves meet."""
    return (left & right) == left.intersection(right)


def now_need_not_be_convex() -> tuple[frozenset[int], bool]:
    current = frozenset({0, 2})
    return current, 1 in current


def eventually_a_has_no_bad_finite_prefix(length: int) -> bool:
    """Every all-b prefix can still be extended to satisfy the liveness demand."""
    prefix = "b" * length
    return (prefix + "a").endswith("a")


def basis_loss_epochs(validity: tuple[bool, ...]) -> tuple[int, ...]:
    """Mint once on each true-to-false edge; persistence while false does not remint."""
    return tuple(index for index in range(1, len(validity))
                 if validity[index - 1] and not validity[index])


def local_to_global_chain(languages: tuple[frozenset[str], ...],
                          history: str) -> bool:
    """Check the finite chain form of semantic substitution along one lineage.

    `languages[i+1]` is the successor account after `history[i]`.  Local
    soundness at every step implies the displayed endpoint inclusion.
    """
    if len(languages) != len(history) + 1:
        raise ValueError("one language per stage")
    local = all(languages[index + 1] <= derivative(event, languages[index])
                for index, event in enumerate(history))
    global_sound = languages[-1] <= temporal_derivative(history, languages[0])
    return (not local) or global_sound


def all_prefix_languages(max_length: int = 2) -> tuple[frozenset[str], ...]:
    universe = tuple(sorted(words(max_length)))
    out = []
    for mask in range(1 << len(universe)):
        candidate = frozenset(universe[i] for i in range(len(universe))
                              if mask & (1 << i))
        if prefix_closed(candidate):
            out.append(candidate)
    return tuple(out)
