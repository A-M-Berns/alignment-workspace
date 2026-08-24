"""Restricted compilation: finite environment + finite-state recurrent
service monitors + coalescing => Request-Response game, checked as a
play-level correspondence on ultimately periodic plays."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

from embeddings import RRGame, rr_occurrences, rr_play_winning


def compile_to_rr(env_states, s0, delta, actions, mon):
    """Compile a turn-based generic fragment to an RR game.

    - `delta(s, a)` -> set of (y, s') pairs (finite environment).
    - `mon`: recurrent type monitor with states {'idle', 'open', 'acc'},
      step function mon(m, a, y) -> m'; 'acc' counts as the response
      and behaves as 'idle' for the next transition (reset-on-accept =
      coalescing recurrent service).

    Vertices: ('act', s, m) for Player 0 (choose an action) and
    ('rsp', s, m, a) for Player 1 (choose a permitted response).
    Q = vertices whose monitor component is 'open'; P = 'acc'.
    """
    verts, edges, owner = set(), {}, {}
    frontier = [("act", s0, "idle")]
    while frontier:
        v = frontier.pop()
        if v in verts:
            continue
        verts.add(v)
        if v[0] == "act":
            _, s, m = v
            owner[v] = 0
            succ = []
            for a in actions:
                w = ("rsp", s, m, a)
                succ.append(w)
                frontier.append(w)
            edges[v] = tuple(succ)
        else:
            _, s, m, a = v
            owner[v] = 1
            base = "idle" if m == "acc" else m
            succ = []
            for (y, s2) in delta(s, a):
                w = ("act", s2, mon(base, a, y))
                succ.append(w)
                frontier.append(w)
            edges[v] = tuple(succ)
    q_set = frozenset(v for v in verts if v[0] == "act" and v[2] == "open")
    p_set = frozenset(v for v in verts if v[0] == "act" and v[2] == "acc")
    game = RRGame(tuple(sorted(verts)), edges, owner, ((q_set, p_set),))
    return game, ("act", s0, "idle")


def all_lassos(game, start, max_len):
    """Every (stem, cycle) lasso from `start` with |stem|+|cycle| <=
    max_len, cycle nonempty and closed under the edge relation."""
    out = []
    def walk(path):
        v = path[-1]
        for w in game.edges[v]:
            if w in path:
                i = path.index(w)
                out.append((tuple(path[:i]), tuple(path[i:])))
            elif len(path) < max_len:
                walk(path + [w])
    walk([start])
    return out


class TestCompilation(unittest.TestCase):
    def fragment(self):
        # Environment: probing may succeed or stall; a request opens
        # whenever the environment emits "need" and closes when a probe
        # returns "fixed".
        def delta(s, a):
            if a == "wait":
                return {("need", "hot"), ("quiet", s)}
            if a == "probe":
                if s == "hot":
                    return {("fixed", "cool"), ("stall", "hot")}
                return {("quiet", s)}
            raise KeyError(a)

        def mon(m, a, y):
            if m == "idle":
                return "open" if y == "need" else "idle"
            if m == "open":
                return "acc" if y == "fixed" else "open"
            raise KeyError(m)
        return delta, ("wait", "probe"), mon

    def occurrences_all_closed(self, game, stem, cycle):
        # Unroll far enough that any occurrence opened in the first
        # period must close if it ever will (state space is finite and
        # the play is periodic).
        reps = len(cycle) + 3
        prefix = tuple(stem) + tuple(cycle) * reps
        horizon = len(stem) + len(cycle)
        occ = rr_occurrences(game, prefix)
        return all(closed is not None
                   for (_, opened, closed) in occ if opened <= horizon)

    def test_play_level_correspondence_on_all_small_lassos(self):
        delta, actions, mon = self.fragment()
        game, start = compile_to_rr({"cool", "hot"}, "cool", delta,
                                    actions, mon)
        lassos = all_lassos(game, start, 12)
        self.assertGreaterEqual(len(lassos), 8)   # every simple lasso
        seen = {True: 0, False: 0}
        for stem, cycle in lassos:
            rr = rr_play_winning(game, stem, cycle)
            occ = self.occurrences_all_closed(game, stem, cycle)
            self.assertEqual(rr, occ, (stem, cycle))
            seen[rr] += 1
        # Both verdicts occur: the correspondence is not vacuous.
        self.assertGreater(seen[True], 0)
        self.assertGreater(seen[False], 0)


if __name__ == "__main__":
    unittest.main()
