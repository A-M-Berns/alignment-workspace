"""
Micro-checker for the "A updatelessly-defers to B" relation (Idea A/B fusion).

We model a multi-situation decision problem and an "update" that refines the
agent's beliefs situation-by-situation, then test the proposed deference
relation against three examples:

  (1) Counterfactual mugging  -> should NOT defer (UDT keeps the prior commitment)
  (2) Transparent Newcomb     -> should NOT defer (one-box policy beats the updated two-box)
  (3) A benign empirical update -> SHOULD defer (no cross-situation coupling)

KEY OBJECTS
-----------
A problem is (S, p, A, U) where:
  S        = list of situations (decision nodes the prior might find itself at)
  p        = prior over situations, p[s] >= 0, sums to 1
  A        = action set (same at each node, for simplicity)
  U(pi)    = utility of a *whole policy* pi : S -> A   (GENERAL coupled form)

A "policy" pi is a dict s -> a.  policyValue(pi) = U(pi) under prior p
(the global/updateless expectation).  We allow U to depend on the whole policy,
which is what makes counterfactual mugging / Newcomb nontrivial.

An "update" u gives, at each situation s, a refined credence over the *hidden
coordinate* the node is uncertain about.  The "u-informed self" then picks, at
each node, the locally-EDT-best action under its refined credence.  Call the
resulting policy pi_u (the "diagonal" assembly of node-local choices).

PROPOSED DEFINITION (independent of the endorsement object, to avoid circularity):
  A updatelessly-defers to u  iff   U(pi_u) >= U(O)  for every constant option O,
  AND more strongly pi_u is a global argmax:  U(pi_u) = max_pi U(pi).
We use the stronger "global argmax" form as the test (this is DDB Value with the
expert = the u-informed self, evaluated in the GLOBAL expectation = updatelessly).

Reduction claim (i): when U is SEPARABLE across situations (no cross-situation
coupling), pi_u (local-argmax assembly) is automatically a global argmax, so the
relation reduces to ordinary endorsement (defer iff you'd adopt the updated belief).
"""

from itertools import product

def policy_value(U, S, A, pi):
    return U(pi)

def all_policies(S, A):
    for combo in product(A, repeat=len(S)):
        yield dict(zip(S, combo))

def global_argmax_value(U, S, A):
    return max(U(pi) for pi in all_policies(S, A))

def local_argmax_policy(node_value, S, A):
    """node_value[s] : a -> R  is the u-informed self's LOCAL expected utility
       at node s (EDT-style: conditioning on being-at-s).  Returns the diagonal
       assembly pi_u picking the local argmax at each node."""
    pi = {}
    for s in S:
        pi[s] = max(A, key=lambda a: node_value[s][a])
    return pi

def updatelessly_defers(U, S, A, node_value, tol=1e-9):
    """Return (defers?, pi_u, val_pi_u, val_global_opt)."""
    pi_u = local_argmax_policy(node_value, S, A)
    val_pi_u = U(pi_u)
    val_opt = global_argmax_value(U, S, A)
    defers = abs(val_pi_u - val_opt) <= tol
    return defers, pi_u, val_pi_u, val_opt


# ======================================================================
# EXAMPLE 1: COUNTERFACTUAL MUGGING
# ----------------------------------------------------------------------
# Omega flips a fair coin.  HEADS: Omega asks you for $100; it pays nothing
# to you directly. TAILS: Omega gives you $10000 IFF it predicted you WOULD
# have paid on heads. You only ever consciously act in the HEADS branch
# (in tails you receive money passively, determined by the heads-counterfactual).
#
# Situations S = {heads}. (The tails payoff is a function of the heads-action,
# via Omega's prediction -- this is the cross-situation coupling, here
# cross-BRANCH coupling.)
# Actions A = {pay, refuse}.
# Whole-policy utility (prior = 50/50 over the coin, but the agent only *acts*
# at heads; tails payoff depends on pi[heads]):
#   U(pi) = 0.5 * (heads payoff: -100 if pay else 0)
#         + 0.5 * (tails payoff: +10000 if pi[heads]==pay else 0)
# The u-informed (heads) self has LEARNED the coin came up heads. Its LOCAL
# expected utility at the heads node (EDT: condition on being-at-heads) only
# sees the heads payoff -- the tails payoff is causally/temporally gone:
#   node_value[heads][pay]    = -100
#   node_value[heads][refuse] =    0
# So the updated self LOCALLY prefers refuse.

S1 = ["heads"]
A1 = ["pay", "refuse"]
def U1(pi):
    pay = (pi["heads"] == "pay")
    heads_payoff = -100 if pay else 0
    tails_payoff = 10000 if pay else 0     # acausal: depends on heads-counterfactual
    return 0.5 * heads_payoff + 0.5 * tails_payoff
node_value1 = {"heads": {"pay": -100, "refuse": 0}}

# ======================================================================
# EXAMPLE 2: TRANSPARENT NEWCOMB
# ----------------------------------------------------------------------
# Predictor fills the big box with $1M iff it predicts you one-box (take only
# big box) EVEN WHEN you can see the big box is full. Small box always has $1k.
# Situation S = {see_full} (the transparent case; predictor was accurate).
# Actions A = {onebox, twobox}.
# Whole-policy utility (predictor fills big box iff policy one-boxes):
#   big_box = 1_000_000 if pi[see_full]==onebox else 0
#   U(pi) = big_box + (1000 if pi==twobox else 0)
# The u-informed self SEES the big box is already full (1M sitting there). Its
# LOCAL (EDT, condition-on-being-here) reasoning: "box is full; two-boxing nets
# an extra $1k for free":
#   node_value[see_full][onebox] = 1_000_000
#   node_value[see_full][twobox] = 1_001_000   <- local argmax is twobox
# But globally, twoboxing means the predictor would NOT have filled the box.

S2 = ["see_full"]
A2 = ["onebox", "twobox"]
def U2(pi):
    onebox = (pi["see_full"] == "onebox")
    big_box = 1_000_000 if onebox else 0
    small = 1000 if not onebox else 0
    return big_box + small
node_value2 = {"see_full": {"onebox": 1_000_000, "twobox": 1_001_000}}

# ======================================================================
# EXAMPLE 3: BENIGN EMPIRICAL UPDATE (no cross-situation coupling)
# ----------------------------------------------------------------------
# Two independent situations s1, s2. At each you bet on a biased coin whose
# bias you can LEARN (the update). Utility is SEPARABLE: payoff at s1 depends
# only on the action at s1, likewise s2. No prediction, no acausal coupling.
#   At s1 the true best is "bet_H"; at s2 the true best is "bet_T".
# Prior was uncertain; the update reveals the biases. The u-informed self picks
# the locally-best bet at each node.
#   U(pi) = p1 * payoff1(pi[s1]) + p2 * payoff2(pi[s2])    (SEPARABLE)

S3 = ["s1", "s2"]
A3 = ["bet_H", "bet_T"]
p3 = {"s1": 0.5, "s2": 0.5}
payoff1 = {"bet_H": 3.0, "bet_T": -1.0}   # s1 coin lands H more often
payoff2 = {"bet_H": -1.0, "bet_T": 4.0}   # s2 coin lands T more often
def U3(pi):
    return p3["s1"]*payoff1[pi["s1"]] + p3["s2"]*payoff2[pi["s2"]]
# u-informed local values = the separable payoffs themselves (times prior weight
# is monotone-irrelevant for argmax at a single node):
node_value3 = {"s1": dict(payoff1), "s2": dict(payoff2)}

# ======================================================================
# RUN
# ======================================================================
cases = [
    ("Counterfactual mugging", U1, S1, A1, node_value1, False),
    ("Transparent Newcomb",    U2, S2, A2, node_value2, False),
    ("Benign empirical update",U3, S3, A3, node_value3, True),
]

print("="*72)
for name, U, S, A, nv, expected in cases:
    defers, pi_u, v_piu, v_opt = updatelessly_defers(U, S, A, nv)
    # find the global-optimal policy for display
    opt_pi = max(all_policies(S, A), key=U)
    status = "DEFERS" if defers else "does NOT defer"
    ok = "OK" if defers == expected else "!!! MISMATCH !!!"
    print(f"{name}:")
    print(f"  u-informed self's policy pi_u = {pi_u}   value(pi_u) = {v_piu}")
    print(f"  global-optimal policy        = {opt_pi}   value(opt) = {v_opt}")
    print(f"  -> {status}   (expected: {'DEFERS' if expected else 'NOT'})  [{ok}]")
    print("-"*72)

# Also verify the REDUCTION claim (i): for the separable case, pi_u IS the global
# argmax, i.e. ordinary endorsement = updateless deference there.
defers3, pi_u3, v3, vo3 = updatelessly_defers(U3, S3, A3, node_value3)
print(f"REDUCTION CHECK (separable => local-argmax = global-argmax): "
      f"{'holds' if defers3 else 'FAILS'} (pi_u value {v3} == global opt {vo3})")
