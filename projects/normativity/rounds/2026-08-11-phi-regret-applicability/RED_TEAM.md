# Independent red team

**Verdict: Near miss.** The review received the artifacts and audit questions,
not the constructing transcript.

## Fatal counterexample

The proposed encoding did not produce a fixed eight-action set. `Response`
equality includes the occasion-specific ledger effect, including the decision
obligation identifier. The union of repository-native responses through horizon
`T` therefore has

```
N_T = 3T + 5
T = 12, 24, 48, 96  ->  N_T = 41, 77, 149, 293.
```

Blum--Mansour Theorem 18 then gives
`O(sqrt(T N_T log K)) = O(T sqrt(log K))`, which does not supply the sublinear
bridge item 30 needs. Retraction padding is algebraically valid for a fixed
union; the implementation hid the horizon growth in that union.

The missing interface is a fixed eight-label online action type containing only
`basis`, the contextual positive/negative verdict choice, and `tolled`, with an
occasion-local decoder deriving the ledger effect. Item 29 needs a proof and
test that encode/decode preserves action maps, charge, and comparator regret and
keeps `N=8` uniformly.

## Legality seal limit

`sealed_legality_state` removes future rows, account data, service costs, and
actual tariffs from the arguments passed to a callback. It does not sandbox an
arbitrary Python callable. A guard closing over the original occasion can still
read its tariff and fire through `induced_action_map`. The finite comparator
programs therefore remain audited/trusted code unless callbacks are replaced by
an interpreted declarative rule language or another enforced capability
boundary. The tests now exhibit both the argument seal and the closure bypass.

## Theorem audit

- Blum--Mansour §2 and Theorem 18 are the closest source result: modification
  rules may take history and action, and `F^t` is history-indexed.
- Theorem 5 is too narrow; Gordon--Greenwald--Marks Theorem 1 assumes fixed
  transformations and is a worse fit for prefix guards.
- Frozen filings, actual-prefix guards, and no suspension make replay additive;
  unrestricted replay remains outside the theorem.
- Full charge vectors are exact and bounded by 2 in the item-30 configuration.
- The theorem controls expected mixed loss. An exact sampled-trajectory claim
  would additionally need a sampling/concentration statement.
- Identity and the canonical repair inhabit a nontrivial fragment. Two of the
  specified nine rules are not implemented, so the full class is not yet an
  executable fixed comparator set.

## Checklist verdicts

| question | verdict |
|---|---|
| BM comparator class? | yes, after a causal fixed-action encoding |
| fixed action set? | false in the implemented encoding |
| invalid padding? | raw padding is correctly rejected; horizon growth was missed |
| fixed ex ante? | specification only; full nine-rule list absent |
| prefix guard allowed? | yes, if predictable from pre-action history |
| future/current leakage? | removed from callback arguments, not from closures/globals |
| legality independent of profit? | true for audited defaults; not enforced for arbitrary callbacks |
| replay changes future state? | not in frozen/no-suspension v1; yes in unrestricted replay |
| bounded lifetime influence? | only under no coupling or bounded fences |
| counterfactual feedback? | full charge vector available |
| bounded loss? | yes, `[0,2]` |
| regret-preserving encoding? | padding lemma yes; fixed-`N` repository encoding absent |
| comparator class inhabited? | nontrivial fragment yes; nine-rule class incomplete |
| better neighboring theorem? | no; BM18 remains closest |
| item 30 smuggled in? | no experiment, but “unblocked” was unsupported |
| philosophical overstatement? | charge-only caveat sound; distinguish expected from sampled regret |

No major failure was patched silently. The counterexamples are part of the
round's test suite and the main verdict follows them.
