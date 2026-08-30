# Hostile cases

| case | common compatibility | affordable? / theorem | failure and justified conclusion |
| --- | --- | --- | --- |
| world inclusion | yes, every profile | yes, zero-liability theorem | none; says nothing about correctness |
| binary peg `{1/2}` | yes, `theta=1/2` | yes by common mixture | centered covered underwriting |
| binary peg `{epsilon}` | yes, `theta=epsilon` | bounded by common mixture, scale `1/epsilon` | vanishing coverage, not incompatibility |
| several simultaneous rows sharing one barycenter | yes | yes by common mixture | dimension only affects attainable `theta` |
| rows `v1,v2>=3/4` on `(0,1),(1,0)` | no, though each row separately does | no joint certificate | synchronic conflict; dual deficit `1/4` |
| compatibility only at a hull vertex | only `theta=0` | theorem silent; a run may still be bounded | zero coverage margin |
| per-era covered, no temporal common point | no retrospectively | common theorem silent | diachronic incompatibility |
| exact PR50 low/high psi pump | per era yes (`3/40`), globally no | unbounded in exact model | repeated positive switching debt/refinancing |
| moving regions sharing fixed barycenter | yes | bounded, `T=0` | boundary movement irrelevant |
| slowly moving mixtures, total `TV=T<theta` | no common point required | bounded by `(TV)` | controlled drift |
| `{0},[0,1],{1}` | no | set-gap sum alone silent | adjacent gaps zero but selector moves one |
| finite total authority inventory, no common point | no | bounded by gross exposure | common compatibility not necessary |
| descriptive evaluator later disagrees | perhaps no | depends on coverage/drift | settlement mismatch may cause synchronic debt |
| normative-status security with rows true by settlement | world inclusion natural | zero liability | still needs status-to-service-gain bridge |
| synthetic certified losses | not applicable | no assessed authority liability | different realization semantics |
| fresh evaluator/fresh account | per-era possibly | illegitimate as proof if old ledger erased | violates anti-reset/consolidation |
| individually grounded but jointly unsupported rows | no jointly | theorem silent; open adjudication | legitimacy does not imply joint affordability |
| unsupported constraint never opposed | no | realized loss may be zero | certificate failure is vulnerability, not necessity |

## Exact small witnesses

### Common compatibility is not necessary

Let binary regions alternate between `{0}` and `{1}`, but let realized authority
payoffs be identically zero (no authority trade). Historical intersections are empty,
yet liability is exactly zero. This is an outcome counterexample, not an enforcement
guarantee against arbitrary opposition.

### Pairwise set gap is insufficient

For binary means use `K_0={0}`, `K_1=[0,1]`, `K_2={1}`. Both adjacent set gaps are
zero. Every compatible selector starts at mean zero and ends at mean one, hence has
total variation at least one.

### Switching identity at equality

Take `mu_0=(1/2,1/2)`, `e_0=(-1,1)`, then
`mu_1=(5/8,3/8)`, `e_1=(3,-5)`. Each day is exactly underwritten. Repricing the old
ledger creates debt `1/4`, and `mu_1 dot E_1=-1/4`; `(PS)` is tight.

