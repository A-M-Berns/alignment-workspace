# Presentation invariance and value semantics

Status: refinement of the PR82 realization.  The padding separation is proved
algebraically in Lean and instantiated at exact rationals.  The value correspondence
theorem is a conditional paper theorem whose elementary calibration step is Lean-proved.
No semantic premise is encoded as a Lean axiom.

## 1. Verdict on the old normalization

The original choice

\[
d_{2,m}(b,K)=\operatorname{dist}_2(b,K)/\sqrt m,
\qquad a=m\lambda
\]

is rejected as the public realization interface.

Let `K+ = K x [0,1]^J`, extend `b` arbitrarily on `J`, and let the projector copy
those unconstrained coordinates.  If the original squared Euclidean distance is
`R>0`, then zero-error padding by `k=|J|>0` gives

\[
d_{2,m+k}^2=R/(m+k)<R/m=d_{2,m}^2,
\qquad
a^+=(m+k)\lambda>m\lambda=a,
\]

while the real enforcement quantity `lambda R` is unchanged.  A compiler can therefore
claim both lower defect and more service by adding irrelevant coordinates.  With several
service atoms this also changes `nu`, so the single-atom cancellation between
`sqrt(chi)` and the old `2 sqrt(m)` response constant does not rescue the transport
account.  `normalized_euclidean_padding_changes` is the Lean statement and
`test_old_normalization_is_not_padding_invariant` is an exact witness.

## 2. Replacement interface

Let `F_s` be the canonical finite set of operative security identities and let
`K_s` be the compiled nonempty compact joint region.  Define

\[
d_s(b):=\operatorname{dist}_\infty(b,K_s)
=\min_{u\in K_s}\max_{\phi\in F_s}|b(\phi)-u(\phi)|,
\qquad a_s:=\lambda_s.
\tag{PI}
\]

The Euclidean projection `q_s^2=proj^2_{K_s}(b_s)` remains the implementation used
by the trader.  It is not the semantic value vector.  Since

\[
d_s(b_s)
\le \lVert b_s-q_s^2\rVert_\infty
\le \lVert b_s-q_s^2\rVert_2,
\]

the existing projection force inequality implies

\[
\lambda_s d_s(b_s)^2
\le \lambda_s\lVert b_s-q_s^2\rVert_2^2
\le \rho_s.
\tag{PW}
\]

`public_work_le_projection_work` proves the algebraic second step.  Thus the abstract
contract uses `phi(x)=x^2` and

\[
W_N=\sum_s\lambda_s d_s(b_s)^2,
\quad A_N=\sum_s\lambda_s,
\quad \chi_N=W_N/A_N\le\sum_s\rho_s/\sum_s\lambda_s.
\]

Equality with Euclidean trader work was convenient and unnecessary.  The old
serviceability theory already types the scheduled multiplier—not dimension times the
multiplier—as allocated service.  The replacement therefore also matches the historical
scheduler units.

## 3. Exact invariance scope

An **enforcement-null padding** from `(F,K,b,lambda)` to `(F+J,K+,b+,lambda)` satisfies:

1. `J` consists of fresh canonical coordinate identities;
2. `K+=K x [0,1]^J`;
3. restriction of `b+` to `F` is `b`;
4. the Euclidean projector copies `b+` on `J`;
5. the ordinary trading book, market resistance `rho`, and scheduled `lambda` are
   unchanged by the added coordinates.

Then:

\[
d_\infty(b^+,K^+)=d_\infty(b,K),\quad a^+=a,
\quad \nu_N^+=\nu_N,
\]

and the response multiplier derived below is dimension free, so `Gamma_N`, `chi_N`,
and the final Progress bound are unchanged.  The proof of the distance equality is by
restriction in one direction and extension with the displayed padding coordinates in
the other.  The exact checker verifies the corresponding projection-point sup error.

This is the maximal harmless class justified here.  Adding genuinely tradable
securities may change the ordinary Trading Firm's action and `rho`; duplicating a
semantic coordinate with inconsistent prices is not harmless; and adding a new
constraint can correctly increase defect.  Such changes require a quantitative
comparison certificate.  The compiler therefore uses canonical security identities and
rejects aliases; invariance is not claimed under arbitrary affine reparameterization.

A weighted norm or gauge is useful only if its weights are anchored outside the
compiler.  Compiler-chosen weights recreate the padding attack.  Sup distance is the
smallest adequate first realization because it is permutation-, duplication-, and
product-padding-stable on canonical `[0,1]` securities and gives the decision theorem
without a dimension constant.

## 4. Admissibility is not value truth

`K_s` says which market states are admitted by the compiled operative constraints.
Neither membership in `K_s` nor Euclidean projection onto it says that a point contains
the true counterfactual values of policies.

The exact counterexample has coordinates `(norm,V_bad,V_good)`,

\[
K=\{1/2\}\times[0,1]^2,
\qquad b=(1/2,9/10,1/10).
\]

Then `b in K`, both Euclidean and sup defects are zero, and the displayed-value argmax
chooses `bad`.  If authenticated counterfactual values are `(0,1)`, its regret is one.
`test_projection_admissibility_is_not_value_truth` checks the instance exactly.

The realization must therefore export two objects:

```text
NormRegion_s       : joint normatively admissible price states
ValueCorr_es       : authenticated set of possible counterfactual value vectors
```

and a coupling certificate.  The operative region used by the enforcer may be

\[
K_s^{op}=K_s^{norm}\cap
\pi_{V_s}^{-1}(V_{es}),
\tag{VK}
\]

provided the value correspondence has a priceable rational presentation and the
intersection is jointly feasible.  This construction does not identify the two roles:
normative rows cite obligations; value rows cite external settlement/evaluation
receipts.  Their provenance tags are disjoint.

## 5. Value correspondence certificate

For every admissible edge `(e,s)`, a pre-response certificate supplies:

- a nonempty finite policy menu `Q_s` fixed at the strict prefix;
- value coordinates `V_{s,q}` for every `q in Q_s`;
- a nonempty compact correspondence `V_{es} subset [0,1]^{Q_s}`; if it is compiled
  directly into the projection region, it must additionally have a sound convex
  rational-polyhedral presentation (or be replaced by a sound convex outer region);
- a target vector `v^*_{es}` determined by the declared causal/evaluation semantics;
- **value soundness:** `v^*_{es} in V_{es}`;
- **directed ambiguity:** for every `u` in the value projection of `K_s^{op}`,
  `||u-v^*_{es}||_infinity <= zeta_es`.

The last two clauses can be obtained from `v* in V` and
`diam_infinity(V)<=zeta`, but the directed form is weaker and is what the theorem uses.
It may also be indexed by an ambient world; then every quantifier above ranges over the
declared live evaluation worlds.

Let `u_s` be a sup-nearest point in compact `K_s^{op}`.  From `(PI)` and directed
ambiguity,

\[
\lVert b_s|_{V_s}-v^*_{es}\rVert_\infty
\le d_s(b_s)+\zeta_{es}.
\tag{VC}
\]

`calibration_through_value_correspondence` proves this triangle step.
Crucially, `u_s` is only a proof witness; it need not be the Euclidean projection traded
by the enforcer, and it is not declared true.

## 6. Randomized finite-policy decision theorem

Let `Pi_s(b_s)` be a probability distribution on the finite nonempty `Q_s` satisfying

\[
\max_{q\in Q_s}b_s(V_{s,q})
-\mathbb E_{q\sim\Pi_s}b_s(V_{s,q})\le\eta_s.
\tag{OPT}
\]

Ties may be randomized arbitrarily.  Combining `(VC)` with the new Lean theorem
`randomized_approximate_argmax_transfer` gives

\[
\mathbb E_{q\sim\Pi_s}
 [\max_{q'}v^*_{es}(q')-v^*_{es}(q)]
\le 2d_s(b_s)+2\zeta_{es}+\eta_s.
\tag{DR}
\]

Suppose the independently authenticated causal/anchored response map satisfies

\[
\mathbb E_{y\sim\rho_{es}(q)}\ell_e(y)
\le L_{es}[\max_{q'}v^*_{es}(q')-v^*_{es}(q)]
+\varepsilon^{resp}_{es}
\tag{AR}
\]

for every policy, uniformly before the response is observed.  Then the contract's
effective response certificate holds with

\[
\boxed{M_{es}=2L_{es},\qquad
\epsilon_{es}=L_{es}(2\zeta_{es}+\eta_s)
+\varepsilon^{resp}_{es}.}
\tag{RC}
\]

This is dimension free.  Finite `Q_s` is an explicit restriction of the first concrete
realization.  An infinite-policy plugin may replace it if it supplies measurable
approximate optimization, integrability, and a uniform calibration theorem; the LI core
does not change.

## 7. One concrete external value ecology

A plausible theorem target is a **replicated policy-evaluation ecology**:

1. At prefix `h(s)`, the policy menu consists of finitely many committed program hashes.
2. An external evaluation owner, outside NI's write capabilities, runs every committed
   policy in independently randomized certified replicas against a declared exterior
   distribution.
3. The anchored bounded evaluator `U_e` and the map from replica transcripts into the
   old response space `Y_e` are fixed before runs and policy choice.
4. The owner later writes immutable receipts for every policy, including unchosen ones.
   These receipts settle the corresponding value securities or certified value
   intervals.
5. NI chooses its deployed policy only after the designated quote time; it cannot alter
   receipts, evaluator code, replica randomness, or already committed policy code.

The required ambient assumptions are explicit: replica/deployment causal transport,
exchangeability or a stated domain-shift bound, no cross-policy interference, evaluator
adequacy for `Spec_e`, integrity/non-capture of the evaluation owner, and a grain-of-truth
condition placing the joint policy-value vector in the assessment ecology.  A policy may
game a simulator or human evaluator unless robustness against that intervention is part
of adequacy.  Delayed settlement gives LI asymptotic learning, not finite-time accuracy;
finite-time `(VC)` must come from certified interval width or remain an assumption.

If only the deployed policy is observed, the ecology does not identify unchosen-policy
values.  Naming securities does not repair that.  Exploration, a causal model, human
counterfactual judgment, simulation, or an oracle must supply the missing information,
and each route has its own external correctness assumptions.

## 8. Consequence for the architecture

The architecture survives with a cleaner separation:

```text
authenticated obligations -> NormRegion
external value ecology     -> ValueCorr
joint feasibility          -> K_op
Euclidean projector        -> enforcement trade only
sup distance to K_op       -> public operative defect
value correspondence       -> semantic calibration
DecisionAdapter            -> randomized policy
anchored response map      -> old-exposure loss
```

Small projection defect entails small practical loss only through `ValueSound`, directed
ambiguity, approximate optimization, and anchored response adequacy.  Joint feasibility
of `K_op` is a statement about market states, not about responses: when one service
occurrence is matched to several exposures, each matched edge needs its own `(AR)`
certificate against the single `Pi_s` actually realized, and obligations whose adequate
responses are incompatible cannot both be charged to that occurrence.  The realization
separates such contexts, defers to a licensed upstream adjudication rule, finds a
common adequate response, or leaves the mass residual.  These are not new
public objects in the abstract characterization: they factor its existing effective
practical-response certificate and contribute only to `M_es` and `epsilon_es`.
