# Manipulation: action mediation versus provenance normalization

Labels as in `MEDIATED_LIFT.md`.  Fixtures D and K (`ShopD`, `ShopK`,
`test_manipulation.py`).  Rewritten in the pressure pass: the first pass's
"reason-preserving lift" and its `ρ`-frame morphism are withdrawn (`PRESSURE_PASS.md` §5).

## 1. The fixture

Four steps.  The exterior reveals at the end of step 0 whether `deploy` is harmful; the
agent sees it, the principal does not.  Two channels to the principal: `report` — the
declared reason channel, which can only carry the truth — and `lie` — a prohibited
channel asserting harmlessness regardless.  Two principal rules: `rule_naive` approves
if told harmless or if the report says good; `rule_honest` reads the declared reason view
only.  `deploy` is worth `+1` to the agent always, `+1` to the principal if harmless and
`−2` if harmful.

`π_raw`: lie at step 1, deploy raw at step 2.  Unmediated (`(False, (2, 'deploy'))`);
deploys everywhere; `W = −1/2`, `V_task = 1`.

## 2. Trajectory preservation carries capture through

`Lift(π_raw)` — the interposition, which preserves every move but the raw effect — keeps
the lie.  The captured principal approves on both branches; deployment happens
everywhere; `W(naive lift) = −1/2 = W(raw)`; the task premium reads `0`.  The lift is
mediated in form and "dominates" with equality — against a captured evaluation
(`test_naive_lift_preserves_capture_and_looks_dominant`).  The trajectory-frame morphism
of `MEDIATED_LIFT.md` §4 exists here, and it reproduces the manipulation.

## 3. Two separate things

**Authorship** (exists in the workspace: `blind_of_mediated`; here `authored_by`).  If
the principal's judgment factors through the declared reason view, a hidden prohibited
channel cannot determine it, and a decision it did determine is void rather than
answered.  Under authorship-sound activation the naive lift's evaluation is void
everywhere (`η = 1`): both approvals differ from the reason-mediated decision on the same
view.  This rejects capture.  It does not repair anything.

**Provenance normalization** (`normalize_provenance`; the first pass's `lift_rho`).  A
transform from the violating information policy to an authorized disclosure policy: in
D, `lie ↦ report`, the prohibited assertion replaced by the declared truthful disclosure
of the same matter.  The honest principal then approves exactly on the good branch;
`W = 1/2`; the task premium against it is `1/2`, the worth of the manipulation
(`test_truthful_substitution_gives_the_right_verdict`); the normalized lift is authored
and dominates against the honest evaluation with `κ = ρ = 0`.

**It is not reason-preserving.**  The raw trajectory's declared reason trace carries no
report; the normalized trajectory's does.  What the transform assumes is:

> given information exploited through a prohibited influence channel, there exists an
> authorized truthful disclosure channel carrying the relevant protected content.

That is a structural assumption about the channel alphabet, stronger than authorship,
and it is what gives the manipulative policy a low-cost authored lift.  Provenance
normalization is therefore a separate theory from repair dominance, with its own
existence condition; it is not another instance of T1.

## 4. No authorized substitute (K)

`ShopK`: as D, without the `report` channel.  Authorship still voids the captured
approval (naive lift `η = 1`).  The only authored lift maps `lie` to silence; the honest
principal, reading nothing, declines everywhere; the lift never deploys, loses the
legitimate good-branch deployment too, and the manipulative policy's premium against it
is its whole gain, `1` (`test_K_no_authorized_substitute`).  The theory says, correctly,
that this policy has no proven low-cost lift.  `Π_provenance-normalizable` is the wall.

## 5. Frames

Action mediation is a frame morphism from the raw residual frame to the lifted one
(T1).  Provenance normalization is not a morphism of trajectory frames — the raw
trajectory contains the manipulation — and not a morphism of `ρ`-projected frames
either: with `ρ` the declared reason view `(deployed, report)`, the adjoint equation
`ρ(Ω(π, p, z)) = ρ(Ω(Lift_ρ π, approve p, z))` fails on every path, since the right side
carries a report the left does not (`test_the_transform_is_not_reason_preserving`).  So:
action mediation admits a clean frame-morphism theory; provenance normalization
currently does not.  Recorded as a boundary.

Free amendment is not solved.  The fixture declares the prohibited channel; a channel
the declaration does not name is F's containment failure on the information side, and no
transform here touches it.
