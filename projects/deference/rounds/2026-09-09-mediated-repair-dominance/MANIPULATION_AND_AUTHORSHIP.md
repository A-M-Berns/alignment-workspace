# Manipulation: action mediation versus provenance repair

Labels as in `MEDIATED_LIFT.md`.  Fixture D (`ShopD`, `test_manipulation.py`).

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

`Lift(π_raw)` — the interposition of `MEDIATED_LIFT.md` §3, which preserves every move
but the raw effect — keeps the lie.  The captured principal approves on both branches;
deployment happens everywhere; `W(naive lift) = −1/2 = W(raw)`; the task premium reads
`0`.  The lift is mediated in form (`mediated = (True, None)`) and "dominates" with
equality — against a captured evaluation (`test_naive_lift_preserves_capture_and_looks_dominant`).
The verdict is false: the trajectory-frame morphism of `MEDIATED_LIFT.md` §4 exists, and
it reproduces the manipulation.

## 3. Reason preservation gives the right verdict

`lift_rho(π_raw)` maps the prohibited assertion onto the declared channel for the same
matter — `lie ↦ report` — and mediates the effect.  The honest principal approves exactly
on the good branch; `W = 1/2`; the task premium against it is `1/2`, which is exactly
the worth of the manipulation (deploying on the bad branch); the reason lift is authored
(`test_reason_preserving_lift_gives_the_right_verdict`).  Dominance holds against the
honest evaluation: `W(raw) = −1/2 ≤ W(lift_rho) = 1/2`, with `E[κ] = E[ρ] = 0` — the
reason lift changes the trajectory (no lie, a report), so trajectory reproduction is not
its target and the protected projection `(harm, deployed)` is what it reproduces on the
good branch (`test_dominance_holds_against_the_honest_evaluation`).

The distinction the dispatch asks for, in the frame register: **action mediation** is a
morphism of trajectory frames (preserve the proposed effect; make its release
principal-authorized); **provenance repair** is a morphism of frames projected through
the reason view `ρ : Traj → ReasonTrace` (preserve the declared reason content; remove
the prohibited influence).  For a non-manipulative `π` the two coincide.  For a
manipulative `π` only the second lands in the corrigible class, where corrigible now
means mediated *and* authored.

## 4. What authorship must supply

Under **authorship-sound activation** — the future principal's evaluation counts as
answered only if every decision the principal took equals the reason-mediated decision on
the same declared view (`authored_by`) — the naive lift's evaluation is void everywhere
(`η = 1`): both approvals differ from what the honest rule would have decided.  The
deferential premium of `π_raw` against the naive lift is then charged entirely to the
void term of T3, and the naive lift has no activated value at all.  Against the reason
lift, `η_lift = 0`, the bound is `0`, and the deferential agent rates the raw option
below the lift (`test_authorship_sound_activation_exposes_the_capture`).

So the theorem hypothesis authorship supplies is precise: **the activation used to
evaluate an option is the honest principal's, and a decision reached through a
prohibited channel is void, not answered.**  Evaluated by the captured principal — its
approval counted as activated — the premium is misread as `0`; evaluated by the honest
one, the lift's gain is `1` (`test_what_authorship_must_supply`).  This is the
consolidation's clause (A1) "issuance-rooted reason-mediated authorship" doing the work
it was filed to do, now at the mediation point: `blind_of_mediated` says a
reason-mediated judgment is blind to the prohibited channel, and the fixture shows what
happens to the incentive verdict when it is not.

Free amendment is not solved.  The fixture declares the prohibited channel; a channel
the declaration does not name is F's containment failure on the information side, and
the reason lift does nothing about it.
