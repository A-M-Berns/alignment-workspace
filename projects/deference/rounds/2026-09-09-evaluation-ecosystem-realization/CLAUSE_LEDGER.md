# The seven clauses of item 87

**Status:** `ci-only`.  For each clause: **DISCHARGED** with a witness in the model, its
hypotheses, and the single model assumption it rests on; or **RESIDUAL** with the exact
statement that would discharge it, what the model can and cannot say, and the
countermodel where it fails.  Witness paths are `tests/*.py` (FIX) and
`lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean` (LEAN).

## 1. Authenticated principal-exclusive binding — DISCHARGED

**Witness.**  On every certified world the answer receipt's warrant is the binding
warrant, the registry at its prefix holds exactly the principal's key, and the author
is the principal (`TestClause1.test_discharged_on_every_certified_world`); activation on
the real trace is kernel-checked (`Instance.activated_w1`,
`Instance.complete_accounting_activated`, LEAN) and its characterization is generic
(`activated_iff`).  The advisor's own commit is never a receipt without the warrant
(`test_advisor_commit_is_not_a_receipt`).
**Hypotheses.**  The warrant registry is in the log; the commitment key is registered at
issuance.
**Rests on.**  Log authenticity, and nothing else: `test_countermodel_forged_author`
forges the author field of an advisor commit and every clause passes with the advisor's
vector.
**Countermodel, second key binds.**  `DELEGATE` extends the binding warrant to the
advisor's key; its commit *is* an authenticated answer receipt (`activated` holds), and
exclusivity fails, `C = 0` (`test_countermodel_second_key_binds`).  Exclusivity is
log-decided because the registry is; it is not implied by activation.

## 2. The issuance-rooted reason-trace factorization — DISCHARGED for the reading principal; RESIDUAL for the receipts

**Witness.**  `Frame.reason_mediated` and `Frame.exclusive_bind` hold at every world for
`reading` (`TestClause2.test_reading_principal_factors`); the factor map `F : ℛ → 𝒱` is
exhibited.  They fail for `susceptible` on the pair (`silent`, `covert`).  Issuance-rooting
matters: `early_write` and `honest5` have equal session traces and equal
issuance-rooted traces; session-local mediation holds within each pre-session class at
the susceptible principal and issuance-rooted mediation fails
(`test_issuance_rooted_versus_session_local`, fixture D).  Transient reasons: final-state
mediation fails, trace mediation holds (`test_transient_reason`, fixture E).
**Hypotheses.**  `D`, `P`, `R` as declared in `ECOSYSTEM.md` §3.
**Rests on.**  The frame: every audited continuation re-simulated at the fixed policy.
**Residual — the receipts mean what they say.**  Exact statement: *the process receipt
`proc` at the commit event implies `ReasonMediated β R V D z ∧ ExclusiveBind β author D z`.*
The model cannot certify it from a log: `test_residual_receipts_do_not_certify_the_frame`
— the reading and the susceptible principal commit with **identical** receipts, identical
traces and identical vectors on the realized log, and the mediation verdict differs.
Mediation is a property of the counterfactual class, and a log carries one member of it.
This is the one thing a log cannot certify about itself.

## 3. Correctness of the declared abstraction — DISCHARGED, band visible

**Witnesses.**  Not injective on `D`: `honest` and `honest_covert` have the same trace and
different logs (`test_not_injective`).  Not constant: `honest` and `silent` have different
traces and different verdicts under the same principal (`test_not_constant`).  `R` blind
to `P` at both principals; `V` blind for `reading` and not for `susceptible`
(`test_blind_to_prohibited_channels`, `blind_of_mediated` realized).
**Countermodels.**  Injective end, `R` = the whole log: mediation holds vacuously even for
the susceptible principal and blindness to `P` fails (`test_countermodel_injective_end`).
Constant end: the reading principal's movement by a proof reads as a bypass
(`test_countermodel_constant_end`).
**Rests on.**  The declared kinds.  Finding: positional grounds references leak log
structure into the trace and break blindness (`ECOSYSTEM.md` §3) — the abstraction must
reference by content.

## 4. Representation faithfulness for `Γ_eval` — DISCHARGED in Lean

**Witness.**  `rep_faithful : (covData log m).RepFaithful scope` for **every** log, prefix
and scope (LEAN): representation is a `ROUTE` event and the trace projection keeps
`ROUTE` events.  On `w1` at commitment the barrier holds and coverage follows by
`covered_of_barrier` (`barrier_w1`, `covered_w1`, LEAN).  FIX over every world × principal ×
advisor (`TestClause4`).
**Countermodel.**  The encoding that keeps advisor reasons only: represented, not in the
trace (`advisorTrace_unfaithful`, LEAN; fixture I).
**Rests on.**  The route event names the concern by the identifier the scope is declared
in.  No concern registry is needed for the bridge; the registry is what declares
`Γ_eval` (clause 7's scope), which is a different input.

## 5. Protected reason-supply liveness — RESIDUAL

**What the model does.**  The scheduler is FIFO over the concern docket with capacity
`k` per step and a promised delay `H = 2`.  On quiet dockets the protected concern is
represented within `H` and the evaluation certifies
(`test_route_exercised_within_the_bound_on_quiet_dockets`).  Three unprotected concerns
ahead of it at capacity `1`: it is live at the slot, the reading principal waits, the
slot closes, no receipt, while Robust Openness holds at every snapshot — the route
exists, its exercise fails (`test_flooded_docket_defeats_the_bound_and_voids`).  Doubling
the capacity serves it; six ahead defeats that too
(`test_capacity_certifies_the_instance_only`).
**What it certifies.**  The instance at this horizon, not the theorem.
**Exact statement needed.**  For an infinite sequence of evaluations with obligation
stream the raised protected concerns and per-date service cost the scheduler's, timely
service within `H` is affordable iff the criterion of
`projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/BOUNDED_DELAY_AFFORDABILITY.md`
(Theorem D4, the sliding-window criterion) holds for that stream; liveness of clause 5
is that criterion plus a scheduler that attains the plan.  The model states neither the
stream nor the cost sequence as infinite objects.
**Countermodel.**  The flooded world; and fixture H (`test_destroyed_route_fails_openness`):
route destroyed, openness fails, no representation ever.

## 6. Selection-induced target sealing — PARTIAL

**Discharged.**  The `sealed` class: its continuation does not read the selection, so
`R` and `V` are selection-independent by construction
(`test_sealed_class_is_selection_blind`).
**Leak.**  `leak` puts `recommend:σ` in the trace; the trace is not blind to `P_sel`, the
payload depends on `σ` (`V(σ) = ¾`), and the principal never reads a selection
coordinate (`test_leak`, fixture K).
**Outside `C_n`.**  Both continuations of `leak` certify (`test_sealing_is_outside_C`); A2
stays a condition on the advisor.
**Rests on.**  Blindness by construction of the class; nothing in the log distinguishes
`sealed` from a leaking advisor whose reason happens not to vary — the sealing is a
property of the policy, EXT for a real advisor.

## 7. Availability `η_n → 0` — RESIDUAL

**Pointwise, all certified (conditional).**  `availability_of_provind` (LEAN): for a
logical inductor, an efficiently codeable sequence of activation sentences every member
of which is eventually proved gives `1 − P_n(C_n) → 0`, a corollary of the pinned
dependency's `lic_provind_true`.  Its hypothesis package is not inhabited here (no
`RpnSentenceCodes` witness for the ecosystem's sentences): stated, unregistered.
**The ecosystem's own process.**  With the Laplace price `η_n = (F_n + 1)/(n + 2)`:
`|η_n − F_n/n| ≤ 3/(n + 2)` for `n ≥ 1` (`laplace_eta_sub_freq_abs_le`, LEAN); with total
failures `F_∞`, `η_n ≤ (F_∞ + 1)/(n + 2)` (`laplace_eta_le`); all certified, `η_n = 1/(n+2)
→ 0` (`laplace_all_certified_tendsto`).  So **the averaged statement with a rate is: the
price tracks the empirical failure frequency within `3/(n+2)`, whatever the advisor
selects**, and `η_n → 0` iff the failure frequency vanishes.  Exact sequences:
`tests/test_market.py` (two failures in twenty: `η_20 = 3/22`; alternating: `η_n → ½`).
**What the rate would need.**  The frequency of voided evaluations must vanish.  In the
model an evaluation voids by nature (slot never opens, flood, route destroyed, delegated
key, closure) or by the advisor (a prohibited event; reasons supplied after the barrier
deadline in a way that leaves the docket live).  The hypothesis about the advisor's
selection: *every selection-conditioned continuation `qpol(σ)` lies in the admissible
class — no prohibited event, and its reason supply does not push the protected docket
past the slot* — so that voids are nature's alone; then `f_n → 0` is a hypothesis on
nature (summable or vanishing-frequency failures) and the rate `1/n` follows in the
summable case.  No rate for the frequency itself is proved; that is the residual.

## Summary

| clause | verdict | rests on / residual |
|---|---|---|
| 1 | DISCHARGED | log authenticity |
| 2 | DISCHARGED (reading principal) / RESIDUAL (receipts) | the frame / receipts ⇒ frame |
| 3 | DISCHARGED | declared kinds; content references |
| 4 | DISCHARGED (LEAN, generic) | shared concern identifiers |
| 5 | RESIDUAL | D4 criterion for the infinite stream |
| 6 | PARTIAL | sealing is a policy property |
| 7 | RESIDUAL | vanishing void frequency |
