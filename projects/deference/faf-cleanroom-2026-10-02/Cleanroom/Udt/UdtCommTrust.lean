import Cleanroom.Udt.UdtCommTrust.Factor
import Cleanroom.Udt.UdtCommTrust.FfsBridge
import Cleanroom.Udt.UdtCommTrust.Condense
import Cleanroom.Udt.UdtCommTrust.Prob
import Cleanroom.Udt.UdtCommTrust.Structure
import Cleanroom.Udt.UdtCommTrust.Determination
import Cleanroom.Udt.UdtCommTrust.Concrete
import Cleanroom.Udt.UdtCommTrust.SelfTrust
import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCommTrust.Construct
import Cleanroom.Udt.UdtCommTrust.Fairness
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCommTrust.Witness
import Cleanroom.Udt.UdtCommTrust.WitnessSmall
import Cleanroom.Udt.UdtCommTrust.WitnessDet

/-!
# `Cleanroom.Udt.UdtCommTrust`: Communication & Trust — decision structures, decision-determination,
self-trust and advice-following

Root module of work package `udt-comm-trust` (faf-cleanroom run, 2026-09-30). Report, findings,
ledger and open list in `run/wp/udt-comm-trust/`.

* `Factor`, `FfsBridge` — random variables, "factors as", the FFS `IsFactorization` bridge (T1).
* `Condense` — the translation's condensation variable, the non-uniqueness refutation (T2).
* `Prob`, `Count` — finite-probability plumbing and integer-weight counting for witnesses.
* `Structure` — the abstract decision structure, `Π̈`/`Π†` derived, the UDT rule (T3, T4(a)).
* `Determination` — decision-determination and its readings, the factoring theorem, the
  decomposition over external policies (T5, T6, T7).
* `Concrete` — the concrete structure, modification, communicative alternatives, stability (T8, T9, T12).
* `SelfTrust` — Communicative Expectation, the Self-Trust tautology and its repair (T10, T11, T17).
* `Advice` — Advice-Following termwise, `Faithful`, "`Π̈ = R` in fact" per world and as printed, the
  audit-r1 inconsistency finding, the constant-policy fixed point (T13, T14(b)).
* `Construct` — a defensible `Π*` from `D_B` and a neutral side channel (T4(b), repair round 1).
* `Fairness` — with a constant recommendation, communicative alternatives force `P(Π̈ = R) = 1`
  (T15(a), positive half, repair round 1).
* `Witness`, `WitnessSmall`, `WitnessDet` — `W2` (64 worlds), the small witnesses `W2m`, `Two`, `NoSub`,
  and (repair round 1) `Det` plus the per-world and construction checks on `W2`/`W2m`.
-/
