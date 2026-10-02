import Cleanroom.Udt.UdtEndorsePolicy.Defs
import Cleanroom.Udt.UdtEndorsePolicy.Generalize
import Cleanroom.Udt.UdtEndorsePolicy.Reflection
import Cleanroom.Udt.UdtEndorsePolicy.ReflectionWitnesses
import Cleanroom.Udt.UdtEndorsePolicy.Transitive
import Cleanroom.Udt.UdtEndorsePolicy.TransitiveWitness
import Cleanroom.Udt.UdtEndorsePolicy.NodeValue
import Cleanroom.Udt.UdtEndorsePolicy.Deference
import Cleanroom.Udt.UdtEndorsePolicy.Flat
import Cleanroom.Udt.UdtEndorsePolicy.Structure

/-!
# `udt-endorse-policy` — endorsement, updateless deference and Geometric UDT

Root module of the package (faf-cleanroom run, 2026-09-30; repair round 1 the same day), namespace
`Cleanroom.Udt.UdtEndorsePolicy`. Modules:

* `Defs` — T1: the six endorsement definitions of record (finite, multiplicative, positive-mass
  form), division forms, point forms, conditional ⟹ unconditional.
* `Generalize` — T2: what "control endorsement generalizes the others" amounts to (Brier grid).
* `Reflection`, `ReflectionWitnesses` — T3: the Reflection Principle and the ladder
  `Calibrated ⟹ BeliefEndorsedAll ⟹ Reflective` over `udt-supercondition`, both strict.
* `Transitive`, `TransitiveWitness` — T6: conditional endorsement is not transitive but acyclic;
  the closure of strict trust is a strict partial order.
* `NodeValue` — T7, T5, T10: EDT node value through a kernel, the `κ`-collapse lemma, the coupled
  mugging, the self-kernel lemmas (an EDT assembly through one's own decoupled kernel is a local
  optimum, so T5's "updateful ⟹ not endorsed" is a question about the kernel's base, not about
  `U`), the Geometric-UDT identity and the values-coin reading.
* `Deference` — T8: policy-respecting endorsement and "defers" (definitional; menu form refuted).
* `Flat` — T9: decision-flat refinements as a theorem about coupling graphs (both directions).
* `Structure` — T4: policy endorsement and the pointwise UDT rule over `udt-comm-trust`'s
  `AbstractDS`; support collapse; the two separations (neither decision-determined); the
  equivalence of the two rules on external-only structures with a separable policy utility
  (repair round 1), and `CB8X`, the witness of the full package.

Deliverables: `run/wp/udt-endorse-policy/` (report, findings, ledger, open list).
-/
