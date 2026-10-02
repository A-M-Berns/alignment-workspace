import Cleanroom.Udt.UdtCtExamples.CountExt
import Cleanroom.Udt.UdtCtExamples.Infra
import Cleanroom.Udt.UdtCtExamples.CoordButtons
import Cleanroom.Udt.UdtCtExamples.CoordButtonsMsg
import Cleanroom.Udt.UdtCtExamples.CoordButtonsHidden
import Cleanroom.Udt.UdtCtExamples.Memory
import Cleanroom.Udt.UdtCtExamples.MemoryHidden
import Cleanroom.Udt.UdtCtExamples.MemoryInternal
import Cleanroom.Udt.UdtCtExamples.ThirdButton
import Cleanroom.Udt.UdtCtExamples.Realized
import Cleanroom.Udt.UdtCtExamples.Convention
import Cleanroom.Udt.UdtCtExamples.Bridge
import Cleanroom.Udt.UdtCtExamples.NonInterference
import Cleanroom.Udt.UdtCtExamples.Independence
import Cleanroom.Udt.UdtCtExamples.Modification
import Cleanroom.Udt.UdtCtExamples.Screening
import Cleanroom.Udt.UdtCtExamples.Frames

/-!
# `Cleanroom.Udt.UdtCtExamples`: Communication & Trust — the examples, the partition
transcription and the probability-zero convention

Root module of work package `udt-ct-examples` (faf-cleanroom run, 2026-09-30). Report, findings,
ledger and open list in `run/wp/udt-ct-examples/`. Depends on `udt-comm-trust` (imported by
module, never by root) and `udt-policy-calc`.

* `CountExt`, `Infra` — `u/m`-valued utilities and modification probabilities as ratios of
  counts; `aI_indep_of_dI` (the structural lemma behind the representation choice); reading `Π†`
  off a witness.
* `CoordButtons` — Coordinated Buttons (T1(a)–(c)): decision-determined, the `$5` and `$10`
  fixed points, the pill strictly best at `pre`, no communicative alternatives.
* `CoordButtonsMsg` — with the message channel (T1(d)): communicative alternatives, the repaired
  Self-Trust theorem applies and its conclusion is exercised.
* `CoordButtonsHidden` — `CB`'s worlds and priors with the pre-choice hidden from `Π̈` (repair
  round 2): decision-determination **fails** under `W5` at the hand-checked atom of F-2(a) and
  holds under `W10` — `CB W5`'s decision-determination is through the `Π̈(pre)` leak.
* `Memory` — the Memory Problem (T2) with the pill choice as the light instance's external
  action: decision-determined *because* `Π̈(light)` reveals the choice; the CA failure is the
  same representation artifact (`asked_law_agrees`: the report's law is the same coin).
* `MemoryHidden` — the same worlds and weights with the pill choice hidden from `Π̈` (the paper's
  internal-action picture): decision-determination **fails** at a named atom — the retracted
  diagnosis holds on this representation (repair round 1, findings F-15).
* `MemoryInternal` — the pill as a *realized internal action* with a probabilistic effect, hidden
  from `Π̈` (repair round 2, the mandate's own fallback design): decision-determination **and**
  communicative alternatives both fail, the latter at the report coordinate — the paper's
  reason; the pill is strictly preferred and the Self-Trust conclusion fails.
* `ThirdButton` — the Third Button (T3(a)–(c)): decision-determined, `P(Π̈ = R) < 1`, and the
  source's two claims under two incompatible priors.
* `Realized` — what `P(Π̈ = R) = 1` does to the deviation conditionals (T7(d)), the witness `J2`.
* `Convention` — the rule of record and the junk-value convention quantified (T5(a)–(b)).
* `Bridge` — the `argmax E[U ∣ Π*(o) = a] = argmax U'(π[o ↦ a])` bridge iff locality (T5(c)).
* `NonInterference` — the two non-interference formalizations (T4).
* `Independence`, `Modification` — the write-up's independence packages (T7(a); witnesses of
  record `EffVary`, `DDnotEff` with `Π†` varying) and behavioural versus forcing modification
  (T7(b)).
* `Screening` — the screening extension (T7(e): `PolicyFairCT` from decision-determination,
  `EffScreens` and bli-paper-091's display) and "proper policies" (T7(c): degenerate on `CB`).
* `Frames` — the Cartesian-frames analogy has no statement (T6).
-/
