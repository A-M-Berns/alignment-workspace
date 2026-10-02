import Cleanroom.Udt.UdtCtExamples.MemoryInternal

/-!
# Audit r3 (adversarial) probe: with a harmless dummy, the Memory Problem on the paper's
picture *has* communicative alternatives under `MemI`'s own weights

`MemI` makes the light instance's external action the report policy `r` (a dummy `E_fac`
forces to be two-valued), so `Π̈(light) = r` and the action at a light input is `(c', r)`. This
probe replaces that dummy by a free boundary coordinate `r'` (uniform, read by nothing) on the
96 worlds `(((c', d), (r, r')), (ö, ℓ))`, keeps `MemI`'s weights otherwise (`tie`, the memory
wipe, the `7 : 1` pill), and computes, in count form, exactly what `IsCA` unfolds to on a
message-free carrier (`evFollowsR = univ`):

* `ca_identity`: for every external policy `π` and both dummy values `x`,
  `P(Π̈ = π ∣ pill, x) = P(Π̈ = π ∣ nothing, x)` — the CA identity **holds**;
* `minMod_nothing`: `m(nothing, x) = 1/4 ≤ 3/4 = m(pill, x)` — "nothing" is minimally modifying;
* `minMod_asked`: at the asked input both attained actions tie at `m = 1/2`, so each is its own
  communicative alternative — the carrier **has communicative alternatives** (`HasCA`, in count form);
* `dd_fails`: decision-determination's clause (2) still fails at `MemI`'s atom (`21 · 256 ≠ 88 · 48`).

So on this carrier "nothing" is a communicative alternative of the pill at every light input,
and the Memory Problem fails decision-determination **only** — the retracted diagnosis, not
F-15's "both". `MemI.report_law_differs`'s `5/8 ≠ 7/8` is the law of the report *given `r`*,
which the dummy `Ä(light) = r` puts into the conditioning action; with these symmetric weights
the report's own law is the same coin under both actions (`MemIReportMarginal`). The structure
fields of this carrier are not re-discharged here (cost: 96² pairs); they are `MemI`'s with one
more boundary coordinate, and nothing in the three statements uses them. Evidence only; not
library code.
-/

namespace Cleanroom.Udt.UdtCtExamples.AuditR3.NoiseDummy

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

/-- Worlds `(((c', d), (r, r')), (ö, ℓ))`: `MemI`'s coordinates plus `r'`, the light instance's
external action — a free boundary coordinate nothing reads. -/
abbrev Ω : Type := ((Fin 2 × Fin 3) × (Fin 2 × Fin 2)) × (Fin 2 × Fin 2)

/-- `MemI.obs` on the new carrier. -/
def obs (ω : Ω) : Fin 3 := if ω.2.1 = 0 then Fin.castSucc ω.2.2 else 2

/-- `MemI.weights` with `r'` uniform; total `1024`. -/
def W : IntWeights Ω where
  wt ω := MemI.tie ω.1.1.1 ω.1.1.2 * (if ω.2.1 = 0 then 4 else if ω.1.1.2 = 0 then 4 else
    (if (if ω.1.1.2 = 1 then (0 : Fin 2) else 1) = ω.2.2 then 7 else 1))
  pos ω := by revert ω; decide
  N := 1024
  sum_eq := by decide +kernel

/-- The external policy `Π̈` of a world: `r'` at the light instance, the (possibly forced)
report `MemH.actOf d r 2` at the asked one. -/
def polE' (ω : Ω) : Fin 3 → Fin 2 :=
  fun e => if e = 2 then MemH.actOf ω.1.1.2 ω.1.2.1 2 else ω.1.2.2

/-- The pill action `(1, x)` at a light input: `{c' = 1, r' = x}`. -/
abbrev pill (x : Fin 2) : Finset Ω := event fun ω : Ω => ω.1.1.1 = 1 ∧ ω.1.2.2 = x

/-- The "nothing" action `(0, x)` at a light input: `{c' = 0, r' = x}`. -/
abbrev nothing (x : Fin 2) : Finset Ω := event fun ω : Ω => ω.1.1.1 = 0 ∧ ω.1.2.2 = x

/-- The modification event `{d ≠ 0}` (`MemI.evMod_eq`). -/
abbrev modEv : Finset Ω := event fun ω : Ω => ω.1.1.2 ≠ 0

/-- **The CA identity holds** for "nothing" against the pill with the same dummy value, for
every external policy. -/
theorem ca_identity : ∀ (π : Fin 3 → Fin 2) (x : Fin 2),
    W.cnt ((event fun ω : Ω => polE' ω = π) ∩ pill x) * W.cnt (nothing x) =
      W.cnt ((event fun ω : Ω => polE' ω = π) ∩ nothing x) * W.cnt (pill x) := by
  decide +kernel

/-- **"Nothing" is minimally modifying**: `m(nothing, x) ≤ m(pill, x)` (and trivially
`≤ m(nothing, x)`); the attained actions at a light input are these four. -/
theorem minMod_nothing : ∀ x : Fin 2,
    W.cnt (modEv ∩ nothing x) * W.cnt (pill x) ≤ W.cnt (modEv ∩ pill x) * W.cnt (nothing x) := by
  decide +kernel

theorem values : W.cnt (pill 0) = 256 ∧ W.cnt (nothing 0) = 256 ∧
    W.cnt (modEv ∩ pill 0) = 192 ∧ W.cnt (modEv ∩ nothing 0) = 64 := by
  decide +kernel

/-- At the asked input the two attained actions `(0, r)` tie at `m = 1/2`, so each is minimally
modifying and its own communicative alternative (`isCA_self_of_minMod`, `evFollowsR = univ`):
with `ca_identity` and `minMod_nothing`, every attained action at every input has a
communicative alternative on this carrier. -/
theorem minMod_asked :
    W.cnt (modEv ∩ event fun ω : Ω => ω.1.2.1 = 0) * W.cnt (event fun ω : Ω => ω.1.2.1 = 1) =
      W.cnt (modEv ∩ event fun ω : Ω => ω.1.2.1 = 1) * W.cnt (event fun ω : Ω => ω.1.2.1 = 0) := by
  decide +kernel

/-- **Decision-determination still fails** at `MemI`'s atom `e = (report red, (asked, light red))`,
`d = (red pill, (pill, (r = red, r' = red)))`: `21 · 256 ≠ 88 · 48`. -/
theorem dd_fails :
    W.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2.1 (obs ω), ω.2) = (0, (1, 0)) ∧
        (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, (0, 0)))) *
      W.cnt (event fun ω : Ω => polE' ω = fun _ => 0) ≠
    W.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2.1 (obs ω), ω.2) = (0, (1, 0)) ∧
        polE' ω = fun _ => 0) *
      W.cnt (event fun ω : Ω => (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, (0, 0)))) := by
  decide +kernel

theorem dd_values :
    W.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2.1 (obs ω), ω.2) = (0, (1, 0)) ∧
        (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, (0, 0)))) = 21 ∧
    W.cnt (event fun ω : Ω => polE' ω = fun _ => 0) = 256 ∧
    W.cnt (event fun ω : Ω => (MemH.actOf ω.1.1.2 ω.1.2.1 (obs ω), ω.2) = (0, (1, 0)) ∧
        polE' ω = fun _ => 0) = 88 ∧
    W.cnt (event fun ω : Ω => (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (1, (1, (0, 0)))) = 48 := by
  decide +kernel

end Cleanroom.Udt.UdtCtExamples.AuditR3.NoiseDummy
