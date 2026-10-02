import Cleanroom.Fixpoint.FixOraclesCorresp.BrouwerOnly
import Cleanroom.Fixpoint.FixOraclesCorresp.Correlated

/-!
# Audit round 3 (adversarial) probe: Kakutani-freeness and route independence, re-run on the
current library

Not imported by the library. The round-2 audit probes (`audit-r2-probes/{KakutaniFree,
AdvKakutaniFree}.lean`) ran against the library *before* repair round 2, which added
`exists_reflectiveOn_via_gameR_brouwer`, `exists_isMixedNashEq_nashMap`,
`exists_reflective_via_gameR_nashMap` and changed `exists_reflectiveOn`'s hypothesis; the repair
agent's own `repair-r2-probes/NashMapIndependent.lean` covered the new rows. Earlier audits are
claims to verify, so this probe re-walks the transitive constant closure of **every** Brouwer-route
headline (all nine `BrouwerOnly` rows' declarations) on the library as it stands, plus target 7's
Kakutani-free claim and three controls, and reports

* names containing `akutani`, and every `Cleanroom.Found.FixKakutani.*` constant reached;
* the Kakutani-route headlines (`exists_reflective`, `exists_isMixedNashEq`, `exists_reflectiveOn`,
  `exists_reflective_via_gameR`, `exists_reflectiveOn_via_gameR`, `oracleCorr_hasClosedGraphOn`);
* the clamp-step-route constants (`clampStep`, `reflective_of_clampStep_eq`,
  `exists_reflective_brouwer`, `exists_isMixedNashEq_brouwer`, …) — absent from the Nash-map rows iff
  the "independent second proof" claim holds at the proof-term level;
* the Nash-map-route constants (`nashStep`, `reflective_of_nashStep_eq`, `exists_isMixedNashEq_nashMap`);
* FAF's `LogicalInduction.brouwer_fixed_point` and `brouwer_findim`.

Recursion goes through every non-library constant (everything outside Mathlib/Lean/Init/Std/…),
i.e. through all of `Cleanroom.*`, FAF and EconCSLib. `ConstantInfo.value? (allowOpaque := true)`
is essential under Lean v4.31 (without it theorem bodies are skipped; the controls catch that).
Meta code only inspects the environment. Output is `logInfo`, saved as `AdvKakutaniFreeR3.out.txt`.
-/

open Lean Elab Command

namespace AdvKakutaniFreeR3Probe

def skipRoot : List String :=
  ["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible",
   "LeanSearchClient", "ImportGraph", "MD4Lean", "UnicodeBasic", "BibtexQuery", "Cli", "Lake"]

def moduleRoot (env : Environment) (n : Name) : Option String :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => some m.getRoot.toString
    | none => none
  | none => none

def usedConsts (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[])

partial def closure (env : Environment) (start : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut out : Array Name := #[]
  let mut work : Array Name := #[start]
  while true do
    match work.back? with
    | none => break
    | some n =>
      work := work.pop
      if visited.contains n then
        continue
      visited := visited.insert n
      out := out.push n
      let recurse := match moduleRoot env n with
        | some r => !skipRoot.contains r
        | none => true
      if recurse then
        if let some ci := env.find? n then
          for c in usedConsts ci do
            if !visited.contains c then
              work := work.push c
  return out

def hasKakutani (n : Name) : Bool := (n.toString.splitOn "akutani").length > 1

def kakutaniRouteNames : List Name :=
  [``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_via_gameR,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.oracleCorr_hasClosedGraphOn,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_collapse_fixed_point]

def clampRouteNames : List Name :=
  [``Cleanroom.Fixpoint.FixOraclesCorresp.clampStep,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.clampStep_mapsTo,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.continuousOn_clampStep,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.reflective_of_clampStep_eq,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.clampStep_eq_of_reflective,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.clampStep_eq_iff_reflective,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_brouwer,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_polynomial_brouwer,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_brouwer,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR_brouwer,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_brouwer]

def nashRouteNames : List Name :=
  [``Cleanroom.Fixpoint.FixOraclesCorresp.nashStep,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.nashStep_mapsTo,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.continuous_nashStep,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.reflective_of_nashStep_eq,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_nashMap]

def report (env : Environment) (n : Name) : String := Id.run do
  let cl := closure env n
  let kak := cl.filter hasKakutani
  let route := cl.filter fun c => kakutaniRouteNames.contains c
  let found := cl.filter fun c => c.toString.startsWith "Cleanroom.Found.FixKakutani"
  let clamp := cl.filter fun c => clampRouteNames.contains c
  let nash := cl.filter fun c => nashRouteNames.contains c
  let brouwer := cl.contains ``LogicalInduction.brouwer_fixed_point
  let brouwerFindim := cl.contains ``Cleanroom.Fixpoint.FixOraclesCorresp.brouwer_findim
  let thm41 := cl.contains ``Cleanroom.Fixpoint.FixOraclesCorresp.isMixedNashEq_iff_reflective
  let gadget := cl.contains ``Cleanroom.Fixpoint.FixOraclesCorresp.gameR_nash_reflective
  let mut s := s!"== {n}\n  closure size (non-library expanded): {cl.size}\n"
  s := s ++ s!"  names containing 'akutani': {kak.toList}\n"
  s := s ++ s!"  Kakutani-route headlines present: {route.toList}\n"
  s := s ++ s!"  Cleanroom.Found.FixKakutani.* present (count): {found.size}\n"
  s := s ++ s!"  clamp-step-route constants present: {clamp.toList}\n"
  s := s ++ s!"  Nash-map-route constants present: {nash.toList}\n"
  s := s ++ s!"  brouwer_fixed_point: {brouwer}; brouwer_findim: {brouwerFindim}; "
  s := s ++ s!"isMixedNashEq_iff_reflective: {thm41}; gameR_nash_reflective: {gadget}\n"
  return s

end AdvKakutaniFreeR3Probe

open AdvKakutaniFreeR3Probe in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : List Name :=
    [-- the nine BrouwerOnly rows' declarations
     ``Cleanroom.Fixpoint.FixOraclesCorresp.brouwer_findim,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_polynomial_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_via_gameR_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_nashMap,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR_nashMap,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_mp_brouwer,
     -- target 7's Kakutani-free claim (pigeonhole route)
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_correlatedFixedPoint,
     -- controls: the Kakutani route must show the Kakutani names
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_via_gameR]
  let mut msg := ""
  for t in targets do
    msg := msg ++ report env t
  logInfo msg
