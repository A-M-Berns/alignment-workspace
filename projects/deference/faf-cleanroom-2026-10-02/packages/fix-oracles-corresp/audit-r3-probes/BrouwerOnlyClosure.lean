import Cleanroom.Fixpoint.FixOraclesCorresp

/-!
# Audit round 3 (fidelity) probe: the "Brouwer only" / "Kakutani-free" rows against the *current* proof terms

Not imported by the library. The ledger's eight Brouwer-route rows say "Kakutani-free
probe-checked", citing the round-2 audit probes (`audit-r2-probes/{KakutaniFree,AdvKakutaniFree}.lean`)
and the repair-round-2 probe (`repair-r2-probes/NashMapIndependent.lean`). Those ran on earlier
states of the package: repair round 2 changed the hypothesis (and hence the proof term) of
`exists_reflectiveOn_brouwer` after the round-2 audit probes ran, and `NashMapIndependent` did not
include `exists_reflective_brouwer`, `exists_reflective_polynomial_brouwer`,
`exists_isMixedNashEq_brouwer`, `exists_reflectiveOn_brouwer` or `exists_reflective_mp_brouwer` among
its targets. This probe re-runs the same dependency walk (the round-2 adversarial auditor's code,
`allowOpaque := true`) on every Brouwer-route headline as committed at `73d3ad26`, plus the
Kakutani-free `exists_correlatedFixedPoint`, with the two Kakutani-based controls.

For each target it reports: closure size; every constant whose name contains `akutani`; every
constant of `Cleanroom.Found.FixKakutani`; which Kakutani-route headlines occur; which clamp-step
constants occur; which Nash-map constants occur; whether FAF's `brouwer_fixed_point` occurs.

Meta code (`#eval` in `CommandElabM`) only inspects the environment; nothing is added to it.
Output is `logInfo`, read from the `lean-check` log and saved next to this file.
-/

open Lean Elab Command

namespace BrouwerOnlyClosureProbe

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

/-- `allowOpaque := true` is essential: without it `value?` returns `none` for theorems and the
traversal never enters a proof body (round-2 caveat, Lean v4.31). -/
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

def clampRouteNames : List Name :=
  [``Cleanroom.Fixpoint.FixOraclesCorresp.clampStep,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.reflective_of_clampStep_eq,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_brouwer,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_brouwer]

def kakutaniRouteNames : List Name :=
  [``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_polynomial,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.oracleCorr_hasClosedGraphOn,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_via_gameR]

def nashMapNames : List Name :=
  [``Cleanroom.Fixpoint.FixOraclesCorresp.nashStep,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.reflective_of_nashStep_eq,
   ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_nashMap]

def report (env : Environment) (n : Name) : String := Id.run do
  let cl := closure env n
  let kak := cl.filter hasKakutani
  let found := cl.filter fun c => c.toString.startsWith "Cleanroom.Found.FixKakutani"
  let route := cl.filter fun c => kakutaniRouteNames.contains c
  let clamp := cl.filter fun c => clampRouteNames.contains c
  let nash := cl.filter fun c => nashMapNames.contains c
  let brouwer := cl.contains ``LogicalInduction.brouwer_fixed_point
  let mut s := s!"== {n}\n  closure size (non-library expanded): {cl.size}\n"
  s := s ++ s!"  names containing 'akutani': {kak.toList}\n"
  s := s ++ s!"  Cleanroom.Found.FixKakutani.* present: {found.toList}\n"
  s := s ++ s!"  Kakutani-route headlines present: {route.toList}\n"
  s := s ++ s!"  clamp-step constants present: {clamp.toList}\n"
  s := s ++ s!"  Nash-map constants present: {nash.toList}\n"
  s := s ++ s!"  FAF brouwer_fixed_point present: {brouwer}\n"
  return s

end BrouwerOnlyClosureProbe

open BrouwerOnlyClosureProbe in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : List Name :=
    [-- the eight Brouwer-route ledger rows / headlines
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_polynomial_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_via_gameR_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_isMixedNashEq_nashMap,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_via_gameR_nashMap,
     -- the N+ witness through the Brouwer route and the Kakutani-free correlated fixed point
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective_mp_brouwer,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_correlatedFixedPoint,
     -- controls (must show the Kakutani names)
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflective,
     ``Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_via_gameR]
  let mut msg := ""
  for t in targets do
    msg := msg ++ report env t
  logInfo msg

/-! The ledger's "stronger: `I` arbitrary (not necessarily finite)" on the `exists_reflectiveOn` rows:
the elaborated signatures must carry no `Fintype I` argument. -/
#check @Cleanroom.Fixpoint.FixOraclesCorresp.ReflectiveOn
#check @Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn
#check @Cleanroom.Fixpoint.FixOraclesCorresp.exists_reflectiveOn_brouwer
