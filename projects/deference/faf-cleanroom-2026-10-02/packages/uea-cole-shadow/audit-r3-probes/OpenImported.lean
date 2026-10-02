import Cleanroom.Uea.UeaColeShadow

/-!
Round-3 fidelity probe (uea-cole-shadow): the root module imports `Open.lean`, so a dependent that imports the
root (as the mandate directs) has the three OPEN declarations, `sorryAx` included, in its environment. The
`Open.lean` and root docstrings say "a leaf — nothing in the library imports it". Not imported by the library.
-/

#print axioms Cleanroom.Uea.UeaColeShadow.Model.pure_exists_open
#print axioms Cleanroom.Uea.UeaColeShadow.Model.theoremC_log_open

example : True := trivial
