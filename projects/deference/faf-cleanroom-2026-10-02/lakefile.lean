import Lake
open Lake DSL

-- Clean-room Lean 4 formalizations of `research/`, built on Formalized Agent Foundations (FAF).
-- FAF is a pinned, read-only dependency: its definitions are the vetted substrate these
-- formalizations are stated over. Never patch `.lake/packages/agentFoundations`; lemmas
-- FAF lacks are proved here. See README.md and STANDARDS.md.
package fafCleanroom where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require agentFoundations from git
  "https://github.com/A-M-Berns/Formalized-Agent-Foundations.git" @ "159ec3f4d55948d741302a915cce388616a3875f"

@[default_target]
lean_lib Cleanroom where
  srcDir := "."
  globs := #[.andSubmodules `Cleanroom]
