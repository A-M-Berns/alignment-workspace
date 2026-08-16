#!/usr/bin/env python3
"""Render the declared item-30 numerical experiment tables to standard output."""

from __future__ import annotations

import pathlib
import sys


HERE = pathlib.Path(__file__).resolve().parents[1]
PREP = HERE.parent / "2026-08-11-phi-regret-prep"
APPLICABILITY = HERE.parent / "2026-08-11-phi-regret-applicability"
BRIDGE = HERE.parent / "2026-08-11-phi-regret-bridge"
sys.path[:0] = [str(HERE / "src"), str(BRIDGE / "src"),
                str(APPLICABILITY / "src"), str(PREP)]

from experiment import FIXTURE_BUILDERS, HORIZONS, integration_audit, run_fixture
from phi_learner import decimal_text
from semantic_bridge import AUDITED_PROGRAMS


def shown(value) -> str:
    return decimal_text(value, places=9)


def main() -> int:
    runs = []
    for builder in FIXTURE_BUILDERS:
        for horizon in HORIZONS:
            runs.extend(run_fixture(builder(horizon)))

    print("Comparator class: " + ", ".join(program.program_id
                                             for program in AUDITED_PROGRAMS))
    print()
    print("| fixture | T | policy | mixed charge | max regret | max/T | max/scale | beta | source bound |")
    print("|---|---:|---|---:|---:|---:|---:|---:|---:|")
    for run in runs:
        print(f"| {run.fixture_id} | {run.horizon} | {run.policy} | "
              f"{shown(run.expected_charge)} | {shown(run.max_regret)} | "
              f"{shown(run.normalized_regret)} | {shown(run.theorem_scale_ratio)} | "
              f"{shown(run.beta) if run.beta is not None else '—'} | "
              f"{shown(run.source_bound) if run.source_bound is not None else '—'} |")

    print()
    print("Blum--Mansour comparator detail:")
    print()
    print("| fixture | T | comparator | counterfactual charge | regret | positive-saving mass |")
    print("|---|---:|---|---:|---:|---:|")
    for run in runs:
        if run.policy != "blum_mansour":
            continue
        for program in AUDITED_PROGRAMS:
            identifier = program.program_id
            print(f"| {run.fixture_id} | {run.horizon} | {identifier} | "
                  f"{shown(run.comparator_charge[identifier])} | "
                  f"{shown(run.regret[identifier])} | "
                  f"{shown(run.failure_mass[identifier])} |")

    print()
    print("Integration audit (sampled Blum--Mansour path at T=96):")
    print()
    print("| fixture | record | identity | canonical | no erasure | response service | non-capture | compute priced | integrated |")
    print("|---|---|---|---|---|---|---|---|---|")
    for builder in FIXTURE_BUILDERS:
        run = next(run for run in run_fixture(builder(96))
                   if run.policy == "blum_mansour")
        audit = integration_audit(run)
        mark = lambda value: "yes" if value else "no"
        print(f"| {run.fixture_id} | {mark(audit.well_formed_record)} | "
              f"{mark(audit.identity_replay_faithful)} | "
              f"{mark(audit.canonical_responses)} | {mark(audit.no_burden_erasure)} | "
              f"{mark(audit.response_service_feasible)} | "
              f"{mark(audit.legality_non_capture)} | "
              f"{mark(audit.learning_computation_accounted)} | "
              f"{mark(audit.integrated)} |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
