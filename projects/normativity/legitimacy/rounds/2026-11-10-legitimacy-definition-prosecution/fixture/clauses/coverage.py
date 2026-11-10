"""Coverage, the single-run clause: every due offering arrived and was taken up."""
from __future__ import annotations

from ..model import due_of


def coverage(run, e):
    due = due_of(e)
    return sorted(due - run.taken_up)
