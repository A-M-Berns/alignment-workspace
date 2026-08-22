from __future__ import annotations

import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main() -> int:
    result = subprocess.run(
        [sys.executable, "-m", "unittest", "discover", "-s", str(HERE), "-v"],
        check=False,
    )
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
