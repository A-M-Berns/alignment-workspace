#!/usr/bin/env python3
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
raise SystemExit(subprocess.call([sys.executable, "-m", "unittest", "discover", "-s", str(HERE), "-v"]))

