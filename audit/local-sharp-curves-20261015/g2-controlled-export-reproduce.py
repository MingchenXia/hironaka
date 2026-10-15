#!/usr/bin/env python3
"""Reproduce the bounded, read-only export guard; no exporter or Lean process."""
from pathlib import Path
import os
import runpy

os.environ.setdefault('HIRONAKA_REVIEW_AUDIT_ROOT',str(Path(__file__).resolve().parent))
runpy.run_path(
    str(Path(__file__).with_name('g2-controlled-export-byteguard.py')),
    run_name='__main__',
)
