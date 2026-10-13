#!/usr/bin/env python3
"""Positive control for verify8pz's anchor assertion (L0 <= L): replay a DATA file with T1 WITHOUT step 5 (tz.t1 with
reclip=False, the pre-2026-10-03 semantics).  On DATA_try2_0.0002.VOID_L0GAP.json (the first emission, under that semantics) it
reported anchor = 70 failing leaves, so the assertion fires.  Usage: ctl_anchor.py DATA.json"""
import os, sys, runpy
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import tz
_t1 = tz.t1
tz.t1 = lambda l, u, cons, Q: _t1(l, u, cons, Q, reclip=False)
sys.argv = [os.path.join(HERE, "verify8pz.py"), sys.argv[1]]
runpy.run_path(sys.argv[0], run_name="__main__")
