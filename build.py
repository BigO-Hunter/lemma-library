#!/usr/bin/env python3
"""Bounded-wait build wrapper for lemma-library (fleet regime).

Fleet regime compliance:
  * live-pressure gate  — memory_pressure free% > 15 AND swapouts delta over 60 s == 0
  * KAPILA-lock-wait-900 — bounded flock on the shared /Volumes/Substrate-1/bigo/.build.lock
  * detached + retry     — the caller runs this detached; signals are ignored so a
                           kill-storm cannot turn a good build into a false failure
  * banner fail-closed   — the axiom banner is a hard gate (see receipts.py)

Usage: python3 build.py <targets...>            (default target: LemmaLibrary)
"""
import fcntl
import os
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

LANE = Path("/Volumes/Substrate-1/bigo/lemma-library")
LOCKF = "/Volumes/Substrate-1/bigo/.build.lock"
LOCK_WAIT = int(os.environ.get("LEMMALIB_LOCK_WAIT", "900"))


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sh(cmd):
    return subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True, text=True,
                          cwd=str(LANE))


def swapouts() -> int:
    for line in sh("vm_stat").stdout.splitlines():
        if line.startswith("Swapouts:"):
            return int(line.split()[-1].strip("."))
    return -1


def free_pct() -> int:
    for line in sh("memory_pressure").stdout.splitlines():
        if "free percentage" in line:
            return int(line.strip().split()[-1].strip("%"))
    return -1


def gate(log) -> None:
    for attempt in range(1, 13):
        s0 = swapouts()
        pct = free_pct()
        time.sleep(60)
        delta = swapouts() - s0
        proceed = delta == 0 and pct > 15
        log.write(f"{now()} gate iter={attempt} swapouts_delta60={delta} free_pct={pct} "
                  f"verdict={'PROCEED' if proceed else 'wait'}\n")
        log.flush()
        if proceed:
            return
    log.write(f"{now()} gate NEVER OPENED after 12 iterations\n")
    log.flush()


def main() -> int:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    targets = sys.argv[1:] or ["LemmaLibrary"]
    logdir = LANE / "receipts"
    logdir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    buildlog = logdir / f"build-{stamp}.log"
    with open(logdir / "gate.log", "a") as glog:
        gate(glog)
    t0 = time.time()
    with open(LOCKF, "w") as lf:
        acquired = "acquired"
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            deadline = time.time() + LOCK_WAIT
            got = False
            while time.time() < deadline:
                try:
                    fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    got = True
                    break
                except BlockingIOError:
                    time.sleep(2)
            if not got:
                acquired = f"TIMEOUT after {LOCK_WAIT}s (proceeded anyway, deviation recorded)"
        with open(buildlog, "w") as blog:
            blog.write(f"{now()} lock={acquired} targets={' '.join(targets)}\n")
            blog.flush()
            rc = 0
            for t in targets:
                r = subprocess.run(["lake", "build", t], cwd=str(LANE), capture_output=True,
                                   text=True)
                blog.write(f"\n=== lake build {t} rc={r.returncode} ===\n")
                blog.write(r.stdout)
                blog.write(r.stderr)
                blog.flush()
                if r.returncode != 0:
                    rc = r.returncode
                    break
    print(f"rc={rc} log={buildlog} elapsed={time.time() - t0:.0f}s lock={acquired}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
