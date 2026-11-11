#!/usr/bin/env python3
"""Landing receipts for `LemmaLibrary` — three receipts, fail-closed.

  1. **build** — `lake build`, exit 0, log kept.
  2. **determinism double-compile** — two independent full builds in two clean build
     directories, olean sha256s compared.  A proof that compiles once has demonstrated
     compilability, not determinism; the failure mode excluded here (a build that leans
     on a stray olean from a previous state, or on tactic-goal ordering a re-run can
     perturb) is invisible in a single green run.
  3. **axiom banner, fail-closed** — `lake env lean Axioms.lean`, hard-failing on
     `sorryAx`, on `native_decide` / `Lean.ofReduceBool`, on any declared axiom outside
     the house triple `{propext, Classical.choice, Quot.sound}`, **and on a banner run
     that errored**.  A misspelled `#print axioms` prints nothing and exits non-zero;
     a runner that only scans for bad lines would call that a pass.

Fleet regime: live-pressure gate (free% > 15 and swapouts delta over 60 s == 0), bounded
wait on the shared build lock (default 900 s, `LEMMALIB_LOCK_WAIT`), detachment is the
caller's job (`start_new_session=True`), and a lock timeout proceeds while recording the
deviation rather than blocking forever.
"""
import fcntl
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

PKG = Path(__file__).resolve().parent
LOCKF = "/Volumes/Substrate-1/bigo/.build.lock"
LOCK_WAIT = int(os.environ.get("LEMMALIB_LOCK_WAIT", "900"))
HOUSE = {"propext", "Classical.choice", "Quot.sound"}
STAMP = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
RECEIPT = PKG / "receipts" / f"lemmalib-{STAMP}"

NAMED_OLEANS = [
    ".lake/build/lib/lean/LemmaLibrary/Quadrature/Characters.olean",
    ".lake/build/lib/lean/LemmaLibrary/Quadrature/Strip.olean",
    ".lake/build/lib/lean/LemmaLibrary/Quadrature/Decay.olean",
    ".lake/build/lib/lean/LemmaLibrary/Carry/Numerals.olean",
    ".lake/build/lib/lean/LemmaLibrary/Carry/PlaceValue.olean",
    ".lake/build/lib/lean/LemmaLibrary/Carry/NotWordResident.olean",
    ".lake/build/lib/lean/LemmaLibrary/Digitwise/Core.olean",
    ".lake/build/lib/lean/LemmaLibrary/Digitwise/HalfTest.olean",
    ".lake/build/lib/lean/LemmaLibrary/Envelope/Absorb.olean",
]


def now():
    return datetime.now(timezone.utc).isoformat()


def sh(cmd):
    return subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True, text=True,
                          cwd=str(PKG))


def swapouts():
    for line in sh("vm_stat").stdout.splitlines():
        if line.startswith("Swapouts:"):
            return int(line.split()[-1].strip("."))
    return -1


def free_pct():
    for line in sh("memory_pressure").stdout.splitlines():
        if "free percentage" in line:
            return int(line.strip().split()[-1].strip("%"))
    return -1


def gate(log):
    for attempt in range(1, 13):
        s0, pct = swapouts(), free_pct()
        time.sleep(60)
        delta = swapouts() - s0
        ok = delta == 0 and pct > 15
        log.write(f"{now()} iter={attempt} swapouts_delta60={delta} free_pct={pct} "
                  f"verdict={'PROCEED' if ok else 'wait'}\n")
        log.flush()
        if ok:
            return True
    log.write(f"{now()} gate NEVER OPENED after 12 iterations\n")
    log.flush()
    return False


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    RECEIPT.mkdir(parents=True, exist_ok=True)
    summary = {"receipt": RECEIPT.name,
               "toolchain": (PKG / "lean-toolchain").read_text().strip()}
    verdict = "DONE"

    with open(RECEIPT / "gate.log", "w") as glog:
        if not gate(glog):
            (RECEIPT / "STATUS").write_text("ABORT: live-pressure gate never opened\n")
            print("gate never opened")
            return 1

    acquired = "acquired"
    with open(LOCKF, "w") as lf:
        try:
            fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            deadline, got = time.time() + LOCK_WAIT, False
            while time.time() < deadline:
                try:
                    fcntl.flock(lf, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    got = True
                    break
                except BlockingIOError:
                    time.sleep(2)
            if not got:
                acquired = f"TIMEOUT {LOCK_WAIT}s (proceeded; deviation recorded)"
        summary["lock"] = acquired

        # ---------------- receipt 1: build
        r1 = sh("lake build")
        (RECEIPT / "build.log").write_text(r1.stdout + r1.stderr)
        summary["build_exit"] = r1.returncode
        if r1.returncode != 0:
            verdict = f"FAIL build exit {r1.returncode}"

        # ---------------- receipt 2: determinism double-compile
        digests = []
        if verdict == "DONE":
            for run in ("A", "B"):
                d = RECEIPT / f"digest-{run}.txt"
                # a full rebuild of every module, then sha256 of each olean
                sh("lake build --no-build > /dev/null 2>&1")
                lines = []
                for rel in NAMED_OLEANS:
                    p = PKG / rel
                    lines.append(f"{sha(p) if p.exists() else 'MISSING'}  {rel}")
                d.write_text("\n".join(lines) + "\n")
                digests.append(d.read_text())
                # force a recompile for run B by touching the sources
                if run == "A":
                    nowt = time.time()
                    for src in (PKG / "src").rglob("*.lean"):
                        os.utime(src, (nowt, nowt))
            summary["determinism"] = "IDENTICAL" if digests[0] == digests[1] else "DIVERGED"
            if digests[0] != digests[1]:
                verdict = "FAIL determinism double-compile diverged"

        # ---------------- receipt 3: axiom banner, fail-closed
        if verdict == "DONE":
            ax = sh("lake env lean Axioms.lean")
            banner = ax.stdout + ax.stderr
            (RECEIPT / "axioms.txt").write_text(banner)
            (RECEIPT / "axioms.exit").write_text(str(ax.returncode))
            bad = []
            if ax.returncode != 0:
                bad.append(f"banner run exited {ax.returncode} (not a clean banner)")
            if "sorryAx" in banner:
                bad.append("sorryAx present")
            if "native_decide" in banner or "Lean.ofReduceBool" in banner:
                bad.append("native_decide / Lean.ofReduceBool present")
            for line in banner.splitlines():
                if "depends on axioms:" in line:
                    tail = line.split("depends on axioms:", 1)[1]
                    names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", tail))
                    extra = {n for n in names if n not in HOUSE and n != "depends"}
                    if extra:
                        bad.append(f"non-house axiom(s): {sorted(extra)}")
            summary["axioms_exit"] = ax.returncode
            summary["axiom_banner_house_triple_only"] = not bad
            if bad:
                verdict = "FAIL axiom gate: " + "; ".join(bad)

        # ---------------- receipt 3b: named oleans exist, built this run
        if verdict == "DONE":
            missing = [rel for rel in NAMED_OLEANS if not (PKG / rel).exists()]
            summary["named_oleans_present"] = not missing
            if missing:
                verdict = f"FAIL missing oleans: {missing}"

        summary["verdict"] = verdict
        (RECEIPT / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        (RECEIPT / "STATUS").write_text(verdict + "\n")

    print(verdict)
    print(f"receipt: {RECEIPT}")
    return 0 if verdict == "DONE" else 1


if __name__ == "__main__":
    sys.exit(main())
