#!/usr/bin/env python3
"""Declaration-granular extractor: emit named Lean declarations with their docstrings.

Given a source file and a list of declaration names, emit the text of each declaration
from its attached `/-- ... -/` docstring (or attribute line) through the line before the
next top-level declaration.  Preserves proof bodies byte-for-byte, which is the point:
the ported lemma must be the *same proof*, recompiled in a new package.
"""
import re
import sys
from pathlib import Path

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )?'
                  r'(?:theorem|lemma|def|structure|abbrev|instance)\s+([A-Za-z0-9_.\'_]+)')


def decls(path: Path):
    lines = path.read_text().splitlines()
    starts = []
    for i, ln in enumerate(lines):
        m = DECL.match(ln)
        if m:
            starts.append((i, m.group(1)))
    return lines, starts


def block_start(lines, i):
    """Walk back from declaration line `i` over its attached docstring/attributes.

    The emitted block MUST start here and the previous block MUST end here: taking the
    next declaration line as the previous block's end swallows that declaration's
    docstring, and the docstring then appears twice (which is a parse error, not a
    cosmetic duplication — measured: `expected 'lemma'` at the second copy).
    """
    j = i
    while j > 0:
        prev = lines[j - 1].strip()
        if prev.startswith('@['):
            j -= 1
        elif prev.endswith('-/'):
            k = j - 1
            while k >= 0 and not lines[k].lstrip().startswith('/--'):
                k -= 1
            if k < 0:
                break
            j = k
            break
        elif prev == '':
            break
        else:
            break
    return j


def extract(path: Path, names, out_path: Path, header: str = "", footer: str = ""):
    lines, starts = decls(path)
    chunks = []
    missing = []
    bstarts = [block_start(lines, i) for i, _ in starts]
    for name in names:
        hit = None
        for k, (i, n) in enumerate(starts):
            if n == name:
                hit = k
                break
        if hit is None:
            missing.append(name)
            continue
        j = bstarts[hit]
        end = bstarts[hit + 1] if hit + 1 < len(starts) else len(lines)
        # trim trailing blank lines and any section markers
        body = lines[j:end]
        while body and body[-1].strip() == '':
            body.pop()
        chunks.append("\n".join(body))
    if missing:
        raise SystemExit(f"MISSING in {path.name}: {missing}")
    text = (header + "\n\n".join(chunks) + "\n" + footer)
    out_path.write_text(text)
    print(f"{out_path.name}: {len(names)} decls, {len(text.splitlines())} lines")


if __name__ == "__main__":
    print("use as a module", file=sys.stderr)
