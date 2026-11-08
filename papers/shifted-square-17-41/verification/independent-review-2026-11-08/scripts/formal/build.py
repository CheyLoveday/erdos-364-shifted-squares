#!/usr/bin/env python3
"""Incremental out-of-tree builder for the Erdos364 Lean sources.

Compiles ../.. (the repository root) Erdos364/*.lean into ./leanbuild,
using the ambient LEAN_PATH plus ./leanbuild at the front.  Never writes
inside the repository working tree.

Usage: python3 build.py [--jobs N] [--target MODULE]...
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get("ERDOS_SRC",
                      os.path.abspath(os.path.join(HERE, "..", "..", "..")))
BUILD = os.environ.get("ERDOS_BUILD", os.path.join(HERE, "leanbuild"))


def discover():
    mods = {}
    for root, _dirs, files in os.walk(os.path.join(REPO, "Erdos364")):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            mod = os.path.relpath(p, REPO)[:-5].replace(os.sep, ".")
            src = open(p, encoding="utf-8").read()
            imports = re.findall(r"^import\s+(\S+)", src, re.M)
            mods[mod] = {
                "path": p,
                "imports": [i for i in imports if i in mods or i.startswith("Erdos364")],
            }
    # second pass now that all modules are known
    for mod, info in mods.items():
        src = open(info["path"], encoding="utf-8").read()
        info["imports"] = [i for i in re.findall(r"^import\s+(\S+)", src, re.M)
                           if i in mods]
        info["mtime"] = os.path.getmtime(info["path"])
    return mods


def olean(mod):
    return os.path.join(BUILD, mod.replace(".", os.sep) + ".olean")


def up_to_date(mod, info):
    o = olean(mod)
    return os.path.exists(o) and os.path.getmtime(o) >= info["mtime"]


def compile_one(mod, info, env):
    o = olean(mod)
    os.makedirs(os.path.dirname(o), exist_ok=True)
    cmd = ["lean", "-R", REPO, "-o", o,
           "-i", o[:-len(".olean")] + ".ilean", info["path"]]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=REPO, env=env, capture_output=True, text=True)
    return mod, p.returncode, time.time() - t0, p.stdout + p.stderr


def closure(mods, targets):
    seen = set()
    stack = list(targets)
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        stack.extend(mods[m]["imports"])
    return seen


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--target", action="append", default=[])
    args = ap.parse_args()

    mods = discover()
    targets = args.target or ["Erdos364.DicksonLucas.ShiftedSquarePropagation"]
    need = closure(mods, targets)
    env = dict(os.environ)
    env["LEAN_PATH"] = BUILD + ":" + env.get("LEAN_PATH", "")

    pending = {m for m in need if not up_to_date(m, mods[m])}
    print(f"{len(need)} modules in closure, {len(pending)} to build, "
          f"{len(need) - len(pending)} already built", flush=True)
    failures = []
    done = set(m for m in need if up_to_date(m, mods[m]))
    t00 = time.time()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running = {}
        while pending or running:
            ready = [m for m in pending
                     if all(i in done for i in mods[m]["imports"])]
            for m in ready:
                if len(running) >= args.jobs:
                    break
                pending.discard(m)
                running[pool.submit(compile_one, m, mods[m], env)] = m
            if not running:
                if pending:
                    for m in sorted(pending):
                        missing = [i for i in mods[m]["imports"] if i not in done]
                        print(f"BLOCKED {m}: {missing}", flush=True)
                    break
                continue
            fut = next(f for f in running if f.done()) if any(
                f.done() for f in running) else None
            if fut is None:
                fut = next(iter(running))
            # wait for at least one completion
            for f in list(running):
                if f.done():
                    fut = f
                    break
            else:
                import concurrent.futures as cf
                fut = next(cf.as_completed(list(running)))
            mod, rc, dt, out = fut.result()
            del running[fut]
            if rc == 0:
                done.add(mod)
                print(f"ok   {mod} ({dt:.1f}s)", flush=True)
            else:
                failures.append((mod, out))
                print(f"FAIL {mod} ({dt:.1f}s)\n{out[:4000]}", flush=True)
    print(f"elapsed {time.time() - t00:.0f}s; built {len(done)}/{len(need)}; "
          f"failures {len(failures)}", flush=True)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
