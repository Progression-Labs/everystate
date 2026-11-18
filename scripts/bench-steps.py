#!/usr/bin/env python3
"""CPU time (user+sys) of several everystate binaries on three model sets, interleaved round by round so
that drift of a shared machine affects every binary alike. Median and minimum of --runs per cell.

usage: bench-steps.py --out FILE [--runs 5] [--sets large5,large11,bench12] BIN [BIN ...]
  large5 / large11 need a directory of generated Feynman oracle configurations (FEYNMAN_CFG, as written by
  scripts/feynman-bench.ts --out DIR, i.e. DIR/cfg); bench12 needs EXAMPLES (tlaplus/Examples).
"""
import json, os, re, subprocess, sys, statistics

args = sys.argv[1:]
def opt(name, default):
    if name in args:
        i = args.index(name); v = args[i + 1]; del args[i:i + 2]; return v
    return default
out = opt("--out", None); runs = int(opt("--runs", "5")); sets = opt("--sets", "large5,large11,bench12").split(",")
bins = [os.path.abspath(b) for b in args]
CFG = os.environ.get("FEYNMAN_CFG", "")
EX = os.environ.get("EXAMPLES", "/home/user/refs/Examples")
models = []  # (set, name, cwd, argv)
if "large5" in sets:
    for name, mod in [("OrSet-fixed-f1", "OrSet"), ("OrSet-fixed-f4", "OrSet"), ("ReadRepair-fixed-f6", "ReadRepair"), ("LostUpdate-fixed-f6", "LostUpdate"), ("LeaseLock-fixed-f5", "LeaseLock")]:
        models.append(("large5", name, os.path.join(CFG, "large", name), ["-deadlock", "-json", "-config", mod + ".cfg", mod + ".tla"]))
if "large11" in sets:
    for name in ["LeaseLock-fixed-f1", "LeaseLock-buggy-f1", "OrSet-fixed-f0", "OrSet-fixed-f1", "OrSet-buggy-f1", "ReadRepair-fixed-f0", "ReadRepair-fixed-f1", "ReadRepair-buggy-f0", "ReadRepair-buggy-f1", "LostUpdate-fixed-f1", "LostUpdate-buggy-f1"]:
        mod = name.split("-")[0]
        models.append(("large11", name, os.path.join(CFG, name), ["-deadlock", "-json", "-config", mod + ".cfg", mod + ".tla"]))
if "bench12" in sets:
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "bench.mjs")).read()
    for cfg, spec in re.findall(r"\['(specifications/[^']+\.cfg)', '(specifications/[^']+\.tla)'", src):
        models.append(("bench12", os.path.basename(cfg)[:-4], EX, ["-json", "-config", cfg, spec]))

# Every run is appended to FILE.jsonl as it finishes; a restarted benchmark continues from there.
cells = {}
done = set()
log = (out + ".jsonl") if out else None
def record(r):
    c = cells.setdefault((r["set"], r["model"], r["bin"]), {"cpu": [], "rss": 0})
    c["cpu"].append(r["cpu"]); c["rss"] = max(c["rss"], r["rss"])
    c["distinct"] = r["distinct"]; c["generated"] = r["generated"]; c["status"] = r["status"]
    done.add((r["round"], r["set"], r["model"], r["bin"]))
if log and os.path.exists(log):
    for line in open(log):
        try: record(json.loads(line))
        except Exception: pass
for rnd in range(runs):
    for m in models:
        for b in bins:
            if (rnd, m[0], m[1], os.path.basename(b)) in done:
                continue
            p = subprocess.Popen([b] + m[3], cwd=m[2], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            o = p.stdout.read(); _, st, ru = os.wait4(p.pid, 0)
            try: j = json.loads(o.decode().strip().split("\n")[-1])
            except Exception: j = {}
            r = {"round": rnd, "set": m[0], "model": m[1], "bin": os.path.basename(b), "cpu": ru.ru_utime + ru.ru_stime, "rss": ru.ru_maxrss // 1024, "distinct": j.get("distinct"), "generated": j.get("generated"), "status": j.get("status"), "load": os.getloadavg()[0]}
            record(r)
            if log:
                with open(log, "a") as f: f.write(json.dumps(r) + "\n")
    print(f"round {rnd + 1}/{runs} done, load {os.getloadavg()[0]:.1f}", file=sys.stderr, flush=True)
rows = []
for m in models:
    row = {"set": m[0], "model": m[1]}
    for b in bins:
        c = cells[(m[0], m[1], os.path.basename(b))]
        row[os.path.basename(b)] = {"medianCpuS": round(statistics.median(c["cpu"]), 3), "minCpuS": round(min(c["cpu"]), 3), "rssMb": c["rss"], "distinct": c["distinct"], "generated": c["generated"], "status": c["status"]}
    rows.append(row)
    print(m[0].ljust(8), m[1].ljust(24), " ".join(f"{row[os.path.basename(b)]['medianCpuS']:7.2f}" for b in bins), row[os.path.basename(bins[0])]["distinct"], flush=True)
if out:
    json.dump({"load": os.getloadavg(), "runs": runs, "binaries": [os.path.basename(b) for b in bins], "rows": rows}, open(out, "w"), indent=1)
