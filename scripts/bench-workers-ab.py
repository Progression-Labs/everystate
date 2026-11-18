#!/usr/bin/env python3
"""Wall-clock and CPU time of two (or more) everystate binaries with -workers 1 and -workers N on the
five larger Feynman oracle models and (optionally) Examples models, one process at a time. Every run is
appended to OUT.jsonl; a restarted measurement continues from there.

usage: bench-workers-ab.py --out FILE [--runs 3] [--workers 1,4] [--examples cfg:spec,...] BIN [BIN ...]
  env: FEYNMAN_CFG (the cfg directory written by scripts/feynman-bench.ts), EXAMPLES
"""
import json, os, subprocess, sys, statistics, time
args = sys.argv[1:]
def opt(name, default):
    if name in args:
        i = args.index(name); v = args[i + 1]; del args[i:i + 2]; return v
    return default
out = opt("--out", "bench/workers-ab.json"); runs = int(opt("--runs", "3")); workers = opt("--workers", "1,4").split(",")
examples = [x for x in opt("--examples", "").split(",") if x]
bins = [os.path.abspath(b) for b in args]
CFG = os.environ.get("FEYNMAN_CFG", ""); EX = os.environ.get("EXAMPLES", "/home/user/refs/Examples")
models = [(n, os.path.join(CFG, "large", n), ["-deadlock", "-json", "-config", m + ".cfg", m + ".tla"]) for n, m in
          [("OrSet-fixed-f4", "OrSet"), ("ReadRepair-fixed-f6", "ReadRepair"), ("LostUpdate-fixed-f6", "LostUpdate"), ("LeaseLock-fixed-f5", "LeaseLock")]]
for e in examples:
    cfg, spec = e.split(":"); models.append((os.path.basename(cfg)[:-4], EX, ["-json", "-config", cfg, spec]))
log = out + ".jsonl"; rows = []
if os.path.exists(log):
    rows = [json.loads(l) for l in open(log) if l.strip()]
done = {(r["round"], r["model"], r["bin"], r["workers"]) for r in rows}
for rnd in range(runs):
    for name, cwd, argv in models:
        for w in workers:
            for b in bins:
                key = (rnd, name, os.path.basename(b), w)
                if key in done: continue
                t = time.monotonic()
                p = subprocess.Popen([b, "-workers", w] + argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
                o = p.stdout.read(); _, st, ru = os.wait4(p.pid, 0)
                wall = time.monotonic() - t
                try: j = json.loads(o.decode().strip().split("\n")[-1])
                except Exception: j = {}
                r = {"round": rnd, "model": name, "bin": key[2], "workers": w, "wall": wall, "cpu": ru.ru_utime + ru.ru_stime, "rss": ru.ru_maxrss // 1024, "distinct": j.get("distinct"), "generated": j.get("generated"), "load": os.getloadavg()[0]}
                rows.append(r)
                with open(log, "a") as f: f.write(json.dumps(r) + "\n")
table = []
for name, _, _ in models:
    for w in workers:
        row = {"model": name, "workers": w}
        for b in bins:
            rs = [r for r in rows if r["model"] == name and r["workers"] == w and r["bin"] == os.path.basename(b)]
            row[os.path.basename(b)] = {"wallS": round(statistics.median(r["wall"] for r in rs), 2), "cpuS": round(statistics.median(r["cpu"] for r in rs), 2), "rssMb": max(r["rss"] for r in rs), "distinct": rs[-1]["distinct"], "generated": rs[-1]["generated"]}
        table.append(row)
        print(name.ljust(22), f"workers {w}", " | ".join(f"{os.path.basename(b)}: wall {row[os.path.basename(b)]['wallS']:.2f}s cpu {row[os.path.basename(b)]['cpuS']:.2f}s rss {row[os.path.basename(b)]['rssMb']}MB" for b in bins), flush=True)
json.dump({"load": os.getloadavg(), "runs": runs, "rows": table}, open(out, "w"), indent=1)
