#!/usr/bin/env bun
// Conformance and benchmark against Feynman (a TypeScript model checker) on the TLA+ oracle models that ship
// in its repository. Nothing of Feynman's is copied here: the script reads a local clone.
//
//   bun scripts/feynman-bench.ts [--runs 3] [--min-states N] [--only Module] [--skip-feynman-timing]
//                                [--large] [--out DIR] [--json FILE]
//   env: FEYNMAN (clone root, default /home/user/refs/feynman), EVERYSTATE (binary, default target/release),
//        EVERYSTATE_ENGINE and any other EVERYSTATE_* variable are passed through to the binary.
//
// Default mode: for every configuration of Feynman's corpus that has a TLA+ oracle (125 at commit 80e674b)
//   - Feynman runs in-process; its distinct states are the TLA projection of each state it visits,
//   - everystate runs as a process (-deadlock -json) on the oracle model with the same constants,
//   - distinct-state counts must agree and, per invariant, the verdict and the counterexample length,
//   - CPU time (user+sys) is reported for both: the median of --runs.
// --large: the five larger models (more faults than the corpus uses), each engine as a whole process;
//   reports CPU seconds, states per CPU-second and peak RSS. Feynman is run through this same script (--one).
// Exit status 1 when any configuration disagrees.
import { spawnSync } from "node:child_process";
import { appendFileSync, copyFileSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { loadavg, tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { parseArgs } from "node:util";

const FEY = process.env.FEYNMAN ?? "/home/user/refs/feynman";
const ES = process.env.EVERYSTATE ?? resolve(import.meta.dir, "../target/release/everystate");
const { values } = parseArgs({
  options: {
    runs: { type: "string", default: "3" },
    "min-states": { type: "string", default: "0" },
    only: { type: "string" },
    out: { type: "string" },
    json: { type: "string" },
    large: { type: "boolean", default: false },
    "skip-feynman-timing": { type: "boolean", default: false },
    one: { type: "string" }, // internal: "Module,variant,faults"
  },
});
const runs = Number(values.runs);
const out = values.out ?? mkdtempSync(join(tmpdir(), "feynman-bench-"));
const { corpus, configured } = await import(`${FEY}/packages/feynman/test/examples/corpus.ts`);
const { check, pendingText } = await import(`${FEY}/packages/feynman/src/check/index.ts`);
const { sortedJson } = await import(`${FEY}/packages/feynman/src/spec/json.ts`);
const median = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];
const env: Record<string, string> = { ...(process.env as any) };
delete env.JAVA_TOOL_OPTIONS;
const load = () => loadavg().map((l) => l.toFixed(1)).join(" ");

// The projection of a Feynman world onto the variables of the TLA+ model (what Feynman's own oracle test compares).
function projection(world: any, memory: string): string {
  const channels = new Map<string, string[]>();
  for (const p of [...world.pending].sort((a: any, b: any) => a.id - b.id))
    if (p.kind === "deliver" && p.ordered) channels.set(`${p.from}>${p.to}`, [...(channels.get(`${p.from}>${p.to}`) ?? []), pendingText(p)]);
  return [
    world.instances.map((i: any) => `${i.id}=${sortedJson(i.state)}${i.variables ? `@${sortedJson(i.variables)}` : ""}`).sort().join("\n"),
    world.pending.filter((p: any) => p.kind !== "deliver" || !p.ordered).map((p: any) => pendingText(p)).sort().join("\n"),
    [...channels].map(([c, q]) => `${c}: ${q.join(" ; ")}`).sort().join("\n"),
    sortedJson(world.fresh),
    sortedJson(world.variables ?? {}),
    memory,
  ].join("\n--\n");
}
function feynmanSpec(module: string, variant: string, faults: number) {
  const ex = corpus.find((e: any) => e.tla?.module === module);
  if (!ex) throw new Error(`no corpus entry with TLA+ module ${module}`);
  const o = ex.tla;
  const { spec, bounds } = configured(ex.spec(variant), { faults, instances: ex.instances ?? {}, ...(o.depth ? { depth: o.depth } : {}) });
  return { ex, o, spec, bounds };
}
function cfgText(o: any, variant: string, faults: number, repeats: number, inv?: string) {
  const consts: Record<string, unknown> = { Buggy: variant === "buggy" ? "TRUE" : "FALSE", Faults: faults, Repeats: repeats, ...(o.depth ? { Depth: o.depth } : {}) };
  return ["CONSTANTS", ...Object.entries(consts).map(([k, v]) => `  ${k} = ${v}`), "INIT Init", "NEXT Next", ...(o.depth || o.view ? ["VIEW view"] : []), ...(inv ? ["INVARIANTS", `  ${inv}`] : [])].join("\n") + "\n";
}
function everystate(dir: string, module: string, cfg: string, json = true) {
  const r = Bun.spawnSync({ cmd: [ES, "-deadlock", ...(json ? ["-json"] : []), "-config", cfg, `${module}.tla`], cwd: dir, env, stdout: "pipe", stderr: "pipe" });
  const stdout = r.stdout.toString();
  let j: any;
  try {
    j = JSON.parse(stdout.trim().split("\n").at(-1)!);
  } catch {
    j = { status: "unparsed", stdout: stdout.slice(0, 300) };
  }
  const ru: any = r.resourceUsage;
  return { j, cpuMs: Number(ru?.cpuTime?.total ?? NaN) / 1000, rssMb: Number(ru?.maxRSS ?? NaN) / (1 << 20) };
}

if (values.one) {
  // one Feynman run as a whole process (for --large)
  const [module, variant, faults, mode] = values.one.split(",");
  const { spec, bounds } = feynmanSpec(module, variant, Number(faults));
  const t = performance.now();
  const seen = new Set<string>();
  const watch = mode === "project" ? [[], { watch: { state: (w: any, m: string) => seen.add(projection(w, m)) } }] : [];
  const r = await (check as any)(spec, { maxStates: 50_000_000, timeLimit: 3_000_000, memoryLimit: 12_000, walks: 0, symmetry: false, ...bounds }, ...watch);
  console.log(JSON.stringify({ states: r.states, projected: seen.size, exhaustive: r.exhaustive, searchMs: Math.round(performance.now() - t) }));
  process.exit(0);
}

mkdirSync(out, { recursive: true });
const rows: any[] = [];
let bad = 0;
console.log(`load ${load()}; runs ${runs}; everystate ${ES}; engine ${process.env.EVERYSTATE_ENGINE ?? "(default)"}; out ${out}`);

if (values.large) {
  const LARGE: [string, string, number, number][] = [
    ["OrSet", "fixed", 1, 2],
    ["OrSet", "fixed", 4, 2],
    ["ReadRepair", "fixed", 6, 2],
    ["LostUpdate", "fixed", 6, 2],
    ["LeaseLock", "fixed", 5, 2],
  ];
  console.log(["model".padEnd(24), "distinct".padStart(9), "fey cpu s".padStart(10), "fey st/s".padStart(9), "fey MB".padStart(7), "es cpu s".padStart(9), "es st/s".padStart(9), "es MB".padStart(6), "agree"].join(" "));
  for (const [module, variant, faults, repeats] of LARGE) {
    if (values.only && module !== values.only) continue;
    const { o } = feynmanSpec(module, variant, faults);
    const name = `${module}-${variant}-f${faults}`;
    const dir = join(out, "cfg", name);
    mkdirSync(dir, { recursive: true });
    copyFileSync(join(FEY, "packages/feynman/examples/oracles", `${module}.tla`), join(dir, `${module}.tla`));
    writeFileSync(join(dir, `${module}.cfg`), cfgText(o, variant, faults, repeats));
    const fcpu: number[] = [], frss: number[] = [], ecpu: number[] = [], erss: number[] = [];
    let fstates = NaN, esj: any;
    // the distinct TLA-projected states, from one untimed run (Feynman's own count can include states the projection merges)
    const pr = Bun.spawnSync({ cmd: ["bun", import.meta.path, "--one", `${module},${variant},${faults},project`], env, stdout: "pipe", stderr: "pipe" });
    let projected = NaN;
    try {
      projected = JSON.parse(pr.stdout.toString().trim().split("\n").at(-1)!).projected;
    } catch {}
    for (let i = 0; i < runs; i++) {
      if (!values["skip-feynman-timing"] || i === 0) {
        const r = Bun.spawnSync({ cmd: ["bun", import.meta.path, "--one", `${module},${variant},${faults}`], env, stdout: "pipe", stderr: "pipe" });
        const ru: any = r.resourceUsage;
        fcpu.push(Number(ru?.cpuTime?.total ?? NaN) / 1e6);
        frss.push(Number(ru?.maxRSS ?? NaN) / (1 << 20));
        try {
          fstates = JSON.parse(r.stdout.toString().trim().split("\n").at(-1)!).states;
        } catch {}
      }
      const e = everystate(dir, module, `${module}.cfg`, true);
      ecpu.push(e.cpuMs / 1000);
      erss.push(e.rssMb);
      esj = e.j;
    }
    const problems = esj.distinct === projected ? [] : [`distinct es=${esj.distinct} fey=${projected}`];
    if (problems.length) bad++;
    const row = { at: new Date().toISOString(), load: loadavg()[0], config: name, large: true, distinct: esj.distinct, generated: esj.generated, feynmanCpuS: median(fcpu), feynmanRssMb: Math.round(median(frss)), everystateCpuS: median(ecpu), everystateRssMb: Math.round(median(erss)), feynmanStates: fstates, feynmanStatesPerCpuS: Math.round(fstates / median(fcpu)), everystateStatesPerCpuS: Math.round(esj.distinct / median(ecpu)), problems };
    rows.push(row);
    console.log([name.padEnd(24), String(row.distinct).padStart(9), row.feynmanCpuS.toFixed(2).padStart(10), String(row.feynmanStatesPerCpuS).padStart(9), String(row.feynmanRssMb).padStart(7), row.everystateCpuS.toFixed(2).padStart(9), String(row.everystateStatesPerCpuS).padStart(9), String(row.everystateRssMb).padStart(6), problems.length ? "NO: " + problems.join("; ") : "yes"].join(" "));
  }
} else {
  console.log(["config".padEnd(34), "distinct".padStart(9), "fey cpu".padStart(8), "es cpu".padStart(8), "es/fey".padStart(7), "agree"].join(" "));
  for (const ex of corpus) {
    const o = ex.tla;
    if (!o || (values.only && o.module !== values.only)) continue;
    for (const c of o.configs) {
      const name = `${o.module}-${c.variant}-f${c.faults}`;
      const dir = join(out, "cfg", name);
      mkdirSync(dir, { recursive: true });
      copyFileSync(join(FEY, "packages/feynman/examples/oracles", `${o.module}.tla`), join(dir, `${o.module}.tla`));
      writeFileSync(join(dir, `${o.module}.cfg`), cfgText(o, c.variant, c.faults, c.repeats));
      const { spec, bounds } = feynmanSpec(o.module, c.variant, c.faults);
      const B = { maxStates: 5_000_000, timeLimit: 300_000, walks: 0, symmetry: false, ...bounds };
      const seen = new Set<string>();
      const c0 = process.cpuUsage();
      const first = await check(spec, B, [], { watch: { state: (w: any, m: string) => seen.add(projection(w, m)) } });
      const c1 = process.cpuUsage(c0);
      const distinct = seen.size;
      if (distinct < Number(values["min-states"])) continue;
      // CPU time of the whole Bun process over the search (JIT and GC threads included): steadier than wall time under load
      const feycpu: number[] = values["skip-feynman-timing"] ? [(c1.user + c1.system) / 1000] : [];
      if (!values["skip-feynman-timing"])
        for (let i = 0; i < runs; i++) {
          const a = process.cpuUsage();
          await check(spec, B);
          const b = process.cpuUsage(a);
          feycpu.push((b.user + b.system) / 1000);
        }
      const escpu: number[] = [];
      let esj: any;
      for (let i = 0; i < runs; i++) {
        const e = everystate(dir, o.module, `${o.module}.cfg`);
        escpu.push(e.cpuMs);
        esj = e.j;
      }
      const problems: string[] = [];
      if (esj.distinct !== distinct) problems.push(`distinct es=${esj.distinct} fey=${distinct}`);
      for (const inv of o.invariants) {
        writeFileSync(join(dir, `${o.module}-${inv}.cfg`), cfgText(o, c.variant, c.faults, c.repeats, inv));
        const j = everystate(dir, o.module, `${o.module}-${inv}.cfg`).j;
        const theirs = j.status === "invariant" ? j.trace.length - 1 : j.status === "ok" ? undefined : `status ${j.status}`;
        const p = first.properties.find((x: any) => x.id === inv);
        const ours = !p ? "missing" : p.holds || p.unreached ? undefined : p.counterexample.events.length;
        if (theirs !== ours) problems.push(`${inv}: es=${theirs} fey=${ours}`);
      }
      if (problems.length) bad++;
      const row = { at: new Date().toISOString(), load: loadavg()[0], config: name, module: o.module, ...c, depth: o.depth, distinct, generated: esj.generated, feynmanCpuMs: median(feycpu), everystateCpuMs: median(escpu), problems };
      rows.push(row);
      appendFileSync(join(out, "results.jsonl"), JSON.stringify(row) + "\n");
      console.log([name.padEnd(34), String(distinct).padStart(9), row.feynmanCpuMs.toFixed(1).padStart(8), row.everystateCpuMs.toFixed(1).padStart(8), (row.everystateCpuMs / row.feynmanCpuMs).toFixed(1).padStart(7), problems.length ? "NO: " + problems.join("; ") : "yes"].join(" "));
    }
  }
  const sum = (k: string) => rows.reduce((a, r) => a + r[k], 0);
  console.log(`total CPU ms: feynman ${sum("feynmanCpuMs").toFixed(0)}, everystate ${sum("everystateCpuMs").toFixed(0)}`);
}
console.log(`${rows.length} configs, ${bad} with disagreements; load ${load()}`);
if (values.json) writeFileSync(values.json, JSON.stringify({ at: new Date().toISOString(), everystate: ES, engine: process.env.EVERYSTATE_ENGINE ?? null, runs, load: loadavg(), large: values.large, rows }, null, 1) + "\n");
process.exit(bad ? 1 : 0);
