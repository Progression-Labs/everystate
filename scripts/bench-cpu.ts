#!/usr/bin/env bun
// CPU time (user+sys, median of --runs), peak RSS and state counts of the BENCHMARK.md models for one binary.
//   bun scripts/bench-cpu.ts [--runs 5] [--only substring] [--json FILE]     env: EVERYSTATE, EXAMPLES
// CPU time rather than wall-clock time: the benchmark machine is shared.
import { writeFileSync } from "node:fs";
import { loadavg } from "node:os";
import { resolve } from "node:path";
import { parseArgs } from "node:util";
const ES = process.env.EVERYSTATE ?? resolve(import.meta.dir, "../target/release/everystate");
const EXAMPLES = process.env.EXAMPLES ?? "/home/user/refs/Examples";
const { values } = parseArgs({ options: { runs: { type: "string", default: "5" }, only: { type: "string" }, json: { type: "string" } } });
const MODELS: [string, string][] = [
  ["specifications/transaction_commit/TCommit.cfg", "specifications/transaction_commit/TCommit.tla"],
  ["specifications/acp/ACP_SB_TLC.cfg", "specifications/acp/ACP_SB_TLC.tla"],
  ["specifications/StaleViewShrink/StaleShrinkV6Wait2x.cfg", "specifications/StaleViewShrink/StaleShrink.tla"],
  ["specifications/barriers/Barriers.cfg", "specifications/barriers/Barriers.tla"],
  ["specifications/TeachingConcurrency/SimpleRegular.cfg", "specifications/TeachingConcurrency/SimpleRegular.tla"],
  ["specifications/SimplifiedFastPaxos/Paxos.cfg", "specifications/SimplifiedFastPaxos/Paxos.tla"],
  ["specifications/byzpaxos/VoteProof.cfg", "specifications/byzpaxos/VoteProof.tla"],
  ["specifications/NanoBlockchain/MCNanoMedium.cfg", "specifications/NanoBlockchain/MCNano.tla"],
  ["specifications/Bakery-Boulangerie/MCBakery.cfg", "specifications/Bakery-Boulangerie/MCBakery.tla"],
  ["specifications/lamport_mutex/MCLamportMutex.cfg", "specifications/lamport_mutex/MCLamportMutex.tla"],
  ["specifications/btree/MCbtree.cfg", "specifications/btree/MCbtree.tla"],
  ["specifications/GameOfLife/GameOfLife.cfg", "specifications/GameOfLife/GameOfLife.tla"],
];
const median = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)];
const rows: any[] = [];
console.log(`load ${loadavg().map((l) => l.toFixed(1)).join(" ")}; ${ES}`);
for (const [cfg, spec] of MODELS) {
  if (values.only && !cfg.includes(values.only)) continue;
  const cpu: number[] = [], rss: number[] = [];
  let j: any = {};
  for (let i = 0; i < Number(values.runs); i++) {
    const r = Bun.spawnSync({ cmd: [ES, "-json", "-config", cfg, spec], cwd: EXAMPLES, stdout: "pipe", stderr: "pipe" });
    const ru: any = r.resourceUsage;
    cpu.push(Number(ru.cpuTime.total) / 1e6);
    rss.push(Number(ru.maxRSS) / (1 << 20));
    try {
      j = JSON.parse(r.stdout.toString().trim().split("\n").at(-1)!);
    } catch {
      j = { status: "unparsed" };
    }
  }
  const row = { model: cfg.split("/").at(-1)!.replace(".cfg", ""), status: j.status, distinct: j.distinct, generated: j.generated, cpuS: median(cpu), minCpuS: Math.min(...cpu), rssMb: Math.round(median(rss)), load: loadavg()[0] };
  rows.push(row);
  console.log(`${row.model.padEnd(22)} ${String(row.distinct).padStart(8)} ${String(row.generated).padStart(9)} ${row.cpuS.toFixed(2).padStart(7)}s (min ${row.minCpuS.toFixed(2)}) ${String(row.rssMb).padStart(5)} MB ${row.status}`);
}
if (values.json) writeFileSync(values.json, JSON.stringify({ at: new Date().toISOString(), everystate: ES, load: loadavg(), rows }, null, 1) + "\n");
