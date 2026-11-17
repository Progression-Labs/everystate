// The PlusCal translator through the WebAssembly API. The expected translation was produced by the
// Java translator (pcal.trans 1.12 of tla2tools); scripts/pcal-corpus.mjs compares the two at scale.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { check, translatePlusCal } from '../wasm/everystate.mjs';

const TRANSFER = `---- MODULE Transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice = 10, bob = 10, money \\in 1..20;
begin
  Withdraw: alice := alice - money;
  Deposit:  bob := bob + money;
  Check:    assert alice >= 0;
end algorithm *)
====
`;

const TRANSLATED = `---- MODULE Transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice = 10, bob = 10, money \\in 1..20;
begin
  Withdraw: alice := alice - money;
  Deposit:  bob := bob + money;
  Check:    assert alice >= 0;
end algorithm *)
\\* BEGIN TRANSLATION (chksum(pcal) = "b9bac7e3" /\\ chksum(tla) = "f745b8df")
VARIABLES pc, alice, bob, money

vars == << pc, alice, bob, money >>

Init == (* Global variables *)
        /\\ alice = 10
        /\\ bob = 10
        /\\ money \\in 1..20
        /\\ pc = "Withdraw"

Withdraw == /\\ pc = "Withdraw"
            /\\ alice' = alice - money
            /\\ pc' = "Deposit"
            /\\ UNCHANGED << bob, money >>

Deposit == /\\ pc = "Deposit"
           /\\ bob' = bob + money
           /\\ pc' = "Check"
           /\\ UNCHANGED << alice, money >>

Check == /\\ pc = "Check"
         /\\ Assert(alice >= 0, "Failure of assertion at line 9, column 13.")
         /\\ pc' = "Done"
         /\\ UNCHANGED << alice, bob, money >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\\ UNCHANGED vars

Next == Withdraw \\/ Deposit \\/ Check
           \\/ Terminating

Spec == Init /\\ [][Next]_vars

Termination == <>(pc = "Done")

\\* END TRANSLATION${" "}
====
`;

test('translatePlusCal: the translation and its checksums are those of the Java translator', () => {
  const r = translatePlusCal(TRANSFER);
  assert.deepEqual(r.errors, []);
  assert.equal(r.output, TRANSLATED);
  assert.deepEqual(r.messages, ['Parsing completed.', 'Translation completed.']);
});

test('translatePlusCal: translating again replaces the old translation with the same text', () => {
  assert.equal(translatePlusCal(TRANSLATED).output, TRANSLATED);
  const edited = TRANSLATED.replace("/\\ alice' = alice - money", "/\\ alice' = 0");
  assert.equal(translatePlusCal(edited).output, TRANSLATED);
});

test('translatePlusCal: the translation can be model-checked (the assertion fails when money > alice)', () => {
  const { output } = translatePlusCal(TRANSFER);
  const { result } = check({ root: 'Transfer', modules: { Transfer: output! }, config: 'SPECIFICATION Spec' });
  assert.equal(result.status, 'error');
  assert.match(result.message!, /Failure of assertion at line 9, column 13/);
  assert.deepEqual(result.trace!.map(t => t.action?.name ?? 'Init'), ['Init', 'Withdraw', 'Deposit']);
  const fixed = translatePlusCal(TRANSFER.replace('1..20', '1..10'));
  const ok = check({ root: 'Transfer', modules: { Transfer: fixed.output! }, config: 'SPECIFICATION Spec\nPROPERTY Termination' });
  assert.equal(ok.result.status, 'liveness'); // no fairness: the algorithm may stutter forever
});

test('translatePlusCal: options as command-line flags or as an object', () => {
  const a = translatePlusCal(TRANSFER.replace('1..20', '1..10'), ['-wf', '-termination']);
  const b = translatePlusCal(TRANSFER.replace('1..20', '1..10'), { fairness: 'wf', termination: true });
  assert.equal(a.output, b.output);
  assert.match(a.output!, /Spec == \/\\ Init \/\\ \[\]\[Next\]_vars\n {8}\/\\ WF_vars\(Next\)/);
  const ok = check({ root: 'Transfer', modules: { Transfer: a.output! }, config: 'SPECIFICATION Spec\nPROPERTY Termination' });
  assert.equal(ok.result.status, 'ok');
  assert.deepEqual([ok.result.generated, ok.result.distinct], [50, 40]);
  // labels are added on request (a second assignment to alice must start a new step)
  const unlabeled = TRANSFER.replace('Deposit:  bob := bob + money;', '          alice := alice + money;');
  assert.equal(translatePlusCal(unlabeled).errors[0], 'Missing label at the following location:\n     line 8, column 13');
  assert.equal(translatePlusCal(unlabeled, { label: true }).errors.length, 0);
  assert.match(translatePlusCal(unlabeled, { label: true, labelRoot: 'Step' }).output!, /Withdraw == [^]*Step1 == /);
});

test('translatePlusCal: errors carry the position in the module', () => {
  const r = translatePlusCal(TRANSFER.replace('alice := alice - money;', 'alice := alice - money'));
  assert.equal(r.output, null);
  assert.deepEqual(r.errors, ['Expected ";" but found ":="\n    line 8, column 17']);
  assert.deepEqual(translatePlusCal('---- MODULE M ----\n====\n').errors, ['Beginning of algorithm string --algorithm not found.']);
  assert.match(translatePlusCal(TRANSFER, ['-frobnicate']).errors[0], /Unknown command-line option: -frobnicate/);
});
