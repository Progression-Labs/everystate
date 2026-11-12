#!/usr/bin/env node
// Drop-in stand-in for the `java` binary when the only thing being run is the TLA+ tools:
//   JAVA=verify-java  (or put it first on PATH as `java`)
import * as fs from 'node:fs';
import * as path from 'node:path';
import { runJavaShim } from './main.ts';
runJavaShim(process.argv.slice(2), { fs, path, stdout: s => process.stdout.write(s), exit: c => { process.exitCode = c; }, env: process.env });
