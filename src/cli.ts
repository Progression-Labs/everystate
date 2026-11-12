#!/usr/bin/env node
import * as fs from 'node:fs';
import * as path from 'node:path';
import { runCli } from './main.ts';
runCli(process.argv.slice(2), { fs, path, stdout: s => process.stdout.write(s), exit: c => process.exit(c) });
