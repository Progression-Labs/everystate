#!/usr/bin/env node
import { runCli } from './main.ts';
import { nodeHost } from './node-host.ts';
runCli(process.argv.slice(2), nodeHost());
