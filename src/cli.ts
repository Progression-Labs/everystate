#!/usr/bin/env node
import { runCli } from './main.ts';
import { runEntry } from './entry.ts';
runEntry(import.meta.url, runCli);
