#!/usr/bin/env node
// Drop-in stand-in for the `java` binary when the only thing being run is the TLA+ tools
// (`java -cp tla2tools.jar tlc2.TLC ...`): point JAVA at this script, or put it on PATH as `java`.
import { runJavaShim } from './main.ts';
import { nodeHost } from './node-host.ts';
runJavaShim(process.argv.slice(2), nodeHost());
