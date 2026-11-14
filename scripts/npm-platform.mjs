// Creates the npm package that carries one prebuilt binary.
// usage: node scripts/npm-platform.mjs <platform> <arch> <path/to/binary> <outdir>
//   platform/arch use Node's names (linux, darwin, win32 / x64, arm64).
import fs from 'node:fs';
import path from 'node:path';
const [platform, arch, binary, outdir] = process.argv.slice(2);
if (!platform || !arch || !binary || !outdir) {
  console.error('usage: node scripts/npm-platform.mjs <platform> <arch> <binary> <outdir>');
  process.exit(1);
}
const root = JSON.parse(fs.readFileSync(path.resolve(import.meta.dirname, '../package.json'), 'utf8'));
const name = `everystate-${platform}-${arch}`;
if (root.optionalDependencies?.[name] !== root.version) {
  console.error(`${name}@${root.version} is not listed in optionalDependencies of package.json`);
  process.exit(1);
}
const exe = platform === 'win32' ? 'everystate.exe' : 'everystate';
fs.mkdirSync(path.join(outdir, 'bin'), { recursive: true });
fs.copyFileSync(binary, path.join(outdir, 'bin', exe));
fs.chmodSync(path.join(outdir, 'bin', exe), 0o755);
fs.copyFileSync(path.resolve(import.meta.dirname, '../LICENSE'), path.join(outdir, 'LICENSE'));
fs.writeFileSync(path.join(outdir, 'README.md'), `# ${name}\n\nPrebuilt ${platform}-${arch} binary for [everystate](https://www.npmjs.com/package/everystate). Install \`everystate\` instead of this package.\n`);
fs.writeFileSync(path.join(outdir, 'package.json'), JSON.stringify({
  name, version: root.version, description: `Prebuilt ${platform}-${arch} binary for everystate`,
  license: root.license, repository: root.repository, os: [platform], cpu: [arch], files: ['bin'],
}, null, 2) + '\n');
console.log(`${name}@${root.version} -> ${outdir}`);
