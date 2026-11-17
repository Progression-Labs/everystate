// Copies the version in package.json to Cargo.toml and Cargo.lock (run after `changeset version`).
import fs from 'node:fs';
import path from 'node:path';
const root = path.resolve(import.meta.dirname, '..');
const { version } = JSON.parse(fs.readFileSync(path.join(root, 'package.json'), 'utf8'));
const edit = (file, re) => {
  const p = path.join(root, file), s = fs.readFileSync(p, 'utf8');
  if (!re.test(s)) { console.error(`${file}: version line not found`); process.exit(1); }
  fs.writeFileSync(p, s.replace(re, `$1${version}$2`));
};
edit('Cargo.toml', /(\[package\][^[]*?\nversion = ")[^"]*(")/);
edit('Cargo.lock', /(\[\[package\]\]\nname = "everystate"\nversion = ")[^"]*(")/);
console.log(`Cargo.toml and Cargo.lock -> ${version}`);
