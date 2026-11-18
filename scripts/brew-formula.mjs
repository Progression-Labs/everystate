// Prints the Homebrew formula for a release.
// usage: node scripts/brew-formula.mjs <version> <dir with everystate-<platform>-<arch>.tar.gz>
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
const [version, dir] = process.argv.slice(2);
if (!version || !dir) { console.error('usage: node scripts/brew-formula.mjs <version> <dir>'); process.exit(1); }
const part = name => {
  const file = path.join(dir, `everystate-${name}.tar.gz`);
  const sha = crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex');
  return `      url "https://github.com/mattzcarey/everystate/releases/download/v${version}/everystate-${name}.tar.gz"\n      sha256 "${sha}"`;
};
process.stdout.write(`class Everystate < Formula
  desc "TLA+ model checker with a TLC-compatible command-line"
  homepage "https://github.com/mattzcarey/everystate"
  version "${version}"
  license "MIT"

  on_macos do
    on_arm do
${part('darwin-arm64')}
    end
    on_intel do
${part('darwin-x64')}
    end
  end

  on_linux do
    on_arm do
${part('linux-arm64')}
    end
    on_intel do
${part('linux-x64')}
    end
  end

  def install
    chmod 0755, "everystate"
    bin.install "everystate"
  end

  test do
    assert_match version.to_s, shell_output("#{bin}/everystate --version")
  end
end
`);
