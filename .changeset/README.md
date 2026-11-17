# Changesets

Every pull request that should reach users adds a file here: run `npx changeset`, pick
patch / minor / major and write one line for the changelog.

When such a pull request lands on `main`, a "Version Packages" pull request is opened (or updated).
Merging that one bumps `package.json`, `Cargo.toml` and `CHANGELOG.md`, and the Release workflow
then publishes to npm and crates.io.
