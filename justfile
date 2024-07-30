set positional-arguments
alias t := test

# default recipe to display help information
default:
  @just --list

# Test for the native target with all features
test *args='':
  cargo nextest run --workspace --all --release $@

# Lint the workspace for all available targets
lint: clippy lint-docs

# Fixes the formatting of the workspace
fmt-fix:
  cargo +nightly fmt --all

# Check the formatting of the workspace
fmt-check:
  cargo +nightly fmt --all -- --check

# Run clippy on the workspace
clippy: fmt-check
  cargo +nightly clippy --workspace --all --all-features --all-targets -- -D warnings

# Lint the Rust documentation
lint-docs:
  RUSTDOCFLAGS="-D warnings" cargo doc --all --no-deps --document-private-items 

# Run benchmarks for the workspace
bench:
  cargo bench --workspace --all-features --all-targets
