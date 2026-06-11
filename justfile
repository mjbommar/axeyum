# Canonical development commands. Run `just` to list.

default:
    @just --list

# Run every check CI runs (except cargo-deny, which needs the tool installed).
check: fmt clippy test doc links

fmt:
    cargo fmt --all --check

clippy:
    cargo clippy --workspace --all-targets --all-features -- -D warnings

test:
    cargo test --workspace --all-features

doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps

deny:
    cargo deny check

links:
    ./scripts/check-links.sh

# Repopulate gitignored reference clones.
references:
    ./scripts/fetch-references.sh

# Fetch public benchmark corpora into corpus/public/ (large downloads).
corpus:
    ./scripts/fetch-corpus.sh
