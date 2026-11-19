# Hironaka exact build-cache workflow

This branch builds and publishes a Lean build cache for Hironaka source commit
`6ad4296663977a25e15cb476504f414f2aaf9e23`. The workflow runs when the branch is
updated. It stages assets in the draft release `build-cache-lean-4.33.1-6ad429666397`
and makes the release public after verifying the complete archive. [GitHub releases](https://github.com/MingchenXia/hironaka/releases)

The default runner is the ordinary disposable `ubuntu-24.04` runner. The workflow
removes fixed unused software directories only on a GitHub-hosted Linux runner,
then measures workspace capacity. No paid runner is required. Optional labels
can select an already available runner; no runner entitlement or machine is
created. On self-hosted runners the cleanup is skipped. They require x86_64 Linux,
Python 3.12+, git, curl, gh, zstd, tar, trusted CA roots and enough measured disk.

The default initial 36 GiB free-space guard is a configurable minimum, **not** a
claim that this source's cold build fits 36 GiB. The driver also measures space
before cache download, before supplemental batches, during every child command,
and before publishing. It stops with an incomplete receipt below its reserve.
The source's full build may need more disk or time than an ordinary hosted job
provides; this bundle has not run that production build. It keeps a 315-minute
build budget inside the 360-minute hosted-job limit. There is no silent
partial-cache success, automatic resume, or promised six-hour completion.

## Exact build and checks

Lean is selected from the checked-out `lean-toolchain`, downloaded from its exact
official HTTPS GitHub release and checked using the asset SHA-256 and size recorded in `lean-asset.json`,
and safely extracted. Missing asset digest metadata is a hard failure. TLS
verification stays enabled, redirects must stay HTTPS, and no `curl | sh` installer
or moving Lean version is used. `lake exe cache get` materializes the exact Git
revisions in the unchanged manifest and obtains their Mathlib cache. Its temporary
compressed downloads are isolated under `RUNNER_TEMP` and discarded by the exact
pinned Mathlib `cache clean!` command only after successful unpack.

The driver inventories and hashes **every physical** `Hironaka/**/*.lean` plus
`Hironaka.lean`, checks local import existence/cycles, and runs ordinary
`lake build`. It then requests supplemental `.olean` targets in
dependency order, at most 32 per invocation, and checks the entire physical
source/olean inventory. This is broader compilation coverage than merely
building the default umbrella. The published source's 8099-module static inventory
was read independently during preparation; counts are recomputed for every input.

The cache workflow uses three Lean threads and the source's warnings-as-errors
settings. The source CI runs the axiom and kernel checks from `main`.

After a compilation failure, the runner can save its project build files in
GitHub Actions cache storage. A retry can reuse those files with the same Lean
toolchain and locked dependencies. Lake checks the default build and every
supplemental target against the exact current source before packaging.

## Draft cache and trust

Only the final publishing step receives the repository's `GITHUB_TOKEN`
as `GH_TOKEN`; job permission is `contents: write`. The unchanged rolling publisher
obtains the clean source/dependency/Lean/platform identity and streams the exact
build roots through one zstd encoder and one bounded 256 MiB spool part. Each
immutable part is read back and hashed before local removal. The entire remote
tar/zstd stream is audited before any final manifest is exposed.

The draft-only GitHub adapter pins the numeric release ID, stages the manifest
under a SHA-named asset, verifies it, then renames it to `cache.json` using the
release asset API. Ambiguous mutation responses trigger actual-state readback
before retry. Existing different bytes are never clobbered. The manifest is
limited to 64 MiB, individual parts to 256 MiB, with bounded metadata/process outputs;
an exclusive draft writer is required: GitHub provides no atomic draft-state
compare-and-swap against another actor publishing the release. The final manifest is read back before publication. The workflow records the manifest SHA-256
in `publication-receipt.json` and the Actions summary. The workflow publishes the release after the final audit and records its public URL.

Receipts record every compiled module. The workflow retains logs and JSON receipts even on failure.
The public release includes the finalized manifest and every verified compressed part.

## Portable restore on a fresh clean checkout

The augmented rolling manifest retains version1 `identity` and `chunks`, so the
unchanged `cache_tools/vendor/cache.py` supports a true restore. Its implementation
has been exercised on tiny fixture bytes through this exact rolling Sink. Root
also verified a separate real Lean 4.33.1 fixture with a pinned Git dependency,
withdrew both original source repositories, and passed a downstream import,
kernel replay and an up-to-date no-build Lake replay after restoring. A complete
published Hironaka cache restore/rebuild on a fresh runner remains unverified.
Actual platform/libc, Lean/Lake/core binary hashes, source tree and every dependency
revision/clean state must match the manifest exactly. A different Ubuntu image
libc or rebuilt Lean executable can correctly cause identity rejection.

Prepare a clean checkout at the exact manifest source commit, install its exact
Lean archive with the included installer, then run `lake env true` inside that
checkout to materialize pinned dependencies without building project targets or
changing the tracked manifest. This exact bootstrap passed root's dependency
restore fixture. Do not use `lake update`. All manifest build roots must be absent;
the restore utility refuses existing destinations. Do not delete a live checkout's
build to force this precondition. On that fresh checkout, with `lean` on PATH:

```sh
# Explicit values from the verified Actions publication receipt:
export CACHE_REPO=MingchenXia/hironaka
export CACHE_TAG='build-cache-lean-4.33.1-6ad429666397'
export TRUSTED_MANIFEST_SHA256='THE_SHA256_FROM_THE_RELEASE_NOTES'
export CHECKOUT='/absolute/path/to/fresh/source'
export CACHE_DIRECTORY='/absolute/path/to/fresh/download'
export CHECK_DIRECTORY='/absolute/path/to/fresh/stream-audit'
(cd "$CHECKOUT" && lake env true)
mkdir "$CACHE_DIRECTORY" "$CHECK_DIRECTORY"
gh release download "$CACHE_TAG" --repo "$CACHE_REPO" --pattern cache.json --dir "$CACHE_DIRECTORY"
gh release download "$CACHE_TAG" --repo "$CACHE_REPO" --pattern 'cache-*.tar.zst.part' --dir "$CACHE_DIRECTORY"
python3 cache_tools/rolling_cache.py verify-mock \
  --sink "$CACHE_DIRECTORY" --manifest-sha256 "$TRUSTED_MANIFEST_SHA256" --scratch "$CHECK_DIRECTORY"
python3 cache_tools/vendor/cache.py restore "$CACHE_DIRECTORY" \
  --project "$CHECKOUT" --lean "$(command -v lean)"
cd "$CHECKOUT"
lake build
lake env lean scripts/CheckAxioms.lean
lake env leanchecker Hironaka
```

`verify-mock` is the historical CLI name for a local downloaded-cache verifier;
it verifies the real downloaded manifest, all compressed parts and every tar
member, without extraction. Restore streams the parts directly into extraction
without a second concatenated archive, but still requires capacity for the
downloaded compressed cache plus the full expanded build. ## Local validation without GitHub calls

From this bundle directory, with Python, PyYAML and zstd installed:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -W error::ResourceWarning -m unittest discover -s tests -v
PYTHONDONTWRITEBYTECODE=1 python3 -W error::ResourceWarning -m unittest discover -s cache_tools -p test_rolling_cache.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -W error::ResourceWarning -m unittest discover -s cache_tools/github_release_adapter -p test_github_release_sink.py -v
bash -n scripts/recover-disk.sh
```

All `gh` invocations in these tests use an explicit fake executable or in-memory
client. They do not call the actual GitHub service. Fixture Lean/Lake objects are
marked dummy bytes; tests make no production proof or runner-capacity claim.
