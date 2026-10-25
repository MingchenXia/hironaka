# Cache and cold-build preflight

The isolated worktree has independently copied artifacts for 1,558 modules
whose standalone source bytes match. The copy is 1,119,846,361 bytes and includes
the original `lib/lean` artifacts plus matching `.c` and `.c.hash` files. No
`.setup.json`, hardlink or writer-output symlink was copied. The changed umbrella
and test module, and the two absent deferred sources, were excluded.

The unchanged HolomorphicGermRing `--no-build` sentinel **failed** with exit 3:
the module is out of date. Its old trace has `autoImplicit=false`; newer main
also sets `warningAsError=true`. Main's configuration and the original traces
remain unchanged. The separate non-buildable `depTrace` query succeeded but
serialized `null`, so it is not claimed as a captured current trace. No stale
artifact is relabeled fresh.

The complete external-import cache preflight **passed**: 730 shared package
targets plus one toolchain import, 4,656 warm jobs and zero compiler work under
`--no-build`. All 130,495 shared package/config metadata entries are unchanged.
This is command-policy/snapshot protection, not an OS read-only mount.

The actual de Jong root has 1,112 proof modules plus its generated narrow root,
all cold here. Its exact dependency order has depth 52 and 279 batches of at most
four targets. The minimal root target is `+DeJongAlterations:olean`; a whole
library glob is unnecessary. The whole combined source closure has 2,673 modules
before the separate test module. The main option change means old Hironaka
artifacts may also need genuine recompilation. This is a library build, not an
old kernel or expression replay.

Root authorizes a genuine build only after the native baseline's durable
`work/g1-g9-20261025-phase7/main-runtime/BASELINE-COMPLETE.json` has status PASS.
`build_bounded_batches.py` checks that marker and the external-cache gate, holds
the shared global `lean-build.lock` for at most four targets, then releases it
and yields to native mathematical writers. Each batch retains full logs, exit,
source/config pins, elapsed time and warnings. After all own compiler children
are reaped, only newly generated successful private-cache `.setup.json` files
may be hashed, recorded and removed. Shared/old artifacts, `.c` and `.trace`
files are never removed. The disk floor is 2 GiB, checked before each batch and
after completing it; lower free space pauses subsequent work.

With setup JSON removed at successful batch boundaries, expected additional
steady storage is primarily the vendor's new olean/ilean/C output: allow up to
2 GiB until a pilot measures it, plus small per-batch temporary setup files and
logs. No truthful fixed cold-runtime estimate is available before that pilot.
The initial source-only 88 MiB reconciliation and copied 1.12 GB cache are
already included in the current disk usage. The first pilot must report measured
growth/time before extrapolating. Existing de Jong warnings remain recorded;
they must not be suppressed by changing proof sources.

At this checkpoint, no actual compiler, old kernel/Expr replay, commit, push or
remote merge has run. The baseline marker is still pending. All cache-preflight
subprocesses have ended and been reaped.
