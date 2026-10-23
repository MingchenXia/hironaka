# De Jong integration verification

[validation.json](validation.json) records the current check status and exact
source inventory. The proof sources are vendored from the recorded revision,
with all 1,112 original module bytes preserved. Public entry points live in
`Hironaka.DeJong` and are imported by `Hironaka`.

Reproduce the checks from the repository root:

```sh
python3 scripts/check_dejong_source.py
lake build
lake test
LEAN_NUM_THREADS=1 lake env leanchecker -v Hironaka.DeJong DeJongAlterations.StableModificationBridge.AlterationUnconditional
```

The recursive axiom test includes every Hironaka and DeJongAlterations module
owner, including private/generated declarations and native-namespace extensions.
The explicit kernel replays target the new public module and final native
endpoint. The original source bytes and headers, including three historical
blank-at-EOF source files and one `.gitignore` blank, are preserved; whitespace
checks are strict for the authored integration files.

Hironaka package warnings are errors through its own Lake options. The vendored
package retains its original options and 55 visible upstream linter warnings.
No warnings are suppressed. GitHub Actions are skipped by user instruction.
