# De Jong alterations: vendored proof package

This package contains the complete source import closure of the unconditional
alteration theorem over every field. The 1,112 upstream Lean modules retain
their original bytes, namespaces and author/license headers. The package root
imports only the final endpoint. [SOURCE.json](SOURCE.json) records every source
path, Git blob and SHA-256 at the original source revision.

The proof source is included here so that building the public Hironaka repository
does not require access to its original private development repository. Its only
package dependency is the same pinned Mathlib as Hironaka. Build from the main
repository root with `lake build`.

Use `import Hironaka.DeJong` for the public Hironaka entry points, or
`import DeJongAlterations` for the native statement and theorem. See
[the integration guide](../../docs/DEJONG.md) for the full geometric output,
public APIs, source attribution and verification commands.
