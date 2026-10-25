# Fixed14 integration with the de Jong main

This is a source-only reconciliation on standalone main
`6e0ec1b397026973570a44769abc1084b938bffd` of the fixed14 branch
`668ccdac96b962a30f2f12fff2b3f4fbda20ef75`, with common base `dfce539`.
The isolated worktree is `/workspace/hironaka-phase5-main-integration`.
The original `/workspace/hironaka` branch and all historical audit receipts
are unchanged. No commit, push, remote merge or PR merge has been performed.

- All 373 nonoverlapping changed paths are exact fixed14 Git blobs: 17 Lean
  files (14 whole producers and three original support extracts), 14 whole
  Blueprint chapters, and their original evidence.
- The umbrella and Blueprint master merge disjoint original import/input
  hunks. The existing de Jong import, chapter and bibliography remain.
- STATUS keeps the de Jong text and distinguishes the four-goal standalone
  export from the later five-goal native checkpoint546, which is not exported.
  The fixed14 build counts are explicitly historical.
- Main's README (61 lines), public API, Lake/CI/test configuration, root
  license and the entire de Jong vendor, including contributor headers,
  are preserved. Historical audits excluded by sparse checkout remain in
  Git; they are not deleted from the integration index.

Reproduce the source-only checks without Lean or network access:

```sh
python3 audit/phase5-main-integration-20261025/prepare_integration.py --check
python3 scripts/check_dejong_source.py
```

`mechanical-source-verification.json` binds the exact inputs and the three
explicit merges. It claims no combined-build success. The fixed14 and de Jong
receipts validate their respective historical graphs; neither is relabeled as
validation of this combined graph. No old kernel or full-expression replay is
needed for this mechanical reconciliation.

The combined build is **pending** the separately coordinated private-cache
recipe. At the initial source-only freeze no build/cache directory existed.
The later [cache preflight](cache-preflight/README.md) records the independent
artifact copy, failed unchanged sentinel and successful external-cache check;
no actual compiler has run yet. Shared package artifacts are consumers only,
and the original standalone cache remains untouched. Root owns subsequent
review, commits and publication.
