# Fixed14 and de Jong combined verification

The actual combined build and test passed. See [the concise final report](final-report.md) and [the bound verification receipt](publication-verification.json). The repository's main README remains byte-identical at 61 lines.

The [initial preparation README](audit-readme-before-final.md), source-only receipts, failed unchanged-cache sentinel, every batch log and historical mathematical audits remain as recorded. Their pending or failed statuses are not rewritten.

After completing the recorded batches, reproduce the final byte/source bookkeeping without compiler, kernel, expression, frontend or network replay:

```sh
python3 audit/phase5-main-integration-20261025/assemble_final_verification.py --check
```

Commit, push and merge are handled separately by the root publication lane.
