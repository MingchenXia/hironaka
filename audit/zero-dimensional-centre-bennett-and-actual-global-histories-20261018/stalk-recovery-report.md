# Stalk source recovery

Recovered four complete published original parents and three complete original AmbientHS declarations from normal revision `bae7068afc70d624cd8563fd4291436195a7f25f`. Mathematical proof tokens are unchanged. Frozen relocation was loaded directly from `audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py`.

- Whole parents: `HironakaActualWholeStalkHolomorphicPullback` (10 explicit declarations), `HironakaActualBiholomorphicWholeStalkHS` (8), `HironakaActualOpenIntrinsicHS` (6), `HironakaActualBlowupOffCentreIntrinsicHS` (5).
- Support: `GenuineAmbientJetAlgEquivExact`, original contiguous AmbientHS source lines 21–48, retaining both section instance variables and all three complete declarations.
- Sole whole-parent adjustment: replace the absent original AmbientHS module import in BiholomorphicWholeStalkHS by the exact support module.
- Whole AmbientHS recovery would reach existing canonical declarations in `RealDomainOriginDictionaryExact` and `RealDomainLocalCoherenceExact`; this support avoids those duplicate definitions.

Validation: support narrow `lake env lean` passed with empty output. One bounded `LEAN_NUM_THREADS=1 timeout 180s lake build --wfail Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS` passed, all five owned modules built, 4277 jobs, no warnings. No failed-source or context-repair iteration was needed. LSP tools were unavailable; the authorized fallback and final build were used. Exact pinned-source byte replay passed for all five outputs.

Provenance is in `stalk-whole-source-provenance.json`, `stalk-support-provenance.json`, and `stalk-recovery-receipt.json`; the original bytes are retained in `stalk-*-original.lean.txt` files. Compiler `.ilean` source ranges and hashes are recorded per complete declaration; `whole_proof_source_envelope_sha256` hashes the full original declaration including its entire proof.

Claim class: imported boundary, now checked as complete original source. Consumer: the major395 stalk/germ/HS dependencies named in the parent's missing-constant audit. Strict ALL expression comparison and independent root review remain in the parent lane. No source theorem, axiom audit or publication-completion claim is made here. Honesty reviewer: skipped because this worker performs fixed-source recovery only; parent owns independent review.

No existing public mathematical module, global root, map, README, native source, or repository state was edited. No network request, AST export, heavy serialization, or axiom audit ran in this lane.
