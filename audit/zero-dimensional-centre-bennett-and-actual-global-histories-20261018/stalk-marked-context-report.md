# Original marked-tower section context recovery

The extracted transport support omitted the exact original command `variable {Y Z : CMfd.{u} n}` from published native `MarkedIdealTowerTransport.lean` line 190, byte range 9949–9977. The original Transport section declares these variables before both `length_transport` and `proj_transport`; the former theorem signature shadows `Y`, but the original unused section context still exists during elaboration. The separate Invariance section closes at line 150 and contributes no active local variables here.

Restored only that original command after the retained X/Xprime/Phi variable declaration in the new support. Added the same literal command to the fragment recovery recipe. The recovery generator was not run; the parent owns its combined support provenance and any separate declaration-local typeclass restoration.

Support SHA-256 before: `c101f5c59f4b2c45396a804eab684ef7ac3f1a79d8c1baaa0611b3ab6b444a3f`. After: `e4fa08de58d98fe0c3af9e8284fb2bf6aff004fc5b2fa6306ff1afc7b35a212c`. Original parent SHA-256: `22d4855929089c490291eb3984e3f8ea9f0eb432e88493eeff334bcbacc89251`. Original context-command SHA-256: `f5d6e79bc1c9068e7bd34d139aaa081df4756c963ca96857729924b07d2bda23`.

Both complete original declaration sidecars occur exactly once and byte-identically before and after. No statement, proof, explicit binder name, numerical hygiene component, serializer or canonicalizer was edited. The prior strict comparison snapshot and all original-source byte contexts are retained in `stalk-marked-context-recovery.json` and its three `.lean.txt` sidecars.

Validation: source-only checks passed. No Lean, build, export, Git or network action ran. The missing original command is consistent with the observed uniform numeral difference of four; exact generated-name alignment remains pending the parent serial compiler/capture check. Claim class: recovered original elaboration context, not a new mathematical proof or a claimed successful strict comparison.
