# Two missing MemberInterTowerAlong declarations: draft only

`MemberInterTowerAlongOriginalExact.lean` copies the complete original `mem_strictAlong_inter_memberInter_self` (including `open Classical in`, documentation, statement and proof; native lines267–276) and `centresIn_restrict_of_centresIn_union` (documentation, whole recursive statement/proof; lines298–312). The whole native source is captured and checked against ordinary published revision4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07. Only namespace roots are relocated.

The original options, universe, shared open/scoped namespaces, outer `n`, Tower's explicit marked-ideal variable, and Localise's own base variable/opens are retained. `end Tower`, `end Localise`, the bare `end` closing the anonymous noncomputable section, and the final namespace `end` are independently stack-checked. There are no active `include`, `omit`, or local attribute commands to lose; the local Classical scope is explicitly retained.

The draft purely imports the existing old MemberInterTowerAlong and MemberStrictPartitionExact. The latter already owns the genuinely available `strictAlong_union` needed by the recursive proof; its frozen old source and actual captured base name are verified. No third theorem is duplicated.

Both complete written blueprint proofs already occur in retained OLD `blueprint/blowup-calculus.tex`: `bcalc:member-intersection-tower` and `bcalc:centres-localise`. Exact original and retained complete nodes are captured. Their whole statements and written proofs are identical after removing only documentation binding/status commands. Old upstream annotations are not edited. Neither label belongs to the seven proposed new external anchors, and neither requires a duplicate local node or anchor to cover these two proofs.

This is static extraction evidence, not compilation, kernel or compatibility approval. No production source, old source/chapter, Git state, Lean process, exporter or strict comparator was touched. Root owns the peer; frontier owns any eventual installation and gates.
