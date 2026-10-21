# OriginalGlobalOffZero first-DAG diagnosis

Read-only diagnosis of immutable attempt1, no source edit, Lean, exporter, kernel or comparator replay. There is one whole-value difference and no missing/extra root. The actual private declaration anchor is `private theorem offZeroEquiv_symm_contMDiff`; the relevant source expression is `(hs q.val hqV).comp q hval.contMDiffAt`.

The first existing DAG mismatch descends through ContMDiffAt.comp argument24, modelWithCornersSelf and PiLp.normedSpace to the component NormedSpace ℂ ℂ instance. Native uses NonUnitalCStarAlgebra.toNormedSpace via the nonunital commutative C-star algebra and commutative C-star algebra chain ending at instCommCStarAlgebraComplex. The copy uses InnerProductSpace.toNormedSpace through RCLike.innerProductSpace Complex.instRCLike. This is a genuine inferred instance-family divergence, not a hygiene-owner or numeric-name difference.

A narrowly theorem-local instance priority for NonUnitalCStarAlgebra.toNormedSpace is a candidate authentic original elaboration-context restoration; parent owns testing and exact capture validation. No instance priority, source theorem or proofbody was changed by this diagnosis. The full selected existing subtrees and immutable report/capture hashes are in the adjacent JSON.
