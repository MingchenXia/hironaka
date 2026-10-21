# PointOrderRetainingHS: exact ENat instance ancestry

The two mathematical raw differences are genuine class-instance selection
differences in the proofs. Both full theorem types are exact. The original
`attempt1` exports and `BLOCKED_EXACT_DIFFERENCE` report remain byte-identical.
The separate notation-frontend differences in that report remain untouched.

| Complete declaration | First original/public differing nodes | Ordered-additive ancestor roots |
|---|---|---|
| `actualHomogeneousInitialIdeal_eq_reduced_component_span` | 1526 / 1514 | 1527 / 1521 |
| private `reduced_component_member_span` | 3148 / 3137 | 3149 / 3143 |

In each case the first differing raw constant is original
`instIsOrderedRingENat` versus public
`instLinearOrderedAddCommMonoidWithTopENat`. Their complete application ancestry
is `Nat.cast_lt._simp_1` → `IsOrderedAddMonoid.toAddLeftMono` → original
`IsOrderedRing.toIsOrderedAddMonoid`, whereas the public proof uses
`LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid` at that last step.
The full exact child paths, binder/let ancestry, raw nodes and both complete
instance sub-DAGs are in `paired-first-dag-context-proposal.json`.

The private result differs inside the `¬ weight ≤ q` branch, under `Q`, `ha`,
`hG` and `hprod`, at `by exact_mod_cast Nat.lt_succ_self q` (native line 83).
The public result differs under the original member `F`, `α`, `hα` and `ho`,
at the `exact_mod_cast` for the original initial degree (native line 100).
These are the unchanged casts of natural strict inequalities into ENat.

The pinned native/public Mathlib source bytes agree. ENat's original deriving
block provides both genuine instances; `IsOrderedRing` extends
`IsOrderedAddMonoid`. No replacement instance, theorem, cast or owner alias is
needed. The raw native proof establishes the intended ancestor selection; it
does not imply that the native source contained an explicit priority command.
The exact import/environment event that changes tie-breaking is not asserted.

The context-only remedy is the established declaration-local command
`attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in`
on each of the two entire declarations above. No statement or proof token is
changed. A candidate with exactly these two insertions is saved separately;
while this diagnostic was being written, the production owner applied the
same authorized commands. Its observed source is exactly that candidate.

This is a structural diagnosis and context proposal, not a fresh expression
PASS. Frontier owns the build and unchanged complete-parent replay. No Lean,
kernel, Expr runtime, production source, Git state, DAG field, proof number,
binder name, normalization rule or prior raw evidence was changed by this lane.
