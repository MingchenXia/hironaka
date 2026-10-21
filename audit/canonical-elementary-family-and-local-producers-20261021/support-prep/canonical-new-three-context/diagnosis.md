# Three new-parent context diagnosis

Read-only diagnosis: 3 modules, 4 complete declaration scopes, 5 differing actual proof roots. Every reported first difference was reproduced by following the paired original/native root DAGs in the frozen comparator traversal order. All selected full types match; there are no missing/extra owners or generated-name mismatches.

The ENat differences use the original IsOrderedRing-to-IsOrderedAddMonoid ancestor versus the copied LinearOrderedAddCommMonoidWithTop ancestor. The apparently different Complex ring leaves occur downstream of the established zero-class split: original SubsemiringClass.toAddSubmonoidClass versus copied AddSubgroupClass.toAddSubmonoidClass. They do not call for a new Complex ring instance.

Apply the already used theorem-local priority forms at these exact scopes:

- HomogeneousInitialTangentDerivatives.homogeneousComponent_mem_actual_initial_of_mem_power: IsOrderedRing.toIsOrderedAddMonoid.
- HomogeneousInitialTangentDerivatives.actual_homogeneous_initial_ideal_pderiv_of_first_symbol_closure: IsOrderedRing.toIsOrderedAddMonoid and SubsemiringClass.toAddSubmonoidClass, including generated _abel_1_5.
- InitialCoordinateQuotient private mem_power_actualInitialDegree: IsOrderedRing.toIsOrderedAddMonoid.
- TangentCutLayers.actualTangentCutLayerMap_tangentSymbol_zero: SubsemiringClass.toAddSubmonoidClass.

Exact source anchors, source fingerprints, original/native first nodes and paired ancestor paths are retained in the adjacent JSON reports. This is a context recipe, not a post-change acceptance result. Frontier owns production changes and the fresh public build/whole-expression replay. No Lean, original recapture, production source, frozen comparator or prior evidence was changed.
