import Hironaka
open Lean
run_cmd do
  for n in #[``Hironaka.RemmertSteinFlat.remmertStein_flat_pure,
      ``Hironaka.RemmertSteinFlat.exists_badSet,
      ``Hironaka.RemmertSteinGeneral.nonempty_presentation_closure_of_regularAtDim,
      ``Hironaka.HironakaActualTaylorCoordinateNaturality.map_actualGerm_maximalIdeal_le_formal_coordinates] do
    let ci ← getConstInfo n
    for (field, e) in #[("type", ci.type), ("value", (ci.value? (allowOpaque := true)).getD ci.type)] do
      let used := e.getUsedConstants
      logInfo m!"{n} {field}: CSTAR={used.contains `instCommCStarAlgebraComplex}; FIELD={used.contains `Complex.instNormedField}; ADD_SUBMONOID={used.contains `SubsemiringClass.toAddSubmonoidClass}"
