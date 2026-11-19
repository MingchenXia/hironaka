import Hironaka.Geometry.CurveFibrationBaseChangeGenericIntegrality
import Hironaka.Geometry.CurveFibrationMarkedOpenSmooth

/-! Geometric integrality for the SAME proper smooth connected family over an arbitrary base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationSmoothIntegrality

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual field pullbacks of the SAME proper smooth geometrically connected family are integral. -/
theorem geometricallyIntegral_of_proper_smooth_connected {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f where
  geometrically_isIntegral := by
    intro K _ a Q i q h
    let : Smooth q := MorphismProperty.of_isPullback h inferInstance
    let : IsProper q := MorphismProperty.of_isPullback h inferInstance
    let : ConnectedSpace Q := GeometricallyConnected.geometrically_connectedSpace a i q h
    let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian q
    let : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace q
    let : AlgebraicGeometry.IsNoetherian Q := ⟨⟩
    exact CurveFibrationBaseChange.isIntegral_of_smooth_connected q

/-- Original generic smoothness and geometric connectedness produce actual SAME-family
dense-open smoothness and geometric integrality; no GI-openness assumption is used. -/
theorem exists_dense_smooth_integral_base_open {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    [Smooth (f.fiberToSpecResidueField (genericPoint S))] :
    ∃ (V : S.Opens) (_hη : genericPoint S ∈ V),
      Dense (V : Set S) ∧ f ⁻¹ᵁ V ≤ f.smoothLocus ∧
      IsProper (f ∣_ V) ∧ Smooth (f ∣_ V) ∧ Flat (f ∣_ V) ∧
      GeometricallyConnected (f ∣_ V) ∧ GeometricallyIntegral (f ∣_ V) := by
  obtain ⟨V, hnonempty, hdense, hV, hsmooth⟩ :=
    CurveFibrationMarkedOpen.exists_nonempty_dense_smooth_base_open f
  have hη : genericPoint S ∈ V :=
    (genericPoint_specializes (Classical.choice hnonempty).val).mem_open V.isOpen
      (Classical.choice hnonempty).property
  let : Smooth (f ∣_ V) := hsmooth
  let : GeometricallyConnected (f ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip inferInstance
  exact ⟨V, hη, hdense, hV, inferInstance, hsmooth, inferInstance, inferInstance,
    geometricallyIntegral_of_proper_smooth_connected (f ∣_ V)⟩

end Hironaka.Geometry.CurveFibrationSmoothIntegrality
