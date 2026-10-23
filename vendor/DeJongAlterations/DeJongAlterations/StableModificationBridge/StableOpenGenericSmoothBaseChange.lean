import DeJongAlterations.StableModification.Global.StableOpenReduce
import DeJongAlterations.StableModification.Global.Setup

/-! Actual generic fibres through flat field extension and SAME native component normalization. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenGenericSmoothBaseChange

open StableModification Global BlowDown.ClosureComponent
open Geometry.NormalizationGluing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Flat generalization and ORIGINAL component maximality give the ORIGINAL generic base point. -/
theorem map_genericPoint_of_flat {Y S : Scheme.{u}} [IsIntegral S]
    (p : Y ⟶ S) [Flat p] {v : Y} (hv : v ∈ genericPoints Y) :
    p v = genericPoint S := by
  obtain ⟨w, hwv, hw⟩ := Flat.generalizingMap p ((genericPoint_spec S).specializes (Set.mem_univ (p v)))
  have hle : closure ({v} : Set Y) ⊆ closure {w} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hwv)) isClosed_closure
  have heq : closure ({v} : Set Y) = closure {w} :=
    Set.Subset.antisymm hle (hv.2 isIrreducible_singleton.closure hle)
  have hvw : v = w := (inseparable_iff_closure_eq.mpr heq).eq
  simpa only [hvw] using hw

/-- The native normalization's actual generic point maps to the SAME original point v. -/
theorem normalization_genericPoint_image {Y : Scheme.{u}} (v : Y) :
    letI : IsIntegral (normalization (closureScheme v)) :=
      Geometry.NormalizationFinite.isIntegral_normalization
    (normalizationStructure (closureScheme v) ≫ closureι v)
      (genericPoint (normalization (closureScheme v))) = v := by
  let : IsIntegral (normalization (closureScheme v)) :=
    Geometry.NormalizationFinite.isIntegral_normalization
  have : IsDominant (normalizationStructure (closureScheme v)) :=
    Geometry.NormalizationFinite.normalizationStructure_isDominant
  have hgen : genericPoint (closureScheme v) = closurePt v := by
    apply (genericPoint_spec (closureScheme v)).eq
    rw [isGenericPoint_iff_specializes]
    exact fun x => ⟨fun _ => trivial, fun _ => closurePt_specializes v x⟩
  rw [Scheme.Hom.comp_apply, genericPoint_map_of_isDominant, hgen, closureι_closurePt]

/-- Native whole cartesian fibre square, without any open-generic-point assumption. -/
theorem smooth_generic_fibre_of_isPullback {X X' S T : Scheme.{u}}
    [IsIntegral S] [IsIntegral T] {f : X ⟶ S} {f' : X' ⟶ T}
    {u : X' ⟶ X} {p : T ⟶ S} (H : IsPullback u f' f p)
    (hsm : Smooth (f.fiberToSpecResidueField (genericPoint S)))
    (hη : p (genericPoint T) = genericPoint S) :
    Smooth (f'.fiberToSpecResidueField (genericPoint T)) := by
  rw [← hη] at hsm
  exact MorphismProperty.of_isPullback (P := @Smooth)
    (isPullback_fiberToSpecResidueField_of_isPullback H (genericPoint T)) hsm

/-- Original smooth generic fibre supplies EVERY actual component generic fibre after flat
base change, including when the base change is reducible or nonreduced. -/
theorem smooth_component_generic_fibre_of_flat_pullback {X S Y : Scheme.{u}}
    [IsIntegral S] (f : X ⟶ S) (p : Y ⟶ S) [Flat p]
    (hsm : Smooth (f.fiberToSpecResidueField (genericPoint S)))
    {v : Y} (hv : v ∈ genericPoints Y) :
    Smooth ((pullback.snd f p).fiberToSpecResidueField v) := by
  have hη := map_genericPoint_of_flat p hv
  rw [← hη] at hsm
  exact MorphismProperty.of_isPullback (P := @Smooth)
    (isPullback_fiber_pullback_snd f p v) hsm

end DeJongAlterations.StableModificationBridge.StableOpenGenericSmoothBaseChange
