import Hironaka.Geometry.NormalizationInExtension
import Hironaka.Geometry.FiniteBirationalNormalLiftGeneric
import Hironaka.Geometry.CurveFibrationBaseChange

/-! The actual finite-extension generic points on the actual normalized pullback. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationNormalizedGenericPoints

open NormalizationInExtension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} [IsIntegral S] (L : Type u) [Field L]
  [Algebra S.functionField L] [FiniteDimensional S.functionField L]

local notation "N" => normalization S L
local notation "π" => normalizationStructure S L

/-- The actual inverse of the constructed normalization field equivalence. -/
def genericFieldMap : Spec (N).functionField ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (normalizationFunctionFieldEquiv (X := S) L).symm.toRingHom)

/-- The WHOLE original coefficient/generic-point square uses the prescribed field inclusion. -/
theorem genericFieldMap_triangle :
    genericFieldMap (S := S) L ≫ Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
        S.fromSpecStalk (_root_.genericPoint S) =
      (N).fromSpecStalk (_root_.genericPoint N) ≫ π := by
  have hcoeff : (normalizationFunctionFieldEquiv (X := S) L).symm.toRingHom.comp
      (algebraMap S.functionField L) = (functionFieldMap π).hom := by
    ext a
    apply (normalizationFunctionFieldEquiv (X := S) L).injective
    change (normalizationFunctionFieldEquiv (X := S) L)
      ((normalizationFunctionFieldEquiv (X := S) L).symm
        (algebraMap S.functionField L a)) = _
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun (normalizationFunctionFieldEquiv_comp (X := S) L) a).symm
  have hcat : CommRingCat.ofHom (algebraMap S.functionField L) ≫
      CommRingCat.ofHom (normalizationFunctionFieldEquiv (X := S) L).symm.toRingHom =
        functionFieldMap π := CommRingCat.hom_ext hcoeff
  change Spec.map (CommRingCat.ofHom (normalizationFunctionFieldEquiv (X := S) L).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
      S.fromSpecStalk (_root_.genericPoint S) = _
  rw [← Spec.map_comp_assoc, hcat]
  exact FiniteBirationalNormal.functionFieldMap_fromSpecStalk π

variable {X : Scheme.{u}} (f : X ⟶ S) (a : Spec (.of L) ⟶ X)
  (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
    S.fromSpecStalk (_root_.genericPoint S))

/-- The SAME actual original generic L-point gives its actual normalized pullback generic point. -/
def genericPoint : Spec (N).functionField ⟶ pullback f π :=
  pullback.lift (genericFieldMap L ≫ a) ((N).fromSpecStalk (_root_.genericPoint N))
    (by rw [Category.assoc, ha]; exact genericFieldMap_triangle L)

/-- The ENTIRE original X projection is the SAME original generic L-point map. -/
theorem genericPoint_fst :
    genericPoint L f a ha ≫ pullback.fst f π = genericFieldMap L ≫ a :=
  pullback.lift_fst _ _ _

/-- The ENTIRE native normalized-base projection is its original generic-point morphism. -/
theorem genericPoint_snd :
    genericPoint L f a ha ≫ pullback.snd f π =
      (N).fromSpecStalk (_root_.genericPoint N) := pullback.lift_snd _ _ _

/-- The actual field point retains its EXACT original ambient X-image. -/
theorem genericPoint_original_image :
    pullback.fst f π (genericPoint L f a ha (IsLocalRing.closedPoint (N).functionField)) =
      a (IsLocalRing.closedPoint L) := by
  have H := congrArg (fun m : Spec (N).functionField ⟶ X => m (IsLocalRing.closedPoint (N).functionField))
    (genericPoint_fst L f a ha)
  change pullback.fst f π (genericPoint L f a ha _) =
    a (genericFieldMap L (IsLocalRing.closedPoint (N).functionField)) at H
  exact H.trans (congrArg a (Subsingleton.elim _ _))

/-- Distinct actual ORIGINAL images give distinct actual normalized pullback images. -/
theorem genericPoints_injective {ι : Type u} (as : ι → (Spec (.of L) ⟶ X))
    (has : ∀ i, as i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
      S.fromSpecStalk (_root_.genericPoint S))
    (hdist : Function.Injective (fun i => as i (IsLocalRing.closedPoint L))) :
    Function.Injective (fun i => genericPoint L f (as i) (has i)
      (IsLocalRing.closedPoint (N).functionField)) := by
  intro i j hij
  apply hdist
  have H := congrArg (pullback.fst f π) hij
  simpa only [genericPoint_original_image] using H

/-- Membership in the ORIGINAL ambient smooth locus gives actual pullback smoothness. -/
theorem genericPoint_mem_smoothLocus [LocallyOfFinitePresentation f]
    (hsm : a (IsLocalRing.closedPoint L) ∈ f.smoothLocus) :
    genericPoint L f a ha (IsLocalRing.closedPoint (N).functionField) ∈
      (pullback.snd f π).smoothLocus := by
  let U := (pullback.fst f π) ⁻¹ᵁ f.smoothLocus
  let : Smooth (U.ι ≫ pullback.snd f π) := CurveFibrationBaseChange.smooth_originalLocus f π
  have hz : genericPoint L f a ha (IsLocalRing.closedPoint (N).functionField) ∈ U := by
    change pullback.fst f π (genericPoint L f a ha _) ∈ f.smoothLocus
    rw [genericPoint_original_image]
    exact hsm
  have hs : (⟨_, hz⟩ : U) ∈ (U.ι ≫ pullback.snd f π).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hs

end Hironaka.Geometry.CurveFibrationNormalizedGenericPoints
