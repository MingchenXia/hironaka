import Hironaka.Geometry.ProjectiveSecantProjectionResidueField
import Hironaka.Geometry.ProjectiveSecantProjectionUnramifiedStalk
import Hironaka.Geometry.ProjectiveSecantProjectionFibreSupport
import Hironaka.Geometry.ProjectiveCompactification

/-!
# Native actual integral image of the SAME original finite projective projection

This produces its actual local data internally from original geometry.
The remaining native Nakayama neighbourhood-isomorphism step is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionPoint ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native image factor of the SAME original finite map is finite; no image-map finiteness is supplied. -/
theorem toImage_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] : IsFinite f.toImage := by
  let : IsFinite (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  exact IsFinite.of_comp f.toImage f.imageι

/-- Original actual stalk unramifiedness passes to the SAME map's literal actual image factor by native restriction of scalars. -/
theorem toImage_stalkMap_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : (f.stalkMap x).hom.FormallyUnramified) :
    (f.toImage.stalkMap x).hom.FormallyUnramified := by
  have hc0 : ((f.toImage ≫ f.imageι).stalkMap x).hom.FormallyUnramified := by
    rw [Scheme.Hom.stalkMap_congr_hom _ _ f.toImage_imageι x]
    exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso _ (f.stalkMap x)).mpr h
  have hc : (f.imageι.stalkMap (f.toImage x) ≫ f.toImage.stalkMap x).hom.FormallyUnramified := by
    simpa only [Scheme.Hom.stalkMap_comp] using hc0
  exact RingHom.FormallyUnramified.of_comp hc

/-- The literal original rational-point coefficient triangle internally gives the original actual image-factor residue-field isomorphism. -/
theorem toImage_residueFieldMap_isIso_at_rational_point
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of k)) (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ f) ≫ g = 𝟙 _) :
    IsIso (f.toImage.residueFieldMap (s (⊥ : PrimeSpectrum k))) := by
  apply residueFieldMap_isIso_at_rational_point f.toImage (f.imageι ≫ g) s
  rw [Category.assoc, ← Category.assoc f.toImage, f.toImage_imageι, ← Category.assoc, hs]

/-- Actual original integral projective geometry and actual rational centre in the computed tangent-secant open produce finite dominant integral-image geometry, SAME-point native stalk unramifiedness, actual residue-field isomorphism and exact actual singleton fibre for the SAME original native image factor. No local-image or one-point-fibre certificate is supplied. -/
theorem originalProjection_toImage_local_data
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hsmall : topologicalKrullDim X < n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ tangentSecantCenterOpen k n i s hs hx hsmall) :
    let f := projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2
    IsFinite f.toImage ∧ IsDominant f.toImage ∧ IsIntegral f.image ∧
      (f.toImage.stalkMap (s (⊥ : PrimeSpectrum k))).hom.FormallyUnramified ∧
      IsIso (f.toImage.residueFieldMap (s (⊥ : PrimeSpectrum k))) ∧
      f.toImage ⁻¹' {f.toImage (s (⊥ : PrimeSpectrum k))} = {s (⊥ : PrimeSpectrum k)} := by
  let f := projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2
  let : IsFinite f := projectionFromFixedPointOpen_isFinite k n (s ≫ i) hs i hsmall p hp hc.2
  have hsf : (s ≫ f) ≫ projectiveSpaceStructure k n = 𝟙 _ := by
    rw [Category.assoc, projectionFromFixedPointOpen_structure, ← Category.assoc, hs]
  refine ⟨toImage_isFinite f, inferInstance, ProjectiveCompactification.image_isIntegral f, ?_,
    toImage_residueFieldMap_isIso_at_rational_point f (projectiveSpaceStructure k n) s hsf, ?_⟩
  · apply toImage_stalkMap_formallyUnramified
    exact projectionFromPoint_stalkMap_formallyUnramified k n i p hp s hs hsmall.le hx
      (fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hsmall _ hc.2) hc.1
  · ext x
    constructor
    · intro h
      have he := congrArg (fun y => f.imageι y) (Set.mem_singleton_iff.mp h)
      change (f.toImage ≫ f.imageι) x = (f.toImage ≫ f.imageι) (s (⊥ : PrimeSpectrum k)) at he
      rw [f.toImage_imageι] at he
      exact projectionFromFixedPointOpen_fibre_eq_source k n i s hs hsmall p hp hc.2 x he
    · intro h
      rw [Set.mem_singleton_iff.mp h]
      rfl

end Hironaka.Geometry.ProjectiveSecant
