import Hironaka.Geometry.ProjectiveSecantGeneralTangentOpen
import Hironaka.Geometry.ProjectiveSecantProjectionGeneralFibreSupport
import Hironaka.Geometry.ProjectiveSecantProjectionUnramifiedStalk
import Hironaka.Geometry.ProjectiveSecantProjectionImageOpenIso

/-!
# Actual whole-source projection point data and native-image isomorphism opens
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates ProjectiveProjectionPoint

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
  (hdim : topologicalKrullDim X < n)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hc : pointImage k n p ∈ generalTangentSecantCenterOpen k n i s hs hx hdim)

/-- Actual original geometry internally supplies all local data of the same finite projection, without integral or reduced hypotheses. -/
theorem projectionFromGeneralTangentSecantOpen_point_data :
    let f := projectionFromGeneralFixedPointOpen k n (s ≫ i) hs i hdim p hp hc.2
    (∀ z : X, f z = f (s (⊥ : PrimeSpectrum k)) → z = s (⊥ : PrimeSpectrum k)) ∧
      (f.stalkMap (s (⊥ : PrimeSpectrum k))).hom.FormallyUnramified ∧
      IsIso (f.residueFieldMap (s (⊥ : PrimeSpectrum k))) := by
  refine ⟨fun z hz => projectionFromGeneralFixedPointOpen_fibre_eq_source
    k n i s hs hdim p hp hc.2 z hz, ?_, ?_⟩
  · exact projectionFromPoint_stalkMap_formallyUnramified k n i p hp s hs hdim.le hx
      (generalFixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hdim _ hc.2) hc.1
  · exact projectionFromPoint_residueFieldMap_isIso k n i p hp s hs
      (generalFixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hdim _ hc.2)

/-- The same original finite projection has an actual isomorphism neighbourhood in its entire actual native image, retaining all nilpotents. -/
theorem projectionFromGeneralTangentSecantOpen_native_image_open_isIso :
    let f := projectionFromGeneralFixedPointOpen k n (s ≫ i) hs i hdim p hp hc.2
    ∃ W : f.image.Opens, f.toImage (s (⊥ : PrimeSpectrum k)) ∈ W ∧ IsIso (f.toImage ∣_ W) := by
  let f := projectionFromGeneralFixedPointOpen k n (s ≫ i) hs i hdim p hp hc.2
  let : IsFinite f := projectionFromGeneralFixedPointOpen_isFinite k n (s ≫ i) hs i hdim p hp hc.2
  obtain ⟨hfibre, hfu, hres⟩ := projectionFromGeneralTangentSecantOpen_point_data k n i s hs hx hdim p hp hc
  let : IsIso (f.residueFieldMap (s (⊥ : PrimeSpectrum k))) := hres
  exact exists_native_image_target_open_isIso_of_finite_point_data f (s (⊥ : PrimeSpectrum k)) hfibre hfu

end Hironaka.Geometry.ProjectiveSecant
