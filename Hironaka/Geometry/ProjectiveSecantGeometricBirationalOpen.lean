import Hironaka.Geometry.ProjectiveSecantGeometricComponentPoints
import Hironaka.Geometry.ProjectiveSecantProjectionComponentGeometry

/-!
# Genuine original birational projection centre open over an arbitrary separably closed coefficient field

All original smooth points and original general-position centre data are
internally produced from the original dense geometrically reduced open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveRationalPointCoordinates ProjectiveProjectionPoint

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original dense geometric open and original dimension internally construct an actual nonempty original centre open with native BR of the SAME original finite projection for EVERY original rational centre in it, without a smooth-point family or general-position certificate. -/
theorem exists_original_birational_center_open_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (U : X.Opens) (hU : Dense (U : Set X))
    [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k (n + 1)))]
    (hdim : topologicalKrullDim X < n) :
    ∃ O : (projectiveSpace k (n + 1)).Opens, (O : Set (projectiveSpace k (n + 1))).Nonempty ∧
      ∀ (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
        (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _), pointImage k n p ∈ O →
        ∃ hout : pointImage k n p ∉ Set.range i,
          IsFinite (projectionFromPoint k n p hp i hout) ∧
          projectionFromPoint k n p hp i hout ≫ projectiveSpaceStructure k n =
            i ≫ projectiveSpaceStructure k (n + 1) ∧
          Scheme.BirationalOver (projectionFromPoint k n p hp i hout).toImage
            (𝟙 (projectionFromPoint k n p hp i hout).image) := by
  let : IsNoetherian X := originalProjectiveSource_isNoetherian k (n + 1) i
  let : Finite (irreducibleComponents X) := finite_irreducibleComponents_of_isNoetherian
  choose s hsC _ hs hsx using (fun C : irreducibleComponents X =>
    exists_original_rational_smooth_component_point k (n + 1) i U hU C.1 C.2)
  have hcover : ∀ C ∈ irreducibleComponents X, ∃ a, s a (⊥ : PrimeSpectrum k) ∈ C := by
    intro C hC
    exact ⟨⟨C, hC⟩, hsC ⟨C, hC⟩⟩
  let O := smoothPointFamilyCenterOpen k n i s hs hsx hdim
  refine ⟨O, smoothPointFamilyCenterOpen_nonempty k n i s hs hsx hdim, ?_⟩
  intro p hp hc
  let hout := smoothPointFamilyCenterOpen_avoids_image k n i s hs hsx hdim hcover _ hc
  refine ⟨hout, projectionFromSmoothPointFamilyOpen_isFinite k n i s hs hsx hdim hcover p hp hc,
    projectionFromPoint_structure k n p hp i hout, ?_⟩
  exact projectionFromSmoothPointFamilyOpen_birational k n i s hs hsx hdim hcover p hp hc

end Hironaka.Geometry.ProjectiveSecant
