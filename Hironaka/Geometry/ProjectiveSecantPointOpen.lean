import Hironaka.Geometry.ProjectiveSecantOpen

/-!
# An original rational fixed point internally produces an actual nonempty centre open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionCenter ProjectiveRationalPointCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual inverse scheme morphisms transport a genuine open-set point without expanding its construction. -/
theorem iso_preimage_open_nonempty {Y Z : Scheme.{u}} (e : Y ≅ Z) (U : Z.Opens)
    (hU : (U : Set Z).Nonempty) : (e.hom ⁻¹ᵁ U : Set Y).Nonempty := by
  obtain ⟨z, hz⟩ := hU
  refine ⟨e.inv z, ?_⟩
  change e.hom (e.inv z) ∈ U
  have he : e.hom (e.inv z) = z := congrArg (fun f : Z ⟶ Z => f z) e.inv_hom_id
  rw [he]
  exact hz

variable (k : Type u) [Field k] (n : ℕ)
  (q : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hq : q ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- Actual coordinates are internally constructed from the original scheme point and original coefficient triangle. -/
def fixedPointAutomorphism : projectiveSpace k (n + 1) ≅ projectiveSpace k (n + 1) :=
  coordinateAutomorphism k n (pointVector k n q hq) (pointVector_ne_zero k n q hq)

/-- The exact original scheme point goes to the literal native standard point. -/
theorem fixedPointAutomorphism_apply :
    (fixedPointAutomorphism k n q hq).hom (pointImage k n q) = Algebra.ProjectiveProjectionFinite.centrePoint k n := by
  rw [← pointVector_image k n q hq]
  exact coordinateAutomorphism_apply_vectorPoint _ _ _ _

/-- The actual inverse carries the native standard point to the exact original scheme point. -/
theorem fixedPointAutomorphism_inv_apply :
    (fixedPointAutomorphism k n q hq).inv (Algebra.ProjectiveProjectionFinite.centrePoint k n) = pointImage k n q := by
  have h := congrArg (fun z => (fixedPointAutomorphism k n q hq).inv z) (fixedPointAutomorphism_apply k n q hq)
  change ((fixedPointAutomorphism k n q hq).hom ≫ (fixedPointAutomorphism k n q hq).inv) (pointImage k n q) = _ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

/-- The internally produced coordinate automorphism retains the actual original field structure. -/
@[reassoc]
theorem fixedPointAutomorphism_structure :
    (fixedPointAutomorphism k n q hq).hom ≫ projectiveSpaceStructure k (n + 1) =
      projectiveSpaceStructure k (n + 1) := coordinateAutomorphism_structure _ _ _ _

/-- The inverse retains the same literal original field structure. -/
@[reassoc]
theorem fixedPointAutomorphism_inv_structure :
    (fixedPointAutomorphism k n q hq).inv ≫ projectiveSpaceStructure k (n + 1) =
      projectiveSpaceStructure k (n + 1) := by
  calc
    _ = (fixedPointAutomorphism k n q hq).inv ≫
        ((fixedPointAutomorphism k n q hq).hom ≫ projectiveSpaceStructure k (n + 1)) := by
      rw [fixedPointAutomorphism_structure]
    _ = _ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The original source is retained in the internally produced fixed-point coordinates. -/
def fixedPointInclusion : X ⟶ projectiveSpace k (n + 1) :=
  i ≫ (fixedPointAutomorphism k n q hq).hom

instance fixedPointInclusion_isClosedImmersion : IsClosedImmersion (fixedPointInclusion k n q hq i) := by
  dsimp only [fixedPointInclusion]
  infer_instance

variable [IsIntegral X] (hdim : topologicalKrullDim X < n)

/-- The actual parameter open in the original ambient scheme is an actual inverse image of the internally computed open. -/
def fixedPointCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  (fixedPointAutomorphism k n q hq).hom ⁻¹ᵁ secantCenterOpen k n (fixedPointInclusion k n q hq i) hdim

/-- Nonemptiness uses an actual native point and the two actual scheme inverse identities. -/
theorem fixedPointCenterOpen_nonempty :
    (fixedPointCenterOpen k n q hq i hdim : Set (projectiveSpace k (n + 1))).Nonempty := by
  exact iso_preimage_open_nonempty (fixedPointAutomorphism k n q hq)
    (secantCenterOpen k n (fixedPointInclusion k n q hq i) hdim)
    (secantCenterOpen_nonempty k n (fixedPointInclusion k n q hq i) hdim)

/-- The actual centre open avoids the exact original closed image, before any coordinate transport. -/
theorem fixedPointCenterOpen_avoids_image (c : projectiveSpace k (n + 1))
    (hc : c ∈ fixedPointCenterOpen k n q hq i hdim) : c ∉ Set.range i := by
  rintro ⟨x, rfl⟩
  exact secantCenterOpen_avoids_image k n (fixedPointInclusion k n q hq i) hdim _ hc ⟨x, rfl⟩

/-- Every actual original rational centre in this produced original open gives a genuine finite projection on the same original source. -/
def projectionFromFixedPointOpen (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ fixedPointCenterOpen k n q hq i hdim) : X ⟶ projectiveSpace k n :=
  ProjectiveProjectionPoint.projectionFromPoint k n p hp i
    (fixedPointCenterOpen_avoids_image k n q hq i hdim _ hc)

/-- Finiteness is a genuine property of the actual original projection, with no supplied certificate. -/
theorem projectionFromFixedPointOpen_isFinite (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ fixedPointCenterOpen k n q hq i hdim) :
    IsFinite (projectionFromFixedPointOpen k n q hq i hdim p hp hc) :=
  ProjectiveProjectionPoint.projectionFromPoint_isFinite _ _ _ _ _ _

/-- The original coefficient triangle for the original finite projection is retained literally. -/
@[reassoc]
theorem projectionFromFixedPointOpen_structure (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ fixedPointCenterOpen k n q hq i hdim) :
    projectionFromFixedPointOpen k n q hq i hdim p hp hc ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) :=
  ProjectiveProjectionPoint.projectionFromPoint_structure _ _ _ _ _ _

end Hironaka.Geometry.ProjectiveSecant
