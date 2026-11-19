import Hironaka.Geometry.ProjectiveSecantProjectionCoordinates
import Hironaka.Geometry.ProjectiveSecantLinearRange
import Hironaka.Algebra.ProjectiveSecantProjectionFibre
import Hironaka.Geometry.ProjectiveProjectionPointFinite

/-!
# The same actual original finite projection fibre lies on an actual native original line
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter ProjectiveRationalPointCoordinates ProjectiveProjectionPoint
open Algebra.ProjectiveSecant Algebra.ProjectiveLinearCoordinates Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The SAME actual original standard-centre finite projection retains its whole original homogeneous-prime contraction, for every original polynomial. -/
theorem closedProjection_mem_ideal_iff (hout : centrePoint k n ∉ Set.range i)
    (x : X) (F : MvPolynomial (Fin (n + 1)) k) :
    F ∈ (closedProjection k n i hout x).asHomogeneousIdeal ↔
      MvPolynomial.rename Fin.succ F ∈ (i x).asHomogeneousIdeal := by
  have hi : originalInclusion k n (representativeIdeal k n i) ((representativeIso k n i).hom x) = i x :=
    congrArg (fun f : X ⟶ projectiveSpace k (n + 1) => f x) (representativeIso_hom_inclusion k n i)
  rw [← hi]
  rfl

/-- Equality in the actual original projection fibre gives the actual original remaining-coordinate minors in the actual original point prime. -/
theorem closedProjection_fibre_minors (hout : centrePoint k n ∉ Set.range i)
    (x q : X) (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hq : i q = vectorPoint k n v hv)
    (hf : closedProjection k n i hout x = closedProjection k n i hout q)
    (j a : Fin (n + 1)) :
    C (v j.succ) * MvPolynomial.X a.succ - C (v a.succ) * MvPolynomial.X j.succ ∈ (i x).asHomogeneousIdeal := by
  let F : MvPolynomial (Fin (n + 1)) k := C (v j.succ) * MvPolynomial.X a - C (v a.succ) * MvPolynomial.X j
  have hF : F.IsHomogeneous 1 := by
    exact ((MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X k a)).sub
      ((MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X k j))
  have hqF : MvPolynomial.rename Fin.succ F ∈ (i q).asHomogeneousIdeal := by
    rw [hq]
    apply (vectorPoint_mem_homogeneous k n v hv hF.rename_isHomogeneous).mpr
    simp [F]
    ring
  have ht := (closedProjection_mem_ideal_iff k n i hout q F).mpr hqF
  rw [← hf] at ht
  have hx := (closedProjection_mem_ideal_iff k n i hout x F).mp ht
  simpa [F] using hx

/-- The whole actual original fibre at the original rational vector lies on the actual native line; all whole-kernel and native-line-point data are produced internally. -/
theorem closedProjection_fibre_mem_lineImmersion (hout : centrePoint k n ∉ Set.range i)
    (x q : X) (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (j : Fin (n + 1)) (hj : v j.succ ≠ 0) (hq : i q = vectorPoint k n v hv)
    (hf : closedProjection k n i hout x = closedProjection k n i hout q) :
    i x ∈ Set.range (lineImmersion k n v j hj) := by
  exact point_mem_range_projMap_of_ker_le (lineGradedMap k n v)
    (lineGradedMap_surjective k n v j hj) (lineGradedMap_irrelevant_le k n v j hj) (i x)
    (lineGradedMap_ker_le_of_minors k n v j hj (i x).asHomogeneousIdeal.toIdeal
      (fun a => closedProjection_fibre_minors k n i hout x q v hv hq hf j a))

variable (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hout : pointImage k n p ∉ Set.range i)

/-- An actual nonzero remaining coordinate of the SAME original rational source point is selected internally. -/
def projectionFibreLinePivot : Fin (n + 1) :=
  Classical.choose (exists_projectionCoordinatePointVector_remaining_ne_zero k n p hp i s hs hout)

omit [IsClosedImmersion i] in
/-- The actual internally selected coordinate is genuinely nonzero. -/
theorem projectionFibreLinePivot_ne_zero :
    projectionCoordinatePointVector k n (s ≫ i) p hs hp
      (projectionFibreLinePivot k n i p hp s hs hout).succ ≠ 0 :=
  Classical.choose_spec (exists_projectionCoordinatePointVector_remaining_ne_zero k n p hp i s hs hout)

/-- The actual native original projective line through the original centre and original source point, from original geometric data alone. -/
def projectionFibreLine : projectiveSpace k 1 ⟶ projectiveSpace k (n + 1) :=
  lineImmersion k n (projectionCoordinatePointVector k n (s ≫ i) p hs hp)
    (projectionFibreLinePivot k n i p hp s hs hout)
    (projectionFibreLinePivot_ne_zero k n i p hp s hs hout) ≫
      (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).inv

instance projectionFibreLine_isClosedImmersion : IsClosedImmersion (projectionFibreLine k n i p hp s hs hout) := by
  dsimp only [projectionFibreLine]
  infer_instance


omit [IsClosedImmersion i] in
/-- The actual original line retains its entire literal original coefficient triangle. -/
@[reassoc]
theorem projectionFibreLine_structure :
    projectionFibreLine k n i p hp s hs hout ≫ projectiveSpaceStructure k (n + 1) =
      projectiveSpaceStructure k 1 := by
  let e := coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
  have hc := coordinateAutomorphism_structure k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
  have he : e.inv ≫ projectiveSpaceStructure k (n + 1) = projectiveSpaceStructure k (n + 1) := by
    calc
      _ = e.inv ≫ (e.hom ≫ projectiveSpaceStructure k (n + 1)) :=
        congrArg (fun f => e.inv ≫ f) hc.symm
      _ = _ := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  change (lineImmersion k n (projectionCoordinatePointVector k n (s ≫ i) p hs hp)
    (projectionFibreLinePivot k n i p hp s hs hout)
    (projectionFibreLinePivot_ne_zero k n i p hp s hs hout) ≫ e.inv) ≫ _ = _
  rw [Category.assoc, he, lineImmersion_structure]


omit [IsClosedImmersion i] in
/-- The first actual native endpoint maps to exactly the original outside rational centre. -/
theorem projectionFibreLine_apply_centre :
    projectionFibreLine k n i p hp s hs hout (centrePoint k 0) = pointImage k n p := by
  let e := coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
  have hp0 : e.hom (pointImage k n p) = centrePoint k n := by
    rw [← pointVector_image k n p hp]
    exact coordinateAutomorphism_apply_vectorPoint k n _ _
  change e.inv (lineImmersion _ _ _ _ _ (centrePoint k 0)) = _
  rw [lineImmersion_apply_standard, ← hp0]
  exact congrArg (fun f : projectiveSpace k (n + 1) ⟶ projectiveSpace k (n + 1) =>
    f (pointImage k n p)) e.hom_inv_id


omit [IsClosedImmersion i] in
/-- The other actual native endpoint maps to exactly the original rational source point. -/
theorem projectionFibreLine_apply_source :
    projectionFibreLine k n i p hp s hs hout
      (vectorPoint k 0 (lineEndVector k) (lineEndVector_ne_zero k)) = pointImage k n (s ≫ i) := by
  let e := coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
  change e.inv (lineImmersion _ _ _ _ _ _) = _
  rw [lineImmersion_apply_vector_end _ _ _ (projectionCoordinatePointVector_ne_zero k n (s ≫ i) p hs hp)]
  rw [← coordinateAutomorphism_apply_originalPoint k n (s ≫ i) p hs hp]
  exact congrArg (fun f : projectiveSpace k (n + 1) ⟶ projectiveSpace k (n + 1) =>
    f (pointImage k n (s ≫ i))) e.hom_inv_id


/-- Every actual original point in the SAME original finite projection's fibre at the original source point belongs to the actual native original line through the original source point and centre. No vector, prime, minor or line certificate is supplied. -/
theorem projectionFromPoint_fibre_mem_line (x : X)
    (hf : projectionFromPoint k n p hp i hout x =
      projectionFromPoint k n p hp i hout (s (⊥ : PrimeSpectrum k))) :
    i x ∈ Set.range (projectionFibreLine k n i p hp s hs hout) := by
  let e := coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
  let i' := i ≫ e.hom
  have hout' : centrePoint k n ∉ Set.range i' := transformedInclusion_centre_outside k n i
    (pointVector k n p hp) (pointVector_ne_zero k n p hp) (pointVector_outside k n p hp i hout)
  have hq : i' (s (⊥ : PrimeSpectrum k)) =
      vectorPoint k n (projectionCoordinatePointVector k n (s ≫ i) p hs hp)
        (projectionCoordinatePointVector_ne_zero k n (s ≫ i) p hs hp) :=
    coordinateAutomorphism_apply_originalPoint k n (s ≫ i) p hs hp
  change closedProjection k n i' hout' x = closedProjection k n i' hout' (s (⊥ : PrimeSpectrum k)) at hf
  obtain ⟨y, hy⟩ := closedProjection_fibre_mem_lineImmersion k n i' hout' x
    (s (⊥ : PrimeSpectrum k)) (projectionCoordinatePointVector k n (s ≫ i) p hs hp)
    (projectionCoordinatePointVector_ne_zero k n (s ≫ i) p hs hp)
    (projectionFibreLinePivot k n i p hp s hs hout)
    (projectionFibreLinePivot_ne_zero k n i p hp s hs hout) hq hf
  refine ⟨y, ?_⟩
  have he := congrArg (fun z => e.inv z) hy
  have hinv : e.inv (e.hom (i x)) = i x := congrArg (fun f : projectiveSpace k (n + 1) ⟶
    projectiveSpace k (n + 1) => f (i x)) e.hom_inv_id
  exact he.trans hinv

end Hironaka.Geometry.ProjectiveSecant
