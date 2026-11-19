import Hironaka.Geometry.ProjectiveSecantProjectionFibre
import Hironaka.Geometry.ProjectiveSecantPointLine
import Hironaka.Algebra.ProjectiveSecantLineUniqueness

/-!
# The SAME original finite projection has the SAME original rational point as its whole fibre support
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
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X < n)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hc : pointImage k n p ∈ fixedPointCenterOpen k n (s ≫ i) hs i hdim)

/-- Both exact actual original endpoint triangles internally force the original fixed-point secant minors on every actual original projection-fibre line point. -/
theorem projectionFibreLine_fixedPoint_minors (y : projectiveSpace k 1) (j a : Fin (n + 1)) :
    let hout := fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hdim _ hc
    let v := pointVector k n (transformedCenter k n (s ≫ i) hs p)
      (transformedCenter_structure k n (s ≫ i) hs p hp)
    C (v j.succ) * MvPolynomial.X a.succ - C (v a.succ) * MvPolynomial.X j.succ ∈
      ((fixedPointAutomorphism k n (s ≫ i) hs).hom
        (projectionFibreLine k n i p hp s hs hout y)).asHomogeneousIdeal := by
  let hout := fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hdim _ hc
  let v := pointVector k n (transformedCenter k n (s ≫ i) hs p)
    (transformedCenter_structure k n (s ≫ i) hs p hp)
  let hv := pointVector_ne_zero k n (transformedCenter k n (s ≫ i) hs p)
    (transformedCenter_structure k n (s ≫ i) hs p hp)
  let F : MvPolynomial (Fin (n + 2)) k :=
    C (v j.succ) * MvPolynomial.X a.succ - C (v a.succ) * MvPolynomial.X j.succ
  have hF : F.IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_C_mul_X _ _).sub (MvPolynomial.isHomogeneous_C_mul_X _ _)
  let w := projectionCoordinatePointVector k n (s ≫ i) p hs hp
  let α := (lineGradedMap k n w).comp
    ((inverseCoordinateGradedMap k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).comp
      (coordinateGradedMap k n (pointVector k n (s ≫ i) hs) (pointVector_ne_zero k n (s ≫ i) hs)))
  have hα : (α F).IsHomogeneous 1 := α.map_mem hF
  have h0 : centreGradedMap k 0 (α F) = 0 := by
    have hm : F ∈ ((fixedPointAutomorphism k n (s ≫ i) hs).hom
        (projectionFibreLine k n i p hp s hs hout (centrePoint k 0))).asHomogeneousIdeal := by
      rw [projectionFibreLine_apply_centre]
      change F ∈ (pointImage k n (transformedCenter k n (s ≫ i) hs p)).asHomogeneousIdeal
      rw [← pointVector_image k n (transformedCenter k n (s ≫ i) hs p)
        (transformedCenter_structure k n (s ≫ i) hs p hp)]
      apply (vectorPoint_mem_homogeneous k n v hv hF).mpr
      simp only [F, map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring
    exact hm
  have h1 : MvPolynomial.eval (fun z : Fin 2 => if z = 0 then 0 else 1) (α F) = 0 := by
    have hm : F ∈ ((fixedPointAutomorphism k n (s ≫ i) hs).hom
        (projectionFibreLine k n i p hp s hs hout
          (vectorPoint k 0 (lineEndVector k) (lineEndVector_ne_zero k)))).asHomogeneousIdeal := by
      rw [projectionFibreLine_apply_source, fixedPointAutomorphism_apply]
      change centreGradedMap k n F = 0
      simp [F, centreGradedMap]
    change α F ∈ (vectorPoint k 0 (lineEndVector k) (lineEndVector_ne_zero k)).asHomogeneousIdeal at hm
    exact (vectorPoint_mem_homogeneous k 0 (lineEndVector k) (lineEndVector_ne_zero k) hα).mp hm
  have hz : α F = 0 := binary_homogeneous_linear_eq_zero hα h0 h1
  change α F ∈ y.asHomogeneousIdeal
  rw [hz]
  exact y.asHomogeneousIdeal.zero_mem

set_option maxHeartbeats 1000000 in
/-- The actual original line produced in projection-centre coordinates is contained in the SAME actual original secant line previously produced in original fixed-point coordinates. -/
theorem projectionFibreLine_mem_fixedPointLine (y : projectiveSpace k 1) :
    let hout := fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hdim _ hc
    projectionFibreLine k n i p hp s hs hout y ∈
      Set.range (fixedPointLine k n (s ≫ i) hs i hdim p hp hc) := by
  let hout := fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hdim _ hc
  let v := pointVector k n (transformedCenter k n (s ≫ i) hs p)
    (transformedCenter_structure k n (s ≫ i) hs p hp)
  let hv := pointVector_ne_zero k n (transformedCenter k n (s ≫ i) hs p)
    (transformedCenter_structure k n (s ≫ i) hs p hp)
  let hc' := transformedCenter_vector_mem k n (s ≫ i) hs i hdim p hp hc
  let j := (exists_secant_coordinate k n (fixedPointInclusion k n (s ≫ i) hs i) hdim v hv hc').choose
  have hj : v j.succ ≠ 0 :=
    (exists_secant_coordinate k n (fixedPointInclusion k n (s ≫ i) hs i) hdim v hv hc').choose_spec
  let z := (fixedPointAutomorphism k n (s ≫ i) hs).hom (projectionFibreLine k n i p hp s hs hout y)
  have hm (a : Fin (n + 1)) :
      C (v j.succ) * MvPolynomial.X a.succ - C (v a.succ) * MvPolynomial.X j.succ ∈ z.asHomogeneousIdeal :=
    projectionFibreLine_fixedPoint_minors k n i s hs hdim p hp hc y j a
  have hr : z ∈ Set.range (secantLine k n (fixedPointInclusion k n (s ≫ i) hs i) hdim v hv hc') :=
    point_mem_range_projMap_of_ker_le (lineGradedMap k n v)
      (lineGradedMap_surjective k n v j hj) (lineGradedMap_irrelevant_le k n v j hj) z
      (lineGradedMap_ker_le_of_minors k n v j hj z.asHomogeneousIdeal.toIdeal hm)
  obtain ⟨t, ht⟩ := hr
  refine ⟨t, ?_⟩
  have he := congrArg (fun x => (fixedPointAutomorphism k n (s ≫ i) hs).inv x) ht
  have hinv : (fixedPointAutomorphism k n (s ≫ i) hs).inv z =
      projectionFibreLine k n i p hp s hs hout y :=
    congrArg (fun f : projectiveSpace k (n + 1) ⟶ projectiveSpace k (n + 1) =>
      f (projectionFibreLine k n i p hp s hs hout y)) (fixedPointAutomorphism k n (s ≫ i) hs).hom_inv_id
  exact he.trans hinv

/-- Original integral projective source, actual original rational source point and actual centre in its internally produced original secant open force the SAME original finite projection's entire actual fibre at that SAME point to contain only that point. -/
theorem projectionFromFixedPointOpen_fibre_eq_source (x : X)
    (hf : projectionFromFixedPointOpen k n (s ≫ i) hs i hdim p hp hc x =
      projectionFromFixedPointOpen k n (s ≫ i) hs i hdim p hp hc (s (⊥ : PrimeSpectrum k))) :
    x = s (⊥ : PrimeSpectrum k) := by
  let hout := fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hdim _ hc
  obtain ⟨y, hy⟩ := projectionFromPoint_fibre_mem_line k n i p hp s hs hout x hf
  have hl : i x ∈ Set.range (fixedPointLine k n (s ≫ i) hs i hdim p hp hc) := by
    rw [← hy]
    exact projectionFibreLine_mem_fixedPointLine k n i s hs hdim p hp hc y
  have hqX : pointImage k n (s ≫ i) ∈ Set.range i := ⟨s (⊥ : PrimeSpectrum k), rfl⟩
  have hi : i x = pointImage k n (s ≫ i) := by
    apply Set.mem_singleton_iff.mp
    rw [← fixedPointLine_range_inter_range k n (s ≫ i) hs i hdim p hp hc hqX]
    exact ⟨hl, ⟨x, rfl⟩⟩
  exact i.isClosedEmbedding.injective hi

/-- The SAME actual original finite projection's actual point-set fibre at the SAME original rational source point is exactly its singleton. -/
theorem projectionFromFixedPointOpen_fibre_singleton :
    (projectionFromFixedPointOpen k n (s ≫ i) hs i hdim p hp hc) ⁻¹'
      {projectionFromFixedPointOpen k n (s ≫ i) hs i hdim p hp hc (s (⊥ : PrimeSpectrum k))} =
        {s (⊥ : PrimeSpectrum k)} := by
  ext x
  constructor
  · exact fun h => projectionFromFixedPointOpen_fibre_eq_source k n i s hs hdim p hp hc x h
  · intro h
    rw [Set.mem_singleton_iff.mp h]
    rfl

end Hironaka.Geometry.ProjectiveSecant
