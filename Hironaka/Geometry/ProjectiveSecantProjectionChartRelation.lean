import Hironaka.Geometry.ProjectiveSecantProjectionCoordinates

/-!
# The whole original tangent relation vanishes under the actual original projection chart map
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open Algebra.ProjectiveSecant Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The entire actual original polynomial coordinate section of a homogeneous form is its native whole homogeneous fraction section. -/
theorem nativeCoordinateSection_eq_awayToSection (j : Fin (n + 2))
    {d : ℕ} {H : MvPolynomial (Fin (n + 2)) k} (hH : H.IsHomogeneous d) :
    (nativeCoordinateSectionsIso (R := k) j).hom (coordinateDehom j H) =
      (Proj.awayToSection (ProjectiveGrading k (n + 1)) (MvPolynomial.X j)).hom
        (Away.mk (ProjectiveGrading k (n + 1)) (MvPolynomial.isHomogeneous_X k j)
          d H (by simpa using hH)) := by
  change (nativeHomogeneousChartSectionsIso (R := k) j).hom
    (homogeneousChartRatioHom j (coordinateDehom j H)) = _
  rw [nativeHomogeneousChartSectionsIso_hom,
    homogeneousChartRatioHom_dehom_of_isHomogeneous j hH]
  rfl

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- Whole original homogeneous ideal membership, actual native Proj section pullback, and exact inverse polynomial coordinates internally prove the relation lies in the WHOLE actual transformed chart kernel. -/
theorem inverseCoordinateRelation_mem_tangentChartKernel
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (j : Fin (n + 2))
    {d : ℕ} {H : MvPolynomial (Fin (n + 2)) k} (hH : H.IsHomogeneous d)
    (hHJ : H ∈ representativeIdeal k n i) :
    coordinateDehom j ((coordinatePolynomialEquiv k n v hv).symm H) ∈
      RingHom.ker (tangentChartPolynomialMap k n (i ≫ (coordinateAutomorphism k n v hv).hom) j) := by
  let G := ProjectiveGrading k (n + 1)
  let E := coordinateGradedMap k n v hv
  let J := representativeIdeal k n i
  let H' := (coordinatePolynomialEquiv k n v hv).symm H
  have hH' : H'.IsHomogeneous d := coordinatePolynomialEquiv_symm_isHomogeneous k n v hv hH
  have hH'mem : H' ∈ G (d • (1 : ℕ)) := by
    change H'.IsHomogeneous (d • (1 : ℕ))
    simpa using hH'
  let a := Away.mk G (MvPolynomial.isHomogeneous_X k j) d H' hH'mem
  have hEH : E H' = H := (coordinatePolynomialEquiv k n v hv).apply_symm_apply H
  have hzero : Away.map (GradedQuotient.gradedMk G J.toIdeal) (E (MvPolynomial.X j))
      (Away.map E (MvPolynomial.X j) a) = 0 := by
    dsimp only [a]
    rw [Away.map_mk]
    exact (GradedQuotient.awayMap_mk_eq_zero_iff G J
      (E.map_mem (MvPolynomial.isHomogeneous_X k j)) d (E H') (E.map_mem hH'mem)).mpr
        ⟨0, by
          simp only [pow_zero, one_mul, hEH]
          exact HomogeneousIdeal.mem_iff.mpr hHJ⟩
  have hI := (GradedQuotient.mem_quotientIdealSheaf_awayToSection_iff G J
    (by decide : 0 < (1 : ℕ)) (E.map_mem (MvPolynomial.isHomogeneous_X k j))
      (Away.map E (MvPolynomial.X j) a)).mpr hzero
  change (Proj.awayToSection G (E (MvPolynomial.X j))).hom (Away.map E (MvPolynomial.X j) a) ∈
    (originalInclusion k n J).ker.ideal ⟨Proj.basicOpen G (E (MvPolynomial.X j)),
      Proj.isAffineOpen_basicOpen G _ (E.map_mem (MvPolynomial.isHomogeneous_X k j))
        (by decide : 0 < (1 : ℕ))⟩ at hI
  rw [representativeInclusion_ker k n i, Scheme.Hom.ker_apply] at hI
  change i.app (Proj.basicOpen G (E (MvPolynomial.X j)))
    ((Proj.awayToSection G (E (MvPolynomial.X j))).hom (Away.map E (MvPolynomial.X j) a)) = 0 at hI
  have hn := congrArg (fun f => f.hom a)
    (Proj.awayToSection_comp_appLE E (coordinateGradedMap_irrelevant_le k n v hv)
      (MvPolynomial.isHomogeneous_X k j))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, CommRingCat.hom_ofHom] at hn
  change (coordinateAutomorphism k n v hv).hom.app (nativeCoordinateOpen j)
      ((Proj.awayToSection G (MvPolynomial.X j)).hom a) =
    (Proj.awayToSection G (E (MvPolynomial.X j))).hom (Away.map E (MvPolynomial.X j) a) at hn
  have hsec : (tangentCoordinateRingIso k n j).hom.hom (coordinateDehom j H') =
      (Proj.awayToSection G (MvPolynomial.X j)).hom a := by
    rw [tangentCoordinateRingIso_eq_native]
    exact nativeCoordinateSection_eq_awayToSection k n j hH'
  change i.app (Proj.basicOpen G (E (MvPolynomial.X j)))
    ((coordinateAutomorphism k n v hv).hom.app (nativeCoordinateOpen j)
      ((tangentCoordinateRingIso k n j).hom.hom (coordinateDehom j H'))) = 0
  calc
    _ = i.app (Proj.basicOpen G (E (MvPolynomial.X j)))
        ((coordinateAutomorphism k n v hv).hom.app (nativeCoordinateOpen j)
          ((Proj.awayToSection G (MvPolynomial.X j)).hom a)) :=
      congrArg (fun z => i.app (Proj.basicOpen G (E (MvPolynomial.X j)))
        ((coordinateAutomorphism k n v hv).hom.app (nativeCoordinateOpen j) z)) hsec
    _ = i.app (Proj.basicOpen G (E (MvPolynomial.X j)))
        ((Proj.awayToSection G (E (MvPolynomial.X j))).hom (Away.map E (MvPolynomial.X j) a)) :=
      congrArg (fun z => i.app (Proj.basicOpen G (E (MvPolynomial.X j))) z) hn
    _ = 0 := hI

variable (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X ≤ n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- The actual original geometric data internally produce a relation in the WHOLE actual projection source-chart kernel, without supplied transformed-ideal membership. -/
theorem projectionCoordinateTangentEquation_mem_kernel (j : Fin (n + 2)) :
    coordinateDehom j (projectionCoordinateTangentEquation k n p hp i s hs hdim hx) ∈
      RingHom.ker (tangentChartPolynomialMap k n
        (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) j) :=
  inverseCoordinateRelation_mem_tangentChartKernel k n i _ _ j
    (originalHomogeneousTangentEquation k n i s hs hdim hx).property.2.1
    (originalHomogeneousTangentEquation k n i s hs hdim hx).property.2.2.2.1

end Hironaka.Geometry.ProjectiveSecant
