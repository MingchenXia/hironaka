import Hironaka.Geometry.ProjectiveSecantTangentChart

/-!
# Original coefficient-preserving source points on actual original coordinate charts
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The actual original affine chart's coefficient action comes from the whole original coordinate map. -/
@[instance_reducible]
def tangentChartAlgebra (j : Fin (n + 2)) : Algebra k Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j) :=
  ((tangentChartPolynomialMap k n i j).comp (algebraMap k (CoordinateRing k j))).toAlgebra

attribute [local instance] tangentChartAlgebra

/-- The actual original chart presentation retains precisely this original coefficient action. -/
def tangentChartAlgHom (j : Fin (n + 2)) :
    CoordinateRing k j →ₐ[k] Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j) where
  __ := tangentChartPolynomialMap k n i j
  commutes' _ := rfl

/-- The coefficient action is the original source chart's literal scheme structure map. -/
@[reassoc]
theorem tangentSourceChart_structure (j : Fin (n + 2)) :
    ((tangentSourceChart_isAffine k n i j).fromSpec ≫ i) ≫ projectiveSpaceStructure k (n + 1) =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j))) := by
  rw [← tangentChartPolynomialMap_spec, Category.assoc, Segre.coordinateChartInclusion_structure,
    ← Spec.map_comp]
  rfl

variable (s : Spec (CommRingCat.of k) ⟶ X)

/-- The actual whole source field spectrum lies in its internally chosen original affine source chart. -/
theorem sourcePoint_range_subset_tangentChart :
    Set.range s ⊆ Set.range (tangentSourceChart_isAffine k n i (chosenChart k n (s ≫ i))).fromSpec := by
  rintro _ ⟨z, rfl⟩
  rw [(tangentSourceChart_isAffine k n i (chosenChart k n (s ≫ i))).range_fromSpec]
  change i (s z) ∈ nativeCoordinateOpen (chosenChart k n (s ≫ i))
  have h := range_subset_chart k n (s ≫ i) ⟨z, rfl⟩
  change i (s z) ∈ (Segre.coordinateChartInclusion (R := k) (chosenChart k n (s ≫ i))).opensRange at h
  rwa [Segre.coordinateChartInclusion_opensRange] at h

/-- The actual original scheme point lifts internally to the actual original affine source chart. -/
def tangentSourcePointLift : Spec (CommRingCat.of k) ⟶
    Spec (CommRingCat.of Γ(X, i ⁻¹ᵁ nativeCoordinateOpen (chosenChart k n (s ≫ i)))) :=
  IsOpenImmersion.lift (tangentSourceChart_isAffine k n i (chosenChart k n (s ≫ i))).fromSpec s
    (sourcePoint_range_subset_tangentChart k n i s)

/-- The source-point lift retains the entire original scheme morphism. -/
@[reassoc]
theorem tangentSourcePointLift_fac :
    tangentSourcePointLift k n i s ≫ (tangentSourceChart_isAffine k n i (chosenChart k n (s ≫ i))).fromSpec = s :=
  IsOpenImmersion.lift_fac _ _ _

/-- Fully faithful native Spec reads the whole original algebra point from this actual original source lift. -/
def tangentSourcePointRingHom : Γ(X, i ⁻¹ᵁ nativeCoordinateOpen (chosenChart k n (s ≫ i))) →+* k :=
  (Spec.preimage (tangentSourcePointLift k n i s)).hom

/-- This whole original source algebra point is exactly the internally constructed actual scheme lift. -/
theorem tangentSourcePointRingHom_spec :
    Spec.map (CommRingCat.ofHom (tangentSourcePointRingHom k n i s)) = tangentSourcePointLift k n i s :=
  Spec.map_preimage _

variable (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The actual original source algebra point and actual original coordinate presentation give precisely the original ambient point evaluation. -/
theorem tangentSourcePointRingHom_comp :
    (tangentSourcePointRingHom k n i s).comp (tangentChartPolynomialMap k n i (chosenChart k n (s ≫ i))) =
      (chartAlgebraPoint k n (s ≫ i) hs).toRingHom := by
  have h : CommRingCat.ofHom (tangentChartPolynomialMap k n i (chosenChart k n (s ≫ i))) ≫
      CommRingCat.ofHom (tangentSourcePointRingHom k n i s) =
        CommRingCat.ofHom (chartAlgebraPoint k n (s ≫ i) hs).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, tangentSourcePointRingHom_spec, chartAlgebraPoint_spec]
    apply (cancel_mono (Segre.coordinateChartInclusion (R := k) (chosenChart k n (s ≫ i)))).mp
    rw [Category.assoc, tangentChartPolynomialMap_spec, ← Category.assoc, tangentSourcePointLift_fac,
      chartLift_fac]
  exact congrArg (fun f : CommRingCat.of (CoordinateRing k (chosenChart k n (s ≫ i))) ⟶ CommRingCat.of k => f.hom) h

/-- The original coefficient triangle proves that the internally recovered whole source point is a genuine original algebra point. -/
def tangentSourcePoint : Γ(X, i ⁻¹ᵁ nativeCoordinateOpen (chosenChart k n (s ≫ i))) →ₐ[k] k where
  __ := tangentSourcePointRingHom k n i s
  commutes' c := by
    have h := RingHom.congr_fun (tangentSourcePointRingHom_comp k n i s hs) (algebraMap k _ c)
    exact h.trans ((chartAlgebraPoint k n (s ≫ i) hs).commutes c)

end Hironaka.Geometry.ProjectiveSecant
