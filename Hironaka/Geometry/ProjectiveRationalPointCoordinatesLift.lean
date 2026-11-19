import Hironaka.Geometry.SegreGluing

/-!
# Actual affine chart lift of an original rational projective scheme point

Adapted in arbitrary coefficient fields from the chart-lift and affine-point
constructions in BingWangEntropy/SchemeComplexPointOpen.lean and
SchemeAffineComplexPoints.lean. All maps are actual native scheme maps.
The preserved source hashes are respectively
b62a733a60604f6efc75eeb08acc33b035adc661c6aab1fd0498f7b20c44cc46
and 6c3fee0ef33074724a6db1dbacbc8d3429c17d5d7032fd5c07a43ca675c1068e.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

namespace Hironaka.Geometry.ProjectiveRationalPointCoordinates

open ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))

/-- The image of the actual unique point of the original coefficient-field spectrum. -/
def pointImage : projectiveSpace k (n + 1) := p (⊥ : PrimeSpectrum k)

/-- An actual standard chart contains the original scheme point. -/
theorem exists_chart : ∃ j : Fin (n + 2),
    pointImage k n p ∈ Set.range (Segre.coordinateChartInclusion (R := k) j) := by
  have hx : pointImage k n p ∈ (⊤ : (projectiveSpace k (n + 1)).Opens) := trivial
  rw [← iSup_nativeCoordinateOpen_eq_top (R := k) (n := n + 1)] at hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  refine ⟨j, ?_⟩
  change pointImage k n p ∈ (Segre.coordinateChartInclusion (R := k) j).opensRange
  rwa [Segre.coordinateChartInclusion_opensRange]

/-- The actual coordinate chart is chosen internally from the original morphism. -/
def chosenChart : Fin (n + 2) := (exists_chart k n p).choose

/-- The internally chosen chart contains the original image point. -/
theorem chosenChart_mem : pointImage k n p ∈
    Set.range (Segre.coordinateChartInclusion (R := k) (chosenChart k n p)) :=
  (exists_chart k n p).choose_spec

/-- The entire original source range lies in the chosen chart. -/
theorem range_subset_chart : Set.range p ⊆
    Set.range (Segre.coordinateChartInclusion (R := k) (chosenChart k n p)) := by
  rintro _ ⟨x, rfl⟩
  have hx : x = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
  rw [hx]
  exact chosenChart_mem k n p

/-- The native open-immersion universal property constructs the actual original morphism's chart lift. -/
def chartLift : Spec (CommRingCat.of k) ⟶
    Spec (CommRingCat.of (CoordinateRing k (chosenChart k n p))) :=
  IsOpenImmersion.lift (Segre.coordinateChartInclusion (R := k) (chosenChart k n p)) p
    (range_subset_chart k n p)

/-- The actual lifted morphism recovers the literal original rational scheme morphism. -/
@[reassoc]
theorem chartLift_fac : chartLift k n p ≫
    Segre.coordinateChartInclusion (R := k) (chosenChart k n p) = p :=
  IsOpenImmersion.lift_fac _ _ _

/-- Original compatibility over the coefficient field is inherited by the actual chosen chart. -/
theorem chartLift_over_base (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _) :
    chartLift k n p ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (CoordinateRing k (chosenChart k n p)))) = 𝟙 _ := by
  rw [← Segre.coordinateChartInclusion_structure, ← Category.assoc, chartLift_fac, hp]

/-- The genuine affine scheme point gives its actual algebra point, with coefficient compatibility derived. -/
def chartAlgebraPoint (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _) :
    CoordinateRing k (chosenChart k n p) →ₐ[k] k where
  __ := (Spec.preimage (chartLift k n p)).hom
  commutes' a := by
    have h := congrArg Spec.preimage (chartLift_over_base k n p hp)
    have hc := congrArg (fun q : CommRingCat.of k ⟶ CommRingCat.of k => q a) h
    simpa [Spec.preimage_comp] using hc

/-- The internally obtained actual affine algebra map retains the original native scheme lift. -/
theorem chartAlgebraPoint_spec (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _) :
    Spec.map (CommRingCat.ofHom (chartAlgebraPoint k n p hp).toRingHom) = chartLift k n p :=
  Spec.map_preimage _

end Hironaka.Geometry.ProjectiveRationalPointCoordinates
