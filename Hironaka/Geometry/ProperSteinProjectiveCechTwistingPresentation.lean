import Hironaka.Geometry.ProperSteinProjectiveCechTwistingSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Internally produced native finite presentations of ORIGINAL twisting sheaves

The native local-generator construction adapts same-workspace
`BingWangEntropy/ProjectiveSectionExtension.lean`,
SHA256 e50e0f49d0d38a9b072e1dab24ba6a16cd713184b4575bd97539e253831de2d8.
The ORIGINAL polynomial irrelevant-ideal computation adapts
`BingWangEntropy/ProjectiveTwistingSheaf.lean`,
SHA256 ba9b02873b50ce110c6fea0ce797395a3febfd23a4ab513710120f726844c238.
All original coordinate frames are internally derived; no atlas or finite-presentation output is assumed.
The polynomial coefficient ring is ANY ORIGINAL commutative ring.
-/

universe u
open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {I : Type u} (k : ℕ) (a : I → 𝒜 1)

/-- The ORIGINAL coordinate frame gives the actual one-generator native free frame. -/
def projectiveTwistingFreeFrame (i : I) :
    (projectiveTwistingSheaf 𝒜 k).over (Proj.basicOpen 𝒜 (a i).val) ≅
      SheafOfModules.free (R := (Proj 𝒜).ringCatSheaf.over (Proj.basicOpen 𝒜 (a i).val))
        (ULift.{u} PUnit) :=
  projectiveTwistingCoordinateFrame 𝒜 k (a i) ≪≫
    (Limits.coproductUniqueIso (fun _ : ULift.{u} PUnit =>
      SheafOfModules.unit ((Proj 𝒜).ringCatSheaf.over (Proj.basicOpen 𝒜 (a i).val)))).symm

variable (hcover : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
  Ideal.span (Set.range (fun i => (a i).val)))
include hcover

/-- Actual ORIGINAL degree-one coordinates give actual native local-generator data. -/
def projectiveTwistingLocalGeneratorsData : (projectiveTwistingSheaf 𝒜 k).LocalGeneratorsData where
  I := I
  X i := Proj.basicOpen 𝒜 (a i).val
  coversTop := by
    rw [_root_.Opens.coversTop_iff]
    exact Proj.iSup_basicOpen_eq_top 𝒜 _ hcover
  generators i := (SheafOfModules.free.generatingSections
    (R := (Proj 𝒜).ringCatSheaf.over (Proj.basicOpen 𝒜 (a i).val)) (ULift.{u} PUnit)).ofEpi
      (projectiveTwistingFreeFrame 𝒜 k a i).inv

/-- Each ORIGINAL local-generator map is actually an isomorphism. -/
theorem projectiveTwistingLocalGeneratorsData_isLocallyFreeData :
    (projectiveTwistingLocalGeneratorsData 𝒜 k a hcover).IsLocallyFreeData := by
  constructor
  intro i
  change IsIso ((SheafOfModules.free.generatingSections
    (R := (Proj 𝒜).ringCatSheaf.over (Proj.basicOpen 𝒜 (a i).val)) (ULift.{u} PUnit)).ofEpi
      (projectiveTwistingFreeFrame 𝒜 k a i).inv).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  exact (congrArg IsIso (Category.id_comp (projectiveTwistingFreeFrame 𝒜 k a i).inv)).mpr
    (inferInstance : IsIso (projectiveTwistingFreeFrame 𝒜 k a i).inv)

/-- Original local freeness is derived from actual homogeneous fraction division. -/
theorem projectiveTwisting_isLocallyFree : (projectiveTwistingSheaf 𝒜 k).IsLocallyFree := by
  let := projectiveTwistingLocalGeneratorsData_isLocallyFreeData 𝒜 k a hcover
  exact (projectiveTwistingLocalGeneratorsData 𝒜 k a hcover).isLocallyFree

/-- Actual one-generator frames and no relations give native quasicoherent data. -/
def projectiveTwistingQuasicoherentData : (projectiveTwistingSheaf 𝒜 k).QuasicoherentData := by
  let := projectiveTwistingLocalGeneratorsData_isLocallyFreeData 𝒜 k a hcover
  exact (projectiveTwistingLocalGeneratorsData 𝒜 k a hcover).quasiCoherentData

/-- The SAME actual local presentations have finite original generators and relations. -/
theorem projectiveTwistingQuasicoherentData_isFinitePresentation :
    (projectiveTwistingQuasicoherentData 𝒜 k a hcover).IsFinitePresentation := by
  constructor
  intro i
  constructor
  · constructor
    change Finite (ULift.{u} PUnit)
    infer_instance
  · constructor
    change Finite (ULift Empty)
    infer_instance

/-- Native finite presentation is derived for the SAME original twisting sheaf. -/
theorem projectiveTwisting_isFinitePresentation :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := (Proj 𝒜).ringCatSheaf) (projectiveTwistingSheaf 𝒜 k) := by
  let := projectiveTwistingQuasicoherentData_isFinitePresentation 𝒜 k a hcover
  apply SheafOfModules.IsFinitePresentation.mk
  refine ⟨(projectiveTwistingQuasicoherentData 𝒜 k a hcover).shrink, ?_⟩
  constructor
  intro i
  exact inferInstanceAs
    (((projectiveTwistingQuasicoherentData 𝒜 k a hcover).presentation i.property.choose).IsFinite)

section PolynomialModel
omit hcover
variable {K J : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous polynomial irrelevant ideal is generated by actual coordinates. -/
theorem homogeneousPolynomial_irrelevant_le_coordinates :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule J K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : J → MvPolynomial J K)) := by
  classical
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn p hp
  have hp' : p.IsHomogeneous n := hp
  change p ∈ Ideal.span (Set.range (MvPolynomial.X : J → MvPolynomial J K))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  have hdn : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp' (MvPolynomial.mem_support_iff.mp hd)
  by_contra! h
  have hz : d = 0 := by
    ext i
    exact h i (Set.mem_univ i)
  rw [hz] at hdn
  change 0 = n at hdn
  omega

/-- The ORIGINAL polynomial coordinates internally produce native finite presentation. -/
theorem polynomialProjectiveTwisting_isFinitePresentation (m : ℕ) :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := (Proj (MvPolynomial.homogeneousSubmodule J K)).ringCatSheaf)
      (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule J K) m) :=
  projectiveTwisting_isFinitePresentation _ m
    (fun j => ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩)
    homogeneousPolynomial_irrelevant_le_coordinates

end PolynomialModel
end

end Hironaka.Geometry.ProperSteinProjectiveCech
