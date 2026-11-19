import Hironaka.Geometry.ProjectiveSecantTangentPoint
import Hironaka.Geometry.RegularSmooth
import Hironaka.Geometry.RegularCurve
import Hironaka.Algebra.ProjectiveSecantTangentAffineFiniteCoordinates

/-!
# Original smooth rational projective points internally produce actual tangent equations
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial IsLocalRing

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates
open Algebra.ProjectiveSecant

universe u

attribute [local instance] MvPolynomial.gradedAlgebra tangentChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The actual original affine source chart has dimension bounded by the original geometric source dimension. -/
theorem tangentSourceChart_dimension_le (j : Fin (n + 2)) :
    ringKrullDim Γ(X, i ⁻¹ᵁ nativeCoordinateOpen j) ≤ topologicalKrullDim X := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (tangentSourceChart_isAffine k n i j).fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

/-- The original actual affine coordinate set has the original ambient dimension, internally counted. -/
theorem tangentChart_coordinate_card (j : Fin (n + 2)) :
    Nat.card {l : Fin (n + 2) // l ≠ j} = n + 1 := by
  classical
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

variable (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The actual original affine source point maps to the exact original source scheme point. -/
theorem tangentAffinePoint_image :
    (tangentSourceChart_isAffine k n i (chosenChart k n (s ≫ i))).fromSpec
      (PrimeSpectrum.comap (tangentSourcePoint k n i s hs).toRingHom (⊥ : PrimeSpectrum k)) =
        s (⊥ : PrimeSpectrum k) := by
  have h := congrArg (fun f : Spec (CommRingCat.of k) ⟶ X => f (⊥ : PrimeSpectrum k))
    (tangentSourcePointLift_fac k n i s)
  rw [← tangentSourcePointRingHom_spec] at h
  exact h

/-- Actual native smooth-locus regularity and the two actual stalk isomorphisms derive regularity at the original affine algebra point. -/
theorem tangentAffinePoint_isRegularLocalRing
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus) :
    IsRegularLocalRing (Localization.AtPrime (rationalPointIdeal (tangentSourcePoint k n i s hs))) := by
  let A := Γ(X, i ⁻¹ᵁ nativeCoordinateOpen (chosenChart k n (s ≫ i)))
  let b : PrimeSpectrum A := PrimeSpectrum.comap (tangentSourcePoint k n i s hs).toRingHom (⊥ : PrimeSpectrum k)
  let g := (tangentSourceChart_isAffine k n i (chosenChart k n (s ≫ i))).fromSpec
  have hr : IsRegularLocalRing (X.presheaf.stalk (g b)) := by
    change IsRegularLocalRing (X.presheaf.stalk ((tangentSourceChart_isAffine k n i (chosenChart k n (s ≫ i))).fromSpec _))
    rw [tangentAffinePoint_image k n i s hs]
    exact RegularSmooth.isRegularLocalRing_of_mem_smoothLocus
      (i ≫ projectiveSpaceStructure k (n + 1)) _ hx
  let : IsRegularLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk b) :=
    IsRegularLocalRing.of_ringEquiv (asIso (g.stalkMap b)).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv (R := (Spec (CommRingCat.of A)).presheaf.stalk b)
    (StructureSheaf.stalkIso A b).toRingEquiv.symm

/-- The original closed projective source, original smooth rational point, and original geometric dimension internally produce a WHOLE original chart-kernel relation with a genuine nonzero original partial derivative. -/
theorem exists_original_tangent_chart_relation (hdim : topologicalKrullDim X ≤ n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus) :
    ∃ F : CoordinateRing k (chosenChart k n (s ≫ i)),
      F ∈ (i.ker.ideal ⟨nativeCoordinateOpen (chosenChart k n (s ≫ i)),
        nativeCoordinateOpen_isAffine (R := k) (chosenChart k n (s ≫ i))⟩).comap
          (tangentCoordinateRingIso k n (chosenChart k n (s ≫ i))).hom.hom ∧
      ∃ j : {l : Fin (n + 2) // l ≠ chosenChart k n (s ≫ i)},
        chartAlgebraPoint k n (s ≫ i) hs (MvPolynomial.pderiv j F) ≠ 0 := by
  let : IsRegularLocalRing (Localization.AtPrime (rationalPointIdeal (tangentSourcePoint k n i s hs))) :=
    tangentAffinePoint_isRegularLocalRing k n i s hs hx
  have hA : ringKrullDim Γ(X, i ⁻¹ᵁ nativeCoordinateOpen (chosenChart k n (s ≫ i))) <
      Nat.card {l : Fin (n + 2) // l ≠ chosenChart k n (s ≫ i)} := by
    rw [tangentChart_coordinate_card]
    apply (tangentSourceChart_dimension_le k n i _).trans_lt
    apply hdim.trans_lt
    exact_mod_cast Nat.lt_succ_self n
  obtain ⟨F, hF, j, hFj⟩ := exists_affine_kernel_derivative_ne_zero_finiteCoordinates
    (tangentChartAlgHom k n i (chosenChart k n (s ≫ i)))
    (tangentChartPolynomialMap_surjective k n i (chosenChart k n (s ≫ i)))
    (tangentSourcePoint k n i s hs) hA
  refine ⟨F, ?_, j, ?_⟩
  · rw [← tangentChartPolynomialMap_ker]
    exact hF
  · change tangentSourcePointRingHom k n i s
      (tangentChartPolynomialMap k n i (chosenChart k n (s ≫ i)) (MvPolynomial.pderiv j F)) ≠ 0 at hFj
    intro hz
    apply hFj
    exact (RingHom.congr_fun (tangentSourcePointRingHom_comp k n i s hs) (MvPolynomial.pderiv j F)).trans hz

end Hironaka.Geometry.ProjectiveSecant
