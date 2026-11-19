import Hironaka.Geometry.ProperSteinProjectiveCechTwistingCoordinateEvaluation

/-!
# Actual original coordinate fractions preserve EVERY actual original restriction

The proof uses ALL actual original prime values and native module-localization
uniqueness, with zero divisors and localization torsion retained.
No common generic point or desired restriction-square certificate is assumed.
-/

universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [LinearOrder I] [Fintype I] in
/-- Actual original subset inclusion gives the SAME original coordinate-product divisibility. -/
theorem polynomialCoordinateProduct_dvd_of_subset {S T : Finset I} (hST : S ⊆ T) :
    polynomialCoordinateProduct (K := K) S ∣ polynomialCoordinateProduct (K := K) T :=
  Finset.prod_dvd_prod_of_subset S T (fun i => (MvPolynomial.X i : MvPolynomial I K)) hST

/-- Actual ORIGINAL prime specialization retains the ORIGINAL polynomial algebra structure. -/
def polynomialCoordinateAtPointAlg (S : Finset I)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S)) :
    Localization.Away (polynomialCoordinateProduct (K := K) S) →ₐ[MvPolynomial I K]
      projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x :=
  { polynomialCoordinateAtPoint S x hx with
    commutes' := polynomialCoordinateAtPoint_algebraMap S x hx }

/-- Original native module fractions specialize by their SAME actual original ring-fraction values. -/
def polynomialCoordinateModuleAtPoint (S : Finset I)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S)) :
    LocalizedModule (Submonoid.powers (polynomialCoordinateProduct (K := K) S)) (MvPolynomial I K)
      →ₗ[MvPolynomial I K] projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x :=
  (polynomialCoordinateAtPointAlg S x hx).toLinearMap.comp
    (polynomialCoordinateModuleLocalizationEquiv S).toLinearMap

omit [LinearOrder I] [Fintype I] in
/-- Every ORIGINAL polynomial is retained by the SAME original module-fraction specialization. -/
theorem polynomialCoordinateModuleAtPoint_comp (S : Finset I)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S)) :
    (polynomialCoordinateModuleAtPoint S x hx).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers (polynomialCoordinateProduct S)) (MvPolynomial I K)) =
      Algebra.linearMap (MvPolynomial I K)
        (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x) := by
  apply LinearMap.ext
  intro p
  change polynomialCoordinateAtPoint S x hx
      (polynomialCoordinateModuleLocalizationEquiv S (LocalizedModule.mk p 1)) = _
  rw [polynomialCoordinateModuleLocalizationEquiv_mk_one, polynomialCoordinateAtPoint_algebraMap]
  rfl

omit [LinearOrder I] [Fintype I] in
/-- The literal ORIGINAL divisor restriction commutes with EVERY original prime specialization. -/
theorem polynomialCoordinateModuleAtPoint_restriction {S T : Finset I} (hST : S ⊆ T)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) T))
    (z : LocalizedModule (Submonoid.powers (polynomialCoordinateProduct (K := K) S)) (MvPolynomial I K)) :
    polynomialCoordinateModuleAtPoint T x hx
      (actualLocalizedModuleDivisorRestriction (M := MvPolynomial I K)
        (polynomialCoordinateProduct S) (polynomialCoordinateProduct T)
        (polynomialCoordinateProduct_dvd_of_subset hST) z) =
      polynomialCoordinateModuleAtPoint S x
        ((Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset hST)) hx) z := by
  let hxS := (Proj.basicOpen_mono (MvPolynomial.homogeneousSubmodule I K) _ _
    (polynomialCoordinateProduct_dvd_of_subset hST)) hx
  have hunit : ∀ s : Submonoid.powers (polynomialCoordinateProduct (K := K) S),
      IsUnit (algebraMap (MvPolynomial I K)
        (Module.End (MvPolynomial I K) (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x)) s) := by
    intro s
    have hs : (s : MvPolynomial I K) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
      (Submonoid.powers_le.mpr ((Proj.mem_basicOpen _ _ _).mp hxS)) s.property
    exact IsLocalizedModule.map_units
      (Algebra.linearMap (MvPolynomial I K)
        (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x))
      (⟨s.val, hs⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)
  have heq : (polynomialCoordinateModuleAtPoint T x hx).comp
      (actualLocalizedModuleDivisorRestriction (M := MvPolynomial I K)
        (polynomialCoordinateProduct S) (polynomialCoordinateProduct T)
        (polynomialCoordinateProduct_dvd_of_subset hST)) = polynomialCoordinateModuleAtPoint S x hxS := by
    apply IsLocalizedModule.ext (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
      (LocalizedModule.mkLinearMap (Submonoid.powers (polynomialCoordinateProduct S)) (MvPolynomial I K)) hunit
    rw [LinearMap.comp_assoc, actualLocalizedModuleDivisorRestriction_comp,
      polynomialCoordinateModuleAtPoint_comp, polynomialCoordinateModuleAtPoint_comp]
  exact LinearMap.congr_fun heq z

omit [LinearOrder I] in
/-- Equality at ALL original primes is faithful on the SAME actual original homogeneous fraction piece. -/
theorem polynomialCoordinatePiece_eq_of_prime_values (k : ℕ) (S : Finset I) (i : I) (hi : i ∈ S)
    (z w : polynomialCoordinateHomogeneousPiece (K := K) (I := I) (k : ℤ) S)
    (h : ∀ (x : Proj (MvPolynomial.homogeneousSubmodule I K))
      (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S)),
      polynomialCoordinateModuleAtPoint S x hx z.val = polynomialCoordinateModuleAtPoint S x hx w.val) : z = w := by
  apply (polynomialTwistingCoordinatePieceEquiv k S i hi).symm.injective
  apply Subtype.ext
  funext x
  rw [polynomialTwistingCoordinatePieceEquiv_symm_eval, polynomialTwistingCoordinatePieceEquiv_symm_eval]
  exact h x.val x.property

/-- Genuine ORIGINAL twisting coordinate equivalences preserve EVERY original restriction,
even when different selected ORIGINAL coordinates are used on the two intersections. -/
theorem polynomialTwistingCoordinatePieceEquiv_restrict (k : ℕ) {S T : Finset I} (hST : S ⊆ T)
    (i j : I) (hi : i ∈ S) (hj : j ∈ T)
    (s : bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct S))) :
    homogeneousCoordinateSubsetRestriction (polynomialIntegralGrading (K := K) (I := I))
      (polynomialIntegralGrading (K := K) (I := I))
      (fun a => (MvPolynomial.X a : MvPolynomial I K)) polynomialCoordinate_X_degree hST (k : ℤ)
      (polynomialTwistingCoordinatePieceEquiv k S i hi s) =
    polynomialTwistingCoordinatePieceEquiv k T j hj
      ((projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).val.map
        (homOfLE (Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset hST))).op s) := by
  apply polynomialCoordinatePiece_eq_of_prime_values k T j hj
  intro x hx
  change polynomialCoordinateModuleAtPoint T x hx
      (actualLocalizedModuleDivisorRestriction (M := MvPolynomial I K)
        (polynomialCoordinateProduct S) (polynomialCoordinateProduct T)
        (polynomialCoordinateProduct_dvd_of_subset hST)
        (polynomialTwistingCoordinatePieceEquiv k S i hi s).val) = _
  rw [polynomialCoordinateModuleAtPoint_restriction hST x hx]
  change polynomialCoordinateAtPoint S x
      ((Proj.basicOpen_mono _ _ _ (polynomialCoordinateProduct_dvd_of_subset hST)) hx)
      (polynomialCoordinateModuleLocalizationEquiv S (polynomialTwistingCoordinatePieceEquiv k S i hi s).val) =
    polynomialCoordinateAtPoint T x hx
      (polynomialCoordinateModuleLocalizationEquiv T
        (polynomialTwistingCoordinatePieceEquiv k T j hj _).val)
  rw [polynomialTwistingCoordinatePieceEquiv_eval, polynomialTwistingCoordinatePieceEquiv_eval]
  rfl

end
end Hironaka.Geometry.ProperSteinProjectiveCech
