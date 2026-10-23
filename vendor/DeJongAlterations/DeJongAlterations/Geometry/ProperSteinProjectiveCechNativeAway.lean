import DeJongAlterations.Geometry.ProperSteinProjectiveCechTwistingCoefficients
import DeJongAlterations.Geometry.ProperSteinProjectiveCechPolynomialLocalization

/-!
# Actual native homogeneous Away rings and the SAME integral degree-zero module

All objects and proofs use native Mathlib and owned DeJongAlterations modules.
Original polynomial numerators, actual coordinate-product denominators and
original coefficient actions are retained, including rings with zero divisors.
-/

universe u
open CategoryTheory AlgebraicGeometry
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [LinearOrder I] in
/-- The SAME original polynomial homogeneous degree is retained by the natural-to-integer cast. -/
theorem polynomialNatIntegralHomogeneous_iff (p : MvPolynomial I K) (n : ℕ) :
    p ∈ MvPolynomial.homogeneousSubmodule I K n ↔
      p ∈ polynomialIntegralGrading (n : ℤ) := by
  constructor
  · intro hp d hd
    have h := hp hd
    change Finsupp.weight (1 : I → ℕ) d = n at h
    change Finsupp.weight (fun _ : I => (1 : ℤ)) d = (n : ℤ)
    rw [Finsupp.weight_eq_sum] at h ⊢
    simp only [Pi.one_apply, nsmul_eq_mul, mul_one] at h ⊢
    exact_mod_cast h
  · intro hp d hd
    have h := hp hd
    change Finsupp.weight (fun _ : I => (1 : ℤ)) d = (n : ℤ) at h
    change Finsupp.weight (1 : I → ℕ) d = n
    rw [Finsupp.weight_eq_sum] at h ⊢
    simp only [Pi.one_apply, nsmul_eq_mul, mul_one] at h ⊢
    exact_mod_cast h

omit [LinearOrder I] [Fintype I] in
/-- The ORIGINAL selected-coordinate product has its actual natural homogeneous degree. -/
theorem polynomialCoordinateProduct_natDegree (S : Finset I) :
    polynomialCoordinateProduct (K := K) S ∈ MvPolynomial.homogeneousSubmodule I K S.card := by
  simpa [polynomialCoordinateProduct] using
    SetLike.prod_mem_graded (MvPolynomial.homogeneousSubmodule I K)
      (fun _ : I => (1 : ℕ)) (fun i => (MvPolynomial.X i : MvPolynomial I K))
      (F := S) (fun i _ => MvPolynomial.isHomogeneous_X K i)

omit [LinearOrder I] [Fintype I] in
/-- Native ring/module localization comparison retains the SAME original literal fraction. -/
theorem polynomialCoordinateModuleLocalizationEquiv_mk (S : Finset I)
    (p : MvPolynomial I K) (s : Submonoid.powers (polynomialCoordinateProduct (K := K) S)) :
    polynomialCoordinateModuleLocalizationEquiv S (LocalizedModule.mk p s) =
      Localization.mk p s := by
  apply (IsLocalization.map_units (Localization.Away (polynomialCoordinateProduct (K := K) S)) s).mul_right_cancel
  have hmul : (s : MvPolynomial I K) • LocalizedModule.mk p s =
      (LocalizedModule.mk p 1 : LocalizedModule
        (Submonoid.powers (polynomialCoordinateProduct S)) (MvPolynomial I K)) := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel s p
  have h := congrArg (polynomialCoordinateModuleLocalizationEquiv (K := K) S) hmul
  rw [LinearEquiv.map_smul, polynomialCoordinateModuleLocalizationEquiv_mk_one] at h
  have he : Localization.mk p s *
      algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S)) s.val =
        algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S)) p := by
    simpa only [Localization.mk_eq_mk'] using
      IsLocalization.mk'_spec (Localization.Away (polynomialCoordinateProduct S)) p s
  calc
    _ = algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S)) p := by
      simpa only [Algebra.smul_def, mul_comm] using h
    _ = _ := he.symm

/-- Actual native homogeneous Away elements retain their SAME original ordinary localization values. -/
def polynomialNativeAwayToOrdinary (S : Finset I) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S) →ₗ[K]
      Localization.Away (polynomialCoordinateProduct (K := K) S) where
  toFun z := z.val
  map_add' z w := HomogeneousLocalization.val_add z w
  map_smul' r z := by
    rw [Algebra.smul_def, HomogeneousLocalization.val_mul,
      homogeneousPolynomialLocalization_algebraMap_val, Algebra.smul_def]
    rfl

/-- Every ORIGINAL native homogeneous Away value lies in the SAME integral degree-zero module. -/
def polynomialNativeAwayToModule (S : Finset I) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S) →ₗ[K]
      polynomialCoordinateHomogeneousPiece (K := K) (I := I) 0 S :=
  ((((polynomialCoordinateModuleLocalizationEquiv S).symm.restrictScalars K).toLinearMap).comp
    (polynomialNativeAwayToOrdinary S)).codRestrict _ (by
      intro z
      obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
        (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct_natDegree S) z
      refine ⟨n, p, ?_, ?_⟩
      · have h := (polynomialNatIntegralHomogeneous_iff p (n • S.card)).mp hp
        simpa [nsmul_eq_mul] using h
      · apply (polynomialCoordinateModuleLocalizationEquiv S).injective
        change (polynomialCoordinateModuleLocalizationEquiv S)
            (LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n)) =
          (polynomialCoordinateModuleLocalizationEquiv S)
            ((polynomialCoordinateModuleLocalizationEquiv S).symm
              (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule I K)
                (polynomialCoordinateProduct_natDegree S) n p hp).val)
        rw [LinearEquiv.apply_symm_apply, polynomialCoordinateModuleLocalizationEquiv_mk]
        rfl)

omit [LinearOrder I] in
/-- The ORIGINAL literal module piece is exactly the native homogeneous Away ring, internally. -/
theorem polynomialNativeAwayToModule_bijective (S : Finset I) :
    Function.Bijective (polynomialNativeAwayToModule (K := K) S) := by
  constructor
  · intro z w h
    apply HomogeneousLocalization.val_injective
    apply (polynomialCoordinateModuleLocalizationEquiv S).symm.injective
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨n, p, hp, he⟩ := z.property
    have hpn : p ∈ MvPolynomial.homogeneousSubmodule I K (n • S.card) :=
      (polynomialNatIntegralHomogeneous_iff p (n • S.card)).mpr (by
        simpa [nsmul_eq_mul] using hp)
    refine ⟨HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct_natDegree S) n p hpn, ?_⟩
    apply Subtype.ext
    change (polynomialCoordinateModuleLocalizationEquiv S).symm _ = z.val
    rw [← he]
    apply (polynomialCoordinateModuleLocalizationEquiv S).injective
    rw [LinearEquiv.apply_symm_apply, polynomialCoordinateModuleLocalizationEquiv_mk]
    rfl

/-- The actual native original homogeneous Away ring is the SAME actual degree-zero fraction module. -/
def polynomialNativeAwayModuleEquiv (S : Finset I) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K)
      (polynomialCoordinateProduct (K := K) S) ≃ₗ[K]
      polynomialCoordinateHomogeneousPiece (K := K) (I := I) 0 S :=
  LinearEquiv.ofBijective (polynomialNativeAwayToModule S) (polynomialNativeAwayToModule_bijective S)

end
end DeJongAlterations.Geometry.ProperSteinProjectiveCech
