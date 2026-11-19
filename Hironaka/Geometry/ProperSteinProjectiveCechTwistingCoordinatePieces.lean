import Hironaka.Geometry.ProperSteinProjectiveCechNativeAway

/-!
# Actual original twisting sections on EVERY nonempty original coordinate intersection

Literal original numerator/denominator arithmetic derives the actual shifted
module equivalence. Native Proj regular sections and the internally proved
coordinate frame then give the actual twisting-section comparison.
No domain, generic zero prime, or desired local comparison is assumed.
-/

universe u
open CategoryTheory AlgebraicGeometry
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplication by the ORIGINAL coordinate power shifts the SAME actual literal fraction degree. -/
def polynomialCoordinateModuleMultiply (k : ℕ) (S : Finset I) (i : I) :
    polynomialCoordinateHomogeneousPiece (K := K) (I := I) 0 S →ₗ[K]
      polynomialCoordinateHomogeneousPiece (K := K) (I := I) (k : ℤ) S where
  toFun z := ⟨((MvPolynomial.X i : MvPolynomial I K) ^ k) • z.val, by
    obtain ⟨n, p, hp, he⟩ := z.property
    refine ⟨n, (MvPolynomial.X i : MvPolynomial I K) ^ k * p, ?_, ?_⟩
    · have hx : (MvPolynomial.X i : MvPolynomial I K) ^ k ∈ polynomialIntegralGrading (k : ℤ) := by
        simpa only [nsmul_eq_mul, mul_one] using
          SetLike.pow_mem_graded k (polynomialCoordinate_X_degree (K := K) i)
      simpa only [zero_add] using SetLike.mul_mem_graded hx hp
    · rw [← he, LocalizedModule.smul'_mk]
      rfl⟩
  map_add' z w := by
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' r z := by
    apply Subtype.ext
    exact smul_comm _ _ _

omit [LinearOrder I] [Fintype I] in
/-- If the ORIGINAL coordinate is selected, original literal division gives BOTH inverse identities. -/
theorem polynomialCoordinateModuleMultiply_bijective (k : ℕ) (S : Finset I) (i : I) (hi : i ∈ S) :
    Function.Bijective (polynomialCoordinateModuleMultiply (K := K) k S i) := by
  classical
  constructor
  · intro z w h
    apply Subtype.ext
    apply (polynomialCoordinateModuleLocalizationEquiv S).injective
    have hu : IsUnit (algebraMap (MvPolynomial I K)
        (Localization.Away (polynomialCoordinateProduct (K := K) S)) (MvPolynomial.X i)) :=
      isUnit_of_dvd_unit
        (map_dvd (algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct (K := K) S)))
          (Finset.dvd_prod_of_mem (MvPolynomial.X : I → MvPolynomial I K) hi))
        (IsLocalization.Away.algebraMap_isUnit (polynomialCoordinateProduct (K := K) S))
    have h' := congrArg (polynomialCoordinateModuleLocalizationEquiv S) (congrArg Subtype.val h)
    change (polynomialCoordinateModuleLocalizationEquiv S)
        (((MvPolynomial.X i : MvPolynomial I K) ^ k) • z.val) =
      (polynomialCoordinateModuleLocalizationEquiv S)
        (((MvPolynomial.X i : MvPolynomial I K) ^ k) • w.val) at h'
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul] at h'
    exact (hu.pow k).mul_left_cancel (by
      simpa only [Algebra.smul_def, map_pow] using h')
  · intro z
    obtain ⟨n, p, hp, he⟩ := z.property
    let g : MvPolynomial I K := polynomialCoordinateProduct (K := K) (S.erase i)
    have hfactor : MvPolynomial.X i * g = polynomialCoordinateProduct (K := K) S :=
      Finset.mul_prod_erase S (MvPolynomial.X : I → MvPolynomial I K) hi
    have hcard : (S.card : ℤ) = ((S.erase i).card : ℤ) + 1 := by
      exact_mod_cast (Finset.card_erase_add_one hi).symm
    have hpn : p * g ^ k ∈ polynomialIntegralGrading
        (0 + ((n + k : ℕ) : ℤ) * (S.card : ℤ)) := by
      have hg : g ^ k ∈ polynomialIntegralGrading ((k : ℤ) * ((S.erase i).card : ℤ)) := by
        simpa only [nsmul_eq_mul] using
          SetLike.pow_mem_graded k (polynomialCoordinateProduct_degree (K := K) (S.erase i))
      convert SetLike.mul_mem_graded hp hg using 1
      congr 1
      rw [hcard, Nat.cast_add]
      ring
    let q : polynomialCoordinateHomogeneousPiece (K := K) (I := I) 0 S :=
      ⟨LocalizedModule.mk (p * g ^ k)
        (homogeneousPowerDenominator (polynomialCoordinateProduct (K := K) S) (n + k)),
        n + k, p * g ^ k, hpn, rfl⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change ((MvPolynomial.X i : MvPolynomial I K) ^ k) • LocalizedModule.mk (p * g ^ k)
      (homogeneousPowerDenominator (polynomialCoordinateProduct (K := K) S) (n + k)) = z.val
    rw [← he, LocalizedModule.smul'_mk]
    change LocalizedModule.mk ((MvPolynomial.X i : MvPolynomial I K) ^ k * (p * g ^ k)) _ = _
    have hnum : (MvPolynomial.X i : MvPolynomial I K) ^ k * (p * g ^ k) = polynomialCoordinateProduct (K := K) S ^ k * p := by
      rw [← hfactor, mul_pow]
      ring
    rw [hnum]
    have hden : homogeneousPowerDenominator (polynomialCoordinateProduct (K := K) S) (n + k) =
        homogeneousPowerDenominator (polynomialCoordinateProduct (K := K) S) k *
          homogeneousPowerDenominator (polynomialCoordinateProduct (K := K) S) n := by
      apply Subtype.ext
      change polynomialCoordinateProduct (K := K) S ^ (n + k) =
        polynomialCoordinateProduct (K := K) S ^ k * polynomialCoordinateProduct (K := K) S ^ n
      rw [Nat.add_comm, pow_add]
    rw [hden]
    exact LocalizedModule.mk_cancel_common_left
      (homogeneousPowerDenominator (polynomialCoordinateProduct (K := K) S) k)
      (homogeneousPowerDenominator (polynomialCoordinateProduct (K := K) S) n) p

/-- The SAME actual literal coordinate localization has its internally derived shifted degree equivalence. -/
def polynomialCoordinateModuleMultiplyEquiv (k : ℕ) (S : Finset I) (i : I) (hi : i ∈ S) :
    polynomialCoordinateHomogeneousPiece (K := K) (I := I) 0 S ≃ₗ[K]
      polynomialCoordinateHomogeneousPiece (K := K) (I := I) (k : ℤ) S :=
  LinearEquiv.ofBijective (polynomialCoordinateModuleMultiply k S i)
    (polynomialCoordinateModuleMultiply_bijective k S i hi)

/-- Native ORIGINAL Proj basic-open sections retain the SAME actual polynomial constant action. -/
def polynomialNativeAwayBasicOpenEquiv (S : Finset I) (hS : S.Nonempty) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K)
        (polynomialCoordinateProduct (K := K) S) ≃ₐ[K]
      Γ(Proj (MvPolynomial.homogeneousSubmodule I K),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct (K := K) S)) := by
  let e := (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule I K)
    (polynomialCoordinateProduct (K := K) S) (polynomialCoordinateProduct_natDegree S)
      (Finset.card_pos.mpr hS)).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro r
  apply Subtype.ext
  funext x
  rfl

/-- Actual ORIGINAL twisting sections on EVERY original nonempty coordinate intersection
are the SAME literal integral-degree coordinate fraction module. -/
def polynomialTwistingCoordinatePieceEquiv (k : ℕ) (S : Finset I) (i : I) (hi : i ∈ S) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct (K := K) S)) ≃ₗ[K]
      polynomialCoordinateHomogeneousPiece (K := K) (I := I) (k : ℤ) S :=
  (LinearEquiv.restrictScalars K (projectiveTwistingChartSectionsFrame
    (MvPolynomial.homogeneousSubmodule I K) k
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (polynomialCoordinateProduct (K := K) S))
    (Proj.basicOpen_mono _ _ _ (Finset.dvd_prod_of_mem (MvPolynomial.X : I → MvPolynomial I K) hi)))).trans
      (((polynomialNativeAwayBasicOpenEquiv S ⟨i, hi⟩).symm.toLinearEquiv.trans
        (polynomialNativeAwayModuleEquiv S)).trans (polynomialCoordinateModuleMultiplyEquiv k S i hi))

end
end Hironaka.Geometry.ProperSteinProjectiveCech
