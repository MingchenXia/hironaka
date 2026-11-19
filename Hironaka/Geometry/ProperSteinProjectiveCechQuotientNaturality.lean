import Hironaka.Geometry.ProperSteinProjectiveCechQuotientEvaluation

/-! # Actual quotient regular restrictions commute with SAME original fractions at EVERY prime -/

universe u
open CategoryTheory AlgebraicGeometry
open Hironaka.Geometry.ProjectiveIdeal
namespace Hironaka.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K))

omit [Fintype I] in
/-- Actual original subset inclusion gives the original quotient basic-open inclusion. -/
theorem polynomialQuotientSubsetOpen_mono {S T : Finset I} (hST : S ⊆ T) :
    polynomialQuotientSubsetOpen J T ≤ polynomialQuotientSubsetOpen J S :=
  Proj.basicOpen_mono _ _ _ (map_dvd (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal))
    (homogeneousCoordinateSubsetProduct_dvd (fun i => (MvPolynomial.X i : MvPolynomial I K)) hST))

/-- Original quotient prime specialization retains the SAME actual quotient algebra structure. -/
def polynomialQuotientCoordinateAtPointAlg (S : Finset I) (x : polynomialQuotientScheme J)
    (hx : x ∈ polynomialQuotientSubsetOpen J S) :
    Localization.Away
        (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S))
      →ₐ[MvPolynomial I K ⧸ J.toIdeal] Localization x.asHomogeneousIdeal.toIdeal.primeCompl :=
  { polynomialQuotientCoordinateAtPoint J S x hx with
    commutes' := polynomialQuotientCoordinateAtPoint_algebraMap J S x hx }

/-- Actual quotient module fractions specialize by their SAME original quotient ring-fraction values. -/
def polynomialQuotientModuleAtPoint (S : Finset I) (x : polynomialQuotientScheme J)
    (hx : x ∈ polynomialQuotientSubsetOpen J S) :
    LocalizedModule (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
        (MvPolynomial I K ⧸ J.toIdeal) →ₗ[MvPolynomial I K]
      Localization x.asHomogeneousIdeal.toIdeal.primeCompl :=
  ((polynomialQuotientCoordinateAtPointAlg J S x hx).toLinearMap.restrictScalars (MvPolynomial I K)).comp
    (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)).toLinearMap

omit [LinearOrder I] [Fintype I] in
/-- The SAME actual specialization fixes EACH original quotient numerator over the original polynomial scalars. -/
theorem polynomialQuotientModuleAtPoint_comp (S : Finset I) (x : polynomialQuotientScheme J)
    (hx : x ∈ polynomialQuotientSubsetOpen J S) :
    (polynomialQuotientModuleAtPoint J S x hx).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
          (MvPolynomial I K ⧸ J.toIdeal)) =
      (Algebra.linearMap (MvPolynomial I K ⧸ J.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)).restrictScalars (MvPolynomial I K) := by
  apply LinearMap.ext
  intro q
  change polynomialQuotientCoordinateAtPoint J S x hx
    (algebraModuleAwayEquiv (A := MvPolynomial I K ⧸ J.toIdeal) (polynomialCoordinateProduct S)
      (LocalizedModule.mk q 1)) = _
  rw [algebraModuleAwayEquiv_mk_one, polynomialQuotientCoordinateAtPoint_algebraMap]
  rfl

omit [Fintype I] in
/-- Actual divisor restrictions commute with EVERY original full quotient-prime localization. -/
theorem polynomialQuotientModuleAtPoint_restriction {S T : Finset I} (hST : S ⊆ T)
    (x : polynomialQuotientScheme J) (hx : x ∈ polynomialQuotientSubsetOpen J T)
    (z : LocalizedModule (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
      (MvPolynomial I K ⧸ J.toIdeal)) :
    polynomialQuotientModuleAtPoint J T x hx
      (actualLocalizedModuleDivisorRestriction (M := MvPolynomial I K ⧸ J.toIdeal)
        (polynomialCoordinateProduct S) (polynomialCoordinateProduct T)
        (homogeneousCoordinateSubsetProduct_dvd (fun i => (MvPolynomial.X i : MvPolynomial I K)) hST) z) =
      polynomialQuotientModuleAtPoint J S x (polynomialQuotientSubsetOpen_mono J hST hx) z := by
  let hxS := polynomialQuotientSubsetOpen_mono J hST hx
  have hunit : ∀ s : Submonoid.powers (polynomialCoordinateProduct (K := K) S),
      IsUnit (algebraMap (MvPolynomial I K)
        (Module.End (MvPolynomial I K) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)) s) := by
    intro s
    have hs : algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) s.val ∈
        x.asHomogeneousIdeal.toIdeal.primeCompl := by
      obtain ⟨n, hn⟩ := s.property
      rw [← hn, map_pow]
      exact x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem ((Proj.mem_basicOpen _ _ _).mp hxS) n
    have hu := IsLocalization.map_units (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
      (⟨_, hs⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)
    change IsUnit (algebraMap (MvPolynomial I K ⧸ J.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
      (algebraMap (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) s.val)) at hu
    rw [← IsScalarTower.algebraMap_apply (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)] at hu
    have hu' := hu.map (Algebra.lmul (MvPolynomial I K)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)).toRingHom
    change IsUnit ((Algebra.lmul (MvPolynomial I K)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
        (algebraMap (MvPolynomial I K) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) s.val)) at hu'
    simpa only [AlgHom.commutes] using hu'
  have heq : (polynomialQuotientModuleAtPoint J T x hx).comp
      (actualLocalizedModuleDivisorRestriction (M := MvPolynomial I K ⧸ J.toIdeal)
        (polynomialCoordinateProduct S) (polynomialCoordinateProduct T)
        (homogeneousCoordinateSubsetProduct_dvd (fun i => (MvPolynomial.X i : MvPolynomial I K)) hST)) =
      polynomialQuotientModuleAtPoint J S x hxS := by
    apply IsLocalizedModule.ext (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
      (LocalizedModule.mkLinearMap (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
        (MvPolynomial I K ⧸ J.toIdeal)) hunit
    rw [LinearMap.comp_assoc, actualLocalizedModuleDivisorRestriction_comp,
      polynomialQuotientModuleAtPoint_comp, polynomialQuotientModuleAtPoint_comp]
  exact LinearMap.congr_fun heq z

/-- The SAME original quotient's actual regular-section comparison respects EVERY original restriction. -/
theorem polynomialQuotientRegularPieceEquiv_restrict {S T : Finset I} (hST : S ⊆ T)
    (hS : S.Nonempty) (hT : T.Nonempty) (z : polynomialQuotientCoordinatePiece J S) :
    (polynomialQuotientScheme J).presheaf.map (homOfLE (polynomialQuotientSubsetOpen_mono J hST)).op
      (polynomialQuotientRegularPieceEquiv J S hS z) =
      polynomialQuotientRegularPieceEquiv J T hT
        (homogeneousCoordinateSubsetRestriction (polynomialIntegralGrading (K := K) (I := I))
          (polynomialQuotientIntegralPiece J) (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree hST 0 z) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change ((polynomialQuotientRegularPieceEquiv J S hS z).val
    ⟨x.val, polynomialQuotientSubsetOpen_mono J hST x.property⟩).val = _
  rw [polynomialQuotientRegularPieceEquiv_eval, polynomialQuotientRegularPieceEquiv_eval]
  change polynomialQuotientModuleAtPoint J S x.val
      (polynomialQuotientSubsetOpen_mono J hST x.property) z.val =
    polynomialQuotientModuleAtPoint J T x.val x.property
      (actualLocalizedModuleDivisorRestriction (M := MvPolynomial I K ⧸ J.toIdeal)
        (polynomialCoordinateProduct S) (polynomialCoordinateProduct T)
        (homogeneousCoordinateSubsetProduct_dvd (fun i => (MvPolynomial.X i : MvPolynomial I K)) hST) z.val)
  exact (polynomialQuotientModuleAtPoint_restriction J hST x.val x.property z.val).symm

end
end Hironaka.Geometry.ProperSteinProjectiveCech
