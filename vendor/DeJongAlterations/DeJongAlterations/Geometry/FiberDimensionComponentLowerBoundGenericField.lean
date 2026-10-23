import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundConstructedProjection
import DeJongAlterations.Algebra.FunctionFieldDimensionGenericFiber

/-!
# Actual generic-point quasi-finiteness and the coefficient fraction field

The affine stalk comparison carries native scheme quasi-finiteness to the
actual localization algebra. The residue field of the zero prime is the
original domain's actual fraction field; no field quasi-finiteness certificate
is required from the caller.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped TensorProduct

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundGenericField

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual affine stalk comparison gives the native localization formulation. -/
theorem algebra_quasiFiniteAt_of_specMap
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (q : PrimeSpectrum A)
    (hq : (Spec.map (CommRingCat.ofHom (algebraMap R A))).QuasiFiniteAt q) :
    Algebra.QuasiFiniteAt R q.asIdeal := by
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  have hloc : Algebra.QuasiFinite (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) := by
    rw [← RingHom.quasiFinite_algebraMap]
    exact (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R A)) q)).mp hq
  let : Algebra.QuasiFinite (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) := hloc
  let : Algebra.QuasiFinite R (Localization.AtPrime (q.asIdeal.under R)) :=
    .of_isLocalization (q.asIdeal.under R).primeCompl
  exact .trans R (Localization.AtPrime (q.asIdeal.under R)) (Localization.AtPrime q.asIdeal)

/-- Generic scheme quasi-finiteness implies quasi-finiteness of the canonical
fraction field, here represented by the native zero-prime residue field. -/
theorem residueField_quasiFinite_of_generic_specMap
    (R A : Type u) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    (hq : (Spec.map (CommRingCat.ofHom (algebraMap R A))).QuasiFiniteAt
      (genericPoint (Spec (.of A)))) : Algebra.QuasiFinite R (⊥ : Ideal A).ResidueField := by
  have hbot : (Spec.map (CommRingCat.ofHom (algebraMap R A))).QuasiFiniteAt
      (⟨⊥, inferInstance⟩ : PrimeSpectrum A) := by
    have heq : (⊥ : PrimeSpectrum A) = ⟨⊥, inferInstance⟩ := PrimeSpectrum.ext rfl
    simpa only [genericPoint_eq_bot_of_affine, heq] using hq
  let : Algebra.QuasiFinite R (Localization.AtPrime (⊥ : Ideal A)) :=
    algebra_quasiFiniteAt_of_specMap R A ⟨⊥, inferInstance⟩ hbot
  exact .trans R (Localization.AtPrime (⊥ : Ideal A)) (⊥ : Ideal A).ResidueField


/-- Quasi-finiteness of an actual original coordinate projection at the generic
point bounds transcendence degree over the actual coefficient fraction field. -/
theorem generic_trdeg_le_of_quasiFinite_projection
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] (hinj : Function.Injective (algebraMap R A))
    (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] A)
    (hq : (Spec.map (CommRingCat.ofHom f.toRingHom)).QuasiFiniteAt
      (genericPoint (Spec (.of A)))) :
    letI := Algebra.FunctionFieldDimension.coefficientFractionAlgebra R A
      (⊥ : Ideal R).ResidueField (⊥ : Ideal A).ResidueField hinj
    Algebra.trdeg (⊥ : Ideal R).ResidueField (⊥ : Ideal A).ResidueField ≤ d := by
  let F := (⊥ : Ideal R).ResidueField
  let K := (⊥ : Ideal A).ResidueField
  let := Algebra.FunctionFieldDimension.coefficientFractionAlgebra R A F K hinj
  let := Algebra.FunctionFieldDimension.coefficientFractionScalarTower R A F K hinj
  have hfield : ((algebraMap A K).comp f.toRingHom).QuasiFinite := by
    let := f.toRingHom.toAlgebra
    have : Algebra.QuasiFinite (MvPolynomial (Fin d) R) K :=
      residueField_quasiFinite_of_generic_specMap (MvPolynomial (Fin d) R) A hq
    exact RingHom.quasiFinite_algebraMap.mpr this
  let g : MvPolynomial (Fin d) F →ₐ[F] K :=
    aeval (fun i ↦ algebraMap A K (f (X i)))
  have hsquare : g.toRingHom.comp (MvPolynomial.map (algebraMap R F)) =
      (algebraMap A K).comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change g (MvPolynomial.map (algebraMap R F) (C r)) =
        algebraMap A K (f (C r))
      rw [MvPolynomial.map_C]
      change g (algebraMap F (MvPolynomial (Fin d) F) (algebraMap R F r)) =
        algebraMap A K (f (algebraMap R (MvPolynomial (Fin d) R) r))
      rw [g.commutes, f.commutes]
      exact (IsScalarTower.algebraMap_apply R F K r).symm.trans
        (IsScalarTower.algebraMap_apply R A K r)
    · intro i
      change g (MvPolynomial.map (algebraMap R F) (X i)) =
        algebraMap A K (f (X i))
      simp [g]
  have hg : g.toRingHom.QuasiFinite := RingHom.QuasiFinite.of_comp (hsquare ▸ hfield)
  let := g.toRingHom.toAlgebra
  let : Algebra.QuasiFinite (MvPolynomial (Fin d) F) K := hg
  exact FiberDimensionComponentLowerBoundAlgebra.trdeg_le_of_quasiFinite_polynomial_algebra F K d


/-- Native generic-fiber ring dimension is bounded by an actual generic
quasi-finite original coordinate projection. -/
theorem genericFiber_ringKrullDim_le_of_quasiFinite_projection
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R A))
    (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] A)
    (hq : (Spec.map (CommRingCat.ofHom f.toRingHom)).QuasiFiniteAt
      (genericPoint (Spec (.of A)))) : ringKrullDim ((⊥ : Ideal R).Fiber A) ≤ d := by
  let F := (⊥ : Ideal R).ResidueField
  let K := (⊥ : Ideal A).ResidueField
  let := Algebra.FunctionFieldDimension.coefficientFractionAlgebra R A F K hinj
  let := Algebra.FunctionFieldDimension.genericTensorAlgebra R A F K hinj
  let := Algebra.FunctionFieldDimension.genericTensorScalarTowerLeft R A F K hinj
  let : IsDomain (F ⊗[R] A) :=
    Algebra.FunctionFieldDimension.genericTensor_isDomain R A F hinj
  let : IsFractionRing (F ⊗[R] A) K :=
    Algebra.FunctionFieldDimension.genericTensor_isFractionRing R A F K hinj
  obtain ⟨n, hdim, htr⟩ :=
    Algebra.FunctionFieldDimension.exists_dimension_and_trdeg F (F ⊗[R] A) K
  have hle := generic_trdeg_le_of_quasiFinite_projection R A hinj d f hq
  change Algebra.trdeg F K ≤ d at hle
  rw [htr] at hle
  have hnd : n ≤ d := by exact_mod_cast hle
  change ringKrullDim (F ⊗[R] A) ≤ d
  rw [hdim]
  exact_mod_cast hnd

/-- Every actual minimal fiber-prime quotient has dimension at least that of
the actual generic fiber ring, constructed from the original dominant map of domains. -/
theorem genericFiber_ringKrullDim_le_minimalPrime_quotient
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R A))
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber A)) [Q.IsPrime]
    (hmin : Q ∈ minimalPrimes (p.Fiber A)) :
    ringKrullDim ((⊥ : Ideal R).Fiber A) ≤ ringKrullDim (p.Fiber A ⧸ Q) := by
  obtain ⟨d, f, hdim, hq⟩ :=
    FiberDimensionComponentLowerBoundConstructedProjection.exists_generic_quasiFinite_polynomial_projection
      R A p Q hmin
  rw [hdim]
  exact genericFiber_ringKrullDim_le_of_quasiFinite_projection R A hinj d f hq

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundGenericField
