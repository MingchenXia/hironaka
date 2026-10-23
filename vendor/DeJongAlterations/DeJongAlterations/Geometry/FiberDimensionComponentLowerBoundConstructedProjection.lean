import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundPolynomialBaseChange
import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundPrimeQuotient

/-!
# Actual quasi-finite coordinate projections constructed from minimal fiber primes

The original algebra supplies all coordinates. Finite normalization of the
actual prime fiber quotient proves quasi-finiteness at the original source
point, by the actual polynomial coefficient pullback and fiber isomorphisms.
For a domain source the actual open quasi-finite locus contains its generic point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped TensorProduct

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundConstructedProjection

open FiberDimensionComponentLowerBoundCoordinates
  FiberDimensionComponentLowerBoundPolynomialBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

/-- Original finite type constructs a relative polynomial projection quasi-finite at
the original point of an actual minimal fiber prime, with computed component dimension. -/
theorem exists_quasiFinite_polynomial_projection (p : Ideal R) [p.IsPrime]
    (Q : Ideal (p.Fiber A)) [Q.IsPrime] (hmin : Q ∈ minimalPrimes (p.Fiber A)) :
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] A),
      ringKrullDim (p.Fiber A ⧸ Q) = d ∧
      (Spec.map (CommRingCat.ofHom f.toRingHom)).QuasiFiniteAt
        ((⟨Q, inferInstance⟩ : PrimeSpectrum (p.Fiber A)).comap
          Algebra.TensorProduct.includeRight.toRingHom) := by
  obtain ⟨d, f, g, hg, hfin, hdim, hcomp⟩ :=
    exists_lifted_finite_normalization_coordinates R A p Q
  let B : Type u := p.Fiber A
  let C : Type u := B ⧸ Q
  let : CommRing B := inferInstance
  let : CommRing C := inferInstance
  let : Algebra p.ResidueField C := inferInstance
  let α : MvPolynomial (Fin d) p.ResidueField →ₐ[p.ResidueField] B :=
    coefficientMap R p.ResidueField A d f
  have hvar (i : Fin d) : g (X i) = fiberQuotientMap R A p Q (f (X i)) := by
    have hv := DFunLike.congr_fun hcomp (X i)
    change g (MvPolynomial.map (algebraMap R p.ResidueField) (X i)) =
      fiberQuotientMap R A p Q (f (X i)) at hv
    simpa only [MvPolynomial.map_X] using hv
  have hquot : (Ideal.Quotient.mkₐ p.ResidueField Q).comp α = g := by
    ext i
    change Ideal.Quotient.mk Q (α (X i)) = g (X i)
    have hi := (hvar i).symm
    change Ideal.Quotient.mk Q (1 ⊗ₜ[R] f (X i)) = g (X i) at hi
    have hα : α (X i) = 1 ⊗ₜ[R] f (X i) := by
      exact MvPolynomial.aeval_X _ _
    rw [hα]
    exact hi
  have hfinα : RingHom.Finite (A := MvPolynomial (Fin d) p.ResidueField) (B := C)
      ((Ideal.Quotient.mk Q).comp α.toRingHom) := by
    have heq : (Ideal.Quotient.mk Q).comp α.toRingHom = g.toRingHom :=
      congrArg AlgHom.toRingHom hquot
    rw [heq]
    exact hfin
  have hq := FiberDimensionComponentLowerBoundPrimeQuotient.quasiFiniteAt_of_finite_minimalPrime_quotient
    p.ResidueField B d α Q hmin hfinα
  have hft : f.toRingHom.FiniteType := by
    have h : (algebraMap R A).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
    rw [← f.comp_algebraMap] at h
    exact h.of_comp_finiteType
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hft
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom α.toRingHom)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (coefficientMap_isPullback R p.ResidueField A d f) inferInstance
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (MvPolynomial.map
      (algebraMap R p.ResidueField) : MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) p.ResidueField))) :=
    polynomial_residueField_coefficient_isPreimmersion R d p
  exact ⟨d, f, hdim,
    FiberDimensionComponentLowerBoundBaseChange.quasiFiniteAt_of_isPullback_of_preimmersion
      (coefficientMap_isPullback R p.ResidueField A d f) ⟨Q, inferInstance⟩ hq⟩

/-- The same internally constructed original polynomial projection is quasi-finite
at the actual generic source point when the original source algebra is a domain. -/
theorem exists_generic_quasiFinite_polynomial_projection [IsDomain A]
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber A)) [Q.IsPrime]
    (hmin : Q ∈ minimalPrimes (p.Fiber A)) :
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] A),
      ringKrullDim (p.Fiber A ⧸ Q) = d ∧
      (Spec.map (CommRingCat.ofHom f.toRingHom)).QuasiFiniteAt (genericPoint (Spec (.of A))) := by
  obtain ⟨d, f, hdim, hq⟩ := exists_quasiFinite_polynomial_projection R A p Q hmin
  let π := Spec.map (CommRingCat.ofHom f.toRingHom)
  have hft : f.toRingHom.FiniteType := by
    have h : (algebraMap R A).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
    rw [← f.comp_algebraMap] at h
    exact h.of_comp_finiteType
  have : LocallyOfFiniteType π := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hft
  exact ⟨d, f, hdim,
    ((genericPoint_spec (Spec (.of A))).mem_open_set_iff π.quasiFiniteLocus.isOpen).mpr
      ⟨_, Set.mem_univ _, hq⟩⟩

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundConstructedProjection
