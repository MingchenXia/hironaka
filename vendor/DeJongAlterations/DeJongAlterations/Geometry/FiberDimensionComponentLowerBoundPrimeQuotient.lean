import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundDescent
import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundCoordinates

/-!
# Actual polynomial quasi-finiteness from finite normalization of a minimal-prime quotient

The quotient's actual spectrum is the native integral irreducible component.
Its finite projection descends on its actual nonempty open part, computing
quasi-finiteness at the original minimal-prime point of the polynomial map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundPrimeQuotient

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual finite quotient normalization at a minimal prime makes the original polynomial
spectrum projection quasi-finite there; no quasi-finite-point output is a premise. -/
theorem quasiFiniteAt_of_finite_minimalPrime_quotient
    (k B : Type u) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (d : ℕ) (α : MvPolynomial (Fin d) k →ₐ[k] B) (Q : Ideal B) [Q.IsPrime]
    (hmin : Q ∈ minimalPrimes B)
    (hfin : ((Ideal.Quotient.mk Q).comp α.toRingHom).Finite) :
    (Spec.map (CommRingCat.ofHom α.toRingHom)).QuasiFiniteAt ⟨Q, inferInstance⟩ := by
  let P := MvPolynomial (Fin d) k
  let C := B ⧸ Q
  let π : Spec (.of B) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom α.toRingHom)
  let i : Spec (.of C) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q))
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hft : α.toRingHom.FiniteType := by
    have h : (algebraMap k B).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
    rw [← α.comp_algebraMap] at h
    exact h.of_comp_finiteType
  have : LocallyOfFiniteType π := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hft
  have hcomp : i ≫ π = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk Q).comp α.toRingHom)) := by
    dsimp only [i, π]
    rw [← Spec.map_comp]
    rfl
  have : IsFinite (i ≫ π) := by
    rw [hcomp]
    exact (IsFinite.SpecMap_iff _).mpr hfin
  have hrange : Set.range i = PrimeSpectrum.zeroLocus (Q : Set B) := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk Q)) = _
    have hker : RingHom.ker (Ideal.Quotient.mk Q) = Q := Ideal.mk_ker
    exact (range_comap_of_surjective C (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective).trans
      (congrArg (fun J : Ideal B => PrimeSpectrum.zeroLocus (J : Set B)) hker)
  have hcomponent : Set.range i ∈ irreducibleComponents (Spec (.of B)) := by
    rw [hrange]
    exact PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
      (by simpa only [Ideal.IsPrime.radical] using hmin)
  have hpoint : i (genericPoint (Spec (.of C))) = (⟨Q, inferInstance⟩ : PrimeSpectrum B) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk Q) ⊥ = Q
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hq := FiberDimensionComponentLowerBoundDescent.quasiFiniteAt_genericPoint_of_finite_component
    i π hcomponent
  simpa only [hpoint] using hq

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundPrimeQuotient
