import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundGenericField

/-!
# Every component of every actual affine fiber satisfies the generic lower bound

The actual tensor spectrum comparison and native minimal-prime classification
translate the proved algebra inequality to the literal scheme-theoretic fibers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundAffine

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native quotient spectrum identifies the actual zero locus with its quotient dimension. -/
theorem topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient
    (B : Type u) [CommRing B] (Q : Ideal B) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (Q : Set B)) = ringKrullDim (B ⧸ Q) := by
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk Q)) =
      PrimeSpectrum.zeroLocus (Q : Set B) := by
    exact (range_comap_of_surjective (B ⧸ Q) (Ideal.Quotient.mk Q)
      Ideal.Quotient.mk_surjective).trans
        (congrArg (fun J : Ideal B ↦ PrimeSpectrum.zeroLocus (J : Set B)) (Ideal.mk_ker))
  let e : PrimeSpectrum (B ⧸ Q) ≃ₜ PrimeSpectrum.zeroLocus (Q : Set B) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm.trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (B ⧸ Q))

/-- The actual scheme fiber dimension is that of its actual native tensor coordinate ring. -/
theorem fiberDimension_specMap_eq_ringKrullDim
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (p : PrimeSpectrum R) :
    FiberDimension.fiberDimension (Spec.map (CommRingCat.ofHom (algebraMap R A))) p =
      ringKrullDim (p.asIdeal.Fiber A) := by
  let e := Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R A p)
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (p.asIdeal.Fiber A))

/-- The generic tensor dimension bounds every actual component of a special tensor spectrum. -/
theorem genericFiber_ringKrullDim_le_componentDimension
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R A)) (p : Ideal R) [p.IsPrime]
    (T : Set (PrimeSpectrum (p.Fiber A))) (hT : T ∈ irreducibleComponents (PrimeSpectrum (p.Fiber A))) :
    ringKrullDim ((⊥ : Ideal R).Fiber A) ≤ topologicalKrullDim T := by
  have hm := hT
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes (p.Fiber A)] at hm
  obtain ⟨Q, hQ, hQT⟩ := hm
  let : Q.IsPrime := hQ.isPrime
  have hle := FiberDimensionComponentLowerBoundGenericField.genericFiber_ringKrullDim_le_minimalPrime_quotient
    R A hinj p Q hQ
  change PrimeSpectrum.zeroLocus (Q : Set (p.Fiber A)) = T at hQT
  rw [← hQT, topologicalKrullDim_zeroLocus_eq_ringKrullDim_quotient]
  exact hle

/-- The full native componentwise generic lower bound for an actual injective
finite-type map of domains, in every relative dimension. -/
theorem everyFiberComponentDimensionGEGeneric_specMap
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R A)) :
    FiberDimension.EveryFiberComponentDimensionGEGeneric
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  intro s Z hZ
  let e := (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R A s)).hom.homeomorph
  let T : Set (PrimeSpectrum (s.asIdeal.Fiber A)) := e.symm ⁻¹' Z
  have hT : T ∈ irreducibleComponents (PrimeSpectrum (s.asIdeal.Fiber A)) := by
    apply preimage_mem_irreducibleComponents hZ e.symm.isOpenEmbedding
    obtain ⟨z, hz⟩ := hZ.1.nonempty
    exact ⟨z, hz, e z, e.symm_apply_apply z⟩
  let eZ : T ≃ₜ Z := e.symm.isEmbedding.homeomorphOfSubsetRange
    (fun z _ ↦ e.symm.surjective z)
  rw [genericPoint_eq_bot_of_affine, fiberDimension_specMap_eq_ringKrullDim]
  exact (genericFiber_ringKrullDim_le_componentDimension R A hinj s.asIdeal T hT).trans
    (IsHomeomorph.topologicalKrullDim_eq _ eZ.isHomeomorph).le

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundAffine
