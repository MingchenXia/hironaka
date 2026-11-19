import Hironaka.Resolution.HironakaRelativeNormalIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The entire original zero-section local algebra and all its actual jets are unchanged.
This is intrinsic-invariant stabilization, not independence of a resolution algorithm. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaActualZeroSectionStabilization
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicPointJets

/-- The genuine zero-section ideal includes the WHOLE original ideal and all actual normal coordinates. -/
def actualZeroSectionIdeal (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.map (tangentPullback d t).toRingHom I ⊔ normalIdeal d t

/-- Actual original relative Hadamard division identifies BOTH entire trace-ideal directions. -/
theorem comap_planeTrace_eq_actualZeroSectionIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) :
    Ideal.comap (planeTrace d t).toRingHom I=actualZeroSectionIdeal d t I := by
  apply le_antisymm
  · intro g hg
    have htrace : planeTrace d t g ∈ I := hg
    obtain ⟨h,he⟩ := exists_relative_decomposition d t g
    rw [he]
    apply Ideal.add_mem
    · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem (tangentPullback d t).toRingHom htrace)
    · apply Ideal.mem_sup_right
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro g hg
      change planeTrace d t (tangentPullback d t g) ∈ I
      rwa [planeTrace_tangentPullback]
    · intro g hg
      change planeTrace d t g ∈ I
      have hz : planeTrace d t g=0 := by
        rw [normalIdeal_eq_ker_planeTrace] at hg
        exact hg
      rw [hz]
      exact I.zero_mem

/-- Every original ambient germ is tested by its SAME genuine entire plane trace. -/
theorem mem_actualZeroSectionIdeal_iff (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (g : HolGerm (ComplexModel (d+t))) :
    g ∈ actualZeroSectionIdeal d t I ↔ planeTrace d t g ∈ I := by
  rw [← comap_planeTrace_eq_actualZeroSectionIdeal]
  rfl

/-- Genuine trace surjectivity computes the entire ideal image without a generator certificate. -/
theorem map_actualZeroSectionIdeal_planeTrace (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) :
    Ideal.map (planeTrace d t).toRingHom (actualZeroSectionIdeal d t I)=I := by
  rw [← comap_planeTrace_eq_actualZeroSectionIdeal]
  exact Ideal.map_comap_of_surjective _ (planeTrace_surjective d t) I

private def traceQuotientMap (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel d) ⧸ I :=
  (Ideal.Quotient.mkₐ ℂ I).comp (planeTrace d t)

private theorem traceQuotientMap_surjective (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) : Function.Surjective (traceQuotientMap d t I) :=
  Ideal.Quotient.mk_surjective.comp (planeTrace_surjective d t)

private theorem ker_traceQuotientMap (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) :
    RingHom.ker (traceQuotientMap d t I).toRingHom=
      Ideal.comap (planeTrace d t).toRingHom I := by
  change Ideal.comap (planeTrace d t).toRingHom (RingHom.ker (Ideal.Quotient.mk I))=_
  rw [Ideal.mk_ker]

/-- The WHOLE actual original zero-section quotient is the original base quotient algebra. -/
def actualZeroSectionQuotientAlgEquiv (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸ actualZeroSectionIdeal d t I) ≃ₐ[ℂ]
      (HolGerm (ComplexModel d) ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq ℂ ((ker_traceQuotientMap d t I).trans
    (comap_planeTrace_eq_actualZeroSectionIdeal d t I)).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (traceQuotientMap_surjective d t I))

/-- The entire quotient equivalence retains the SAME actual original germ numerator and its true trace. -/
theorem actualZeroSectionQuotientAlgEquiv_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (g : HolGerm (ComplexModel (d+t))) :
    actualZeroSectionQuotientAlgEquiv d t I
      (Ideal.Quotient.mk (actualZeroSectionIdeal d t I) g)=
        Ideal.Quotient.mk I (planeTrace d t g) := rfl

/-- Every actual original maximal-power inverse image is the SAME stabilized ideal plus the true ambient power. -/
theorem comap_planeTrace_sup_maximalIdeal_pow (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (q : ℕ) :
    Ideal.comap (planeTrace d t).toRingHom
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q)=
        actualZeroSectionIdeal d t I ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
  have hmap : Ideal.map (planeTrace d t).toRingHom
      (actualZeroSectionIdeal d t I ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q)=
      I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q := by
    rw [Ideal.map_sup,map_actualZeroSectionIdeal_planeTrace,Ideal.map_pow,
      IsLocalRing.map_maximalIdeal_of_surjective _ (planeTrace_surjective d t)]
  rw [← hmap,Ideal.comap_map_of_surjective (planeTrace d t).toRingHom (planeTrace_surjective d t)]
  change (actualZeroSectionIdeal d t I ⊔
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q) ⊔
      RingHom.ker (planeTrace d t).toRingHom=_
  rw [← normalIdeal_eq_ker_planeTrace]
  apply sup_eq_left.mpr
  exact (show normalIdeal d t ≤ actualZeroSectionIdeal d t I from le_sup_right).trans le_sup_left

/-- Every true original jet is the SAME base jet as a whole complex algebra, including q=0. -/
def actualZeroSectionJetAlgEquiv (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) (q : ℕ) :
    (HolGerm (ComplexModel (d+t)) ⧸ (actualZeroSectionIdeal d t I ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q)) ≃ₐ[ℂ]
      (HolGerm (ComplexModel d) ⧸ (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q)) :=
  (Ideal.quotientEquivAlgOfEq ℂ
    ((ker_traceQuotientMap d t (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q)).trans
      (comap_planeTrace_sup_maximalIdeal_pow d t I q)).symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective
          (traceQuotientMap_surjective d t (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q)))

/-- The full q-jet equivalence keeps every actual numerator, rather than only an unspecified jet class. -/
theorem actualZeroSectionJetAlgEquiv_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    actualZeroSectionJetAlgEquiv d t I q
      (Ideal.Quotient.mk (actualZeroSectionIdeal d t I ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q) g)=
          Ideal.Quotient.mk (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ q)
            (planeTrace d t g) := rfl

/-- ALL existing original intrinsic HS values are unchanged by the genuine zero-section embedding. -/
theorem hilbertSamuelValue_actualZeroSectionIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (ℓ : ℕ) :
    hilbertSamuelValue (actualZeroSectionIdeal d t I) ℓ=hilbertSamuelValue I ℓ :=
  (actualZeroSectionJetAlgEquiv d t I (ℓ+1)).toLinearEquiv.finrank_eq

end
end Hironaka.HironakaActualZeroSectionStabilization
