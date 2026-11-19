import Hironaka.Resolution.Algebraic.ActualDescendedHistorySmoothEndpoint
import Hironaka.Algebra.RegularSmooth.SingularLocus
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ReducedComponents
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Glue.Product

/-!
# Genuine ORIGINAL singular-ideal applicability on the SAME native endpoint

Source-first proof: `actual-original-sing-ideal-nonzero-20261102.tex`.
An actual original Cartier subideal survives the actual separation blowup
and the entire SAME native history; no smooth-centre premise is needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualOriginalSingIdealNonzero

noncomputable section

/-- Finite prime avoidance in the actual reduced ring produces a genuine regular element. -/
theorem exists_regular_element_of_avoids_minimalPrimes (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsReduced R] (I : Ideal R)
    (hI : ∀ p ∈ minimalPrimes R, ¬ I ≤ p) :
    ∃ t ∈ I, t ∈ nonZeroDivisors R := by
  classical
  have hnot : ¬ (I : Set R) ⊆ ⋃ p ∈ minimalPrimes R, (p : Set R) := by
    intro h
    obtain ⟨p,hp,hIp⟩ := (Ideal.subset_union_prime_finite
      (minimalPrimes.finite_of_isNoetherianRing R) (⊥ : Ideal R) (⊥ : Ideal R)
      (fun p hp _ _ => hp.isPrime)).mp h
    exact hI p hp hIp
  obtain ⟨t,htI,ht⟩ := Set.not_subset.mp hnot
  refine ⟨t,htI,mem_nonZeroDivisors_iff_right.mpr ?_⟩
  intro x hxt
  have hx : x ∈ sInf (minimalPrimes R) := by
    apply Ideal.mem_sInf.mpr
    intro p hp
    have htp : t ∉ p := fun h => ht (Set.mem_iUnion₂.mpr ⟨p,hp,h⟩)
    exact (hp.isPrime.mem_or_mem (hxt ▸ p.zero_mem)).resolve_right htp
  simpa only [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced, Ideal.mem_bot] using hx

private theorem support_specIdealSheaf {R : Type u} [CommRing R] (I : Ideal R) :
    ((specIdealSheaf I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [specIdealSheaf, coe_support_ofIdealTop, Spec_zeroLocus]
  change PrimeSpectrum.zeroLocus
    (((I.map (Scheme.ΓSpecIso (.of R)).inv.hom).comap
      (Scheme.ΓSpecIso (.of R)).inv.hom) : Set R) = _
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _)]

/-- The genuine ORIGINAL singular ideal contains an internally constructed actual Cartier ideal. -/
theorem exists_invertible_le_original_singIdeal (R : Type u) [CommRing R]
    (k : Type u) [Field k] [PerfectField k] [Algebra k R] [Algebra.FiniteType k R] [IsReduced R] :
    ∃ K : (Spec (.of R)).IdealSheafData, K.IsInvertible ∧ K ≤ (Spec (.of R)).singIdeal := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let f := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let : (Spec (.of R)).Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType (Spec (.of R) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType f
    infer_instance
  let J := (Spec (.of R)).singIdeal
  let c := (Scheme.ΓSpecIso (.of R)).inv.hom
  let I := (J.ideal ⟨⊤,isAffineOpen_top _⟩).comap c
  have hJ : specIdealSheaf I = J := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [specIdealSheaf_ideal_top]
    exact Ideal.map_comap_of_surjective c
      (ConcreteCategory.bijective_of_isIso (C := CommRingCat) (Scheme.ΓSpecIso (.of R)).inv).2 _
  have hI : ∀ p ∈ minimalPrimes R, ¬ I ≤ p := by
    intro p hp hIp
    have : p.IsPrime := hp.isPrime
    let η : Spec (.of R) := ⟨p,hp.isPrime⟩
    let C : Set (Spec (.of R)) := PrimeSpectrum.zeroLocus (p : Set R)
    have hC : C ∈ irreducibleComponents (Spec (.of R)) := by
      change PrimeSpectrum.zeroLocus (p : Set R) ∈ irreducibleComponents (PrimeSpectrum R)
      apply PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
      simpa only [Ideal.IsPrime.radical] using hp
    obtain ⟨η',hη',hsm⟩ := Hironaka.Resolution.exists_isGenericPoint_mem_smoothLocus
      (X := Spec (.of R)) (k := k) C hC
    have hη : IsGenericPoint η C := PrimeSpectrum.closure_singleton η
    have heq : η' = η := hη'.eq hη
    have hsing : η ∈ J.support := by
      rw [← hJ]
      change η ∈ ((specIdealSheaf I).support : Set (Spec (.of R)))
      rw [support_specIdealSheaf]
      exact hIp
    have hsupp : (J.support : Set (Spec (.of R))) = (f.smoothLocus : Set (Spec (.of R)))ᶜ := by
      rw [Scheme.coe_support_singIdeal_eq_singularLocus f,
        Scheme.singularLocus_eq_compl_smoothLocus f]
    change η ∈ (J.support : Set (Spec (.of R))) at hsing
    rw [hsupp] at hsing
    exact hsing (heq ▸ hsm)
  obtain ⟨t,htI,ht⟩ := exists_regular_element_of_avoids_minimalPrimes R I hI
  refine ⟨specIdealSheaf (Ideal.span {t}), ?_, ?_⟩
  · change (ofIdealTop ((Ideal.span {t}).map c)).IsInvertible
    rw [Ideal.map_span, Set.image_singleton]
    exact isInvertible_ofIdealTop_span_singleton
      (map_mem_nonZeroDivisors_of_ringEquiv
        (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv ht)
  · change specIdealSheaf (Ideal.span {t}) ≤ J
    rw [← hJ]
    apply le_of_isAffine
    rw [specIdealSheaf_ideal_top, specIdealSheaf_ideal_top]
    exact Ideal.map_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr htI))

/-- Any actual invertible ideal remains invertible through the ENTIRE actual native sequence. -/
theorem invertible_comap_composite : ∀ {X : Scheme.{u}} (S : X.BlowUpSequence)
    (K : X.IdealSheafData), K.IsInvertible → (K.comap S.composite).IsInvertible := by
  intro X S
  induction S with
  | nil X =>
    intro K hK
    change (K.comap (𝟙 X)).IsInvertible
    rw [comap_id]
    exact hK
  | cons X D T ih =>
    intro K hK
    change (K.comap (T.composite ≫ D.blowUpπ)).IsInvertible
    rw [comap_comp]
    exact ih _ (blowUp.isInvertible_comap_of_isInvertible D K hK)

private theorem invertible_comap_affineBlowUp {R : Type u} [CommRing R] (I : Ideal R)
    (K : (Spec (.of R)).IdealSheafData) (hK : K.IsInvertible) :
    (K.comap (affineBlowUp.π I)).IsInvertible := by
  obtain ⟨e,he,-⟩ := IsBlowUp.exists_iso (affineBlowUp.isBlowUp I)
    (blowUp.isBlowUp (specIdealSheaf I))
  rw [← he, comap_comp]
  exact IsInvertible.comap_of_isOpenImmersion e.hom
    (blowUp.isInvertible_comap_of_isInvertible (specIdealSheaf I) K hK)

open ActualDimensionGroupBlowup ActualRelativeAffineHistoryDescent

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- The genuine ORIGINAL singular ideal pulled to the SAME actual native base-history endpoint. -/
def originalSingPullback : (nativeBaseHistory R k).last.IdealSheafData :=
  (Spec (.of R)).singIdeal.comap
    ((nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R))

/-- Actual original-singular pullback applicability: every actual stalk ideal is nonzero. -/
theorem originalSingPullback_nonzero : (originalSingPullback R k).IsNonzeroEverywhere := by
  obtain ⟨K,hK,hKJ⟩ := exists_invertible_le_original_singIdeal R k
  have hKB := invertible_comap_affineBlowUp (dimensionSeparationIdeal R) K hK
  have hKA := invertible_comap_composite (nativeBaseHistory R k) _ hKB
  apply Hironaka.BMO.isNonzeroEverywhere_of_le
    (comap_mono _ hKJ)
  apply Hironaka.BMO.isNonzeroEverywhere_of_isInvertible
  change (K.comap ((nativeBaseHistory R k).composite ≫
    affineBlowUp.π (dimensionSeparationIdeal R))).IsInvertible
  rw [comap_comp]
  exact hKA

/-- This actual ideal's support is the inverse ORIGINAL singular locus, with no substituted locus. -/
theorem originalSingPullback_support :
    ((originalSingPullback R k).support : Set (nativeBaseHistory R k).last) =
      ((nativeBaseHistory R k).composite ≫ affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹'
        (Spec (.of R)).singularLocus := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  rw [originalSingPullback, support_comap, Closeds.coe_preimage,
    Scheme.coe_support_singIdeal_eq_singularLocus
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))]
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualOriginalSingIdealNonzero
