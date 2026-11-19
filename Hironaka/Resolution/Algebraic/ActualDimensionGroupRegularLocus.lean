import Hironaka.Resolution.Algebraic.ActualDimensionGroupBlowup
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Uniqueness
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Existence
import Hironaka.Scheme.BlowUp.FlatBaseChange
import Hironaka.Geometry.ReducedClosedSubscheme

/-! The SAME original separation projection over the entire original regular
and smooth locus. Component uniqueness and a complementary element avoiding
each regular prime are derived, not supplied as certificates.
Source-first proof: `actual-dimension-group-regular-locus-20261101.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualDimensionGroupRegularLocus
noncomputable section
open ActualDimensionGroupBlowup

variable (R : Type u) [CommRing R]

private theorem minimal_prime_eq_localization_kernel (p : PrimeSpectrum R)
    [IsDomain (Localization.AtPrime p.asIdeal)] (q : minimalPrimes R) (hq : q.val ≤ p.asIdeal) :
    q.val = (⊥ : Ideal (Localization.AtPrime p.asIdeal)).under R := by
  let C := Localization.AtPrime p.asIdeal
  have : q.val.IsPrime := q.property.isPrime
  have hd : Disjoint (p.asIdeal.primeCompl : Set R) (q.val : Set R) :=
    Set.disjoint_left.mpr fun x hx hxq => hx (hq hxq)
  have hUnder : (q.val.map (algebraMap R C)).under R = q.val :=
    IsLocalization.under_map_of_isPrime_disjoint p.asIdeal.primeCompl C q.property.isPrime hd
  have hMin : q.val.map (algebraMap R C) ∈ minimalPrimes C := by
    have h := IsLocalization.minimalPrimes_map p.asIdeal.primeCompl C (⊥ : Ideal R)
    have hm : q.val.map (algebraMap R C) ∈ ((⊥ : Ideal R).map (algebraMap R C)).minimalPrimes := by
      rw [h]
      change (q.val.map (algebraMap R C)).under R ∈ minimalPrimes R
      rw [hUnder]
      exact q.property
    simpa only [Ideal.map_bot] using hm
  have hZero : q.val.map (algebraMap R C) = ⊥ := by
    simpa only [IsDomain.minimalPrimes_eq_singleton_bot,Set.mem_singleton_iff] using hMin
  rw [← hUnder,hZero]

/-- At an actual domain localization, exactly one original minimal prime occurs. -/
theorem unique_minimal_prime_below_of_localization_domain (p : PrimeSpectrum R)
    [IsDomain (Localization.AtPrime p.asIdeal)] :
    ∃! q : minimalPrimes R, q.val ≤ p.asIdeal := by
  obtain ⟨q,hq,hqp⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
  refine ⟨⟨q,hq⟩,hqp,?_⟩
  intro q' hq'
  apply Subtype.ext
  exact (minimal_prime_eq_localization_kernel R p q' hq').trans
    (minimal_prime_eq_localization_kernel R p ⟨q,hq⟩ hqp).symm

/-- A literal complementary group element is derived from original local domain geometry. -/
theorem exists_complement_avoiding_of_localization_domain [IsNoetherianRing R]
    (p : PrimeSpectrum R) [IsDomain (Localization.AtPrime p.asIdeal)] :
    ∃ d : dimensionIndex R, ∃ a : complementIdeal R (dimensionGroupIdeal R) d,
      a.val ∉ p.asIdeal := by
  classical
  obtain ⟨q₀,hq₀,huniq⟩ := unique_minimal_prime_below_of_localization_domain R p
  let d : dimensionIndex R := ⟨componentDimension R q₀,⟨q₀,rfl⟩⟩
  have : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  let T := {q : minimalPrimes R // componentDimension R q ≠ d.val}
  let : Fintype T := Fintype.ofFinite T
  have hL : (⨅ q : T, q.val.val) ≤ complementIdeal R (dimensionGroupIdeal R) d := by
    intro x hx
    apply Ideal.mem_iInf.mpr
    intro e
    apply Ideal.mem_iInf.mpr
    intro hed
    apply Ideal.mem_iInf.mpr
    intro q
    apply Ideal.mem_iInf.mpr
    intro hqe
    exact (Ideal.mem_iInf.mp hx) ⟨q,fun h => hed (Subtype.ext (hqe.symm.trans h))⟩
  have hnot : ¬(⨅ q : T, q.val.val) ≤ p.asIdeal := by
    intro h
    have hfin : Finset.univ.inf (fun q : T => q.val.val) ≤ p.asIdeal := by
      simpa [Finset.inf_eq_iInf] using h
    obtain ⟨q,_hq,hqp⟩ := p.isPrime.inf_le'.mp hfin
    exact q.property (congrArg (componentDimension R) (huniq q.val hqp))
  change ¬ ∀ x : R, x ∈ (⨅ q : T, q.val.val) → x ∈ p.asIdeal at hnot
  push Not at hnot
  obtain ⟨a,ha,hap⟩ := hnot
  exact ⟨d,⟨a,hL ha⟩,hap⟩

/-- The original separation centre misses every actual regular prime. -/
theorem regular_prime_avoids_separation [IsNoetherianRing R] (p : PrimeSpectrum R)
    [IsRegularLocalRing (Localization.AtPrime p.asIdeal)] :
    ¬ dimensionSeparationIdeal R ≤ p.asIdeal := by
  have : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalRing.isDomain_of_isRegularLocalRing _
  obtain ⟨d,a,ha⟩ := exists_complement_avoiding_of_localization_domain R p
  intro h
  exact ha (h ((le_iSup (fun e => complementIdeal R (dimensionGroupIdeal R) e) d) a.property))

private theorem mem_support_specIdealSheaf_iff (I : Ideal R) (p : PrimeSpectrum R) :
    p ∈ (specIdealSheaf I).support ↔ I ≤ p.asIdeal := by
  have hEq : specIdealSheaf I =
      Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R I := by
    apply le_antisymm
    · apply le_of_isAffine
      rw [specIdealSheaf_ideal_top,
        Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf_ideal_top]
    · apply le_of_isAffine
      rw [specIdealSheaf_ideal_top,
        Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf_ideal_top]
  rw [hEq]
  change p ∈ ((Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R I).support :
    Set (Spec (.of R))) ↔ _
  rw [Hironaka.Geometry.ReducedClosedSubscheme.specIdealSheaf_support]
  rfl

private theorem native_affine_isBlowUp (I : Ideal R) :
    IsBlowUp (specIdealSheaf I) (affineBlowUp.π I) where
  admissible := affineBlowUp.isInvertible_exceptionalIdeal I
  existsUnique_lift f hf := by
    obtain ⟨g,hg⟩ := affineBlowUp.exists_lift I f hf
    exact ⟨g,hg,fun g' hg' => affineBlowUp.hom_ext I f hf g' g hg' hg⟩

private theorem identity_isBlowUp_top (X : Scheme.{u}) :
    IsBlowUp (⊤ : X.IdealSheafData) (𝟙 X) where
  admissible := by simpa only [comap_id] using (isInvertible_top (X := X))
  existsUnique_lift f _hf := by
    refine ⟨f,Category.comp_id _,?_⟩
    intro g hg
    simpa only [Category.comp_id] using hg

/-- The SAME native affine projection is an isomorphism over every original regular open. -/
theorem separation_isIso_over_regular_open [IsNoetherianRing R]
    (U : (Spec (.of R)).Opens)
    (hreg : ∀ p : PrimeSpectrum R, p ∈ U → IsRegularLocalRing (Localization.AtPrime p.asIdeal)) :
    IsIso (affineBlowUp.π (dimensionSeparationIdeal R) ∣_ U) := by
  let I := dimensionSeparationIdeal R
  have hunit : (specIdealSheaf I).comap U.ι = ⊤ := by
    rw [← support_eq_bot_iff,support_comap]
    ext p
    change U.ι p ∈ (specIdealSheaf I).support ↔ False
    constructor
    · intro hp
      let q : PrimeSpectrum R := p.val
      have : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := hreg q p.property
      exact (regular_prime_avoids_separation R q)
        ((mem_support_specIdealSheaf_iff R I q).mp hp)
    · exact False.elim
  have hid : IsBlowUp ((specIdealSheaf I).comap U.ι) (𝟙 U.toScheme) := by
    rw [hunit]
    exact identity_isBlowUp_top U.toScheme
  obtain ⟨φ,hφ⟩ := IsBlowUp.exists_isPullback_of_flat U.ι (native_affine_isBlowUp R I) hid
  obtain ⟨e,he⟩ := exists_restrictIso_of_isPullback U hφ
  have hEq : (affineBlowUp.π I ∣_ U) = e.inv := by
    rw [← cancel_epi e.hom,he,e.hom_inv_id]
  rw [hEq]
  infer_instance

private instance original_locallyOfFiniteType (k : Type u) [Field k]
    [Algebra k R] [Algebra.FiniteType k R] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- This exact smooth open is the entire original prime-localization regular locus. -/
theorem mem_smoothLocus_iff_regular_localization (k : Type u) [Field k] [CharZero k]
    [Algebra k R] [Algebra.FiniteType k R] (p : PrimeSpectrum R) :
    p ∈ (Spec.map (CommRingCat.ofHom (algebraMap k R))).smoothLocus ↔
      IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  constructor
  · intro h
    have : IsRegularLocalRing ((Spec (.of R)).presheaf.stalk p) :=
      (Scheme.mem_smoothLocus_iff_isRegularAt
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) p).mp h
    exact IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (.of R) p).commRingCatIsoToRingEquiv
  · intro h
    have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := h
    apply (Scheme.mem_smoothLocus_iff_isRegularAt
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) p).mpr
    exact IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (.of R) p).symm.commRingCatIsoToRingEquiv

/-- The entire native smooth locus, hence the entire original regular locus in characteristic zero. -/
theorem separation_isIso_over_smoothLocus (k : Type u) [Field k] [CharZero k]
    [Algebra k R] [Algebra.FiniteType k R] [IsReduced R] :
    IsIso (affineBlowUp.π (dimensionSeparationIdeal R) ∣_
      (Spec.map (CommRingCat.ofHom (algebraMap k R))).smoothLocus) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact separation_isIso_over_regular_open R _ fun p hp =>
    (mem_smoothLocus_iff_regular_localization R k p).mp hp

end
end Hironaka.Resolution.Algebraic.ActualDimensionGroupRegularLocus
