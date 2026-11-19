import Hironaka.Geometry.MonomialBlowupRegularBaseSNCParameters
import Hironaka.Geometry.BoundaryEnlargementComponents
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! Actual localized heights of genuine native SNC component-intersection ideals. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCIntersection

open SpecIdealSheaf ReducedClosedSubscheme Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

/-- Intrinsic pure codimension computes every actual minimal prime, including reducible closed intersections. -/
theorem minimalPrime_height_of_hasPureCodimension (I : Ideal A) (r : ℕ)
    (hI : HasPureCodimension (specIdealSheaf A I).support r)
    (q : Ideal A) (hq : q ∈ I.minimalPrimes) : q.height = r := by
  let : q.IsPrime := hq.isPrime
  let E := specIdealSheaf A I
  let x : Spec (CommRingCat.of A) := (⟨q, inferInstance⟩ : PrimeSpectrum A)
  have hirr : IsIrreducible (PrimeSpectrum.zeroLocus (q : Set A)) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical q ‹q.IsPrime›.isRadical).mpr inferInstance
  have hle : PrimeSpectrum.zeroLocus (q : Set A) ⊆ (E.support : Set (Spec (CommRingCat.of A))) := by
    rw [specIdealSheaf_support]
    exact PrimeSpectrum.zeroLocus_anti_mono hq.le
  obtain ⟨C, hC⟩ := BoundaryEnlargement.exists_component_containing E _ hirr hle
  let hCirr := SNCLocality.divisorComponent_isIrreducible E C
  let z := hCirr.genericPoint
  have hg : IsGenericPoint z (C.val : Set (Spec (CommRingCat.of A))) :=
    hCirr.isGenericPoint_genericPoint C.val.isClosed
  have hIz : I ≤ (show PrimeSpectrum A from z).asIdeal := by
    have hz := SNCSubdivisorComponent.component_le_support E C hg.mem
    change z ∈ ((specIdealSheaf A I).support : Set (Spec (CommRingCat.of A))) at hz
    rw [specIdealSheaf_support] at hz
    exact hz
  have hxC : x ∈ (C.val : Set (Spec (CommRingCat.of A))) := hC (show q ≤ q from le_rfl)
  have hzq : (show PrimeSpectrum A from z).asIdeal ≤ q :=
    (PrimeSpectrum.le_iff_specializes (show PrimeSpectrum A from z) x).mpr (hg.specializes hxC)
  have hqz : q ≤ (show PrimeSpectrum A from z).asIdeal := hq.2 ⟨z.isPrime, hIz⟩ hzq
  have hzx : z = x := PrimeSpectrum.ext (le_antisymm hzq hqz)
  obtain ⟨S, hS, hSC⟩ := C.property
  have hd := hI S hS x (by rw [hSC, ← hzx]; exact hg)
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight] at hd
  exact_mod_cast hd

/-- The actual localized quotient is regular local, with no global primeness hypothesis on its ideal. -/
theorem quotient_atPrime_isRegularLocalRing (I p : Ideal A) [p.IsPrime]
    [IsRegularRing (A ⧸ I)] (hIp : I ≤ p) :
    IsRegularLocalRing (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) := by
  let q := p.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hIp)
  have hqp : q.comap (Ideal.Quotient.mk I) = p := by
    simp only [q, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hIp]
  let L := Localization.AtPrime p
  let J := I.map (algebraMap A L)
  have hnot : ∀ x : A, Ideal.Quotient.mk I x ∉ q ↔ x ∉ p := by
    intro x
    apply not_congr
    change x ∈ q.comap (Ideal.Quotient.mk I) ↔ x ∈ p
    rw [hqp]
  have heq : Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl = q.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hnot x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨x, (hnot x).mp hy, rfl⟩
  let : IsLocalization q.primeCompl (L ⧸ J) := by rw [← heq]; infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (L ⧸ J) (Localization.AtPrime q)).symm.toRingEquiv

/-- Actual pure codimension and quotient regularity force the exact height of the actual localized ideal. -/
theorem localized_height_of_hasPureCodimension (I p : Ideal A) [p.IsPrime]
    [IsRegularRing (A ⧸ I)] (hIp : I ≤ p) (r : ℕ)
    (hI : HasPureCodimension (specIdealSheaf A I).support r) :
    (I.map (algebraMap A (Localization.AtPrime p))).height = r := by
  let L := Localization.AtPrime p
  let J := I.map (algebraMap A L)
  let := quotient_atPrime_isRegularLocalRing I p hIp
  let : IsDomain (L ⧸ J) := Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  let : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  have hJmin : J ∈ J.minimalPrimes := by simp [Ideal.minimalPrimes_eq_subsingleton_self]
  have hqmin : J.under A ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map p.primeCompl L I] at hJmin
    exact hJmin
  have hd : Disjoint (p.primeCompl : Set A) (J.under A : Set A) :=
    (IsLocalization.disjoint_under_iff p.primeCompl L J).mpr ‹J.IsPrime›.ne_top
  have hh := IsLocalization.height_map_of_disjoint (S := L) p.primeCompl (J.under A) hd
  rw [IsLocalization.map_under p.primeCompl L J] at hh
  exact hh.trans (minimalPrime_height_of_hasPureCodimension I r hI _ hqmin)

/-- The actual affine ideal of the full native scheme-theoretic component intersection. -/
def intersectionIdeal (D : (Spec (CommRingCat.of A)).IdealSheafData)
    (J : Finset (DivisorComponent D)) : Ideal A :=
  specIdealSheafEquiv A (componentIntersection D J)

/-- Exact ideal-sheaf equality, retaining every component intersection's original scheme structure. -/
theorem intersectionIdeal_spec (D : (Spec (CommRingCat.of A)).IdealSheafData)
    (J : Finset (DivisorComponent D)) :
    specIdealSheaf A (intersectionIdeal D J) = componentIntersection D J :=
  (specIdealSheafEquiv A).symm_apply_apply _

variable [IsNoetherianRing A]

/-- The actual localized SNC intersection has regular quotient and exact height; no such certificates are inputs. -/
theorem intersection_local_data
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (hJ : J.Nonempty)
    (p : Ideal A) [p.IsPrime] (hIp : intersectionIdeal D J ≤ p) :
    IsRegularLocalRing (Localization.AtPrime p ⧸
      (intersectionIdeal D J).map (algebraMap A (Localization.AtPrime p))) ∧
      ((intersectionIdeal D J).map (algebraMap A (Localization.AtPrime p))).height = J.card := by
  let I := intersectionIdeal D J
  have hreg : IsRegularScheme (specIdealSheaf A I).subscheme := by
    rw [intersectionIdeal_spec]
    exact hD.intersectionsRegular J hJ
  let : IsRegularRing (A ⧸ I) :=
    SNCSubdivisorComponent.isRegularRing_quotient_of_specIdealSheaf I hreg
  have hcodim : HasPureCodimension (specIdealSheaf A I).support J.card := by
    rw [intersectionIdeal_spec]
    exact hD.intersectionsCodimension J hJ
  exact ⟨quotient_atPrime_isRegularLocalRing I p hIp,
    localized_height_of_hasPureCodimension I p hIp J.card hcodim⟩

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCIntersection
