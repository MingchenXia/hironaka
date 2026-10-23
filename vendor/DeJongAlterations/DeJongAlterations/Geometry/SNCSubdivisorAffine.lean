import DeJongAlterations.Geometry.SNCSubdivisorAlgebra
import DeJongAlterations.Geometry.SNCSubdivisorSpread
import DeJongAlterations.Geometry.RegularNode
import DeJongAlterations.Geometry.BlowupCartier
import DeJongAlterations.Geometry.ReducedClosedSubscheme

/-!
# Actual affine regular codimension-one components

The component height, localized regular equation and affine Cartier equations
are proved for the native spectrum ideal sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.Geometry.SNCSubdivisorAffine

open SpecIdealSheaf ReducedClosedSubscheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R]

/-- The intrinsic pure codimension of a native prime closed subscheme computes its actual ideal height. -/
theorem height_eq_of_hasPureCodimension
    (I : Ideal R) [I.IsPrime] (r : ℕ)
    (hI : HasPureCodimension (specIdealSheaf R I).support r) : I.height = r := by
  let T := (specIdealSheaf R I).support
  have hirr : IsIrreducible (T : Set (Spec (CommRingCat.of R))) := by
    rw [specIdealSheaf_support]
    exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _ ‹I.IsPrime›.isRadical).mpr
      inferInstance
  let : IrreducibleSpace T := Subtype.irreducibleSpace hirr
  let q : Spec (CommRingCat.of R) := (⟨I, inferInstance⟩ : PrimeSpectrum R)
  have hcomp : (Set.univ : Set T) ∈ irreducibleComponents T := by
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
  have hgeneric : IsGenericPoint q ((Subtype.val : T → Spec (CommRingCat.of R)) '' Set.univ) := by
    have himage : (Subtype.val : T → Spec (CommRingCat.of R)) '' Set.univ =
        (T : Set (Spec (CommRingCat.of R))) := by
      ext y
      simp
    rw [himage]
    have h := PrimeSpectrum.closure_singleton (⟨I, inferInstance⟩ : PrimeSpectrum R)
    exact h.trans (specIdealSheaf_support R I).symm
  have hdim := hI Set.univ hcomp q hgeneric
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight] at hdim
  exact_mod_cast hdim

/-- A height-one prime with actual regular source and quotient local rings has a genuine regular local equation. -/
theorem exists_regular_generator_atPrime
    (I p : Ideal R) [I.IsPrime] [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)]
    [IsRegularRing (R ⧸ I)] (hIp : I ≤ p) (hheight : I.height = 1) :
    ∃ b : Localization.AtPrime p, IsRegular b ∧
      I.map (algebraMap R (Localization.AtPrime p)) = Ideal.span {b} := by
  let q := p.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hIp)
  have hqp : q.comap (Ideal.Quotient.mk I) = p := by
    simp only [q, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hIp]
  let L := Localization.AtPrime p
  let J := I.map (algebraMap R L)
  have hequiv : (L ⧸ J) ≃+* Localization.AtPrime q := by
    have hnot : ∀ x : R, Ideal.Quotient.mk I x ∉ q ↔ x ∉ p := by
      intro x
      apply not_congr
      change x ∈ q.comap (Ideal.Quotient.mk I) ↔ x ∈ p
      rw [hqp]
    have heq : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hnot x).mpr hx
      · intro hy
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨x, (hnot x).mp hy, rfl⟩
    let : IsLocalization q.primeCompl (L ⧸ J) := by
      rw [← heq]
      infer_instance
    exact (IsLocalization.algEquiv q.primeCompl (L ⧸ J)
      (Localization.AtPrime q)).toRingEquiv
  let : IsRegularLocalRing (L ⧸ J) := IsRegularLocalRing.of_ringEquiv hequiv.symm
  let : IsDomain L := Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing L
  have hd : Disjoint (p.primeCompl : Set R) (I : Set R) := by
    exact Set.disjoint_left.mpr (fun x hxM hxI ↦ hxM (hIp hxI))
  have hJheight : J.height = 1 :=
    (IsLocalization.height_map_of_disjoint (S := L) p.primeCompl I hd).trans hheight
  have hJne : J ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hJheight
  obtain ⟨b, _, _, hb, hspan⟩ :=
    SNCSubdivisorAlgebra.exists_regular_kernel_generator (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hJne)
      (by simpa only [Ideal.mk_ker, hJheight] using (le_refl (1 : ℕ∞)))
  exact ⟨b, hb, by simpa only [Ideal.mk_ker] using hspan.symm⟩

/-- Actual regular principal equations of prime localizations give actual affine Cartier neighborhoods. -/
theorem isEffectiveCartierDivisor_of_local_equations [IsNoetherianRing R]
    (I : Ideal R)
    (hloc : ∀ (p : Ideal R) [p.IsPrime],
      ∃ b : Localization.AtPrime p, IsRegular b ∧
        I.map (algebraMap R (Localization.AtPrime p)) = Ideal.span {b}) :
    IsEffectiveCartierDivisor (specIdealSheaf R I) := by
  intro x
  let p : PrimeSpectrum R := x
  let : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨b, hb, hspan⟩ := hloc p.asIdeal
  obtain ⟨s, hs, a, _, hreg, ha⟩ :=
    SNCSubdivisorSpread.exists_away_regular_span_eq I p.asIdeal b hb hspan
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))
  have hx : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away s))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
    exact hs
  obtain ⟨y, hy⟩ := hx
  have hc : IsEffectiveCartierDivisor ((specIdealSheaf R I).comap f) := by
    rw [specIdealSheaf_comap, ha]
    exact isEffectiveCartierDivisor_specIdealSheaf_span _ hreg
  have H := CartierLocality.exists_affine_neighborhood_of_isOpenImmersion
    f (specIdealSheaf R I) hc y
  have hfy : f y = x := hy
  simpa only [hfy] using H

/-- A prime regular codimension-one closed subscheme has its actual Cartier ideal, without a principality certificate. -/
theorem isEffectiveCartierDivisor_of_prime_regular_quotient [IsNoetherianRing R]
    (I : Ideal R) [I.IsPrime] [IsRegularRing (R ⧸ I)] (hheight : I.height = 1)
    (hreg : ∀ (p : Ideal R) [p.IsPrime], I ≤ p →
      IsRegularLocalRing (Localization.AtPrime p)) :
    IsEffectiveCartierDivisor (specIdealSheaf R I) := by
  apply isEffectiveCartierDivisor_of_local_equations
  intro p hp
  by_cases hIp : I ≤ p
  · let : IsRegularLocalRing (Localization.AtPrime p) := hreg p hIp
    exact exists_regular_generator_atPrime I p hIp hheight
  · refine ⟨1, isRegular_one, ?_⟩
    rw [Ideal.span_singleton_one]
    apply IsLocalization.map_eq_top_of_not_subset p.primeCompl (Localization.AtPrime p)
    intro h
    apply hIp
    intro x hx
    by_contra hxp
    exact h hx hxp

end DeJongAlterations.Geometry.SNCSubdivisorAffine
