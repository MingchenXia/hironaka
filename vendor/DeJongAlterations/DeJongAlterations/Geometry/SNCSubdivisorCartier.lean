import DeJongAlterations.Geometry.SNCSubdivisorTopology
import DeJongAlterations.Geometry.SNCSubdivisorLocal
import DeJongAlterations.Geometry.SNCSubdivisorProducts
import Mathlib.Algebra.Regular.Pow

/-!
# Actual Cartier equations for finite SNC subunions

The native finite intersection ideal is localized at the actual point,
generated there by the product of its actual distinct prime equations,
and spread to an actual affine neighborhood.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.SNCSubdivisorCartier

open Scheme.IdealSheafData SNCSubdivisorTopology SNCSubdivisorLocal SpecIdealSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}}

/-- The actual affine ideal of the reduced subunion is the finite intersection of its actual component ideals. -/
theorem selectedDivisor_ideal (D : X.IdealSheafData) (F : Finset (DivisorComponent D))
    (U : X.affineOpens) :
    (selectedDivisor D F).ideal U = F.inf (fun C ↦ (vanishingIdeal C.val).ideal U) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [selectedDivisor, selectedSupport]
  | @insert C F hC ih =>
    simpa only [selectedDivisor, selectedSupport, Finset.sup_insert, vanishingIdeal_sup,
      ideal_inf, Pi.inf_apply, Finset.inf_insert] using congrArg (fun I ↦
        (vanishingIdeal C.val).ideal U ⊓ I) ih

/-- Native localization preserves the actual finite ideal intersection. -/
theorem map_finset_inf {R S ι : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (F : Finset ι) (I : ι → Ideal R) :
    (F.inf I).map (algebraMap R S) = F.inf (fun i ↦ (I i).map (algebraMap R S)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simpa only [Finset.inf_empty] using Ideal.map_top (algebraMap R S)
  | @insert i F hi ih =>
    simp only [Finset.inf_insert, IsLocalization.map_inf M S, ih]

/-- The actual localized ideal of a finite SNC subunion has a regular product equation. -/
theorem exists_regular_generator_localized [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (F : Finset (DivisorComponent D)) (U : X.affineOpens)
    (p : Ideal Γ(X, U.1)) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)]
    (hmeet : ∀ C ∈ F, ((C.val : Set X) ∩ Set.range U.2.fromSpec).Nonempty)
    (hcontain : ∀ C ∈ F, (vanishingIdeal C.val).ideal U ≤ p) :
    ∃ b : Localization.AtPrime p, IsRegular b ∧
      ((selectedDivisor D F).ideal U).map
        (algebraMap Γ(X, U.1) (Localization.AtPrime p)) = Ideal.span {b} := by
  classical
  let A := Γ(X, U.1)
  let L := Localization.AtPrime p
  let I : DivisorComponent D → Ideal A := fun C ↦ (vanishingIdeal C.val).ideal U
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  let : IsDomain L := Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing L
  have hinfo : ∀ C ∈ F, (I C).IsPrime ∧ (I C).height = 1 ∧ IsRegularRing (A ⧸ I C) := by
    intro C hC
    exact component_affine_prime_data D hD C U (hmeet C hC)
  have hdisjoint : ∀ C ∈ F, Disjoint (p.primeCompl : Set A) (I C : Set A) :=
    fun C hC ↦ Set.disjoint_left.mpr (fun x hxM hxI ↦ hxM (hcontain C hC hxI))
  have hJheight : ∀ C ∈ F, ((I C).map (algebraMap A L)).height = 1 := by
    intro C hC
    let : (I C).IsPrime := (hinfo C hC).1
    exact (IsLocalization.height_map_of_disjoint (S := L) p.primeCompl (I C)
      (hdisjoint C hC)).trans (hinfo C hC).2.1
  have hgen : ∀ C : {C : DivisorComponent D // C ∈ F},
      ∃ b : L, IsRegular b ∧ (I C.val).map (algebraMap A L) = Ideal.span {b} := by
    intro C
    let : (I C.val).IsPrime := (hinfo C.val C.property).1
    let : IsRegularRing (A ⧸ I C.val) := (hinfo C.val C.property).2.2
    exact SNCSubdivisorAffine.exists_regular_generator_atPrime (I C.val) p
      (hcontain C.val C.property) (hinfo C.val C.property).2.1
  choose a hareg haspan using hgen
  let b : DivisorComponent D → L := fun C ↦ if hC : C ∈ F then a ⟨C, hC⟩ else 1
  have hbreg : ∀ C ∈ F, IsRegular (b C) := by
    intro C hC
    simpa only [b, dif_pos hC] using hareg ⟨C, hC⟩
  have hbspan : ∀ C ∈ F, (I C).map (algebraMap A L) = Ideal.span {b C} := by
    intro C hC
    simpa only [b, dif_pos hC] using haspan ⟨C, hC⟩
  have hbprime : ∀ C ∈ F, Prime (b C) := by
    intro C hC
    apply (Ideal.span_singleton_prime (hbreg C hC).ne_zero).mp
    rw [← hbspan C hC]
    exact IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl L (I C)
      (hinfo C hC).1 (hdisjoint C hC)
  have hbdist : ∀ C ∈ F, ∀ C' ∈ F, C ≠ C' → ¬ b C ∣ b C' := by
    intro C hC C' hC' hne hdiv
    have hle : (I C').map (algebraMap A L) ≤ (I C).map (algebraMap A L) := by
      rw [hbspan C hC, hbspan C' hC']
      exact Ideal.span_singleton_le_span_singleton.mpr hdiv
    let : ((I C').map (algebraMap A L)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl L (I C')
        (hinfo C' hC').1 (hdisjoint C' hC')
    have heqJ : (I C').map (algebraMap A L) = (I C).map (algebraMap A L) :=
      ((I C').map (algebraMap A L)).eq_of_le_of_height_le hle
        (by rw [hJheight C hC, hJheight C' hC'])
    have heqI := congrArg (fun J : Ideal L ↦ J.under A) heqJ
    rw [IsLocalization.under_map_of_isPrime_disjoint p.primeCompl L
      (hinfo C' hC').1 (hdisjoint C' hC'),
      IsLocalization.under_map_of_isPrime_disjoint p.primeCompl L
        (hinfo C hC).1 (hdisjoint C hC)] at heqI
    exact hne (component_affine_ideal_injective D U C' C (hmeet C' hC') (hmeet C hC)
      heqI).symm
  refine ⟨∏ C ∈ F, b C, IsRegular.prod hbreg, ?_⟩
  rw [selectedDivisor_ideal, map_finset_inf p.primeCompl]
  have heq : F.inf (fun C ↦ (I C).map (algebraMap A L)) =
      F.inf (fun C ↦ Ideal.span {b C}) :=
    Finset.inf_congr rfl (fun C hC ↦ hbspan C hC)
  exact heq.trans
    (SNCSubdivisorProducts.finset_inf_span_singleton_of_prime F b hbprime hbdist)

/-- Discarding ideals not contained in the actual point does not change their localized intersection. -/
theorem map_finset_inf_filter {R ι : Type*} [CommRing R]
    (p : Ideal R) [p.IsPrime] (F : Finset ι) (I : ι → Ideal R)
    [DecidablePred (fun i ↦ I i ≤ p)] :
    (F.inf I).map (algebraMap R (Localization.AtPrime p)) =
      ((F.filter fun i ↦ I i ≤ p).inf I).map
        (algebraMap R (Localization.AtPrime p)) := by
  classical
  let L := Localization.AtPrime p
  let G := F.filter fun i ↦ I i ≤ p
  have htop : ∀ i ∈ F, i ∉ G → (I i).map (algebraMap R L) = ⊤ := by
    intro i hi hiG
    have hno : ¬ I i ≤ p := fun h ↦ hiG (Finset.mem_filter.mpr ⟨hi, h⟩)
    apply IsLocalization.map_eq_top_of_not_subset p.primeCompl L
    intro h
    apply hno
    intro x hx
    by_contra hxp
    exact h hx hxp
  rw [map_finset_inf p.primeCompl, map_finset_inf p.primeCompl,
    Finset.inf_eq_iInf, Finset.inf_eq_iInf]
  apply le_antisymm
  · apply le_iInf
    intro i
    apply le_iInf
    intro hiG
    exact iInf_le_of_le i (iInf_le_of_le (Finset.mem_filter.mp hiG).1 le_rfl)
  · refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
    by_cases hiG : i ∈ G
    · exact iInf_le_of_le i (iInf_le_of_le hiG le_rfl)
    · rw [htop i hi hiG]
      exact le_top

/-- The actual reduced union of any finite selected native SNC components is effective Cartier. -/
theorem selectedDivisor_isEffectiveCartierDivisor [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (F : Finset (DivisorComponent D)) :
    IsEffectiveCartierDivisor (selectedDivisor D F) := by
  classical
  let E := selectedDivisor D F
  have hlocal : ∀ U : X.affineOpens,
      IsEffectiveCartierDivisor (E.comap U.2.fromSpec) := by
    intro U
    let A := Γ(X, U.1)
    let f := U.2.fromSpec
    let I : DivisorComponent D → Ideal A := fun C ↦ (vanishingIdeal C.val).ideal U
    let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
    rw [BlowupCartier.comap_fromSpec]
    apply SNCSubdivisorAffine.isEffectiveCartierDivisor_of_local_equations
    intro p hp
    let L := Localization.AtPrime p
    let y : Spec A := (⟨p, hp⟩ : PrimeSpectrum A)
    let G := F.filter fun C ↦ I C ≤ p
    have hpoint : ∀ C : DivisorComponent D, I C ≤ p ↔ f y ∈ C.val := by
      intro C
      have hEI := BlowupCartier.comap_fromSpec (vanishingIdeal C.val) U
      have hsupp : ((specIdealSheaf A (I C)).support : Set (Spec A)) =
          f ⁻¹' (C.val : Set X) := by
        rw [← hEI, support_comap]
        rfl
      have hmem : (y ∈ ((specIdealSheaf A (I C)).support : Set (Spec A))) ↔ I C ≤ p := by
        rw [ReducedClosedSubscheme.specIdealSheaf_support]
        rfl
      rw [hsupp] at hmem
      exact hmem.symm
    have hIdeq : (E.ideal U).map (algebraMap A L) =
        ((selectedDivisor D G).ideal U).map (algebraMap A L) := by
      rw [selectedDivisor_ideal, selectedDivisor_ideal]
      exact map_finset_inf_filter p F I
    by_cases hG : G.Nonempty
    · obtain ⟨C₀, hC₀⟩ := hG
      have hIp₀ := (Finset.mem_filter.mp hC₀).2
      have hxD := SNCSubdivisorComponent.component_le_support D C₀ ((hpoint C₀).mp hIp₀)
      let : IsRegularLocalRing (X.presheaf.stalk (f y)) := hD.regularAlong (f y) hxD
      let : IsRegularLocalRing ((Spec A).presheaf.stalk y) :=
        IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
      let : IsRegularLocalRing L :=
        IsRegularLocalRing.of_ringEquiv (Spec.stalkIso A y).commRingCatIsoToRingEquiv
      obtain ⟨b, hb, hspan⟩ := exists_regular_generator_localized D hD G U p
        (fun C hC ↦ ⟨f y, (hpoint C).mp (Finset.mem_filter.mp hC).2, y, rfl⟩)
        (fun C hC ↦ (Finset.mem_filter.mp hC).2)
      exact ⟨b, hb, hIdeq.trans hspan⟩
    · have hGe : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
      refine ⟨1, isRegular_one, ?_⟩
      rw [hIdeq, hGe, selectedDivisor_ideal]
      simp only [Finset.inf_empty, Ideal.map_top, Ideal.span_singleton_one]
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := (⊤ : X.Opens)) (by trivial)
  have H := CartierLocality.exists_affine_neighborhood_of_isOpenImmersion
    hU.fromSpec E (hlocal ⟨U, hU⟩) (hU.primeIdealOf ⟨x, hxU⟩)
  simpa only [IsAffineOpen.fromSpec_primeIdealOf] using H

end DeJongAlterations.Geometry.SNCSubdivisorCartier
