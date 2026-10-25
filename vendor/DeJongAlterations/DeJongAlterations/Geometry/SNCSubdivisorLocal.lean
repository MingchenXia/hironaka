import DeJongAlterations.Geometry.SNCSubdivisorComponent

/-!
# Actual affine prime ideals of SNC components

The height-one and regular-quotient data are extracted from native
singleton intersections and actual generic points.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.SNCSubdivisorLocal

open Scheme.IdealSheafData SpecIdealSheaf ReducedClosedSubscheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}}

/-- The actual affine prime of a native SNC component is height one and has actual regular quotient. -/
theorem component_affine_prime_data [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (U : X.affineOpens)
    (hmeet : ((C.val : Set X) ∩ Set.range U.2.fromSpec).Nonempty) :
    let I := (vanishingIdeal C.val).ideal U
    I.IsPrime ∧ I.height = 1 ∧ IsRegularRing (Γ(X, U.1) ⧸ I) := by
  classical
  let A := Γ(X, U.1)
  let f := U.2.fromSpec
  let E := vanishingIdeal C.val
  let I := E.ideal U
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have hEI : E.comap f = specIdealSheaf A I := BlowupCartier.comap_fromSpec E U
  have hsupp : ((specIdealSheaf A I).support : Set (Spec A)) =
      f ⁻¹' (C.val : Set X) := by
    rw [← hEI, support_comap]
    rfl
  have hirr : IsIrreducible (C.val : Set X) := SNCLocality.divisorComponent_isIrreducible D C
  have hirr' := hirr.preimage f.isOpenEmbedding hmeet
  have hrad : I.radical = I :=
    congrArg (fun E : X.IdealSheafData ↦ E.ideal U) (radical_vanishingIdeal C.val)
  let : I.IsPrime :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I
      (Ideal.radical_eq_iff.mp hrad)).mp (by
        rw [← specIdealSheaf_support, hsupp]
        exact hirr')
  have hreg : IsRegularScheme E.subscheme := by
    simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left] using
      hD.intersectionsRegular {C} (Finset.singleton_nonempty C)
  have hregI : IsRegularScheme (specIdealSheaf A I).subscheme := by
    rw [← hEI]
    exact hreg.of_isOpenImmersion (SNCLocality.comapSubschemeMap f E)
  have hquot : IsRegularRing (A ⧸ I) :=
    SNCSubdivisorComponent.isRegularRing_quotient_of_specIdealSheaf I hregI
  have hcodim : HasPureCodimension C.val 1 := by
    simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left,
      support_vanishingIdeal, Finset.card_singleton] using
      hD.intersectionsCodimension {C} (Finset.singleton_nonempty C)
  let q : Spec A := (⟨I, inferInstance⟩ : PrimeSpectrum A)
  have hq : IsGenericPoint q (f ⁻¹' (C.val : Set X)) := by
    have h := PrimeSpectrum.closure_singleton (⟨I, inferInstance⟩ : PrimeSpectrum A)
    exact h.trans ((specIdealSheaf_support A I).symm.trans hsupp)
  have hfq : IsGenericPoint (f q) (C.val : Set X) := by
    have h := hq.image f.continuous
    have hcl := SNCLocality.componentRestrict_closure f D C hmeet
    change closure (f '' (f ⁻¹' (C.val : Set X))) = (C.val : Set X) at hcl
    rw [hcl] at h
    exact h
  let : IrreducibleSpace C.val := Subtype.irreducibleSpace hirr
  have hcomp : (Set.univ : Set C.val) ∈ irreducibleComponents C.val := by
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
  have hgeneric : IsGenericPoint (f q) ((Subtype.val : C.val → X) '' Set.univ) := by
    have himage : (Subtype.val : C.val → X) '' Set.univ = (C.val : Set X) := by
      ext y
      simp
    rw [himage]
    exact hfq
  have hdim := hcodim Set.univ hcomp (f q) hgeneric
  have hdim' : ringKrullDim ((Spec A).presheaf.stalk q) = 1 :=
    (ringKrullDim_eq_of_ringEquiv
      (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv).symm.trans hdim
  have hheight : I.height = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight] at hdim'
    exact_mod_cast hdim'
  exact ⟨inferInstance, hheight, hquot⟩

/-- Extension of the actual component prime to any containing point preserves its height one. -/
theorem component_affine_height_atPrime [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (U : X.affineOpens)
    (hmeet : ((C.val : Set X) ∩ Set.range U.2.fromSpec).Nonempty)
    (p : Ideal Γ(X, U.1)) [p.IsPrime]
    (hIp : (vanishingIdeal C.val).ideal U ≤ p) :
    (((vanishingIdeal C.val).ideal U).map
      (algebraMap Γ(X, U.1) (Localization.AtPrime p))).height = 1 := by
  let I := (vanishingIdeal C.val).ideal U
  obtain ⟨hp, hheight, _⟩ := component_affine_prime_data D hD C U hmeet
  let : I.IsPrime := hp
  have hd : Disjoint (p.primeCompl : Set Γ(X, U.1)) (I : Set Γ(X, U.1)) :=
    Set.disjoint_left.mpr (fun x hxM hxI ↦ hxM (hIp hxI))
  exact (IsLocalization.height_map_of_disjoint (S := Localization.AtPrime p)
    p.primeCompl I hd).trans hheight

/-- Distinct actual global components meeting an affine chart have distinct actual affine ideals. -/
theorem component_affine_ideal_injective
    (D : X.IdealSheafData) (U : X.affineOpens)
    (C C' : DivisorComponent D)
    (hC : ((C.val : Set X) ∩ Set.range U.2.fromSpec).Nonempty)
    (hC' : ((C'.val : Set X) ∩ Set.range U.2.fromSpec).Nonempty)
    (heq : (vanishingIdeal C.val).ideal U = (vanishingIdeal C'.val).ideal U) :
    C = C' := by
  have heqE : (vanishingIdeal C.val).comap U.2.fromSpec =
      (vanishingIdeal C'.val).comap U.2.fromSpec := by
    rw [BlowupCartier.comap_fromSpec, BlowupCartier.comap_fromSpec, heq]
  have heqS := congrArg Scheme.IdealSheafData.support heqE
  simp only [support_comap, support_vanishingIdeal] at heqS
  apply SNCLocality.componentRestrict_injective U.2.fromSpec D C C' hC hC'
  apply Subtype.ext
  exact heqS

end DeJongAlterations.Geometry.SNCSubdivisorLocal
