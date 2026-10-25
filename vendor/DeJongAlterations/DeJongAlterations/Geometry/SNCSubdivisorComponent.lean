import DeJongAlterations.Geometry.SNCSubdivisorAffine
import DeJongAlterations.Geometry.SNCLocality

/-!
# Actual regular codimension-one closed components are Cartier

Actual affine restrictions, quotient spectra and local-ring isomorphisms
provide the regular local equations. No local principality is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.SNCSubdivisorComponent

open SpecIdealSheaf ReducedClosedSubscheme Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R]

/-- Regular native spectrum stalks give the actual regular coordinate ring. -/
theorem isRegularRing_of_spec [IsNoetherianRing R]
    (hR : IsRegularScheme (Spec (CommRingCat.of R))) : IsRegularRing R := by
  apply isRegularRing_iff.mpr
  intro p hp
  let q : Spec (CommRingCat.of R) := (⟨p, hp⟩ : PrimeSpectrum R)
  let : IsRegularLocalRing ((Spec (CommRingCat.of R)).presheaf.stalk q) := hR q
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of R) q).commRingCatIsoToRingEquiv

/-- Regularity of the actual closed subscheme implies regularity of its original quotient ring. -/
theorem isRegularRing_quotient_of_specIdealSheaf [IsNoetherianRing R]
    (I : Ideal R) (hI : IsRegularScheme (specIdealSheaf R I).subscheme) :
    IsRegularRing (R ⧸ I) := by
  let D := specIdealSheaf R I
  let U : (Spec (CommRingCat.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let f := D.subschemeCover.f U
  let : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have hspec : IsRegularScheme
      (Spec (CommRingCat.of (Γ(Spec (CommRingCat.of R), ⊤) ⧸ D.ideal U))) :=
    hI.of_isOpenImmersion f
  let : IsRegularRing (Γ(Spec (CommRingCat.of R), ⊤) ⧸ D.ideal U) :=
    isRegularRing_of_spec hspec
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let eQ := Ideal.quotientEquiv I (D.ideal U) e (specIdealSheaf_ideal_top R I)
  exact IsRegularRing.of_ringEquiv eQ.symm

variable {X : Scheme.{u}}

/-- A genuine regular irreducible codimension-one closed subscheme has its actual Cartier ideal. -/
theorem isEffectiveCartierDivisor_vanishingIdeal [IsLocallyNoetherian X]
    (C : Closeds X) (hirr : IsIrreducible (C : Set X))
    (hcodim : HasPureCodimension C 1)
    (hreg : IsRegularScheme (vanishingIdeal C).subscheme)
    (hambient : ∀ x : X, x ∈ C → IsRegularLocalRing (X.presheaf.stalk x)) :
    IsEffectiveCartierDivisor (vanishingIdeal C) := by
  let E := vanishingIdeal C
  have hlocal : ∀ U : X.affineOpens,
      IsEffectiveCartierDivisor (E.comap U.2.fromSpec) := by
    intro U
    let A := Γ(X, U.1)
    let f := U.2.fromSpec
    let I := E.ideal U
    let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
    have hEI : E.comap f = specIdealSheaf A I := BlowupCartier.comap_fromSpec E U
    have hsupp : ((specIdealSheaf A I).support : Set (Spec A)) =
        f ⁻¹' (C : Set X) := by
      rw [← hEI, support_comap]
      rfl
    by_cases hmeet : ((C : Set X) ∩ Set.range f).Nonempty
    · have hirr' : IsIrreducible (f ⁻¹' (C : Set X)) :=
        hirr.preimage f.isOpenEmbedding hmeet
      have hrad : I.radical = I :=
        congrArg (fun D : X.IdealSheafData ↦ D.ideal U) (radical_vanishingIdeal C)
      let : I.IsPrime :=
        (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I
          (Ideal.radical_eq_iff.mp hrad)).mp (by
            rw [← specIdealSheaf_support, hsupp]
            exact hirr')
      have hregI : IsRegularScheme (specIdealSheaf A I).subscheme := by
        rw [← hEI]
        exact hreg.of_isOpenImmersion (SNCLocality.comapSubschemeMap f E)
      let : IsRegularRing (A ⧸ I) := isRegularRing_quotient_of_specIdealSheaf I hregI
      let q : Spec A := (⟨I, inferInstance⟩ : PrimeSpectrum A)
      have hq : IsGenericPoint q (f ⁻¹' (C : Set X)) := by
        have h := PrimeSpectrum.closure_singleton (⟨I, inferInstance⟩ : PrimeSpectrum A)
        exact h.trans ((specIdealSheaf_support A I).symm.trans hsupp)
      have hclosure : closure (f '' (f ⁻¹' (C : Set X))) = (C : Set X) := by
        apply closure_image_preimage_of_isPreirreducible f f.isOpenEmbedding.isOpenMap
        · obtain ⟨_, hx, y, rfl⟩ := hmeet
          exact ⟨y, hx⟩
        · exact hirr.2
        · exact C.isClosed
      have hfq : IsGenericPoint (f q) (C : Set X) := by
        have h := hq.image f.continuous
        rw [hclosure] at h
        exact h
      let : IrreducibleSpace C := Subtype.irreducibleSpace hirr
      have hcomp : (Set.univ : Set C) ∈ irreducibleComponents C := by
        simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
      have hgeneric : IsGenericPoint (f q) ((Subtype.val : C → X) '' Set.univ) := by
        have himage : (Subtype.val : C → X) '' Set.univ = (C : Set X) := by
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
      rw [hEI]
      apply SNCSubdivisorAffine.isEffectiveCartierDivisor_of_prime_regular_quotient I hheight
      intro p hp hIp
      let y : Spec A := (⟨p, hp⟩ : PrimeSpectrum A)
      have hy : f y ∈ C := by
        have hyI : y ∈ ((specIdealSheaf A I).support : Set (Spec A)) := by
          rw [specIdealSheaf_support]
          exact hIp
        rw [hsupp] at hyI
        exact hyI
      let : IsRegularLocalRing (X.presheaf.stalk (f y)) := hambient (f y) hy
      let : IsRegularLocalRing ((Spec A).presheaf.stalk y) :=
        IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
      exact IsRegularLocalRing.of_ringEquiv
        (Spec.stalkIso A y).commRingCatIsoToRingEquiv
    · have hempty : (E.comap f).support = ⊥ := by
        ext y
        change y ∈ (E.comap f).support ↔ False
        constructor
        · intro hy
          rw [support_comap] at hy
          change f y ∈ C at hy
          exact hmeet ⟨f y, hy, y, rfl⟩
        · exact False.elim
      rw [(support_eq_bot_iff (E.comap f)).mp hempty]
      exact isEffectiveCartierDivisor_top _
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := (⊤ : X.Opens)) (by trivial)
  have H := CartierLocality.exists_affine_neighborhood_of_isOpenImmersion
    hU.fromSpec E (hlocal ⟨U, hU⟩) (hU.primeIdealOf ⟨x, hxU⟩)
  simpa only [IsAffineOpen.fromSpec_primeIdealOf] using H

/-- Every actual SNC component is contained in the actual full support. -/
theorem component_le_support (D : X.IdealSheafData) (C : DivisorComponent D) :
    C.val ≤ D.support := by
  intro x hx
  obtain ⟨S, _, hSC⟩ := C.property
  change x ∈ (C.val : Set X) at hx
  rw [← hSC] at hx
  obtain ⟨z, _, rfl⟩ := hx
  exact z.property

/-- The actual reduced vanishing ideal of each native SNC component is Cartier. -/
theorem component_isEffectiveCartierDivisor [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D) (C : DivisorComponent D) :
    IsEffectiveCartierDivisor (vanishingIdeal C.val) := by
  classical
  apply isEffectiveCartierDivisor_vanishingIdeal C.val
    (SNCLocality.divisorComponent_isIrreducible D C)
  · simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left,
      support_vanishingIdeal, Finset.card_singleton] using
      hD.intersectionsCodimension {C} (Finset.singleton_nonempty C)
  · simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left] using
      hD.intersectionsRegular {C} (Finset.singleton_nonempty C)
  · intro x hx
    exact hD.regularAlong x (component_le_support D C hx)

end DeJongAlterations.Geometry.SNCSubdivisorComponent
