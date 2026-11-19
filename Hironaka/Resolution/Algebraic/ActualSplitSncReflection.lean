import Hironaka.Resolution.Algebraic.LocalSplitSncParameters
import Hironaka.Scheme.Snc.HasSncWith

/-!
# SNC of the genuine ORIGINAL inverse singular support downstairs

Source-first proof: `actual-split-snc-reflection-20261102.tex`.
Actual stalk retractions and fixed-ideal parameter reflection prove SNC
of the specified descended canonical boundary on the SAME actual endpoint.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open Scheme.IdealSheafData Scheme.BlowUpSequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualSplitSncReflection

noncomputable section

/-- The genuine actual section induces a ring retraction of the actual local stalk map. -/
theorem section_stalk_retraction {X Y : Scheme.{u}} (q : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ q = 𝟙 X) (x : X) :
    ∃ β : Y.presheaf.stalk (s x) →+* X.presheaf.stalk (q (s x)),
      β.comp (q.stalkMap (s x)).hom = RingHom.id _ := by
  have hp : q (s x) = x := congrArg (fun f => f x) hs
  let e := X.presheaf.stalkCongr (.of_eq hp)
  have hcomp : q.stalkMap (s x) ≫ s.stalkMap x = e.hom := by
    rw [← Scheme.Hom.stalkMap_comp,Scheme.Hom.stalkMap_congr_hom _ _ hs,
      Scheme.Hom.stalkMap_id]
    change e.hom ≫ 𝟙 (X.presheaf.stalk x) = e.hom
    exact Category.comp_id _
  refine ⟨(s.stalkMap x ≫ e.inv).hom,?_⟩
  change (q.stalkMap (s x) ≫ (s.stalkMap x ≫ e.inv)).hom = _
  rw [← Category.assoc,hcomp,Iso.hom_inv_id]
  rfl

private theorem exists_isSncAt_of_split_pullback {X Y : Scheme.{u}}
    (q : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X)
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (E : Scheme.DivisorFamily X) (hE : (E.comap q).IsSnc) (x : X) :
    ∃ (m : ℕ) (t : Fin m → X.presheaf.stalk x), E.IsSncAt x t := by
  classical
  have hp : q (s x) = x := congrArg (fun f => f x) hs
  have : IsRegularLocalRing (X.presheaf.stalk (q (s x))) := hX _
  have : IsRegularLocalRing (Y.presheaf.stalk (s x)) := hY _
  obtain ⟨n,z,hz,c,hc,hI⟩ := hE.2 (s x)
  obtain ⟨β,hβ⟩ := section_stalk_retraction q s hs x
  let ι := {i : E.ι // q (s x) ∈ (E.component i).support}
  let a : ι → {i : (E.comap q).ι // s x ∈ ((E.comap q).component i).support} :=
    fun i => ⟨i.1,by
      change s x ∈ ((E.component i.1).comap q).support
      rw [support_comap]
      exact i.2⟩
  have ha : Function.Injective a := by
    intro i j h
    apply Subtype.ext
    exact congrArg (fun t : {i : (E.comap q).ι // s x ∈ ((E.comap q).component i).support} => t.1) h
  have hmap : ∀ i : ι, Ideal.map (q.stalkMap (s x)).hom
      ((E.component i.1).stalkIdeal (q (s x))) = Ideal.span {z (c (a i))} := by
    intro i
    rw [← stalkIdeal_comap]
    exact hI (a i)
  obtain ⟨m,t,ht,d,hd,hdt⟩ := LocalSplitSncParameters.fixed_ideals_are_parameters_of_local_retract
    (q.stalkMap (s x)).hom β hβ (fun i : ι => (E.component i.1).stalkIdeal (q (s x)))
      z hz (c ∘ a) (hc.comp ha) hmap
  have hresult : ∃ (m : ℕ) (t : Fin m → X.presheaf.stalk (q (s x))),
      E.IsSncAt (q (s x)) t := ⟨m,t,ht,d,hd,hdt⟩
  exact hp ▸ hresult

/-- The SAME specified downstairs family is SNC, derived from its actual split pullback. -/
theorem isSnc_of_split_pullback {X Y : Scheme.{u}}
    (q : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X)
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (E : Scheme.DivisorFamily X) (hE : (E.comap q).IsSnc) : E.IsSnc := by
  classical
  have hdata := exists_isSncAt_of_split_pullback q s hs hX hY E hE
  refine ⟨fun i => ?_,hdata⟩
  apply isRegular_subscheme_of_isRegularLocalRing_quotient
  intro x hx
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨m,t,ht,d,hd,hdt⟩ := hdata x
  apply isRegularLocalRing_quotient_stalkIdeal_of_eq_span ht
    (s := {d ⟨i,hx⟩})
  simpa only [Finset.coe_singleton,Set.image_singleton] using hdt ⟨i,hx⟩

open ActualDimensionGroupBlowup ActualPaddedEnvelopeNativeTranslations
  ActualRelativeAffineHistoryDescent ActualDescendedHistorySmoothEndpoint
  ActualOriginalSingPrincipalizationHistoryDescent ActualPrincipalizedEndpointGeometry
  ActualPrincipalizationCanonicalBoundary ActualPaddedNativePrincipalizationInput

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- Genuine SNC of the SAME specified descended canonical boundary. -/
theorem nativeBaseBoundary_isSnc : (nativeBaseBoundary R k).IsSnc := by
  let f : (nativeBasePrincipalizationHistory R k).last ⟶ Spec (.of k) :=
    (nativeBasePrincipalizationHistory R k).composite ≫
      (nativeBaseHistory R k).composite ≫ separationStructure R k
  have : Smooth f := nativePrincipalizedBase_smooth R k
  have : Smooth (nativePrincipalizedProjection R k) := nativePrincipalizedProjection_smooth R k
  exact isSnc_of_split_pullback (nativePrincipalizedProjection R k) (nativePrincipalizedSection R k)
    (nativePrincipalizedSection_projection R k) (fun x => isRegularLocalRing_stalk f x)
    (fun y => isRegularLocalRing_stalk (nativePrincipalizedProjection R k ≫ f) y)
    (nativeBaseBoundary R k) (nativeBaseBoundary_snc_pullback R k)

/-- The genuine ORIGINAL terminal singular ideal has an actual specified SNC support. -/
theorem nativePrincipalizedOriginalSupport_isSnc :
    Scheme.IsSncDivisor ((nativePrincipalizedOriginalIdeal R k).support :
      Set (nativeBasePrincipalizationHistory R k).last) := by
  exact ⟨nativeBaseBoundary R k,nativeBaseBoundary_isSnc R k,
    congrArg (fun Z : Closeds (nativeBasePrincipalizationHistory R k).last =>
      (Z : Set (nativeBasePrincipalizationHistory R k).last))
      (nativeBaseBoundary_original_support R k)⟩

/-- True SNC of the inverse ORIGINAL singular locus under the SAME actual terminal composite. -/
theorem nativeOriginalSing_inverse_image_isSncDivisor :
    Scheme.IsSncDivisor
      (((nativeBasePrincipalizationHistory R k).composite ≫ (nativeBaseHistory R k).composite ≫
        affineBlowUp.π (dimensionSeparationIdeal R)) ⁻¹' (Spec (.of R)).singularLocus) := by
  let f : Spec (.of R) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have : LocallyOfFiniteType f := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  have h := nativePrincipalizedOriginalSupport_isSnc R k
  rw [nativePrincipalizedOriginalIdeal,support_comap,Closeds.coe_preimage,
    Scheme.coe_support_singIdeal_eq_singularLocus f] at h
  exact h
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualSplitSncReflection
