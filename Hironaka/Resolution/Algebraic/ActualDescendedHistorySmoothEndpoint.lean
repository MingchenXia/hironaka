import Hironaka.Resolution.Algebraic.ActualRelativeAffineHistoryDescent
import Hironaka.Scheme.BlowUpSequence.Triple

/-!
# The actual descended native history has a smooth endpoint

Source-first proof: `actual-descended-history-smooth-endpoint-20261102.tex`.
Actual affine split retractions reflect smoothness, and the actual native
flat-pullback stage squares supply the necessary stagewise sections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v w

namespace Hironaka.Resolution.Algebraic.ActualDescendedHistorySmoothEndpoint

noncomputable section

/-- Formal smoothness is inherited by an actual ring retract over the original base. -/
theorem formallySmooth_of_ring_retract {R : Type u} {A : Type v} {P : Type w}
    [CommRing R] [CommRing A] [CommRing P]
    (f : R →+* A) (i : A →+* P) (r : P →+* A)
    (hr : r.comp i = RingHom.id A) (hP : (i.comp f).FormallySmooth) : f.FormallySmooth := by
  let := f.toAlgebra
  let := (i.comp f).toAlgebra
  let i' : A →ₐ[R] P := { i with commutes' := fun _ => rfl }
  let r' : P →ₐ[R] A := { r with commutes' := fun x => DFunLike.congr_fun hr (f x) }
  have : Algebra.FormallySmooth R P := hP
  apply Algebra.FormallySmooth.of_split r' ((Ideal.Quotient.mkₐ R _).comp i')
  ext x
  simp only [AlgHom.comp_apply]
  exact DFunLike.congr_fun hr x

/-- Reflect smoothness through an actual affine map with an actual section. -/
theorem smooth_of_affine_split {X Y Z : Scheme.{u}} (f : X ⟶ Z) (q : Y ⟶ X)
    [LocallyOfFinitePresentation f] [IsAffineHom q] (s : X ⟶ Y)
    (hs : s ≫ q = 𝟙 X) [Smooth (q ≫ f)] : Smooth f := by
  constructor
  intro V hV U hU e
  let W := q ⁻¹ᵁ U
  have hsU : U ≤ s ⁻¹ᵁ W := by
    intro x hx
    change q (s x) ∈ U
    have hp : q (s x) = x := congrArg (fun g => g x) hs
    exact hp.symm ▸ hx
  have eW : W ≤ (q ≫ f) ⁻¹ᵁ V := q.preimage_mono e
  let i := (q.appLE U W le_rfl).hom
  let r := (s.appLE W U hsU).hom
  have hri : r.comp i = RingHom.id Γ(X,U) := by
    change (q.appLE U W le_rfl ≫ s.appLE W U hsU).hom = _
    rw [Scheme.Hom.appLE_comp_appLE]
    have hid : ∀ (g : X ⟶ X), g = 𝟙 X → ∀ (h : U ≤ g ⁻¹ᵁ U),
        g.appLE U U h = 𝟙 Γ(X,U) := by
      rintro g rfl h
      simp [Scheme.Hom.appLE]
      exact X.presheaf.map_id _
    exact congrArg CommRingCat.Hom.hom (hid (s ≫ q) hs _)
  have hcomp : i.comp (f.appLE V U e).hom = ((q ≫ f).appLE V W eW).hom := by
    change (f.appLE V U e ≫ q.appLE U W le_rfl).hom = _
    rw [Scheme.Hom.appLE_comp_appLE]
  apply RingHom.smooth_def.mpr
  refine ⟨formallySmooth_of_ring_retract _ i r hri ?_, f.finitePresentation_appLE hV hU e⟩
  rw [hcomp]
  exact ((q ≫ f).smooth_appLE hV (hU.preimage q) eW).formallySmooth

/-- The genuine flat-pullback stage square constructs a compatible actual section. -/
theorem pullback_stage_has_section {X Y : Scheme.{u}} (S : X.BlowUpSequence)
    (q : Y ⟶ X) [Flat q] (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X)
    (i : Fin (S.length + 1)) :
    ∃ t : S.stage i ⟶ (S.pullback q).stage (S.pullbackStageIdx q i),
      t ≫ S.pullbackStageHom q i = 𝟙 (S.stage i) ∧
      t ≫ (S.pullback q).stageMap (S.pullbackStageIdx q i) = S.stageMap i ≫ s := by
  apply (isPullback_pullbackStageHom S q i).exists_lift (𝟙 _) (S.stageMap i ≫ s)
  simp [hs]

/-- Smoothness of a SAME actual pullback stage reflects to the actual base stage. -/
theorem history_stage_smooth_descends {X Y Z : Scheme.{u}}
    (S : X.BlowUpSequence) (q : Y ⟶ X) [Flat q] [IsAffineHom q]
    (s : X ⟶ Y) (hs : s ≫ q = 𝟙 X) (i : Fin (S.length + 1)) (f : X ⟶ Z)
    [LocallyOfFinitePresentation (S.stageMap i ≫ f)]
    [Smooth ((S.pullback q).stageMap (S.pullbackStageIdx q i) ≫ q ≫ f)] :
    Smooth (S.stageMap i ≫ f) := by
  let p := S.pullbackStageHom q i
  have : IsAffineHom p := property_of_isPullback _ (isPullback_pullbackStageHom S q i)
    (inferInstance : IsAffineHom q)
  obtain ⟨t,ht,-⟩ := pullback_stage_has_section S q s hs i
  have he : p ≫ (S.stageMap i ≫ f) =
      (S.pullback q).stageMap (S.pullbackStageIdx q i) ≫ q ≫ f := by
    rw [← Category.assoc, pullbackStageHom_stageMap, Category.assoc]
  have : Smooth (p ≫ (S.stageMap i ≫ f)) := he.symm ▸ inferInstance
  exact smooth_of_affine_split (S.stageMap i ≫ f) p t ht

open ActualDimensionGroupBlowup ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- The actual separation blowup's original coefficient structure morphism. -/
def separationStructure : affineBlowUp (dimensionSeparationIdeal R) ⟶ Spec (.of k) :=
  affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))

/-- The actual canonical base history has a smooth endpoint, derived from its SAME native pullback. -/
theorem nativeBaseHistory_smooth :
    Smooth ((nativeBaseHistory R k).composite ≫ separationStructure R k) := by
  let A := nativeBaseHistory R k
  let q := envelopeProjection R k
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType (separationStructure R k) := by
    dsimp only [separationStructure]
    infer_instance
  have : IsLocallyNoetherian (affineBlowUp (dimensionSeparationIdeal R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (separationStructure R k)
  have : IsProper A.composite := A.isProper_composite
  have : Smooth q := envelopeProjection_smooth R k
  have : IsAffineHom q := envelopeProjection_isAffineHom R k
  have hwhole : nativePaddedHistory R k = A.pullback q :=
    nativePaddedHistory_canonical_history_descends R k
  have : Smooth ((A.pullback q).composite ≫ q ≫ separationStructure R k) := by
    change Smooth ((A.pullback q).composite ≫ (paddedEnvelope R k).obj.hom)
    rw [← hwhole]
    exact (nativePaddedHistory_isStrongResolution R k).smooth
  have : Smooth ((A.pullback q).stageMap (A.pullbackStageIdx q (Fin.last _)) ≫
      q ≫ separationStructure R k) := by
    rw [pullbackStageIdx_last]
    change Smooth ((A.pullback q).composite ≫ q ≫ separationStructure R k)
    infer_instance
  have : LocallyOfFinitePresentation (A.stageMap (Fin.last _) ≫ separationStructure R k) := by
    change LocallyOfFinitePresentation (A.composite ≫ separationStructure R k)
    infer_instance
  exact history_stage_smooth_descends A q (envelopeZeroSection R k)
    (envelopeZeroSection_projection R k) (Fin.last _) (separationStructure R k)
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualDescendedHistorySmoothEndpoint
