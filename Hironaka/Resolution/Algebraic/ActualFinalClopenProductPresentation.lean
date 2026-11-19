import Hironaka.Resolution.Algebraic.ActualPaddedPrincipalizationTranslationEquivariance
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SigmaCharts

/-!
# Actual final clopen relative products of ONE inherited native history

Source-first proof: `actual-final-clopen-product-presentation-20261102.tex`.
Every final piece is the endpoint of a restriction of the SAME original clock.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.BlowUpSequence Hironaka.Sequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualFinalClopenProductPresentation

noncomputable section

/-- The genuine last-stage square, including its actual native index transport. -/
theorem lastStage_isPullback {X Y : Scheme.{u}} (A : X.BlowUpSequence)
    (q : Y ⟶ X) [Flat q] :
    IsPullback (A.pullbackLastHom q) (A.pullback q).composite A.composite q := by
  let c := eqToHom (congrArg (A.pullback q).stage (pullbackStageIdx_last A q).symm)
  have hc : IsPullback c (c ≫ (A.pullback q).stageMap (A.pullbackStageIdx q (Fin.last _)))
      ((A.pullback q).stageMap (A.pullbackStageIdx q (Fin.last _))) (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := hc.paste_horiz (isPullback_pullbackStageHom A q (Fin.last _))
  rw [Category.id_comp] at h
  change IsPullback (A.pullbackLastHom q) (c ≫ (A.pullback q).stageMap
    (A.pullbackStageIdx q (Fin.last _))) A.composite q at h
  rw [← stageMap_eq_idx (A.pullback q) (pullbackStageIdx_last A q)] at h
  exact h

private theorem coproductDesc_isIso_of_disjoint_cover {ι : Type} {F : ι → Scheme.{u}}
    {X : Scheme.{u}} (j : ∀ i, F i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hdisj : Pairwise (fun i l => Disjoint (Set.range (j i)) (Set.range (j l))))
    (hcover : ∀ x : X, ∃ i, ∃ y : F i, j i y = x) : IsIso (Sigma.desc j) := by
  have : IsOpenImmersion (Sigma.desc j) := isOpenImmersion_sigmaDesc F j hdisj
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_le_iff.mp
  intro x hx
  obtain ⟨i,y,rfl⟩ := hcover x
  refine ⟨Sigma.ι F i y,?_⟩
  exact congrArg (fun f => f y) (Sigma.ι_desc j i)

/-! The summand argument is universe-polymorphic in the schemes while retaining
the ORIGINAL Type0 labels. It changes no coproduct or history index. -/
private theorem sigmaMap_apply {ι : Type} {W B : ι → Scheme.{u}}
    (j : ∀ i, W i ⟶ B i) (i : ι) (w : W i) :
    Limits.Sigma.map j (Sigma.ι W i w) = Sigma.ι B i (j i w) := by
  change (Sigma.ι W i ≫ Limits.Sigma.map j) w = _
  rw [Sigma.ι_map]
  rfl

private theorem sigmaMap_piece_isPullback {ι : Type} {W B : ι → Scheme.{u}}
    (j : ∀ i, W i ⟶ B i) (i : ι) :
    IsPullback (j i) (Sigma.ι W i) (Sigma.ι B i) (Limits.Sigma.map j) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (Sigma.ι_map j i)
  ext z
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := Scheme.Hom.mem_opensRange.mp hz
    obtain ⟨l,w,rfl⟩ := (sigmaOpenCover W).exists_eq z
    change Sigma.ι B i b = Limits.Sigma.map j (Sigma.ι W l w) at hb
    change Sigma.ι W l w ∈ (Sigma.ι W i).opensRange
    rw [sigmaMap_apply] at hb
    obtain ⟨rfl,-⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff B i l _ _).mp hb)
    exact Scheme.Hom.mem_opensRange.mpr ⟨w,rfl⟩
  · intro hz
    obtain ⟨w,hw⟩ := Scheme.Hom.mem_opensRange.mp hz
    refine Scheme.Hom.mem_opensRange.mpr ⟨j i w,?_⟩
    rw [← hw,sigmaMap_apply]

private theorem sigmaMap_sigmaDesc_isPullback {ι : Type} {W B : ι → Scheme.{u}}
    (j : ∀ i, W i ⟶ B i) {Y X : Scheme.{u}} (e : ∀ i, W i ⟶ Y)
    (f : ∀ i, B i ⟶ X) (p : Y ⟶ X)
    (h : ∀ i, IsPullback (j i) (e i) (f i) p) :
    IsPullback (Limits.Sigma.map j) (Sigma.desc e) (Sigma.desc f) p := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (sigmaOpenCover B) fun i => ?_
  have hi := (sigmaMap_piece_isPullback j i).flip
  refine (h i).of_iso hi.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change j i ≫ 𝟙 (B i) = hi.isoPullback.hom ≫ pullback.snd (Limits.Sigma.map j) (Sigma.ι B i)
    rw [Category.comp_id,hi.isoPullback_hom_snd]
  · change e i ≫ 𝟙 Y =
      hi.isoPullback.hom ≫ pullback.fst (Limits.Sigma.map j) (Sigma.ι B i) ≫ Sigma.desc e
    rw [Category.comp_id,← Category.assoc,hi.isoPullback_hom_fst]
    exact (Sigma.ι_desc e i).symm
  · change f i ≫ 𝟙 X = 𝟙 (B i) ≫ Sigma.ι B i ≫ Sigma.desc f
    rw [Category.comp_id,Category.id_comp]
    exact (Sigma.ι_desc f i).symm
  · simp

section ActualPartition
variable {ι : Type} {X : Scheme.{u}} (U : ι → X.Opens) (V : ι → Type u)
  (A : X.BlowUpSequence)

/-- Actual endpoint of the restriction of the ONE original history, with its entire clock. -/
def restrictedEndpoint (i : ι) : Scheme.{u} := (A.pullback (U i).ι).last

/-- The actual last-stage inclusion of this SAME restricted history. -/
def restrictedEndpointInclusion (i : ι) : restrictedEndpoint U A i ⟶ A.last :=
  A.pullbackLastHom (U i).ι

private instance restrictedEndpointInclusion_isOpenImmersion (i : ι) :
    IsOpenImmersion (restrictedEndpointInclusion U A i) :=
  property_of_isPullback _ (lastStage_isPullback A (U i).ι) inferInstance

/-- Actual coproduct map of endpoints of restrictions of the SAME whole history. -/
def restrictedEndpointsDesc : (∐ restrictedEndpoint U A) ⟶ A.last :=
  Sigma.desc (restrictedEndpointInclusion U A)

/-- The actual final pieces form the SAME base endpoint, proved from the real partition geometry. -/
theorem restrictedEndpointsDesc_isIso (hcover : (⨆ i, U i) = ⊤)
    (hdisj : Pairwise (fun i l => Disjoint (U i : Set X) (U l : Set X))) :
    IsIso (restrictedEndpointsDesc U A) := by
  apply coproductDesc_isIso_of_disjoint_cover
  · intro i l hil
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy⟩ ⟨z,hz⟩
    have hi : A.composite x ∈ U i := by
      rw [← hy,← Scheme.Hom.comp_apply,restrictedEndpointInclusion,pullbackLastHom_comp_composite]
      exact ((A.pullback (U i).ι).composite y).property
    have hl : A.composite x ∈ U l := by
      rw [← hz,← Scheme.Hom.comp_apply,restrictedEndpointInclusion,pullbackLastHom_comp_composite]
      exact ((A.pullback (U l).ι).composite z).property
    exact Set.disjoint_left.mp (hdisj hil) hi hl
  · intro x
    have hx : A.composite x ∈ ⨆ i, U i := by rw [hcover]; trivial
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨y,hy,-⟩ := Scheme.exists_preimage_of_isPullback
      (lastStage_isPullback A (U i).ι) x (⟨A.composite x,hi⟩ : (U i).toScheme) rfl
    exact ⟨i,y,hy⟩

private def initialPiecesDesc : (∐ fun i => (U i).toScheme) ⟶ X := Sigma.desc (fun i => (U i).ι)

private theorem initialPiecesDesc_isIso (hcover : (⨆ i, U i) = ⊤)
    (hdisj : Pairwise (fun i l => Disjoint (U i : Set X) (U l : Set X))) :
    IsIso (initialPiecesDesc U) := by
  apply coproductDesc_isIso_of_disjoint_cover
  · simpa only [Scheme.Opens.range_ι] using hdisj
  · intro x
    have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨i,⟨x,hi⟩,rfl⟩

/-- Actual original padded projection built from the given original partition. -/
def clopenPaddedProjection : (∐ fun i => AffineSpace (V i) (U i).toScheme) ⟶ X :=
  Sigma.desc (fun i => (AffineSpace (V i) (U i).toScheme ↘ (U i).toScheme) ≫ (U i).ι)

private theorem clopenPaddedProjection_factor :
    clopenPaddedProjection U V =
      Limits.Sigma.map (fun i => AffineSpace (V i) (U i).toScheme ↘ (U i).toScheme) ≫ initialPiecesDesc U := by
  apply Sigma.hom_ext
  intro i
  rw [clopenPaddedProjection,Sigma.ι_desc,← Category.assoc,Sigma.ι_map,
    Category.assoc,initialPiecesDesc,Sigma.ι_desc]

private theorem clopenPaddedProjection_piece (hcover : (⨆ i, U i) = ⊤)
    (hdisj : Pairwise (fun i l => Disjoint (U i : Set X) (U l : Set X))) (i : ι) :
    IsPullback (AffineSpace (V i) (U i).toScheme ↘ (U i).toScheme)
      (Sigma.ι (fun l => AffineSpace (V l) (U l).toScheme) i) (U i).ι (clopenPaddedProjection U V) := by
  have := initialPiecesDesc_isIso U hcover hdisj
  refine (sigmaMap_piece_isPullback
    (fun i => AffineSpace (V i) (U i).toScheme ↘ (U i).toScheme) i).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (initialPiecesDesc U)) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [initialPiecesDesc]
  · change Limits.Sigma.map (fun i => AffineSpace (V i) (U i).toScheme ↘ (U i).toScheme) ≫
      initialPiecesDesc U = clopenPaddedProjection U V
    exact (clopenPaddedProjection_factor U V).symm

/-- Actual varying-rank relative projection over the SAME canonical endpoint. -/
def finalProductProjection : (∐ fun i => AffineSpace (V i) (restrictedEndpoint U A i)) ⟶ A.last :=
  Limits.Sigma.map (fun i => AffineSpace (V i) (restrictedEndpoint U A i) ↘ restrictedEndpoint U A i) ≫
    restrictedEndpointsDesc U A

/-- Actual original padded map, using each restricted history's SAME composite. -/
def finalProductOriginalMap : (∐ fun i => AffineSpace (V i) (restrictedEndpoint U A i)) ⟶
    ∐ fun i => AffineSpace (V i) (U i).toScheme :=
  Sigma.desc (fun i => AffineSpace.map (V i) (A.pullback (U i).ι).composite ≫
    Sigma.ι (fun l => AffineSpace (V l) (U l).toScheme) i)

/-- Genuine actual final product comparison, derived by TWO global cartesian squares. -/
theorem exists_finalClopenProductIso (hcover : (⨆ i, U i) = ⊤)
    (hdisj : Pairwise (fun i l => Disjoint (U i : Set X) (U l : Set X)))
    [Flat (clopenPaddedProjection U V)] :
    ∃ e : (∐ fun i => AffineSpace (V i) (restrictedEndpoint U A i)) ≅
        (A.pullback (clopenPaddedProjection U V)).last,
      e.hom ≫ A.pullbackLastHom (clopenPaddedProjection U V) = finalProductProjection U V A ∧
      e.hom ≫ (A.pullback (clopenPaddedProjection U V)).composite = finalProductOriginalMap U V A := by
  have hpiece : ∀ i, IsPullback (AffineSpace (V i) (restrictedEndpoint U A i) ↘ restrictedEndpoint U A i)
      (AffineSpace.map (V i) (A.pullback (U i).ι).composite ≫
        Sigma.ι (fun l => AffineSpace (V l) (U l).toScheme) i)
      (restrictedEndpointInclusion U A i ≫ A.composite) (clopenPaddedProjection U V) := by
    intro i
    have h := (AffineSpace.isPullback_map (n := V i) (A.pullback (U i).ι).composite).flip.paste_vert
      (clopenPaddedProjection_piece U V hcover hdisj i)
    rw [← pullbackLastHom_comp_composite] at h
    exact h
  have hSigma := sigmaMap_sigmaDesc_isPullback
    (fun i => AffineSpace (V i) (restrictedEndpoint U A i) ↘ restrictedEndpoint U A i)
    (fun i => AffineSpace.map (V i) (A.pullback (U i).ι).composite ≫
      Sigma.ι (fun l => AffineSpace (V l) (U l).toScheme) i)
    (fun i => restrictedEndpointInclusion U A i ≫ A.composite) (clopenPaddedProjection U V) hpiece
  have := restrictedEndpointsDesc_isIso U A hcover hdisj
  have hnew : IsPullback (finalProductProjection U V A) (finalProductOriginalMap U V A)
      A.composite (clopenPaddedProjection U V) := by
    refine hSigma.of_iso (Iso.refl _) (asIso (restrictedEndpointsDesc U A)) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom,Category.id_comp]
      rfl
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
      rfl
    · simp only [Iso.refl_hom,Category.comp_id]
      apply Sigma.hom_ext
      intro i
      simp [restrictedEndpointsDesc]
    · simp
  let e := hnew.isoIsPullback _ _ (lastStage_isPullback A (clopenPaddedProjection U V))
  exact ⟨e,hnew.isoIsPullback_hom_fst _ _ _,hnew.isoIsPullback_hom_snd _ _ _⟩
end ActualPartition

open ActualDimensionGroupBlowup ActualDimensionGroupPaddedCover
  ActualPaddedEnvelopeNativeTranslations ActualRelativeAffineHistoryDescent
  ActualPaddedNativePrincipalizationInput

section OriginalInput
variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

private theorem nativeProductExists :
    ∃ e : (∐ fun d : dimensionIndex R => AffineSpace (paddingVariables R k d)
        (restrictedEndpoint (dimensionPartOpen R) (nativeBaseHistory R k) d)) ≅
      (nativePaddedHistory R k).last,
      e.hom ≫ paddedFinalProjection R k =
        finalProductProjection (dimensionPartOpen R) (paddingVariables R k) (nativeBaseHistory R k) ∧
      e.hom ≫ (nativePaddedHistory R k).composite =
        finalProductOriginalMap (dimensionPartOpen R) (paddingVariables R k) (nativeBaseHistory R k) := by
  have : Smooth (clopenPaddedProjection (dimensionPartOpen R) (paddingVariables R k)) :=
    envelopeProjection_smooth R k
  obtain ⟨e,he₁,he₂⟩ := exists_finalClopenProductIso (dimensionPartOpen R) (paddingVariables R k)
    (nativeBaseHistory R k) (dimension_group_clopen_partition R).1
      (dimension_group_clopen_partition R).2.1
  let c := eqToIso (congrArg Scheme.BlowUpSequence.last
    (nativePaddedHistory_canonical_history_descends R k))
  refine ⟨e ≪≫ c.symm,?_,?_⟩
  · change (e.hom ≫ c.inv) ≫ (c.hom ≫ (nativeBaseHistory R k).pullbackLastHom
      (envelopeProjection R k)) = _
    rw [Category.assoc,Iso.inv_hom_id_assoc]
    exact he₁
  · change (e.hom ≫ c.inv) ≫ (nativePaddedHistory R k).composite = _
    have hc : c.inv ≫ (nativePaddedHistory R k).composite =
        ((nativeBaseHistory R k).pullback (envelopeProjection R k)).composite :=
      eqToHom_comp_composite_of_eq (nativePaddedHistory_canonical_history_descends R k).symm
    rw [Category.assoc,hc]
    exact he₂

/-- Actual final product isomorphism for the ONE original native history, internally constructed. -/
def nativeFinalProductIso : (∐ fun d : dimensionIndex R => AffineSpace (paddingVariables R k d)
    (restrictedEndpoint (dimensionPartOpen R) (nativeBaseHistory R k) d)) ≅
      (nativePaddedHistory R k).last := (nativeProductExists R k).choose

/-- The actual product comparison has the SAME genuine final projection. -/
theorem nativeFinalProductIso_projection :
    (nativeFinalProductIso R k).hom ≫ paddedFinalProjection R k =
      finalProductProjection (dimensionPartOpen R) (paddingVariables R k) (nativeBaseHistory R k) :=
  (nativeProductExists R k).choose_spec.1

/-- The actual product comparison retains the SAME original native composite map. -/
theorem nativeFinalProductIso_original_map :
    (nativeFinalProductIso R k).hom ≫ (nativePaddedHistory R k).composite =
      finalProductOriginalMap (dimensionPartOpen R) (paddingVariables R k) (nativeBaseHistory R k) :=
  (nativeProductExists R k).choose_spec.2
end OriginalInput

end
end Hironaka.Resolution.Algebraic.ActualFinalClopenProductPresentation
