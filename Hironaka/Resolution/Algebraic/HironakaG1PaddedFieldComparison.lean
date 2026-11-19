import Hironaka.Resolution.Algebraic.HironakaG1FieldExtensionLayers
import Hironaka.Resolution.Algebraic.ActualGlobalStrongResolutionSmoothNaturality
import Hironaka.Resolution.Algebraic.ActualAffineCoordinateForgetting
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SigmaCharts

/-!
# Actual dimension parts and the same padded native family under field extension

The source padding variables are transported through the actual dimension
labels. Existing padding-choice independence then identifies the resulting
base history with the canonical base history. No target history equality
or reduced-equidimensional target-input certificate is assumed.

The endpoint square transports the ORIGINAL mixed-dimensional singular
ideal before applying BP. Concatenation, flat-surjective cancellation and
native empty-stage pruning then compare the actual final assignment.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

universe u

namespace Hironaka.Resolution.Algebraic.HironakaG1PaddedFieldComparison

noncomputable section

open ActualIntrinsicComponentDimensions ActualGlobalDimensionClopenPartition
  ActualGlobalDimensionPiecePurity ActualGlobalVariablePaddingGeometry
  ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualGlobalOriginalSingPrincipalizationInput ActualGlobalStrongResolutionSmoothNaturality
  HironakaG1FieldExtensionLayers

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {X XL : Scheme.{u}} {f : X ⟶ Spec (.of k)} {fL : XL ⟶ Spec (.of L)}
  {p : XL ⟶ X}

def dimensionIndexEquiv
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] : dimensionIndex XL ≃ dimensionIndex X :=
  Equiv.setCongr (range_componentDimension_baseChange h)

theorem dimensionIndexEquiv_val
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] (d : dimensionIndex XL) :
    (dimensionIndexEquiv h d).val = d.val := rfl

section DimensionParts
variable [PerfectField k] [NoetherianSpace X] [NoetherianSpace XL]
  [LocallyOfFiniteType f]

theorem complementaryIdeal_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : WithBot ℕ∞) :
    (complementaryIdeal X d).comap p = complementaryIdeal XL d := by
  unfold complementaryIdeal
  rw [Hironaka.HironakaG1RVanishingIdealBaseChange.comap_vanishingIdeal_of_isPullback h,
    complementaryClosed_baseChange h]

theorem exceptionalIdeal_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    (exceptionalIdeal X).comap (separationMap_baseChange h) = exceptionalIdeal XL := by
  unfold exceptionalIdeal
  rw [← comap_comp, separationMap_baseChange_over, comap_comp, separationIdeal_baseChange h]

theorem normalizedIdeal_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    (normalizedIdeal X (dimensionIndexEquiv h d)).comap (separationMap_baseChange h) =
      normalizedIdeal XL d := by
  let : Flat (separationMap_baseChange h) := separationMap_baseChange_flat h
  rw [normalizedIdeal_flat_pullback]
  change (((complementaryIdeal X (dimensionIndexEquiv h d).val).comap (separationProjection X)).comap
      (separationMap_baseChange h)).colon ((exceptionalIdeal X).comap (separationMap_baseChange h)) =
    ((complementaryIdeal XL d.val).comap (separationProjection XL)).colon (exceptionalIdeal XL)
  rw [exceptionalIdeal_baseChange]
  congr 1
  rw [← comap_comp, separationMap_baseChange_over, comap_comp,
    complementaryIdeal_baseChange h, dimensionIndexEquiv_val]

theorem dimensionPartOpen_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    separationMap_baseChange h ⁻¹ᵁ dimensionPartOpen X (dimensionIndexEquiv h d) =
      dimensionPartOpen XL d := by
  ext x
  change ¬ separationMap_baseChange h x ∈ (normalizedIdeal X (dimensionIndexEquiv h d)).support ↔
    ¬ x ∈ (normalizedIdeal XL d).support
  rw [← normalizedIdeal_baseChange h d, support_comap]
  rfl
end DimensionParts

section ActualPaddedInput
variable [CharZero k] [CharZero L]
  [IsNoetherian X] [IsReduced X] [IsNoetherian XL] [IsReduced XL]
  [LocallyOfFiniteType f] [LocallyOfFiniteType fL] [IsSeparated f] [IsSeparated fL]

omit [CharZero k] [CharZero L] [AlgebraicGeometry.IsNoetherian X] [IsReduced X]
  [AlgebraicGeometry.IsNoetherian XL] [IsReduced XL] [IsSeparated f] [IsSeparated fL] in
theorem dimensionNat_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    dimensionNat fL d = dimensionNat f (dimensionIndexEquiv h d) := by
  exact_mod_cast (show (dimensionNat fL d : WithBot ℕ∞) =
      (dimensionNat f (dimensionIndexEquiv h d) : WithBot ℕ∞) by
    simp only [dimensionNat_spec, dimensionIndexEquiv_val])

omit [CharZero k] [CharZero L] [IsReduced X] [IsReduced XL]
  [IsSeparated f] [IsSeparated fL] in
theorem commonDimension_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    commonDimension fL = commonDimension f := by
  classical
  let : Fintype (dimensionIndex X) := Fintype.ofFinite _
  let : Fintype (dimensionIndex XL) := Fintype.ofFinite _
  apply le_antisymm
  · change Finset.univ.sup (dimensionNat fL) ≤ commonDimension f
    apply Finset.sup_le
    intro d _
    rw [dimensionNat_baseChange h]
    exact commonDimension_ge f (dimensionIndexEquiv h d)
  · change Finset.univ.sup (dimensionNat f) ≤ commonDimension fL
    apply Finset.sup_le
    intro d _
    have hd := commonDimension_ge fL ((dimensionIndexEquiv h).symm d)
    rw [dimensionNat_baseChange h, Equiv.apply_symm_apply] at hd
    exact hd

/-- The old source's literal coordinate types, indexed by the actual extended dimension labels. -/
abbrev transportedVariables
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) : Type u := paddingVariables f (dimensionIndexEquiv h d)

omit [CharZero k] [CharZero L] [IsReduced X] [AlgebraicGeometry.IsNoetherian XL]
  [IsReduced XL] [IsSeparated f] [IsSeparated fL] in
theorem transported_rank
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    dimensionNat fL d + Nat.card (transportedVariables h d) = commonDimension f := by
  rw [dimensionNat_baseChange h]
  exact padding_rank f (dimensionIndexEquiv h d)

private def openMapOfEq {A B : Scheme.{u}} (q : A ⟶ B) (U : A.Opens) (V : B.Opens)
    (h : q ⁻¹ᵁ V = U) : U.toScheme ⟶ V.toScheme :=
  eqToHom (congrArg (fun W : A.Opens => W.toScheme) h.symm) ≫ (q ∣_ V)

private theorem openMapOfEq_isPullback {A B : Scheme.{u}} (q : A ⟶ B)
    (U : A.Opens) (V : B.Opens) (h : q ⁻¹ᵁ V = U) :
    IsPullback (openMapOfEq q U V h) U.ι V.ι q := by
  subst U
  simpa only [openMapOfEq, eqToHom_refl, Category.id_comp] using isPullback_morphismRestrict q V

def dimensionPartMap
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) : pieceFamily XL d ⟶ pieceFamily X (dimensionIndexEquiv h d) :=
  openMapOfEq (separationMap_baseChange h) (dimensionPartOpen XL d)
    (dimensionPartOpen X (dimensionIndexEquiv h d)) (dimensionPartOpen_baseChange h d)

omit [CharZero L] [IsReduced X] [IsReduced XL] [LocallyOfFiniteType fL]
  [IsSeparated f] [IsSeparated fL] in
theorem dimensionPartMap_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    IsPullback (dimensionPartMap h d) (dimensionPartOpen XL d).ι
      (dimensionPartOpen X (dimensionIndexEquiv h d)).ι (separationMap_baseChange h) :=
  openMapOfEq_isPullback _ _ _ _

private abbrev targetPiece
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) : Scheme.{u} :=
  piece X (paddingVariables f) (dimensionIndexEquiv h d)

private def targetReindexIso
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    (∐ targetPiece h) ≅ envelope X (paddingVariables f) :=
  Sigma.whiskerEquiv (dimensionIndexEquiv h) (fun _ => Iso.refl _)

def paddedPieceMap
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    piece XL (transportedVariables h) d ⟶ targetPiece h d :=
  AffineSpace.map (paddingVariables f (dimensionIndexEquiv h d)) (dimensionPartMap h d)

omit [CharZero L] [IsReduced X] [IsReduced XL] [LocallyOfFiniteType fL]
  [IsSeparated f] [IsSeparated fL] in
theorem paddedPieceMap_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    IsPullback (paddedPieceMap h d)
      (pieceProjection XL (transportedVariables h) d ≫ (dimensionPartOpen XL d).ι)
      (pieceProjection X (paddingVariables f) (dimensionIndexEquiv h d) ≫
        (dimensionPartOpen X (dimensionIndexEquiv h d)).ι)
      (separationMap_baseChange h) :=
  (AffineSpace.isPullback_map (n := paddingVariables f (dimensionIndexEquiv h d))
    (dimensionPartMap h d)).paste_vert (dimensionPartMap_isPullback h d)

def paddedFieldMap
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    envelope XL (transportedVariables h) ⟶ envelope X (paddingVariables f) :=
  Limits.Sigma.map (paddedPieceMap h) ≫ (targetReindexIso h).hom

omit [CharZero L] [IsReduced X] [IsReduced XL] [LocallyOfFiniteType fL]
  [IsSeparated f] [IsSeparated fL] in
theorem paddedFieldMap_piece
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (d : dimensionIndex XL) :
    Sigma.ι (piece XL (transportedVariables h)) d ≫ paddedFieldMap h =
      paddedPieceMap h d ≫ Sigma.ι (piece X (paddingVariables f)) (dimensionIndexEquiv h d) := by
  rw [paddedFieldMap, ← Category.assoc, Sigma.ι_map, Category.assoc]
  simp only [targetReindexIso, Sigma.whiskerEquiv_hom, Sigma.ι_comp_map',
    Iso.refl_inv, Category.id_comp]

omit [CharZero k] [CharZero L] [IsReduced X] [AlgebraicGeometry.IsNoetherian XL] [IsReduced XL]
  [LocallyOfFiniteType fL] [IsSeparated f] [IsSeparated fL] in
private theorem targetReindexIso_projection
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    (targetReindexIso h).hom ≫ projection X (paddingVariables f) =
      Sigma.desc (fun d => pieceProjection X (paddingVariables f) (dimensionIndexEquiv h d) ≫
        (dimensionPartOpen X (dimensionIndexEquiv h d)).ι) := by
  apply Sigma.hom_ext
  intro d
  simp only [← Category.assoc, targetReindexIso, Sigma.whiskerEquiv_hom,
    Sigma.ι_comp_map', Iso.refl_inv, Category.id_comp, projection, Sigma.ι_desc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Universe transport only: the native public coproduct theorem uses an
index in the scheme universe, whereas the actual dimension labels are small.
Lift those labels and transport its square through coproduct isomorphisms. -/
private theorem isPullback_sigmaMap_smallIndex {ι : Type} {W B : ι → Scheme.{u}}
    (j : ∀ i, W i ⟶ B i) {Y Z : Scheme.{u}} (e : ∀ i, W i ⟶ Y)
    (g : ∀ i, B i ⟶ Z) (q : Y ⟶ Z)
    (hs : ∀ i, IsPullback (j i) (e i) (g i) q) :
    IsPullback (Limits.Sigma.map j) (Sigma.desc e) (Sigma.desc g) q := by
  let eW : (∐ fun i : ULift.{u} ι => W i.down) ≅ ∐ W :=
    Sigma.whiskerEquiv (Equiv.ulift : ULift.{u} ι ≃ ι) (fun _ => Iso.refl _)
  let eB : (∐ fun i : ULift.{u} ι => B i.down) ≅ ∐ B :=
    Sigma.whiskerEquiv (Equiv.ulift : ULift.{u} ι ≃ ι) (fun _ => Iso.refl _)
  have hLift := Hironaka.Resolution.isPullback_sigmaMap_sigmaDesc
    (fun i : ULift.{u} ι => j i.down) (fun i => e i.down)
    (fun i => g i.down) q (fun i => hs i.down)
  refine hLift.of_iso eW eB (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · apply Sigma.hom_ext
    intro i
    dsimp only [eW, eB, Sigma.whiskerEquiv]
    simp only [Iso.refl_inv, Sigma.ι_map_assoc, Sigma.ι_comp_map'_assoc,
      Sigma.ι_map, Sigma.ι_comp_map']
    change j i.down ≫ 𝟙 (B i.down) ≫ Sigma.ι B i.down =
      𝟙 (W i.down) ≫ j i.down ≫ Sigma.ι B i.down
    simp
  · apply Sigma.hom_ext
    intro i
    dsimp only [eW, Sigma.whiskerEquiv]
    simp only [Iso.refl_inv, Iso.refl_hom, Sigma.ι_comp_map'_assoc,
      Sigma.ι_desc, Category.comp_id]
    change e i.down = 𝟙 (W i.down) ≫ e i.down
    simp
  · apply Sigma.hom_ext
    intro i
    dsimp only [eB, Sigma.whiskerEquiv]
    simp only [Iso.refl_inv, Iso.refl_hom, Sigma.ι_comp_map'_assoc,
      Sigma.ι_desc, Category.comp_id]
    change g i.down = 𝟙 (B i.down) ≫ g i.down
    simp
  · simp

omit [CharZero L] [IsReduced X] [IsReduced XL] [LocallyOfFiniteType fL]
  [IsSeparated f] [IsSeparated fL] in
theorem paddedFieldMap_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    IsPullback (paddedFieldMap h) (projection XL (transportedVariables h))
      (projection X (paddingVariables f)) (separationMap_baseChange h) := by
  have hs := isPullback_sigmaMap_smallIndex (paddedPieceMap h)
    (fun d => pieceProjection XL (transportedVariables h) d ≫ (dimensionPartOpen XL d).ι)
    (fun d => pieceProjection X (paddingVariables f) (dimensionIndexEquiv h d) ≫
      (dimensionPartOpen X (dimensionIndexEquiv h d)).ι)
    (separationMap_baseChange h) (paddedPieceMap_isPullback h)
  refine hs.of_iso (Iso.refl _) (targetReindexIso h) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [paddedFieldMap, Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simpa only [Iso.refl_hom, Category.comp_id] using (targetReindexIso_projection h).symm
  · simp

omit [CharZero L] [IsReduced X] [IsReduced XL] [LocallyOfFiniteType fL]
  [IsSeparated f] [IsSeparated fL] in
theorem paddedFieldMap_fieldSquare
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    IsPullback (paddedFieldMap h) (envelopeStructure fL (transportedVariables h))
      (envelopeStructure f (paddingVariables f))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  (paddedFieldMap_isPullback h).paste_vert ((separationMap_baseChange_isPullback h).paste_vert h)

private theorem zeroSection_piece {Z : Scheme.{u}} [NoetherianSpace Z] [IsReduced Z]
    (V : dimensionIndex Z → Type u) (d : dimensionIndex Z) :
    (dimensionPartOpen Z d).ι ≫ zeroSection Z V =
      pieceZeroSection Z V d ≫ Sigma.ι (piece Z V) d := by
  have hd : Sigma.ι (pieceFamily Z) d ≫ piecesDesc Z = (dimensionPartOpen Z d).ι := by
    rw [piecesDesc, Sigma.ι_desc]
  rw [← hd, Category.assoc, zeroSection, IsIso.hom_inv_id_assoc, Sigma.ι_map]

omit [CharZero L] [LocallyOfFiniteType fL] [IsSeparated f] [IsSeparated fL] in
theorem paddedFieldMap_zero
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    zeroSection XL (transportedVariables h) ≫ paddedFieldMap h =
      separationMap_baseChange h ≫ zeroSection X (paddingVariables f) := by
  apply (cancel_epi (piecesDesc XL)).mp
  apply Sigma.hom_ext
  intro d
  simp only [piecesDesc, ← Category.assoc, Sigma.ι_desc]
  rw [zeroSection_piece, Category.assoc, paddedFieldMap_piece, ← Category.assoc]
  have hz : pieceZeroSection XL (transportedVariables h) d ≫ paddedPieceMap h d =
      dimensionPartMap h d ≫ pieceZeroSection X (paddingVariables f) (dimensionIndexEquiv h d) := by
    simpa only [pieceZeroSection, paddedPieceMap, ActualAffineCoordinateForgetting.coordinateMap,
      AffineSpace.reindex_id, Category.id_comp] using
      ActualAffineCoordinateForgetting.coordinateMap_zero (id : transportedVariables h d → transportedVariables h d)
        (dimensionPartMap h d)
  rw [hz, Category.assoc, ← zeroSection_piece, ← Category.assoc,
    (dimensionPartMap_isPullback h d).w, Category.assoc]

theorem transportedHistory_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    history fL (transportedVariables h) (commonDimension f) (transported_rank h) =
      (canonicalHistory f).pullback (paddedFieldMap h) := by
  let : (envelope XL (transportedVariables h)).Over (Spec (.of L)) :=
    ⟨envelopeStructure fL (transportedVariables h)⟩
  let : (envelope X (paddingVariables f)).Over (Spec (.of k)) :=
    ⟨envelopeStructure f (paddingVariables f)⟩
  let : LocallyOfFiniteType (envelope XL (transportedVariables h) ↘ Spec (.of L)) := by
    change LocallyOfFiniteType (envelopeStructure fL (transportedVariables h))
    infer_instance
  let : LocallyOfFiniteType (envelope X (paddingVariables f) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (envelopeStructure f (paddingVariables f))
    infer_instance
  have hTarget : (envelope XL (transportedVariables h)).IsReducedEquidimensional L :=
    isReducedEquidimensional_baseChange (paddedFieldMap_fieldSquare h) (paddedEnvelope f).property
  let XLInput : ReducedEquidimensionalScheme L :=
    ⟨envelopeAlgScheme fL (transportedVariables h), hTarget⟩
  exact ActualPaddedEnvelopeNativeTranslations.nativeResolutionFamily_commutesWithChangeOfFields
    k L (algebraMap k L) (paddedEnvelope f) XLInput (paddedFieldMap h) (paddedFieldMap_fieldSquare h)

/-- The SAME canonical base clock follows from actual field geometry and actual padding-choice independence. -/
theorem canonicalBaseHistory_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    canonicalBaseHistory fL = (canonicalBaseHistory f).pullback (separationMap_baseChange h) := by
  calc
    canonicalBaseHistory fL =
        baseHistory fL (transportedVariables h) (commonDimension f) (transported_rank h) :=
      (ActualGlobalPaddingResolutionChoice.baseHistory_eq_canonical fL
        (transportedVariables h) (commonDimension f) (transported_rank h)).symm
    _ = (history fL (transportedVariables h) (commonDimension f) (transported_rank h)).pullback
        (zeroSection XL (transportedVariables h)) := rfl
    _ = ((canonicalHistory f).pullback (paddedFieldMap h)).pullback
        (zeroSection XL (transportedVariables h)) := by rw [transportedHistory_baseChange h]
    _ = (canonicalHistory f).pullback
        (zeroSection XL (transportedVariables h) ≫ paddedFieldMap h) :=
      (pullback_comp _ _ _).symm
    _ = (canonicalHistory f).pullback
        (separationMap_baseChange h ≫ zeroSection X (paddingVariables f)) := by rw [paddedFieldMap_zero h]
    _ = ((canonicalHistory f).pullback (zeroSection X (paddingVariables f))).pullback
        (separationMap_baseChange h) := pullback_comp _ _ _
    _ = (canonicalBaseHistory f).pullback (separationMap_baseChange h) := rfl

def nativeEndpointMap
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    (history fL (transportedVariables h) (commonDimension f) (transported_rank h)).last ⟶
      (canonicalHistory f).last :=
  eqToHom (congrArg Scheme.BlowUpSequence.last (transportedHistory_baseChange h)) ≫
    (canonicalHistory f).pullbackLastHom (paddedFieldMap h)

theorem nativeEndpoint_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    IsPullback (nativeEndpointMap h)
      (history fL (transportedVariables h) (commonDimension f) (transported_rank h)).composite
      (canonicalHistory f).composite (paddedFieldMap h) := by
  let : Flat (paddedFieldMap h) :=
    Hironaka.HironakaG1RComponentBaseChange.flat_of_isPullback
      (paddedFieldMap_fieldSquare h)
  exact ActualHistoryOriginalRegularIsomorphism.lastStage_isPullback_of_eq
    (canonicalHistory f) (paddedFieldMap h)
    (history fL (transportedVariables h) (commonDimension f) (transported_rank h))
    (transportedHistory_baseChange h)

theorem nativeEndpoint_original
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    nativeEndpointMap h ≫ ((canonicalHistory f).composite ≫
        projection X (paddingVariables f) ≫ separationProjection X) =
      ((history fL (transportedVariables h) (commonDimension f) (transported_rank h)).composite ≫
        projection XL (transportedVariables h) ≫ separationProjection XL) ≫ p := by
  rw [← Category.assoc, (nativeEndpoint_isPullback h).w, Category.assoc,
    ← Category.assoc (paddedFieldMap h), (paddedFieldMap_isPullback h).w,
    Category.assoc, separationMap_baseChange_over]
  simp only [Category.assoc]

theorem originalIdeal_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    originalIdeal fL (transportedVariables h) (commonDimension f) (transported_rank h) =
      (originalIdeal f (paddingVariables f) (commonDimension f) (padding_rank f)).comap
        (nativeEndpointMap h) := by
  rw [originalIdeal, originalIdeal, ← singIdeal_baseChange_charZero h,
    ← comap_comp, ← comap_comp]
  apply congrArg X.singIdeal.comap
  exact (nativeEndpoint_original h).symm

theorem principalizationHistory_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    principalizationHistory fL (transportedVariables h) (commonDimension f) (transported_rank h) =
      (principalizationHistory f (paddingVariables f) (commonDimension f) (padding_rank f)).pullback
        (nativeEndpointMap h) := by
  let T := originalTriple f (paddingVariables f) (commonDimension f) (padding_rank f)
  let TL := originalTriple fL (transportedVariables h) (commonDimension f) (transported_rank h)
  have hSquare : IsPullback (nativeEndpointMap h)
      (TL.X.left ↘ Spec (.of L)) (T.X.left ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    (nativeEndpoint_isPullback h).paste_vert (paddedFieldMap_fieldSquare h)
  have hI : TL.I = T.I.comap (nativeEndpointMap h) := originalIdeal_baseChange h
  have hE : TL.E = T.E.comap (nativeEndpointMap h) := (empty_comap (nativeEndpointMap h)).symm
  exact BP_baseChange (algebraMap k L) T TL (nativeEndpointMap h) ⟨hSquare, hI, hE⟩

theorem paddedCompleteHistory_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    (history fL (transportedVariables h) (commonDimension f) (transported_rank h)).concat
        (principalizationHistory fL (transportedVariables h) (commonDimension f) (transported_rank h)) =
      ((canonicalHistory f).concat
        (principalizationHistory f (paddingVariables f) (commonDimension f) (padding_rank f))).pullback
          (paddedFieldMap h) :=
  ActualGlobalStrongResolutionSmoothSurjective.concat_eq_pullback_of_eq (paddedFieldMap h)
    (canonicalHistory f)
    (history fL (transportedVariables h) (commonDimension f) (transported_rank h))
    (principalizationHistory f (paddingVariables f) (commonDimension f) (padding_rank f))
    (principalizationHistory fL (transportedVariables h) (commonDimension f) (transported_rank h))
    (transportedHistory_baseChange h) (principalizationHistory_baseChange h)

theorem canonicalBaseCompleteHistory_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    canonicalBaseCompleteHistory fL =
      (canonicalBaseCompleteHistory f).pullback (separationMap_baseChange h) := by
  let q := projection XL (transportedVariables h)
  let : Smooth q := projection_smooth XL (transportedVariables h)
  have hq : Function.Surjective q := (projection_surjective XL (transportedVariables h)).1
  apply pullback_injective_of_surjective q hq
  calc
    (canonicalBaseCompleteHistory fL).pullback q =
        (history fL (transportedVariables h) (commonDimension f) (transported_rank h)).concat
          (principalizationHistory fL (transportedVariables h) (commonDimension f) (transported_rank h)) :=
      (paddedCompleteHistory_descends fL (transportedVariables h) (commonDimension f)
        (transported_rank h)).symm
    _ = ((canonicalHistory f).concat
        (principalizationHistory f (paddingVariables f) (commonDimension f) (padding_rank f))).pullback
          (paddedFieldMap h) := paddedCompleteHistory_baseChange h
    _ = (((canonicalBaseCompleteHistory f).pullback (projection X (paddingVariables f))).pullback
        (paddedFieldMap h)) := by
      rw [paddedCompleteHistory_descends f (paddingVariables f) (commonDimension f) (padding_rank f)]
    _ = ((canonicalBaseCompleteHistory f).pullback (separationMap_baseChange h)).pullback q := by
      rw [← pullback_comp, ← pullback_comp, (paddedFieldMap_isPullback h).w]

theorem canonicalOriginalHistory_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    ActualGlobalMixedDimensionResolution.canonicalOriginalHistory fL =
      (ActualGlobalMixedDimensionResolution.canonicalOriginalHistory f).pullback p :=
  ActualGlobalWeakResolutionSmoothSurjective.cons_eq_pullback_of_ideal_eq p
    (ActualGlobalDimensionSeparationIdeal.separationIdeal X)
    (ActualGlobalDimensionSeparationIdeal.separationIdeal XL)
    (canonicalBaseCompleteHistory f) (canonicalBaseCompleteHistory fL)
    (separationIdeal_baseChange h) (canonicalBaseCompleteHistory_baseChange h)

theorem resolutionHistory_baseChange
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    resolutionHistory fL = (resolutionHistory f).pullback p := by
  let : Flat p := Hironaka.HironakaG1RComponentBaseChange.flat_of_isPullback h
  change (ActualGlobalMixedDimensionResolution.canonicalOriginalHistory fL).eraseEmpty =
    (ActualGlobalMixedDimensionResolution.canonicalOriginalHistory f).eraseEmpty.pullback p
  rw [canonicalOriginalHistory_baseChange h, eraseEmpty_pullback_of_flat_surjective _ p
    (Hironaka.HironakaG1RComponentBaseChange.surjective_of_isPullback h).1]

end ActualPaddedInput

section OrdinarySource
variable [CharZero k] [IsNoetherian X] [IsReduced X]
  [LocallyOfFiniteType f] [IsSeparated f]

omit [CharZero k] [IsReduced X] [IsSeparated f] in
private theorem targetIsNoetherian
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    IsNoetherian XL := by
  let : LocallyOfFiniteType fL :=
    MorphismProperty.of_isPullback h (inferInstance : LocallyOfFiniteType f)
  let : IsLocallyNoetherian XL := LocallyOfFiniteType.isLocallyNoetherian fL
  let : NoetherianSpace XL :=
    Hironaka.HironakaG1RNoetherianBaseChange.noetherianSpace_of_isPullback h
  exact ⟨⟩

/-- No property of the extended original scheme or its histories is an input.
All target classes are derived from the source and its actual field square. -/
theorem canonicalBaseHistory_baseChange_of_source
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    letI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
    letI : LocallyOfFiniteType fL :=
      MorphismProperty.of_isPullback h (inferInstance : LocallyOfFiniteType f)
    letI : IsSeparated fL :=
      MorphismProperty.of_isPullback h (inferInstance : IsSeparated f)
    letI : IsNoetherian XL := targetIsNoetherian h
    letI : IsReduced XL :=
      Hironaka.HironakaG1RReducedEquidimensionalBaseChange.isReduced_of_isPullback h
    canonicalBaseHistory fL = (canonicalBaseHistory f).pullback (separationMap_baseChange h) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  let : LocallyOfFiniteType fL :=
    MorphismProperty.of_isPullback h (inferInstance : LocallyOfFiniteType f)
  let : IsSeparated fL :=
    MorphismProperty.of_isPullback h (inferInstance : IsSeparated f)
  let : IsNoetherian XL := targetIsNoetherian h
  let : IsReduced XL :=
    Hironaka.HironakaG1RReducedEquidimensionalBaseChange.isReduced_of_isPullback h
  exact canonicalBaseHistory_baseChange h

/-- Field-extension compatibility of the actual final assignment, from only
the original noetherian reduced finite-type separated scheme and its field square. -/
theorem resolutionHistory_baseChange_of_source
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    letI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
    letI : LocallyOfFiniteType fL :=
      MorphismProperty.of_isPullback h (inferInstance : LocallyOfFiniteType f)
    letI : IsSeparated fL :=
      MorphismProperty.of_isPullback h (inferInstance : IsSeparated f)
    letI : IsNoetherian XL := targetIsNoetherian h
    letI : IsReduced XL :=
      Hironaka.HironakaG1RReducedEquidimensionalBaseChange.isReduced_of_isPullback h
    resolutionHistory fL = (resolutionHistory f).pullback p := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  let : LocallyOfFiniteType fL :=
    MorphismProperty.of_isPullback h (inferInstance : LocallyOfFiniteType f)
  let : IsSeparated fL :=
    MorphismProperty.of_isPullback h (inferInstance : IsSeparated f)
  let : IsNoetherian XL := targetIsNoetherian h
  let : IsReduced XL :=
    Hironaka.HironakaG1RReducedEquidimensionalBaseChange.isReduced_of_isPullback h
  exact resolutionHistory_baseChange h

end OrdinarySource

end
end Hironaka.Resolution.Algebraic.HironakaG1PaddedFieldComparison
