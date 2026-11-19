import Hironaka.Resolution.Algebraic.ActualVariablePaddingEnvelope

/-!
# Genuine pure common native envelope and exact resolution-history choice comparison

Source-first proof: `actual-common-native-resolution-comparison-20261102.tex`.
The essential extra affine dimension is constructed, then genuine smooth
surjective native functoriality compares ONE common whole history.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualCommonNativeResolutionComparison

noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupEquidimensionalPieces ActualDimensionGroupPaddedCover
  ActualCommonPaddedEnvelopeGeometry ActualAffineSpaceSumDecomposition ActualPaddedEnvelopeNativeTranslations

variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]
  (V₁ V₂ : dimensionIndex R → Type u) [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)]

/-- The original component dimension supplies the essential EXTRA actual affine variables. -/
def commonVariables (d : dimensionIndex R) : Type u :=
  ULift.{u} (Fin (dimensionNat R k d)) ⊕ (V₁ d ⊕ V₂ d)

private instance commonVariables_finite (d : dimensionIndex R) : Finite (commonVariables R k V₁ V₂ d) := by
  dsimp only [commonVariables]
  infer_instance

omit [CharZero k] [IsReduced R] in
/-- Actual original dimension plus actual common variable rank is EXACTLY N₁+N₂ on every original piece. -/
theorem common_rank (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    ∀ d, dimensionNat R k d + Nat.card (commonVariables R k V₁ V₂ d) = N₁ + N₂ := by
  intro d
  simp only [commonVariables,Nat.card_sum,Nat.card_ulift,Nat.card_fin]
  have h1 := h₁ d
  have h2 := h₂ d
  omega

/-- ONE genuine pure common native input, internally derived from actual original component dimensions. -/
def commonInput (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) : ReducedEquidimensionalScheme k :=
  ActualVariablePaddingEnvelope.variableEnvelope R (commonVariables R k V₁ V₂) k (N₁+N₂)
    (common_rank R k V₁ V₂ N₁ N₂ h₁ h₂)

private abbrev pieceIso (d : dimensionIndex R) :
    ActualVariablePaddingEnvelope.piece R (commonVariables R k V₁ V₂) d ≅
      commonSpace (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme :=
  commonSumIso (V₁ d) (V₂ d) (dimensionPartOpen R d).toScheme (ULift.{u} (Fin (dimensionNat R k d)))

private def pieceToFirst (d : dimensionIndex R) :
    ActualVariablePaddingEnvelope.piece R (commonVariables R k V₁ V₂) d ⟶
      ActualVariablePaddingEnvelope.piece R V₁ d :=
  (pieceIso R k V₁ V₂ d).hom ≫
    commonToFirst (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme

private def pieceToSecond (d : dimensionIndex R) :
    ActualVariablePaddingEnvelope.piece R (commonVariables R k V₁ V₂) d ⟶
      ActualVariablePaddingEnvelope.piece R V₂ d :=
  (pieceIso R k V₁ V₂ d).hom ≫
    commonToSecond (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme

/-- Actual common projection to the SAME first original padded input. -/
def toFirst : ActualVariablePaddingEnvelope.envelope R (commonVariables R k V₁ V₂) ⟶
    ActualVariablePaddingEnvelope.envelope R V₁ := Limits.Sigma.map (pieceToFirst R k V₁ V₂)

/-- Actual common projection to the SAME second original padded input. -/
def toSecond : ActualVariablePaddingEnvelope.envelope R (commonVariables R k V₁ V₂) ⟶
    ActualVariablePaddingEnvelope.envelope R V₂ := Limits.Sigma.map (pieceToSecond R k V₁ V₂)

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global first projection identity over the SAME original separation blowup. -/
theorem toFirst_projection : toFirst R k V₁ V₂ ≫ ActualVariablePaddingEnvelope.projection R V₁ =
    ActualVariablePaddingEnvelope.projection R (commonVariables R k V₁ V₂) := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc,toFirst,Sigma.ι_map,Category.assoc,ActualVariablePaddingEnvelope.projection,
    Sigma.ι_desc,← Category.assoc]
  have he := commonSumIso_over (V₁ d) (V₂ d) (dimensionPartOpen R d).toScheme
    (ULift.{u} (Fin (dimensionNat R k d)))
  have hp : pieceToFirst R k V₁ V₂ d ≫ (AffineSpace (V₁ d) (dimensionPartOpen R d).toScheme ↘
      (dimensionPartOpen R d).toScheme) =
        (AffineSpace (commonVariables R k V₁ V₂ d) (dimensionPartOpen R d).toScheme ↘
          (dimensionPartOpen R d).toScheme) := by
    rw [pieceToFirst,Category.assoc]
    exact he
  rw [ActualVariablePaddingEnvelope.projection,Sigma.ι_desc]
  exact congrArg (fun f => f ≫ (dimensionPartOpen R d).ι) hp

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global second projection identity over the SAME original separation blowup. -/
theorem toSecond_projection : toSecond R k V₁ V₂ ≫ ActualVariablePaddingEnvelope.projection R V₂ =
    ActualVariablePaddingEnvelope.projection R (commonVariables R k V₁ V₂) := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc,toSecond,Sigma.ι_map,Category.assoc,ActualVariablePaddingEnvelope.projection,
    Sigma.ι_desc,← Category.assoc]
  have he := commonSumIso_over (V₁ d) (V₂ d) (dimensionPartOpen R d).toScheme
    (ULift.{u} (Fin (dimensionNat R k d)))
  have hs := common_projection_square (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d)))
    (dimensionPartOpen R d).toScheme
  have hp : pieceToSecond R k V₁ V₂ d ≫ (AffineSpace (V₂ d) (dimensionPartOpen R d).toScheme ↘
      (dimensionPartOpen R d).toScheme) =
        (AffineSpace (commonVariables R k V₁ V₂ d) (dimensionPartOpen R d).toScheme ↘
          (dimensionPartOpen R d).toScheme) := by
    rw [pieceToSecond,Category.assoc,← hs]
    exact he
  rw [ActualVariablePaddingEnvelope.projection,Sigma.ι_desc]
  exact congrArg (fun f => f ≫ (dimensionPartOpen R d).ι) hp

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] in
private theorem pieceToFirst_relativeDimension (N₂ : ℕ)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) (d : dimensionIndex R) :
    SmoothOfRelativeDimension N₂ (pieceToFirst R k V₁ V₂ d) := by
  have hdim := commonToFirst_relativeDimension (V₁ d) (V₂ d)
    (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme
  have : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin (dimensionNat R k d))) + Nat.card (V₂ d))
      (commonToFirst (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme) := hdim
  have hc : SmoothOfRelativeDimension (0 + (Nat.card (ULift.{u} (Fin (dimensionNat R k d))) + Nat.card (V₂ d)))
      (pieceToFirst R k V₁ V₂ d) := by
    dsimp only [pieceToFirst]
    infer_instance
  simpa only [Nat.zero_add,Nat.card_ulift,Nat.card_fin,h₂ d] using hc

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₂ d)] in
private theorem pieceToSecond_relativeDimension (N₁ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁) (d : dimensionIndex R) :
    SmoothOfRelativeDimension N₁ (pieceToSecond R k V₁ V₂ d) := by
  have hdim := commonToSecond_relativeDimension (V₁ d) (V₂ d)
    (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme
  have : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin (dimensionNat R k d))) + Nat.card (V₁ d))
      (commonToSecond (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme) := hdim
  have hc : SmoothOfRelativeDimension (0 + (Nat.card (ULift.{u} (Fin (dimensionNat R k d))) + Nat.card (V₁ d)))
      (pieceToSecond R k V₁ V₂ d) := by
    dsimp only [pieceToSecond]
    infer_instance
  simpa only [Nat.zero_add,Nat.card_ulift,Nat.card_fin,h₁ d] using hc

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] in
/-- The actual GLOBAL first projection has ONE constant relative dimension N₂. -/
theorem toFirst_relativeDimension (N₂ : ℕ)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    SmoothOfRelativeDimension N₂ (toFirst R k V₁ V₂) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension N₂) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  change SmoothOfRelativeDimension N₂ (Sigma.desc (fun d => pieceToFirst R k V₁ V₂ d ≫
    Sigma.ι (ActualVariablePaddingEnvelope.piece R V₁) d))
  apply IsZariskiLocalAtSource.sigmaDesc
  intro d
  have := pieceToFirst_relativeDimension R k V₁ V₂ N₂ h₂ d
  have hc : SmoothOfRelativeDimension (N₂ + 0) (pieceToFirst R k V₁ V₂ d ≫
      Sigma.ι (ActualVariablePaddingEnvelope.piece R V₁) d) := inferInstance
  simpa only [Nat.add_zero] using hc

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₂ d)] in
/-- The actual GLOBAL second projection has ONE constant relative dimension N₁. -/
theorem toSecond_relativeDimension (N₁ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁) :
    SmoothOfRelativeDimension N₁ (toSecond R k V₁ V₂) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension N₁) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  change SmoothOfRelativeDimension N₁ (Sigma.desc (fun d => pieceToSecond R k V₁ V₂ d ≫
    Sigma.ι (ActualVariablePaddingEnvelope.piece R V₂) d))
  apply IsZariskiLocalAtSource.sigmaDesc
  intro d
  have := pieceToSecond_relativeDimension R k V₁ V₂ N₁ h₁ d
  have hc : SmoothOfRelativeDimension (N₁ + 0) (pieceToSecond R k V₁ V₂ d ≫
      Sigma.ι (ActualVariablePaddingEnvelope.piece R V₂) d) := inferInstance
  simpa only [Nat.add_zero] using hc

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private instance pieceToFirst_surjective (d : dimensionIndex R) : Surjective (pieceToFirst R k V₁ V₂ d) := by
  have := commonToFirst_surjective (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d)))
    (dimensionPartOpen R d).toScheme
  dsimp only [pieceToFirst]
  infer_instance

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private instance pieceToSecond_surjective (d : dimensionIndex R) : Surjective (pieceToSecond R k V₁ V₂ d) := by
  have := commonToSecond_surjective (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d)))
    (dimensionPartOpen R d).toScheme
  dsimp only [pieceToSecond]
  infer_instance

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global first surjectivity, including empty original label sets. -/
theorem toFirst_surjective : Surjective (toFirst R k V₁ V₂) := by
  constructor
  intro x
  obtain ⟨d,y,rfl⟩ := (sigmaOpenCover (ActualVariablePaddingEnvelope.piece R V₁)).exists_eq x
  obtain ⟨w,hw⟩ := (pieceToFirst_surjective R k V₁ V₂ d).1 y
  refine ⟨Sigma.ι (ActualVariablePaddingEnvelope.piece R (commonVariables R k V₁ V₂)) d w,?_⟩
  rw [← Scheme.Hom.comp_apply,toFirst,Sigma.ι_map,Scheme.Hom.comp_apply,hw]
  rfl

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global second surjectivity, with the SAME original coproduct labels. -/
theorem toSecond_surjective : Surjective (toSecond R k V₁ V₂) := by
  constructor
  intro x
  obtain ⟨d,y,rfl⟩ := (sigmaOpenCover (ActualVariablePaddingEnvelope.piece R V₂)).exists_eq x
  obtain ⟨w,hw⟩ := (pieceToSecond_surjective R k V₁ V₂ d).1 y
  refine ⟨Sigma.ι (ActualVariablePaddingEnvelope.piece R (commonVariables R k V₁ V₂)) d w,?_⟩
  rw [← Scheme.Hom.comp_apply,toSecond,Sigma.ι_map,Scheme.Hom.comp_apply,hw]
  rfl

private def pieceSection (d : dimensionIndex R) : (dimensionPartOpen R d).toScheme ⟶
    ActualVariablePaddingEnvelope.piece R (commonVariables R k V₁ V₂) d :=
  commonZeroSection (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat R k d))) (dimensionPartOpen R d).toScheme ≫
    (pieceIso R k V₁ V₂ d).inv

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private theorem pieceSection_first (d : dimensionIndex R) :
    pieceSection R k V₁ V₂ d ≫ pieceToFirst R k V₁ V₂ d =
      AffineSpace.homOfVector (𝟙 (dimensionPartOpen R d).toScheme) (fun _ : V₁ d => 0) := by
  rw [pieceSection,pieceToFirst,Category.assoc,Iso.inv_hom_id_assoc,commonZeroSection_first]

omit [CharZero k] [IsReduced R] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private theorem pieceSection_second (d : dimensionIndex R) :
    pieceSection R k V₁ V₂ d ≫ pieceToSecond R k V₁ V₂ d =
      AffineSpace.homOfVector (𝟙 (dimensionPartOpen R d).toScheme) (fun _ : V₂ d => 0) := by
  rw [pieceSection,pieceToSecond,Category.assoc,Iso.inv_hom_id_assoc,commonZeroSection_second]

/-- ONE genuine common section over the SAME original base. -/
def commonSection : affineBlowUp (dimensionSeparationIdeal R) ⟶
    ActualVariablePaddingEnvelope.envelope R (commonVariables R k V₁ V₂) :=
  inv (piecesDesc R) ≫ Limits.Sigma.map (pieceSection R k V₁ V₂)

omit [CharZero k] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- The actual common section projects to the SAME original first zero section. -/
theorem commonSection_first : commonSection R k V₁ V₂ ≫ toFirst R k V₁ V₂ =
    ActualVariablePaddingEnvelope.zeroSection R V₁ := by
  change (inv (piecesDesc R) ≫ Limits.Sigma.map (pieceSection R k V₁ V₂)) ≫
    Limits.Sigma.map (pieceToFirst R k V₁ V₂) = _
  rw [Category.assoc,Sigma.map_comp_map]
  exact congrArg (fun f => inv (piecesDesc R) ≫ f)
    (congrArg Limits.Sigma.map (funext (pieceSection_first R k V₁ V₂)))

omit [CharZero k] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- The SAME actual common section projects to the SAME original second zero section. -/
theorem commonSection_second : commonSection R k V₁ V₂ ≫ toSecond R k V₁ V₂ =
    ActualVariablePaddingEnvelope.zeroSection R V₂ := by
  change (inv (piecesDesc R) ≫ Limits.Sigma.map (pieceSection R k V₁ V₂)) ≫
    Limits.Sigma.map (pieceToSecond R k V₁ V₂) = _
  rw [Category.assoc,Sigma.map_comp_map]
  exact congrArg (fun f => inv (piecesDesc R) ≫ f)
    (congrArg Limits.Sigma.map (funext (pieceSection_second R k V₁ V₂)))

/-- The SAME globally chosen native family on a genuine actual arbitrary-padding input. -/
def history (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) :
    (ActualVariablePaddingEnvelope.envelope R V).BlowUpSequence :=
  nativeResolutionFamily k (ActualVariablePaddingEnvelope.variableEnvelope R V k N hN)

private def firstInputMap (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    commonInput R k V₁ V₂ N₁ N₂ h₁ h₂ ⟶ ActualVariablePaddingEnvelope.variableEnvelope R V₁ k N₁ h₁ :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (toFirst R k V₁ V₂) (by
    change toFirst R k V₁ V₂ ≫ (ActualVariablePaddingEnvelope.projection R V₁ ≫
      affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) = _
    rw [← Category.assoc,toFirst_projection]
    rfl))

private def secondInputMap (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    commonInput R k V₁ V₂ N₁ N₂ h₁ h₂ ⟶ ActualVariablePaddingEnvelope.variableEnvelope R V₂ k N₂ h₂ :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (toSecond R k V₁ V₂) (by
    change toSecond R k V₁ V₂ ≫ (ActualVariablePaddingEnvelope.projection R V₂ ≫
      affineBlowUp.π (dimensionSeparationIdeal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) = _
    rw [← Category.assoc,toSecond_projection]
    rfl))

/-- ONE common native whole history is literally the actual pullback of the first SAME history. -/
theorem commonHistory_first (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    history R k (commonVariables R k V₁ V₂) (N₁+N₂) (common_rank R k V₁ V₂ N₁ N₂ h₁ h₂) =
      (history R k V₁ N₁ h₁).pullback (toFirst R k V₁ V₂) := by
  have := toFirst_relativeDimension R k V₁ V₂ N₂ h₂
  have hs : Smooth (HasUnderlyingScheme.hom (firstInputMap R k V₁ V₂ N₁ N₂ h₁ h₂)) := by
    change Smooth (toFirst R k V₁ V₂)
    exact SmoothOfRelativeDimension.smooth N₂ _
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (firstInputMap R k V₁ V₂ N₁ N₂ h₁ h₂) hs (toFirst_surjective R k V₁ V₂).1

/-- The SAME common native whole history is literally the actual pullback of the second SAME history. -/
theorem commonHistory_second (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    history R k (commonVariables R k V₁ V₂) (N₁+N₂) (common_rank R k V₁ V₂ N₁ N₂ h₁ h₂) =
      (history R k V₂ N₂ h₂).pullback (toSecond R k V₁ V₂) := by
  have := toSecond_relativeDimension R k V₁ V₂ N₁ h₁
  have hs : Smooth (HasUnderlyingScheme.hom (secondInputMap R k V₁ V₂ N₁ N₂ h₁ h₂)) := by
    change Smooth (toSecond R k V₁ V₂)
    exact SmoothOfRelativeDimension.smooth N₁ _
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (secondInputMap R k V₁ V₂ N₁ N₂ h₁ h₂) hs (toSecond_surjective R k V₁ V₂).1

/-- Actual whole native history on the SAME original base, through its actual original zero section. -/
def baseHistory (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) :
    (affineBlowUp (dimensionSeparationIdeal R)).BlowUpSequence :=
  (history R k V N hN).pullback (ActualVariablePaddingEnvelope.zeroSection R V)

/-- Genuine actual padding-choice independence, preserving the SAME WHOLE native clock and all internal empties. -/
theorem baseHistories_eq (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat R k d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat R k d + Nat.card (V₂ d) = N₂) :
    baseHistory R k V₁ N₁ h₁ = baseHistory R k V₂ N₂ h₂ := by
  have hfirst := congrArg (fun S => S.pullback (commonSection R k V₁ V₂))
    (commonHistory_first R k V₁ V₂ N₁ N₂ h₁ h₂)
  have hsecond := congrArg (fun S => S.pullback (commonSection R k V₁ V₂))
    (commonHistory_second R k V₁ V₂ N₁ N₂ h₁ h₂)
  rw [← pullback_comp,commonSection_first] at hfirst
  rw [← pullback_comp,commonSection_second] at hsecond
  exact hfirst.symm.trans hsecond

omit [CharZero k] [IsReduced R] in
/-- The original canonical actual padding satisfies its SAME numerical rank equations. -/
theorem canonicalRank : ∀ d, dimensionNat R k d + Nat.card (paddingVariables R k d) = commonDimension R k := by
  intro d
  simpa only [paddingVariables,Nat.card_ulift,Nat.card_fin,Nat.add_comm] using paddingDimension_add R k d

/-- Canonical specialization is the SAME actual native base history already geometrically descended. -/
theorem canonicalBaseHistory :
    baseHistory R k (paddingVariables R k) (commonDimension R k) (canonicalRank R k) =
      ActualRelativeAffineHistoryDescent.nativeBaseHistory R k := by
  rfl

/-- EVERY valid actual padding choice gives EXACTLY the original genuine descended native resolution history. -/
theorem baseHistory_eq_original (V : dimensionIndex R → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) :
    baseHistory R k V N hN = ActualRelativeAffineHistoryDescent.nativeBaseHistory R k :=
  (baseHistories_eq R k V (paddingVariables R k) N (commonDimension R k) hN (canonicalRank R k)).trans
    (canonicalBaseHistory R k)

end
end Hironaka.Resolution.Algebraic.ActualCommonNativeResolutionComparison
