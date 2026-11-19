import Hironaka.Resolution.Algebraic.ActualGlobalMixedDimensionResolution
import Hironaka.Resolution.Algebraic.ActualAffineSpaceSumDecomposition

/-!
# Genuine pure common native envelope and exact resolution-history choice comparison

Source-first proof: `actual-global-padding-resolution-choice-20261102.tex`.
The essential extra affine dimension is constructed, then genuine smooth
surjective native functoriality compares ONE common whole history.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.BlowUpSequence
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalPaddingResolutionChoice

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity ActualGlobalDimensionClopenPartition
  ActualGlobalVariablePaddingGeometry ActualGlobalPaddedNativeInput ActualGlobalNativeHistoryDescent
  ActualCommonPaddedEnvelopeGeometry ActualAffineSpaceSumDecomposition ActualPaddedEnvelopeNativeTranslations

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
  {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
  (V₁ V₂ : dimensionIndex X → Type u) [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)]

/-- The original component dimension supplies the essential EXTRA actual affine variables. -/
def commonVariables (d : dimensionIndex X) : Type u :=
  ULift.{u} (Fin (dimensionNat p d)) ⊕ (V₁ d ⊕ V₂ d)

private instance commonVariables_finite (d : dimensionIndex X) : Finite (commonVariables p V₁ V₂ d) := by
  dsimp only [commonVariables]
  infer_instance

omit [AlgebraicGeometry.IsNoetherian X] [IsSeparated p] [CharZero k] [IsReduced X] in
/-- Actual original dimension plus actual common variable rank is EXACTLY N₁+N₂ on every original piece. -/
theorem common_rank (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    ∀ d, dimensionNat p d + Nat.card (commonVariables p V₁ V₂ d) = N₁ + N₂ := by
  intro d
  simp only [commonVariables,Nat.card_sum,Nat.card_ulift,Nat.card_fin]
  have h1 := h₁ d
  have h2 := h₂ d
  omega

/-- ONE genuine pure common native input, internally derived from actual original component dimensions. -/
def commonInput (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) : ReducedEquidimensionalScheme k :=
  ActualGlobalPaddedNativeInput.variableEnvelope p (commonVariables p V₁ V₂) (N₁+N₂)
    (common_rank p V₁ V₂ N₁ N₂ h₁ h₂)

private abbrev pieceIso (d : dimensionIndex X) :
    ActualGlobalVariablePaddingGeometry.piece X (commonVariables p V₁ V₂) d ≅
      commonSpace (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme :=
  commonSumIso (V₁ d) (V₂ d) (dimensionPartOpen X d).toScheme (ULift.{u} (Fin (dimensionNat p d)))

private def pieceToFirst (d : dimensionIndex X) :
    ActualGlobalVariablePaddingGeometry.piece X (commonVariables p V₁ V₂) d ⟶
      ActualGlobalVariablePaddingGeometry.piece X V₁ d :=
  (pieceIso p V₁ V₂ d).hom ≫
    commonToFirst (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme

private def pieceToSecond (d : dimensionIndex X) :
    ActualGlobalVariablePaddingGeometry.piece X (commonVariables p V₁ V₂) d ⟶
      ActualGlobalVariablePaddingGeometry.piece X V₂ d :=
  (pieceIso p V₁ V₂ d).hom ≫
    commonToSecond (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme

/-- Actual common projection to the SAME first original padded input. -/
def toFirst : ActualGlobalVariablePaddingGeometry.envelope X (commonVariables p V₁ V₂) ⟶
    ActualGlobalVariablePaddingGeometry.envelope X V₁ := Limits.Sigma.map (pieceToFirst p V₁ V₂)

/-- Actual common projection to the SAME second original padded input. -/
def toSecond : ActualGlobalVariablePaddingGeometry.envelope X (commonVariables p V₁ V₂) ⟶
    ActualGlobalVariablePaddingGeometry.envelope X V₂ := Limits.Sigma.map (pieceToSecond p V₁ V₂)

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global first projection identity over the SAME original separation blowup. -/
theorem toFirst_projection : toFirst p V₁ V₂ ≫ ActualGlobalVariablePaddingGeometry.projection X V₁ =
    ActualGlobalVariablePaddingGeometry.projection X (commonVariables p V₁ V₂) := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc,toFirst,Sigma.ι_map,Category.assoc,ActualGlobalVariablePaddingGeometry.projection,
    Sigma.ι_desc,← Category.assoc]
  have he := commonSumIso_over (V₁ d) (V₂ d) (dimensionPartOpen X d).toScheme
    (ULift.{u} (Fin (dimensionNat p d)))
  have hp : pieceToFirst p V₁ V₂ d ≫ (AffineSpace (V₁ d) (dimensionPartOpen X d).toScheme ↘
      (dimensionPartOpen X d).toScheme) =
        (AffineSpace (commonVariables p V₁ V₂ d) (dimensionPartOpen X d).toScheme ↘
          (dimensionPartOpen X d).toScheme) := by
    rw [pieceToFirst,Category.assoc]
    exact he
  rw [ActualGlobalVariablePaddingGeometry.projection,Sigma.ι_desc]
  exact congrArg (fun f => f ≫ (dimensionPartOpen X d).ι) hp

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global second projection identity over the SAME original separation blowup. -/
theorem toSecond_projection : toSecond p V₁ V₂ ≫ ActualGlobalVariablePaddingGeometry.projection X V₂ =
    ActualGlobalVariablePaddingGeometry.projection X (commonVariables p V₁ V₂) := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc,toSecond,Sigma.ι_map,Category.assoc,ActualGlobalVariablePaddingGeometry.projection,
    Sigma.ι_desc,← Category.assoc]
  have he := commonSumIso_over (V₁ d) (V₂ d) (dimensionPartOpen X d).toScheme
    (ULift.{u} (Fin (dimensionNat p d)))
  have hs := common_projection_square (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d)))
    (dimensionPartOpen X d).toScheme
  have hp : pieceToSecond p V₁ V₂ d ≫ (AffineSpace (V₂ d) (dimensionPartOpen X d).toScheme ↘
      (dimensionPartOpen X d).toScheme) =
        (AffineSpace (commonVariables p V₁ V₂ d) (dimensionPartOpen X d).toScheme ↘
          (dimensionPartOpen X d).toScheme) := by
    rw [pieceToSecond,Category.assoc,← hs]
    exact he
  rw [ActualGlobalVariablePaddingGeometry.projection,Sigma.ι_desc]
  exact congrArg (fun f => f ≫ (dimensionPartOpen X d).ι) hp

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] in
private theorem pieceToFirst_relativeDimension (N₂ : ℕ)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) (d : dimensionIndex X) :
    SmoothOfRelativeDimension N₂ (pieceToFirst p V₁ V₂ d) := by
  have hdim := commonToFirst_relativeDimension (V₁ d) (V₂ d)
    (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme
  have : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin (dimensionNat p d))) + Nat.card (V₂ d))
      (commonToFirst (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme) := hdim
  have hc : SmoothOfRelativeDimension (0 + (Nat.card (ULift.{u} (Fin (dimensionNat p d))) + Nat.card (V₂ d)))
      (pieceToFirst p V₁ V₂ d) := by
    dsimp only [pieceToFirst]
    infer_instance
  simpa only [Nat.zero_add,Nat.card_ulift,Nat.card_fin,h₂ d] using hc

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₂ d)] in
private theorem pieceToSecond_relativeDimension (N₁ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁) (d : dimensionIndex X) :
    SmoothOfRelativeDimension N₁ (pieceToSecond p V₁ V₂ d) := by
  have hdim := commonToSecond_relativeDimension (V₁ d) (V₂ d)
    (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme
  have : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin (dimensionNat p d))) + Nat.card (V₁ d))
      (commonToSecond (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme) := hdim
  have hc : SmoothOfRelativeDimension (0 + (Nat.card (ULift.{u} (Fin (dimensionNat p d))) + Nat.card (V₁ d)))
      (pieceToSecond p V₁ V₂ d) := by
    dsimp only [pieceToSecond]
    infer_instance
  simpa only [Nat.zero_add,Nat.card_ulift,Nat.card_fin,h₁ d] using hc

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] in
/-- The actual GLOBAL first projection has ONE constant relative dimension N₂. -/
theorem toFirst_relativeDimension (N₂ : ℕ)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    SmoothOfRelativeDimension N₂ (toFirst p V₁ V₂) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension N₂) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  change SmoothOfRelativeDimension N₂ (Sigma.desc (fun d => pieceToFirst p V₁ V₂ d ≫
    Sigma.ι (ActualGlobalVariablePaddingGeometry.piece X V₁) d))
  apply IsZariskiLocalAtSource.sigmaDesc
  intro d
  have := pieceToFirst_relativeDimension p V₁ V₂ N₂ h₂ d
  have hc : SmoothOfRelativeDimension (N₂ + 0) (pieceToFirst p V₁ V₂ d ≫
      Sigma.ι (ActualGlobalVariablePaddingGeometry.piece X V₁) d) := inferInstance
  simpa only [Nat.add_zero] using hc

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₂ d)] in
/-- The actual GLOBAL second projection has ONE constant relative dimension N₁. -/
theorem toSecond_relativeDimension (N₁ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁) :
    SmoothOfRelativeDimension N₁ (toSecond p V₁ V₂) := by
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension N₁) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  change SmoothOfRelativeDimension N₁ (Sigma.desc (fun d => pieceToSecond p V₁ V₂ d ≫
    Sigma.ι (ActualGlobalVariablePaddingGeometry.piece X V₂) d))
  apply IsZariskiLocalAtSource.sigmaDesc
  intro d
  have := pieceToSecond_relativeDimension p V₁ V₂ N₁ h₁ d
  have hc : SmoothOfRelativeDimension (N₁ + 0) (pieceToSecond p V₁ V₂ d ≫
      Sigma.ι (ActualGlobalVariablePaddingGeometry.piece X V₂) d) := inferInstance
  simpa only [Nat.add_zero] using hc

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private instance pieceToFirst_surjective (d : dimensionIndex X) : Surjective (pieceToFirst p V₁ V₂ d) := by
  have := commonToFirst_surjective (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d)))
    (dimensionPartOpen X d).toScheme
  dsimp only [pieceToFirst]
  infer_instance

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private instance pieceToSecond_surjective (d : dimensionIndex X) : Surjective (pieceToSecond p V₁ V₂ d) := by
  have := commonToSecond_surjective (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d)))
    (dimensionPartOpen X d).toScheme
  dsimp only [pieceToSecond]
  infer_instance

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global first surjectivity, including empty original label sets. -/
theorem toFirst_surjective : Surjective (toFirst p V₁ V₂) := by
  constructor
  intro x
  obtain ⟨d,y,rfl⟩ := (sigmaOpenCover (ActualGlobalVariablePaddingGeometry.piece X V₁)).exists_eq x
  obtain ⟨w,hw⟩ := (pieceToFirst_surjective p V₁ V₂ d).1 y
  refine ⟨Sigma.ι (ActualGlobalVariablePaddingGeometry.piece X (commonVariables p V₁ V₂)) d w,?_⟩
  rw [← Scheme.Hom.comp_apply,toFirst,Sigma.ι_map,Scheme.Hom.comp_apply,hw]
  rfl

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- Genuine global second surjectivity, with the SAME original coproduct labels. -/
theorem toSecond_surjective : Surjective (toSecond p V₁ V₂) := by
  constructor
  intro x
  obtain ⟨d,y,rfl⟩ := (sigmaOpenCover (ActualGlobalVariablePaddingGeometry.piece X V₂)).exists_eq x
  obtain ⟨w,hw⟩ := (pieceToSecond_surjective p V₁ V₂ d).1 y
  refine ⟨Sigma.ι (ActualGlobalVariablePaddingGeometry.piece X (commonVariables p V₁ V₂)) d w,?_⟩
  rw [← Scheme.Hom.comp_apply,toSecond,Sigma.ι_map,Scheme.Hom.comp_apply,hw]
  rfl

private def pieceSection (d : dimensionIndex X) : (dimensionPartOpen X d).toScheme ⟶
    ActualGlobalVariablePaddingGeometry.piece X (commonVariables p V₁ V₂) d :=
  commonZeroSection (V₁ d) (V₂ d) (ULift.{u} (Fin (dimensionNat p d))) (dimensionPartOpen X d).toScheme ≫
    (pieceIso p V₁ V₂ d).inv

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private theorem pieceSection_first (d : dimensionIndex X) :
    pieceSection p V₁ V₂ d ≫ pieceToFirst p V₁ V₂ d =
      AffineSpace.homOfVector (𝟙 (dimensionPartOpen X d).toScheme) (fun _ : V₁ d => 0) := by
  rw [pieceSection,pieceToFirst,Category.assoc,Iso.inv_hom_id_assoc,commonZeroSection_first]

omit [IsSeparated p] [CharZero k] [IsReduced X] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
private theorem pieceSection_second (d : dimensionIndex X) :
    pieceSection p V₁ V₂ d ≫ pieceToSecond p V₁ V₂ d =
      AffineSpace.homOfVector (𝟙 (dimensionPartOpen X d).toScheme) (fun _ : V₂ d => 0) := by
  rw [pieceSection,pieceToSecond,Category.assoc,Iso.inv_hom_id_assoc,commonZeroSection_second]

/-- ONE genuine common section over the SAME original base. -/
def commonSection : separationSpace X ⟶
    ActualGlobalVariablePaddingGeometry.envelope X (commonVariables p V₁ V₂) :=
  inv (piecesDesc X) ≫ Limits.Sigma.map (pieceSection p V₁ V₂)

omit [IsSeparated p] [CharZero k] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- The actual common section projects to the SAME original first zero section. -/
theorem commonSection_first : commonSection p V₁ V₂ ≫ toFirst p V₁ V₂ =
    ActualGlobalVariablePaddingGeometry.zeroSection X V₁ := by
  change (inv (piecesDesc X) ≫ Limits.Sigma.map (pieceSection p V₁ V₂)) ≫
    Limits.Sigma.map (pieceToFirst p V₁ V₂) = _
  rw [Category.assoc,Sigma.map_comp_map]
  exact congrArg (fun f => inv (piecesDesc X) ≫ f)
    (congrArg Limits.Sigma.map (funext (pieceSection_first p V₁ V₂)))

omit [IsSeparated p] [CharZero k] [∀ d, Finite (V₁ d)] [∀ d, Finite (V₂ d)] in
/-- The SAME actual common section projects to the SAME original second zero section. -/
theorem commonSection_second : commonSection p V₁ V₂ ≫ toSecond p V₁ V₂ =
    ActualGlobalVariablePaddingGeometry.zeroSection X V₂ := by
  change (inv (piecesDesc X) ≫ Limits.Sigma.map (pieceSection p V₁ V₂)) ≫
    Limits.Sigma.map (pieceToSecond p V₁ V₂) = _
  rw [Category.assoc,Sigma.map_comp_map]
  exact congrArg (fun f => inv (piecesDesc X) ≫ f)
    (congrArg Limits.Sigma.map (funext (pieceSection_second p V₁ V₂)))

private def firstInputMap (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    commonInput p V₁ V₂ N₁ N₂ h₁ h₂ ⟶ ActualGlobalPaddedNativeInput.variableEnvelope p V₁ N₁ h₁ :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (toFirst p V₁ V₂) (by
    change toFirst p V₁ V₂ ≫ (ActualGlobalVariablePaddingGeometry.projection X V₁ ≫
      separationProjection X ≫ p) = _
    rw [← Category.assoc,toFirst_projection]
    rfl))

private def secondInputMap (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    commonInput p V₁ V₂ N₁ N₂ h₁ h₂ ⟶ ActualGlobalPaddedNativeInput.variableEnvelope p V₂ N₂ h₂ :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (toSecond p V₁ V₂) (by
    change toSecond p V₁ V₂ ≫ (ActualGlobalVariablePaddingGeometry.projection X V₂ ≫
      separationProjection X ≫ p) = _
    rw [← Category.assoc,toSecond_projection]
    rfl))

/-- ONE common native whole history is literally the actual pullback of the first SAME history. -/
theorem commonHistory_first (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    history p (commonVariables p V₁ V₂) (N₁+N₂) (common_rank p V₁ V₂ N₁ N₂ h₁ h₂) =
      (history p V₁ N₁ h₁).pullback (toFirst p V₁ V₂) := by
  have := toFirst_relativeDimension p V₁ V₂ N₂ h₂
  have hs : Smooth (HasUnderlyingScheme.hom (firstInputMap p V₁ V₂ N₁ N₂ h₁ h₂)) := by
    change Smooth (toFirst p V₁ V₂)
    exact SmoothOfRelativeDimension.smooth N₂ _
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (firstInputMap p V₁ V₂ N₁ N₂ h₁ h₂) hs (toFirst_surjective p V₁ V₂).1

/-- The SAME common native whole history is literally the actual pullback of the second SAME history. -/
theorem commonHistory_second (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    history p (commonVariables p V₁ V₂) (N₁+N₂) (common_rank p V₁ V₂ N₁ N₂ h₁ h₂) =
      (history p V₂ N₂ h₂).pullback (toSecond p V₁ V₂) := by
  have := toSecond_relativeDimension p V₁ V₂ N₁ h₁
  have hs : Smooth (HasUnderlyingScheme.hom (secondInputMap p V₁ V₂ N₁ N₂ h₁ h₂)) := by
    change Smooth (toSecond p V₁ V₂)
    exact SmoothOfRelativeDimension.smooth N₁ _
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (secondInputMap p V₁ V₂ N₁ N₂ h₁ h₂) hs (toSecond_surjective p V₁ V₂).1

/-- Genuine actual padding-choice independence, preserving the SAME WHOLE native clock and all internal empties. -/
theorem baseHistories_eq (N₁ N₂ : ℕ)
    (h₁ : ∀ d, dimensionNat p d + Nat.card (V₁ d) = N₁)
    (h₂ : ∀ d, dimensionNat p d + Nat.card (V₂ d) = N₂) :
    baseHistory p V₁ N₁ h₁ = baseHistory p V₂ N₂ h₂ := by
  have hfirst := congrArg (fun S => S.pullback (commonSection p V₁ V₂))
    (commonHistory_first p V₁ V₂ N₁ N₂ h₁ h₂)
  have hsecond := congrArg (fun S => S.pullback (commonSection p V₁ V₂))
    (commonHistory_second p V₁ V₂ N₁ N₂ h₁ h₂)
  rw [← pullback_comp,commonSection_first] at hfirst
  rw [← pullback_comp,commonSection_second] at hsecond
  exact hfirst.symm.trans hsecond

/-- Every actual valid padding gives exactly the canonical whole global base history. -/
theorem baseHistory_eq_canonical (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    baseHistory p V N hN = canonicalBaseHistory p :=
  baseHistories_eq p V (paddingVariables p) N (commonDimension p) hN (padding_rank p)

/-- Every SAME padded history literally descends to the SAME canonical global base clock. -/
theorem history_canonical_descends (V : dimensionIndex X → Type u) [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    history p V N hN = (canonicalBaseHistory p).pullback (projection X V) := by
  rw [history_descends, baseHistory_eq_canonical]

end
end Hironaka.Resolution.Algebraic.ActualGlobalPaddingResolutionChoice
