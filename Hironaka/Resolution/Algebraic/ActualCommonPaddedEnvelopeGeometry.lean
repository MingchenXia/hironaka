import Hironaka.Resolution.Algebraic.ActualMixedDimensionAffineResolution

/-!
# Genuine common padded pieces, including the essential extra affine d-factor

Source-first proof: `actual-common-padded-envelope-geometry-20261102.tex`.
The actual maps and exact constant relative dimensions are constructed.
Global purity and SAME native-history comparison are separate consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualCommonPaddedEnvelopeGeometry

noncomputable section

/-- Exact relative dimension of an actual relative affine projection over ANY scheme. -/
theorem affine_projection_relativeDimension (V : Type u) [Finite V] (X : Scheme.{u}) :
    SmoothOfRelativeDimension (Nat.card V) (AffineSpace V X ↘ X) := by
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (ULift.{u} ℤ) (MvPolynomial V (ULift.{u} ℤ))))
  have hg : SmoothOfRelativeDimension (Nat.card V) g :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card V))).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).mpr inferInstance))
  have hcomp : SmoothOfRelativeDimension (Nat.card V + 0)
      (g ≫ terminal.from (Spec (.of (ULift.{u} ℤ)))) := inferInstance
  rw [Nat.add_zero,terminal.comp_from] at hcomp
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (Nat.card V)) :=
    smoothOfRelativeDimension_isStableUnderBaseChange _
  exact property_of_isPullback (@SmoothOfRelativeDimension (Nat.card V))
    (IsPullback.of_hasPullback (terminal.from X)
      (terminal.from (Spec (.of (MvPolynomial V (ULift.{u} ℤ)))))) hcomp

variable (V₁ V₂ D : Type u) (X : Scheme.{u})

/-- The actual product of the TWO original affine envelopes, with the required extra actual affine factor. -/
def commonSpace : Scheme.{u} := AffineSpace D (AffineSpace V₁ (AffineSpace V₂ X))

/-- Actual projection to the first original affine envelope. -/
def commonToFirst : commonSpace V₁ V₂ D X ⟶ AffineSpace V₁ X :=
  (AffineSpace D (AffineSpace V₁ (AffineSpace V₂ X)) ↘ AffineSpace V₁ (AffineSpace V₂ X)) ≫
    AffineSpace.map V₁ (AffineSpace V₂ X ↘ X)

/-- Actual projection to the second original affine envelope. -/
def commonToSecond : commonSpace V₁ V₂ D X ⟶ AffineSpace V₂ X :=
  (AffineSpace D (AffineSpace V₁ (AffineSpace V₂ X)) ↘ AffineSpace V₁ (AffineSpace V₂ X)) ≫
    (AffineSpace V₁ (AffineSpace V₂ X) ↘ AffineSpace V₂ X)

/-- The two genuine common projections lie over the SAME actual original base. -/
theorem common_projection_square :
    commonToFirst V₁ V₂ D X ≫ (AffineSpace V₁ X ↘ X) =
      commonToSecond V₁ V₂ D X ≫ (AffineSpace V₂ X ↘ X) := by
  rw [commonToFirst,commonToSecond,Category.assoc,AffineSpace.map_over,Category.assoc]

/-- The first actual common projection has the exact rank of the OTHER padding plus the extra factor. -/
theorem commonToFirst_relativeDimension [Finite V₂] [Finite D] :
    SmoothOfRelativeDimension (Nat.card D + Nat.card V₂) (commonToFirst V₁ V₂ D X) := by
  have : SmoothOfRelativeDimension (Nat.card D)
      (AffineSpace D (AffineSpace V₁ (AffineSpace V₂ X)) ↘ AffineSpace V₁ (AffineSpace V₂ X)) :=
    affine_projection_relativeDimension D _
  have hV₂ := affine_projection_relativeDimension V₂ X
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (Nat.card V₂)) :=
    smoothOfRelativeDimension_isStableUnderBaseChange _
  have : SmoothOfRelativeDimension (Nat.card V₂) (AffineSpace.map V₁ (AffineSpace V₂ X ↘ X)) :=
    property_of_isPullback _ (AffineSpace.isPullback_map (n := V₁) (AffineSpace V₂ X ↘ X)) hV₂
  dsimp only [commonToFirst]
  infer_instance

/-- The second actual common projection has the exact first-padding rank plus the extra factor. -/
theorem commonToSecond_relativeDimension [Finite V₁] [Finite D] :
    SmoothOfRelativeDimension (Nat.card D + Nat.card V₁) (commonToSecond V₁ V₂ D X) := by
  have := affine_projection_relativeDimension D (AffineSpace V₁ (AffineSpace V₂ X))
  have := affine_projection_relativeDimension V₁ (AffineSpace V₂ X)
  dsimp only [commonToSecond]
  infer_instance

/-- Actual surjectivity is inherited from the genuine product square and two actual affine projections. -/
theorem commonToFirst_surjective : Surjective (commonToFirst V₁ V₂ D X) := by
  have : Surjective (AffineSpace.map V₁ (AffineSpace V₂ X ↘ X)) :=
    property_of_isPullback _ (AffineSpace.isPullback_map (n := V₁) (AffineSpace V₂ X ↘ X)) inferInstance
  dsimp only [commonToFirst]
  infer_instance

/-- The second projection is a genuine composite of two surjective affine projections. -/
theorem commonToSecond_surjective : Surjective (commonToSecond V₁ V₂ D X) := by
  dsimp only [commonToSecond]
  infer_instance

/-- Actual affineness of the first common projection. -/
theorem commonToFirst_affine : IsAffineHom (commonToFirst V₁ V₂ D X) := by
  have : IsAffineHom (AffineSpace.map V₁ (AffineSpace V₂ X ↘ X)) :=
    property_of_isPullback _ (AffineSpace.isPullback_map (n := V₁) (AffineSpace V₂ X ↘ X)) inferInstance
  dsimp only [commonToFirst]
  infer_instance

/-- Actual affineness of the second common projection. -/
theorem commonToSecond_affine : IsAffineHom (commonToSecond V₁ V₂ D X) := by
  dsimp only [commonToSecond]
  infer_instance

private def zeroSection (V : Type u) (Y : Scheme.{u}) : Y ⟶ AffineSpace V Y :=
  AffineSpace.homOfVector (𝟙 Y) (fun _ => 0)

private theorem zeroSection_projection (V : Type u) (Y : Scheme.{u}) :
    zeroSection V Y ≫ (AffineSpace V Y ↘ Y) = 𝟙 Y := AffineSpace.homOfVector_over _ _

/-- Actual section of the first common projection, using the other original zero section. -/
def firstSection : AffineSpace V₁ X ⟶ commonSpace V₁ V₂ D X :=
  AffineSpace.map V₁ (zeroSection V₂ X) ≫ zeroSection D (AffineSpace V₁ (AffineSpace V₂ X))

/-- Genuine first split identity. -/
theorem firstSection_projection :
    firstSection V₁ V₂ D X ≫ commonToFirst V₁ V₂ D X = 𝟙 (AffineSpace V₁ X) := by
  rw [firstSection,commonToFirst,Category.assoc,← Category.assoc (zeroSection D _),
    zeroSection_projection,Category.id_comp,← AffineSpace.map_comp,zeroSection_projection,
    AffineSpace.map_id]

/-- Actual section of the second common projection. -/
def secondSection : AffineSpace V₂ X ⟶ commonSpace V₁ V₂ D X :=
  zeroSection V₁ (AffineSpace V₂ X) ≫ zeroSection D (AffineSpace V₁ (AffineSpace V₂ X))

/-- Genuine second split identity. -/
theorem secondSection_projection :
    secondSection V₁ V₂ D X ≫ commonToSecond V₁ V₂ D X = 𝟙 (AffineSpace V₂ X) := by
  rw [secondSection,commonToSecond,Category.assoc,← Category.assoc (zeroSection D _),
    zeroSection_projection,Category.id_comp,zeroSection_projection]

/-- ONE actual common zero section over the original base. -/
def commonZeroSection : X ⟶ commonSpace V₁ V₂ D X :=
  zeroSection V₁ X ≫ firstSection V₁ V₂ D X

/-- Its first projection is the actual original first zero section. -/
theorem commonZeroSection_first :
    commonZeroSection V₁ V₂ D X ≫ commonToFirst V₁ V₂ D X =
      AffineSpace.homOfVector (𝟙 X) (fun _ : V₁ => 0) := by
  rw [commonZeroSection,Category.assoc,firstSection_projection,Category.comp_id]
  rfl

/-- Its second projection is the actual original second zero section. -/
theorem commonZeroSection_second :
    commonZeroSection V₁ V₂ D X ≫ commonToSecond V₁ V₂ D X =
      AffineSpace.homOfVector (𝟙 X) (fun _ : V₂ => 0) := by
  rw [commonZeroSection,firstSection,commonToSecond]
  simp only [Category.assoc,← Category.assoc (zeroSection D _),zeroSection_projection,Category.id_comp]
  rw [AffineSpace.map_over,← Category.assoc,zeroSection_projection,Category.id_comp]
  rfl

/-- The actual common base projection has its genuine global zero-section retraction. -/
theorem commonZeroSection_base :
    commonZeroSection V₁ V₂ D X ≫ (commonToFirst V₁ V₂ D X ≫ (AffineSpace V₁ X ↘ X)) = 𝟙 X := by
  rw [← Category.assoc,commonZeroSection_first,AffineSpace.homOfVector_over]

/-- On a dimension-d piece the essential extra actual d-factor gives the first projection dimension N₂. -/
theorem dimensionPiece_first_relativeDimension (d N₁ N₂ : ℕ) (h₂ : d ≤ N₂) :
    SmoothOfRelativeDimension N₂
      (commonToFirst (ULift.{u} (Fin (N₁-d))) (ULift.{u} (Fin (N₂-d))) (ULift.{u} (Fin d)) X) := by
  have h := commonToFirst_relativeDimension (ULift.{u} (Fin (N₁-d)))
    (ULift.{u} (Fin (N₂-d))) (ULift.{u} (Fin d)) X
  simpa only [Nat.card_ulift,Nat.card_fin,Nat.add_sub_of_le h₂] using h

/-- On the SAME dimension-d piece the extra actual d-factor gives the second projection dimension N₁. -/
theorem dimensionPiece_second_relativeDimension (d N₁ N₂ : ℕ) (h₁ : d ≤ N₁) :
    SmoothOfRelativeDimension N₁
      (commonToSecond (ULift.{u} (Fin (N₁-d))) (ULift.{u} (Fin (N₂-d))) (ULift.{u} (Fin d)) X) := by
  have h := commonToSecond_relativeDimension (ULift.{u} (Fin (N₁-d)))
    (ULift.{u} (Fin (N₂-d))) (ULift.{u} (Fin d)) X
  simpa only [Nat.card_ulift,Nat.card_fin,Nat.add_sub_of_le h₁] using h

end
end Hironaka.Resolution.Algebraic.ActualCommonPaddedEnvelopeGeometry
