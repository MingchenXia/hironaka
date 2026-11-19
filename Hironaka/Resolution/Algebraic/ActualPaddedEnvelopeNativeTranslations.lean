import Hironaka.Resolution.Algebraic.ActualDimensionGroupPaddedCover
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36

/-!
# Actual translations and the ONE native padded resolution history

Source-first proof: `actual-padded-envelope-native-translations-20261102.tex`.
The actual native history retains its clock under literal integer translations.
No history on the original mixed-dimensional scheme is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualPaddedEnvelopeNativeTranslations

noncomputable section

section AffineTranslations
variable (σ : Type u) (X : Scheme.{u})

private def affineTranslationHom (v : σ → ℤ) : AffineSpace σ X ⟶ AffineSpace σ X :=
  AffineSpace.homOfVector (AffineSpace σ X ↘ X)
    (fun i => AffineSpace.coord X i + (v i : Γ(AffineSpace σ X, ⊤)))

private theorem affineTranslationHom_projection (v : σ → ℤ) :
    affineTranslationHom σ X v ≫ (AffineSpace σ X ↘ X) = AffineSpace σ X ↘ X :=
  AffineSpace.homOfVector_over _ _

@[simp] private theorem affineTranslationHom_coord (v : σ → ℤ) (i : σ) :
    (affineTranslationHom σ X v).appTop (AffineSpace.coord X i) =
      AffineSpace.coord X i + (v i : Γ(AffineSpace σ X, ⊤)) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private theorem affineTranslationHom_comp (v w : σ → ℤ) :
    affineTranslationHom σ X v ≫ affineTranslationHom σ X w =
      affineTranslationHom σ X (v+w) := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, affineTranslationHom_projection]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineTranslationHom_coord,
      map_add, map_intCast, Pi.add_apply, Int.cast_add]
    ring

private theorem affineTranslationHom_zero :
    affineTranslationHom σ X 0 = 𝟙 (AffineSpace σ X) := by
  apply AffineSpace.hom_ext
  · rw [affineTranslationHom_projection, Category.id_comp]
  · intro i
    simp

/-- An actual scheme automorphism over the SAME base, constructed from the
literal original polynomial coordinates and an integer vector. -/
def affineTranslation (v : σ → ℤ) : AffineSpace σ X ≅ AffineSpace σ X where
  hom := affineTranslationHom σ X v
  inv := affineTranslationHom σ X (-v)
  hom_inv_id := by rw [affineTranslationHom_comp, add_neg_cancel, affineTranslationHom_zero]
  inv_hom_id := by rw [affineTranslationHom_comp, neg_add_cancel, affineTranslationHom_zero]

theorem affineTranslation_projection (v : σ → ℤ) :
    (affineTranslation σ X v).hom ≫ (AffineSpace σ X ↘ X) = AffineSpace σ X ↘ X :=
  affineTranslationHom_projection σ X v
end AffineTranslations

open ActualDimensionGroupBlowup ActualDimensionGroupEquidimensionalPieces
  ActualDimensionGroupPaddedCover

variable (R : Type u) [CommRing R] (k : Type u) [Field k] [CharZero k]
  [Algebra k R] [Algebra.FiniteType k R] [IsReduced R]

/-- The literal coproduct of actual translations on all original padded pieces. -/
def envelopeTranslation (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    (paddedEnvelope R k).obj.left ⟶ (paddedEnvelope R k).obj.left :=
  Limits.Sigma.map (fun d =>
    (affineTranslation (paddingVariables R k d) (dimensionPartOpen R d).toScheme (v d)).hom)

instance envelopeTranslation_isIso
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    IsIso (envelopeTranslation R k v) := by
  dsimp only [envelopeTranslation]
  infer_instance

/-- The actual translation fixes the SAME projection to the original blowup. -/
theorem envelopeTranslation_projection
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    envelopeTranslation R k v ≫ envelopeProjection R k = envelopeProjection R k := by
  apply Sigma.hom_ext
  intro d
  rw [← Category.assoc, envelopeTranslation, Sigma.ι_map, Category.assoc]
  have hd := (envelopeProjection_isPullback_piece R k d).w
  have ht : (affineTranslation (paddingVariables R k d)
      (dimensionPartOpen R d).toScheme (v d)).hom ≫ paddedProjection R k d =
      paddedProjection R k d :=
    affineTranslation_projection (paddingVariables R k d) (dimensionPartOpen R d).toScheme (v d)
  rw [← hd, ← Category.assoc, ht]

private theorem envelopeTranslation_structure
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    envelopeTranslation R k v ≫ (paddedEnvelope R k).obj.hom =
      (paddedEnvelope R k).obj.hom := by
  change envelopeTranslation R k v ≫ (envelopeProjection R k ≫
    affineBlowUp.π (dimensionSeparationIdeal R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) = _
  rw [← Category.assoc, envelopeTranslation_projection]
  rfl

private def envelopeTranslationInput
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    paddedEnvelope R k ⟶ paddedEnvelope R k :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (envelopeTranslation R k v) (envelopeTranslation_structure R k v))

/-- ONE actual native resolution family is chosen for ALL characteristic-zero
fields at once, preserving the native smooth/field compatibility witness. -/
def nativeResolutionFamily : ∀ (K : Type u) [Field K] [CharZero K],
    BlowUpSequenceFunctor (ReducedEquidimensionalScheme K) :=
  Classical.choose exists_functorial_resolution

theorem nativeResolutionFamily_commutesWithSmoothMorphisms (K : Type u)
    [Field K] [CharZero K] : CommutesWithSmoothMorphisms (nativeResolutionFamily K) :=
  (Classical.choose_spec exists_functorial_resolution).2.1 K

theorem nativeResolutionFamily_commutesWithChangeOfFields :
    CommutesWithChangeOfFields nativeResolutionFamily :=
  (Classical.choose_spec exists_functorial_resolution).2.2

/-- Run the SAME actual chosen native family on the ONE actual padded input. -/
def nativePaddedHistory : (paddedEnvelope R k).obj.left.BlowUpSequence :=
  nativeResolutionFamily k (paddedEnvelope R k)

theorem nativePaddedHistory_isStrongResolution :
    @Scheme.BlowUpSequence.IsStrongResolution k _ (paddedEnvelope R k).obj
      (nativePaddedHistory R k) :=
  (Classical.choose_spec exists_functorial_resolution).1 k (paddedEnvelope R k)

/-- Smooth SURJECTIVE naturality gives literal whole-sequence equality.
No eraseEmpty call or independent component clock occurs. -/
theorem nativePaddedHistory_eq_pullback_translation
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    nativePaddedHistory R k =
      (nativePaddedHistory R k).pullback (envelopeTranslation R k v) := by
  have ht : Smooth (HasUnderlyingScheme.hom (envelopeTranslationInput R k v)) := by
    change Smooth (envelopeTranslation R k v)
    infer_instance
  exact (nativeResolutionFamily_commutesWithSmoothMorphisms k).eq_pullback_of_surjective
    (envelopeTranslationInput R k v) ht
    (AlgebraicGeometry.surjective_of_isIso (envelopeTranslation R k v))

/-- The actual first ideal sheaf; the empty sequence has the actual unit ideal. -/
def initialCentre : {X : Scheme.{u}} → X.BlowUpSequence → X.IdealSheafData
  | _, .nil _ => ⊤
  | _, .cons _ D _ => D

private theorem initialCentre_pullback {X Y : Scheme.{u}}
    (S : X.BlowUpSequence) (f : Y ⟶ X) :
    initialCentre (S.pullback f) = (initialCentre S).comap f := by
  cases S <;> simp [initialCentre, Scheme.BlowUpSequence.pullback]

/-- The SAME actual first-centre ideal is invariant under every literal
integer translation, derived from the actual native whole-history equality. -/
theorem nativePaddedHistory_initialCentre_translation
    (v : ∀ d : dimensionIndex R, paddingVariables R k d → ℤ) :
    (initialCentre (nativePaddedHistory R k)).comap (envelopeTranslation R k v) =
      initialCentre (nativePaddedHistory R k) := by
  rw [← initialCentre_pullback, ← nativePaddedHistory_eq_pullback_translation R k v]

end
end Hironaka.Resolution.Algebraic.ActualPaddedEnvelopeNativeTranslations
