import Hironaka.Resolution.Algebraic.ActualGlobalDimensionPiecePurity
import Hironaka.Resolution.Algebraic.ActualCommonPaddedEnvelopeGeometry

/-!
# One actual variable-padded envelope over the global separation blowup

Source-first proof: `actual-global-variable-padding-geometry-20261102.tex`.
The actual global clopen pieces produce the single actual smooth affine
surjective split projection.  Entire uniform purity is a separate actual
polynomial-chart consumer; no piece native histories are chosen.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalVariablePaddingGeometry

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionClopenPartition

variable (X : Scheme.{u}) [NoetherianSpace X] [IsReduced X]

abbrev pieceFamily : dimensionIndex X → Scheme.{u} := fun d => (dimensionPartOpen X d).toScheme

def piecesDesc : (∐ pieceFamily X) ⟶ separationSpace X :=
  Sigma.desc (fun d => (dimensionPartOpen X d).ι)

instance piecesDesc_isIso : IsIso (piecesDesc X) := by
  have : IsOpenImmersion (piecesDesc X) :=
    isOpenImmersion_sigmaDesc (pieceFamily X) (fun d => (dimensionPartOpen X d).ι) (by
      simpa only [Function.onFun_apply, Scheme.Opens.range_ι] using dimensionPartOpen_disjoint X)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ (⨆ d : dimensionIndex X, dimensionPartOpen X d) := by
    rw [dimensionPartOpen_cover]
    trivial
  obtain ⟨d, hd⟩ := Opens.mem_iSup.mp hx
  refine ⟨Sigma.ι (pieceFamily X) d ⟨x, hd⟩, ?_⟩
  exact congrArg (fun f => f (⟨x, hd⟩ : pieceFamily X d))
    (Sigma.ι_desc (fun d => (dimensionPartOpen X d).ι) d)

variable (V : dimensionIndex X → Type u)

abbrev piece (d : dimensionIndex X) : Scheme.{u} := AffineSpace (V d) (pieceFamily X d)

abbrev pieceProjection (d : dimensionIndex X) : piece X V d ⟶ pieceFamily X d :=
  AffineSpace (V d) (pieceFamily X d) ↘ pieceFamily X d

abbrev envelope : Scheme.{u} := ∐ piece X V

def projection : envelope X V ⟶ separationSpace X :=
  Sigma.desc (fun d => pieceProjection X V d ≫ (dimensionPartOpen X d).ι)

def pieceZeroSection (d : dimensionIndex X) : pieceFamily X d ⟶ piece X V d :=
  AffineSpace.homOfVector (𝟙 _) (fun _ => 0)

omit [IsReduced X] in
theorem pieceZeroSection_projection (d : dimensionIndex X) :
    pieceZeroSection X V d ≫ pieceProjection X V d = 𝟙 _ := AffineSpace.homOfVector_over _ _

instance pieceProjection_smooth [∀ d, Finite (V d)] (d : dimensionIndex X) :
    Smooth (pieceProjection X V d) := by
  have : SmoothOfRelativeDimension (Nat.card (V d)) (pieceProjection X V d) :=
    ActualCommonPaddedEnvelopeGeometry.affine_projection_relativeDimension (V d) (pieceFamily X d)
  exact SmoothOfRelativeDimension.smooth (Nat.card (V d)) _

omit [IsReduced X] in
theorem projection_smooth [∀ d, Finite (V d)] : Smooth (projection X V) := by
  have : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

def zeroSection : separationSpace X ⟶ envelope X V :=
  inv (piecesDesc X) ≫ Limits.Sigma.map (pieceZeroSection X V)

theorem zeroSection_projection : zeroSection X V ≫ projection X V = 𝟙 _ := by
  have hz : Limits.Sigma.map (pieceZeroSection X V) ≫ projection X V = piecesDesc X := by
    apply Sigma.hom_ext
    intro d
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, projection, Sigma.ι_desc,
      ← Category.assoc, pieceZeroSection_projection, Category.id_comp, piecesDesc, Sigma.ι_desc]
  rw [zeroSection, Category.assoc, hz, IsIso.inv_hom_id]

theorem projection_surjective : Surjective (projection X V) := by
  constructor
  intro x
  exact ⟨zeroSection X V x, congrArg (fun f => f x) (zeroSection_projection X V)⟩

theorem projection_preimage_piece (d : dimensionIndex X) :
    projection X V ⁻¹ᵁ dimensionPartOpen X d = (Sigma.ι (piece X V) d).opensRange := by
  ext z
  obtain ⟨e, x, rfl⟩ := (sigmaOpenCover (piece X V)).exists_eq z
  have hproj : projection X V (Sigma.ι (piece X V) e x) =
      (dimensionPartOpen X e).ι (pieceProjection X V e x) := by
    rw [← Scheme.Hom.comp_apply, projection, Sigma.ι_desc, Scheme.Hom.comp_apply]
  constructor
  · intro h
    change projection X V (Sigma.ι (piece X V) e x) ∈ dimensionPartOpen X d at h
    have he : e = d := by
      by_contra hed
      have hp : (dimensionPartOpen X e).ι (pieceProjection X V e x) ∈ dimensionPartOpen X d := by
        rw [← hproj]
        exact h
      exact Set.disjoint_left.mp (dimensionPartOpen_disjoint X hed)
        (pieceProjection X V e x).property hp
    subst e
    exact ⟨x, rfl⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    change projection X V (Sigma.ι (piece X V) d y) ∈ dimensionPartOpen X d
    rw [← Scheme.Hom.comp_apply, projection, Sigma.ι_desc, Scheme.Hom.comp_apply]
    exact (pieceProjection X V d y).property

theorem projection_isPullback_piece (d : dimensionIndex X) :
    IsPullback (pieceProjection X V d) (Sigma.ι (piece X V) d)
      (dimensionPartOpen X d).ι (projection X V) :=
  IsOpenImmersion.isPullback _ _ _ _ (Sigma.ι_desc _ _)
    (by simpa only [Scheme.Opens.opensRange_ι] using projection_preimage_piece X V d)

theorem projection_affine : IsAffineHom (projection X V) := by
  have hAffine : HasAffineProperty (@IsAffineHom.{u}) (fun X _ _ _ => IsAffine X) := inferInstance
  have : IsZariskiLocalAtTarget @IsAffineHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hAffine
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (dimensionPartOpen X) (dimensionPartOpen_cover X)
  intro d
  obtain ⟨e, he⟩ := exists_restrictIso_of_isPullback (dimensionPartOpen X d)
    (projection_isPullback_piece X V d).flip
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsAffineHom) e.hom, he]
  change IsAffineHom (AffineSpace (V d) (pieceFamily X d) ↘ pieceFamily X d)
  infer_instance

end
end Hironaka.Resolution.Algebraic.ActualGlobalVariablePaddingGeometry
