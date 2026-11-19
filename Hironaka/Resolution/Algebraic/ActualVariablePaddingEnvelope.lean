import Hironaka.Resolution.Algebraic.ActualAffineSpaceSumDecomposition

/-!
# Actual native envelopes for arbitrary valid finite padding choices

Source-first proof: `actual-variable-padding-envelope-20261102.tex`.
The original component dimensions, real polynomial charts and numerical
padding equations internally derive purity of the ONE actual envelope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualVariablePaddingEnvelope

noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupEquidimensionalPieces
  ActualDimensionGroupChartDimension ActualDimensionGroupPaddedCover
  ActualCommonPaddedEnvelopeGeometry

variable (R : Type u) [CommRing R]
variable (V : dimensionIndex R → Type u)

/-- Arbitrary actual affine padding over the SAME original dimension piece. -/
abbrev piece (d : dimensionIndex R) : Scheme.{u} := AffineSpace (V d) (dimensionPartOpen R d).toScheme

private abbrev pieceProjection (d : dimensionIndex R) : piece R V d ⟶ (dimensionPartOpen R d).toScheme :=
  AffineSpace (V d) (dimensionPartOpen R d).toScheme ↘ (dimensionPartOpen R d).toScheme

/-- ONE actual original coproduct; padding may use ANY specified finite variable sets. -/
abbrev envelope : Scheme.{u} := ∐ piece R V

/-- Actual projection onto the SAME original separation blowup. -/
def projection : envelope R V ⟶ affineBlowUp (dimensionSeparationIdeal R) :=
  Sigma.desc (fun d => pieceProjection R V d ≫ (dimensionPartOpen R d).ι)

private def pieceZeroSection (d : dimensionIndex R) : (dimensionPartOpen R d).toScheme ⟶ piece R V d :=
  AffineSpace.homOfVector (𝟙 _) (fun _ => 0)

private theorem pieceZeroSection_projection (d : dimensionIndex R) :
    pieceZeroSection R V d ≫ pieceProjection R V d = 𝟙 _ := AffineSpace.homOfVector_over _ _

private instance pieceProjection_smooth [∀ d, Finite (V d)] (d : dimensionIndex R) :
    Smooth (pieceProjection R V d) := by
  have : SmoothOfRelativeDimension (Nat.card (V d)) (pieceProjection R V d) :=
    affine_projection_relativeDimension (V d) (dimensionPartOpen R d).toScheme
  exact SmoothOfRelativeDimension.smooth (Nat.card (V d)) _

/-- Actual smoothness follows summandwise from the genuine affine projections. -/
theorem projection_smooth [∀ d, Finite (V d)] : Smooth (projection R V) := by
  have : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

/-- The genuine actual zero section is constructed using the SAME original clopen partition. -/
def zeroSection [IsReduced R] : affineBlowUp (dimensionSeparationIdeal R) ⟶ envelope R V :=
  inv (piecesDesc R) ≫ Limits.Sigma.map (pieceZeroSection R V)

/-- The actual global zero section retracts the actual global projection. -/
theorem zeroSection_projection [IsReduced R] : zeroSection R V ≫ projection R V = 𝟙 _ := by
  have hz : Limits.Sigma.map (pieceZeroSection R V) ≫ projection R V = piecesDesc R := by
    apply Sigma.hom_ext
    intro d
    rw [← Category.assoc,Sigma.ι_map,Category.assoc,projection,Sigma.ι_desc,
      ← Category.assoc,pieceZeroSection_projection,Category.id_comp,piecesDesc,Sigma.ι_desc]
  rw [zeroSection,Category.assoc,hz,IsIso.inv_hom_id]

/-- Actual surjectivity follows from the genuine actual section. -/
theorem projection_surjective [IsReduced R] : Surjective (projection R V) := by
  constructor
  intro x
  exact ⟨zeroSection R V x,congrArg (fun f => f x) (zeroSection_projection R V)⟩

private theorem projection_preimage_piece [IsReduced R] (d : dimensionIndex R) :
    projection R V ⁻¹ᵁ dimensionPartOpen R d = (Sigma.ι (piece R V) d).opensRange := by
  ext z
  obtain ⟨e,x,rfl⟩ := (sigmaOpenCover (piece R V)).exists_eq z
  have hproj : projection R V (Sigma.ι (piece R V) e x) =
      (dimensionPartOpen R e).ι (pieceProjection R V e x) := by
    rw [← Scheme.Hom.comp_apply,projection,Sigma.ι_desc,Scheme.Hom.comp_apply]
  constructor
  · intro h
    change projection R V (Sigma.ι (piece R V) e x) ∈ dimensionPartOpen R d at h
    have he : e = d := by
      by_contra hed
      have hp : (dimensionPartOpen R e).ι (pieceProjection R V e x) ∈ dimensionPartOpen R d := by
        rw [← hproj]
        exact h
      exact Set.disjoint_left.mp ((dimension_group_clopen_partition R).2.1 hed)
        (pieceProjection R V e x).property hp
    subst e
    exact ⟨x,rfl⟩
  · rintro ⟨y,hy⟩
    rw [← hy]
    change projection R V (Sigma.ι (piece R V) d y) ∈ dimensionPartOpen R d
    rw [← Scheme.Hom.comp_apply,projection,Sigma.ι_desc,Scheme.Hom.comp_apply]
    exact (pieceProjection R V d y).property

/-- Actual affineness is local on the SAME original clopen partition. -/
theorem projection_affine [IsReduced R] : IsAffineHom (projection R V) := by
  have hAffine : HasAffineProperty (@IsAffineHom.{u}) (fun X _ _ _ => IsAffine X) := inferInstance
  have : IsZariskiLocalAtTarget @IsAffineHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hAffine
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (dimensionPartOpen R) (dimension_group_clopen_partition R).1
  intro d
  have hsq : IsPullback (pieceProjection R V d) (Sigma.ι (piece R V) d)
      (dimensionPartOpen R d).ι (projection R V) :=
    IsOpenImmersion.isPullback _ _ _ _ (Sigma.ι_desc _ _)
      (by simpa only [Scheme.Opens.opensRange_ι] using projection_preimage_piece R V d)
  obtain ⟨e,he⟩ := exists_restrictIso_of_isPullback (dimensionPartOpen R d) hsq.flip
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsAffineHom) e.hom,he]
  change IsAffineHom (AffineSpace (V d) (dimensionPartOpen R d).toScheme ↘ (dimensionPartOpen R d).toScheme)
  infer_instance

/-- Genuine polynomial-chart map over the SAME actual original blowup chart. -/
def chart (d : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) d) :
    Spec (.of (MvPolynomial (V d) (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))) ⟶ piece R V d :=
  (AffineSpace.SpecIso (V d) (.of (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))).inv ≫
    AffineSpace.map (V d) (pieceChart R d a)

private instance map_pieceChart_isOpenImmersion (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    IsOpenImmersion (AffineSpace.map (V d) (pieceChart R d a)) :=
  property_of_isPullback _ (AffineSpace.isPullback_map (n := V d) (pieceChart R d a)) inferInstance

private instance chart_isOpenImmersion (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) : IsOpenImmersion (chart R V d a) := by
  dsimp only [chart]
  infer_instance

private theorem chart_range (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    Set.range (chart R V d a) = pieceProjection R V d ⁻¹' Set.range (pieceChart R d a) := by
  change ((chart R V d a).opensRange : Set (piece R V d)) = _
  dsimp only [chart]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact range_fst_of_isPullback (AffineSpace.isPullback_map (n := V d) (pieceChart R d a))

/-- Actual polynomial spectra cover the SAME arbitrarily padded original piece. -/
def affineOpenCover (d : dimensionIndex R) : (piece R V d).AffineOpenCover where
  I₀ := complementIdeal R (dimensionGroupIdeal R) d
  X a := .of (MvPolynomial (V d) (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))
  f a := chart R V d a
  idx x := (pieceAffineOpenCover R d).idx (pieceProjection R V d x)
  covers x := by
    rw [chart_range]
    exact (pieceAffineOpenCover R d).covers (pieceProjection R V d x)

variable (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]

private instance piece_over (d : dimensionIndex R) : (piece R V d).Over (Spec (.of k)) :=
  ⟨pieceProjection R V d ≫ (pieceAlgScheme R k d).hom⟩

private instance piece_finiteType [∀ d, Finite (V d)] (d : dimensionIndex R) :
    FiniteType (piece R V d ↘ Spec (.of k)) := by
  have : FiniteType (pieceAlgScheme R k d).hom := (pieceAlgScheme R k d).prop.1
  change FiniteType (pieceProjection R V d ≫ (pieceAlgScheme R k d).hom)
  have : Smooth (pieceProjection R V d) := pieceProjection_smooth R V d
  have : LocallyOfFinitePresentation (pieceProjection R V d) := inferInstance
  have : IsAffineHom (pieceProjection R V d) :=
    inferInstanceAs (IsAffineHom (AffineSpace (V d) (dimensionPartOpen R d).toScheme ↘ (dimensionPartOpen R d).toScheme))
  infer_instance

private theorem chart_comp_projection (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    chart R V d a ≫ pieceProjection R V d =
      Spec.map (CommRingCat.ofHom (algebraMap
        (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)
        (MvPolynomial (V d) (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)))) ≫ pieceChart R d a := by
  simp only [chart,pieceProjection,Category.assoc,AffineSpace.map_over,
    AffineSpace.SpecIso_inv_over_assoc,MvPolynomial.algebraMap_eq]

/-- The actual chart's coefficient map is exactly the ORIGINAL polynomial coefficient map. -/
theorem chart_comp_structure (d : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) d) :
    chart R V d a ≫ (piece R V d ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k
        (MvPolynomial (V d) (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)))) := by
  change chart R V d a ≫ (pieceProjection R V d ≫ (pieceAlgScheme R k d).hom) = _
  rw [← Category.assoc,chart_comp_projection,Category.assoc]
  change _ ≫ (pieceChart R d a ≫ ((dimensionPartOpen R d).toScheme ↘ Spec (.of k))) = _
  rw [pieceChart_comp_structure R k,← Spec.map_comp]
  rfl

private theorem chart_components [IsReduced R] [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N)
    (d : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) d) :
    let P : Type u := MvPolynomial (V d) (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)
    letI : CommRing P := inferInstance
    ∀ p : minimalPrimes P, ringKrullDim (P ⧸ p.val) = N := by
  dsimp only
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let C := affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val
  have : Algebra.FiniteType R C := affineBlowUpAlgebra_finiteType R _ (IsNoetherian.noetherian _) a.val
  have : Algebra.FiniteType k C := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) inferInstance
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hC : ∀ q : minimalPrimes C, ringKrullDim (C ⧸ q.val) = dimensionNat R k d :=
    fun q => ((dimension_group_chart_equidimensional R k d a).2 q).trans (dimensionNat_spec R k d).symm
  have hn : (dimensionNat R k d : WithBot ℕ∞) + Nat.card (V d) = N := by exact_mod_cast hN d
  exact fun p => (mvPolynomial_component_dimensions C (V d) (dimensionNat R k d) hC p).trans hn

private theorem smoothLocus_dimension_congr {X Y : Scheme.{u}} (f g : X ⟶ Y)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) (N : ℕ) :
    SmoothOfRelativeDimension N (f.smoothLocus.ι ≫ f) ↔
      SmoothOfRelativeDimension N (g.smoothLocus.ι ≫ g) := by
  subst h
  rfl

private theorem chart_smoothLocus [CharZero k] [IsReduced R] [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N)
    (d : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) d) :
    SmoothOfRelativeDimension N ((chart R V d a ≫ (piece R V d ↘ Spec (.of k))).smoothLocus.ι ≫
      (chart R V d a ≫ (piece R V d ↘ Spec (.of k)))) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let C := affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val
  have : IsReduced C := (dimension_group_chart_equidimensional R k d a).1
  have : Algebra.FiniteType R C := affineBlowUpAlgebra_finiteType R _ (IsNoetherian.noetherian _) a.val
  have : Algebra.FiniteType k C := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) inferInstance
  have h := affine_smoothLocus_of_component_dimensions (MvPolynomial (V d) C) k N
    (chart_components R V k N hN d a)
  exact (smoothLocus_dimension_congr _ _ (chart_comp_structure R V k d a) N).mpr h

/-- Actual original chart component dimensions prove purity of EACH actual arbitrarily padded piece. -/
theorem piece_isReducedEquidimensional [CharZero k] [IsReduced R] [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) (d : dimensionIndex R) :
    (piece R V d).IsReducedEquidimensional k := by
  apply Scheme.IsReducedEquidimensional.of_openCover (affineOpenCover R V d).openCover N
  · intro a
    have := (dimension_group_chart_equidimensional R k d a).1
    change IsReduced (Spec (.of (MvPolynomial (V d) (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))))
    infer_instance
  · exact chart_smoothLocus R V k N hN d

private instance envelope_over : (envelope R V).Over (Spec (.of k)) :=
  ⟨projection R V ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R))⟩

private instance envelope_finiteType [IsReduced R] [∀ d, Finite (V d)] :
    FiniteType (envelope R V ↘ Spec (.of k)) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : Smooth (projection R V) := projection_smooth R V
  have : IsAffineHom (projection R V) := projection_affine R V
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  change FiniteType (projection R V ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)))
  infer_instance

private instance envelope_separated [IsReduced R] : IsSeparated (envelope R V ↘ Spec (.of k)) := by
  have : IsAffineHom (projection R V) := projection_affine R V
  have : IsSeparated (projection R V) := IsSeparated.of_isAffineHom _
  change IsSeparated (projection R V ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)))
  infer_instance

private theorem envelope_summand_structure (d : dimensionIndex R) :
    Sigma.ι (piece R V) d ≫ (envelope R V ↘ Spec (.of k)) =
      pieceProjection R V d ≫ (pieceAlgScheme R k d).hom := by
  change Sigma.ι (piece R V) d ≫ (projection R V ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫ _) = _
  rw [← Category.assoc,projection,Sigma.ι_desc,Category.assoc]
  rfl

private def envelopeOpenCover : (envelope R V).OpenCover :=
  (sigmaOpenCover (piece R V)).bind fun d => (affineOpenCover R V d).openCover

/-- Genuine purity of the ONE actual arbitrary-padding envelope, derived with ONE numerical N. -/
theorem envelope_isReducedEquidimensional [CharZero k] [IsReduced R] [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) :
    (envelope R V).IsReducedEquidimensional k := by
  apply Scheme.IsReducedEquidimensional.of_openCover (envelopeOpenCover R V) N
  · change ∀ i : (Σ d : dimensionIndex R, complementIdeal R (dimensionGroupIdeal R) d),
      IsReduced (Spec (.of (MvPolynomial (V i.1) (affineBlowUpAlgebra (dimensionSeparationIdeal R) i.2.val))))
    intro i
    have := (dimension_group_chart_equidimensional R k i.1 i.2).1
    infer_instance
  · change ∀ i : (Σ d : dimensionIndex R, complementIdeal R (dimensionGroupIdeal R) d),
      SmoothOfRelativeDimension N ((((chart R V i.1 i.2 ≫ Sigma.ι (piece R V) i.1) ≫
        (envelope R V ↘ Spec (.of k))).smoothLocus.ι) ≫
          ((chart R V i.1 i.2 ≫ Sigma.ι (piece R V) i.1) ≫ (envelope R V ↘ Spec (.of k))))
    intro i
    have h : (chart R V i.1 i.2 ≫ Sigma.ι (piece R V) i.1) ≫ (envelope R V ↘ Spec (.of k)) =
        chart R V i.1 i.2 ≫ (piece R V i.1 ↘ Spec (.of k)) := by
      change (chart R V i.1 i.2 ≫ Sigma.ι (piece R V) i.1) ≫
        (envelope R V ↘ Spec (.of k)) = chart R V i.1 i.2 ≫
          (pieceProjection R V i.1 ≫ (pieceAlgScheme R k i.1).hom)
      rw [Category.assoc,envelope_summand_structure]
    exact (smoothLocus_dimension_congr _ _ h N).mpr (chart_smoothLocus R V k N hN i.1 i.2)

/-- ONE actual native input for ANY genuine finite padding choice satisfying its actual rank equations. -/
def variableEnvelope [CharZero k] [IsReduced R] [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat R k d + Nat.card (V d) = N) : ReducedEquidimensionalScheme k :=
  ⟨AlgScheme.of (k := k) (envelope R V),envelope_isReducedEquidimensional R V k N hN⟩

end
end Hironaka.Resolution.Algebraic.ActualVariablePaddingEnvelope
