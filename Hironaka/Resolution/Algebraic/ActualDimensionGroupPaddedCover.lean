import Hironaka.Resolution.Algebraic.ActualDimensionGroupEquidimensionalPieces
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Polynomial.Quotient

/-! ONE actual native equidimensional padded cover of the SAME dimension-
separation blowup, with a smooth surjective projection and actual zero section.
Source-first proof: `actual-dimension-group-padded-cover-20261101.tex`.
No native resolution history or centre descent is asserted here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v

namespace Hironaka.Resolution.Algebraic.ActualDimensionGroupPaddedCover
noncomputable section
open ActualDimensionGroupBlowup ActualDimensionGroupChartDimension
  ActualDimensionGroupEquidimensionalPieces

section Components
variable (A : Type u) [CommRing A]

/-- Actual polynomial minimal primes are extensions of actual original minimal primes. -/
theorem polynomial_minimal_prime_origin (p : minimalPrimes (Polynomial A)) :
    ∃ q : minimalPrimes A, p.val = q.val.map Polynomial.C := by
  have : p.val.IsPrime := p.property.isPrime
  have : (p.val.comap Polynomial.C).IsPrime := Ideal.IsPrime.comap Polynomial.C
  obtain ⟨q,hq,hqp⟩ := Ideal.exists_minimalPrimes_le (J := p.val.comap Polynomial.C) bot_le
  have : q.IsPrime := hq.isPrime
  have hle : q.map Polynomial.C ≤ p.val := Ideal.map_le_iff_le_comap.mpr hqp
  refine ⟨⟨q,hq⟩,le_antisymm ?_ hle⟩
  exact p.property.2 ⟨inferInstance,bot_le⟩ hle

private theorem component_dimensions_congr {C : Type v} [CommRing C] (e : A ≃+* C)
    (n : ℕ) (hA : ∀ p : minimalPrimes A, ringKrullDim (A ⧸ p.val) = n) :
    ∀ p : minimalPrimes C, ringKrullDim (C ⧸ p.val) = n := by
  intro p
  let q := p.val.comap e.toRingHom
  have hq : q ∈ minimalPrimes A := by
    have h := Ideal.minimalPrimes_comap_of_surjective (f := e.toRingHom) e.surjective p.property
    simpa only [Ideal.comap_bot_of_injective e.toRingHom e.injective] using h
  have hmap : p.val = q.map e.toRingHom :=
    (Ideal.map_comap_of_surjective e.toRingHom e.surjective p.val).symm
  exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv q p.val e hmap)).symm.trans
    (hA ⟨q,hq⟩)

private theorem polynomial_component_dimensions [IsNoetherianRing A] (n : ℕ)
    (hA : ∀ p : minimalPrimes A, ringKrullDim (A ⧸ p.val) = n) :
    ∀ p : minimalPrimes (Polynomial A), ringKrullDim (Polynomial A ⧸ p.val) = n + 1 := by
  intro p
  obtain ⟨q,hq⟩ := polynomial_minimal_prime_origin A p
  rw [hq,← ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial q.val),
    Polynomial.ringKrullDim_of_isNoetherianRing,hA q]

/-- All actual finite polynomial component dimensions are derived from the original ones. -/
theorem mvPolynomial_component_dimensions [IsNoetherianRing A] (σ : Type v) [Finite σ]
    (n : ℕ) (hA : ∀ p : minimalPrimes A, ringKrullDim (A ⧸ p.val) = n) :
    ∀ p : minimalPrimes (MvPolynomial σ A),
      ringKrullDim (MvPolynomial σ A ⧸ p.val) = n + Nat.card σ := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e IH =>
    have h := component_dimensions_congr _ (MvPolynomial.renameEquiv A e).toRingEquiv _ IH
    simpa only [Nat.card_congr e,Nat.cast_add] using h
  | h_empty =>
    simpa using component_dimensions_congr A (MvPolynomial.isEmptyRingEquiv A PEmpty.{v+1}).symm n hA
  | @h_option σ _ IH =>
    have h := polynomial_component_dimensions (MvPolynomial σ A) (n + Nat.card σ) IH
    have h' := component_dimensions_congr _ (MvPolynomial.optionEquivLeft A σ).toRingEquiv.symm _ h
    simpa [Nat.card_eq_fintype_card,Nat.add_assoc] using h'
end Components

variable (R : Type u) [CommRing R] (k : Type u) [Field k]
  [Algebra k R] [Algebra.FiniteType k R]

private instance dimensionIndex_finite_of_noetherian [IsNoetherianRing R] :
    Finite (dimensionIndex R) := dimensionIndex_finite R

/-- ONE finite maximum, with empty maximum zero. -/
def commonDimension : ℕ := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : Fintype (dimensionIndex R) := Fintype.ofFinite _
  exact Finset.univ.sup (dimensionNat R k)

theorem commonDimension_ge (d : dimensionIndex R) : dimensionNat R k d ≤ commonDimension R k := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : Fintype (dimensionIndex R) := Fintype.ofFinite _
  change dimensionNat R k d ≤ Finset.univ.sup (dimensionNat R k)
  exact Finset.le_sup (Finset.mem_univ d)

def paddingDimension (d : dimensionIndex R) : ℕ := commonDimension R k - dimensionNat R k d

theorem paddingDimension_add (d : dimensionIndex R) :
    paddingDimension R k d + dimensionNat R k d = commonDimension R k :=
  Nat.sub_add_cancel (commonDimension_ge R k d)

abbrev paddingVariables (d : dimensionIndex R) : Type u := ULift.{u} (Fin (paddingDimension R k d))

/-- Actual relative affine space over the SAME original clopen piece. -/
def paddedPiece (d : dimensionIndex R) : Scheme.{u} :=
  AffineSpace (paddingVariables R k d) (dimensionPartOpen R d).toScheme

def paddedProjection (d : dimensionIndex R) : paddedPiece R k d ⟶ (dimensionPartOpen R d).toScheme :=
  AffineSpace (paddingVariables R k d) (dimensionPartOpen R d).toScheme ↘ (dimensionPartOpen R d).toScheme

def paddedZeroSection (d : dimensionIndex R) : (dimensionPartOpen R d).toScheme ⟶ paddedPiece R k d :=
  AffineSpace.homOfVector (𝟙 _) (fun _ => 0)

theorem paddedZeroSection_projection (d : dimensionIndex R) :
    paddedZeroSection R k d ≫ paddedProjection R k d = 𝟙 _ :=
  AffineSpace.homOfVector_over _ _

private theorem affineSpace_projection_smooth (σ : Type u) [Finite σ] (X : Scheme.{u}) :
    Smooth (AffineSpace σ X ↘ X) := by
  have ht : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  have hp : SmoothOfRelativeDimension (Nat.card σ) (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (MvPolynomial σ (ULift.{u} ℤ))))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card σ))).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).mpr inferInstance))
  have : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (MvPolynomial σ (ULift.{u} ℤ))))) :=
    SmoothOfRelativeDimension.smooth (Nat.card σ) _
  have hm : Smooth (terminal.from (Spec (.of (MvPolynomial σ (ULift.{u} ℤ))))) := by
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (MvPolynomial σ (ULift.{u} ℤ)))))]
    infer_instance
  have : MorphismProperty.IsStableUnderBaseChange (@Smooth.{u}) := smooth_isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Smooth.{u}) (IsPullback.of_hasPullback (terminal.from X)
      (terminal.from (Spec (.of (MvPolynomial σ (ULift.{u} ℤ)))))).flip hm

instance paddedProjection_smooth (d : dimensionIndex R) : Smooth (paddedProjection R k d) :=
  affineSpace_projection_smooth (paddingVariables R k d) (dimensionPartOpen R d).toScheme

instance paddedProjection_isAffineHom (d : dimensionIndex R) : IsAffineHom (paddedProjection R k d) :=
  inferInstanceAs (IsAffineHom (AffineSpace (paddingVariables R k d)
    (dimensionPartOpen R d).toScheme ↘ (dimensionPartOpen R d).toScheme))

private abbrev pieceFamily : dimensionIndex R → Scheme.{u} := fun d => (dimensionPartOpen R d).toScheme

/-- The actual coproduct of original inclusions into the SAME separation blowup. -/
def piecesDesc : (∐ pieceFamily R) ⟶ affineBlowUp (dimensionSeparationIdeal R) :=
  Sigma.desc (fun d => (dimensionPartOpen R d).ι)

instance piecesDesc_isIso [IsReduced R] : IsIso (piecesDesc R) := by
  have : IsOpenImmersion (piecesDesc R) :=
    isOpenImmersion_sigmaDesc (pieceFamily R) (fun d => (dimensionPartOpen R d).ι) (by
      simpa only [Function.onFun_apply,Scheme.Opens.range_ι] using
        (dimension_group_clopen_partition R).2.1)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ ⨆ d : dimensionIndex R, dimensionPartOpen R d := by
    rw [(dimension_group_clopen_partition R).1]
    trivial
  obtain ⟨d,hd⟩ := Opens.mem_iSup.mp hx
  refine ⟨Sigma.ι (pieceFamily R) d ⟨x,hd⟩,?_⟩
  exact congrArg (fun f => f (⟨x,hd⟩ : pieceFamily R d))
    (Sigma.ι_desc (fun d => (dimensionPartOpen R d).ι) d)

private abbrev rawEnvelope : Scheme.{u} := ∐ (paddedPiece R k)

private def rawProjection : rawEnvelope R k ⟶ affineBlowUp (dimensionSeparationIdeal R) :=
  Sigma.desc (fun d => paddedProjection R k d ≫ (dimensionPartOpen R d).ι)

private theorem rawProjection_smooth : Smooth (rawProjection R k) := by
  have : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

private def rawZeroSection [IsReduced R] :
    affineBlowUp (dimensionSeparationIdeal R) ⟶ rawEnvelope R k :=
  inv (piecesDesc R) ≫ Limits.Sigma.map (paddedZeroSection R k)

private theorem rawZeroSection_projection [IsReduced R] :
    rawZeroSection R k ≫ rawProjection R k = 𝟙 _ := by
  have hz : Limits.Sigma.map (paddedZeroSection R k) ≫ rawProjection R k = piecesDesc R := by
    apply Sigma.hom_ext
    intro d
    rw [← Category.assoc,Sigma.ι_map,Category.assoc]
    rw [rawProjection,Sigma.ι_desc,← Category.assoc,paddedZeroSection_projection,
      Category.id_comp,piecesDesc,Sigma.ι_desc]
  rw [rawZeroSection,Category.assoc,hz,IsIso.inv_hom_id]

private theorem rawProjection_preimage_piece (d : dimensionIndex R) [IsReduced R] :
    rawProjection R k ⁻¹ᵁ dimensionPartOpen R d = (Sigma.ι (paddedPiece R k) d).opensRange := by
  ext z
  obtain ⟨e,x,rfl⟩ := (sigmaOpenCover (paddedPiece R k)).exists_eq z
  have hproj : rawProjection R k (Sigma.ι (paddedPiece R k) e x) =
      (dimensionPartOpen R e).ι (paddedProjection R k e x) := by
    rw [← Scheme.Hom.comp_apply,rawProjection,Sigma.ι_desc,Scheme.Hom.comp_apply]
  constructor
  · intro h
    change rawProjection R k (Sigma.ι (paddedPiece R k) e x) ∈ dimensionPartOpen R d at h
    have he : e = d := by
      by_contra hed
      have hp : (dimensionPartOpen R e).ι (paddedProjection R k e x) ∈ dimensionPartOpen R d := by
        rw [← hproj]
        exact h
      exact Set.disjoint_left.mp ((dimension_group_clopen_partition R).2.1 hed)
        (paddedProjection R k e x).property hp
    subst e
    exact ⟨x,rfl⟩
  · rintro ⟨y,hy⟩
    rw [← hy]
    change rawProjection R k (Sigma.ι (paddedPiece R k) d y) ∈ dimensionPartOpen R d
    rw [← Scheme.Hom.comp_apply,rawProjection,Sigma.ι_desc,Scheme.Hom.comp_apply]
    exact (paddedProjection R k d y).property

private theorem rawProjection_isAffineHom [IsReduced R] : IsAffineHom (rawProjection R k) := by
  have hAffine : HasAffineProperty (@IsAffineHom.{u}) (fun X _ _ _ => IsAffine X) := inferInstance
  have : IsZariskiLocalAtTarget @IsAffineHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hAffine
  have : MorphismProperty.RespectsIso @IsAffineHom :=
    inferInstance
  have hcov : ⨆ d : dimensionIndex R, dimensionPartOpen R d = ⊤ :=
    (dimension_group_clopen_partition R).1
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (dimensionPartOpen R) hcov
  intro d
  have hsq : IsPullback (paddedProjection R k d) (Sigma.ι (paddedPiece R k) d)
      (dimensionPartOpen R d).ι (rawProjection R k) :=
    IsOpenImmersion.isPullback _ _ _ _ (Sigma.ι_desc _ _)
      (by simpa only [Scheme.Opens.opensRange_ι] using rawProjection_preimage_piece R k d)
  obtain ⟨e,he⟩ := exists_restrictIso_of_isPullback (dimensionPartOpen R d) hsq.flip
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsAffineHom) e.hom,he]
  infer_instance

private instance padded_over (d : dimensionIndex R) : (paddedPiece R k d).Over (Spec (.of k)) :=
  ⟨paddedProjection R k d ≫ (pieceAlgScheme R k d).hom⟩

private instance padded_finiteType (d : dimensionIndex R) :
    FiniteType (paddedPiece R k d ↘ Spec (.of k)) := by
  have : FiniteType (pieceAlgScheme R k d).hom := (pieceAlgScheme R k d).prop.1
  change FiniteType (paddedProjection R k d ≫ (pieceAlgScheme R k d).hom)
  infer_instance

/-- The SAME padded original chart, with its native affine-space comparison map. -/
def paddedChart (d : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) d) :
    Spec (.of (MvPolynomial (paddingVariables R k d)
      (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))) ⟶ paddedPiece R k d :=
  (AffineSpace.SpecIso (paddingVariables R k d)
    (.of (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))).inv ≫
      AffineSpace.map (paddingVariables R k d) (pieceChart R d a)

private instance affineSpace_map_pieceChart_isOpenImmersion (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    IsOpenImmersion (AffineSpace.map (paddingVariables R k d) (pieceChart R d a)) :=
  property_of_isPullback _ (AffineSpace.isPullback_map (n := paddingVariables R k d)
    (pieceChart R d a)) inferInstance

instance paddedChart_isOpenImmersion (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) : IsOpenImmersion (paddedChart R k d a) := by
  dsimp only [paddedChart]
  infer_instance

private theorem paddedChart_range (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    Set.range (paddedChart R k d a) = paddedProjection R k d ⁻¹' Set.range (pieceChart R d a) := by
  change ((paddedChart R k d a).opensRange : Set (paddedPiece R k d)) = _
  dsimp only [paddedChart]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact range_fst_of_isPullback (AffineSpace.isPullback_map (n := paddingVariables R k d)
    (pieceChart R d a))

theorem paddedChart_comp_projection (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    paddedChart R k d a ≫ paddedProjection R k d =
      Spec.map (CommRingCat.ofHom (algebraMap
        (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)
        (MvPolynomial (paddingVariables R k d)
          (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)))) ≫ pieceChart R d a := by
  simp only [paddedChart,paddedProjection,Category.assoc,AffineSpace.map_over,
    AffineSpace.SpecIso_inv_over_assoc,MvPolynomial.algebraMap_eq]

theorem paddedChart_comp_structure (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    paddedChart R k d a ≫ (paddedPiece R k d ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (paddingVariables R k d)
        (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)))) := by
  change paddedChart R k d a ≫ (paddedProjection R k d ≫ (pieceAlgScheme R k d).hom) = _
  rw [← Category.assoc,paddedChart_comp_projection,Category.assoc]
  change _ ≫ (pieceChart R d a ≫ ((dimensionPartOpen R d).toScheme ↘ Spec (.of k))) = _
  rw [pieceChart_comp_structure,← Spec.map_comp]
  rfl

/-- The genuine polynomial-chart cover of this SAME padded piece. -/
def paddedAffineOpenCover (d : dimensionIndex R) : (paddedPiece R k d).AffineOpenCover where
  I₀ := complementIdeal R (dimensionGroupIdeal R) d
  X a := .of (MvPolynomial (paddingVariables R k d)
    (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))
  f a := paddedChart R k d a
  idx x := (pieceAffineOpenCover R d).idx (paddedProjection R k d x)
  covers x := by
    rw [paddedChart_range]
    exact (pieceAffineOpenCover R d).covers (paddedProjection R k d x)

private theorem paddedChart_components [IsReduced R] (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    let P : Type u := MvPolynomial (paddingVariables R k d)
      (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)
    letI : CommRing P := inferInstance
    ∀ p : minimalPrimes P, ringKrullDim (P ⧸ p.val) = commonDimension R k := by
  dsimp only
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let C := affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val
  have : Algebra.FiniteType R C :=
    affineBlowUpAlgebra_finiteType R _ (IsNoetherian.noetherian _) a.val
  have : Algebra.FiniteType k C :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) inferInstance
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hC : ∀ q : minimalPrimes C, ringKrullDim (C ⧸ q.val) = dimensionNat R k d :=
    fun q => ((dimension_group_chart_equidimensional R k d a).2 q).trans (dimensionNat_spec R k d).symm
  have hc : Nat.card (paddingVariables R k d) = paddingDimension R k d := by
    simp only [paddingVariables,Nat.card_eq_fintype_card,Fintype.card_ulift,Fintype.card_fin]
  have hn : dimensionNat R k d + Nat.card (paddingVariables R k d) = commonDimension R k := by
    rw [hc,Nat.add_comm,paddingDimension_add]
  have hn' : (dimensionNat R k d : WithBot ℕ∞) + Nat.card (paddingVariables R k d) =
      commonDimension R k := by exact_mod_cast hn
  intro p
  exact (mvPolynomial_component_dimensions C (paddingVariables R k d) (dimensionNat R k d) hC p).trans hn'

private theorem smoothLocus_relative_dimension_congr {X Y : Scheme.{u}} (f g : X ⟶ Y)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) (n : ℕ) :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) ↔
      SmoothOfRelativeDimension n (g.smoothLocus.ι ≫ g) := by
  subst h
  rfl

private theorem paddedChart_smoothLocus [CharZero k] [IsReduced R] (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    SmoothOfRelativeDimension (commonDimension R k)
      ((paddedChart R k d a ≫ (paddedPiece R k d ↘ Spec (.of k))).smoothLocus.ι ≫
        (paddedChart R k d a ≫ (paddedPiece R k d ↘ Spec (.of k)))) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let C := affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val
  have : IsReduced C := (dimension_group_chart_equidimensional R k d a).1
  have : Algebra.FiniteType R C :=
    affineBlowUpAlgebra_finiteType R _ (IsNoetherian.noetherian _) a.val
  have : Algebra.FiniteType k C :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) inferInstance
  have h := affine_smoothLocus_of_component_dimensions
    (MvPolynomial (paddingVariables R k d) C) k (commonDimension R k) (paddedChart_components R k d a)
  exact (smoothLocus_relative_dimension_congr _ _ (paddedChart_comp_structure R k d a)
    (commonDimension R k)).mpr h

theorem paddedPiece_isReducedEquidimensional [CharZero k] [IsReduced R] (d : dimensionIndex R) :
    (paddedPiece R k d).IsReducedEquidimensional k := by
  apply Scheme.IsReducedEquidimensional.of_openCover (paddedAffineOpenCover R k d).openCover
    (commonDimension R k)
  · intro a
    have := (dimension_group_chart_equidimensional R k d a).1
    change IsReduced (Spec (.of (MvPolynomial (paddingVariables R k d)
      (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))))
    infer_instance
  · exact paddedChart_smoothLocus R k d

private instance rawEnvelope_over : (rawEnvelope R k).Over (Spec (.of k)) :=
  ⟨rawProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R))⟩

private instance rawEnvelope_finiteType [IsReduced R] :
    FiniteType (rawEnvelope R k ↘ Spec (.of k)) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : IsAffineHom (rawProjection R k) := rawProjection_isAffineHom R k
  have : Smooth (rawProjection R k) := rawProjection_smooth R k
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  change FiniteType (rawProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)))
  infer_instance

private instance rawEnvelope_isSeparated [IsReduced R] :
    IsSeparated (rawEnvelope R k ↘ Spec (.of k)) := by
  have : IsAffineHom (rawProjection R k) := rawProjection_isAffineHom R k
  have : IsSeparated (rawProjection R k) := IsSeparated.of_isAffineHom _
  change IsSeparated (rawProjection R k ≫ affineBlowUp.π (dimensionSeparationIdeal R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)))
  infer_instance

private theorem rawEnvelope_summand_structure (d : dimensionIndex R) :
    Sigma.ι (paddedPiece R k) d ≫ (rawEnvelope R k ↘ Spec (.of k)) =
      paddedPiece R k d ↘ Spec (.of k) := by
  change Sigma.ι (paddedPiece R k) d ≫ (rawProjection R k ≫
    affineBlowUp.π (dimensionSeparationIdeal R) ≫ _) =
      paddedProjection R k d ≫ (pieceAlgScheme R k d).hom
  rw [← Category.assoc,rawProjection,Sigma.ι_desc,Category.assoc]
  rfl

private def rawEnvelopeOpenCover : (rawEnvelope R k).OpenCover :=
  (sigmaOpenCover (paddedPiece R k)).bind fun d => (paddedAffineOpenCover R k d).openCover

private theorem rawEnvelope_isReducedEquidimensional [CharZero k] [IsReduced R] :
    (rawEnvelope R k).IsReducedEquidimensional k := by
  apply Scheme.IsReducedEquidimensional.of_openCover (rawEnvelopeOpenCover R k) (commonDimension R k)
  · change ∀ i : (Σ d : dimensionIndex R, complementIdeal R (dimensionGroupIdeal R) d),
      IsReduced (Spec (.of (MvPolynomial (paddingVariables R k i.1)
        (affineBlowUpAlgebra (dimensionSeparationIdeal R) i.2.val))))
    intro i
    have := (dimension_group_chart_equidimensional R k i.1 i.2).1
    infer_instance
  · change ∀ i : (Σ d : dimensionIndex R, complementIdeal R (dimensionGroupIdeal R) d),
      SmoothOfRelativeDimension (commonDimension R k)
        ((((paddedChart R k i.1 i.2 ≫ Sigma.ι (paddedPiece R k) i.1) ≫
          (rawEnvelope R k ↘ Spec (.of k))).smoothLocus.ι) ≫
          ((paddedChart R k i.1 i.2 ≫ Sigma.ι (paddedPiece R k) i.1) ≫
            (rawEnvelope R k ↘ Spec (.of k))))
    intro i
    have h : (paddedChart R k i.1 i.2 ≫ Sigma.ι (paddedPiece R k) i.1) ≫
        (rawEnvelope R k ↘ Spec (.of k)) =
          paddedChart R k i.1 i.2 ≫ (paddedPiece R k i.1 ↘ Spec (.of k)) := by
      rw [Category.assoc,rawEnvelope_summand_structure]
    exact (smoothLocus_relative_dimension_congr _ _ h (commonDimension R k)).mpr
      (paddedChart_smoothLocus R k i.1 i.2)

/-- ONE actual native object, the literal finite coproduct of all actual padded pieces. -/
abbrev paddedEnvelope [CharZero k] [IsReduced R] : ReducedEquidimensionalScheme k :=
  ⟨AlgScheme.of (k := k) (rawEnvelope R k),rawEnvelope_isReducedEquidimensional R k⟩

/-- The SINGLE actual projection onto the SAME original separation blowup. -/
def envelopeProjection [CharZero k] [IsReduced R] :
    (paddedEnvelope R k).obj.left ⟶ affineBlowUp (dimensionSeparationIdeal R) := rawProjection R k

theorem envelopeProjection_smooth [CharZero k] [IsReduced R] : Smooth (envelopeProjection R k) :=
  rawProjection_smooth R k

theorem envelopeProjection_isAffineHom [CharZero k] [IsReduced R] : IsAffineHom (envelopeProjection R k) :=
  rawProjection_isAffineHom R k

/-- The literal original-piece square of the SAME global map is an actual pullback. -/
theorem envelopeProjection_isPullback_piece [CharZero k] [IsReduced R] (d : dimensionIndex R) :
    IsPullback (paddedProjection R k d) (Sigma.ι (paddedPiece R k) d)
      (dimensionPartOpen R d).ι (envelopeProjection R k) := by
  change IsPullback (paddedProjection R k d) (Sigma.ι (paddedPiece R k) d)
    (dimensionPartOpen R d).ι (rawProjection R k)
  exact IsOpenImmersion.isPullback _ _ _ _ (Sigma.ι_desc _ _)
    (by simpa only [Scheme.Opens.opensRange_ι] using rawProjection_preimage_piece R k d)

def envelopeZeroSection [CharZero k] [IsReduced R] :
    affineBlowUp (dimensionSeparationIdeal R) ⟶ (paddedEnvelope R k).obj.left := rawZeroSection R k

theorem envelopeZeroSection_projection [CharZero k] [IsReduced R] :
    envelopeZeroSection R k ≫ envelopeProjection R k = 𝟙 _ := rawZeroSection_projection R k

theorem envelopeProjection_surjective [CharZero k] [IsReduced R] :
    Function.Surjective (envelopeProjection R k) := by
  intro x
  exact ⟨envelopeZeroSection R k x,
    congrArg (fun f => f x) (envelopeZeroSection_projection R k)⟩

instance envelopeProjection_surjective_native [CharZero k] [IsReduced R] :
    Surjective (envelopeProjection R k) := ⟨envelopeProjection_surjective R k⟩

end
end Hironaka.Resolution.Algebraic.ActualDimensionGroupPaddedCover
