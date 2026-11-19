import Hironaka.Resolution.Algebraic.ActualGlobalVariablePaddingGeometry
import Hironaka.Resolution.Algebraic.ActualDimensionGroupPaddedCover

/-!
# One genuine global reduced-equidimensional padded native input

Source-first proof: `actual-global-padded-native-input-20261102.tex`.
Actual original polynomial charts and numerical ranks derive ONE whole
constant-dimensional native input, with the genuine split smooth affine
surjective map.  No piece native families or clocks are chosen.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalPaddedNativeInput

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPiecePurity
  ActualGlobalDimensionPieceAffineCover ActualGlobalVariablePaddingGeometry

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (V : dimensionIndex X → Type u)

def paddedPieceStructure (d : dimensionIndex X) : piece X V d ⟶ Spec (.of k) :=
  pieceProjection X V d ≫ pieceStructure p d

def envelopeStructure : envelope X V ⟶ Spec (.of k) :=
  projection X V ≫ ActualGlobalDimensionClopenPartition.separationProjection X ≫ p

instance paddedPieceStructure_finiteType [∀ d, Finite (V d)] (d : dimensionIndex X) :
    FiniteType (paddedPieceStructure p V d) := by
  dsimp [paddedPieceStructure]
  infer_instance

instance paddedPieceStructure_isSeparated [IsSeparated p] (d : dimensionIndex X) :
    IsSeparated (paddedPieceStructure p V d) := by
  dsimp [paddedPieceStructure]
  infer_instance

instance envelopeStructure_finiteType [∀ d, Finite (V d)] : FiniteType (envelopeStructure p V) := by
  have : Smooth (projection X V) := projection_smooth X V
  have : IsAffineHom (projection X V) := projection_affine X V
  have : IsProper (ActualGlobalDimensionClopenPartition.separationProjection X) :=
    ActualGlobalSeparationAffineCharts.separationProjection_isProper (X := X)
  dsimp [envelopeStructure]
  infer_instance

instance envelopeStructure_isSeparated [IsSeparated p] : IsSeparated (envelopeStructure p V) := by
  have : IsAffineHom (projection X V) := projection_affine X V
  have : IsProper (ActualGlobalDimensionClopenPartition.separationProjection X) :=
    ActualGlobalSeparationAffineCharts.separationProjection_isProper (X := X)
  dsimp [envelopeStructure]
  infer_instance

omit [IsReduced X] [LocallyOfFiniteType p] in
theorem envelopeStructure_summand (d : dimensionIndex X) :
    Sigma.ι (piece X V) d ≫ envelopeStructure p V = paddedPieceStructure p V d := by
  rw [envelopeStructure, ← Category.assoc, projection, Sigma.ι_desc]
  rfl

def chart (d : dimensionIndex X) (i : affineChartIndex d) :
    Spec (.of (MvPolynomial (V d) (affineChartRing d i))) ⟶ piece X V d :=
  (AffineSpace.SpecIso (V d) (.of (affineChartRing d i))).inv ≫
    AffineSpace.map (V d) (affineChart p d i)

private instance map_chart_isOpenImmersion (d : dimensionIndex X) (i : affineChartIndex d) :
    IsOpenImmersion (AffineSpace.map (V d) (affineChart p d i)) :=
  property_of_isPullback _ (AffineSpace.isPullback_map (n := V d) (affineChart p d i)) inferInstance

private instance chart_isOpenImmersion (d : dimensionIndex X) (i : affineChartIndex d) :
    IsOpenImmersion (chart p V d i) := by
  dsimp [chart]
  infer_instance

private theorem polynomial_chart_range (W : Type u) (C : CommRingCat.{u}) {B : Scheme.{u}}
    (j : Spec C ⟶ B) [IsOpenImmersion j] :
    Set.range ((AffineSpace.SpecIso W C).inv ≫ AffineSpace.map W j) =
      (AffineSpace W B ↘ B) ⁻¹' Set.range j := by
  have : IsOpenImmersion (AffineSpace.map W j) :=
    property_of_isPullback _ (AffineSpace.isPullback_map (n := W) j) inferInstance
  change (((AffineSpace.SpecIso W C).inv ≫ AffineSpace.map W j).opensRange : Set (AffineSpace W B)) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact range_fst_of_isPullback (AffineSpace.isPullback_map (n := W) j)

private theorem chart_range (d : dimensionIndex X) (i : affineChartIndex d) :
    Set.range (chart p V d i) = pieceProjection X V d ⁻¹' Set.range (affineChart p d i) := by
  exact polynomial_chart_range (V d) (.of (affineChartRing d i)) (affineChart p d i)

def affineOpenCover (d : dimensionIndex X) : (piece X V d).AffineOpenCover where
  I₀ := affineChartIndex d
  X i := .of (MvPolynomial (V d) (affineChartRing d i))
  f i := chart p V d i
  idx x := (ActualGlobalDimensionPieceAffineCover.affineOpenCover p d).idx (pieceProjection X V d x)
  covers x := by
    rw [chart_range]
    exact (ActualGlobalDimensionPieceAffineCover.affineOpenCover p d).covers (pieceProjection X V d x)

private theorem chart_comp_projection (d : dimensionIndex X) (i : affineChartIndex d) :
    chart p V d i ≫ pieceProjection X V d =
      Spec.map (CommRingCat.ofHom (algebraMap (affineChartRing d i)
        (MvPolynomial (V d) (affineChartRing d i)))) ≫ affineChart p d i := by
  simp only [chart, pieceProjection, Category.assoc, AffineSpace.map_over,
    AffineSpace.SpecIso_inv_over_assoc, MvPolynomial.algebraMap_eq]

private theorem spectrumMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]
  rfl

theorem chart_comp_structure (d : dimensionIndex X) (i : affineChartIndex d) :
    letI := chartAlgebra p d i
    chart p V d i ≫ paddedPieceStructure p V d =
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (V d) (affineChartRing d i)))) := by
  let := chartAlgebra p d i
  have hfirst := congrArg (fun f => f ≫ pieceStructure p d) (chart_comp_projection p V d i)
  let g : Spec (.of (MvPolynomial (V d) (affineChartRing d i))) ⟶ Spec (.of (affineChartRing d i)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (affineChartRing d i)
      (MvPolynomial (V d) (affineChartRing d i))))
  have hsecond := congrArg (fun f => g ≫ f) (affineChart_coefficient p d i)
  have hlast := spectrumMap_comp (A := k) (B := affineChartRing d i)
    (C := MvPolynomial (V d) (affineChartRing d i)) (algebraMap k (affineChartRing d i))
    (algebraMap (affineChartRing d i) (MvPolynomial (V d) (affineChartRing d i)))
  have hcoeff : (algebraMap (affineChartRing d i) (MvPolynomial (V d) (affineChartRing d i))).comp
      (algebraMap k (affineChartRing d i)) =
      algebraMap k (MvPolynomial (V d) (affineChartRing d i)) :=
    (IsScalarTower.algebraMap_eq k (affineChartRing d i)
      (MvPolynomial (V d) (affineChartRing d i))).symm
  have hlast' := hlast.trans (congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hcoeff)
  simpa only [paddedPieceStructure, Category.assoc] using hfirst.trans (hsecond.trans hlast')

theorem chart_component_dimensions [∀ d, Finite (V d)] (N : ℕ)
    (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)
    (d : dimensionIndex X) (i : affineChartIndex d) :
    let P : Type u := MvPolynomial (V d) (affineChartRing d i)
    letI : CommRing P := inferInstance
    ∀ q : minimalPrimes P, ringKrullDim (P ⧸ q.val) = N := by
  dsimp only
  let := chartAlgebra p d i
  have : Algebra.FiniteType k (affineChartRing d i) := chartAlgebra_finiteType p d i
  have : IsNoetherianRing (affineChartRing d i) := Algebra.FiniteType.isNoetherianRing k _
  have hdim := (affineChart_reduced_and_dimensions p d i).2
  have hn : (dimensionNat p d : WithBot ℕ∞) + Nat.card (V d) = N := by exact_mod_cast hN d
  exact fun q => (ActualDimensionGroupPaddedCover.mvPolynomial_component_dimensions
    (affineChartRing d i) (V d) (dimensionNat p d) hdim q).trans hn

private theorem smoothLocus_dimension_congr {A B : Scheme.{u}} (f g : A ⟶ B)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) (N : ℕ) :
    SmoothOfRelativeDimension N (f.smoothLocus.ι ≫ f) ↔
      SmoothOfRelativeDimension N (g.smoothLocus.ι ≫ g) := by
  subst h
  rfl

private theorem chart_smoothLocus [CharZero k] [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N)
    (d : dimensionIndex X) (i : affineChartIndex d) :
    SmoothOfRelativeDimension N ((chart p V d i ≫ paddedPieceStructure p V d).smoothLocus.ι ≫
      (chart p V d i ≫ paddedPieceStructure p V d)) := by
  let := chartAlgebra p d i
  have : Algebra.FiniteType k (affineChartRing d i) := chartAlgebra_finiteType p d i
  have : _root_.IsReduced (affineChartRing d i) := (affineChart_reduced_and_dimensions p d i).1
  have h := ActualDimensionGroupEquidimensionalPieces.affine_smoothLocus_of_component_dimensions
    (MvPolynomial (V d) (affineChartRing d i)) k N (chart_component_dimensions p V N hN d i)
  exact (smoothLocus_dimension_congr _ _ (chart_comp_structure p V d i) N).mpr h

theorem envelope_isReducedEquidimensional [CharZero k] [∀ d, Finite (V d)]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) :
    letI : (envelope X V).Over (Spec (.of k)) := ⟨envelopeStructure p V⟩
    letI : LocallyOfFiniteType (envelope X V ↘ Spec (.of k)) := by
      change LocallyOfFiniteType (envelopeStructure p V)
      infer_instance
    (envelope X V).IsReducedEquidimensional k := by
  let : (envelope X V).Over (Spec (.of k)) := ⟨envelopeStructure p V⟩
  have : LocallyOfFiniteType (envelope X V ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (envelopeStructure p V)
    infer_instance
  apply Scheme.IsReducedEquidimensional.of_openCover
    ((sigmaOpenCover (piece X V)).bind fun d => (affineOpenCover p V d).openCover) N
  · change ∀ i : (Σ d : dimensionIndex X, affineChartIndex d),
      IsReduced (Spec (.of (MvPolynomial (V i.1) (affineChartRing i.1 i.2))))
    intro i
    have := (affineChart_reduced_and_dimensions p i.1 i.2).1
    infer_instance
  · change ∀ i : (Σ d : dimensionIndex X, affineChartIndex d),
      SmoothOfRelativeDimension N
        ((((chart p V i.1 i.2 ≫ Sigma.ι (piece X V) i.1) ≫ envelopeStructure p V).smoothLocus.ι) ≫
          ((chart p V i.1 i.2 ≫ Sigma.ι (piece X V) i.1) ≫ envelopeStructure p V))
    intro i
    have hwhole : (chart p V i.1 i.2 ≫ Sigma.ι (piece X V) i.1) ≫ envelopeStructure p V =
        chart p V i.1 i.2 ≫ paddedPieceStructure p V i.1 := by
      have hs := congrArg (fun f => chart p V i.1 i.2 ≫ f) (envelopeStructure_summand p V i.1)
      simp only [Category.assoc] at hs ⊢
      exact hs
    exact (smoothLocus_dimension_congr _ _ hwhole N).mpr (chart_smoothLocus p V N hN i.1 i.2)

def envelopeAlgScheme [∀ d, Finite (V d)] [IsSeparated p] : AlgScheme k := by
  letI : (envelope X V).Over (Spec (.of k)) := ⟨envelopeStructure p V⟩
  have : FiniteType (envelope X V ↘ Spec (.of k)) := by
    change FiniteType (envelopeStructure p V)
    infer_instance
  have : IsSeparated (envelope X V ↘ Spec (.of k)) := by
    change IsSeparated (envelopeStructure p V)
    infer_instance
  exact AlgScheme.of (k := k) (envelope X V)

def variableEnvelope [CharZero k] [∀ d, Finite (V d)] [IsSeparated p]
    (N : ℕ) (hN : ∀ d, dimensionNat p d + Nat.card (V d) = N) : ReducedEquidimensionalScheme k :=
  ⟨envelopeAlgScheme p V, envelope_isReducedEquidimensional p V N hN⟩

private instance dimensionIndex_finite : Finite (dimensionIndex X) :=
  ActualIntrinsicComponentDimensions.dimensionIndex_finite X

def commonDimension : ℕ := by
  let : Fintype (dimensionIndex X) := Fintype.ofFinite _
  exact Finset.univ.sup (dimensionNat p)

omit [IsReduced X] in
theorem commonDimension_ge (d : dimensionIndex X) : dimensionNat p d ≤ commonDimension p := by
  classical
  let : Fintype (dimensionIndex X) := Fintype.ofFinite _
  change dimensionNat p d ≤ Finset.univ.sup (dimensionNat p)
  exact Finset.le_sup (Finset.mem_univ d)

abbrev paddingVariables (d : dimensionIndex X) : Type u :=
  ULift.{u} (Fin (commonDimension p - dimensionNat p d))

omit [IsReduced X] in
theorem padding_rank (d : dimensionIndex X) :
    dimensionNat p d + Nat.card (paddingVariables p d) = commonDimension p := by
  simp only [paddingVariables, Nat.card_ulift, Nat.card_fin]
  exact Nat.add_sub_of_le (commonDimension_ge p d)

abbrev paddedEnvelope [CharZero k] [IsSeparated p] : ReducedEquidimensionalScheme k :=
  variableEnvelope p (paddingVariables p) (commonDimension p) (padding_rank p)

def envelopeProjection [CharZero k] [IsSeparated p] :
    (paddedEnvelope p).obj.left ⟶ ActualGlobalDimensionClopenPartition.separationSpace X :=
  projection X (paddingVariables p)

theorem envelopeProjection_smooth [CharZero k] [IsSeparated p] : Smooth (envelopeProjection p) :=
  projection_smooth X (paddingVariables p)

theorem envelopeProjection_affine [CharZero k] [IsSeparated p] : IsAffineHom (envelopeProjection p) :=
  projection_affine X (paddingVariables p)

theorem envelopeProjection_surjective [CharZero k] [IsSeparated p] : Surjective (envelopeProjection p) :=
  projection_surjective X (paddingVariables p)

def envelopeZeroSection [CharZero k] [IsSeparated p] :
    ActualGlobalDimensionClopenPartition.separationSpace X ⟶ (paddedEnvelope p).obj.left :=
  zeroSection X (paddingVariables p)

theorem envelopeZeroSection_projection [CharZero k] [IsSeparated p] :
    envelopeZeroSection p ≫ envelopeProjection p = 𝟙 _ :=
  zeroSection_projection X (paddingVariables p)

end
end Hironaka.Resolution.Algebraic.ActualGlobalPaddedNativeInput
