import Hironaka.Resolution.Algebraic.ActualGlobalDimensionPieceAffineCover
import Hironaka.Algebra.FiniteTypeFieldPoint

/-!
# Genuine purity of the actual global dimension pieces

Source-first proof: `actual-global-dimension-piece-purity-20261102.tex`.
The original actual chart rings/coefficient maps and one intrinsic dimension
per global piece derive native purity.  One common global padded input and
its native history remain separate consumers; no piece histories are run.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalDimensionPiecePurity

noncomputable section
open ActualIntrinsicComponentDimensions ActualGlobalDimensionPieceAffineCover

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] in
include p in
private theorem dimension_exists_nat (d : dimensionIndex X) :
    ∃ n : ℕ, (n : WithBot ℕ∞) = d.val := by
  obtain ⟨C, hC⟩ := d.property
  obtain ⟨n, hn⟩ := componentDimension_nat p C
  exact ⟨n, hn.symm.trans hC⟩

def dimensionNat (d : dimensionIndex X) : ℕ := Nat.find (dimension_exists_nat p d)

omit [AlgebraicGeometry.IsNoetherian X] [IsReduced X] in
theorem dimensionNat_spec (d : dimensionIndex X) :
    (dimensionNat p d : WithBot ℕ∞) = d.val := Nat.find_spec (dimension_exists_nat p d)

def pieceStructure (d : dimensionIndex X) :
    (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme ⟶ Spec (.of k) :=
  (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι ≫
    ActualGlobalDimensionClopenPartition.separationProjection X ≫ p

instance pieceStructure_finiteType (d : dimensionIndex X) : FiniteType (pieceStructure p d) := by
  have : IsProper (ActualGlobalDimensionClopenPartition.separationProjection X) :=
    ActualGlobalSeparationAffineCharts.separationProjection_isProper (X := X)
  have : IsLocallyNoetherian (ActualGlobalDimensionClopenPartition.separationSpace X) :=
    LocallyOfFiniteType.isLocallyNoetherian (ActualGlobalDimensionClopenPartition.separationProjection X)
  have : CompactSpace (ActualGlobalDimensionClopenPartition.separationSpace X) :=
    QuasiCompact.compactSpace_of_compactSpace (ActualGlobalDimensionClopenPartition.separationProjection X)
  have : IsNoetherian (ActualGlobalDimensionClopenPartition.separationSpace X) := ⟨⟩
  dsimp [pieceStructure]
  infer_instance

instance pieceStructure_isSeparated [IsSeparated p] (d : dimensionIndex X) :
    IsSeparated (pieceStructure p d) := by
  have : IsProper (ActualGlobalDimensionClopenPartition.separationProjection X) :=
    ActualGlobalSeparationAffineCharts.separationProjection_isProper (X := X)
  dsimp [pieceStructure]
  infer_instance

private abbrev affineAlgebra (U : X.affineOpens) : Algebra k Γ(X, U) :=
  (Hironaka.Algebra.FiniteTypePoint.affineBaseMap p U.2).toAlgebra

abbrev chartAlgebra (d : dimensionIndex X) (i : affineChartIndex d) :
    Algebra k (affineChartRing d i) :=
  ((algebraMap Γ(X, i.1) (affineChartRing d i)).comp
    (Hironaka.Algebra.FiniteTypePoint.affineBaseMap p i.1.2)).toAlgebra

omit [IsReduced X] in
theorem chartAlgebra_finiteType (d : dimensionIndex X) (i : affineChartIndex d) :
    letI := chartAlgebra p d i
    Algebra.FiniteType k (affineChartRing d i) := by
  rcases i with ⟨U, ⟨e, he⟩, a⟩
  let := affineAlgebra p U
  let := chartAlgebra p d ⟨U, ⟨e, he⟩, a⟩
  have : Algebra.FiniteType k Γ(X, U) := RingHom.finiteType_algebraMap.mp
    (Hironaka.Algebra.FiniteTypePoint.affineBaseMap_finiteType p U.2)
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have : Algebra.FiniteType Γ(X, U) (affineChartRing d ⟨U, ⟨e, he⟩, a⟩) :=
    ActualDimensionGroupChartDimension.affineBlowUpAlgebra_finiteType Γ(X, U)
      (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)) (IsNoetherian.noetherian _) a.val
  have : IsScalarTower k Γ(X, U) (affineChartRing d ⟨U, ⟨e, he⟩, a⟩) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k Γ(X, U)) inferInstance

private theorem spectrumMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]
  rfl

theorem affineChart_coefficient (d : dimensionIndex X) (i : affineChartIndex d) :
    letI := chartAlgebra p d i
    affineChart p d i ≫ pieceStructure p d =
      Spec.map (CommRingCat.ofHom (algebraMap k (affineChartRing d i))) := by
  let := chartAlgebra p d i
  have hfirst := congrArg (fun f => f ≫ p) (affineChart_original p d i)
  simp only [Category.assoc] at hfirst
  have hcoefficient := congrArg (fun f =>
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, i.1) (affineChartRing d i))) ≫ f)
    (Hironaka.Algebra.FiniteTypePoint.affineBaseMap_spec p i.1.2).symm
  have hlast :
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, i.1) (affineChartRing d i))) ≫
        Spec.map (CommRingCat.ofHom (Hironaka.Algebra.FiniteTypePoint.affineBaseMap p i.1.2)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (affineChartRing d i))) := by
    exact spectrumMap_comp (Hironaka.Algebra.FiniteTypePoint.affineBaseMap p i.1.2)
      (algebraMap Γ(X, i.1) (affineChartRing d i))
  simpa only [pieceStructure, Category.assoc] using hfirst.trans (hcoefficient.trans hlast)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem affineChart_reduced_and_dimensions (d : dimensionIndex X) (i : affineChartIndex d) :
    _root_.IsReduced (affineChartRing d i) ∧
      ∀ q : minimalPrimes (affineChartRing d i),
        ringKrullDim ((affineChartRing d i) ⧸ q.val) = dimensionNat p d := by
  rcases i with ⟨U, ⟨e, he⟩, a⟩
  let := affineAlgebra p U
  have : Algebra.FiniteType k Γ(X, U) := RingHom.finiteType_algebraMap.mp
    (Hironaka.Algebra.FiniteTypePoint.affineBaseMap_finiteType p U.2)
  have hdata := ActualDimensionGroupChartDimension.dimension_group_chart_equidimensional Γ(X, U) k e a
  exact ⟨hdata.1, fun q => (hdata.2 q).trans (he.trans (dimensionNat_spec p d).symm)⟩

private theorem smoothLocus_relative_dimension_congr {A B : Scheme.{u}} (f g : A ⟶ B)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) (n : ℕ) :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) ↔
      SmoothOfRelativeDimension n (g.smoothLocus.ι ≫ g) := by
  subst h
  rfl

theorem piece_isReducedEquidimensional [CharZero k] (d : dimensionIndex X) :
    letI : (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme.Over (Spec (.of k)) :=
      ⟨pieceStructure p d⟩
    letI : LocallyOfFiniteType
        ((ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme ↘ Spec (.of k)) := by
      change LocallyOfFiniteType (pieceStructure p d)
      infer_instance
    (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme.IsReducedEquidimensional k := by
  let : (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme.Over (Spec (.of k)) :=
    ⟨pieceStructure p d⟩
  have : LocallyOfFiniteType
      ((ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pieceStructure p d)
    infer_instance
  apply Scheme.IsReducedEquidimensional.of_openCover (affineOpenCover p d).openCover (dimensionNat p d)
  · intro i
    have := (affineChart_reduced_and_dimensions p d i).1
    exact inferInstanceAs (IsReduced (Spec (.of (affineChartRing d i))))
  · intro i
    let := chartAlgebra p d i
    have : Algebra.FiniteType k (affineChartRing d i) := chartAlgebra_finiteType p d i
    have : _root_.IsReduced (affineChartRing d i) := (affineChart_reduced_and_dimensions p d i).1
    have h := ActualDimensionGroupEquidimensionalPieces.affine_smoothLocus_of_component_dimensions
      (affineChartRing d i) k (dimensionNat p d) (affineChart_reduced_and_dimensions p d i).2
    exact (smoothLocus_relative_dimension_congr _ _ (affineChart_coefficient p d i)
      (dimensionNat p d)).mpr h

def pieceAlgScheme [IsSeparated p] (d : dimensionIndex X) : AlgScheme k := by
  letI : (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme.Over (Spec (.of k)) :=
    ⟨pieceStructure p d⟩
  have : FiniteType ((ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme ↘ Spec (.of k)) := by
    change FiniteType (pieceStructure p d)
    infer_instance
  have : IsSeparated ((ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme ↘ Spec (.of k)) := by
    change IsSeparated (pieceStructure p d)
    infer_instance
  exact AlgScheme.of (k := k) (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme

omit [IsReduced X] in
theorem pieceAlgScheme_structure [IsSeparated p] (d : dimensionIndex X) :
    (pieceAlgScheme p d).hom = pieceStructure p d := rfl

def pieceReducedEquidimensionalScheme [CharZero k] [IsSeparated p] (d : dimensionIndex X) :
    ReducedEquidimensionalScheme k :=
  ⟨pieceAlgScheme p d, piece_isReducedEquidimensional p d⟩

end
end Hironaka.Resolution.Algebraic.ActualGlobalDimensionPiecePurity
