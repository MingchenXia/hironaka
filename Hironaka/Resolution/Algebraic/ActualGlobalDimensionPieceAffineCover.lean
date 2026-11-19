import Hironaka.Resolution.Algebraic.ActualAffineNormalizedDimensionOpens
import Hironaka.Resolution.Algebraic.ActualDimensionGroupEquidimensionalPieces

/-!
# A genuine affine cover of each actual global dimension piece

Source-first proof: `actual-global-dimension-piece-affine-cover-20261102.tex`.
The actual native group pieces and original degree-one chart rings produce
an actual affine cover with the original coefficient projection.  Global
purity and the actual padded envelope remain separate consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalDimensionPieceAffineCover

noncomputable section

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (d : ActualIntrinsicComponentDimensions.dimensionIndex X)

private theorem pieceMap_range (U : X.affineOpens)
    (e : ActualDimensionGroupBlowup.dimensionIndex Γ(X, U)) (he : e.val = d.val) :
    Set.range ((ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).ι ≫
      ActualGlobalSeparationAffineCharts.chartMap p U) ⊆
      Set.range (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι := by
  rintro _ ⟨a, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hmem : (ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).ι a ∈
      ActualGlobalSeparationAffineCharts.chartMap p U ⁻¹ᵁ
        ActualGlobalDimensionClopenPartition.dimensionPartOpen X d := by
    rw [ActualAffineNormalizedDimensionOpens.globalPartOpen_chart p U d e he]
    exact a.property
  exact hmem

def pieceMap (U : X.affineOpens)
    (e : ActualDimensionGroupBlowup.dimensionIndex Γ(X, U)) (he : e.val = d.val) :
    (ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).toScheme ⟶
      (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme :=
  IsOpenImmersion.lift (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι
    ((ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).ι ≫
      ActualGlobalSeparationAffineCharts.chartMap p U) (pieceMap_range p d U e he)

theorem pieceMap_over (U : X.affineOpens)
    (e : ActualDimensionGroupBlowup.dimensionIndex Γ(X, U)) (he : e.val = d.val) :
    pieceMap p d U e he ≫ (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι =
      (ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).ι ≫
        ActualGlobalSeparationAffineCharts.chartMap p U :=
  IsOpenImmersion.lift_fac _ _ _

instance pieceMap_isOpenImmersion (U : X.affineOpens)
    (e : ActualDimensionGroupBlowup.dimensionIndex Γ(X, U)) (he : e.val = d.val) :
    IsOpenImmersion (pieceMap p d U e he) := by
  have : IsOpenImmersion (pieceMap p d U e he ≫
      (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι) := by
    rw [pieceMap_over]
    infer_instance
  exact IsOpenImmersion.of_comp _ (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι

def affineChartIndex : Type u :=
  Σ U : X.affineOpens,
    Σ e : {e : ActualDimensionGroupBlowup.dimensionIndex Γ(X, U) // e.val = d.val},
      ActualDimensionGroupBlowup.complementIdeal Γ(X, U)
        (ActualDimensionGroupBlowup.dimensionGroupIdeal Γ(X, U)) e.val

abbrev affineChartRing (i : affineChartIndex d) : Type u :=
  affineBlowUpAlgebra (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, i.1)) i.2.2.val

def affineChart (i : affineChartIndex d) : Spec (.of (affineChartRing d i)) ⟶
    (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme :=
  ActualDimensionGroupEquidimensionalPieces.pieceChart Γ(X, i.1) i.2.1.val i.2.2 ≫
    pieceMap p d i.1 i.2.1.val i.2.1.property

instance affineChart_isOpenImmersion (i : affineChartIndex d) : IsOpenImmersion (affineChart p d i) := by
  dsimp [affineChart]
  infer_instance

private theorem pieceChart_original (U : X.affineOpens)
    (e : ActualDimensionGroupBlowup.dimensionIndex Γ(X, U)) (he : e.val = d.val)
    (a : ActualDimensionGroupBlowup.complementIdeal Γ(X, U)
      (ActualDimensionGroupBlowup.dimensionGroupIdeal Γ(X, U)) e) :
    (ActualDimensionGroupEquidimensionalPieces.pieceChart Γ(X, U) e a ≫ pieceMap p d U e he) ≫
      (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι ≫
        ActualGlobalDimensionClopenPartition.separationProjection X =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (affineBlowUpAlgebra (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)) a.val))) ≫
          U.2.fromSpec := by
  have hproj : ActualDimensionGroupEquidimensionalPieces.pieceChart Γ(X, U) e a ≫
      (ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).ι ≫
        affineBlowUp.π (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (affineBlowUpAlgebra (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)) a.val))) := by
    rw [← Category.assoc, ActualDimensionGroupEquidimensionalPieces.pieceChart_comp_inclusion,
      affineBlowUp.chart_π]
    rfl
  have hfirst := congrArg (fun f =>
    ActualDimensionGroupEquidimensionalPieces.pieceChart Γ(X, U) e a ≫ f ≫
      ActualGlobalDimensionClopenPartition.separationProjection X) (pieceMap_over p d U e he)
  have hsecond := congrArg (fun f =>
    (ActualDimensionGroupEquidimensionalPieces.pieceChart Γ(X, U) e a ≫
      (ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).ι) ≫ f)
        (ActualGlobalSeparationAffineCharts.chartMap_isPullback p U).w
  have hlast := congrArg (fun f => f ≫ U.2.fromSpec) hproj
  simp only [Category.assoc] at hfirst hsecond hlast ⊢
  exact hfirst.trans (hsecond.trans hlast)

theorem affineChart_original (i : affineChartIndex d) :
    affineChart p d i ≫ (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι ≫
      ActualGlobalDimensionClopenPartition.separationProjection X =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, i.1) (affineChartRing d i))) ≫ i.1.2.fromSpec := by
  rcases i with ⟨U, ⟨e, he⟩, a⟩
  exact pieceChart_original p d U e he a

theorem affineChart_covers (b : (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme) :
    ∃ i : affineChartIndex d, b ∈ (affineChart p d i).opensRange := by
  have hcov : b.val ∈ (⨆ U : X.affineOpens,
      (ActualGlobalSeparationAffineCharts.chartMap p U).opensRange) := by
    rw [ActualGlobalSeparationAffineCharts.chartMap_cover]
    trivial
  obtain ⟨U, c, hc⟩ := Opens.mem_iSup.mp hcov
  have hlocal : c ∈ ActualGlobalSeparationAffineCharts.chartMap p U ⁻¹ᵁ
      ActualGlobalDimensionClopenPartition.dimensionPartOpen X d := by
    change ActualGlobalSeparationAffineCharts.chartMap p U c ∈
      ActualGlobalDimensionClopenPartition.dimensionPartOpen X d
    rw [hc]
    exact b.property
  have hdlocal : d.val ∈ Set.range (ActualDimensionGroupBlowup.componentDimension Γ(X, U)) := by
    by_contra hd
    rw [ActualAffineNormalizedDimensionOpens.globalPartOpen_chart_absent p U d hd] at hlocal
    exact hlocal
  let e : ActualDimensionGroupBlowup.dimensionIndex Γ(X, U) := ⟨d.val, hdlocal⟩
  rw [ActualAffineNormalizedDimensionOpens.globalPartOpen_chart p U d e rfl] at hlocal
  let c' : (ActualDimensionGroupBlowup.dimensionPartOpen Γ(X, U) e).toScheme := ⟨c, hlocal⟩
  have hpc : pieceMap p d U e rfl c' = b := by
    apply (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f c') (pieceMap_over p d U e rfl)).trans hc
  obtain ⟨a, z, hz⟩ :=
    (ActualDimensionGroupEquidimensionalPieces.pieceAffineOpenCover Γ(X, U) e).openCover.exists_eq c'
  change ActualDimensionGroupEquidimensionalPieces.pieceChart Γ(X, U) e a z = c' at hz
  refine ⟨⟨U, ⟨e, rfl⟩, a⟩, z, ?_⟩
  change pieceMap p d U e rfl (ActualDimensionGroupEquidimensionalPieces.pieceChart Γ(X, U) e a z) = b
  rw [hz, hpc]

def affineOpenCover :
    (ActualGlobalDimensionClopenPartition.dimensionPartOpen X d).toScheme.AffineOpenCover where
  I₀ := affineChartIndex d
  X i := .of (affineChartRing d i)
  f i := affineChart p d i
  idx b := (affineChart_covers p d b).choose
  covers b := (affineChart_covers p d b).choose_spec

end
end Hironaka.Resolution.Algebraic.ActualGlobalDimensionPieceAffineCover
