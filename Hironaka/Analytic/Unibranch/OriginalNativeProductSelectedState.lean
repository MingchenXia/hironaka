import Hironaka.Analytic.Unibranch.OriginalNativeProductIndependentRecord

/-! The genuine independently selected native state on an honest original
product open. The overlap is derived by the ordinary-input producer, and
the full native square/whole record are retained. Blueprint FIRST:
original-native-product-selected-state.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProductSelectedState
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces HironakaG11PresLineState HironakaBaseChange
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  InvDomainTowerAlong SourceReducedComplexSpace OriginalNativeProductWindow
  OriginalNativeSmoothProductEmbedding OriginalNativeProductIndependentRecord
  HironakaG11VanishingWindows MaxLocusLocal HironakaSubmersionActualProductWindow
open scoped ProductComplexManifold

private theorem cast_diffeomorph_value {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (A : Opens (ComplexModel n)) {U V : Opens M} (h : U = V)
    (D : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (a : A) :
    (Eq.mp (congrArg (fun O : Opens M =>
      A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ O) h) D a).val = (D a).val := by
  cases h
  rfl

variable {X Y : SourceReducedComplexSpace}

namespace ProductRecordModel

variable {e : LocalEmbedding Y} {r : ℕ} {W : Opens (productAmbient e r)}
  {i : windowSpace e r W ⟶ X} {hi : LocallyRingedSpace.IsOpenImmersion i.hom.left}
  {z : (windowSpace e r W).obj.left} {d : DimEmbedding X (e.dim+r)} {c : d.carrier}

def rawOpen (M : ProductRecordModel e r W i hi z d c) : Opens (productAmbient e r) :=
  productWindow M.sourceOpen e.ambient

theorem rawOpen_subset (M : ProductRecordModel e r W i hi z d c) : rawOpen M ≤ W := by
  intro p hp
  have h : p ∈ productWindow (coordinateWindow e r W) e.ambient := M.source_subset hp
  exact productWindow_eq e r W ▸ h

def rawDiffeomorph (M : ProductRecordModel e r W i hi z d c) :
    M.sourceOpen ≃ₘ⟮𝓘(ℂ,ComplexModel (e.dim+r)),𝓘(ℂ,ComplexModel (e.dim+r))⟯ rawOpen M :=
  splitWindowDiffeomorph M.sourceOpen e.ambient
    (fun q hq => coordinateWindow_first e r W q (M.source_subset hq))

theorem coordinate_square (M : ProductRecordModel e r W i hi z d c) (a : M.sourceOpen) :
    (coordinateDiffeomorph e r W (Opens.inclusion M.source_subset a)).val =
      (rawDiffeomorph M a).val := by
  have h := cast_diffeomorph_value (coordinateWindow e r W) (productWindow_eq e r W)
    (splitWindowDiffeomorph (coordinateWindow e r W) e.ambient (coordinateWindow_first e r W))
    (Opens.inclusion M.source_subset a)
  exact h.trans (Prod.ext (Subtype.ext rfl) rfl)

theorem rawCarrier_eq (M : ProductRecordModel e r W i hi z d c) :
    (rawDiffeomorph M).symm ⁻¹' M.sourceCarrier = windowCarrier e r (rawOpen M) := by
  ext p
  have he := (coordinate_square M ((rawDiffeomorph M).symm p)).trans
    (congrArg Subtype.val ((rawDiffeomorph M).apply_symm_apply p))
  change ((coordinateDiffeomorph e r W
    (Opens.inclusion M.source_subset ((rawDiffeomorph M).symm p))).val.1 ∈ e.carrier) ↔
      p.val.1 ∈ e.carrier
  rw [he]

def rawToCanonical (M : ProductRecordModel e r W i hi z d c) :
    windowSpace e r (rawOpen M) ≅
      chartSpace ((productEmbedding e r W i hi).restrict M.sourceOpen M.source_subset) :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk
      (actualSubspaceBiholomorphicIso (rawDiffeomorph M).symm
        (windowCarrier e r (rawOpen M)) M.sourceCarrier
        (fun p => (Set.ext_iff.mp (rawCarrier_eq M) p).symm))
      (actualSubspaceMap_point (rawDiffeomorph M).symm.contMDiff
        (fun p hp => (Set.ext_iff.mp (rawCarrier_eq M) p).mpr hp)))

def rawIso (M : ProductRecordModel e r W i hi z d c) :
    windowSpace e r (rawOpen M) ≅ chartSpace (d.toLocalEmbedding.restrict M.targetOpen M.target_subset) :=
  rawToCanonical M ≪≫ M.nativeIso

theorem raw_native_square (M : ProductRecordModel e r W i hi z d c) :
    (rawIso M).hom ≫ chartInclusion (d.toLocalEmbedding.restrict M.targetOpen M.target_subset) =
      refinement e r (rawOpen_subset M) ≫ i := by
  calc
    _ = (rawToCanonical M).hom ≫
        (M.nativeIso.hom ≫ chartInclusion (d.toLocalEmbedding.restrict M.targetOpen M.target_subset)) :=
      Category.assoc _ _ _
    _ = (rawToCanonical M).hom ≫
        chartInclusion ((productEmbedding e r W i hi).restrict M.sourceOpen M.source_subset) :=
      congrArg (fun a => (rawToCanonical M).hom ≫ a) M.native_square
    _ = _ := by
      apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
      intro p
      apply congrArg i.hom.left.base
      apply Subtype.ext
      apply Subtype.ext
      exact (coordinate_square M ((rawDiffeomorph M).symm p.val)).trans
        (congrArg Subtype.val ((rawDiffeomorph M).apply_symm_apply p.val))

def rawPoint (M : ProductRecordModel e r W i hi z d c) : (windowSpace e r (rawOpen M)).obj.left :=
  (rawToCanonical M).inv.hom.left.base
    ⟨⟨((coordinateIso e r W).inv.hom.left.base z).val.val,M.point_mem⟩,
      ((coordinateIso e r W).inv.hom.left.base z).property⟩

theorem rawPoint_refinement (M : ProductRecordModel e r W i hi z d c) :
    (refinement e r (rawOpen_subset M)).hom.left.base (rawPoint M) = z := by
  let cp := (coordinateIso e r W).inv.hom.left.base z
  let a : M.sourceOpen := ⟨cp.val.val,M.point_mem⟩
  have hWhole := congrArg (fun q => q.hom.left.base z) (coordinateIso e r W).inv_hom_id
  apply Subtype.ext
  apply Subtype.ext
  exact (coordinate_square M a).symm.trans
    (congrArg (fun q : (windowSpace e r W).obj.left => q.val.val) hWhole)

def rawAmbientMap (M : ProductRecordModel e r W i hi z d c) : rawOpen M → d.ambient :=
  fun p => Opens.inclusion M.target_subset (M.phi ((rawDiffeomorph M).symm p))

theorem rawAmbient_open (M : ProductRecordModel e r W i hi z d c) :
    IsOpenHoloEmbedding (e.dim+r) (rawAmbientMap M) :=
  ⟨nestedOpens d.ambient M.targetOpen,
    (rawDiffeomorph M).symm.trans (M.phi.trans (nestedOpensDiffeo (n := e.dim+r) M.target_subset).symm),
    fun _ => rfl⟩

def rawRecord (M : ProductRecordModel e r W i hi z d c)
    (Q : MarkedIdeal (e.dim+r) (BlowupTowers.CMfd.of (n := e.dim+r) d.ambient)) :
    MarkedIdeal (e.dim+r) (BlowupTowers.CMfd.of (n := e.dim+r) (rawOpen M)) :=
  MarkedIdeal.pullback (rawDiffeomorph M).symm (M.record Q)

theorem rawRecord_eq (M : ProductRecordModel e r W i hi z d c)
    (Q : MarkedIdeal (e.dim+r) (BlowupTowers.CMfd.of (n := e.dim+r) d.ambient))
    (hQ : Q.ideal.IsCoherent) :
    rawRecord M Q = MarkedIdeal.pullback (rawAmbientMap M) Q := by
  have hIncl : ContMDiff 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel (e.dim+r)) ∞
      (Opens.inclusion M.target_subset) := contMDiff_inclusion _
  have h1 := HironakaSmoothSubmersionOrderedChoiceImageTrace.whole_markedPullback_comp
    M.phi.contMDiff (rawDiffeomorph M).symm.contMDiff
    (MarkedIdeal.pullback (Opens.inclusion M.target_subset) Q)
    (GermIdealPullbackCalculus.isCoherent_pullback hIncl hQ)
  have h2 := HironakaSmoothSubmersionOrderedChoiceImageTrace.whole_markedPullback_comp
    hIncl (M.phi.contMDiff.comp (rawDiffeomorph M).symm.contMDiff) Q hQ
  exact h1.symm.trans h2.symm

end ProductRecordModel

/-- Actual independent ordinary-source data produce the selected state on
an honest raw product open; no comparison model/state is an input. -/
theorem exists_selected_product_state (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) (i : windowSpace e r W ⟶ X)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (z : (windowSpace e r W).obj.left)
    (d : DimEmbedding X (e.dim+r)) (c : d.carrier)
    (hc : i.hom.left.base z = d.toLocalEmbedding.toPoint c)
    (Q : MarkedIdeal (e.dim+r) (BlowupTowers.CMfd.of (n := e.dim+r) d.ambient))
    {H : ℕ → ℕ} (hQ : IsInvDomain (e.dim+r) Q) (hE : Q.E = [])
    (hState : NativeHSState Q d.carrier H) :
    ∃ M : ProductRecordModel e r W i hi z d c,
      IsInvDomain (e.dim+r) (ProductRecordModel.rawRecord M Q) ∧
        (ProductRecordModel.rawRecord M Q).E = [] ∧
        NativeHSState (ProductRecordModel.rawRecord M Q)
          (windowCarrier e r (ProductRecordModel.rawOpen M)) H := by
  obtain ⟨M,hD,hEmpty,hNative⟩ := exists_independent_product_record e r W i hi z d c hc Q hQ hE hState
  have hDomain := isInvDomain_pullback (ProductRecordModel.rawDiffeomorph M).symm hD
  have hE' : (ProductRecordModel.rawRecord M Q).E = [] := by
    change (M.record Q).E.map _ = []
    rw [hEmpty]
    rfl
  have hNative' := NativeHSState.pullback
    (X := BlowupTowers.CMfd.of (n := e.dim+r) M.sourceOpen)
    (X' := BlowupTowers.CMfd.of (n := e.dim+r) (ProductRecordModel.rawOpen M))
    (ProductRecordModel.rawDiffeomorph M).symm hNative
  exact ⟨M,hDomain,hE',ProductRecordModel.rawCarrier_eq M ▸ hNative'⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeProductSelectedState
