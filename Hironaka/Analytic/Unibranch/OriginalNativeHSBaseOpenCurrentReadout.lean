import Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenNativeStage

/-! Exact current-native point/full-map and original-prefix cosupp/value
readouts for the SAME base-restricted histories. Blueprint FIRST:
original-native-hs-base-open-current-readout.tex. Frozen parents unchanged. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenCurrentReadout
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11CompatibleCanonicalTowers
  OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism ResolutionInvariantSeq
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism.MarkedIdeal HironakaActualPowerBoundaryExponents
open _root_.Hironaka.ResolutionInvariantSpec (IsCanonical)

variable {X : SourceReducedComplexSpace} {n : ℕ} {ι : Type*}
  (w : ι → DimEmbedding X n) {T : Towers w} (xs : XStage w T)
  (h : PhysicalHistory X xs.Y) (hq : h.projection = xs.q)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
local notation "jB" => OriginalNativeHSBaseOpenNativeStage.baseInclusion U hU
local notation "hjB" => inclusion_isOpenImmersion X U hU
private abbrev retainedHistory (i : ι) := OriginalNativeHSBaseOpenWindows.history w jB hjB i (T i).2
local notation "ns" => OriginalNativeHSBaseOpenNativeStage.nativeStage w xs h hq U hU

def oldWindowMap (i : ι) : ofClosedAnalytic ((ns).carrier i) ((ns).analytic i) ⟶ xs.Y :=
  (ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (C := (ns).carrier i) (D := xs.carrier i)
      (contMDiff_subtype_val.comp (retainedHistory w (T := T) U hU i).back.contMDiff) (fun _ hz => hz))
    (actualSubspaceMap_point (C := (ns).carrier i) (D := xs.carrier i)
      (contMDiff_subtype_val.comp (retainedHistory w (T := T) U hU i).back.contMDiff) (fun _ hz => hz))) :
      ofClosedAnalytic ((ns).carrier i) ((ns).analytic i) ⟶ ofClosedAnalytic (xs.carrier i) (xs.analytic i)) ≫ xs.map i

private theorem chosen_equation {A B C : SourceReducedComplexSpace} (i : B ⟶ C) (a : A ⟶ C)
    (p : ∃ k : A ⟶ B, LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ k ≫ i = a) (z : A.obj.left) :
    i.hom.left.base (p.choose.hom.left.base z) = a.hom.left.base z :=
  congrArg (fun f => f.hom.left.base z) p.choose_spec.2

theorem window_source_point (i : ι) (z : (ns).carrier i) :
    (OriginalNativeHSBaseOpenNativeStage.sourceInclusion h U hU).hom.left.base
      (((ns).map i).hom.left.base z) =
      (xs.map i).hom.left.base ⟨((retainedHistory w (T := T) U hU i).back z.val).val, z.property⟩ := by
  change ((OriginalNativeHSBaseOpenNativeStage.nativeWindow w xs h hq U hU i ≫
    OriginalNativeHSBaseOpenNativeStage.sourceInclusion h U hU).hom.left.base z) = _
  unfold OriginalNativeHSBaseOpenNativeStage.nativeWindow
  exact chosen_equation (A := ofClosedAnalytic ((ns).carrier i) ((ns).analytic i))
    (OriginalNativeHSBaseOpenNativeStage.sourceInclusion h U hU) _ _ z

theorem window_source_square (i : ι) :
    (ns).map i ≫ OriginalNativeHSBaseOpenNativeStage.sourceInclusion h U hU = oldWindowMap w xs h hq U hU i := by
  apply morphism_eq_of_pointwise_eq
  intro z
  exact window_source_point w xs h hq U hU i z

theorem exists_window_preimage (i : ι) (c : xs.carrier i)
    (hc : xs.q.hom.left.base ((xs.map i).hom.left.base c) ∈ U) :
    ∃ z : (ns).carrier i, ((retainedHistory w (T := T) U hU i).back z.val).val = c.val ∧
      (OriginalNativeHSBaseOpenNativeStage.sourceInclusion h U hU).hom.left.base
        (((ns).map i).hom.left.base z) = (xs.map i).hom.left.base c := by
  let y : (OriginalNativeHSBaseOpenNativeStage.source h U hU).obj.left :=
    ⟨(xs.map i).hom.left.base c, by rw [hq]; exact hc⟩
  have hP := congrArg (fun f => f.hom.left.base y)
    (OriginalNativeHSBaseOpenNativeStage.projection_square h U hU)
  have hH := congrArg (fun f => f.hom.left.base ((xs.map i).hom.left.base c)) hq
  have hOldRange : (jB).hom.left.base ((OriginalNativeHSBaseOpenNativeStage.projection h U hU).hom.left.base y) ∈
      range (w i).toLocalEmbedding.toPoint := by
    have hPoint : (jB).hom.left.base ((OriginalNativeHSBaseOpenNativeStage.projection h U hU).hom.left.base y) =
        xs.q.hom.left.base ((xs.map i).hom.left.base c) := hP.trans hH
    have hRange : xs.q.hom.left.base ((xs.map i).hom.left.base c) ∈ range (w i).toLocalEmbedding.toPoint :=
      ⟨⟨(T i).2.proj c.val, xs.proj_mem i c⟩, (xs.square i c (xs.proj_mem i c)).symm⟩
    exact hPoint.symm ▸ hRange
  have hNewRange : (OriginalNativeHSBaseOpenNativeStage.projection h U hU).hom.left.base y ∈
      range (OriginalNativeHSBaseOpenWindows.window w jB hjB i).toLocalEmbedding.toPoint :=
    (Set.ext_iff.mp (OriginalNativeHSBaseOpenWindows.range_dictionary w jB hjB i) _).mp hOldRange
  obtain ⟨z, hz⟩ := (Set.ext_iff.mp
    (OriginalNativeHSBaseOpenNativeStage.nativeWindow_range w xs h hq U hU i) y).mpr hNewRange
  have hPoint : (OriginalNativeHSBaseOpenNativeStage.sourceInclusion h U hU).hom.left.base
      (((ns).map i).hom.left.base z) = (xs.map i).hom.left.base c :=
    congrArg (OriginalNativeHSBaseOpenNativeStage.sourceInclusion h U hU).hom.left.base hz
  have hEq := (xs.isOpenImmersion i).base_open.injective
    ((window_source_point w xs h hq U hU i z).symm.trans hPoint)
  exact ⟨z, congrArg Subtype.val hEq, hPoint⟩

variable {B : SourceReducedComplexSpace} (j : B ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
  (raw : ∀ i, MarkedIdeal n (Amb w i)) {H : ℕ → ℕ}
  (hRaw : ∀ i, HironakaG11PresReduction.IsNativeWindowRecord (w i) (raw i) H)
  (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) {Λ : Type*} [LinearOrder Λ]
  (R : ResolutionInvariant.{0} n n Λ)

include hRaw he in
theorem cosupp_iff (i : ι) {Y : CMfd.{0} n} (S : BlowupTower (Amb w i) Y)
    (hS : IsCanonical (powerMarked (raw i) (e i)) (R.inv (powerMarked (raw i) (e i))) S)
    (z : (OriginalNativeHSBaseOpenWindows.history w j hj i S).target) :
    z ∈ (geoTransformAlong (OriginalNativeHSBaseOpenWindows.record w j hj raw e i)
      (OriginalNativeHSBaseOpenWindows.history w j hj i S).tower).cosupp ↔
      ((OriginalNativeHSBaseOpenWindows.history w j hj i S).back z).val ∈
        (geoTransformAlong (powerMarked (raw i) (e i)) S).cosupp := by
  have hD := powerMarked_isInvDomain _ (hRaw i).1 (he i)
  let O := OriginalNativeHSBaseOpenWindows.traceOpen w j hj i
  have hD' := InvDomainTowerAlong.isInvDomain_pullback_val O hD
  have hCan := Seq.ResolutionInvariantExt.isCanonical_restrict R hD O S hS
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hD S hS
  rw [OriginalNativeHSBaseOpenWindows.record_eq_pullback w j hj raw hRaw e i]
  rw [IsTowerIso.cosupp_geoTransformAlong (OriginalNativeHSBaseOpenWindows.baseEquiv w j hj i)
    hD'.isWellFormed.isClosedSubmanifold_N hD'.isWellFormed.isCoherent
    (OriginalNativeHSBaseOpenWindows.history_isTowerIso w j hj i S)
    (R.isInvValue.isGeoTestTower_of_isCanonical hD' _ hCan)]
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent O S hTest]
  rfl

include hRaw he in
theorem value_eq (i : ι) {Y : CMfd.{0} n} (S : BlowupTower (Amb w i) Y)
    (hS : IsCanonical (powerMarked (raw i) (e i)) (R.inv (powerMarked (raw i) (e i))) S)
    (z : (OriginalNativeHSBaseOpenWindows.history w j hj i S).target)
    (hz : z ∈ (geoTransformAlong (OriginalNativeHSBaseOpenWindows.record w j hj raw e i)
      (OriginalNativeHSBaseOpenWindows.history w j hj i S).tower).cosupp) :
    R.inv (OriginalNativeHSBaseOpenWindows.record w j hj raw e i)
      (OriginalNativeHSBaseOpenWindows.history w j hj i S).tower z =
      R.inv (powerMarked (raw i) (e i)) S ((OriginalNativeHSBaseOpenWindows.history w j hj i S).back z).val :=
  OriginalNativeHSBaseOpenWindows.history_value w j hj raw hRaw e he R i S hS z
    ((cosupp_iff w j hj raw hRaw e he R i S hS z).mp hz)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenCurrentReadout
