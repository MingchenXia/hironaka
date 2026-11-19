import Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenStage
import Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryRestriction

/-! SAME present native physical history and whole XStage over a genuinely
PRECOMPACT native base open. Blueprint FIRST:
original-native-hs-base-open-native-stage.tex. No open-para shortcut. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenNativeStage
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11CompatibleCanonicalTowers
  OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces OriginalNativeSmoothOpenLocality
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals.MarkedIdeal

variable {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))

abbrev base : SourceReducedComplexSpace := restriction X U hU

abbrev baseInclusion : base (X := X) U hU ⟶ X := inclusion X U hU

def source : SourceReducedComplexSpace := preimageRestriction U h.projection hU h.singularModification.isProperMap

def physicalHistory : PhysicalHistory (base (X := X) U hU) (source h U hU) :=
  OriginalNativePhysicalHistoryRestriction.restrict h U hU

def projection : source h U hU ⟶ base (X := X) U hU := (physicalHistory h U hU).projection

def sourceInclusion : source h U hU ⟶ Y :=
  inclusion Y (preimageOpen U h.projection) (isCompact_closure_preimage U h.projection hU h.singularModification.isProperMap)

theorem physical_length : (physicalHistory h U hU).length = h.length :=
  OriginalNativePhysicalHistoryRestriction.length_restrict h U hU

theorem projection_square : projection h U hU ≫ baseInclusion U hU = sourceInclusion h U hU ≫ h.projection :=
  OriginalNativePhysicalHistoryRestriction.projection_square h U hU

theorem projection_scalar : (projection h U hU).hom.left ≫ (base (X := X) U hU).obj.hom =
    (source h U hU).obj.hom := Over.w (projection h U hU).hom

theorem projection_proper : IsProperMap (projection h U hU).hom.left.base :=
  (physicalHistory h U hU).singularModification.isProperMap

variable {n : ℕ} {ι : Type*} (w : ι → DimEmbedding X n) {T : Towers w}
  (xs : XStage w T) (history : PhysicalHistory X xs.Y) (hHistory : history.projection = xs.q)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
local notation "jB" => baseInclusion U hU
local notation "hjB" => inclusion_isOpenImmersion X U hU
local notation "wN" => OriginalNativeHSBaseOpenWindows.window w jB hjB

private def localHistory (i : ι) := OriginalNativeHSBaseOpenWindows.history w jB hjB i (T i).2

/-- Entire actual inverse-carrier of the real old terminal-open map. -/
private def carrier (i : ι) : Set (localHistory w (T := T) U hU i).target :=
  (localHistory w (T := T) U hU i).back ⁻¹'
    ((Subtype.val : openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i) → (T i).1) ⁻¹'
      xs.carrier i)

theorem carrier_dictionary (i : ι) : carrier w xs U hU i =
    strictAlong (localHistory w (T := T) U hU i).tower (wN i).carrier := by
  change (localHistory w (T := T) U hU i).back ⁻¹'
    ((Subtype.val : openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i) → (T i).1) ⁻¹' xs.carrier i) = _
  rw [xs.carrier_eq i]
  exact (OriginalNativeHSBaseOpenWindows.history_carrier w jB hjB i (T i).2).symm

private theorem carrier_analytic (i : ι) : IsComplexAnalyticSubset (n := n) (carrier w xs U hU i) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_subtype_val.comp (localHistory w (T := T) U hU i).back.contMDiff) (xs.analytic i)

private def windowSource (i : ι) : SourceReducedComplexSpace :=
  ofClosedAnalytic (carrier w xs U hU i) (carrier_analytic w xs U hU i)

private def traceSource (i : ι) : SourceReducedComplexSpace :=
  ofClosedAnalytic
    ((Subtype.val : openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i) → (T i).1) ⁻¹'
      xs.carrier i)
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val (xs.analytic i)
      (openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i)))

private def traceIso (i : ι) : windowSource w xs U hU i ≅ traceSource w xs U hU i :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk (actualSubspaceBiholomorphicIso (localHistory w (T := T) U hU i).back _ _ (fun _ => Iff.rfl))
      (actualSubspaceMap_point (localHistory w (T := T) U hU i).back.contMDiff (fun _ hx => hx)))

private def traceInclusion (i : ι) : traceSource w xs U hU i ⟶
    ofClosedAnalytic (xs.carrier i) (xs.analytic i) :=
  ObjectProperty.homMk (Over.homMk
    (actualOpenSubspaceMap (n := n) (xs.carrier i)
      (openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i)))
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))

private theorem traceInclusion_open (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (traceInclusion w xs U hU i).hom.left :=
  actualOpenSubspaceMap_isOpenImmersion _ _

private def oldWindow (i : ι) : windowSource w xs U hU i ⟶ xs.Y :=
  (traceIso w xs U hU i).hom ≫ traceInclusion w xs U hU i ≫ xs.map i

private theorem oldWindow_open (i : ι) : LocallyRingedSpace.IsOpenImmersion (oldWindow w xs U hU i).hom.left := by
  have hIso : LocallyRingedSpace.IsOpenImmersion ((traceIso w xs U hU i).hom).hom.left := by
    change LocallyRingedSpace.IsOpenImmersion
      (actualSubspaceBiholomorphicIso (localHistory w (T := T) U hU i).back _ _ (fun _ => Iff.rfl)).hom
    infer_instance
  let : LocallyRingedSpace.IsOpenImmersion ((traceIso w xs U hU i).hom).hom.left := hIso
  let : LocallyRingedSpace.IsOpenImmersion (traceInclusion w xs U hU i).hom.left := traceInclusion_open w xs U hU i
  let : LocallyRingedSpace.IsOpenImmersion (xs.map i).hom.left := xs.isOpenImmersion i
  change LocallyRingedSpace.IsOpenImmersion
    (((traceIso w xs U hU i).hom).hom.left ≫ (traceInclusion w xs U hU i).hom.left ≫ (xs.map i).hom.left)
  infer_instance

private theorem oldWindow_point (i : ι) (z : (windowSource w xs U hU i).obj.left) :
    (oldWindow w xs U hU i).hom.left.base z = (xs.map i).hom.left.base
      ⟨((localHistory w (T := T) U hU i).back z.val).val, z.property⟩ := rfl

private theorem ambient_projection (i : ι) (z : (localHistory w (T := T) U hU i).target) :
    Opens.inclusion (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (w i).toLocalEmbedding jB hjB)
      ((localHistory w (T := T) U hU i).tower.proj z) =
      (T i).2.proj (((localHistory w (T := T) U hU i).back z).val) := by
  have h := (OriginalNativeHSBaseOpenWindows.history_isTowerIso w jB hjB i (T i).2).proj_comm z
  exact (congrArg Subtype.val h).trans (proj_restrict
    (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i) (T i).2
    ((localHistory w (T := T) U hU i).back z))

private theorem initial_point (i : ι) (c : (wN i).carrier) :
    (jB).hom.left.base ((wN i).toLocalEmbedding.toPoint c) =
      (w i).toLocalEmbedding.toPoint
        ⟨Opens.inclusion (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (w i).toLocalEmbedding jB hjB)
          c.val, c.property⟩ :=
  (congrArg (fun f => f.hom.left.base c) (OriginalNativeHSBaseOpenWindows.base_square w jB hjB i)).trans
    ((w i).toLocalEmbedding.restrict_toPoint _
      (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (w i).toLocalEmbedding jB hjB) c)

include hHistory in
private theorem oldWindow_in_source (i : ι) : range (oldWindow w xs U hU i).hom.left.base ⊆
    range (sourceInclusion history U hU).hom.left.base := by
  rintro y ⟨z, rfl⟩
  let a : xs.carrier i := ⟨((localHistory w (T := T) U hU i).back z.val).val, z.property⟩
  have hp : (T i).2.proj a.val ∈ (w i).carrier := xs.proj_mem i a
  have hO : (T i).2.proj a.val ∈ OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i :=
    ((localHistory w (T := T) U hU i).back z.val).property
  have hRange : (w i).toLocalEmbedding.toPoint ⟨(T i).2.proj a.val, hp⟩ ∈ range (jB).hom.left.base :=
    (Set.ext_iff.mp (OriginalNativeEmbeddingOpenPullback.ambientTrace (w i).toLocalEmbedding jB hjB).trace _).mp hO
  have hU' : history.projection.hom.left.base ((oldWindow w xs U hU i).hom.left.base z) ∈ U := by
    rw [hHistory, oldWindow_point w xs U hU i z, xs.square i a hp]
    exact (Set.ext_iff.mp (inclusion_range X U hU) _).mp hRange
  exact ⟨⟨(oldWindow w xs U hU i).hom.left.base z, hU'⟩, rfl⟩

private theorem sourceInclusion_open : LocallyRingedSpace.IsOpenImmersion (sourceInclusion history U hU).hom.left :=
  inclusion_isOpenImmersion _ _ _

/-- Actual native target-open lift, internally constructed from the WHOLE image. -/
def nativeWindow (i : ι) : windowSource w xs U hU i ⟶ source history U hU :=
  (exists_native_open_lift (sourceInclusion history U hU) (oldWindow w xs U hU i)
    (sourceInclusion_open w xs history U hU) (oldWindow_open w xs U hU i)
    (oldWindow_in_source w xs history hHistory U hU i)).choose

theorem nativeWindow_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (nativeWindow w xs history hHistory U hU i).hom.left :=
  (exists_native_open_lift (sourceInclusion history U hU) (oldWindow w xs U hU i)
    (sourceInclusion_open w xs history U hU) (oldWindow_open w xs U hU i)
    (oldWindow_in_source w xs history hHistory U hU i)).choose_spec.1

private theorem nativeWindow_old_square (i : ι) :
    nativeWindow w xs history hHistory U hU i ≫ sourceInclusion history U hU = oldWindow w xs U hU i :=
  (exists_native_open_lift (sourceInclusion history U hU) (oldWindow w xs U hU i)
    (sourceInclusion_open w xs history U hU) (oldWindow_open w xs U hU i)
    (oldWindow_in_source w xs history hHistory U hU i)).choose_spec.2

private theorem windowProjection_mem (i : ι) (z : (windowSource w xs U hU i).obj.left) :
    (localHistory w (T := T) U hU i).tower.proj z.val ∈ (wN i).carrier :=
  MemberInterTowerAlong.strictAlong_subset_preimage (localHistory w (T := T) U hU i).tower
    (wN i).analytic.isClosed ((carrier_dictionary w xs U hU i) ▸ z.property)

private def windowProjection (i : ι) : windowSource w xs U hU i ⟶
    ofClosedAnalytic (wN i).carrier (wN i).analytic :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (localHistory w (T := T) U hU i).tower.contMDiff_proj
      (fun z hz => windowProjection_mem w xs U hU i ⟨z, hz⟩))
    (actualSubspaceMap_point (localHistory w (T := T) U hU i).tower.contMDiff_proj
      (fun z hz => windowProjection_mem w xs U hU i ⟨z, hz⟩)))

/-- FULL quotient-native square for the SAME actual old physical projection. -/
theorem nativeWindow_square (i : ι) :
    nativeWindow w xs history hHistory U hU i ≫ projection history U hU =
      windowProjection w xs U hU i ≫ EmbeddedBlowupOverlap.chartMorphism (wN i).toLocalEmbedding := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply (hjB).base_open.injective
  have hOld := congrArg (fun f => f.hom.left.base z) (nativeWindow_old_square w xs history hHistory U hU i)
  have hProj := congrArg (fun f => f.hom.left.base
    ((nativeWindow w xs history hHistory U hU i).hom.left.base z)) (projection_square history U hU)
  have hH := congrArg (fun f => f.hom.left.base ((oldWindow w xs U hU i).hom.left.base z)) hHistory
  let a : xs.carrier i := ⟨((localHistory w (T := T) U hU i).back z.val).val, z.property⟩
  have hA := ambient_projection w U hU i z.val
  have hInitial := initial_point w U hU i
    ⟨(localHistory w (T := T) U hU i).tower.proj z.val, windowProjection_mem w xs U hU i z⟩
  exact hProj.trans ((congrArg history.projection.hom.left.base hOld).trans
    (hH.trans ((xs.square i a (xs.proj_mem i a)).trans
      ((congrArg (w i).toLocalEmbedding.toPoint (Subtype.ext hA)).symm.trans hInitial.symm))))

theorem nativeWindow_scalar (i : ι) :
    (nativeWindow w xs history hHistory U hU i).hom.left ≫ (source history U hU).obj.hom =
      (windowSource w xs U hU i).obj.hom := Over.w (nativeWindow w xs history hHistory U hU i).hom

/-- EXACT actual inverse-window range on the SAME literal restricted source. -/
theorem nativeWindow_range (i : ι) :
    range (nativeWindow w xs history hHistory U hU i).hom.left.base =
      (projection history U hU).hom.left.base ⁻¹' range (wN i).toLocalEmbedding.toPoint := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(windowProjection w xs U hU i).hom.left.base z,
      (congrArg (fun f => f.hom.left.base z) (nativeWindow_square w xs history hHistory U hU i)).symm⟩
  · rintro ⟨c, hc⟩
    have hProj := congrArg (fun f => f.hom.left.base y) (projection_square history U hU)
    have hH := congrArg (fun f => f.hom.left.base ((sourceInclusion history U hU).hom.left.base y)) hHistory
    have hBase : xs.q.hom.left.base ((sourceInclusion history U hU).hom.left.base y) =
        (jB).hom.left.base ((projection history U hU).hom.left.base y) := hH.symm.trans hProj.symm
    have hOldRange : (sourceInclusion history U hU).hom.left.base y ∈
        xs.q.hom.left.base ⁻¹' range (w i).toLocalEmbedding.toPoint := by
      change xs.q.hom.left.base ((sourceInclusion history U hU).hom.left.base y) ∈ range (w i).toLocalEmbedding.toPoint
      rw [hBase, ← hc, initial_point w U hU i c]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (xs.range_map i) _).mpr hOldRange
    have haBase : (w i).toLocalEmbedding.toPoint ⟨(T i).2.proj a.val, xs.proj_mem i a⟩ =
        (jB).hom.left.base ((projection history U hU).hom.left.base y) :=
      (xs.square i a (xs.proj_mem i a)).symm.trans ((congrArg xs.q.hom.left.base ha).trans hBase)
    have hO : (T i).2.proj a.val ∈ OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i :=
      (Set.ext_iff.mp (OriginalNativeEmbeddingOpenPullback.ambientTrace (w i).toLocalEmbedding jB hjB).trace _).mpr
        ⟨(projection history U hU).hom.left.base y, haBase.symm⟩
    let b : openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i) := ⟨a.val, hO⟩
    let z : (windowSource w xs U hU i).obj.left :=
      ⟨(localHistory w (T := T) U hU i).back.symm b, by
        change ((localHistory w (T := T) U hU i).back
          ((localHistory w (T := T) U hU i).back.symm b)).val ∈ xs.carrier i
        exact congrArg (Subtype.val : openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i) → (T i).1) ((localHistory w (T := T) U hU i).back.apply_symm_apply b) |>.symm ▸ a.property⟩
    have hPoint : (oldWindow w xs U hU i).hom.left.base z = (xs.map i).hom.left.base a := by
      rw [oldWindow_point w xs U hU i z]
      apply congrArg (xs.map i).hom.left.base
      exact Subtype.ext (congrArg (Subtype.val : openPreimage (T i).2 (OriginalNativeHSBaseOpenWindows.traceOpen w jB hjB i) → (T i).1) ((localHistory w (T := T) U hU i).back.apply_symm_apply b))
    refine ⟨z, (sourceInclusion_open w xs history U hU).base_open.injective ?_⟩
    exact (congrArg (fun f => f.hom.left.base z)
      (nativeWindow_old_square w xs history hHistory U hU i)).trans (hPoint.trans ha)

/-- Full native XStage of the SAME restricted physical history, no new history supplier. -/
def nativeStage : XStage wN (fun i => ⟨(localHistory w (T := T) U hU i).target,
    (localHistory w (T := T) U hU i).tower⟩) where
  Y := source history U hU
  q := projection history U hU
  isSingularCentreModification := (physicalHistory history U hU).singularModification
  carrier := carrier w xs U hU
  analytic := carrier_analytic w xs U hU
  map := nativeWindow w xs history hHistory U hU
  isOpenImmersion := nativeWindow_isOpenImmersion w xs history hHistory U hU
  carrier_eq := carrier_dictionary w xs U hU
  square i c _hc := congrArg (fun f => f.hom.left.base c)
    (nativeWindow_square w xs history hHistory U hU i)
  range_map := nativeWindow_range w xs history hHistory U hU

theorem native_source : (nativeStage w xs history hHistory U hU).Y = source history U hU := rfl

theorem native_projection : (nativeStage w xs history hHistory U hU).q = projection history U hU := rfl

theorem native_clock (i : ι) (hclock : history.length = (T i).2.length) :
    (physicalHistory history U hU).length = (localHistory w (T := T) U hU i).tower.length :=
  (physical_length history U hU).trans (hclock.trans
    (OriginalNativeHSBaseOpenWindows.history_length w jB hjB i (T i).2).symm)

/-- Explicit join to the ACTUAL compatible restricted GStage, on the SAME history. -/
def compatibleNativeStage {H : ℕ → ℕ} (raw : ∀ i, MarkedIdeals.MarkedIdeal n (Amb w i))
    (hRaw : ∀ i, HironakaG11PresReduction.IsNativeWindowRecord (w i) (raw i) H)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) {Λ : Type*} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0} n n Λ) {m : ℕ}
    (s : GStage R (fun i => HironakaActualPowerBoundaryExponents.powerMarked (raw i) (e i)) (mapAdm w) m)
    (ys : XStage w s.T) (h : PhysicalHistory X ys.Y) (hq : h.projection = ys.q) :
    XStage wN (OriginalNativeHSBaseOpenStage.stage w jB hjB raw hRaw e he R s).T :=
  nativeStage w ys h hq U hU

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenNativeStage
