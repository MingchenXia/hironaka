import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeProperFibreShrink
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality
import Hironaka.Analytic.Unibranch.SourceMorphismExt

/-! Proper SOURCE whole-fibre shrinking of the SAME prescribed history.
Blueprint FIRST: original-native-hs-prescribed-fibre-shrink.tex.
No smooth-map properness, next-source packet or new State/history choice. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSPrescribedFibreShrink
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState
  OriginalRelativelyCompactRestriction

private theorem inclusion_range {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    (S : State X K) (W : Opens X.obj.left) (hW : IsCompact (closure (W : Set X.obj.left)))
    (hRange : closure (W : Set X.obj.left) ⊆ range S.inclusion.hom.left.base) :
    range (OriginalNativeHSCurrentOverlap.inclusion S W hW hRange).hom.left.base =
      (S.history.projection ≫ S.inclusion).hom.left.base ⁻¹' (W : Set X.obj.left) := by
  change range (Subtype.val : preimageOpen (OriginalNativePrescribedOpenHistory.pullbackOpen S.inclusion W)
    S.history.projection → S.source.obj.left) = _
  rw [Subtype.range_coe]
  rfl

private theorem factor_range {A B D : SourceReducedComplexSpace}
    (k : A ⟶ B) (e : B ⟶ D) (b : A ⟶ D)
    (he : LocallyRingedSpace.IsOpenImmersion e.hom.left) (hs : k ≫ e = b) :
    range k.hom.left.base = e.hom.left.base ⁻¹' range b.hom.left.base := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x,(congrArg (fun f : A ⟶ D => f.hom.left.base x) hs).symm⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,he.base_open.injective ((congrArg (fun f : A ⟶ D => f.hom.left.base x) hs).trans hx)⟩

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (S : State X K) (W : Opens X.obj.left) (hW : IsCompact (closure (W : Set X.obj.left)))
  (hRange : closure (W : Set X.obj.left) ⊆ range S.inclusion.hom.left.base)

private abbrev oldSource := OriginalNativeHSCurrentOverlap.endpoint S W hW hRange
private abbrev oldBase := restriction X W hW
private abbrev oldHistory := OriginalNativeHSCurrentOverlap.history S W hW hRange
private abbrev p : oldSource S W hW hRange ⟶ oldBase W hW := (oldHistory S W hW hRange).projection
private abbrev iW : oldBase W hW ⟶ X := inclusion X W hW
private abbrev oldInclusion : oldSource S W hW hRange ⟶ S.source :=
  OriginalNativeHSCurrentOverlap.inclusion S W hW hRange
private abbrev oldOriginal : oldSource S W hW hRange ⟶ X := p S W hW hRange ≫ iW W hW

/-- The ENTIRE own compact fibre, with its actual original scalar map. -/
def compact : Set (oldSource S W hW hRange).obj.left :=
  (oldOriginal S W hW hRange).hom.left.base ⁻¹' K

variable (hContains : K ⊆ W) (hK : IsCompact K)
  (U : Opens (oldSource S W hW hRange).obj.left)
  (hGood : compact S W hW hRange ⊆ U) (E : Opens X.obj.left) (hExtra : K ⊆ E)

private def goodBase : Opens (oldBase W hW).obj.left :=
  OriginalNativeProperFibreShrink.goodBase (p S W hW hRange)
    (oldHistory S W hW hRange).singularModification.isProperMap U

include hGood in
private theorem compact_in_goodBase : (iW W hW).hom.left.base ⁻¹' K ⊆
    (goodBase S W hW hRange U : Set (oldBase W hW).obj.left) :=
  OriginalNativeProperFibreShrink.compact_subset_goodBase (p S W hW hRange)
    (oldHistory S W hW hRange).singularModification.isProperMap U hGood

private def originalGood : Opens X.obj.left :=
  ⟨(iW W hW).hom.left.base '' (goodBase S W hW hRange U : Set (oldBase W hW).obj.left) ∩ E,
    ((inclusion_isOpenImmersion X W hW).base_open.isOpenMap _ (goodBase S W hW hRange U).isOpen).inter E.isOpen⟩

include hContains hGood hExtra in
private theorem compact_in_originalGood : K ⊆ originalGood S W hW hRange U E := by
  intro x hx
  let b : (oldBase W hW).obj.left := ⟨x,hContains hx⟩
  have hb : b ∈ goodBase S W hW hRange U := compact_in_goodBase S W hW hRange U hGood hx
  exact ⟨⟨b,hb,rfl⟩,hExtra hx⟩

private def neighbourhood := OriginalNativePrecompactNeighbourhood.neighbourhood X K hK
  (originalGood S W hW hRange U E)
  (compact_in_originalGood S W hW hRange hContains U hGood E hExtra)

/-- ONE original precompact source open, retaining ALL the own compact. -/
def openSet : Opens X.obj.left := (neighbourhood S W hW hRange hContains hK U hGood E hExtra).openSet
theorem compactClosure : IsCompact (closure (openSet S W hW hRange hContains hK U hGood E hExtra : Set X.obj.left)) :=
  (neighbourhood S W hW hRange hContains hK U hGood E hExtra).compactClosure
theorem contains : K ⊆ openSet S W hW hRange hContains hK U hGood E hExtra :=
  (neighbourhood S W hW hRange hContains hK U hGood E hExtra).contains
theorem closure_subset_old : closure (openSet S W hW hRange hContains hK U hGood E hExtra : Set X.obj.left) ⊆ W := by
  intro x hx
  obtain ⟨b,_hb,hbx⟩ := ((neighbourhood S W hW hRange hContains hK U hGood E hExtra).closure_subset hx).1
  have hbW : (iW W hW).hom.left.base b ∈ W := b.property
  exact hbx ▸ hbW
theorem closure_subset_extra : closure (openSet S W hW hRange hContains hK U hGood E hExtra : Set X.obj.left) ⊆ E :=
  fun _ hx => ((neighbourhood S W hW hRange hContains hK U hGood E hExtra).closure_subset hx).2
theorem closureRange : closure (openSet S W hW hRange hContains hK U hGood E hExtra : Set X.obj.left) ⊆
    range S.inclusion.hom.left.base :=
  fun _ hx => hRange (subset_closure (closure_subset_old S W hW hRange hContains hK U hGood E hExtra hx))

local notation "V" => openSet S W hW hRange hContains hK U hGood E hExtra
local notation "hV" => compactClosure S W hW hRange hContains hK U hGood E hExtra
local notation "vRange" => closureRange S W hW hRange hContains hK U hGood E hExtra
private abbrev newSource := OriginalNativeHSCurrentOverlap.endpoint S (V) (hV) (vRange)
private abbrev newHistory := OriginalNativeHSCurrentOverlap.history S (V) (hV) (vRange)
private abbrev newInclusion : newSource S W hW hRange hContains hK U hGood E hExtra ⟶ S.source :=
  OriginalNativeHSCurrentOverlap.inclusion S (V) (hV) (vRange)

private theorem image_subset : range (newInclusion S W hW hRange hContains hK U hGood E hExtra).hom.left.base ⊆
    range (oldInclusion S W hW hRange).hom.left.base := by
  intro y hy
  apply (Set.ext_iff.mp (inclusion_range S W hW hRange) y).mpr
  have hyV := (Set.ext_iff.mp (inclusion_range S (V) (hV) (vRange)) y).mp hy
  exact closure_subset_old S W hW hRange hContains hK U hGood E hExtra (subset_closure hyV)

private theorem exists_map : ∃ k : newSource S W hW hRange hContains hK U hGood E hExtra ⟶ oldSource S W hW hRange,
    LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ k ≫ oldInclusion S W hW hRange =
      newInclusion S W hW hRange hContains hK U hGood E hExtra :=
  OriginalNativeSmoothOpenLocality.exists_native_open_lift (oldInclusion S W hW hRange)
    (newInclusion S W hW hRange hContains hK U hGood E hExtra)
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history)
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion S.inclusion S.inclusion_isOpenImmersion (V) (hV) (vRange) S.history)
    (image_subset S W hW hRange hContains hK U hGood E hExtra)

/-- Actual native OI between the SAME two prescribed endpoints. -/
def sourceMap : newSource S W hW hRange hContains hK U hGood E hExtra ⟶ oldSource S W hW hRange :=
  (exists_map S W hW hRange hContains hK U hGood E hExtra).choose
theorem sourceMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left :=
  (exists_map S W hW hRange hContains hK U hGood E hExtra).choose_spec.1
theorem sourceMap_square : sourceMap S W hW hRange hContains hK U hGood E hExtra ≫ oldInclusion S W hW hRange =
    newInclusion S W hW hRange hContains hK U hGood E hExtra :=
  (exists_map S W hW hRange hContains hK U hGood E hExtra).choose_spec.2

theorem projection_square :
    (newHistory S W hW hRange hContains hK U hGood E hExtra).projection ≫ inclusion X (V) (hV) =
      sourceMap S W hW hRange hContains hK U hGood E hExtra ≫ oldOriginal S W hW hRange := by
  have hn := OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion
    (V) (hV) (vRange) S.history
  have ho := OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro y
  have hn' := congrArg (fun f : newSource S W hW hRange hContains hK U hGood E hExtra ⟶ X => f.hom.left.base y) hn
  have hk := congrArg (fun f => f.hom.left.base y) (sourceMap_square S W hW hRange hContains hK U hGood E hExtra)
  have ho' := congrArg (fun f : oldSource S W hW hRange ⟶ X =>
    f.hom.left.base ((sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base y)) ho
  exact hn'.trans ((congrArg (S.history.projection ≫ S.inclusion).hom.left.base hk.symm).trans ho'.symm)

theorem scalar : (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left ≫
    (oldSource S W hW hRange).obj.hom = (newSource S W hW hRange hContains hK U hGood E hExtra).obj.hom :=
  Over.w (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom

theorem sourceMap_range : range (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base =
    (oldOriginal S W hW hRange).hom.left.base ⁻¹' (V : Set X.obj.left) := by
  have hr := factor_range (sourceMap S W hW hRange hContains hK U hGood E hExtra)
    (oldInclusion S W hW hRange) (newInclusion S W hW hRange hContains hK U hGood E hExtra)
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history)
    (sourceMap_square S W hW hRange hContains hK U hGood E hExtra)
  have hi : range (newInclusion S W hW hRange hContains hK U hGood E hExtra).hom.left.base =
      (S.history.projection ≫ S.inclusion).hom.left.base ⁻¹' (V : Set X.obj.left) := inclusion_range S (V) (hV) (vRange)
  ext y
  have hm := Set.ext_iff.mp hr y
  rw [hi] at hm
  have hp := congrArg (fun f : oldSource S W hW hRange ⟶ X => f.hom.left.base y)
    (OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history)
  exact hm.trans (iff_of_eq (congrArg (fun x : X.obj.left => x ∈ (V : Set X.obj.left)) hp.symm))

private theorem whole_closure_in_good : (oldOriginal S W hW hRange).hom.left.base ⁻¹'
    closure (V : Set X.obj.left) ⊆ (U : Set (oldSource S W hW hRange).obj.left) := by
  intro z hz
  obtain ⟨b,hb,hbz⟩ := ((neighbourhood S W hW hRange hContains hK U hGood E hExtra).closure_subset hz).1
  have he : b = (p S W hW hRange).hom.left.base z := (inclusion_isOpenImmersion X W hW).base_open.injective hbz
  have hgb : (p S W hW hRange).hom.left.base z ∈ goodBase S W hW hRange U := he ▸ hb
  exact OriginalNativeProperFibreShrink.preimage_goodBase_subset (p S W hW hRange)
    (oldHistory S W hW hRange).singularModification.isProperMap U hgb

theorem sourceMap_in_good : range (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base ⊆
    (U : Set (oldSource S W hW hRange).obj.left) := by
  intro z hz
  apply whole_closure_in_good S W hW hRange hContains hK U hGood E hExtra
  exact subset_closure ((Set.ext_iff.mp (sourceMap_range S W hW hRange hContains hK U hGood E hExtra) z).mp hz)

theorem sourceMap_closure_in_good : closure (range (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base) ⊆
    (U : Set (oldSource S W hW hRange).obj.left) := by
  have hc : closure (range (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base) ⊆
      (oldOriginal S W hW hRange).hom.left.base ⁻¹' closure (V : Set X.obj.left) := by
    apply closure_minimal
    · intro z hz
      exact subset_closure ((Set.ext_iff.mp (sourceMap_range S W hW hRange hContains hK U hGood E hExtra) z).mp hz)
    · exact isClosed_closure.preimage (oldOriginal S W hW hRange).hom.left.base.hom.continuous
  exact hc.trans (whole_closure_in_good S W hW hRange hContains hK U hGood E hExtra)

/-- The actual precompact current-source open for genuine phase-frame restriction. -/
def currentOpen : Opens S.source.obj.left := preimageOpen
  (OriginalNativePrescribedOpenHistory.pullbackOpen S.inclusion (V)) S.history.projection

theorem currentOpen_eq_range : (currentOpen S W hW hRange hContains hK U hGood E hExtra : Set S.source.obj.left) =
    range (newInclusion S W hW hRange hContains hK U hGood E hExtra).hom.left.base := by
  change _ = range (Subtype.val : preimageOpen (OriginalNativePrescribedOpenHistory.pullbackOpen S.inclusion (V))
    S.history.projection → S.source.obj.left)
  exact Subtype.range_coe.symm

theorem currentOpen_compactClosure :
    IsCompact (closure (currentOpen S W hW hRange hContains hK U hGood E hExtra : Set S.source.obj.left)) :=
  isCompact_closure_preimage (OriginalNativePrescribedOpenHistory.pullbackOpen S.inclusion (V)) S.history.projection
    (OriginalNativePrescribedOpenHistory.pullbackOpen_compactClosure S.inclusion S.inclusion_isOpenImmersion
      (V) (hV) (vRange)) S.history.singularModification.isProperMap

theorem currentOpen_closure_in_good :
    closure (currentOpen S W hW hRange hContains hK U hGood E hExtra : Set S.source.obj.left) ⊆
      (oldInclusion S W hW hRange).hom.left.base '' (U : Set (oldSource S W hW hRange).obj.left) := by
  have hc : closure (currentOpen S W hW hRange hContains hK U hGood E hExtra : Set S.source.obj.left) ⊆
      (S.history.projection ≫ S.inclusion).hom.left.base ⁻¹' closure (V : Set X.obj.left) := by
    apply closure_minimal
    · intro y hy
      exact subset_closure hy
    · exact isClosed_closure.preimage (S.history.projection ≫ S.inclusion).hom.left.base.hom.continuous
  intro y hy
  have hyV := hc hy
  have hyW : y ∈ range (oldInclusion S W hW hRange).hom.left.base := by
    apply (Set.ext_iff.mp (inclusion_range S W hW hRange) y).mpr
    exact closure_subset_old S W hW hRange hContains hK U hGood E hExtra hyV
  obtain ⟨z,hz⟩ := hyW
  refine ⟨z,?_,hz⟩
  apply whole_closure_in_good S W hW hRange hContains hK U hGood E hExtra
  have hp := congrArg (fun f : oldSource S W hW hRange ⟶ X => f.hom.left.base z)
    (OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history)
  have he : (oldOriginal S W hW hRange).hom.left.base z =
      (S.history.projection ≫ S.inclusion).hom.left.base y :=
    hp.trans (congrArg (S.history.projection ≫ S.inclusion).hom.left.base hz)
  change (oldOriginal S W hW hRange).hom.left.base z ∈ closure (V : Set X.obj.left)
  exact (congrArg (fun x : X.obj.left => x ∈ closure (V : Set X.obj.left)) he).mpr hyV

theorem currentOpen_shadow : shadow S ⊆ currentOpen S W hW hRange hContains hK U hGood E hExtra := by
  intro y hy
  exact contains S W hW hRange hContains hK U hGood E hExtra hy

theorem compact_preimage : compact S (V) (hV) (vRange) =
    (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base ⁻¹' compact S W hW hRange := by
  ext z
  exact iff_of_eq (congrArg (fun f : newSource S W hW hRange hContains hK U hGood E hExtra ⟶ X =>
    f.hom.left.base z ∈ K) (projection_square S W hW hRange hContains hK U hGood E hExtra))

theorem compact_image : (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base ''
    compact S (V) (hV) (vRange) = compact S W hW hRange := by
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (Set.ext_iff.mp (compact_preimage S W hW hRange hContains hK U hGood E hExtra) y).mp hy
  · intro hz
    have hr : z ∈ range (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base := by
      apply (Set.ext_iff.mp (sourceMap_range S W hW hRange hContains hK U hGood E hExtra) z).mpr
      exact contains S W hW hRange hContains hK U hGood E hExtra hz
    obtain ⟨y,hy⟩ := hr
    refine ⟨y,(Set.ext_iff.mp (compact_preimage S W hW hRange hContains hK U hGood E hExtra) y).mpr ?_,hy⟩
    change (sourceMap S W hW hRange hContains hK U hGood E hExtra).hom.left.base y ∈ compact S W hW hRange
    exact (congrArg (fun z => z ∈ compact S W hW hRange) hy).mpr hz

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSPrescribedFibreShrink
