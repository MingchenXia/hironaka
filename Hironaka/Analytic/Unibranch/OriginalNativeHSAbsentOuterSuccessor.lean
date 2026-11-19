import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterInitialBound
import Hironaka.Analytic.Unibranch.OriginalNativeHSAbsentPhaseRestriction

/-! A genuine ABSENT actual outer successor compares its SAME old-prefix
and next-history restrictions over one internally chosen literal base.
Blueprint FIRST: original-native-hs-absent-outer-successor.tex.
No common clock or properness after an open map into a larger old source. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSAbsentOuterSuccessor
noncomputable section
open Hironaka HironakaEmbeddedNativeMorphism
  SourceReducedComplexSpace OriginalIntrinsicHSSuperlevels
  OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction

variable {B Y : SourceReducedComplexSpace} (h : PhysicalHistory B Y) (K : Set B.obj.left)
  (hK : IsCompact K)
  (hne : (Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus Y.obj ∩
    OriginalNativeHSOuterSuccessor.shadow h K).Nonempty)

local notation "B₀" => OriginalNativeHSOuterSuccessor.base h K hK hne
local notation "A" => OriginalNativeHSOuterSuccessor.oldSource h K hK hne
local notation "Z" => OriginalNativeHSOuterSuccessor.source h K hK hne
local notation "N₀" => OriginalNativeHSOuterSuccessor.neighbourhood h K hK hne
local notation "P" => OriginalNativeHSOuterSuccessor.phaseSuffix h K hK hne
local notation "R" => OriginalNativeHSOuterSuccessor.history h K hK hne
local notation "H" => OriginalNativeHSOuterInitialBound.profile h K hK hne

def oldPrefix : PhysicalHistory (B₀) (A) :=
  OriginalNativePhysicalHistoryRestriction.restrict h (N₀).openSet (N₀).compactClosure

private theorem oldPrefix_square : (oldPrefix h K hK hne).projection ≫ (N₀).inclusion =
    OriginalNativeHSOuterSuccessor.oldInclusion h K hK hne ≫ h.projection :=
  OriginalNativePhysicalHistoryRestriction.projection_square h (N₀).openSet (N₀).compactClosure

/-- FULL actual factorization over the computed base, not merely an endpoint point square. -/
theorem next_projection_factorization : (R).projection =
    (P).projection ≫ (oldPrefix h K hK hne).projection := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  have hn := congrArg (fun f : (Z) ⟶ B => f.hom.left.base z)
    (OriginalNativeHSOuterSuccessor.original_projection_factorization h K hK hne)
  have ho := congrArg (fun f : (A) ⟶ B => f.hom.left.base ((P).projection.hom.left.base z))
    (oldPrefix_square h K hK hne)
  exact hn.trans ho.symm

variable (L : Set (OriginalNativeHSOuterSuccessor.base h K hK hne).obj.left) (hL : IsCompact L)

def oldFibre : Set (A).obj.left :=
  fun a : (A).obj.left => (oldPrefix h K hK hne).projection.hom.left.base a ∈ L

include hL in
theorem oldFibre_isCompact : IsCompact (oldFibre h K hK hne L) :=
  (oldPrefix h K hK hne).singularModification.isProperMap.isCompact_preimage hL

private theorem suffix_off : IsIsoOver (P).projection (originalSingularHSThreshold (A) (H))ᶜ :=
  OriginalNativeHSOuterSuccessor.phaseSuffix_off_threshold h K hK hne

variable (hEmpty : oldFibre h K hK hne L ∩
  originalSingularHSThreshold (OriginalNativeHSOuterSuccessor.oldSource h K hK hne)
    (OriginalNativeHSOuterInitialBound.profile h K hK hne) = ∅)

private abbrev skipNeighbourhood := OriginalNativeHSAbsentPhaseRestriction.neighbourhood (P) (H)
  (oldFibre h K hK hne L) (oldFibre_isCompact h K hK hne L hL) (suffix_off h K hK hne) hEmpty
private abbrev skipComparison := OriginalNativeHSAbsentPhaseRestriction.comparison (P) (H)
  (oldFibre h K hK hne L) (oldFibre_isCompact h K hK hne L hL) (suffix_off h K hK hne) hEmpty
private abbrev skipSource := preimageRestriction (skipNeighbourhood h K hK hne L hL hEmpty).openSet
  (P).projection (skipNeighbourhood h K hK hne L hL hEmpty).compactClosure (P).singularModification.isProperMap
private abbrev skipSourceInclusion : skipSource h K hK hne L hL hEmpty ⟶ (Z) :=
  inclusion (Z) (preimageOpen (skipNeighbourhood h K hK hne L hL hEmpty).openSet (P).projection)
    (isCompact_closure_preimage _ _ (skipNeighbourhood h K hK hne L hL hEmpty).compactClosure
      (P).singularModification.isProperMap)

private theorem skip_square : (skipComparison h K hK hne L hL hEmpty).hom ≫
    (skipNeighbourhood h K hK hne L hL hEmpty).inclusion =
      skipSourceInclusion h K hK hne L hL hEmpty ≫ (P).projection :=
  OriginalNativeHSAbsentPhaseRestriction.comparison_square (P) (H) (oldFibre h K hK hne L)
    (oldFibre_isCompact h K hK hne L hL) (suffix_off h K hK hne) hEmpty

private theorem oldFibre_good : (oldPrefix h K hK hne).projection.hom.left.base ⁻¹' L ⊆
    ((skipNeighbourhood h K hK hne L hL hEmpty).openSet : Set (A).obj.left) :=
  (skipNeighbourhood h K hK hne L hL hEmpty).contains

/-- Actual base shrink retaining ALL smaller compact points and their whole good old fibres. -/
def neighbourhood := OriginalNativeProperFibreShrink.neighbourhood (oldPrefix h K hK hne).projection
  (oldPrefix h K hK hne).singularModification.isProperMap
  (skipNeighbourhood h K hK hne L hL hEmpty).openSet L hL (oldFibre_good h K hK hne L hL hEmpty)

theorem compact_retained : L ⊆ range (neighbourhood h K hK hne L hL hEmpty).inclusion.hom.left.base := by
  intro x hx
  exact ⟨⟨x,(neighbourhood h K hK hne L hL hEmpty).contains hx⟩,rfl⟩

private theorem whole_closure_good : (oldPrefix h K hK hne).projection.hom.left.base ⁻¹'
    closure ((neighbourhood h K hK hne L hL hEmpty).openSet : Set (B₀).obj.left) ⊆
      ((skipNeighbourhood h K hK hne L hL hEmpty).openSet : Set (A).obj.left) := by
  intro y hy
  apply OriginalNativeProperFibreShrink.preimage_goodBase_subset (oldPrefix h K hK hne).projection
    (oldPrefix h K hK hne).singularModification.isProperMap
    (skipNeighbourhood h K hK hne L hL hEmpty).openSet
  exact (neighbourhood h K hK hne L hL hEmpty).closure_subset hy

/-- The ENTIRE old threshold fibre stays absent over the closure of the chosen base. -/
theorem old_threshold_fibre_empty :
    ((oldPrefix h K hK hne).projection.hom.left.base ⁻¹'
      closure ((neighbourhood h K hK hne L hL hEmpty).openSet : Set (B₀).obj.left)) ∩
        originalSingularHSThreshold (A) (H) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro a ⟨ha,ht⟩
  have hg := whole_closure_good h K hK hne L hL hEmpty ha
  exact (skipNeighbourhood h K hK hne L hL hEmpty).closure_subset (subset_closure hg) ht

private abbrev localOpen : Opens (B₀).obj.left := (neighbourhood h K hK hne L hL hEmpty).openSet
private theorem localOpen_compact : IsCompact (closure (localOpen h K hK hne L hL hEmpty : Set (B₀).obj.left)) :=
  (neighbourhood h K hK hne L hL hEmpty).compactClosure
local notation "U" => localOpen h K hK hne L hL hEmpty
local notation "hU" => localOpen_compact h K hK hne L hL hEmpty

abbrev oldSource : SourceReducedComplexSpace := preimageRestriction (U)
  (oldPrefix h K hK hne).projection (hU) (oldPrefix h K hK hne).singularModification.isProperMap
abbrev nextSource : SourceReducedComplexSpace := preimageRestriction (U)
  (R).projection (hU) (R).singularModification.isProperMap

def oldHistory : PhysicalHistory (neighbourhood h K hK hne L hL hEmpty).source
    (oldSource h K hK hne L hL hEmpty) :=
  OriginalNativePhysicalHistoryRestriction.restrict (oldPrefix h K hK hne) (U) (hU)
def nextHistory : PhysicalHistory (neighbourhood h K hK hne L hL hEmpty).source
    (nextSource h K hK hne L hL hEmpty) :=
  OriginalNativePhysicalHistoryRestriction.restrict (R) (U) (hU)

def oldInclusion : oldSource h K hK hne L hL hEmpty ⟶ (A) :=
  inclusion (A) (preimageOpen (U) (oldPrefix h K hK hne).projection)
    (isCompact_closure_preimage _ _ (hU) (oldPrefix h K hK hne).singularModification.isProperMap)
def nextInclusion : nextSource h K hK hne L hL hEmpty ⟶ (Z) :=
  inclusion (Z) (preimageOpen (U) (R).projection)
    (isCompact_closure_preimage _ _ (hU) (R).singularModification.isProperMap)

theorem old_length : (oldHistory h K hK hne L hL hEmpty).length = h.length :=
  (OriginalNativePhysicalHistoryRestriction.length_restrict (oldPrefix h K hK hne) (U) (hU)).trans
    (OriginalNativePhysicalHistoryRestriction.length_restrict h (N₀).openSet (N₀).compactClosure)

theorem next_length : (nextHistory h K hK hne L hL hEmpty).length = (R).length :=
  OriginalNativePhysicalHistoryRestriction.length_restrict (R) (U) (hU)

private theorem next_range_in_skip : range (nextInclusion h K hK hne L hL hEmpty).hom.left.base ⊆
    range (skipSourceInclusion h K hK hne L hL hEmpty).hom.left.base := by
  rintro _ ⟨z,rfl⟩
  have hz : (oldPrefix h K hK hne).projection.hom.left.base ((P).projection.hom.left.base z.val) ∈ (U) := by
    have e := congrArg (fun f : (Z) ⟶ (B₀) => f.hom.left.base z.val)
      (next_projection_factorization h K hK hne)
    exact e ▸ z.property
  exact ⟨⟨z.val,whole_closure_good h K hK hne L hL hEmpty (subset_closure hz)⟩,rfl⟩

private def toSkip : nextSource h K hK hne L hL hEmpty ⟶ skipSource h K hK hne L hL hEmpty := by
  let : LocallyRingedSpace.IsOpenImmersion (skipSourceInclusion h K hK hne L hL hEmpty).hom.left :=
    inclusion_isOpenImmersion _ _ _
  let a := LocallyRingedSpace.IsOpenImmersion.lift
    (skipSourceInclusion h K hK hne L hL hEmpty).hom.left
    (nextInclusion h K hK hne L hL hEmpty).hom.left
    (next_range_in_skip h K hK hne L hL hEmpty)
  have hf : a ≫ (skipSourceInclusion h K hK hne L hL hEmpty).hom.left =
      (nextInclusion h K hK hne L hL hEmpty).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  apply ObjectProperty.homMk
  refine Over.homMk a ?_
  calc
    _ = a ≫ ((skipSourceInclusion h K hK hne L hL hEmpty).hom.left ≫ (Z).obj.hom) := rfl
    _ = (a ≫ (skipSourceInclusion h K hK hne L hL hEmpty).hom.left) ≫ (Z).obj.hom :=
      (Category.assoc _ _ _).symm
    _ = (nextInclusion h K hK hne L hL hEmpty).hom.left ≫ (Z).obj.hom :=
      congrArg (fun f => f ≫ (Z).obj.hom) hf
    _ = _ := Over.w (nextInclusion h K hK hne L hL hEmpty).hom

private theorem toSkip_square : toSkip h K hK hne L hL hEmpty ≫
    skipSourceInclusion h K hK hne L hL hEmpty = nextInclusion h K hK hne L hL hEmpty := by
  let : LocallyRingedSpace.IsOpenImmersion (skipSourceInclusion h K hK hne L hL hEmpty).hom.left :=
    inclusion_isOpenImmersion _ _ _
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac
    (skipSourceInclusion h K hK hne L hL hEmpty).hom.left
    (nextInclusion h K hK hne L hL hEmpty).hom.left (next_range_in_skip h K hK hne L hL hEmpty)

private theorem toSkip_open : LocallyRingedSpace.IsOpenImmersion
    (toSkip h K hK hne L hL hEmpty).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion (skipSourceInclusion h K hK hne L hL hEmpty).hom.left :=
    inclusion_isOpenImmersion _ _ _
  let : LocallyRingedSpace.IsOpenImmersion (nextInclusion h K hK hne L hL hEmpty).hom.left :=
    inclusion_isOpenImmersion _ _ _
  let : IsIso (CategoryTheory.Limits.pullback.snd
    (skipSourceInclusion h K hK hne L hL hEmpty).hom.left
    (nextInclusion h K hK hne L hL hEmpty).hom.left) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _
      (next_range_in_skip h K hK hne L hL hEmpty)
  change LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift
    (skipSourceInclusion h K hK hne L hL hEmpty).hom.left
    (nextInclusion h K hK hne L hL hEmpty).hom.left (next_range_in_skip h K hK hne L hL hEmpty))
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private def nextMap : nextSource h K hK hne L hL hEmpty ⟶ (A) :=
  toSkip h K hK hne L hL hEmpty ≫ (skipComparison h K hK hne L hL hEmpty).hom ≫
    (skipNeighbourhood h K hK hne L hL hEmpty).inclusion

private theorem nextMap_square : nextMap h K hK hne L hL hEmpty =
    nextInclusion h K hK hne L hL hEmpty ≫ (P).projection := by
  change toSkip h K hK hne L hL hEmpty ≫
    ((skipComparison h K hK hne L hL hEmpty).hom ≫
      (skipNeighbourhood h K hK hne L hL hEmpty).inclusion) = _
  rw [skip_square, ← Category.assoc, toSkip_square]

private theorem nextMap_open : LocallyRingedSpace.IsOpenImmersion
    (nextMap h K hK hne L hL hEmpty).hom.left := by
  have hs : LocallyRingedSpace.IsOpenImmersion (skipComparison h K hK hne L hL hEmpty).hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (skipComparison h K hK hne L hL hEmpty)).hom
    infer_instance
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (toSkip h K hK hne L hL hEmpty).hom.left (toSkip_open h K hK hne L hL hEmpty)
    ((skipComparison h K hK hne L hL hEmpty).hom ≫
      (skipNeighbourhood h K hK hne L hL hEmpty).inclusion).hom.left
    (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (skipComparison h K hK hne L hL hEmpty).hom.hom.left hs
      (skipNeighbourhood h K hK hne L hL hEmpty).inclusion.hom.left
      (skipNeighbourhood h K hK hne L hL hEmpty).inclusion_isOpenImmersion)

private theorem comparisonRange : range (nextMap h K hK hne L hL hEmpty).hom.left.base =
    range (oldInclusion h K hK hne L hL hEmpty).hom.left.base := by
  rw [nextMap_square]
  change range (fun z : preimageOpen (U) (R).projection => (P).projection.hom.left.base z.val) =
    range (Subtype.val : preimageOpen (U) (oldPrefix h K hK hne).projection → (A).obj.left)
  rw [Subtype.range_coe]
  ext a
  constructor
  · rintro ⟨z,rfl⟩
    change (oldPrefix h K hK hne).projection.hom.left.base ((P).projection.hom.left.base z.val) ∈ (U)
    have e := congrArg (fun f : (Z) ⟶ (B₀) => f.hom.left.base z.val)
      (next_projection_factorization h K hK hne)
    exact e ▸ z.property
  · intro ha
    change (oldPrefix h K hK hne).projection.hom.left.base a ∈ (U) at ha
    have haO := whole_closure_good h K hK hne L hL hEmpty (subset_closure ha)
    let aO : (skipNeighbourhood h K hK hne L hL hEmpty).source.obj.left := ⟨a,haO⟩
    let zO := (skipComparison h K hK hne L hL hEmpty).inv.hom.left.base aO
    have hpz : (P).projection.hom.left.base zO.val = a := by
      have hf := OriginalNativeHSAbsentPhaseRestriction.comparison_inverse_square (P) (H)
        (oldFibre h K hK hne L) (oldFibre_isCompact h K hK hne L hL) (suffix_off h K hK hne) hEmpty
      exact congrArg (fun f => f.hom.left.base aO) hf
    have hz : (R).projection.hom.left.base zO.val ∈ (U) := by
      have e := congrArg (fun f : (Z) ⟶ (B₀) => f.hom.left.base zO.val)
        (next_projection_factorization h K hK hne)
      have hqp : (oldPrefix h K hK hne).projection.hom.left.base ((P).projection.hom.left.base zO.val) ∈ (U) := by
        rw [hpz]
        exact ha
      exact e.symm ▸ hqp
    exact ⟨⟨zO.val,hz⟩,hpz⟩

private def rawComparison : (nextSource h K hK hne L hL hEmpty).obj.left ≅
    (oldSource h K hK hne L hL hEmpty).obj.left := by
  let : LocallyRingedSpace.IsOpenImmersion (nextMap h K hK hne L hL hEmpty).hom.left :=
    nextMap_open h K hK hne L hL hEmpty
  let : LocallyRingedSpace.IsOpenImmersion (oldInclusion h K hK hne L hL hEmpty).hom.left :=
    inclusion_isOpenImmersion _ _ _
  exact openImmersionIsoOfRangeEq (nextMap h K hK hne L hL hEmpty).hom.left
    (oldInclusion h K hK hne L hL hEmpty).hom.left (comparisonRange h K hK hne L hL hEmpty)

private theorem rawComparison_square : (rawComparison h K hK hne L hL hEmpty).hom ≫
    (oldInclusion h K hK hne L hL hEmpty).hom.left =
      (nextMap h K hK hne L hL hEmpty).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion (nextMap h K hK hne L hL hEmpty).hom.left :=
    nextMap_open h K hK hne L hL hEmpty
  let : LocallyRingedSpace.IsOpenImmersion (oldInclusion h K hK hne L hL hEmpty).hom.left :=
    inclusion_isOpenImmersion _ _ _
  exact openImmersionIsoOfRangeEq_hom_fac _ _ (comparisonRange h K hK hne L hL hEmpty)

/-- The SAME old-prefix and actual next-history literal endpoints over one derived base. -/
def comparison : nextSource h K hK hne L hL hEmpty ≅ oldSource h K hK hne L hL hEmpty := by
  let E := rawComparison h K hK hne L hL hEmpty
  have hs : E.hom ≫ (oldSource h K hK hne L hL hEmpty).obj.hom =
      (nextSource h K hK hne L hL hEmpty).obj.hom := by
    calc
      _ = E.hom ≫ ((oldInclusion h K hK hne L hL hEmpty).hom.left ≫ (A).obj.hom) := rfl
      _ = (E.hom ≫ (oldInclusion h K hK hne L hL hEmpty).hom.left) ≫ (A).obj.hom :=
        (Category.assoc _ _ _).symm
      _ = (nextMap h K hK hne L hL hEmpty).hom.left ≫ (A).obj.hom :=
        congrArg (fun f => f ≫ (A).obj.hom) (rawComparison_square h K hK hne L hL hEmpty)
      _ = _ := Over.w (nextMap h K hK hne L hL hEmpty).hom
  exact ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk E hs)

theorem comparison_suffix_square : (comparison h K hK hne L hL hEmpty).hom ≫
    oldInclusion h K hK hne L hL hEmpty = nextInclusion h K hK hne L hL hEmpty ≫ (P).projection := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact (rawComparison_square h K hK hne L hL hEmpty).trans
    (congrArg (fun f => f.hom.left) (nextMap_square h K hK hne L hL hEmpty))

/-- FULL actual projection equality on the common literal derived base. -/
theorem comparison_projection : (comparison h K hK hne L hL hEmpty).hom ≫
    (oldHistory h K hK hne L hL hEmpty).projection = (nextHistory h K hK hne L hL hEmpty).projection := by
  have hs : ((comparison h K hK hne L hL hEmpty).hom ≫
      (oldHistory h K hK hne L hL hEmpty).projection) ≫
        (neighbourhood h K hK hne L hL hEmpty).inclusion =
      (nextHistory h K hK hne L hL hEmpty).projection ≫
        (neighbourhood h K hK hne L hL hEmpty).inclusion := by
    calc
      _ = (comparison h K hK hne L hL hEmpty).hom ≫
          ((oldHistory h K hK hne L hL hEmpty).projection ≫
            (neighbourhood h K hK hne L hL hEmpty).inclusion) := Category.assoc _ _ _
      _ = (comparison h K hK hne L hL hEmpty).hom ≫
          (oldInclusion h K hK hne L hL hEmpty ≫ (oldPrefix h K hK hne).projection) :=
        congrArg (fun f => (comparison h K hK hne L hL hEmpty).hom ≫ f)
          (OriginalNativePhysicalHistoryRestriction.projection_square (oldPrefix h K hK hne) (U) (hU))
      _ = ((comparison h K hK hne L hL hEmpty).hom ≫ oldInclusion h K hK hne L hL hEmpty) ≫
          (oldPrefix h K hK hne).projection := (Category.assoc _ _ _).symm
      _ = (nextInclusion h K hK hne L hL hEmpty ≫ (P).projection) ≫ (oldPrefix h K hK hne).projection :=
        congrArg (fun f => f ≫ (oldPrefix h K hK hne).projection)
          (comparison_suffix_square h K hK hne L hL hEmpty)
      _ = nextInclusion h K hK hne L hL hEmpty ≫ (R).projection := by
        rw [Category.assoc, ← next_projection_factorization]
      _ = _ := (OriginalNativePhysicalHistoryRestriction.projection_square (R) (U) (hU)).symm
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  exact congrArg (fun f => f.hom.left.base z) hs

theorem comparison_original_source_square : (comparison h K hK hne L hL hEmpty).hom ≫
    oldInclusion h K hK hne L hL hEmpty ≫ OriginalNativeHSOuterSuccessor.oldInclusion h K hK hne =
      nextInclusion h K hK hne L hL hEmpty ≫ OriginalNativeHSOuterSuccessor.sourceMap h K hK hne := by
  rw [← Category.assoc, comparison_suffix_square, Category.assoc,
    OriginalNativeHSOuterSuccessor.phaseSuffix_old_square]

theorem comparison_original_base_square : (comparison h K hK hne L hL hEmpty).hom ≫
    (oldHistory h K hK hne L hL hEmpty).projection ≫
      (neighbourhood h K hK hne L hL hEmpty).inclusion ≫ (N₀).inclusion =
    (nextHistory h K hK hne L hL hEmpty).projection ≫
      (neighbourhood h K hK hne L hL hEmpty).inclusion ≫ (N₀).inclusion := by
  rw [← Category.assoc, ← Category.assoc, comparison_projection, Category.assoc]

theorem comparison_inverse_projection : (comparison h K hK hne L hL hEmpty).inv ≫
    (nextHistory h K hK hne L hL hEmpty).projection = (oldHistory h K hK hne L hL hEmpty).projection := by
  rw [← comparison_projection, Iso.inv_hom_id_assoc]

theorem comparison_scalar : (comparison h K hK hne L hL hEmpty).hom.hom.left ≫
    (oldSource h K hK hne L hL hEmpty).obj.hom = (nextSource h K hK hne L hL hEmpty).obj.hom :=
  Over.w (comparison h K hK hne L hL hEmpty).hom.hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSAbsentOuterSuccessor
