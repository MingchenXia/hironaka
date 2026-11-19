import Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSReadout
import Hironaka.Analytic.Unibranch.HironakaG1NativeWindowInitialClass
import Hironaka.Analytic.Unibranch.OriginalNativeCentreLocalClosedness
import Hironaka.Analytic.Unibranch.OriginalNativeShadowCommonCentre

/-! Construct the SAME actual current centre family and its OWN next native
blowup. True univ self-coverage is used, without compact univ footprints.
Blueprint FIRST: original-native-current-centre-blowup.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeCurrentCentreBlowup
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11HSPhaseInduction HironakaG11PresReduction HironakaG11InvBMClass
  HironakaG1CanonicalStageCentreIdeal HironakaG8LocalHistory
  HironakaG11ManifoldWindowCentres OriginalNativeCurrentHSReadout
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11SingularCentreModification
  HironakaIntrinsicReducedCentreIdealSheaf SmoothCentreModification
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain)

variable {X : SourceReducedComplexSpace} {N : ℕ} {ι : Type*}
  (w : ι → DimEmbedding X N) (raw : ∀ i, MarkedIdeal N (Amb w i))
  (H : ℕ → ℕ) (hRaw : ∀ i, IsNativeWindowRecord (w i) (raw i) H)
  (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
  (hd : ∀ i j, (chosenRecord w raw e i).d = (chosenRecord w raw e j).d)
  {Λ : Type*} [LinearOrder Λ]
  (B : BMInvariant.{0} N (fun {Y} A A' => LocWPEquiv (X := Y) A A') N Λ)

include hRaw he in
theorem domain (i : ι) : IsInvDomain N (chosenRecord w raw e i) :=
  (chosen_isHSWindowRecord w raw e hRaw he i).1

include hRaw he in
theorem presentation (i : ι) : HSPresentation B.toResolutionInvariant
    (w i) (chosenRecord w raw e i) H :=
  chosen_presentation w raw e hRaw he B.toResolutionInvariant i

include hRaw he B in
theorem initial_cosupp_subset (i : ι) : (chosenRecord w raw e i).cosupp ⊆ (w i).carrier :=
  HSPresentation.cosupp_subset (fun i => presentation w raw H hRaw e he B i) i

/-- TRUE self-coverage; no compactness of univ is asserted. -/
theorem selfCover (i : ι) (c : (w i).carrier) (_hc : c.val ∈ (chosenRecord w raw e i).cosupp) :
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ (univ : Set (w j).ambient) ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c :=
  ⟨i, c, mem_univ _, rfl⟩

include hRaw he hd in
private theorem initialClass : InitialClassData w (chosenRecord w raw e) :=
  HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers w raw H hRaw e he hd

include hRaw he hd in
theorem recordsTransport : RecordsTransport B.toResolutionInvariant (chosenRecord w raw e) (mapAdm w) :=
  HironakaG1CanonicalStageCentreIdeal.recordsTransport w (chosenRecord w raw e) B
    (domain w raw H hRaw e he) (initialClass w raw H hRaw e he hd)

variable {m : ℕ} (s : GStage B.toResolutionInvariant (chosenRecord w raw e) (mapAdm w) m)
  (xs : XStage w s.T)

include hRaw he in
theorem current_cosupp_subset (i : ι) : rcos (chosenRecord w raw e) s.T i ⊆ xs.carrier i := by
  rw [xs.carrier_eq i]
  exact (presentation w raw H hRaw e he B i (s.T i).2 (s.canonical i)).1

/-- The LITERAL held canonical family with auxiliary footprints univ. -/
def centres : ManifoldSmoothCentres xs.Y ι :=
  xs.centres (K := fun _ => univ) (domain w raw H hRaw e he)
    (initial_cosupp_subset w raw H hRaw e he B) (selfCover w raw e)
    (recordsTransport w raw H hRaw e he hd B) s
    (fun i _ hy => current_cosupp_subset w raw H hRaw e he B s xs i hy.1)

theorem centres_compatible : (centres w raw H hRaw e he hd B s xs).Compatible :=
  xs.centres_compatible (K := fun _ => univ) (domain w raw H hRaw e he)
    (initial_cosupp_subset w raw H hRaw e he B) (selfCover w raw e)
    (recordsTransport w raw H hRaw e he hd B) s
    (fun i _ hy => current_cosupp_subset w raw H hRaw e he B s xs i hy.1)

local notation "F" => centres w raw H hRaw e he hd B s xs
local notation "C" => originalSingularHSThreshold xs.Y H

theorem support_threshold : (F).support ⊆ C := by
  intro y hy
  obtain ⟨i, c, hc, rfl⟩ := (F).mem_support.mp hy
  have ht := current_native_data w raw e hRaw he B.toResolutionInvariant s xs i c
  exact ⟨ht.2.2 hc.1, fun l => (congrFun (ht.2.1.mp hc.1) l).ge⟩

theorem support_singular : (F).support ⊆ intrinsicSingularLocus xs.Y.obj :=
  fun _ hy => (support_threshold w raw H hRaw e he hd B s xs hy).1

variable (l : Λ)
  (hBound : ∀ i (c : xs.carrier i), c.val ∈ rcos (chosenRecord w raw e) s.T i →
    rvalue B.toResolutionInvariant (chosenRecord w raw e) s.T i c.val ≤ l)
  (hAtt : ∃ i, ∃ c : xs.carrier i, c.val ∈ rcos (chosenRecord w raw e) s.T i ∧
    rvalue B.toResolutionInvariant (chosenRecord w raw e) s.T i c.val = l)

include hRaw he hBound hAtt in
theorem greatest : IsGreatest
    (gfootValues B.toResolutionInvariant (chosenRecord w raw e) (fun _ => univ) s.T) l := by
  obtain ⟨i, c, hc, hv⟩ := hAtt
  refine ⟨mem_iUnion.mpr ⟨i, c.val, ⟨hc, mem_univ _⟩, hv⟩, ?_⟩
  rintro v hv
  obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hv
  exact hBound j ⟨z, current_cosupp_subset w raw H hRaw e he B s xs j hz.1⟩ hz.1

include hBound hAtt in
theorem centre_eq_level (i : ι) : (F).centre i =
    {y | y ∈ rcos (chosenRecord w raw e) s.T i ∧
      rvalue B.toResolutionInvariant (chosenRecord w raw e) s.T i y = l} := by
  ext y
  constructor
  · rintro ⟨hy, hUpper⟩
    exact ⟨hy, le_antisymm
      (hBound i ⟨y, current_cosupp_subset w raw H hRaw e he B s xs i hy⟩ hy)
      (hUpper (greatest w raw H hRaw e he B s xs l hBound hAtt).1)⟩
  · rintro ⟨hy, hv⟩
    refine ⟨hy, ?_⟩
    rw [hv]
    exact (greatest w raw H hRaw e he B s xs l hBound hAtt).2

include hBound hAtt in
theorem support_eq_levelSupport : (F).support =
    OriginalNativeShadowCommonCentre.levelSupport w (chosenRecord w raw e) B s xs id l := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, c, hc, hcy⟩ := (F).mem_support.mp hy
    exact mem_iUnion.mpr ⟨i, c, (Set.ext_iff.mp
      (centre_eq_level w raw H hRaw e he hd B s xs l hBound hAtt i) c.val).mp hc, hcy⟩
  · intro hy
    obtain ⟨i, c, hc, hcy⟩ := mem_iUnion.mp hy
    exact (F).mem_support.mpr ⟨i, c, (Set.ext_iff.mp
      (centre_eq_level w raw H hRaw e he hd B s xs l hBound hAtt i) c.val).mpr hc, hcy⟩

include hBound in
theorem mem_support_of_value_eq (i : ι) (c : xs.carrier i)
    (hc : c.val ∈ rcos (chosenRecord w raw e) s.T i)
    (hv : rvalue B.toResolutionInvariant (chosenRecord w raw e) s.T i c.val = l) :
    (xs.map i).hom.left.base c ∈ (F).support := by
  exact (F).mem_support.mpr ⟨i, c, (Set.ext_iff.mp
    (centre_eq_level w raw H hRaw e he hd B s xs l hBound ⟨i, c, hc, hv⟩ i) c.val).mpr ⟨hc, hv⟩, rfl⟩

private theorem closed_threshold (Y : SourceReducedComplexSpace) (H : ℕ → ℕ) :
    IsClosed (originalSingularHSThreshold Y H) :=
  (original_hs_threshold_dictionary Y H).2.1.isClosed

variable (hCover : originalSingularHSThreshold xs.Y H ⊆ ⋃ i, range (xs.map i).hom.left.base)

include hCover in
theorem threshold_covered_local : C ⊆ OriginalNativeCentreLocalClosedness.coveredOpen (F).toLocal := by
  intro y hy
  obtain ⟨i, c, rfl⟩ := mem_iUnion.mp (hCover hy)
  obtain ⟨d, hd⟩ := (F).exists_chartPoint_eq i c
  refine mem_iUnion.mpr ⟨⟨i, c.val⟩, d, ?_⟩
  rw [(F).toLocal_windowMap_apply, hd]
  rfl

include hCover in
theorem closedness_neighbourhood_eq_univ :
    OriginalNativeCentreLocalClosedness.neighbourhood (F).toLocal C (closed_threshold xs.Y H) = ⊤ := by
  apply top_unique
  intro y _
  by_cases hyC : y ∈ C
  · exact Or.inl (threshold_covered_local w raw H hRaw e he hd B s xs hCover hyC)
  · exact Or.inr hyC

include hCover in
theorem support_closed : IsClosed (F).support := by
  have hc := centres_compatible w raw H hRaw e he hd B s xs
  have hFD : (F).toLocal.support ⊆ C := by
    rw [(F).support_toLocal hc]
    exact support_threshold w raw H hRaw e he hd B s xs
  have hcl := OriginalNativeCentreLocalClosedness.native_preimage_closed (F).toLocal C
    (closed_threshold xs.Y H) ((F).compatible_toLocal hc) hFD (𝟙 xs.Y)
    (by rw [closedness_neighbourhood_eq_univ w raw H hRaw e he hd B s xs hCover]; exact subset_univ _)
  change IsClosed (F).toLocal.support at hcl
  rwa [(F).support_toLocal hc] at hcl

/-- The ACTUAL constructed full native next step, never an input packet. -/
structure Step where
  centre_analytic : xs.Y.IsAnalyticSubset (F).support
  source : SourceReducedComplexSpace
  projection : source ⟶ xs.Y
  blowup : IsSmoothCentreBlowup projection
    (OriginalAnalyticClosedSubspace.inclusion xs.Y (F).support centre_analytic)
  singular : IsSingularCentreStep projection
  surjective : Function.Surjective projection.hom.left.base
  isoOver : IsIsoOver projection (F).supportᶜ

include hCover in
theorem exists_step : Nonempty (Step w raw H hRaw e he hd B s xs) := by
  obtain ⟨hS, Y, p, hb, hs, -, hsurj, hi⟩ := (F).exists_singularCentreBlowup
    (centres_compatible w raw H hRaw e he hd B s xs)
    (support_closed w raw H hRaw e he hd B s xs hCover)
    (support_singular w raw H hRaw e he hd B s xs)
  exact ⟨⟨hS, Y, p, hb, hs, hsurj, hi⟩⟩

def step : Step w raw H hRaw e he hd B s xs :=
  (exists_step w raw H hRaw e he hd B s xs hCover).some

namespace Step
variable (t : Step w raw H hRaw e he hd B s xs)

theorem isIdealBlowup : IsIdealBlowup t.projection
    (intrinsicReducedCentreIdealModule xs.Y.obj.left (F).support)
    (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (F).support) := by
  have h := t.blowup.2.2.2.2.2.1
  rw [OriginalAnalyticClosedSubspace.inclusion_range] at h
  exact h

theorem proper : IsProperMap t.projection.hom.left.base :=
  t.singular.isSingularCentreModification.isProperMap

theorem scalar : t.projection.hom.left ≫ xs.Y.obj.hom = t.source.obj.hom :=
  Over.w t.projection.hom

theorem originalRegular : IsIsoOver (t.projection ≫ xs.q) (intrinsicRegularLocus X.obj) :=
  (IsSingularCentreModification.cons t.projection xs.q t.singular
    xs.isSingularCentreModification).isIsoOver_intrinsicRegularLocus

theorem originalScalar : (t.projection ≫ xs.q).hom.left ≫ X.obj.hom = t.source.obj.hom :=
  Over.w (t.projection ≫ xs.q).hom

end Step
end
end Hironaka.Analytic.Unibranch.OriginalNativeCurrentCentreBlowup
