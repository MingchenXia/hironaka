import Hironaka.Analytic.Unibranch.HironakaG11PresReduction

/-! Genuine ordinary native HS window geometry near a COMPACT SHADOW in
an arbitrary original reduced analytic space, with no CompactSpace X.
Blueprint FIRST: original-native-hs-compact-shadow-windows.tex.
No whole-cosupport compactness, compact-driver or dynamic-phase claim. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCompactShadowWindows
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11PresReduction HironakaG11HSMinimalWindows
  BlowupTowers MarkedIdeals

/-- Actual ordinary maximum ON K, with no assertion outside K. -/
structure Maximum (X : SourceReducedComplexSpace) (K : Set X.obj.left) where
  point : X.obj.left
  in_compact : point ∈ K
  singular : point ∈ intrinsicSingularLocus X.obj
  maximal : ∀ x ∈ K, x ∈ intrinsicSingularLocus X.obj →
    toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X point)

theorem exists_maximum (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) (hne : (K ∩ intrinsicSingularLocus X.obj).Nonempty) :
    Nonempty (Maximum X K) := by
  have hf0 : (originalStalkHS X '' (K ∩ intrinsicSingularLocus X.obj)).Finite :=
    (OriginalCompactIntrinsicHSProfiles.original_stalk_hs_finite_range_on_compact X K hK).subset
      (image_mono inter_subset_left)
  have hf : ((fun x => toLex (originalStalkHS X x)) ''
      (K ∩ intrinsicSingularLocus X.obj)).Finite := by
    simpa only [image_image, Function.comp_def] using hf0.image toLex
  obtain ⟨H, hH, hm⟩ := Set.exists_max_image _ id hf (hne.image _)
  obtain ⟨a, ha, rfl⟩ := hH
  exact ⟨⟨a, ha.1, ha.2, fun x hxK hxs => hm _ (mem_image_of_mem _ ⟨hxK, hxs⟩)⟩⟩

/-- Internally chosen from ordinary X and an actual nonempty compact singular shadow. -/
def maximum (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K)
    (hne : (K ∩ intrinsicSingularLocus X.obj).Nonempty) : Maximum X K :=
  (exists_maximum X K hK hne).some

namespace Maximum
variable {X : SourceReducedComplexSpace} {K : Set X.obj.left} (M : Maximum X K)

/-- Literal GLOBAL entire-profile threshold, not a chosen stratum packet. -/
def threshold : Set X.obj.left := originalSingularHSThreshold X (originalStalkHS X M.point)

theorem threshold_analytic : X.IsAnalyticSubset M.threshold :=
  (original_hs_threshold_dictionary X (originalStalkHS X M.point)).2.1

theorem threshold_closed : IsClosed M.threshold := M.threshold_analytic.isClosed

theorem shadow_dictionary :
    K ∩ M.threshold = K ∩ hsStratum X (originalStalkHS X M.point) := by
  ext x
  constructor
  · rintro ⟨hxK, hxs, ht⟩
    exact ⟨hxK, hxs, congrArg ofLex (le_antisymm (M.maximal x hxK hxs) (Pi.toLex_monotone ht))⟩
  · rintro ⟨hxK, hxs, heq⟩
    exact ⟨hxK, hxs, fun ℓ => (congrFun heq ℓ).ge⟩

theorem shadow_compact (hK : IsCompact K) : IsCompact (K ∩ M.threshold) :=
  hK.inter_right M.threshold_closed

theorem point_mem_shadow : M.point ∈ K ∩ M.threshold :=
  ⟨M.in_compact, M.singular, fun _ => le_rfl⟩

end Maximum

/-- Actual native records and compact footprints covering only the specified shadow. -/
structure ShadowWindows (X : SourceReducedComplexSpace) (H : ℕ → ℕ) (S : Set X.obj.left) where
  ι : Type
  finite : Finite ι
  window : ι → DimEmbedding X (H 1 - 1)
  record : ∀ i, MarkedIdeal (H 1 - 1) (Amb window i)
  footprint : ∀ i, Set (window i).ambient
  footprint_compact : ∀ i, IsCompact (footprint i)
  native : ∀ i, IsNativeWindowRecord (window i) (record i) H
  cover : S ⊆ ⋃ i, (window i).toLocalEmbedding.toPoint ''
    ((Subtype.val : (window i).carrier → (window i).ambient) ⁻¹' interior (footprint i))

attribute [instance] ShadowWindows.finite

namespace ShadowWindows
variable {X : SourceReducedComplexSpace} {H : ℕ → ℕ} {S : Set X.obj.left}
  (W : ShadowWindows X H S)

/-- The literal union of actual INTERIOR footprint images is native open. -/
def innerOpen : Opens X.obj.left :=
  ⟨⋃ i, (W.window i).toLocalEmbedding.toPoint ''
      ((Subtype.val : (W.window i).carrier → (W.window i).ambient) ⁻¹' interior (W.footprint i)),
    isOpen_iUnion (fun i => (W.window i).toLocalEmbedding.isOpenEmbedding_toPoint.isOpenMap _
      (isOpen_interior.preimage continuous_subtype_val))⟩

def windowCover : Set X.obj.left := ⋃ i, range (W.window i).toLocalEmbedding.toPoint

theorem innerOpen_subset_windowCover : (W.innerOpen : Set X.obj.left) ⊆ W.windowCover := by
  intro x hx
  obtain ⟨i, c, -, hc⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨i, c, hc⟩

end ShadowWindows

/-- Ordinary compact subset of a stratum; S may be empty. No full-stratum compactness. -/
theorem exists_shadow_windows (X : SourceReducedComplexSpace) (H : ℕ → ℕ)
    (S : Set X.obj.left) (hS : IsCompact S) (hsub : S ⊆ hsStratum X H) :
    Nonempty (ShadowWindows X H S) := by
  classical
  have hex : ∀ x : S, ∃ (w : DimEmbedding X (H 1 - 1))
      (R : MarkedIdeal (H 1 - 1) (CMfd.of (n := H 1 - 1) w.ambient)) (c : w.carrier)
      (F : Set w.ambient), IsCompact F ∧ c.val ∈ interior F ∧
      w.toLocalEmbedding.toPoint c = x.val ∧ range w.toLocalEmbedding.toPoint ⊆ univ ∧
      IsNativeWindowRecord w R H :=
    fun x => exists_native_state_window_at X H (hsub x.property) isOpen_univ trivial
  choose w R c F hF hcF hcx hrange hrec using hex
  let O : S → Set X.obj.left := fun x =>
    (w x).toLocalEmbedding.toPoint '' ((Subtype.val : (w x).carrier → (w x).ambient) ⁻¹' interior (F x))
  have hO : ∀ x, IsOpen (O x) := fun x =>
    (w x).toLocalEmbedding.isOpenEmbedding_toPoint.isOpenMap _
      (isOpen_interior.preimage continuous_subtype_val)
  have hcov : S ⊆ ⋃ x, O x := fun y hy =>
    mem_iUnion.mpr ⟨⟨y, hy⟩, c ⟨y, hy⟩, hcF ⟨y, hy⟩, hcx ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover O hO hcov
  refine ⟨⟨t, inferInstance, fun i => w i.val, fun i => R i.val, fun i => F i.val,
    fun i => hF i.val, fun i => hrec i.val, ?_⟩⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
  exact mem_iUnion.mpr ⟨⟨x, hxt⟩, hyx⟩

namespace Maximum
variable {X : SourceReducedComplexSpace} {K : Set X.obj.left} (M : Maximum X K) (hK : IsCompact K)

/-- All finite native windows are constructed INTERNALLY for the same literal selected shadow. -/
def windows : ShadowWindows X (originalStalkHS X M.point) (K ∩ M.threshold) :=
  (exists_shadow_windows X (originalStalkHS X M.point) (K ∩ M.threshold) (M.shadow_compact hK)
    (by intro x hx; rw [M.shadow_dictionary] at hx; exact hx.2)).some

def innerOpen : Opens X.obj.left := (M.windows hK).innerOpen

theorem shadow_subset_innerOpen : K ∩ M.threshold ⊆ M.innerOpen hK := (M.windows hK).cover

/-- Honest original open; no analytic structure on closure K and no open-para assumption. -/
def neighbourhood : Opens X.obj.left :=
  ⟨(M.threshold \ (M.innerOpen hK : Set X.obj.left))ᶜ,
    (M.threshold_closed.inter (M.innerOpen hK).isOpen.isClosed_compl).isOpen_compl⟩

theorem compact_subset_neighbourhood : K ⊆ M.neighbourhood hK := by
  intro x hx hbad
  exact hbad.2 (M.shadow_subset_innerOpen hK ⟨hx, hbad.1⟩)

theorem threshold_trace_subset_innerOpen :
    M.threshold ∩ (M.neighbourhood hK : Set X.obj.left) ⊆ M.innerOpen hK := by
  rintro x ⟨hxD, hxW⟩
  by_contra hxO
  exact hxW ⟨hxD, hxO⟩

theorem threshold_trace_subset_windowCover :
    M.threshold ∩ (M.neighbourhood hK : Set X.obj.left) ⊆ (M.windows hK).windowCover :=
  (M.threshold_trace_subset_innerOpen hK).trans (M.windows hK).innerOpen_subset_windowCover

end Maximum

/-- Ordinary arbitrary original X + compact K, with no supplied maximum/window/phase packet. -/
theorem exists_original_shadow_windows (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) (hne : (K ∩ intrinsicSingularLocus X.obj).Nonempty) :
    ∃ M : Maximum X K, K ⊆ M.neighbourhood hK ∧
      M.threshold ∩ (M.neighbourhood hK : Set X.obj.left) ⊆ (M.windows hK).windowCover := by
  let M := maximum X K hK hne
  exact ⟨M, M.compact_subset_neighbourhood hK, M.threshold_trace_subset_windowCover hK⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCompactShadowWindows
