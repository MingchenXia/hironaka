import Hironaka.Analytic.Unibranch.OriginalNativeHSCompactShadowWindows
import Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood

/-! A TRUE lex-HS barrier on a genuine original native neighbourhood of K.
Finite whole-profile image is used only on an ACTUAL compact buffer;
each higher profile is excluded by its OWN global pointwise threshold.
Blueprint FIRST: original-native-hs-compact-shadow-barrier.tex.
Static only: no dynamic invariant centre or noncompact phase termination. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCompactShadowBarrier
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalNativeHSCompactShadowWindows

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)

/-- Actual precompact buffer, inside the original threshold-window neighbourhood. -/
def buffer : OriginalNativePrecompactNeighbourhood.Neighbourhood X K (M.neighbourhood hK) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X K hK (M.neighbourhood hK)
    (M.compact_subset_neighbourhood hK)

/-- Literal entire HS image on the ACTUAL compact closure of the buffer. -/
def profiles : Finset (ℕ → ℕ) :=
  (OriginalCompactIntrinsicHSProfiles.original_stalk_hs_finite_range_on_compact X
    (closure ((buffer M hK).openSet : Set X.obj.left)) (buffer M hK).compactClosure).toFinset

theorem mem_profiles (G : ℕ → ℕ) : G ∈ profiles M hK ↔
    G ∈ originalStalkHS X '' closure ((buffer M hK).openSet : Set X.obj.left) :=
  Set.Finite.mem_toFinset _

def badProfiles : Finset (ℕ → ℕ) := by
  classical
  exact (profiles M hK).filter (fun G => toLex (originalStalkHS X M.point) < toLex G)

theorem mem_badProfiles (G : ℕ → ℕ) : G ∈ badProfiles M hK ↔
    G ∈ profiles M hK ∧ toLex (originalStalkHS X M.point) < toLex G := by
  classical
  exact Finset.mem_filter

/-- A FINITE union of genuine GLOBAL singular entire-profile thresholds. -/
def excluded : Set X.obj.left := ⋃ G ∈ badProfiles M hK, originalSingularHSThreshold X G

theorem excluded_closed : IsClosed (excluded M hK) :=
  isClosed_biUnion_finset (fun G _ => (original_hs_threshold_dictionary X G).2.1.isClosed)

theorem compact_avoids_excluded : K ⊆ (excluded M hK)ᶜ := by
  intro x hxK hxE
  obtain ⟨G, hG, hxs, ht⟩ := mem_iUnion₂.mp hxE
  have hlt := (mem_badProfiles M hK G).mp hG |>.2
  exact not_lt_of_ge ((Pi.toLex_monotone ht).trans (M.maximal x hxK hxs)) hlt

def lexOpen : Opens X.obj.left :=
  ⟨(buffer M hK).openSet \ excluded M hK,
    (buffer M hK).openSet.isOpen.inter (excluded_closed M hK).isOpen_compl⟩

theorem compact_subset_lexOpen : K ⊆ lexOpen M hK :=
  fun _ hx => ⟨(buffer M hK).contains hx, compact_avoids_excluded M hK hx⟩

/-- TRUE lex bound: an incomparable higher profile is excluded by ITS OWN threshold. -/
theorem singular_bound (x : X.obj.left) (hx : x ∈ lexOpen M hK)
    (hxs : x ∈ intrinsicSingularLocus X.obj) :
    toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X M.point) := by
  classical
  by_contra hnot
  have hprof : originalStalkHS X x ∈ profiles M hK :=
    (mem_profiles M hK _).mpr (mem_image_of_mem _ (subset_closure hx.1))
  have hbad : originalStalkHS X x ∈ badProfiles M hK :=
    (mem_badProfiles M hK _).mpr ⟨hprof, lt_of_not_ge hnot⟩
  exact hx.2 (mem_iUnion₂.mpr ⟨originalStalkHS X x, hbad, hxs, fun _ => le_rfl⟩)

/-- Shrink genuinely inside the derived actual lex-barrier open. -/
def nativeNeighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood X K (lexOpen M hK) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X K hK (lexOpen M hK)
    (compact_subset_lexOpen M hK)

def nativeSource : SourceReducedComplexSpace := (nativeNeighbourhood M hK).source

def nativeInclusion : nativeSource M hK ⟶ X := (nativeNeighbourhood M hK).inclusion

instance native_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (nativeInclusion M hK).hom.left :=
  (nativeNeighbourhood M hK).inclusion_isOpenImmersion

theorem native_scalar : (nativeInclusion M hK).hom.left ≫ X.obj.hom = (nativeSource M hK).obj.hom :=
  Over.w (nativeInclusion M hK).hom

theorem native_shadow_compact : IsCompact ((nativeInclusion M hK).hom.left.base ⁻¹' K) :=
  (nativeNeighbourhood M hK).shadow_compact hK

theorem compact_subset_native_range : K ⊆ range (nativeInclusion M hK).hom.left.base := by
  intro x hx
  change x ∈ range (nativeNeighbourhood M hK).inclusion.hom.left.base
  rw [(nativeNeighbourhood M hK).inclusion_range]
  exact (nativeNeighbourhood M hK).contains hx

theorem native_bound (y : (nativeSource M hK).obj.left)
    (hy : y ∈ intrinsicSingularLocus (nativeSource M hK).obj) :
    toLex (originalStalkHS (nativeSource M hK) y) ≤ toLex (originalStalkHS X M.point) := by
  let N := nativeNeighbourhood M hK
  let z : N.source.obj.left := y
  have hsing : N.inclusion.hom.left.base z ∈ intrinsicSingularLocus X.obj :=
    (Set.ext_iff.mp N.preimage_singular z).mpr hy
  have himage : N.inclusion.hom.left.base z ∈ N.openSet := by
    change z.val ∈ N.openSet
    exact z.property
  have h := singular_bound M hK (N.inclusion.hom.left.base z)
    (N.closure_subset (subset_closure himage)) hsing
  rw [N.hs z] at h
  exact h

/-- The SAME actual maximum point, retained in the new open by K-containment. -/
def nativePoint : (nativeSource M hK).obj.left :=
  ⟨M.point, (nativeNeighbourhood M hK).contains M.in_compact⟩

theorem nativePoint_image : (nativeInclusion M hK).hom.left.base (nativePoint M hK) = M.point := rfl

theorem nativePoint_singular : nativePoint M hK ∈ intrinsicSingularLocus (nativeSource M hK).obj := by
  have h : nativePoint M hK ∈ (nativeNeighbourhood M hK).inclusion.hom.left.base ⁻¹'
      intrinsicSingularLocus X.obj := by
    change M.point ∈ intrinsicSingularLocus X.obj
    exact M.singular
  exact (Set.ext_iff.mp (nativeNeighbourhood M hK).preimage_singular _).mp h

theorem nativePoint_hs : originalStalkHS (nativeSource M hK) (nativePoint M hK) =
    originalStalkHS X M.point := ((nativeNeighbourhood M hK).hs (nativePoint M hK)).symm

theorem native_maximal (y : (nativeSource M hK).obj.left)
    (hy : y ∈ intrinsicSingularLocus (nativeSource M hK).obj) :
    toLex (originalStalkHS (nativeSource M hK) y) ≤
      toLex (originalStalkHS (nativeSource M hK) (nativePoint M hK)) := by
  rw [nativePoint_hs M hK]
  exact native_bound M hK y hy

/-- All maxima, finite profiles, exclusions and native objects are internally available. -/
theorem exists_original_barrier (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) (hne : (K ∩ intrinsicSingularLocus X.obj).Nonempty) :
    ∃ M : Maximum X K,
      (nativePoint M hK ∈ intrinsicSingularLocus (nativeSource M hK).obj) ∧
      (∀ y ∈ intrinsicSingularLocus (nativeSource M hK).obj,
        toLex (originalStalkHS (nativeSource M hK) y) ≤
          toLex (originalStalkHS (nativeSource M hK) (nativePoint M hK))) ∧
      IsCompact ((nativeInclusion M hK).hom.left.base ⁻¹' K) ∧
      K ⊆ range (nativeInclusion M hK).hom.left.base := by
  let M := maximum X K hK hne
  exact ⟨M, nativePoint_singular M hK, native_maximal M hK,
    native_shadow_compact M hK, compact_subset_native_range M hK⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCompactShadowBarrier
