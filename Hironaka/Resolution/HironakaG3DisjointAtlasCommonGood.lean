import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
import Hironaka.Resolution.HironakaG3RPureEmbedded
import Hironaka.Resolution.EmbeddedFromResolution
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointAtlasCommonGood
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG3DisjointLocalTowerAtlas RestrictEmptyTower EmbeddedFromResolution
open ResolutionInvariantExt (IsEmptyTower)

private theorem empty_avoids {n : ℕ} {X Y : CMfd.{0} n} (U : Opens X) (T : BlowupTower X Y)
    (hT : IsEmptyTower T) : CentresAvoid U T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih => exact ⟨ih hT.1, by rw [hT.2]; exact Set.empty_disjoint _⟩

private theorem empty_iso {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsEmptyTower T) (G : Set X) : IsIsomorphismOver n T.proj G := by
  have hExc : T.proj '' exceptionalLocus n T.proj ⊆ (∅ : Set X) := by
    have hh := image_exceptionalLocus_subset_compl (⊤ : Opens X) T (empty_avoids ⊤ T hT)
    simpa using hh
  have hIso := HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    T.isBlowupSequence hExc
  refine ⟨⟨fun y hy => hy, ?_, ?_⟩,?_⟩
  · intro y₁ hy₁ y₂ hy₂ he
    exact hIso.1.2.1 (by simp) (by simp) he
  · intro x hx
    obtain ⟨y,_,hy⟩ := hIso.1.2.2 (show x ∈ (∅ : Set X)ᶜ by simp)
    exact ⟨y,by change T.proj y ∈ G; rw [hy]; exact hx,hy⟩
  · exact disjoint_left.mpr (fun y _ hy => hExc ⟨y,hy,rfl⟩)

/-- Local isomorphism of every actual class chart glues over the same set. -/
theorem glued_isomorphism_over_of_local {n : ℕ} {X Z : CMfd.{0} n} {𝒞 : LocalTowerClass X}
    (G : Set X) {P : Z → X} (hP : IsGluedFrom 𝒞 Z P)
    (hLocal : ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      𝒞 U Y T → IsIsomorphismOver n T.proj ((Subtype.val : U → X) ⁻¹' G)) :
    IsIsomorphismOver n P G := by
  refine ⟨⟨fun z hz => hz, ?_, ?_⟩, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ he
    obtain ⟨c,hc⟩ := hP.2.2.2 (P z₁)
    have hz₁V : z₁ ∈ c.V := c.mem_V hc
    let y₁ := c.φ.symm ⟨z₁,hz₁V⟩
    have hy₁ : chartIncl c y₁ = z₁ := chartIncl_symm c ⟨z₁,hz₁V⟩
    have hz₂V : z₂ ∈ c.V := c.mem_V (by rw [← he]; exact hc)
    let y₂ := c.φ.symm ⟨z₂,hz₂V⟩
    have hy₂ : chartIncl c y₂ = z₂ := chartIncl_symm c ⟨z₂,hz₂V⟩
    have hLocalC := hLocal c.U c.Y c.T c.mem
    have hy₁G : ((c.T.proj y₁ : c.U) : X) ∈ G := by rw [← proj_chartIncl c y₁,hy₁]; exact hz₁
    have hy₂G : ((c.T.proj y₂ : c.U) : X) ∈ G := by rw [← proj_chartIncl c y₂,hy₂]; exact hz₂
    have hproj : c.T.proj y₁ = c.T.proj y₂ := by
      apply Subtype.ext
      rw [← proj_chartIncl c y₁,← proj_chartIncl c y₂,hy₁,hy₂]
      exact he
    have hEq := hLocalC.1.2.1 hy₁G hy₂G hproj
    exact hy₁.symm.trans ((congrArg (chartIncl c) hEq).trans hy₂)
  · intro x hx
    obtain ⟨z,rfl⟩ := hP.2.2.1 x
    exact ⟨z,hx,rfl⟩
  · apply disjoint_left.mpr
    intro z hzG hzExc
    obtain ⟨c,hc⟩ := hP.2.2.2 (P z)
    have hzV : z ∈ c.V := c.mem_V hc
    let y := c.φ.symm ⟨z,hzV⟩
    have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
    have hyG : ((c.T.proj y : c.U) : X) ∈ G := by rw [← proj_chartIncl c y,hyz]; exact hzG
    have hyExc : y ∈ exceptionalLocus n c.T.proj := by
      rw [exceptionalLocus_chart c hP.1]
      change chartIncl c y ∈ exceptionalLocus n P
      rwa [hyz]
    exact Set.disjoint_left.mp (hLocal c.U c.Y c.T c.mem).2 hyG hyExc

/-- If every component class is locally an isomorphism over G, so is the assembled map. -/
theorem disjoint_atlas_isomorphism_over_common_good {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X) (G : Set X)
    (hLocal : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → IsIsomorphismOver n T.proj ((Subtype.val : U → X) ⁻¹' G))
    {P : Z → X} (hP : IsGluedFrom (disjointWindowClass A W K) Z P) : IsIsomorphismOver n P G := by
  apply glued_isomorphism_over_of_local G hP
  intro U Y T hT
  rcases hT with ⟨i,_,hK⟩ | ⟨_,hEmpty⟩
  · exact hLocal i U Y T hK
  · exact empty_iso T hEmpty _
end
end Hironaka.HironakaG3DisjointAtlasCommonGood
