import Hironaka.Resolution.HironakaG3RPureEmbedded
import Hironaka.Resolution.HironakaAdmissibleSequence
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG3GluedClassFootprint
noncomputable section
open Hironaka.BlowupSequences BlowupTowers RestrictEmptyTower
  HironakaAdmissibleSequence HironakaG3RTowerClass HironakaG3RPureEmbedded

/-- An exceptional point of a glued tower class lies over any closed set
that contains the images of all centres of every class member. -/
theorem glued_exceptional_subset {n : ℕ} {X Z : CMfd.{u} n}
    {𝒞 : LocalTowerClass X} (F : Set X) (hF : IsClosed F)
    (hOver : ∀ (U : Opens X) (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      𝒞 U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' F) T)
    {P : Z → X} (h : IsGluedFrom 𝒞 Z P) : exceptionalLocus n P ⊆ P ⁻¹' F := by
  intro z hz
  obtain ⟨c,hc⟩ := h.2.2.2 (P z)
  have hzV : z ∈ c.V := c.mem_V hc
  let y := c.φ.symm ⟨z,hzV⟩
  have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
  have hy : y ∈ exceptionalLocus n c.T.proj := by
    rw [exceptionalLocus_chart c h.1]
    change chartIncl c y ∈ exceptionalLocus n P
    rwa [hyz]
  let G := (Subtype.val : c.U → X) ⁻¹' F
  let O : Opens (CMfd.of (n := n) c.U) := ⟨Gᶜ,(hF.preimage continuous_subtype_val).isOpen_compl⟩
  have hAvoid : CentresAvoid O c.T := centresAvoid_of_centresOver O disjoint_compl_left c.T (hOver c.U c.Y c.T c.mem)
  have he := EmbeddedFromResolution.image_exceptionalLocus_subset_compl O c.T hAvoid ⟨y,hy,rfl⟩
  change c.T.proj y ∈ (Gᶜ)ᶜ at he
  simp only [compl_compl] at he
  change ((c.T.proj y : c.U) : X) ∈ F at he
  have hProj : P z = ((c.T.proj y : c.U) : X) :=
    (congrArg P hyz.symm).trans (proj_chartIncl c y)
  change P z ∈ F
  rw [hProj]
  exact he

/-- The glued map is an isomorphism away from the same original closed
footprint, provided every local class member has its centres over it. -/
theorem glued_isomorphism_over_compl {n : ℕ} {X Z : CMfd.{u} n}
    {𝒞 : LocalTowerClass X} (F : Set X) (hF : IsClosed F)
    (hOver : ∀ (U : Opens X) (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      𝒞 U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' F) T)
    {P : Z → X} (h : IsGluedFrom 𝒞 Z P) : IsIsomorphismOver n P Fᶜ := by
  have hExc := glued_exceptional_subset F hF hOver h
  refine ⟨⟨fun z hz => hz,fun z₁ hz₁ z₂ hz₂ he => ?_,fun x hx => ?_⟩,?_⟩
  · obtain ⟨c,hc⟩ := h.2.2.2 (P z₁)
    have hz₁V : z₁ ∈ c.V := c.mem_V hc
    let y₁ := c.φ.symm ⟨z₁,hz₁V⟩
    have hy₁ : chartIncl c y₁ = z₁ := chartIncl_symm c ⟨z₁,hz₁V⟩
    have hz₂V : z₂ ∈ c.V := c.mem_V (by rw [← he]; exact hc)
    let y₂ := c.φ.symm ⟨z₂,hz₂V⟩
    have hy₂ : chartIncl c y₂ = z₂ := chartIncl_symm c ⟨z₂,hz₂V⟩
    let G := (Subtype.val : c.U → X) ⁻¹' F
    let O : Opens (CMfd.of (n := n) c.U) := ⟨Gᶜ,(hF.preimage continuous_subtype_val).isOpen_compl⟩
    have hAvoid : CentresAvoid O c.T :=
      centresAvoid_of_centresOver O disjoint_compl_left c.T (hOver c.U c.Y c.T c.mem)
    have hImage : c.T.proj '' exceptionalLocus n c.T.proj ⊆ G := by
      have h1 := EmbeddedFromResolution.image_exceptionalLocus_subset_compl O c.T hAvoid
      change c.T.proj '' exceptionalLocus n c.T.proj ⊆ (Gᶜ)ᶜ at h1
      simpa only [compl_compl] using h1
    have hLocal := HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      c.T.isBlowupSequence hImage
    have hy₁O : c.T.proj y₁ ∈ Gᶜ := by
      change ((c.T.proj y₁ : c.U) : X) ∉ F
      rw [← proj_chartIncl c y₁,hy₁]
      exact hz₁
    have hy₂O : c.T.proj y₂ ∈ Gᶜ := by
      change ((c.T.proj y₂ : c.U) : X) ∉ F
      rw [← proj_chartIncl c y₂,hy₂]
      exact hz₂
    have hproj : c.T.proj y₁ = c.T.proj y₂ := by
      apply Subtype.ext
      rw [← proj_chartIncl c y₁,← proj_chartIncl c y₂,hy₁,hy₂]
      exact he
    have hEq : y₁ = y₂ := hLocal.1.2.1 hy₁O hy₂O hproj
    exact hy₁.symm.trans ((congrArg (chartIncl c) hEq).trans hy₂)
  · obtain ⟨z,rfl⟩ := h.2.2.1 x
    exact ⟨z,hx,rfl⟩
  · exact Set.disjoint_left.mpr fun z hz hz' => hz (hExc hz')
end
end Hironaka.HironakaG3GluedClassFootprint
