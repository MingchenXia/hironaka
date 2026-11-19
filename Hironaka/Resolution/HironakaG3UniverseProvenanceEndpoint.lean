import Hironaka.Resolution.HironakaG3UniverseChartProvenance
import Hironaka.Resolution.HironakaG3EndpointRepresentableClass
import Hironaka.Resolution.HironakaG3RChartOfMember
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.G3UniverseProvenanceEndpoint

noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdealTowerTransport HironakaG3RTowerClass HironakaG3RChartOfMember
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseOpenDiffeo
  G3UniverseChartTowerTransport G3UniverseLiftedChart G3UniverseChartProvenance
  G3EndpointRepresentableClass HironakaG3RigidOverLocalGlue

/-- A compact-enclosed base open lifts with its actual chart and provenance. -/
theorem lifted_provenance_compact_window {n : ℕ}
    {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀}
    (hWindows : ∀ (U : Opens X₀) (L : Set X₀), IsCompact L → (U : Set X₀) ⊆ L →
      ∃ c : TowerChart 𝒞 Y₀ P, c.U = U)
    (U : Opens X) (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
    ∃ c : TowerChart (liftedProvenanceClass e 𝒞) (liftCMfd.{u} Y₀)
      (e.symm ∘ P ∘ (liftDiffeomorph.{u} Y₀).symm), c.U = U := by
  let U₀ := preimageOpens e.symm U
  have hLiftedL : IsCompact (e '' L) := hL.image e.contMDiff.continuous
  have hU₀ : (U₀ : Set X₀) ⊆ e '' L := by
    intro z hz
    exact ⟨e.symm z, hUL hz, e.apply_symm_apply z⟩
  obtain ⟨c,hc⟩ := hWindows U₀ (e '' L) hLiftedL hU₀
  let c' := liftedTowerChart e c
  refine ⟨⟨c'.U,c'.Y,c'.T,lifted_chart_mem_provenance e c,c'.V,c'.V_eq,c'.φ,c'.proj_φ⟩,?_⟩
  change preimageOpens e c.U = U
  rw [hc]
  apply Opens.ext
  ext x
  change e.symm (e x) ∈ U ↔ x ∈ U
  rw [e.symm_apply_apply]

/-- Comparisons of the small endpoints induce comparisons of the actual provenance
class endpoints after lifting. -/
theorem lifted_provenance_endpoint_comparisons {n : ℕ}
    {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀}
    (hG : IsGluedFrom 𝒞 Y₀ P) (hCompare : HasComparisons 𝒞) :
    HasComparisons (liftedProvenanceClass e 𝒞) := by
  let P' := e.symm ∘ P ∘ (liftDiffeomorph.{u} Y₀).symm
  have hP' : Continuous P' := (lifted_provenance_atlas e hG).1.continuous
  have hMember : ∀ (U : Opens X) (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      liftedProvenanceClass e 𝒞 U Y T → endpointRepresentable P' hP' U Y T := by
    intro U Y T hT
    obtain ⟨U₀,Z₀,T₀,hT₀,hU,χ,hiso⟩ := hT
    subst U
    have hBase : (opensCongr (rfl : preimageOpens e U₀ = preimageOpens e U₀)).trans
        (baseLiftDiffeo e U₀) = baseLiftDiffeo e U₀ := by
      ext p
      rfl
    rw [hBase] at hiso
    let c := chartOfMember hCompare T₀ hT₀ hG.2.2.2 hG.1.continuous
    let c' := liftedTowerChart e c
    let S := chartTowerTransport e U₀ T₀
    let φ := χ.trans (S.back.symm.trans c'.φ)
    have hV : c'.V = window P' hP' (preimageOpens e U₀) := Opens.ext c'.V_eq
    refine ⟨φ.trans (opensCongr (n := n) hV),?_⟩
    intro z
    apply Subtype.ext
    change P' (c'.φ (S.back.symm (χ z)) : liftCMfd.{u} Y₀) = (T.proj z).val
    have hProj : P' (c'.φ (S.back.symm (χ z)) : liftCMfd.{u} Y₀) =
        (S.tower.proj (S.back.symm (χ z))).val := c'.proj_φ _
    have hS := proj_transport (baseLiftDiffeo e U₀) (liftTower.{u} T₀) (S.back.symm (χ z))
    change baseLiftDiffeo e U₀ (S.tower.proj (S.back.symm (χ z))) =
      (liftTower.{u} T₀).proj (S.back (S.back.symm (χ z))) at hS
    rw [S.back.apply_symm_apply] at hS
    exact hProj.trans (congrArg Subtype.val ((baseLiftDiffeo e U₀).injective (hS.trans (hiso.proj_comm z).symm)))
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ hT₁ hT₂
  exact endpointRepresentable_hasComparisons P' hP' U₁ U₂ Y₁ Y₂ T₁ T₂
    (hMember U₁ Y₁ T₁ hT₁) (hMember U₂ Y₂ T₂ hT₂)

end
end Hironaka.G3UniverseProvenanceEndpoint
