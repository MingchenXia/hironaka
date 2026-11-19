import Hironaka.Resolution.HironakaG3UniverseLiftedChart
import Hironaka.Resolution.HironakaG3UniverseConjugateGeometry
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseLiftedAtlas
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3UniverseLiftManifold G3UniverseLiftedChart G3UniverseOpenDiffeo
  HironakaG3UniverseDiffeoDerivative
noncomputable section

/-- Candidate universal-class atlas on the literal conjugate of the original glued map. -/
theorem lifted_universal_atlas {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀} (hG : IsGluedFrom 𝒞 Y₀ P) :
    IsGluedFrom (fun _ _ _ => True) (liftCMfd.{u} Y₀)
      (e.symm ∘ P ∘ (liftDiffeomorph.{u} Y₀).symm) := by
  have h := conjugate_map_properties (liftDiffeomorph.{u} Y₀) e.symm P hG.1 hG.2.1 hG.2.2.1
  refine ⟨h.1,h.2.1,h.2.2,?_⟩
  intro x
  obtain ⟨c,hc⟩ := hG.2.2.2 (e x)
  refine ⟨liftedTowerChart e c,?_⟩
  change e x ∈ c.U
  exact hc
end
end Hironaka.G3UniverseLiftedAtlas
