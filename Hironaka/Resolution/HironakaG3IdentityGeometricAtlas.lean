import Hironaka.Resolution.HironakaG3RTowerClass
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3IdentityGeometricAtlas
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass

theorem identity_geometric_atlas {n : ℕ} (X : CMfd.{u} n) :
    IsGluedFrom (fun _ _ _ => True) X (id : X → X) := by
  refine ⟨contMDiff_id,isProperMap_id,surjective_id,?_⟩
  intro x
  let U : Opens X := ⊤
  refine ⟨⟨U,CMfd.of (n := n) U,.refl,True.intro,U,?_,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞,?_⟩,?_⟩
  · ext z
    simp [U]
  · intro z
    rfl
  · trivial
end
end Hironaka.HironakaG3IdentityGeometricAtlas
