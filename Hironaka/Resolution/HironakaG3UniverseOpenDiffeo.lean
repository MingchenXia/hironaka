import Hironaka.Blowup.BlowupTowers
import Hironaka.Blowup.BlowupRestrictOpen
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseOpenDiffeo
open Hironaka.BlowupSequences BlowupTowers
noncomputable section

def preimageOpens {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) (U : Opens Y) : Opens X :=
  ⟨e ⁻¹' (U : Set Y), U.isOpen.preimage e.continuous⟩

def preimageDiffeo {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) (U : Opens Y) :
    CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (preimageOpens e U) :=
  have hU : ∀ y : U, e.symm y ∈ preimageOpens e U := fun y => by
    change e (e.symm y) ∈ (U : Set Y)
    rw [e.apply_symm_apply]
    exact y.property
  { toFun := fun y => ⟨e.symm y,hU y⟩
    invFun := fun x => ⟨e x,x.property⟩
    left_inv := fun y => Subtype.ext (e.apply_symm_apply (y : Y))
    right_inv := fun x => Subtype.ext (e.symm_apply_apply (x : X))
    contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (e.symm.contMDiff.comp contMDiff_subtype_val) hU
    contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk (e.contMDiff.comp contMDiff_subtype_val) fun x => x.property }
end
end Hironaka.G3UniverseOpenDiffeo
