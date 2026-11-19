import Hironaka.Resolution.HironakaG3EndpointRepresentableClass
import Hironaka.Resolution.HironakaG3TowerRestrictedQIdentification
import Hironaka.Resolution.HironakaG3RGluedBoundary
import Hironaka.Blowup.BlowupTowerIsoTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3RestrictedTowerIdentification
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail
  MarkedIdealTowerTransport HironakaG3RGluedBoundary HironakaG3RigidOverLocalGlue MaxLocusLocal

theorem restrict_tower_identification {n : ℕ} {X Y B : CMfd.{u} n}
    (Q : Y → X) (hQ : Continuous Q) (A A' : Opens X) (hA : A' ≤ A)
    (M : BlowupTower (CMfd.of (n := n) A) B)
    (Φ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ A))
    (hΦ : ∀ z, restrictedBaseMap Q hQ A (Φ z) = M.proj z) :
    ∃ (B' : CMfd.{u} n) (M' : BlowupTower (CMfd.of (n := n) A') B')
      (Φ' : B' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (window Q hQ A')),
      ∀ z, restrictedBaseMap Q hQ A' (Φ' z) = M'.proj z := by
  obtain ⟨e,he⟩ := G3RestrictedEndpointWindow.restricted_endpoint_window Q hQ A A' hA M Φ hΦ
  let V : Opens A := nestedOpens A A'
  let β := (nestedOpensDiffeo (n := n) hA).symm
  let T := transport β (restrict V M)
  refine ⟨T.target,T.tower,T.back.trans e,?_⟩
  intro z
  apply Subtype.ext
  have hp := proj_transport β (restrict V M) z
  have hr := proj_restrict V M (T.back z)
  change Q (e (T.back z)).val = ((T.tower.proj z : A') : X)
  have h2 := congrArg (fun q : V => ((q : A) : X)) hp
  have h3 := congrArg Subtype.val hr
  exact (he (T.back z)).trans (h3.symm.trans h2.symm)
end
end Hironaka.HironakaG3RestrictedTowerIdentification
