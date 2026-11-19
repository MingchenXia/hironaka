import Hironaka.Resolution.HironakaG8ActualContactDomainOpen
import Hironaka.Resolution.HironakaG8ActualContactEndpoint
/-! # Actual endpoint produces the contact common-domain open -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ActualContactEndpointDomain
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  TangentDirectionAlong StepOneValue ResolutionInvariantSpec DivisorExponentAlong
  HironakaG11InvBMLower HironakaG8LocalHistory HironakaG8PairDomainOpen
  HironakaG8CaseTActualAmbient HironakaG8CaseTContactPair NormalCrossings NormalCrossingsInvariance
open HironakaG11InvBMClass (SameCarrierDim)

/-- Ambient endpoint data produce the common invariant-domain stage open. -/
theorem actual_endpoint_common_domain_open
    {n : ℕ} {X Y Z : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B) (hAB : LocWPEquiv A B)
    (hd : A.d = B.d) (hdim : SameCarrierDim A B)
    (U : Opens X) {f g : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (hg : IsTangentDirectionAlong B.N B.ideal B.d U g)
    (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked A) (P.append Q))
    {z : Z} (hzU : P.proj (Q.proj z) ∈ U)
    (hzA : z ∈ (contactCoeffBM A f (P.append Q)).N)
    (hzB : z ∈ (contactCoeffBM B g (P.append Q)).N)
    (hnzA : IsNonzeroAlongAt (contactCoeffBM A f (P.append Q)).N (contactCoeffBM A f (P.append Q)).ideal z)
    (hnzB : IsNonzeroAlongAt (contactCoeffBM B g (P.append Q)).N (contactCoeffBM B g (P.append Q)).ideal z) :
    let V := openPreimage P U
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
    let D := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B g P)
    let F := (A.E.map (strictAlong P)).map ((Subtype.val : V → Y) ⁻¹' ·)
    let T := restrict V Q
    let z' : openPreimage Q V := ⟨z,hzU⟩
      ∃ G : Opens V, T.proj z' ∈ G ∧
        let CG := MarkedIdeal.pullback (Subtype.val : G → V) C
        let DG := MarkedIdeal.pullback (Subtype.val : G → V) D
        let FG := F.map ((Subtype.val : G → V) ⁻¹' ·)
        IsInvDomain n CG ∧ IsInvDomain n DG ∧
        LocWPEquiv (X := CMfd.of (n := n) G) {CG with E := FG ++ CG.E} {DG with E := FG ++ CG.E} ∧
        SameCarrierDim (X := CMfd.of (n := n) G) CG DG ∧ DG.d = CG.d ∧
        IsSNCDivisor n (FG ++ CG.E) ∧
        IsGeoTestTower CG (restrict G T) ∧ IsGeoTestTower DG (restrict G T) ∧
        IsGeoTestTower {CG with E := FG ++ CG.E} (restrict G T) := by
  have hTA : IsGeoTestTower A (P.append Q) := ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hT
  have hTB : IsGeoTestTower B (P.append Q) := (hAB.wEquiv.2 _).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) (P.append Q) := ((StepOneBridge.barMarked_wEquiv B hB).2 _).1.mpr hTB
  have hAend := HironakaG8ActualContactEndpoint.actual_contact_endpoint_restrict A hA U hf P Q hT hzU hzA hnzA
  have hBend := HironakaG8ActualContactEndpoint.actual_contact_endpoint_restrict B hB U hg P Q hTJB hzU hzB hnzB
  exact HironakaG8ActualContactDomainOpen.actual_contact_common_domain_open hA hB hAB hd hdim U hf hg P Q hT
    ⟨z,hzU⟩ hAend.1 hBend.1 hAend.2 hBend.2

end
end Hironaka.HironakaG8ActualContactEndpointDomain
