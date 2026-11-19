import Hironaka.Resolution.HironakaG3CoupledNativeNormalization
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CoupledOpenRestriction
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3CoupledNativeNormalization
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeOpenLift
  HironakaDisjointNativeReferenceWindow HironakaSharpActualCurveComparisonRestriction
  ResolutionInvariantSpec

/-- The actual ambient restriction of a coupled test history has a native
lift whose stages physically agree with the actual intrinsic restriction. -/
theorem exists_open_native_lift_of_coupled
    {d t : ℕ} {X : CMfd.{0} (d+t)} {N : Set X}
    (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    {P : CMfd.{0} d} :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (Φ : P ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ N)
      {B : List (Set X)} {J : GermIdeal (d+t) X} {ι : P → X} {M : MarkedIdeal d P}
      (_hι : ∀ p, ι p = (Φ p).val) (_hM : IsInvDomain d M)
      {Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)} {T : BlowupTower P Q}
      {U : BlowupTower X Y} {η : Q → Y},
      IsGeoTestTower M T → IsGeoTestTower (fullMarked B J) U →
      CoupledHistory N B J ι M T U η → ∀ O : Opens X,
      ∃ (hSc : IsClosed (openSection (contactAlong N U) (openPreimage U O)))
        (hS : ∀ y ∈ openSection (contactAlong N U) (openPreimage U O),
          RegularAtDim (n := d+t) (openSection (contactAlong N U) (openPreimage U O)) y d)
        (R : BlowupTower
          (nativeManifold (Nat.le_add_right d t) (openSection N O) (openSection_regular hN O))
          (nativeManifold (Nat.le_add_right d t) (openSection (contactAlong N U) (openPreimage U O)) hS))
        (α : CMfd.of (n := d) (preimageOpen Φ (nativeWindow (Nat.le_add_right d t) N hN O))
          ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
          nativeManifold (Nat.le_add_right d t) (openSection N O) (openSection_regular hN O))
        (β : CMfd.of (n := d) (openPreimage T (preimageOpen Φ (nativeWindow (Nat.le_add_right d t) N hN O)))
          ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
          nativeManifold (Nat.le_add_right d t) (openSection (contactAlong N U) (openPreimage U O)) hS),
        Lift (Nat.le_add_right d t) (openSection N O) (hNc.preimage continuous_subtype_val)
          (openSection_regular hN O) (B.map ((Subtype.val : O → X) ⁻¹' ·))
          (restrict O U) (openSection (contactAlong N U) (openPreimage U O)) hSc hS R ∧
        IsTowerIso α (restrict (preimageOpen Φ (nativeWindow (Nat.le_add_right d t) N hN O)) T) R β ∧
        (∀ p, ((α p).val : O).val = ι p.val) ∧
        ∀ q, ((β q).val : openPreimage U O).val = η q.val := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro Φ B J ι M hι hM Q Y T U η hT hU h O
  obtain ⟨hSc,hS,R,F,hLift,hIso,hF⟩ := exists_native_normalization hNc hN Φ hι hM hT hU h
  obtain ⟨hScO,hSO,RO,hLiftO,hIsoO⟩ := exists_open_lift hLift O
  let W := nativeWindow (Nat.le_add_right d t) N hN O
  let hRestrict := HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction hIso W
  let α := (openRestriction Φ (preimageOpen Φ W) W rfl).trans (windowEquiv (Nat.le_add_right d t) N hN hNc O).symm
  let β := (openRestriction F (openPreimage T (preimageOpen Φ W)) (openPreimage R W)
    (openPreimage_eq_preimage hIso W)).trans (endpointEquiv hLift O).symm
  refine ⟨hScO,hSO,RO,α,β,hLiftO,?_,?_,?_⟩
  · exact hRestrict.trans hIsoO.symm
  · intro p
    change (((windowEquiv (Nat.le_add_right d t) N hN hNc O).symm
      (openRestriction Φ (preimageOpen Φ W) W rfl p)).val : O).val = ι p.val
    exact (hι p.val).symm
  · intro q
    have hp := endpointEquiv_val_native hLift O (β q)
    have he : endpointEquiv hLift O (β q) =
        openRestriction F (openPreimage T (preimageOpen Φ W)) (openPreimage R W)
          (openPreimage_eq_preimage hIso W) q := by
      exact (endpointEquiv hLift O).apply_symm_apply _
    rw [he] at hp
    change (F q.val).val = ((β q).val : openPreimage U O).val at hp
    exact hp.symm.trans (hF q.val)

end
end Hironaka.HironakaG3CoupledOpenRestriction
