import Hironaka.Resolution.HironakaG1InitialSelectedOrderPhase
import Hironaka.Invariant.ContactStageInvDomain

/-! The global normal tangent of the literal initial selected companion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1InitialCompanionNormalTangent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec InvDomainTowerAlong RelativePrincipalizationSpan
  HomogenizedIdealAlong HomogenizedGlueingLiftAlong TangentDirectionAlong
  StepOneValue StepOneValueMasked BoundaryCount ContactEquivalenceAlong ContactStageInvDomain
  InvDomainMemberRestriction
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1InitialSelectedNormalOrder HironakaG1InitialSelectedOrderPhase
  HironakaG1PositiveNormalRepairCentres GeneralValue NonmonomialOrderTail CompanionRebase

/-- The actual initial positive selected companion on the evaluator's
literal order mask has the global normal tangent, at its own mark. -/
theorem initial_positive_companion_normal_tangent {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (p : productOpen U) (hLevel : level (properNormalMarked Q) (BlowupTower.refl
      (X := CMfd.of (n := n + 1) (productOpen U))) p = s + 1) :
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := lowerMask P (s + 1) H p
    let X := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) X := lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) P (s + 1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (BlowupTower.refl (X := X))) L.d
    let J : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) C) :=
      compAt (X := X) L L.d (BlowupTower.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    C = ⊤ ∧ IsInvDomain k J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsTangentDirectionAlong J.N J.ideal J.d univ u := by
  intro P H O X L C J u
  let X₀ := CMfd.of (n := n + 1) (productOpen U)
  let B := barMarked (X := X₀) P
  let A := memberRestrict B (membersThrough B.E B.E p)
  have hOld : origMembers P H = B.E := by
    change B.E.take B.E.length = B.E
    exact List.take_length
  have hp : 0 < boundaryCount P.E p := by
    change boundaryCount (origMembers P H) p = s + 1 at hLevel
    rw [hOld] at hLevel
    change 0 < boundaryCount B.E p
    rw [hLevel]
    exact Nat.succ_pos s
  have hSelected : L = MarkedIdeal.pullback (Subtype.val : O → X₀) A := by
    change MarkedIdeal.pullback (Subtype.val : O → X₀)
      (memberRestrict B (membersThrough B.E (origMembers P H) p)) = _
    rw [hOld]
  obtain ⟨hA, _, _, hTangent, _⟩ := initial_selected_normal_data Q hQ p hp
  have hTangentL : IsTangentDirectionAlong L.N L.ideal L.d univ
      (relativeNormalCoordinate U ∘ (Subtype.val : O → X₀)) := by
    rw [hSelected]
    exact isTangentDirectionAlong_pullback_val O
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hg)
      (isTangentDirectionAlong_mono hTangent O.isOpen (subset_univ _))
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H trivial p hLevel
  obtain ⟨hMask, hComp, _⟩ := original_initial_positive_lower_order_phase Q hQ p hLevel
  obtain ⟨hLC, hMax, _⟩ := original_initial_positive_lower_companion_recursion Q hQ p hLevel
  let F : MarkedIdeal (n + 1) X := companionOf (n + 1) L L.d
  have hRF : F = (⟨L.N, L.E, RestrictedIdealExtension.restrictOn (n + 1) L.N L.ideal, L.d⟩ :
      MarkedIdeal (n + 1) X) := hComp
  have hTangentF : IsTangentDirectionAlong F.N F.ideal F.d univ
      (relativeNormalCoordinate U ∘ (Subtype.val : O → X₀)) := by
    rw [hRF]
    exact ⟨hTangentL.isOpen, fun z hz =>
      iterDerivIdealAlong_mono (N := L.N)
        (RestrictedIdealExtension.le_restrictOn hL.isWellFormed.isCoherent)
        (L.d - 1) z _ (hTangentL.mem z hz), hTangentL.multiplicity_one⟩
  have hEq : MarkedIdeal.pullback (Subtype.val : C → X) F = J :=
    pullback_val_companionOf (Nat.succ_pos n) hL.isWellFormed hL.isNonzeroAlongAt C L.d
  have hJ : IsInvDomain k J := hEq ▸ isInvDomain_pullback_val C hLC
  have hJT : IsTangentDirectionAlong J.N J.ideal J.d univ u := by
    rw [← hEq]
    exact isTangentDirectionAlong_pullback_val C
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hLC.isWellFormed.isCoherent hg)
      (isTangentDirectionAlong_mono hTangentF C.isOpen (subset_univ _))
  have hJM : IsMaximalOrderAlong J.N J.ideal J.d := by
    rw [← hEq]
    intro z hz
    let F' : MarkedIdeal (n + 1) X := ⟨F.N, F.E, F.ideal, F.d + 1⟩
    change z ∈ (MarkedIdeal.pullback (Subtype.val : C → X) F').cosupp at hz
    rw [cosupp_pullback_val F'
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hLC.isWellFormed.isCoherent hg) C] at hz
    exact hMax z.val hz
  exact ⟨hMask, hJ, hJM, hJT⟩

end Hironaka.HironakaG1InitialCompanionNormalTangent
