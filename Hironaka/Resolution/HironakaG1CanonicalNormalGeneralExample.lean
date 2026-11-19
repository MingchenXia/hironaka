import Hironaka.Resolution.HironakaG1CanonicalNormalSelectedExample
import Hironaka.Resolution.HironakaG1InitialSelectedOrderPhase
import Hironaka.Resolution.HironakaDisjointZeroCoordinateInitialRecoding

/-!
# The enclosing general value on the initial padded selected record

The order-one branch reads the actual true-mark companion on its order
mask. Its finite Step One letter is the value of the normal contact.
-/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CanonicalNormalGeneralExample
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal MarkedIdealRestrictOpen
  GermIdealPullbackCalculus RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal GermIdealOrder HomogenizedIdealAlong
  ResolutionInvariantSpec CanonicalCentres GeneralValue GeneralCompare NonmonomialOrderLocal NonmonomialOrderTail InvDomainRebase
  CompanionReductionAlong CompanionRebase RestrictLeCalculus
  StepOneValue StepOneValueMasked ContactStageKept HironakaG8MixedOrderInvariance
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaG1CanonicalNormalSelectedExample HironakaG1InitialSelectedOrderPhase
  HironakaG1InitialSelectedNormalOrder HironakaG1PositiveNormalRepairCentres
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualRelativeNormalGeometry HironakaDisjointZeroCoordinateInitialRecoding

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev D : Set U := (Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor
private abbrev H : Set X := projection U ⁻¹' D
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev T : BlowupTower X X := .refl
private abbrev O := lowerMask P 1 T p
private abbrev M := CMfd.of (n := 3) O
private abbrev L : MarkedIdeal 3 M := lowerMarkedM P 1 T p
private abbrev e : BlowupTower M M := .refl
private abbrev t : M → ℂ := relativeNormalCoordinate U ∘ Subtype.val
private abbrev R := invFamily (by decide : 0 < 3) 1

private theorem lower_eq :
    L = MarkedIdeal.pullback (Subtype.val : O → X) (⟨H, [], P.ideal, 1⟩ : MarkedIdeal 3 X) := by
  have hP := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain
  have hp : p ∈ H := by
    change tangentProjection 2 1 (tangentInclusion 2 1 0) ∈ firstCoordinateDivisor
    rw [tangentProjection_tangentInclusion]
    simp [firstCoordinateDivisor]
  have h := positive_mark_one_single_member_lower_eq (X := X) P rfl
    hP.isWellFormed.isCoherent H rfl p hp
  have hN : P.N = univ := preimage_univ
  rw [hN, univ_inter] at h
  exact h

private theorem lower_d : L.d = 1 := by rw [lower_eq]; rfl

private theorem lower_cosupp_at_origin (pO : O) (hp : pO.val = p) (hCos : p ∈ P.cosupp) :
    pO ∈ L.cosupp := by
  have hP := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain
  have hh : ∀ x g, P.ideal.mem x g → HolomorphicAt 3 g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg
  let K : MarkedIdeal 3 X := ⟨H, [], P.ideal, 1⟩
  have hK : K.cosupp = H ∩ P.ideal.zeroLocus := cosupport_one hh
  have hPC : P.cosupp = P.N ∩ P.ideal.zeroLocus := cosupport_one hh
  rw [lower_eq, cosupp_pullback_val K hh, hK]
  change pO.val ∈ H ∩ P.ideal.zeroLocus
  rw [hp]
  refine ⟨?_, (hPC ▸ hCos).2⟩
  change tangentProjection 2 1 (tangentInclusion 2 1 0) ∈ firstCoordinateDivisor
  rw [tangentProjection_tangentInclusion]
  simp [firstCoordinateDivisor]

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem actual_companion_step_eq (pO : O) (hLcos : pO ∈ L.cosupp)
    (hLev : level P T p = 1) (hpW : pO ∈ ordMask (M := M) L 1) :
    let W := ordMask (M := M) L 1
    Seq.StepOneValueMasked.stepOneInvM (X := CMfd.of (n := 3) W) R
      (compAt (X := M) L 1 e) .refl ⟨pO, hpW⟩ =
    Seq.StepOneValueMasked.stepOneInvM (X := M) R L e pO := by
  intro W
  let C : MarkedIdeal 3 M := companionOf 3 L L.d
  let q : W := ⟨pO, hpW⟩
  have hL : IsInvDomain 2 L := padded_lower_isInvDomain sourceRecord sourceRecord_domain T trivial p hLev
  obtain ⟨hC, hCM, _⟩ := original_initial_positive_lower_companion_recursion
    sourceRecord sourceRecord_domain p hLev
  obtain ⟨_, hCEq⟩ := original_initial_positive_lower_companion_eq
    sourceRecord sourceRecord_domain p hLev
  have he : C = (⟨L.N, L.E, restrictOn 3 L.N L.ideal, L.d⟩ : MarkedIdeal 3 M) := hCEq
  have hRel : RestrictEquiv L C := by
    rw [he]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hL.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hv : pO ∈ C.cosupp := hRel.cosupp_eq ▸ hLcos
  have hLM : IsMaximalOrderAlong L.N L.ideal L.d := by
    intro x hx
    apply hCM x
    rw [← hRel.N_eq, ← hRel.d_eq]
    exact cosupport_subset_of_restrictLe hRel.ge (L.d + 1) hx
  have hAt : compAt (X := M) L 1 e = MarkedIdeal.pullback (Subtype.val : W → M) C := by
    change companionOf 3 (M := CMfd.of (n := 3) W) (MarkedIdeal.pullback (Subtype.val : W → M) L) 1 = _
    change _ = MarkedIdeal.pullback (Subtype.val : W → M) (companionOf 3 L L.d)
    rw [lower_d, pullback_val_companionOf (by decide) hL.isWellFormed hL.isNonzeroAlongAt W]
  have hF := StepOneSeq.isMaxOrderValue_stepOneInvM (k := 2) R (by decide : 0 < 3)
  have hRest := hF.restrictOpen (X := M) C hC hCM W e trivial q hv
  have hRep := hF.representative (X := M) C L hC hCM hL hLM
    (restrictEquiv_symm hRel) e trivial pO hv
  rw [hAt]
  exact hRest.trans hRep

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the actual padded selected record, the general depth-two value at
the empty history is the order-one, level-zero insertion of the genuine
depth-one normal contact value, whose first entry is two. -/
theorem canonical_normal_selected_general_value :
    ∃ (pO : O) (v : ValTy 1), pO.val = p ∧
      (invFamily (by decide : 0 < 3) 2).inv L e pO = initialEmbedding 1 v ∧
      v =
        R.inv (contactMarkedKept L t e (⊤ : Opens M))
          (BlowupTower.refl (X := CMfd.of (n := 3) (⊤ : Opens M))) ⟨pO, Set.mem_univ _⟩ ∧
      fstEntry (k := 0) v = 2 := by
  obtain ⟨pO, v, hp, hStep, hContact, hv⟩ := canonical_normal_selected_finite_stepOne
  obtain ⟨_, _, _, _, _, _, _, _, hCos, _, hLev, _, _, _, _, _, _⟩ :=
    joint_positive_nonspecial_first_entries
  have hLcos := lower_cosupp_at_origin pO hp hCos
  obtain ⟨hW, _, hRun⟩ := original_initial_positive_lower_order_phase
    sourceRecord sourceRecord_domain p hLev
  have ho : nmOrd (geoTransformAlong L e) pO = 1 := by
    have hOrd := (hRun e trivial pO hLcos).1.2
    exact hOrd.trans lower_d
  have hpW : pO ∈ ordMask (M := M) L 1 := by
    have h : ordMask (M := M) L L.d = ⊤ := hW
    rw [lower_d] at h
    rw [h]
    trivial
  have hComp := (actual_companion_step_eq pO hLcos hLev hpW).trans hStep
  let F := fun {Y : CMfd.{0} 3} (K : MarkedIdeal 3 Y) {Z : CMfd.{0} 3}
    (D' : BlowupTower Y Z) (z : Z) => Seq.StepOneValueMasked.stepOneInvM R K D' z
  refine ⟨pO, v, hp, ?_, hContact, hv⟩
  change genInv (X := M) F L e pO = _
  rw [genInv_of_nmOrd_ne_zero (X := M) F L e ho (by decide)]
  change toLex (1, Sum.inrₗ (genLowerValue (X := M) F L 1 e e pO)) = _
  have hGen := genLowerValue_eq_of_mem (X := M) (T₀ := e) (T₁ := e)
    (y := pO) F L hpW
  have hCoefficient := hGen.trans
    (congrArg (fun w : ℕ ×ₗ WithTop (ValTy 1) => (w : WithTop (ℕ ×ₗ WithTop (ValTy 1)))) hComp)
  exact congrArg (fun w : WithTop (ℕ ×ₗ WithTop (ValTy 1)) =>
    (toLex (1, Sum.inrₗ w) : ValTy 2)) hCoefficient

/-- The original padded Step One value at level one contains the inserted
normal letter inside its actual finite selected lower value. -/
theorem canonical_normal_original_positive_stepOne_value :
    ∃ (pO : O) (v : ValTy 1), pO.val = p ∧
      Seq.StepOneValueMasked.stepOneInvM (X := X) (invFamily (by decide : 0 < 3) 2) P T p =
        toLex (1, (↑(initialEmbedding 1 v) : WithTop (ValTy 2))) ∧
      v =
        R.inv (contactMarkedKept L t e (⊤ : Opens M))
          (BlowupTower.refl (X := CMfd.of (n := 3) (⊤ : Opens M))) ⟨pO, Set.mem_univ _⟩ ∧
      fstEntry (k := 0) v = 2 := by
  classical
  obtain ⟨pO, v, hp, hGen, hContact, hv⟩ := canonical_normal_selected_general_value
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hLevel, _, hNS, _, _, _, _⟩ :=
    joint_positive_nonspecial_first_entries
  let R₂ := invFamily (by decide : 0 < 3) 2
  refine ⟨pO, v, hp, ?_, hContact, hv⟩
  change Seq.StepOneValueMasked.stepOneInvL (X := X) R₂ P (lowerMarkedM P) T p = _
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R₂ P (lowerMarkedM P) T hNS, hLevel]
  change toLex (1, Seq.StepOneValueMasked.lowerValueL R₂ P (lowerMarkedM P) 1 T T p) = _
  have hm : p ∈ O := by
    have hm' : pO.val ∈ O := pO.property
    simpa only [hp] using hm'
  unfold Seq.StepOneValueMasked.lowerValueL
  rw [dif_pos (show T.proj p ∈ lowerMask P 1 T (T.proj p) from hm)]
  have hPoint : (⟨p, hm⟩ : O) = pO := Subtype.ext hp.symm
  have hRead : R₂.inv L e (⟨p, hm⟩ : O) = initialEmbedding 1 v := hPoint.symm ▸ hGen
  exact congrArg (fun b : ValTy 2 => toLex (1, (↑b : WithTop (ValTy 2)))) hRead

end
end Hironaka.HironakaG1CanonicalNormalGeneralExample
