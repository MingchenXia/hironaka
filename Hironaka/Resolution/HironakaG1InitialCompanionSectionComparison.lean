import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaG1InitialCompanionZeroHistory
import Hironaka.Resolution.HironakaG1InitialNormalSelectedLocalClass
import Hironaka.Resolution.HironakaG8LocalRestrictEquiv

/-! The actual initial positive companion and its prescribed normal contact on nested masks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialCompanionSectionComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked InvDomainMemberRestriction
  InvDomainTowerAlong ContactRepresentative RestrictedIdealExtension MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaG1PositiveNormalRepairCentres HironakaG1InitialSelectedOrderPhase HironakaG1InitialCompanionNormalTangent
  HironakaG1InitialCompanionZeroHistory HironakaG1InitialNormalSelectedSectionClass
  HironakaG1SeparateCarrierMemberCut HironakaG1OriginalContactClassAtStage
  HironakaG8LocalHistory HironakaG8LocalRestrictEquiv HironakaG8HomStable
  HironakaG11InvBMClass ContactStageKept BoundaryCount DivisorExponentAlong
  GeneralValue NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong

private theorem contact_refl_slots {m : ℕ} {Z : CMfd.{0} m}
    (J : MarkedIdeal m Z) (u : Z → ℂ) (W : Opens Z) :
    (contactMarkedKept J u (.refl (X := Z)) W).E =
      J.E.map ((Subtype.val : W → Z) ⁻¹' ·) := rfl

set_option maxHeartbeats 500000 in
/-- The original prescribed contact of the actual positive companion, at
the empty lower history, agrees in class and carrier with the supported
section selected member on the same nested opens. -/
theorem initial_companion_normal_section_contact {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X₀)
    let P := properNormalMarked Q
    let O := lowerMask P (s+1) H p
    let X := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) X := lowerMarkedM (X := X₀) P (s+1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let Y := CMfd.of (n := n+1) C
    let J : MarkedIdeal (n+1) Y := compAt (X := X) L L.d (.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    let B := barMarked (X := X₀) (supportedNormalMarked Q)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let R₁ := MarkedIdeal.pullback (Subtype.val : O → X₀) S
    let R₂ := MarkedIdeal.pullback (Subtype.val : C → X) R₁
    ∀ W : Opens Y,
      let K := contactMarkedKept J u (.refl (X := Y)) W
      let R := MarkedIdeal.pullback (Subtype.val : W → Y) R₂
      LocWPEquiv (X := CMfd.of (n := n+1) W) K R ∧ K.N = R.N ∧
      (∀ D ∈ K.E, D = ∅) := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ W K R
  let M := supportedNormalMarked Q
  let A := barMarked (X := X₀) P
  let F := companionOf (n+1) (M := X) L L.d
  have hOld : origMembers P H = A.E := List.take_length
  have hOldM : origMembers M H = B.E := List.take_length
  have hLevel' : boundaryCount A.E p = s+1 := by
    change boundaryCount (origMembers P H) p = s+1 at hLevel
    rwa [hOld] at hLevel
  have hp : 0 < boundaryCount P.E p := hLevel' ▸ Nat.succ_pos s
  have hP := properNormalMarked_isInvDomain Q hQ
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H trivial p hLevel
  obtain ⟨_, hJ, _, hu⟩ := initial_positive_companion_normal_tangent Q hQ p hLevel
  have hF := (original_initial_positive_lower_companion_recursion Q hQ p hLevel).1
  have hEq : MarkedIdeal.pullback (Subtype.val : C → X) F = J :=
    pullback_val_companionOf (Nat.succ_pos n) hL.isWellFormed hL.isNonzeroAlongAt C L.d
  have hLF : RestrictEquiv L F := by
    rw [show F = ⟨L.N, L.E, restrictOn (n+1) L.N L.ideal, L.d⟩ from
      (original_initial_positive_lower_companion_eq Q hQ p hLevel).2]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hL.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hLJ : RestrictEquiv (MarkedIdeal.pullback (Subtype.val : C → X) L) J := by
    rw [← hEq]
    exact restrictEquiv_pullback_val C hLF hL.isWellFormed.isCoherent hF.isWellFormed.isCoherent
  have hJR : LocWPEquiv (X := Y) J R₂ := by
    have hCut := member_stage_local_of_local (Nat.succ_pos n) P M hP hM hPM H trivial O p
    dsimp only [H, geoTransformAlong] at hCut
    rw [hOldM] at hCut
    have hCut' : LocWPEquiv (X := X) L R₁ := hCut
    exact (locWPEquiv_of_restrictEquiv (isInvDomain_pullback_val C hL) hJ hLJ).symm.trans
      (hCut'.restrict C)
  have hCt := original_bar_local_to_reference_contact J J hJ hJ rfl
    (LocEquiv.refl _ J) ⊤ u hu (.refl (X := Y)) trivial W (by
      change (W : Set Y) ⊆ Set.univ
      exact subset_univ _)
  have hBar := (bar_local_any_boundary J hJ).restrict W
  have hClass : LocWPEquiv (X := CMfd.of (n := n+1) W) K R :=
    hCt.symm.trans (hBar.symm.trans (hJR.restrict W))
  have hBase := (initial_normal_selected_section_wEquiv Q hQ p hp O hpO).2.1
  have hCarrier : L.N ∩ {x | relativeNormalCoordinate U (x : productOpen U) = 0} = R₁.N := by
    change (Subtype.val : O → X₀) ⁻¹' (A.N ∩ memberInter A.E (membersThrough A.E (origMembers P H) p))
      ∩ {x | relativeNormalCoordinate U (x : productOpen U) = 0} = R₁.N
    rw [hOld]
    exact hBase
  have hN : K.N = R.N := by
    change (Subtype.val : W → Y) ⁻¹' (J.N ∩ {x | u x = 0}) =
      (Subtype.val : W → Y) ⁻¹' ((Subtype.val : C → X) ⁻¹' R₁.N)
    rw [← hLJ.N_eq, ← hCarrier]
    rfl
  have hKE : K.E = J.E.map ((Subtype.val : W → Y) ⁻¹' ·) := contact_refl_slots J u W
  have hJE : ∀ D ∈ J.E, D = ∅ :=
    (initial_positive_companion_zero_history Q hQ p hLevel).1
  have hEmpty : ∀ D ∈ K.E, D = ∅ := by
    rw [hKE]
    intro D hD
    obtain ⟨D', hD', rfl⟩ := List.mem_map.mp hD
    rw [hJE D' hD', preimage_empty]
  exact ⟨hClass, hN, hEmpty⟩

set_option maxHeartbeats 700000 in
/-- A domain proof for the prescribed contact suffices to compare original
canonical histories with those of the actual nested supported section. -/
theorem initial_companion_normal_section_can_iff {n k s l : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X₀)
    let P := properNormalMarked Q
    let O := lowerMask P (s+1) H p
    let X := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) X := lowerMarkedM (X := X₀) P (s+1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let Y := CMfd.of (n := n+1) C
    let J : MarkedIdeal (n+1) Y := compAt (X := X) L L.d (.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    let B := barMarked (X := X₀) (supportedNormalMarked Q)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let R₁ := MarkedIdeal.pullback (Subtype.val : O → X₀) S
    let R₂ := MarkedIdeal.pullback (Subtype.val : C → X) R₁
    ∀ W : Opens Y,
      let K := contactMarkedKept J u (.refl (X := Y)) W
      let R := MarkedIdeal.pullback (Subtype.val : W → Y) R₂
      IsInvDomain l K →
      IsInvDomain l R ∧
      ∀ {Z : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) W) Z),
        IsCanonical K ((invFamily (Nat.succ_pos n) l).inv K) T ↔
          IsCanonical R ((invFamily (Nat.succ_pos n) l).inv R) T := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ W K R hK
  obtain ⟨hLoc, hN, hEmpty⟩ := initial_companion_normal_section_contact Q hQ p hLevel hpO W
  have hW : MarkedIdealEquivalence.MarkedIdeal.WEquiv
      (X := CMfd.of (n := n+1) W) K R := hLoc.wEquiv
  obtain ⟨_, hM, _⟩ := supported_normal_data Q hQ
  have hB : IsInvDomain k B := HironakaCoherentTransformExtension.isInvDomain_barMarked _ hM
  have hS : S.IsWellFormed :=
    isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed _
  have hR₁ : R₁.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hS O
  have hR₂ : R₂.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hR₁ C
  have hRWF : R.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hR₂ W
  have hd : 1 ≤ R.d := one_le_memberRestrict_d B (membersThrough B.E B.E p)
  have hR : IsInvDomain l R :=
    HironakaG1ChosenCommonContactClassData.isInvDomain_of_sameCarrier_cosupp
      (X := CMfd.of (n := n+1) W) R K hK hRWF.isCoherent hd hN.symm hW.1.symm hW.cosupp_eq.symm
  refine ⟨hR, fun T => ?_⟩
  have hInitial : ∀ D ∈ K.E, ∀ x ∈ K.cosupp, x ∈ D →
      R.d * divExpAlong (n+1) K.N K.ideal D x =
        K.d * divExpAlong (n+1) R.N R.ideal D x := by
    intro D hD x _ hx
    have hDE : D = ∅ := hEmpty D hD
    rw [hDE] at hx
    exact False.elim hx
  exact HironakaG1OriginalUnequalMarkCanonical.invFamily_isCanonical_iff_of_local
    (Nat.succ_pos n) K R hK hR hLoc (SameCarrierDim.of_N_eq hN) hInitial T

private theorem zero_contact_restrict_refl {m l : ℕ} (hm : 0 < m) {X : CMfd.{0} m}
    (C : Opens X) (J : MarkedIdeal m (CMfd.of (n := m) C)) (u : C → ℂ)
    (y : X) (hy : y ∈ C) {P : Prop}
    (h : let T := BlowupTowerTransforms.restrict C (.refl (X := X))
      let z : openPreimage (.refl (X := X)) C := ⟨y, hy⟩
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hm l) J) T →
        ¬ IsSpecial J T z → P ∧
          HironakaG1NormalContactChoiceTransfer.ZeroContactTransfer (k := l) hm J u T z)
    (hNS : ¬ IsSpecial J (.refl (X := CMfd.of (n := m) C)) (⟨y, hy⟩ : C)) :
    HironakaG1NormalContactChoiceTransfer.ZeroContactTransfer (k := l) hm J u
      (.refl (X := CMfd.of (n := m) C)) (⟨y, hy⟩ : C) :=
  (h trivial hNS).2

set_option maxHeartbeats 1000000 in
/-- At a nonspecial surviving point of the empty companion history, the
actual finite zero contact supplies the supported branch's domain and CAN
on its literal zero mask. -/
theorem initial_companion_normal_section_finite_refl {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X₀)
    let P := properNormalMarked Q
    let O := lowerMask P (s+1) H p
    let X := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) X := lowerMarkedM (X := X₀) P (s+1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let Y := CMfd.of (n := n+1) C
    let J : MarkedIdeal (n+1) Y := compAt (X := X) L L.d (.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    let B := barMarked (X := X₀) (supportedNormalMarked Q)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let R₁ := MarkedIdeal.pullback (Subtype.val : O → X₀) S
    let R₂ := MarkedIdeal.pullback (Subtype.val : C → X) R₁
    ∀ (y : O) (hyC : y ∈ C),
      let z : C := ⟨y, hyC⟩
      let W := maskB J (.refl (X := Y)) z
      let K := contactMarkedKept J u (.refl (X := Y)) W
      let R := MarkedIdeal.pullback (Subtype.val : W → Y) R₂
      y ∈ L.cosupp → ¬ IsSpecial J (.refl (X := Y)) z →
      ∃ hz : z ∈ W,
        let r : W := ⟨z, hz⟩
        IsInvDomain k K ∧ IsInvDomain k R ∧ r ∈ R.cosupp ∧
        IsCanonical R ((invFamily (Nat.succ_pos n) k).inv R) (.refl (X := CMfd.of (n := n+1) W)) ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) J (.refl (X := Y)) z =
          toLex (0, ((invFamily (Nat.succ_pos n) k).inv K
            (.refl (X := CMfd.of (n := n+1) W)) r : WithTop (ValTy k))) := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ y hyC z W K R hy hNS
  obtain ⟨hyC', hFinite⟩ := initial_positive_companion_zero_contact_value Q hQ p hLevel
    (.refl (X := X)) y hy trivial
  have hTransfer := zero_contact_restrict_refl (l := k) (Nat.succ_pos n) C J u y hyC hFinite hNS
  obtain ⟨hz, _, hK, _, hcK, hKos, _, hValue⟩ := hTransfer
  have hz' : z ∈ W := hz
  have hK' : IsInvDomain k K := hK
  have hCan := initial_companion_normal_section_can_iff Q hQ p hLevel hpO W hK'
  have hLoc := (initial_companion_normal_section_contact Q hQ p hLevel hpO W).1
  have hW : MarkedIdealEquivalence.MarkedIdeal.WEquiv
      (X := CMfd.of (n := n+1) W) K R := hLoc.wEquiv
  have hKos' : (⟨z, hz'⟩ : W) ∈ K.cosupp := hKos
  exact ⟨hz', hK', hCan.1, hW.cosupp_eq ▸ hKos', (hCan.2 _).mp hcK, hValue⟩

end
end Hironaka.HironakaG1InitialCompanionSectionComparison
