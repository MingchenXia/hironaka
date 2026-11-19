import Hironaka.Resolution.HironakaG1InitialCompanionSectionSpecialRead
import Hironaka.Resolution.HironakaG8ScaledCompanionStageOpen
import Hironaka.Resolution.HironakaG1OriginalStepSkeleton

/-! Specialness transfers across the two literal initial order masks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialCompanionSectionSpecialTransfer
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  StepOneValue StepOneValueMasked GeneralValue GeneralCompare NonmonomialOrderLocal NonmonomialOrderTail
  CompanionRebase CompanionReductionAlong InvDomainMemberRestriction CanonicalCentres
  ContactStageKept HironakaG1InitialCompanionSectionComparison HironakaG1InitialCompanionSectionSpecialRead
  HironakaG1LocalOffBoundary HironakaG8MixedOrderInvariance HironakaG8LocalHistory
  HironakaG8ScaledCompanionStageOpen HironakaG1OriginalStepSkeleton
  MarkedIdealOperationsAlong RestrictedIdealExtension DivisorExponentAlong GermIdealOrder
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials

private theorem order_data_of_empty_slots {m k : ℕ} {X : CMfd.{0} m}
    (A : MarkedIdeal m X) (hA : IsInvDomain k A) (he : ∀ D ∈ A.E, D = ∅) :
    (∀ x ∈ A.cosupp, A.d ≤ nmOrd A x) ∧ (∀ (q : ℕ), A.d ≤ q → ordGe A q ⊆ A.cosupp) := by
  have hOff (x : X) (i : Fin A.E.length) : x ∉ A.E.get i := by
    rw [he _ (List.get_mem _ i)]
    exact notMem_empty x
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [nmOrd_eq_ordinaryTraceOrder_of_notMem A (hOff x)]
    exact mark_le_ordinaryTraceOrder A hA hx
  · intro q hq x hx
    have hr := (HironakaG8MixedOrderInvariance.mem_cosupport_congr
      (nmPart_mem_iff_of_notMem A (hOff x)) q).mp hx
    exact cosupport_anti hq
      (cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hA.isWellFormed.isCoherent) q hr)

private theorem special_on_cast_mask {m k : ℕ} {X : CMfd.{0} m} (hm : 0 < m)
    (A : MarkedIdeal m X) (hA : IsInvDomain k A) (x : X) (ho : 1 ≤ nmOrd A x)
    (C : Opens X) (hC : C = ordMask A (nmOrd A x)) (hx : x ∈ C) :
    let Z := CMfd.of (n := m) C
    let F := companionOf m (M := Z) (MarkedIdeal.pullback (Subtype.val : C → X) A) (nmOrd A x)
    IsInvDomain k F ∧
      (IsSpecial F (.refl (X := Z)) (⟨x, hx⟩ : C) ↔ InitialOrderSpecial A x (hC ▸ hx)) := by
  subst C
  exact ⟨isInvDomain_compAt hm ho (.refl (X := X)) hA, Iff.rfl⟩

set_option maxHeartbeats 1000000 in
/-- Empty retained slots force the true initial masks to coincide at
corresponding raw orders. The actual companions have the same specialness. -/
theorem initial_order_special_iff_of_empty_slots {m k l : ℕ} {X : CMfd.{0} m}
    (hm : 0 < m) (A B : MarkedIdeal m X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (he : ∀ D ∈ A.E, D = ∅)
    (x : X) (hx : x ∈ A.cosupp) :
    let a := nmOrd A x
    let b := nmOrd B x
    ordMask A a = ordMask B b ∧
      ∃ (ha : x ∈ ordMask A a) (hb : x ∈ ordMask B b),
        InitialOrderSpecial A x ha ↔ InitialOrderSpecial B x hb := by
  intro a b
  have hE := hL.wEquiv.1
  have hBE : ∀ D ∈ B.E, D = ∅ := fun D hD => he D (hE.symm ▸ hD)
  have hxB := hL.cosupp_eq_base ▸ hx
  obtain ⟨ha, hAboveA⟩ := order_data_of_empty_slots A hA he
  obtain ⟨hb, hAboveB⟩ := order_data_of_empty_slots B hB hBE
  have haPos : 1 ≤ a := hA.one_le_d.trans (ha x hx)
  have hbPos : 1 ≤ b := hB.one_le_d.trans (hb x hxB)
  have hScale (y : X) (hy : y ∈ A.cosupp) : B.d * nmOrd A y = A.d * nmOrd B y :=
    nmOrd_along_local_off_boundary A B hA hB hN hL (.refl (X := X)) trivial y hy
      (fun D hD => he D hD ▸ notMem_empty y)
  have hMasks : ordMask A a = ordMask B b := by
    ext y
    change y ∈ ordMask A a ↔ y ∈ ordMask B b
    rw [mem_ordMask_iff hm hA.isWellFormed hA.isNonzeroAlongAt,
      mem_ordMask_iff hm hB.isWellFormed hB.isNonzeroAlongAt]
    apply not_congr
    constructor
    · intro hy
      have hyA : y ∈ A.cosupp := hAboveA _ (by have := ha x hx; omega) hy
      have hyB : y ∈ B.cosupp := hL.cosupp_eq_base ▸ hyA
      have hgt : a < nmOrd A y :=
        (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt (ordGe_subset_N A _ hy) _).mp hy
      have hs := Nat.mul_lt_mul_of_pos_left hgt hB.one_le_d
      rw [hScale x hx, hScale y hyA] at hs
      exact (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (B.cosupp_subset_N hyB) _).mpr
        (Nat.lt_of_mul_lt_mul_left hs)
    · intro hy
      have hyB : y ∈ B.cosupp := hAboveB _ (by have := hb x hxB; omega) hy
      have hyA : y ∈ A.cosupp := hL.cosupp_eq_base.symm ▸ hyB
      have hgt : b < nmOrd B y :=
        (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (ordGe_subset_N B _ hy) _).mp hy
      have hs := Nat.mul_lt_mul_of_pos_left hgt hA.one_le_d
      rw [← hScale x hx, ← hScale y hyA] at hs
      exact (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt (A.cosupp_subset_N hyA) _).mpr
        (Nat.lt_of_mul_lt_mul_left hs)
  let C := ordMask A a
  let Z := CMfd.of (n := m) C
  let F := companionOf m (M := Z) (MarkedIdeal.pullback (Subtype.val : C → X) A) a
  let G := companionOf m (M := Z) (MarkedIdeal.pullback (Subtype.val : C → X) B) b
  have hxC : x ∈ C :=
    (proj_tail_mem_ordMask (𝔪 := A) hm hA (.refl (X := X)) trivial hx (o := a) rfl).2
  obtain ⟨hF, hSA⟩ := special_on_cast_mask hm A hA x haPos C rfl hxC
  obtain ⟨hG, hSB⟩ := special_on_cast_mask hm B hB x hbPos C hMasks hxC
  have hInitial : ∀ D ∈ A.E, ∀ y ∈ A.cosupp, y ∈ D →
      B.d * divExpAlong m A.N A.ideal D y = A.d * divExpAlong m B.N B.ideal D y := by
    intro D hD y _ hy
    rw [he D hD] at hy
    exact False.elim hy
  have hFG : LocWPEquiv (X := Z) F G :=
    scaled_companions_local_stage_open hm A B hA hB hN.symm hE.symm hL hInitial
      (.refl (X := X)) trivial haPos (hScale x hx) C le_rfl
  have hNFG : F.N = G.N := by
    simp only [F, G, companionOf, companionAlong_N, MarkedIdeal.pullback, hN]
  have hSp := (original_step_skeleton_of_wEquiv hm F G hF hG hNFG hFG.wEquiv
    (.refl (X := Z)) trivial (⟨x, hxC⟩ : C)).2.1
  exact ⟨hMasks, hxC, hMasks ▸ hxC, hSA.symm.trans (hSp.trans hSB)⟩

set_option maxHeartbeats 900000 in
/-- On the actual finite zero mask, the two next order masks agree and the
special payload formula requires only the prescribed contact's specialness. -/
theorem initial_companion_normal_section_finite_special_read {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+2) Q) (p : productOpen U)
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
        let Z := CMfd.of (n := n+1) W
        let T := BlowupTower.refl (X := Z)
        let V := invFamily (Nat.succ_pos n) (k+1)
        let a := nmOrd (M := Z) K r
        let b := nmOrd (M := Z) R r
        let topRead : ℕ → ValTy (k+1) := fun o =>
          toLex (o, toLex (Sum.inr (↑(toLex (0, (⊤ : WithTop (ValTy k)))) :
            WithTop (ℕ ×ₗ WithTop (ValTy k)))))
        ordMask (M := Z) K a = ordMask (M := Z) R b ∧
        ∃ (hK : r ∈ ordMask (M := Z) K a) (hR : r ∈ ordMask (M := Z) R b),
          (InitialOrderSpecial (X := Z) K r hK ↔ InitialOrderSpecial (X := Z) R r hR) ∧
          (InitialOrderSpecial (X := Z) K r hK →
          Seq.StepOneValueMasked.stepOneInvM V J (.refl (X := Y)) z =
            toLex (0, (topRead ((K.d / R.d) * b) : WithTop (ValTy (k+1)))) ∧
          V.inv R T r = topRead b) := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ y hyC z W K R hy hNS
  obtain ⟨hz, hK, hR, hrR, _, _⟩ :=
    initial_companion_normal_section_finite_refl (k := k+1) Q hQ p hLevel hpO y hyC hy hNS
  let r : W := ⟨z, hz⟩
  let Z := CMfd.of (n := n+1) W
  obtain ⟨hClass, hN, hEmpty⟩ := initial_companion_normal_section_contact Q hQ p hLevel hpO W
  have hLoc : LocWPEquiv (X := Z) K R := hClass
  have hrK : r ∈ K.cosupp := hLoc.cosupp_eq_base.symm ▸ hrR
  obtain ⟨hMasks, _, _, hSp⟩ :=
    initial_order_special_iff_of_empty_slots (X := Z) (Nat.succ_pos n) K R hK hR hN hLoc hEmpty r hrK
  obtain ⟨hz', hmK, hmR, hRead⟩ :=
    initial_companion_normal_section_finite_special_reads Q hQ p hLevel hpO y hyC hy hNS
  refine ⟨hz, hMasks, hmK, hmR, hSp, fun hsK => ?_⟩
  exact hRead hsK (hSp.mp hsK)

end
end Hironaka.HironakaG1InitialCompanionSectionSpecialTransfer
