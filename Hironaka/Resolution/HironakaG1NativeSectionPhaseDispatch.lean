import Hironaka.Resolution.HironakaG1NativePositivePhase
import Hironaka.Resolution.HironakaG1NativeSectionEvaluator

/-! Actual native section histories dispatched by the original Step One guards. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set TopologicalSpace

namespace Hironaka.HironakaG1NativeSectionPhaseDispatch

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  SubmanifoldChartedSpace HomogenizedGlueingTower HomogenizedIdealAlong
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualNativeSectionFiniteHistory HironakaActualSectionBoundaryDimension
  HironakaG1RecursiveMemberValueTransport HironakaG1NativePositivePhase HironakaG1NativeSectionEvaluator

/-- At a supported endpoint on the literal section, the special guard
gives the exact top value. Each finite branch produces its own native
canonical lower suffix at the actual attained level, retaining the
literal phase record and reading the original masked evaluator. -/
theorem native_literal_section_phase_dispatch {n k : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp) :
    let Sec := sectionMarked Q
    let l := level Sec T y
    let j := regimeRun (stepRegime Sec l) T y
    let H := head T j
    let S := tail T j
    let p := S.proj y
    let out := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) Sec T y
    (IsSpecial Sec T y ∧ out = toLex (l,(⊤ : WithTop (ValTy k)))) ∨
    (¬ IsSpecial Sec T y ∧
      ∃ (O : Opens (split T j).1) (hp : p ∈ O) (P : MarkedIdeal (n+1) O),
        ((l = 0 ∧ O = maskB Sec H p ∧ HEq P (lowerMarkedM Sec 0 H p)) ∨
         (0 < l ∧ P = positiveMemberOn Sec H p O)) ∧
        let A := CMfd.of (n := n+1) O
        let D := CMfd.of (n := n+1) (openPreimage S O)
        let G := restrict O S
        ∃ (W : Set A) (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n),
        W = (Subtype.val : O → _) ⁻¹' strictAlong H (zeroPlane U) ∧
        ∃ (V : Set D) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n+1) V z n)
          (N : BlowupTower (nativeManifold (Nat.le_succ n) W hW)
            (nativeManifold (Nat.le_succ n) V hV)),
          Lift (Nat.le_succ n) W hWc hW P.E G V hVc hV N ∧
          let PN := nativePullback (Nat.le_succ n) W hW P
          IsInvDomain k PN ∧ IsCanonical PN ((invFamily hn k).inv PN) N ∧
            IsGeoTestTower PN N ∧ N.length = G.length ∧
            geoTransformAlong PN N = nativePullback (Nat.le_succ n) V hV (geoTransformAlong P G) ∧
            ∃ z : nativeManifold (Nat.le_succ n) V hV,
              z.val = (⟨y,hp⟩ : openPreimage S O) ∧ z ∈ (geoTransformAlong PN N).cosupp ∧
              out = toLex (l,(sameIndexMap 1 k ((invFamily hn k).inv PN N z) : WithTop (ValTy k)))) := by
  by_cases hs : IsSpecial (sectionMarked Q) T y
  · apply Or.inl
    refine ⟨hs,?_⟩
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hs]
  · apply Or.inr
    refine ⟨hs,?_⟩
    dsimp only
    cases hLevel : level (sectionMarked Q) T y with
    | zero =>
        obtain ⟨hp,W,hWc,hW,hW_eq,V,hVc,hV,N,hLift,hDom,hNCan,hTest,hLen,hWhole,z,hz,hzN,hRead⟩ :=
          native_section_zero_evaluator hn Q hQ T hMax hCan y hy hLevel hs
        exact ⟨_,hp,_,Or.inl ⟨rfl,rfl,HEq.rfl⟩,W,hWc,hW,hW_eq,V,hVc,hV,N,
          hLift,hDom,hNCan,hTest,hLen,hWhole,z,hz,hzN,hRead⟩
    | succ s =>
        obtain ⟨O,u,hp,hComp,W,hWc,hW,hW_eq,hSub,hTrans,V,hVc,hV,N,hLift,hDom,hTest,
            hCDom,hCCan,hCVal,hNCan,hWhole,hCos,z,hz,hzN,hRead⟩ :=
          exists_actual_positive_selected_native_phase hn Q hQ T hMax hCan y hy hLevel hs
        exact ⟨O,hp,_,Or.inr ⟨Nat.succ_pos _,rfl⟩,W,hWc,hW,hW_eq,V,hVc,hV,N,
          hLift,hDom,hNCan,hTest,hLift.length,hWhole,z,hz,hzN,hRead⟩

#print axioms native_literal_section_phase_dispatch

end Hironaka.HironakaG1NativeSectionPhaseDispatch
