import Hironaka.Resolution.HironakaG1ChronologicalSurvivorSymmetry

/-! # Actual mixed maxima under marked tower symmetry -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1MixedMaskSymmetry
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HomogenizedIdealAlong
  StepOneValue StepOneRegime HironakaG1ProperCarrierNormalContact
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1LaterPositiveBranchOrder
  HironakaG1LaterPositiveStratumCentres HironakaG1LaterMixedUpperBornTrace
  HironakaG1LaterMixedLiveCentres HironakaG1InitialPositiveGeneralRead

set_option maxHeartbeats 1100000 in
/-- Under a tested tower isomorphism the literal positive mask is the
preimage of the target mask, including its interior and each retained
boundary condition. -/
theorem positive_mask_preimage_of_towerIso {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (J : MarkedIdeal n X₂) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d)
    (φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (χ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    (hIso : IsTowerIso φ T₁ T₂ χ) (hT : IsGeoTestTower (barMarked J) T₂) (p : Y₁) :
    (maskA (pullback φ J) T₁ p : Set Y₁) = χ ⁻¹' (maskA J T₂ (χ p) : Set Y₂) := by
  have hOrig := ContactLowerValue.origMembers_isTowerIso φ J hJ hd hIso hT
  have hFacts := (StepOneTowerIso.isTowerIso_facts φ J hJ hd hIso hT).2.2
  change interior _ = χ.toHomeomorph ⁻¹' interior _
  rw [χ.toHomeomorph.preimage_interior]
  congr 1
  ext z
  change ((_ ∧ ¬ (_ ∧ _)) ↔ (_ ∧ ¬ (_ ∧ _)))
  rw [(hFacts z).1, (hFacts p).1, (hFacts z).2.1, hOrig]
  apply and_congr_left'
  constructor
  · intro h H hH hz
    exact h (χ ⁻¹' H) (List.mem_map_of_mem hH) hz
  · intro h D hD hz
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hD
    exact h H hH hz

section Mixed

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n+1)}
  (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)

local notation "X₀" => CMfd.of (n := n+1) (productOpen U)
local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1)) P
local notation "v" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC
local notation "C₀" => (MarkedIdeal.cosupp (geoTransformAlong P T))
local notation "S₀" => positiveLevelStratum Q T s
local notation "E₀" => Set.ofPred (fun a : S₀ => IsSpecial SEC T (Subtype.val a))
local notation "countAt" => upperHeadNonOriginalBoundaryCount Q T s

/-- An actual upper tower symmetry preserving both literal marked source
records. Its endpoints and masks are then compared by the tested tower
naturality lemmas. -/
structure MixedTowerSymmetry where
  source : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel (n+1)), 𝓘(ℂ, ComplexModel (n+1))⟯ X₀
  target : Y ≃ₘ⟮𝓘(ℂ, ComplexModel (n+1)), 𝓘(ℂ, ComplexModel (n+1))⟯ Y
  tower : IsTowerIso source T T target
  padded : pullback source P = P
  sectionRecord : pullback source SEC = SEC

set_option maxHeartbeats 1000000 in
/-- Both section branch labels and actual padded upper run lengths are
preserved by the same marked symmetry. -/
theorem MixedTowerSymmetry.preserves_section_and_upper_run
    (A : MixedTowerSymmetry Q T) (hQ : IsInvDomain (k+1) Q)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (y : Y) :
    (IsSpecial SEC T y ↔ IsSpecial SEC T (A.target y)) ∧
    regimeRun (stepRegime P (s+1)) T y = regimeRun (stepRegime P (s+1)) T (A.target y) := by
  have hP := properNormalMarked_isInvDomain Q hQ
  have hPM := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hSec : IsInvDomain (k+1) SEC :=
    HironakaActualSectionBoundaryGeometry.section_projected_domain (k+1) Q.N Q.E Q.ideal Q.d hQ
  have hTB := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) (k+1)) P hP hPM (Nat.succ_pos n) T hCan).1
  have hTS := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) k) SEC hSec hMax (Nat.succ_pos n) T hSecCan).1
  have hSp := ((StepOneTowerIso.isTowerIso_facts A.source SEC hSec.isWellFormed
    hSec.one_le_d A.tower hTS).2.2 y).2.1
  rw [A.sectionRecord] at hSp
  refine ⟨hSp, ?_⟩
  exact NonmonomialOrderRegime.regimeRun_isTowerIso_of (stepRegime P (s+1))
    (stepRegime P (s+1)) (fun {Z} (S : BlowupTower X₀ Z) => IsGeoTestTower (barMarked (X := X₀) P) S)
    (fun _ _ _ _ h => h.1)
    (fun S₁ S₂ ψ hψ hS q => by
      have h := ((StepOneTowerIso.isTowerIso_facts A.source P hP.isWellFormed
        hP.one_le_d hψ hS).2.2 q).2.2 (s+1)
      rw [A.padded] at h
      exact h) A.tower hTB y

set_option maxHeartbeats 1300000 in
/-- At the actual upper run cut the same symmetry identifies both masked
tails. The common run length is obtained from the tested history. -/
theorem MixedTowerSymmetry.actual_positive_masks
    (A : MixedTowerSymmetry Q T) (hQ : IsInvDomain (k+1) Q)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (y : Y) :
    let j := regimeRun (stepRegime P (s+1)) T y
    let H := head T j
    let R := tail T j
    let O₁ := maskA P H (R.proj y)
    let O₂ := maskA P H (R.proj (A.target y))
    regimeRun (stepRegime P (s+1)) T (A.target y) = j ∧
      ∃ ψ : (split T j).1 ≃ₘ⟮𝓘(ℂ, ComplexModel (n+1)), 𝓘(ℂ, ComplexModel (n+1))⟯ (split T j).1,
        IsTowerIso A.source H H ψ ∧ IsTowerIso ψ R R A.target ∧
          (O₁ : Set (split T j).1) = ψ ⁻¹' (O₂ : Set (split T j).1) := by
  intro j H R O₁ O₂
  have hP := properNormalMarked_isInvDomain Q hQ
  have hPM := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTB := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) (k+1)) P hP hPM (Nat.succ_pos n) T hCan).1
  have hRun := (MixedTowerSymmetry.preserves_section_and_upper_run Q T A hQ hCan hMax hSecCan (s := s) y).2
  have hH := ((isGeoTestTower_iff_head_tail (barMarked P) T j).mp hTB).1
  obtain ⟨ψ, hIsoH, hIsoR⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split A.tower j
  have hm := positive_mask_preimage_of_towerIso P hP.isWellFormed hP.one_le_d
    A.source ψ hIsoH hH (R.proj y)
  rw [A.padded, hIsoR.proj_comm y] at hm
  exact ⟨hRun.symm, ψ, hIsoH, hIsoR, hm⟩

set_option maxHeartbeats 1100000 in
/-- Actual upper raw values and the live companion letters agree at
anchors related by a marked symmetry, regardless of retained count. -/
theorem MixedTowerSymmetry.companion_eq
    (A : MixedTowerSymmetry Q T) (hQ : IsInvDomain (k+1) Q)
    (hCan : IsCanonical P f T)
    (a b : S₀) (hab : A.target a.val = b.val)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s) :
    (F a).companion = (F b).companion := by
  have hP := properNormalMarked_isInvDomain Q hQ
  have hPM := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have h := Seq.StepOneBridge.towerIso_field (invFamily (Nat.succ_pos n) (k+1))
    P A.source hP hPM (Nat.succ_pos n) T T A.target A.tower hCan a.val
    (hab.symm ▸ b.property.1)
  rw [A.padded, hab, (F a).raw_upper, (F b).raw_upper] at h
  have hInner := congrArg (fun w : ℕ ×ₗ WithTop (ValTy (k+1)) => (ofLex w).2) h
  have hSuccess := WithTop.coe_inj.mp hInner
  have hValue := congrArg (fun w : ValTy (k+1) => ofLex ((ofLex w).2)) hSuccess
  exact WithTop.coe_inj.mp (Sum.inr.inj hValue)

set_option maxHeartbeats 1100000 in
/-- If the section-special anchors form one orbit, their actual retained
counts and live leaves agree. Section-finite anchors lying strictly
below the maximal retained count need no recursive comparison. -/
theorem later_mixed_max_eq_of_section_special_orbit
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (ref : S₀) (hRef : ref ∈ E₀)
    (hOrbit : ∀ a ∈ E₀, ∃ A : MixedTowerSymmetry Q T, A.target a.val = ref.val)
    (hOff : ∀ a ∉ E₀, countAt a.val < countAt ref.val) :
    maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  have hLetter (a : S₀) (ha : a ∈ E₀) : (F a).companion = (F ref).companion := by
    obtain ⟨A, hA⟩ := hOrbit a ha
    exact MixedTowerSymmetry.companion_eq Q T A hQ hCan a ref hA F
  have readCount (a : S₀) : (ofLex (F a).companion).1 = countAt a.val :=
    laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan a.val
      a.property.1 a.property.2 (hNS a) (F a)
  have hTie (a : S₀) (ha : a ∈ E₀) : countAt a.val = countAt ref.val :=
    (readCount a).symm.trans ((congrArg (fun c => (ofLex c).1) (hLetter a ha)).trans (readCount ref))
  apply (later_mixed_max_eq_iff_max_count_and_live_leaf Q T hQ hT hCan hMax hSecCan
    hBound F hNS ref hRef).mpr
  refine ⟨⟨ref.property, fun y hy => ?_⟩, ?_, fun a ha he => ((lt_irrefl _) (he ▸ hOff a ha)).elim⟩
  · by_cases hm : (⟨y, hy⟩ : S₀) ∈ E₀
    · exact (hTie ⟨y, hy⟩ hm).le
    · exact (hOff ⟨y, hy⟩ hm).le
  · intro a ha
    exact ⟨hTie a ha, congrArg (fun c => (ofLex c).2) (hLetter a ha)⟩

end Mixed
end
end Hironaka.HironakaG1MixedMaskSymmetry
