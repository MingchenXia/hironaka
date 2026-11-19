import Hironaka.Resolution.HironakaOriginalNCCountHistory
import Hironaka.Resolution.HironakaOriginalNCCoefficientZeroFinish

set_option autoImplicit false

/-!
# One original H-sensitive causal value, independent of any output resolution

The birth frame is formed directly from original M/H, the SAME actual T
and endpoint y. Its cut is the intrinsic oldCount low set, its year is the
actual Nat.find birth, and its tail keeps every empty step. In particular
the coefficient-birth value is used ALSO at count zero.

Actual birth domains are produced for EVERY genuine original history,
including new births inside a later nonempty phase. No completed old L_r
test/resolution, caller empty suffix or caller canonicality is needed.

This fixes the single original value object for the remaining state/phase
induction. It does not prove all its maximum-centre/naturality fields or
the total original NC canonical driver.

Blueprint: hironaka-original-nc-causal-history-value-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCCausalHistoryValue

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder GermIdealPullbackCalculus DivisorExponentAlong
  CoefficientIdeal CoefficientIdealRestriction HomogenizedGlueingTower
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderGlueing
  HironakaBoundaryCoefficientStratumResolution
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCCountHistory
  HironakaOriginalNCCoefficientZeroFinish
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem isOpen_oldCount_le (H : Set X) (T : BlowupTower X Y) (q : ℕ) :
    IsOpen {z | oldCount H T z ≤ q} := by
  by_cases hNC : IsNormalCrossingsCarrier (n := n) (strictAlong T H)
  · have hSet : {z | oldCount H T z ≤ q} = {z | q + 1 ≤ branchMultiplicity hNC z}ᶜ := by
      ext z
      change (oldCount H T z ≤ q) ↔ ¬ q + 1 ≤ branchMultiplicity hNC z
      rw [oldCount_eq T hNC]
      omega
    rw [hSet]
    exact (isClosed_branchMultiplicity_superlevel hNC (q + 1)).isOpen_compl
  · simpa only [oldCount, dif_neg hNC, Nat.zero_le, ofPred_true] using (isOpen_univ : IsOpen (univ : Set Y))

/-- The actual intrinsic low open is determined by H/T/q alone. The existing
oldCount fallback yields the whole open when the current carrier is not NC;
the genuine history theorem below excludes that fallback where it is used. -/
def oldCountLowOpen (H : Set X) (T : BlowupTower X Y) (q : ℕ) : Opens Y :=
  ⟨{z | oldCount H T z ≤ q}, isOpen_oldCount_le H T q⟩

/-- No phase or completed resolution is consulted to select the actual birth open. -/
def causalBirthOpen (H : Set X) (T : BlowupTower X Y) (y : Y) :
    Opens (split T (T.length - birthYear H T y)).1 :=
  oldCountLowOpen H (head T (T.length - birthYear H T y)) (oldCount H T y)

/-- The whole original parent at the actual first-current-count year, restricted
to its specified low open, retaining the entire ordered boundary. -/
def causalBirthParent (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (y : Y) :
    MarkedIdeal n (causalBirthOpen H T y) :=
  MarkedIdeal.pullback
    (Subtype.val : causalBirthOpen H T y → (split T (T.length - birthYear H T y)).1)
    (geoTransformAlong M (head T (T.length - birthYear H T y)))

/-- This set uses the intrinsic original history count, with no choice of branch labels. -/
def causalBirthStratum (H : Set X) (T : BlowupTower X Y) (y : Y) : Set (causalBirthOpen H T y) :=
  {z | oldCount H T y ≤ oldCount H (head T (T.length - birthYear H T y)) z.val}

/-- The causal birth coefficient remainder is formed from the original parent
and actual count stratum, independently of any chosen resolving future. -/
def causalBirthRemainder (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (y : Y) :
    MarkedIdeal n (causalBirthOpen H T y) :=
  contactRemainderMarked (withN (coeffMarked (causalBirthParent M H T y)) (causalBirthStratum H T y)) 0

/-- The SAME literal birth suffix is restricted, retaining every actual empty year. -/
def causalBirthTail (H : Set X) (T : BlowupTower X Y) (y : Y) :
    BlowupTower (CMfd.of (n := n) (causalBirthOpen H T y))
      (CMfd.of (n := n) (openPreimage (tail T (T.length - birthYear H T y)) (causalBirthOpen H T y))) :=
  restrict (causalBirthOpen H T y) (tail T (T.length - birthYear H T y))

private theorem causalBirthProjection_mem (H : Set X) (T : BlowupTower X Y) (y : Y) :
    (tail T (T.length - birthYear H T y)).proj y ∈ causalBirthOpen H T y := by
  change oldCount H (head T (T.length - birthYear H T y))
      ((tail T (T.length - birthYear H T y)).proj y) ≤ oldCount H T y
  have hs := birthYear_spec H T y
  rw [countAt_eq_prefix_count] at hs
  exact hs.le

/-- First attainment of the current count internally constructs the actual
point of the uncompressed restricted birth suffix. -/
def causalBirthPoint (H : Set X) (T : BlowupTower X Y) (y : Y) :
    openPreimage (tail T (T.length - birthYear H T y)) (causalBirthOpen H T y) :=
  ⟨y, causalBirthProjection_mem H T y⟩

/-- ONE original old-carrier-sensitive value. It reads only M/H and the actual
current T/y, and preserves the coefficient-birth numerical branch at q=0.
The mask is the actual transformed birth remainder cosupport. -/
def causalHistoryValue (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (y : Y) :
    ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
  toLex (oldCount H T y,
    if causalBirthPoint H T y ∈
        (geoTransformAlong (causalBirthRemainder M H T y) (causalBirthTail H T y)).cosupp then
      ((CanonicalCentres.canonicalInvariant n).inv (causalBirthRemainder M H T y)
        (causalBirthTail H T y) (causalBirthPoint H T y) : WithBot (CanonicalCentres.ValTy n))
    else ⊥)

/-- The actual phase-boundary induction state keeps all empty historical years;
it is proved by the algorithm and is not a caller input to the final driver. -/
def HasEmptyCausalBirthTails (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) : Prop :=
  ∀ y ∈ (geoTransformAlong M T).cosupp, IsEmptyTower (causalBirthTail H T y)

private theorem coefficient_positive {B : CMfd.{u} n} (M : MarkedIdeal n B) : 1 ≤ (coeffMarked M).d := by
  change 1 ≤ (Finset.range M.d).prod (fun i => M.d - i)
  have hp : 0 < (Finset.range M.d).prod (fun i => M.d - i) :=
    Finset.prod_pos fun i hi => by
      have hi' := Finset.mem_range.mp hi
      omega
  omega

private theorem ambient_domain (M : MarkedIdeal n X) (hN : M.N = univ)
    (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hne : ∀ x, IsNonzeroAlongAt univ M.ideal x) (hE : IsSNCDivisor n M.E) :
    IsInvDomain n M := by
  refine ⟨⟨?_, hI, hE, ?_⟩, ?_, hd, ?_⟩
  · rw [hN]
    exact isClosedSubmanifold_univ
  · rw [hN]
    exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE
  · rw [hN]
    exact fun x _ => ⟨n, le_rfl, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  · intro x _hx
    simpa only [hN] using hne x

/-- Every actual original history, including one with a new drop INSIDE a
later phase, internally supplies the TRUE causal birth remainder domain.
No completed coefficient resolution or canonical/empty tail is assumed. -/
theorem causalBirthRemainder_domain (M : MarkedIdeal n X) (hN : M.N = univ)
    (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y) :
    IsInvDomain n (causalBirthRemainder M H T y) ∧
      (causalBirthRemainder M H T y).E = (causalBirthParent M H T y).E ∧
      (causalBirthParent M H T y).N = univ ∧
      (causalBirthParent M H T y).ideal.IsCoherent ∧ 1 ≤ (causalBirthParent M H T y).d := by
  let k := T.length - birthYear H T y
  let K := head T k
  let W := causalBirthOpen H T y
  let MW := causalBirthParent M H T y
  let q := oldCount H T y
  let hc := currentPair_head M hN hI h T hT hHistory k
  let hW := boundaryAdapted_open W hc
  have hKTest := ((isGeoTestTower_iff_head_tail M T k).mp hT).1
  have hKI : (geoTransformAlong M K).ideal.IsCoherent :=
    (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪 := M) (hN ▸ isClosedSubmanifold_univ) hI K hKTest).2
  have hKN : (geoTransformAlong M K).N = univ :=
    (DerivativeIdealTower.inclusions_tower M hN hI (j := 0) (Nat.zero_le _) K hKTest).2.1
  have hMWN : MW.N = univ := by
    change (Subtype.val : W → (split T k).1) ⁻¹' (geoTransformAlong M K).N = univ
    rw [hKN, preimage_univ]
  have hMWI : MW.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hKI
  have hMWd : 1 ≤ MW.d := by
    change 1 ≤ (geoTransformAlong M K).d
    rw [d_geoTransformAlong]
    exact hd
  have hCount : ∀ z : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z = oldCount H K z.val := by
    intro z
    exact (branchMultiplicity_open W (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted hW) z).trans
        (oldCount_eq K (isNormalCrossingsCarrier_of_boundaryAdapted hc) z.val).symm
  have hBound : ∀ z : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z ≤ q := by
    intro z
    exact (hCount z).trans_le z.property
  have hStratum : causalBirthStratum H T y =
      {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z} := by
    ext z
    change (q ≤ oldCount H K z.val) ↔ q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z
    rw [hCount z]
  let Z := {z : W | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z}
  let L := withN (coeffMarked MW) Z
  have hZ : IsClosedSubmanifold n Z :=
    isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted hW) hBound
  have hLI : L.ideal.IsCoherent :=
    isCoherent_coeffMarked (X := CMfd.of (n := n) W) (𝔪 := MW) hMWN hMWI
  have hLW : L.IsWellFormed :=
    ⟨hZ, hLI, isSNCDivisor_of_boundaryAdapted hW,
      highest_stratum_isTransverse (X := CMfd.of (n := n) W) hW hBound⟩
  have hA := (contactRemainder_boundary_domain (X := CMfd.of (n := n) W) L hLW
    (coefficient_positive (B := CMfd.of (n := n) W) MW)).1
  have hDomain : IsInvDomain n (causalBirthRemainder M H T y) := by
    change IsInvDomain n (contactRemainderMarked (withN (coeffMarked MW) (causalBirthStratum H T y)) 0)
    rw [hStratum]
    exact hA
  exact ⟨hDomain, rfl, hMWN, hMWI, hMWd⟩

/-- The original nonzero hypothesis is transported through the actual head
and open internally. At q=0 the causal datum is literally coeff(M_birth),
so the single causal value uses the SAME coefficient numerical branch. -/
theorem causalBirthRemainder_eq_coeff_of_zero (M : MarkedIdeal n X) (hN : M.N = univ)
    (hI : M.ideal.IsCoherent) (hd : 1 ≤ M.d)
    (hne : ∀ x, IsNonzeroAlongAt univ M.ideal x)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y) (hq : oldCount H T y = 0) :
    causalBirthRemainder M H T y = coeffMarked (causalBirthParent M H T y) := by
  let k := T.length - birthYear H T y
  let K := head T k
  let W := causalBirthOpen H T y
  let MW := causalBirthParent M H T y
  obtain ⟨_hA, _hE, hMWN, hMWI, hMWd⟩ := causalBirthRemainder_domain M hN hI hd h T hT hHistory y
  have hDom := ambient_domain M hN hI hd hne (isSNCDivisor_of_boundaryAdapted h)
  have hKTest := ((isGeoTestTower_iff_head_tail M T k).mp hT).1
  have hDomK := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom K hKTest
  have hKN : (geoTransformAlong M K).N = univ :=
    (DerivativeIdealTower.inclusions_tower M hN hI (j := 0) (Nat.zero_le _) K hKTest).2.1
  have hMWNe : ∀ z : W, IsNonzeroAlongAt univ MW.ideal z := by
    intro z
    have hzN : z.val ∈ (geoTransformAlong M K).N := by rw [hKN]; exact mem_univ z.val
    have hnz := hDomK.isNonzeroAlongAt z.val hzN
    have hp := (isNonzeroAlongAt_pullback_val_iff hDomK.isWellFormed.isCoherent W z).mpr hnz
    change IsNonzeroAlongAt univ
      (GermIdeal.pullback (Subtype.val : W → (split T k).1) (geoTransformAlong M K).ideal) z
    simpa only [hKN, preimage_univ] using hp
  have hZ : causalBirthStratum H T y = univ := by
    ext z
    change (oldCount H T y ≤ oldCount H K z.val) ↔ z ∈ (univ : Set W)
    rw [hq]
    simp only [Nat.zero_le, mem_univ]
  have hL : withN (coeffMarked MW) (causalBirthStratum H T y) = coeffMarked MW := by
    rw [hZ]
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hMWN.symm rfl rfl rfl
  change contactRemainderMarked (withN (coeffMarked MW) (causalBirthStratum H T y)) 0 = coeffMarked MW
  rw [hL]
  exact (coefficient_selected_empty_remainder_eq (X := CMfd.of (n := n) W) MW hMWN hMWI hMWd hMWNe).2

end
end Hironaka.HironakaOriginalNCCausalHistoryValue
