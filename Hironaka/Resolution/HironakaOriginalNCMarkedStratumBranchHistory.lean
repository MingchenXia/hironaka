import Hironaka.Resolution.HironakaOriginalNCMarkedStratum
import Hironaka.Resolution.HironakaOriginalNCOldStratumStrictEquality
import Hironaka.Resolution.HironakaOriginalOldBranchHighestPhase
import Hironaka.Resolution.HironakaOriginalOldBranchAppend
import Hironaka.Resolution.HironakaOriginalOldBranchOpenTransport
import Hironaka.Resolution.HironakaOriginalNCCausalAppendFrame

/-!
# Native branch-history adapters for the NEW marked-stratum joint interpreter

These are internal geometry/field adapters, with zero separate mathematical
credit. Actual native tests supply the actual N/I/d and cosupport; the actual
geometry-only donor supplies NC for the SAME entire ordered boundary. No
native augmented carrier transversality or global old branch list is assumed.
The later unconditional NEW-Psi interpreter must produce every test/history
used by these generic lower interfaces. No old coefficient-Phi theorem is
claimed for the new numerical value.

Math first: joint-frame-design.md and the literal-restriction addendum in
work/hironaka-g9-proper-carrier-marked-stratum-implementation-20261023/;
independent native API review c6767a77 / 997590a1. Source-only; no Lean claim.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumBranchHistory

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MarkedIdealEquivalence.MarkedIdeal
  NormalCrossings HomogenizedGlueingTower MemberInterTowerAlong BoundaryCount
  CoefficientIdealRestriction DropMembers GermIdealOrder GermIdealPullbackCalculus
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsSNCBlockCarrier HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratum
  HironakaOriginalNCCountHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem augmented_test_of_actual_native_and_donor
    (M D : MarkedIdeal n X) (E : List (Set X)) (hE : E = D.E) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      IsGeoTestTower M T → IsGeoTestTower D T →
      IsGeoTestTower ({ M with E := E } : MarkedIdeal n X) T
  | _, .refl, _hM, _hD => trivial
  | _, .step T C π hπ, hM, hD => by
      have ih := augmented_test_of_actual_native_and_donor M D E hE T hM.1 hD.1
      have hc := cosupp_geoTransformAlong_withE M E T
      have he : (geoTransformAlong ({ M with E := E } : MarkedIdeal n X) T).E =
          (geoTransformAlong D T).E := E_geoTransformAlong_eq hE T
      refine ⟨ih, hM.2.1, ?_, ?_⟩
      · rw [hc]
        exact hM.2.2.1
      · rw [he]
        exact hD.2.2.2

/-- Only boundary NC is borrowed; native ideals and carriers are never equated to the donor. -/
theorem original_history_of_same_boundary (M D : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hE : D.E = M.E) (H : Set X)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower D H T) :
    IsOriginalBranchTestTower M H T := by
  intro U B hSNC hUnion
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let DU := MarkedIdeal.pullback (Subtype.val : U → X) D
  let DA : MarkedIdeal n U := { DU with E := B ++ DU.E }
  have hTNative : IsGeoTestTower MU (restrict U T) :=
    isGeoTestTower_restrict U hM.isClosedSubmanifold_N hM.isCoherent T hT
  have hEU : DU.E = MU.E := by
    change D.E.map ((Subtype.val : U → X) ⁻¹' ·) =
      M.E.map ((Subtype.val : U → X) ⁻¹' ·)
    rw [hE]
  have hSNCD : IsSNCDivisor n (B ++ DU.E) := by rw [hEU]; exact hSNC
  have hTD : IsGeoTestTower DA (restrict U T) := hHistory U B hSNCD hUnion
  exact augmented_test_of_actual_native_and_donor MU DA (B ++ MU.E)
    (by change B ++ MU.E = B ++ DU.E; rw [hEU]) (restrict U T) hTNative hTD

/- The already accepted highest-stratum proof needs no positivity of r. Its
only lower mother accepts ALL Nat r, including the genuine zero-count case. -/
private theorem ambient_history_of_highest_centres
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) (r : ℕ)
    (hbound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn
      {x : X | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} T) :
    IsOriginalBranchTestTower (⟨univ, E, I, d⟩ : MarkedIdeal n X) H T := by
  classical
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x : X | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  intro W B hSNC hUnion
  let MU := MarkedIdeal.pullback (Subtype.val : W → X) M
  let EU := MU.E
  let SW := (Subtype.val : W → X) ⁻¹' Z
  let hBU := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_union_of_snc_append B EU hSNC)
  have hHW : IsNormalCrossingsCarrier (n := n) ((Subtype.val : W → X) ⁻¹' H) :=
    hUnion.symm ▸ hBU
  have hCount (x : W) : boundaryCount B x = branchMultiplicity hH x.val := by
    have hRaw := (branchMultiplicity_union_eq_count B EU hSNC x).1
    change branchMultiplicity hBU x = boundaryCount B x at hRaw
    calc
      boundaryCount B x = branchMultiplicity hBU x := hRaw.symm
      _ = branchMultiplicity hHW x := by
        have hcongr {J K : Set W}
            (hJ : IsNormalCrossingsCarrier (n := n) J)
            (hK : IsNormalCrossingsCarrier (n := n) K) (hJK : J = K) :
            branchMultiplicity hJ x = branchMultiplicity hK x := by
          subst K
          rfl
        exact (hcongr hHW hBU hUnion).symm
      _ = branchMultiplicity hH x.val := branchMultiplicity_open W hH hHW x
  have hBoundB : ∀ x : W, boundaryCount B x ≤ r := by
    intro x
    rw [hCount]
    exact hbound x.val
  have hClosedSW : IsClosed SW :=
    (isClosed_branchMultiplicity_superlevel hH r).preimage continuous_subtype_val
  have hScount : ∀ x ∈ SW, r ≤ boundaryCount B x := by
    intro x hx
    rw [hCount]
    exact hx
  have hWF : ({ MU with E := B ++ MU.E } : MarkedIdeal n W).IsWellFormed := by
    refine ⟨?_, GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,
      hSNC, ?_⟩
    · change IsClosedSubmanifold n ((Subtype.val : W → X) ⁻¹' (univ : Set X))
      rw [preimage_univ]
      exact isClosedSubmanifold_univ
    · change IsTransverse n ((Subtype.val : W → X) ⁻¹' (univ : Set X)) (B ++ MU.E)
      rw [preimage_univ]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  have hTW : IsGeoTestTower MU (restrict W T) :=
    isGeoTestTower_restrict (𝔪 := M) W isClosedSubmanifold_univ hI T hT
  have hTZW : CentresIn SW (restrict W T) := centresIn_restrict_original W T hTZ
  exact isGeoTestTower_add_snc_branches_of_centresIn_maxcount
    (X := CMfd.of (n := n) W) MU B hWF r hBoundB
    hClosedSW hScount (restrict W T) hTW hTZW


/-- Genuine highest-stratum centre containment supplies ALL original local native branch tests. -/
theorem original_history_of_highest_centres (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) {H : Set X}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (q : ℕ)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ q)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHigh : CentresIn
      {x : X | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} T) :
    IsOriginalBranchTestTower M H T := by
  let D := boundaryGeometry (X := X) M.E
  have hDTest : IsGeoTestTower D T := boundaryGeometry_test M hM.isSNCDivisor T hT
  have hDHistory : IsOriginalBranchTestTower D H T :=
    ambient_history_of_highest_centres (IdealWeightPowers.unitIdeal n X) IdealWeightPowers.isCoherent_unitIdeal 0
      h q hBound T hDTest hHigh
  exact original_history_of_same_boundary M D hM rfl H T hT hDHistory

/-- The native append consumes only actual ordinary and ALL-local-branch histories.
No transversality of native N to the added old branch block is required. -/
theorem original_history_append_native (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hP : IsGeoTestTower M P) (hHistoryP : IsOriginalBranchTestTower M H P)
    (hHistoryQ : IsOriginalBranchTestTower (geoTransformAlong M P) (strictAlong P H) Q) :
    IsOriginalBranchTestTower M H (P.append Q) := by
  intro W B hSNC hUnion
  let MU := MarkedIdeal.pullback (Subtype.val : W → X) M
  let A : MarkedIdeal n W := { MU with E := B ++ MU.E }
  let PW := restrict W P
  let U := openPreimage P W
  let BP := B.map (strictAlong PW)
  let MP := MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong M P)
  let D := boundaryGeometry (X := X) M.E
  let DU := MarkedIdeal.pullback (Subtype.val : W → X) D
  let DA : MarkedIdeal n W := { DU with E := B ++ DU.E }
  have hAP : IsGeoTestTower A PW := hHistoryP W B hSNC hUnion
  have hDHistory := boundaryGeometry_original_history M H P hHistoryP
  have hDAP : IsGeoTestTower DA PW := hDHistory W B hSNC hUnion
  have hDAN : DA.N = univ := preimage_univ
  have hDAI : DA.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val IdealWeightPowers.isCoherent_unitIdeal
  have hDAWF : DA.IsWellFormed := by
    refine ⟨?_, hDAI, hSNC, ?_⟩
    · rw [hDAN]
      exact isClosedSubmanifold_univ
    · rw [hDAN]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  have hCurrent : geoTransformAlong A PW = ({ MP with E := BP ++ MP.E } : MarkedIdeal n U) :=
    original_branch_terminal_datum M hM.isClosedSubmanifold_N hM.isCoherent P hP W B
  have hDummyCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hDAWF PW hDAP
  have hCurrentE : (geoTransformAlong A PW).E = (geoTransformAlong DA PW).E :=
    E_geoTransformAlong_eq (𝔪 := A) (𝔫 := DA) rfl PW
  have hSNCP : IsSNCDivisor n (BP ++ MP.E) := by
    have hNativeSNC : IsSNCDivisor n (geoTransformAlong A PW).E :=
      hCurrentE.symm ▸ hDummyCurrent.isSNCDivisor
    simpa only [hCurrent] using hNativeSNC
  have hUnionP : (Subtype.val : U → Y) ⁻¹' strictAlong P H = ⋃ C ∈ BP, C := by
    rw [← strictAlong_restrict W P H, hUnion]
    exact strictAlong_original_branch_union PW B
  have hTail := hHistoryQ U BP hSNCP hUnionP
  rw [← hCurrent] at hTail
  have hConcat : IsGeoTestTower A (PW.append (restrict U Q)) :=
    (isGeoTestTower_append_iff A PW (restrict U Q)).mpr ⟨hAP, hTail⟩
  have hNA : IsClosedSubmanifold n A.N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hM.isClosedSubmanifold_N W
  have hIA : A.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hM.isCoherent
  have hIso := BlowupTowerIsoTail.isTowerIso_restrict_append W P Q
  have hLeft := (BlowupTowerIsomorphism.IsTowerIso.isGeoTestTower_iff
    (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) W) (𝔪 := A)
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞)
    hNA hIA hIso).mpr hConcat
  change IsGeoTestTower (MarkedIdeal.pullback (id : W → W) A) (restrict W (P.append Q)) at hLeft
  have hId : MarkedIdeal.pullback (id : W → W) A = A :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
      (show A.E.map (fun C => (id : W → W) ⁻¹' C) = A.E by simp)
      (BlowupControlledTransform.pullback_id hIA) rfl
  rw [hId] at hLeft
  exact hLeft

private theorem countAt_zero (H : Set X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (y : Y) →
      countAt H T y 0 = oldCount H (.refl : BlowupTower X X) (T.proj y)
  | _, .refl, _y => rfl
  | _, .step T C π hπ, y => by
      simpa only [countAt, if_pos (Nat.zero_le T.length), BlowupTower.proj_step, Function.comp_apply]
        using countAt_zero H T (π y)

/-- The NEW auxiliary's actual native test gives ordinary tests, universal
old-branch tests and the whole two-sided current highest-cosupport identity. -/
theorem markedStratum_test_history (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hd : 1 ≤ M.d) {H : Set X}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (q : ℕ)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ q)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (markedStratum M
      {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) T) :
    IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
      (geoTransformAlong (markedStratum M
        {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) T).cosupp =
        {y | y ∈ (geoTransformAlong M T).cosupp ∧ oldCount H T y = q} := by
  let Zq := {x | q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  have hZ : IsClosedSubmanifold n Zq :=
    isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  obtain ⟨hMT, hHigh⟩ := (markedStratum_test_tower_iff M hM hd hZ T).mp hT
  have hHistory := original_history_of_highest_centres M hM h q hBound T hMT hHigh
  obtain ⟨hcT, hStrata⟩ := current_old_strata_eq_strict M h T hMT hHistory
  have hSource : Zq = {x | q ≤ oldCount H (.refl : BlowupTower X X) x} := by
    ext x
    change (q ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x) ↔
      q ≤ oldCount H (.refl : BlowupTower X X) x
    rw [oldCount_eq (.refl : BlowupTower X X) (isNormalCrossingsCarrier_of_boundaryAdapted h)]
    rfl
  have hWhole : strictAlong T Zq = {y | q ≤ oldCount H T y} := by
    rw [hSource]
    exact hStrata q
  have hDTest := boundaryGeometry_test M hM.isSNCDivisor T hMT
  have hDHist := boundaryGeometry_original_history M H T hHistory
  have hCountBound (y : Y) : oldCount H T y ≤ q := by
    have hAnti := countAt_antitone (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal
      h T hDTest hDHist y
    have hLe := hAnti (Nat.zero_le T.length)
    rw [countAt_length, countAt_zero] at hLe
    exact hLe.trans ((oldCount_eq (.refl : BlowupTower X X)
      (isNormalCrossingsCarrier_of_boundaryAdapted h) (T.proj y)).trans_le (hBound (T.proj y)))
  refine ⟨hMT, hHistory, ?_⟩
  rw [markedStratum_tower_cosupp M hM hd hZ T hT, hWhole]
  ext y
  exact ⟨fun hy => ⟨hy.1, le_antisymm (hCountBound y) hy.2⟩,
    fun hy => ⟨hy.1, hy.2.ge⟩⟩

/-- Intrinsic antitonicity is borrowed only from pure ambient geometry;
the actual native appended tests and branch histories are produced here. -/
theorem oldCount_append_le_native (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (P : BlowupTower X Y) (hP : IsGeoTestTower M P)
    (hHistoryP : IsOriginalBranchTestTower M H P)
    (Q : BlowupTower Y Z) (hQ : IsGeoTestTower (geoTransformAlong M P) Q)
    (hHistoryQ : IsOriginalBranchTestTower (geoTransformAlong M P) (strictAlong P H) Q)
    (z : Z) : oldCount H (P.append Q) z ≤ oldCount H P (Q.proj z) := by
  have hAll := (isGeoTestTower_append_iff M P Q).mpr ⟨hP, hQ⟩
  have hAllHistory := original_history_append_native M hM P Q hP hHistoryP hHistoryQ
  have hD := boundaryGeometry_test M hM.isSNCDivisor (P.append Q) hAll
  have hDH := boundaryGeometry_original_history M H (P.append Q) hAllHistory
  have hAnti := countAt_antitone (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal
    h (P.append Q) hD hDH z
  have hLen : P.length ≤ (P.append Q).length := by rw [BlowupTower.length_append]; omega
  calc
    oldCount H (P.append Q) z = countAt H (P.append Q) z (P.append Q).length :=
      (countAt_length H (P.append Q) z).symm
    _ ≤ countAt H (P.append Q) z P.length := hAnti hLen
    _ = countAt H P (Q.proj z) P.length :=
      HironakaOriginalNCCausalAppendFrame.countAt_append_initial_year H P Q z _ le_rfl
    _ = oldCount H P (Q.proj z) := countAt_length H P (Q.proj z)

/-- The native history has the genuine ambient intrinsic antitone chronology,
without replacing any ideal in a lower invariant. -/
theorem countAt_antitone_native (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y) : Antitone (countAt H T y) :=
  countAt_antitone (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h T
    (boundaryGeometry_test M hM.isSNCDivisor T hT)
    (boundaryGeometry_original_history M H T hHistory) y

/-- Only actual same-boundary test/history data enter the intrinsic step inequality. -/
theorem oldCount_step_le_native (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower M (.step T C π hπ))
    (hHistory : IsOriginalBranchTestTower M H (.step T C π hπ)) (z : Z) :
    oldCount H (.step T C π hπ) z ≤ oldCount H T (π z) :=
  oldCount_step_le (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h T C π hπ
    (boundaryGeometry_test M hM.isSNCDivisor (.step T C π hπ) hT)
    (boundaryGeometry_original_history M H (.step T C π hπ) hHistory) z

/-- This entire-set identity reads H and the actual tower only. -/
theorem oldCount_append_data (H : Set X) (P : BlowupTower X Y)
    (Q : BlowupTower Y Z) (z : Z) :
    oldCount H (P.append Q) z = oldCount (strictAlong P H) Q z := by
  unfold oldCount
  rw [MemberInterLocusAlong.strictAlong_append]

/-- Same actual open restriction, with intrinsic geometry obtained from the
native history rather than a caller NC/count certificate. -/
theorem oldCount_restrict_native (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (U : Opens X) (p : openPreimage T U) :
    oldCount ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p = oldCount H T p.val :=
  oldCount_restrict (boundaryGeometry (X := X) M.E) rfl IdealWeightPowers.isCoherent_unitIdeal h T
    (boundaryGeometry_test M hM.isSNCDivisor T hT)
    (boundaryGeometry_original_history M H T hHistory) U p

end
end Hironaka.HironakaOriginalNCMarkedStratumBranchHistory
