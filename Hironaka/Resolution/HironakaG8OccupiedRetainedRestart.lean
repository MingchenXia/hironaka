import Hironaka.Resolution.HironakaG8OccupiedPrincipalResidual

/-! Retained-order comparison across a genuine occupied hypersurface cut,
with every original ordered boundary member carried into the lower epoch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedRetainedRestart
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec GermIdealOrder
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderCanonical
  GeneralValue CanonicalCentres ResolutionDriver StepOneRegime StepOneEmptyPrefix HomogenizedIdealAlong
  HironakaG8OccupiedOrderReset HironakaG8OccupiedPrincipalResidual
  HironakaG8PrincipalRetainedEpochFinite HironakaG8CommonTowerNonmonomialOrders
  HironakaSharpActualChronologicalResidualDictionary HironakaCoherentTransformExtension

variable {n : ℕ} {X D Y : CMfd.{0} (n+1)}

private abbrev whole (W : Set X) (E : List (Set X)) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,d⟩

private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

private theorem order_le_source (F : MarkedIdeal (n+1) D) (hF : IsInvDomain (n+1) F)
    (S : BlowupTower D Y) (hS : IsGeoTestTower F S)
    (hCan : IsCanonical F ((canonicalInvariant (n+1)).inv F) S)
    (y : Y) (hy : y ∈ (geoTransformAlong F S).cosupp) :
    nmOrd (geoTransformAlong F S) y ≤ nmOrd F (S.proj y) := by
  have h := nmOrd_le_nmOrd_proj (Nat.succ_pos n) hF (ordMonotone_genInv evaluator F) .refl S
  simp only [BlowupTower.refl_append,geoTransformAlong_refl] at h
  exact (h hS hCan y hy).2

private theorem order_cap_of_no_factor (F : MarkedIdeal (n+1) D)
    (hF : IsInvDomain (n+1) F) (hNo : HasNoBoundaryFactor F)
    (hCap : IsMaximalOrderAlong F.N F.ideal F.d) :
    ∀ y : D, nmOrd F y ≤ F.d := by
  intro y
  apply nmOrd_le_of_notMem
  rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor F hF.isWellFormed hNo]
  exact hCap y

/-- A lower native epoch may start with genuinely inherited boundary
members. When its fresh strict ideal initially has no boundary factor,
canonicality and the initial cap preserve that exclusion at every stage. -/
theorem no_boundary_factor_along_lower_native_epoch
    (F : MarkedIdeal (n+1) D) (hF : IsInvDomain (n+1) F)
    (hNo : HasNoBoundaryFactor F) (hCap : IsMaximalOrderAlong F.N F.ideal F.d)
    (S : BlowupTower D Y) (hCan : IsCanonical F ((canonicalInvariant (n+1)).inv F) S) :
    HasNoBoundaryFactor (geoTransformAlong F S) := by
  have hS := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hF S hCan
  have hf := order_cap_of_no_factor F hF hNo hCap
  induction S with
  | refl => exact hNo
  | step S C π hπ ih =>
    let B := geoTransformAlong F S
    have hBD : IsInvDomain (n+1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hF S hS.1
    have hnB : HasNoBoundaryFactor B := ih hCan.1 hS.1
    have hCd : IsMaximalOrderAlong B.N B.ideal B.d := by
      intro y hy
      have hyB : y ∈ B.cosupp := cosupport_anti (Nat.le_succ B.d) hy
      have hyG : y ∈ ordGe B (B.d+1) := by
        rwa [ordGe_eq_cosupport_of_hasNoBoundaryFactor B hBD.isWellFormed hnB]
      have hHigh := (mem_ordGe_iff hBD.isWellFormed hBD.isNonzeroAlongAt
        (B.cosupp_subset_N hyB) _).mp hyG
      have hLe := (order_le_source F hF S hS.1 hCan.1 y hyB).trans (hf (S.proj y))
      have hMark : B.d = F.d := d_geoTransformAlong F S
      exact (Nat.not_succ_le_self B.d) (hHigh.trans (hMark.symm ▸ hLe))
    exact hasNoBoundaryFactor_step B hBD.isWellFormed hnB hπ hS.2 hCd

/-- On common actual canonical lower prefixes, the fresh active support is
exactly the previous whole record's top stratum. Both order runs cover
the entire lower suffix. -/
theorem occupied_lower_active_support_and_runs
    (A F : MarkedIdeal (n+1) D) (hA : IsInvDomain (n+1) A) (hF : IsInvDomain (n+1) F)
    (hMarkLe : A.d ≤ F.d) (hN : A.N = F.N) (hE : A.E = F.E) (hPart : nmPart A = nmPart F)
    (hNo : HasNoBoundaryFactor F) (hCap : IsMaximalOrderAlong F.N F.ideal F.d)
    (S : BlowupTower D Y)
    (hCanA : IsCanonical A ((canonicalInvariant (n+1)).inv A) S)
    (hCanF : IsCanonical F ((canonicalInvariant (n+1)).inv F) S) :
    let q := F.d
    let B := geoTransformAlong A S
    let G := geoTransformAlong F S
    (∀ y ∈ B.cosupp, nmOrd B y ≤ q) ∧
    (∀ y : Y, y ∈ G.cosupp ↔ y ∈ B.cosupp ∧ nmOrd B y = q) ∧
    (∀ y ∈ G.cosupp, nmOrd G y = q ∧
      regimeRun (OrdRegime A q) S y = S.length ∧ regimeRun (OrdRegime F q) S y = S.length) := by
  let q := F.d
  let B := geoTransformAlong A S
  let G := geoTransformAlong F S
  have hS := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hA S hCanA
  have hSF := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hF S hCanF
  have hBD : IsInvDomain (n+1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA S hS
  have hGD : IsInvDomain (n+1) G := InvDomainTowerAlong.isInvDomain_geoTransformAlong hF S hSF
  have hFbound : ∀ x : D, nmOrd F x ≤ q := order_cap_of_no_factor F hF hNo hCap
  have hAbound (x : D) : nmOrd A x ≤ q := by
    have he : nmOrd A x = nmOrd F x :=
      nmOrd_congr fun j => by
        change x ∈ cosupport (n+1) A.N (nmPart A) j ↔ x ∈ cosupport (n+1) F.N (nmPart F) j
        rw [hN,hPart]
    rw [he]
    exact hFbound x
  have hPart' : nmPart B = nmPart G :=
    common_test_tower_nonmonomial_part (Nat.succ_pos n) A F hA.isWellFormed hF.isWellFormed
      hA.isNonzeroAlongAt hF.isNonzeroAlongAt hN hE hPart S hS hSF
  have hN' : B.N = G.N := geoTransformAlong_N_eq_of_N_eq hN S
  have hOrder (y : Y) : nmOrd B y = nmOrd G y :=
    nmOrd_congr fun j => by
      change y ∈ cosupport (n+1) B.N (nmPart B) j ↔ y ∈ cosupport (n+1) G.N (nmPart G) j
      rw [hN',hPart']
  have hNoG : HasNoBoundaryFactor G := no_boundary_factor_along_lower_native_epoch F hF hNo hCap S hCanF
  have hGe : ordGe B q = G.cosupp := by
    have he : ordGe B q = ordGe G q := by
      change cosupport (n+1) B.N (nmPart B) q = cosupport (n+1) G.N (nmPart G) q
      rw [hN',hPart']
    rw [he,ordGe_eq_cosupport_of_hasNoBoundaryFactor G hGD.isWellFormed hNoG]
    unfold MarkedIdeal.cosupp
    rw [d_geoTransformAlong]
  have hBound (y : Y) (hy : y ∈ B.cosupp) : nmOrd B y ≤ q :=
    (order_le_source A hA S hS hCanA y hy).trans (hAbound (S.proj y))
  have hLevel (y : Y) : y ∈ G.cosupp ↔ y ∈ B.cosupp ∧ nmOrd B y = q := by
    rw [← hGe]
    constructor
    · intro hy
      have hMark : B.d = A.d := d_geoTransformAlong A S
      have hyB : y ∈ B.cosupp := by
        exact DerivativeIdealTower.cosupport_subset_of_le
          (NonmonomialTransformAlong.le_nonmonomialPartAlong_self hBD.isWellFormed.isCoherent)
          B.d (cosupport_anti (hMark.symm ▸ hMarkLe) hy)
      exact ⟨hyB,le_antisymm (hBound y hyB)
        ((mem_ordGe_iff hBD.isWellFormed hBD.isNonzeroAlongAt (B.cosupp_subset_N hyB) _).mp hy)⟩
    · rintro ⟨hyB,hyq⟩
      exact (mem_ordGe_iff hBD.isWellFormed hBD.isNonzeroAlongAt (B.cosupp_subset_N hyB) _).mpr
        (le_of_eq hyq.symm)
  refine ⟨hBound,hLevel,?_⟩
  intro y hy
  obtain ⟨hyB,hyq⟩ := (hLevel y).mp hy
  have hyG : nmOrd G y = q := (hOrder y).symm.trans hyq
  exact ⟨hyG,regimeRun_eq_length_of_initial_order_bound A hA q hAbound S hCanA hS y hyB hyq,
    regimeRun_eq_length_of_initial_order_bound F hF q hFbound S hCanF hSF y hy hyG⟩

private theorem maximum_eq_on_active_stratum {Λ : Type*} [LinearOrder Λ] {Z : Type*}
    (o : Z → ℕ) (v w : Z → Λ) (A B : Set Z) (q : ℕ)
    (hCap : ∀ z ∈ A, o z ≤ q) (hLevel : ∀ z, z ∈ B ↔ z ∈ A ∧ o z = q)
    (hValue : ∀ z ∈ B, v z = w z) (hHigher : ∀ {x y}, o x < o y → v x < v y)
    (hActive : B.Nonempty) : maxLocus v A = maxLocus w B := by
  obtain ⟨a,ha⟩ := hActive
  obtain ⟨haA,haq⟩ := (hLevel a).mp ha
  ext y
  constructor
  · intro hy
    have hyq : o y = q := le_antisymm (hCap y hy.1) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a haA)) (hHigher (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    have hyB := (hLevel y).mpr ⟨hy.1,hyq⟩
    refine ⟨hyB,fun z hz => ?_⟩
    rw [← hValue z hz,← hValue y hyB]
    exact hy.2 z ((hLevel z).mp hz).1
  · intro hy
    obtain ⟨hyA,hyq⟩ := (hLevel y).mp hy.1
    refine ⟨hyA,fun z hz => ?_⟩
    by_cases hzB : z ∈ B
    · rw [hValue z hzB,hValue y hy.1]
      exact hy.2 z hzB
    · have hzq : o z ≠ q := fun he => hzB ((hLevel z).mpr ⟨hz,he⟩)
      exact le_of_lt (hHigher (by rw [hyq]; exact lt_of_le_of_ne (hCap z hz) hzq))

/-- When the lower top stratum at the occupied cut lies above the old
centre, canonical lower prefixes have the same native, rebased whole,
and chronological whole maximum. The runs and value comparisons are
derived, using only the cut geometry and genuine canonical histories. -/
theorem occupied_principal_maxima_at_common_prefix
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : D → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q) (hqμ : q < μ)
    (S : BlowupTower D Y) :
    let M := whole W E 1
    let H : BlowupTower X D := .step .refl C π hπ
    let A := geoTransformAlong M H
    let F := whole (strictTransform (n+1) π W) A.E q
    let R := canonicalInvariant.{0} (n+1)
    (∀ y ∈ A.cosupp, nmOrd A y = q → π y ∈ C) →
    IsMaximalOrderAlong F.N F.ideal q →
    IsCanonical A (R.inv A) S →
    IsCanonical F (R.inv F) S →
    (geoTransformAlong F S).cosupp.Nonempty →
    maxLocus (R.inv M (H.append S)) (geoTransformAlong M (H.append S)).cosupp =
      maxLocus (R.inv F S) (geoTransformAlong F S).cosupp ∧
    maxLocus (R.inv A S) (geoTransformAlong A S).cosupp =
      maxLocus (R.inv F S) (geoTransformAlong F S).cosupp := by
  dsimp only
  intro hOver hCap hCanA hCanF hActive
  let M := whole W E 1
  let H : BlowupTower X D := .step .refl C π hπ
  let A := geoTransformAlong M H
  let F := whole (strictTransform (n+1) π W) A.E q
  let B := geoTransformAlong A S
  let G := geoTransformAlong F S
  let R := canonicalInvariant.{0} (n+1)
  have hLow : M.IsAdmissibleCentre C := ⟨hHigh.1,
    hHigh.2.1.trans (cosupport_anti (show 1 ≤ μ by omega)),hHigh.2.2⟩
  have hA : IsInvDomain (n+1) A :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom H ⟨trivial,hLow⟩
  obtain ⟨hF,hNo,_hMask,_hComp⟩ := occupied_hypersurface_companion_eq_fresh_companion
    W hW hI hPure E μ hμ hDom hOld hBound C π hπ hHigh q hq
  obtain ⟨_hI,_hNo,hN,_hE,hRes⟩ := occupied_hypersurface_residual_eq_fresh_ideal
    W hW hI hPure E μ hμ hDom hOld hBound C π hπ hHigh
  have hPartF := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hF.isWellFormed.1
    hF.isWellFormed.3 hF.isWellFormed.4 hF.isWellFormed.2 hNo
  change nmPart F = RestrictedIdealExtension.restrictOn (n+1) univ F.ideal at hPartF
  rw [BlowupTowerTransforms.restrictOn_univ hF.isWellFormed.isCoherent] at hPartF
  have hPart : nmPart A = nmPart F := hRes.trans hPartF.symm
  have hActiveData := occupied_lower_active_support_and_runs A F hA hF hq hN rfl hPart hNo hCap S hCanA hCanF
  dsimp only at hActiveData
  obtain ⟨hOrdBound,hLevel,hRuns⟩ := hActiveData
  have hTrans : geoTransformAlong M (H.append S) = B := geoTransformAlong_append M H S
  have hRead (y : Y) (hy : y ∈ G.cosupp) :
      R.inv M (H.append S) y = R.inv F S y ∧ R.inv A S y = R.inv F S y := by
    obtain ⟨hyB,hyq⟩ := (hLevel y).mp hy
    obtain ⟨hyG,hRA,hRF⟩ := hRuns y hy
    have hInitial := regime_base_of_regimeRun_eq (OrdRegime A q) S y ⟨hyB,hyq⟩ hRA
    have hCentre : π (S.proj y) ∈ C := hOver (S.proj y) hInitial.1 hInitial.2
    have hGe : π (S.proj y) ∈ ordGe M μ := by
      rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor M hDom.isWellFormed hOld]
      exact hHigh.2.1 hCentre
    have hDrop : q < nmOrd M (π (S.proj y)) :=
      hqμ.trans_le ((mem_ordGe_iff hDom.isWellFormed hDom.isNonzeroAlongAt (mem_univ _) _).mp hGe)
    have hChron : nmOrd (geoTransformAlong M (H.append S)) y = q := by
      rw [hTrans]; exact hyq
    have hVal := occupied_hypersurface_restart_value_eq_fresh W hW hI hPure E μ hμ hDom hOld hBound
      C π hπ hHigh q hq S y hChron hyG hDrop hRA hRF
    have hRebase := canonical_value_after_occupied_order_drop M .refl C π hπ S y q hChron hDrop
    exact ⟨hVal,hRebase.symm.trans hVal⟩
  have hChronL {x y : Y} (h : nmOrd B x < nmOrd B y) :
      R.inv M (H.append S) x < R.inv M (H.append S) y := by
    change genInv evaluator M (H.append S) x < genInv evaluator M (H.append S) y
    apply genInv_lt_of_nmOrd_lt evaluator M
    rw [hTrans]
    exact h
  have hRebaseL {x y : Y} (h : nmOrd B x < nmOrd B y) : R.inv A S x < R.inv A S y :=
    genInv_lt_of_nmOrd_lt evaluator A h
  change maxLocus (R.inv M (H.append S)) (geoTransformAlong M (H.append S)).cosupp =
      maxLocus (R.inv F S) G.cosupp ∧
    maxLocus (R.inv A S) B.cosupp = maxLocus (R.inv F S) G.cosupp
  rw [hTrans]
  exact ⟨maximum_eq_on_active_stratum (nmOrd B) _ _ B.cosupp G.cosupp q hOrdBound hLevel
    (fun y hy => (hRead y hy).1) hChronL hActive,
    maximum_eq_on_active_stratum (nmOrd B) _ _ B.cosupp G.cosupp q hOrdBound hLevel
    (fun y hy => (hRead y hy).2) hRebaseL hActive⟩

/-- Every actual lower native canonical tower in the retained epoch is
canonical for the whole original record with its occupied first step
attached, provided the lower top stratum starts over that centre. -/
theorem occupied_principal_restart_finite_canonical
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : D → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q) (hqμ : q < μ)
    (S : BlowupTower D Y) :
    let M := whole W E 1
    let H : BlowupTower X D := .step .refl C π hπ
    let A := geoTransformAlong M H
    let F := whole (strictTransform (n+1) π W) A.E q
    let R := canonicalInvariant.{0} (n+1)
    (∀ y ∈ A.cosupp, nmOrd A y = q → π y ∈ C) →
    IsMaximalOrderAlong F.N F.ideal q →
    IsCanonical M (R.inv M) H →
    IsCanonical F (R.inv F) S →
    IsCanonical M (R.inv M) (H.append S) ∧ IsCanonical A (R.inv A) S := by
  dsimp only
  intro hOver hCap hCanH hCanF
  let M := whole W E 1
  let H : BlowupTower X D := .step .refl C π hπ
  let A := geoTransformAlong M H
  let F := whole (strictTransform (n+1) π W) A.E q
  let R := canonicalInvariant.{0} (n+1)
  change IsCanonical F (R.inv F) S at hCanF
  change IsCanonical M (R.inv M) (H.append S) ∧ IsCanonical A (R.inv A) S
  induction S with
  | refl => exact ⟨hCanH,trivial⟩
  | step S K σ hσ ih =>
    obtain ⟨hChron,hLocal⟩ := ih hCanF.1
    rcases hCanF.2 with he | hc
    · exact ⟨⟨hChron,Or.inl he⟩,⟨hLocal,Or.inl he⟩⟩
    · by_cases hne : K.Nonempty
      · obtain ⟨a,ha⟩ := hne
        have hAct : (geoTransformAlong F S).cosupp.Nonempty := by
          rw [hc] at ha
          exact ⟨a,ha.1⟩
        have hMax := occupied_principal_maxima_at_common_prefix W hW hI hPure E μ hμ hDom hOld hBound
          C π hπ hHigh q hq hqμ S hOver hCap hLocal hCanF.1 hAct
        exact ⟨⟨hChron,Or.inr (hc.trans hMax.1.symm)⟩,⟨hLocal,Or.inr (hc.trans hMax.2.symm)⟩⟩
      · have he := Set.not_nonempty_iff_eq_empty.mp hne
        exact ⟨⟨hChron,Or.inl he⟩,⟨hLocal,Or.inl he⟩⟩

end
end Hironaka.HironakaG8OccupiedRetainedRestart
