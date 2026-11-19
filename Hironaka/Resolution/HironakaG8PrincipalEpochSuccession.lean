import Hironaka.Resolution.HironakaG8OccupiedAtlasRestart
import Hironaka.Resolution.HironakaG8SharedResidualInitialFactorFree
import Hironaka.Resolution.HironakaActualPureStrictTransforms

/-! Repeat a principal lower epoch on the actual strict carrier, with
the full original physical prefix and its inherited boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalEpochSuccession
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec GermIdealOrder
  AnalyticDimensionBasics HironakaActualHSSingularBlowupRestart
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderCanonical
  GeneralValue GeneralCompanionPhase CanonicalCentres ResolutionDriver StepOneRegime HomogenizedIdealAlong
  HironakaG8OccupiedMixedRestart HironakaG8OccupiedRetainedRestart HironakaG8OccupiedAtlasRestart
  HironakaG8PrincipalRetainedEpochFinite HironakaG8CommonTowerNonmonomialOrders
  HironakaG8SharedResidualInitialFactorFree HironakaSharpActualChronologicalResidualDictionary
  HironakaStageCenters HironakaG8NativePhaseCertificate

variable {n : ℕ} {X D Y : CMfd.{0} (n+1)}

private abbrev whole (W : Set X) (E : List (Set X)) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,d⟩
private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

private theorem maximum_eq_of_equal_top_field {Λ : Type} [LinearOrder Λ] {Z : Type}
    (o : Z → ℕ) (v w : Z → Λ) (A : Set Z) (q : ℕ)
    (hCap : ∀ z ∈ A, o z ≤ q) (hTop : ∃ z ∈ A, o z = q)
    (hValue : ∀ z ∈ A, o z = q → v z = w z)
    (hv : ∀ {x y}, o x < o y → v x < v y) (hw : ∀ {x y}, o x < o y → w x < w y) :
    maxLocus v A = maxLocus w A := by
  obtain ⟨a,ha,haq⟩ := hTop
  ext y
  constructor
  · intro hy
    have hyq : o y = q := le_antisymm (hCap y hy.1) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a ha)) (hv (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    refine ⟨hy.1,fun z hz => ?_⟩
    by_cases hzq : o z = q
    · rw [← hValue z hz hzq,← hValue y hy.1 hyq]
      exact hy.2 z hz
    · exact le_of_lt (hw (by rw [hyq]; exact lt_of_le_of_ne (hCap z hz) hzq))
  · intro hy
    have hyq : o y = q := le_antisymm (hCap y hy.1) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a ha)) (hw (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    refine ⟨hy.1,fun z hz => ?_⟩
    by_cases hzq : o z = q
    · rw [hValue z hz hzq,hValue y hy.1 hyq]
      exact hy.2 z hz
    · exact le_of_lt (hv (by rw [hyq]; exact lt_of_le_of_ne (hCap z hz) hzq))

private theorem centresOrdGt_of_le (M : MarkedIdeal (n+1) X) {q r : ℕ} (h : r ≤ q)
    (T : BlowupTower X Y) (hT : CentresOrdGt M q T) :
    CentresOrdGt M r T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    exact ⟨ih hT.1,hT.2.trans (ordGe_anti _ (Nat.succ_le_succ h))⟩

/-- One native retained epoch attaches to an arbitrary higher canonical
physical prefix. Shared nonmonomial residue controls all competitors,
and the new nonempty centres have exactly the new order. -/
theorem append_whole_canonical_of_principal_residual_epoch
    (M : MarkedIdeal (n+1) X) (hM : IsInvDomain (n+1) M)
    (P : BlowupTower X D) (hCanP : IsCanonical M ((canonicalInvariant (n+1)).inv M) P)
    (F : MarkedIdeal (n+1) D) (hF : IsInvDomain (n+1) F) (hFN : F.N = univ)
    (hNo : HasNoBoundaryFactor F) (hCap : IsMaximalOrderAlong F.N F.ideal F.d)
    (hHigher : CentresOrdGt M F.d P)
    (S : BlowupTower D Y) (hCanF : IsCanonical F ((canonicalInvariant (n+1)).inv F) S) :
    let A := geoTransformAlong M P
    A.N = univ → A.E = F.E → A.d ≤ F.d → nmPart A = F.ideal →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (P.append S) ∧
      (∀ r < F.d, CentresOrdGt M r (P.append S)) ∧
      nmPart (geoTransformAlong M (P.append S)) = nmPart (geoTransformAlong F S) := by
  dsimp only
  intro hAN hE hd hResidual
  let A := geoTransformAlong M P
  let q := F.d
  let R := canonicalInvariant.{0} (n+1)
  have hTP := R.isInvValue.isGeoTestTower_of_isCanonical hM P hCanP
  have hA : IsInvDomain (n+1) A := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hTP
  have hPartF := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hF.isWellFormed.1
    hF.isWellFormed.3 hF.isWellFormed.4 hF.isWellFormed.2 hNo
  change nmPart F = RestrictedIdealExtension.restrictOn (n+1) F.N F.ideal at hPartF
  rw [hFN,BlowupTowerTransforms.restrictOn_univ hF.isWellFormed.isCoherent] at hPartF
  have hPart : nmPart A = nmPart F := hResidual.trans hPartF.symm
  have hNF : A.N = F.N := hAN.trans hFN.symm
  have hLe : A.ideal.Le F.ideal := hResidual ▸
    NonmonomialTransformAlong.le_nonmonomialPartAlong_self hA.isWellFormed.isCoherent
  have hCapF (x : D) : nmOrd F x ≤ q := by
    apply nmOrd_le_of_notMem
    rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor F hF.isWellFormed hNo]
    exact hCap x
  have hCapA (x : D) (_hx : x ∈ A.cosupp) : nmOrd A x ≤ q := by
    have he : nmOrd A x = nmOrd F x := nmOrd_congr fun j => by
      change x ∈ cosupport (n+1) A.N (nmPart A) j ↔ x ∈ cosupport (n+1) F.N (nmPart F) j
      rw [hNF,hPart]
    rw [he]
    exact hCapF x
  have hCanA : IsCanonical A (R.inv A) S :=
    shared_residual_phase_isCanonical_of_initial_factor_free A F hA hF hAN hFN hE hLe hd
      hPart hNo hCapF S hCanF
  have hTF := R.isInvValue.isGeoTestTower_of_isCanonical hF S hCanF
  have hTA := R.isInvValue.isGeoTestTower_of_isCanonical hA S hCanA
  have hNextPart := common_test_tower_nonmonomial_part (Nat.succ_pos n) A F
    hA.isWellFormed hF.isWellFormed hA.isNonzeroAlongAt hF.isNonzeroAlongAt hNF hE hPart S hTA hTF
  have hTerminal : nmPart (geoTransformAlong M (P.append S)) = nmPart (geoTransformAlong F S) := by
    rw [geoTransformAlong_append]
    exact hNextPart
  refine ⟨?_,?_,hTerminal⟩
  · clear hTerminal hNextPart hTF hTA
    induction S with
    | refl => exact hCanP
    | step S C π hπ ih =>
      have hBefore := ih hCanF.1 hCanA.1
      refine ⟨hBefore,?_⟩
      rcases hCanA.2 with he | hc
      · exact Or.inl he
      · by_cases hcne : C.Nonempty
        · obtain ⟨a,ha⟩ := hcne
          have hNative : C = maxLocus (R.inv F S) (geoTransformAlong F S).cosupp := by
            rcases hCanF.2 with he | hc
            · exact False.elim (Set.notMem_empty a (he ▸ ha))
            · exact hc
          have haF : a ∈ (geoTransformAlong F S).cosupp :=
            (hNative ▸ ha : a ∈ maxLocus (R.inv F S) (geoTransformAlong F S).cosupp).1
          let B := geoTransformAlong A S
          have hData := occupied_lower_active_support_and_runs A F hA hF hd hNF hE hPart hNo hCap S hCanA.1 hCanF.1
          dsimp only at hData
          obtain ⟨hCapB,hLevel,hReads⟩ := hData
          have hMax := maximum_eq_of_equal_top_field (nmOrd B) (R.inv M (P.append S)) (R.inv A S)
            B.cosupp q hCapB ⟨a,(hLevel a).mp haF⟩
            (fun y hy he => original_value_rebase_across_higher_centres M hM P S q hF.one_le_d
              hHigher hCapA hBefore hCanA.1 y hy he
              (hReads y ((hLevel y).mpr ⟨hy,he⟩)).2.1)
            (fun {x y} h => by
              change genInv evaluator M (P.append S) x < genInv evaluator M (P.append S) y
              apply genInv_lt_of_nmOrd_lt evaluator M
              rw [geoTransformAlong_append]
              exact h)
            (fun h => genInv_lt_of_nmOrd_lt evaluator A h)
          rw [geoTransformAlong_append]
          exact Or.inr (hc.trans hMax.symm)
        · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hcne)
  · intro r hr
    apply (centresOrdGt_append M r P S).mpr
    refine ⟨centresOrdGt_of_le M (Nat.le_of_lt hr) P hHigher,?_⟩
    clear hTerminal hNextPart hTA hTF
    induction S with
    | refl => trivial
    | step S C π hπ ih =>
      refine ⟨ih hCanF.1 hCanA.1,?_⟩
      intro y hy
      rcases hCanF.2 with he | hc
      · exact (Set.notMem_empty y (he ▸ hy)).elim
      · have hyF : y ∈ (geoTransformAlong F S).cosupp :=
          (hc ▸ hy : y ∈ maxLocus (R.inv F S) (geoTransformAlong F S).cosupp).1
        have hData := occupied_lower_active_support_and_runs A F hA hF hd hNF hE hPart hNo hCap S hCanA.1 hCanF.1
        dsimp only at hData
        apply mem_ordGe_of_succ_le
        rw [((hData.2.1 y).mp hyF).2]
        exact Nat.succ_le_of_lt hr

/-- A finite native hypersurface epoch at mark at least two retains the
whole reduced strict vanishing sheaf on its actual target. Its strict
carrier remains pure and the sheaf remains invertible. -/
theorem principal_epoch_strict_ideal
    (W : Set D) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hPure : IsPureDim (n := n+1) W n)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (E : List (Set D)) (q : ℕ) (hq : 2 ≤ q)
    (F : MarkedIdeal (n+1) D) (hFrec : F = whole W E q)
    (hF : IsInvDomain (n+1) F) (hNo : HasNoBoundaryFactor F)
    (hCap : IsMaximalOrderAlong F.N F.ideal q)
    (S : BlowupTower D Y) (hCan : IsCanonical F ((canonicalInvariant (n+1)).inv F) S) :
    let W' := strictTransform (n+1) S.proj W
    let B := geoTransformAlong F S
    B.ideal = vanishingIdeal (n := n+1) W' ∧
      (vanishingIdeal (n := n+1) W').IsInvertible ∧ IsPureDim (n := n+1) W' n := by
  let R := canonicalInvariant.{0} (n+1)
  have hFq : F.d = q := by rw [hFrec]
  have hFN : F.N = univ := by rw [hFrec]
  have hOriginalCap : ∀ x : D, nmOrd F x ≤ F.d := by
    intro x
    apply nmOrd_le_of_notMem
    rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor F hF.isWellFormed hNo,hFq]
    exact hCap x
  induction S with
  | refl =>
    have he : strictTransform (n+1) (id : D → D) W = W :=
      HironakaG11PresTowerState.strictTransform_id hW.isClosed
    simp only [BlowupTower.proj_refl,geoTransformAlong_refl,he]
    exact ⟨congrArg MarkedIdeal.ideal hFrec,hI,hPure⟩
  | @step A Y S C π hπ ih =>
    let U := strictTransform (n+1) S.proj W
    let B := geoTransformAlong F S
    obtain ⟨hId,hInv,hPureU⟩ := ih hCan.1
    change B.ideal = vanishingIdeal (n := n+1) U at hId
    have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hF _ hCan
    have hBD : IsInvDomain (n+1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hF S hTest.1
    have hN : B.N = univ :=
      (pullback_eq_mul_geoTransformAlong F hFN hF.isWellFormed.isCoherent S hTest.1).1
    have hMark : B.d = q := (d_geoTransformAlong F S).trans hFq
    have hBrec : B = whole U B.E q :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN rfl hId hMark
    have hA : IsComplexAnalyticSubset (n := n+1) U :=
      HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW S
    have hDense := HironakaActualHSSingularBlowupRestart.actualPure_subset_closure_regularLocus hA hPureU
    have hNoB := canonical_tower_hasNoBoundaryFactor F hF hNo hOriginalCap S hCan.1
    have hCapB := factor_free_canonical_prefix_cap F hF hOriginalCap S hCan.1 hNoB
    dsimp only at hCapB
    have hOrd (x : A) (_hx : x ∈ U) : order (n+1) univ (vanishingIdeal (n := n+1) U) x ≤ (q : ℕ∞) := by
      apply iSup₂_le
      intro k hk
      have hLe : k ≤ q := by
        by_contra hn
        have hk' : x ∈ cosupport (n+1) univ (vanishingIdeal (n := n+1) U) (q+1) :=
          cosupport_anti (by omega : q+1 ≤ k) ⟨mem_univ x,hk⟩
        apply hCapB x
        change x ∈ cosupport (n+1) B.N B.ideal (B.d+1)
        rwa [hN,hId,hMark]
      exact_mod_cast hLe
    have hCentre : (whole U B.E q).IsAdmissibleCentre C := hBrec ▸ hTest.2
    have hEq : strictTransform (n+1) (S.step C π hπ).proj W = strictTransform (n+1) π U := by
      rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp S.contMDiff_proj hπ.contMDiff]
    have hStrict :
        (B.geoTransform C π).ideal = vanishingIdeal (n := n+1) (strictTransform (n+1) π U) := by
      rw [geoTransform_ideal_eq_controlledTransform (𝔪 := B) hN hBD.isWellFormed.isCoherent hπ,hId,hMark]
      exact HironakaHypersurfaceStrictIdeal.controlledTransform_vanishingIdeal_eq_strictTransform
        hA hInv hDense hBD.isWellFormed.isSNCDivisor hq hOrd hCentre hπ
    have hInvNext : (vanishingIdeal (n := n+1) (strictTransform (n+1) π U)).IsInvertible := by
      rw [← hStrict,geoTransform_ideal_eq_controlledTransform (𝔪 := B) hN hBD.isWellFormed.isCoherent hπ,hId,hMark]
      exact HironakaHypersurfaceStrictIdeal.isInvertible_controlledTransform hπ hInv q
        (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport
          (CartanIrreducible.cartanCoherence U hA) hCentre.1 hCentre.2.1)
    have hAvoid : U ⊆ closure (U \ C) := hDense.trans (closure_mono (by
      intro x hx
      refine ⟨hx.2.1,fun hxC => ?_⟩
      exact ((HironakaHypersurfaceStageCenters.cosupport_high_mark_subset_diff_regularLocus
        hA.isClosed (Nat.lt_succ_self n) hq (hCentre.2.1 hxC)).2) hx))
    have hPureNext : IsPureDim (n := n+1) (strictTransform (n+1) π U) n := by
      rw [← BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hAvoid]
      exact HironakaActualPureStrictTransforms.isPureDim_geoStrictTransform hπ hA hPureU
    dsimp only
    rw [hEq]
    exact ⟨hStrict,hInvNext,hPureNext⟩


/-- The data retained on the actual common prefix when its next native
principal epoch is opened. -/
structure PrincipalPrefixState
    (M : MarkedIdeal (n+1) X) (W : Set X) (P : BlowupTower X D) (cap : ℕ) : Prop where
  canonical : IsCanonical M ((canonicalInvariant (n+1)).inv M) P
  singular : StageCentres (fun L C => C ⊆ singularSet (n := n+1)
    (strictTransform (n+1) L.proj W)) P
  higher : ∀ r < cap, CentresOrdGt M r P
  residual : nmPart (geoTransformAlong M P) =
    vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)
  invertible : (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)).IsInvertible
  pure : IsPureDim (n := n+1) (strictTransform (n+1) P.proj W) n
  noFactor : HasNoBoundaryFactor
    (whole (strictTransform (n+1) P.proj W) (geoTransformAlong M P).E 1)

/-- A lower exact native atlas returns the state needed by the next
atlas on the actual strict target and the complete inherited boundary. -/
theorem PrincipalPrefixState.advance
    {M : MarkedIdeal (n+1) X} (hM : IsInvDomain (n+1) M) (hMN : M.N = univ)
    (hMd : M.d = 1) {W : Set X} (hW : IsComplexAnalyticSubset (n := n+1) W)
    {P : BlowupTower X D} {cap : ℕ} (hP : PrincipalPrefixState M W P cap)
    {q : ℕ} (hq : 2 ≤ q) (hqcap : q < cap) (H : ℕ → ℕ) (S : BlowupTower D Y) :
    let U := strictTransform (n+1) P.proj W
    let E := (geoTransformAlong M P).E
    let F := whole U E q
    ActualNativePhase U E H S →
    IsMaximalOrderAlong F.N F.ideal q →
    HasExactCoveredNativeAtlas U E H S F →
    PrincipalPrefixState M W (P.append S) q := by
  dsimp only
  intro hPhase hCap hAtlas
  let U := strictTransform (n+1) P.proj W
  let A := geoTransformAlong M P
  let F := whole U A.E q
  let R := canonicalInvariant.{0} (n+1)
  have hTP := R.isInvValue.isGeoTestTower_of_isCanonical hM P hP.canonical
  have hAD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hTP
  have hAN : A.N = univ :=
    (pullback_eq_mul_geoTransformAlong M hMN hM.isWellFormed.isCoherent P hTP).1
  have hAd : A.d = 1 := (d_geoTransformAlong M P).trans hMd
  have hU : IsComplexAnalyticSubset (n := n+1) U :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  have hDense := HironakaActualHSSingularBlowupRestart.actualPure_subset_closure_regularLocus hU hP.pure
  have hBase := HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure
    le_rfl hU (Nat.lt_succ_self n) hDense
  have hF : IsInvDomain (n+1) F :=
    ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hBase.isWellFormed.isCoherent,
      hAD.isWellFormed.isSNCDivisor,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hAD.isWellFormed.isSNCDivisor⟩,
      hBase.dimLE, by change 1 ≤ q; omega, hBase.isNonzeroAlongAt⟩
  have hCanF := canonical_of_exact_covered_native_atlas U A.E H S F hF hAtlas
  have hNoF : HasNoBoundaryFactor F := hP.noFactor
  obtain ⟨hCan,hHigher,hPart⟩ := append_whole_canonical_of_principal_residual_epoch
    M hM P hP.canonical F hF rfl hNoF hCap (hP.higher q hqcap) S hCanF
    hAN rfl (by change A.d ≤ q; omega) hP.residual
  obtain ⟨hIdeal,hI,hPure⟩ := principal_epoch_strict_ideal U hU hP.pure hP.invertible
    A.E q hq F rfl hF hNoF hCap S hCanF
  let B := geoTransformAlong F S
  have hTF := R.isInvValue.isGeoTestTower_of_isCanonical hF S hCanF
  have hBD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hF S hTF
  have hBN : B.N = univ := (pullback_eq_mul_geoTransformAlong F rfl hF.isWellFormed.isCoherent S hTF).1
  have hNoB := no_boundary_factor_along_lower_native_epoch F hF hNoF hCap S hCanF
  have hNonmon := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hBD.isWellFormed.1
    hBD.isWellFormed.3 hBD.isWellFormed.4 hBD.isWellFormed.2 hNoB
  change nmPart B = RestrictedIdealExtension.restrictOn (n+1) B.N B.ideal at hNonmon
  rw [hBN,BlowupTowerTransforms.restrictOn_univ hBD.isWellFormed.isCoherent] at hNonmon
  have hStrict : strictTransform (n+1) (P.append S).proj W = strictTransform (n+1) S.proj U := by
    rw [BlowupTower.proj_append,StrictTransformComposition.strictTransform_comp
      P.contMDiff_proj S.contMDiff_proj]
  have hBE : (geoTransformAlong M (P.append S)).E = B.E := by
    rw [geoTransformAlong_append]
    exact HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq
      (𝔍 := A) (𝔪 := F) rfl S
  have hSing := HironakaG8IntrinsicSingularBlockSchedule.intrinsic_stage_append
    W P S hP.singular hPhase.singular
  refine ⟨hCan,hSing,hHigher,?_,?_,?_,?_⟩
  · rw [hPart,hNonmon,hStrict]
    exact hIdeal
  · rwa [hStrict]
  · rwa [hStrict]
  · rw [hStrict,hBE]
    unfold HasNoBoundaryFactor at hNoB ⊢
    change ∀ x ∈ univ, ∀ i : Fin B.E.length, x ∈ B.E.get i →
      ∃ g, (vanishingIdeal (n := n+1) (strictTransform (n+1) S.proj U)).mem x g ∧
        ¬ IsInSpanOnAt (n := n+1) univ ((vanishingIdeal (n := n+1) (B.E.get i)).mem x) x g
    change B.ideal = _ at hIdeal
    rwa [hBN,hIdeal] at hNoB



/-- A finite sequence of actual labelled phases. Each next atlas uses
the strict transform and the ordered boundary on the literal appended prefix.
The indices record the Hilbert--Samuel labels and strictly descending marks. -/
inductive PrincipalAtlasEpochs (M : MarkedIdeal (n+1) X) (W : Set X) :
    {A Z : CMfd.{0} (n+1)} → BlowupTower X A → ℕ → BlowupTower A Z →
      List ((ℕ → ℕ) × ℕ) → ℕ → Prop
  | done {A} (P : BlowupTower X A) (cap : ℕ) :
      PrincipalAtlasEpochs M W P cap .refl [] cap
  | next {A B Z} {P : BlowupTower X A} {cap q last : ℕ} {H : ℕ → ℕ}
      {S : BlowupTower A B} {T : BlowupTower B Z} {labels : List ((ℕ → ℕ) × ℕ)}
      (hq : 2 ≤ q) (hDrop : q < cap)
      (phase : ActualNativePhase (strictTransform (n+1) P.proj W)
        (geoTransformAlong M P).E H S)
      (hCap : IsMaximalOrderAlong univ
        (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) q)
      (atlas : HasExactCoveredNativeAtlas (strictTransform (n+1) P.proj W)
        (geoTransformAlong M P).E H S
        (whole (strictTransform (n+1) P.proj W) (geoTransformAlong M P).E q))
      (rest : PrincipalAtlasEpochs M W (P.append S) q T labels last) :
      PrincipalAtlasEpochs M W P cap (S.append T) ((H,q) :: labels) last

/-- All supplied labelled phases concatenate to a canonical prefix for
the original marked ideal. The terminal state can serve another atlas
on its actual strict carrier and inherited boundary. -/
theorem PrincipalAtlasEpochs.canonical
    {M : MarkedIdeal (n+1) X} (hM : IsInvDomain (n+1) M) (hMN : M.N = univ)
    (hMd : M.d = 1) {W : Set X} (hW : IsComplexAnalyticSubset (n := n+1) W)
    {P : BlowupTower X D} {cap last : ℕ} {T : BlowupTower D Y}
    {labels : List ((ℕ → ℕ) × ℕ)}
    (hEpochs : PrincipalAtlasEpochs M W P cap T labels last)
    (hP : PrincipalPrefixState M W P cap) :
    PrincipalPrefixState M W (P.append T) last := by
  induction hEpochs with
  | done _ _ => exact hP
  | next hq hDrop hPhase hCap hAtlas _ ih =>
    rw [← BlowupTower.append_assoc]
    exact ih (hP.advance hM hMN hMd hW hq hDrop _ _ hPhase hCap hAtlas)

/-- The starting state of the whole mark-one record on a pure invertible
hypersurface, with its given ordered boundary. -/
theorem initial_principal_prefix_state
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W) (E : List (Set X))
    (hPure : IsPureDim (n := n+1) W n)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hM : IsInvDomain (n+1) (whole W E 1))
    (hNo : HasNoBoundaryFactor (whole W E 1)) (cap : ℕ) :
    PrincipalPrefixState (whole W E 1) W .refl cap := by
  have he : strictTransform (n+1) (id : X → X) W = W :=
    HironakaG11PresTowerState.strictTransform_id hW.isClosed
  have hPart := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hM.isWellFormed.1
    hM.isWellFormed.3 hM.isWellFormed.4 hM.isWellFormed.2 hNo
  change nmPart (whole W E 1) =
    RestrictedIdealExtension.restrictOn (n+1) univ (vanishingIdeal (n := n+1) W) at hPart
  rw [BlowupTowerTransforms.restrictOn_univ hM.isWellFormed.isCoherent] at hPart
  refine ⟨trivial,trivial,fun _ _ => trivial,?_,?_,?_,?_⟩ <;>
    simp only [BlowupTower.proj_refl,geoTransformAlong_refl,he]
  · exact hPart
  · exact hI
  · exact hPure
  · exact hNo

/-- A finite chain starting at the given hypersurface is canonical for its
original whole mark-one record, and retains the terminal strict ideal. -/
theorem whole_canonical_of_principal_atlas_epochs
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W) (E : List (Set X))
    (hPure : IsPureDim (n := n+1) W n)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hM : IsInvDomain (n+1) (whole W E 1)) (hNo : HasNoBoundaryFactor (whole W E 1))
    {cap last : ℕ} {T : BlowupTower X Y} {labels : List ((ℕ → ℕ) × ℕ)}
    (hEpochs : PrincipalAtlasEpochs (whole W E 1) W .refl cap T labels last) :
    PrincipalPrefixState (whole W E 1) W T last := by
  simpa only [BlowupTower.refl_append] using
    hEpochs.canonical hM rfl rfl hW (initial_principal_prefix_state W hW E hPure hI hM hNo cap)

end
end Hironaka.HironakaG8PrincipalEpochSuccession
