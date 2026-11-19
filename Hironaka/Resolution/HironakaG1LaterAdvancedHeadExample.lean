import Hironaka.Resolution.HironakaG1LaterPositiveBornLevelExample
import Hironaka.Blowup.BlowupTowerSplit

/-! A genuine positive regime change at the first point blowup. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadExample

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupFlatCoordinates
  BlowupMonomialCharts BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings ResolutionInvariantSpec StepOneValue StepOneValueMasked StepOneRegime
  BoundaryCount InvDomainMemberRestriction MemberInterLocusAlong StepOneLowerDomain
  HironakaPrincipalizationBoundary HomogenizedIdealAlong HironakaActualOpenZeroSectionDifferentials
  HironakaActualNativeSectionInitialBar HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaRelativeNormalIdeal
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaOneDimensionalCanonicalSuperlevels HironakaG1LaterPositiveNormalExample
  HironakaG1LaterPositiveSelectedExample HironakaG1LaterPositiveBornLevelExample

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D (i : Fin 3) : Set X := {z | z.val i = 0}
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev M : MarkedIdeal 3 X := { P with E := [D 0, D 1] }
private abbrev T : BlowupTower X X := .refl
private abbrev D' (i : Fin 3) : Set Y := geoStrictTransform π C (D i)
private abbrev F : Set Y := π ⁻¹' C
private abbrev A := geoTransformAlong (barMarked M) B

private theorem p_zero : p.val = 0 := map_zero (tangentInclusion 2 1)
private theorem q_proj : π q = p :=
  joint_first_point_blowup_positive_normal_contact.2.2.2.1
private theorem q_D0 : q ∈ D' 0 :=
  joint_first_point_blowup_positive_normal_contact.2.2.2.2.2.1

private theorem extra_misses_chart (z : Y) (hz : z ∈ yChart.source) : z ∉ D' 1 := by
  intro h
  have hV : ∀ᶠ w in 𝓝 z, w ∈ yChart.source := yChart.isOpen_source.mem_nhds hz
  obtain ⟨w, hw, hwV⟩ := ((mem_closure_iff_frequently.mp h).and_eventually hV).exists
  change π w ∈ D 1 \ C at hw
  apply hw.2
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  rw [chart_projection w hwV, p_zero]
  have hzero : yChart.toFun w (1 : Fin 3) = 0 := by
    have h1 : (π w).val (1 : Fin 3) = 0 := hw.1
    rw [chart_projection w hwV, monomial_apply, if_neg (by simp)] at h1
    exact h1
  ext i
  by_cases hi : i = 1
  · subst i
    simp [hzero]
  · simp [hi, hzero]

private theorem boundaryCount_two {W : Type} (H K : Set W) (z : W)
    (hz : z ∈ H) (hK : z ∉ K) : boundaryCount [H, K] z = 1 := by
  classical
  unfold boundaryCount
  have hf : Finset.univ.filter (fun i : Fin ([H, K].length) => z ∈ [H, K].get i) = {0} := by
    ext i
    fin_cases i <;> simp [hz, hK]
  rw [hf, Finset.card_singleton]

/-- The endpoint retains one original member, after starting on both. The
level-one run has length zero, so the upper split takes the new stage as head. -/
theorem joint_added_boundary_upper_regime_advances :
    level M T p = 2 ∧ level M B q = 1 ∧
      regimeRun (stepRegime M (level M B q)) B q = 0 := by
  have hInitial : level M T p = 2 := by
    change boundaryCount [D 0, D 1] p = 2
    classical
    unfold boundaryCount
    rw [Finset.filter_true_of_mem]
    · simp
    · intro i _
      fin_cases i <;> exact congrArg (fun w : ComplexModel 3 => w _) p_zero
  have hFinal : level M B q = 1 :=
    boundaryCount_two (D' 0) (D' 1) q q_D0 (extra_misses_chart q chart_q.1)
  refine ⟨hInitial, hFinal, ?_⟩
  rw [hFinal]
  change regimeRun (stepRegime M 1) (.step T C π hπ) q = 0
  apply regimeRun_step_of_not
  rw [q_proj]
  intro h
  exact (by decide : (2 : ℕ) ≠ 1) (hInitial.symm.trans h.1)

private theorem old_members : origMembers M B = [D' 0, D' 1] := rfl
private theorem original_members : origMembers P B = [D' 0] := rfl

/-- Adding the old middle-coordinate hyperplane preserves the surviving
endpoint and its nonspeciality in the positive regime. -/
theorem joint_added_boundary_survives_nonspecial :
    q ∈ (geoTransformAlong M B).cosupp ∧ ¬ IsSpecial M B q := by
  refine ⟨q_cosupp, ?_⟩
  rintro (⟨hZero, _⟩ | ⟨_, hMember⟩)
  · exact (by decide : (1 : ℕ) ≠ 0)
      (joint_added_boundary_upper_regime_advances.2.1.symm.trans hZero)
  apply joint_first_blowup_selected_nonspecial
  right
  refine ⟨q_level.ge, mem_memberInterLocus_iff.mpr ?_⟩
  obtain ⟨hq, hLocal⟩ := mem_memberInterLocus_iff.mp hMember
  refine ⟨hq, ?_⟩
  filter_upwards [hLocal] with y hy hyN hyBoundary
  apply hy hyN
  intro H hH hqH
  rw [old_members] at hH
  rcases List.mem_cons.mp hH with rfl | hH
  · exact hyBoundary (D' 0) (by rw [original_members]; simp) hqH
  · rw [List.mem_singleton] at hH
    exact (extra_misses_chart q chart_q.1 (hH ▸ hqH)).elim

private theorem xChart_coord (x y : X) :
    (complexChartAt (n := 3) x).val y = y.val := rfl

private theorem old_snc : IsSNCDivisor 3 M.E := by
  classical
  refine ⟨?_, ?_⟩
  · intro H hH
    change H ∈ [D 0, D 1] at hH
    rcases List.mem_cons.mp hH with rfl | hH
    · exact isClosed_eq ((EuclideanSpace.proj (𝕜 := ℂ) _).continuous.comp
        continuous_subtype_val) continuous_const
    rw [List.mem_singleton] at hH
    subst H
    all_goals exact isClosed_eq ((EuclideanSpace.proj (𝕜 := ℂ) _).continuous.comp
      continuous_subtype_val) continuous_const
  · intro x
    let idx : Fin M.E.length → Fin 3 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
    have hGet (i : Fin M.E.length) : M.E.get i = D (idx i) := by fin_cases i <;> rfl
    refine ⟨fun i => {idx i}, ?_, fun _ _ => Finset.card_singleton _, ?_⟩
    · have hx := xChart_coord x x
      let Φ : LocalHolomorphicEquivAt (n := 3) ((complexChartAt (n := 3) x).val x) :=
        { source := univ
          target := univ
          isOpen_source := isOpen_univ
          isOpen_target := isOpen_univ
          center_mem_source := mem_univ _
          toFun := fun w => w - x.val
          invFun := fun w => w + x.val
          toFun_holomorphic := (differentiable_id.sub_const x.val).differentiableOn
          invFun_holomorphic := (differentiable_id.add_const x.val).differentiableOn
          mapsTo_toFun := mapsTo_univ _ _
          mapsTo_invFun := mapsTo_univ _ _
          left_inv := fun w _ => sub_add_cancel w x.val
          right_inv := fun w _ => add_sub_cancel_right w x.val }
      refine ⟨Φ, ?_, by change _ - _ = 0; rw [hx, sub_self], ?_⟩
      · intro w _
        let y : productOpen U := ⟨w, by
          change tangentProjection 2 1 w ∈ (⊤ : Opens (ComplexModel 2))
          exact mem_univ _⟩
        change w ∈ (chartAt (ComplexModel 3) x).target
        rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
        exact (OpenPartialHomeomorph.refl (ComplexModel 3)).map_subtype_source
          ⟨x⟩ (x := y) (mem_univ _)
      · intro i hi y _ _
        change x ∈ M.E.get i at hi
        change y ∈ M.E.get i ↔ _
        rw [hGet] at hi ⊢
        have hi0 : x.val (idx i) = 0 := hi
        change y.val (idx i) = 0 ↔
          (complexChartAt (n := 3) x).val y - x.val ∈ coordSubspace {idx i}
        rw [xChart_coord]
        simp [coordSubspace, hi0]
    · intro i _ j _ hij
      exact Fin.ext (congrArg (fun j : Fin 3 => j.val) (Finset.singleton_injective hij))

private theorem M_domain : IsInvDomain 3 M := by
  have hP := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain
  exact HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    hP.isWellFormed.isCoherent (fun x => hP.isNonzeroAlongAt x (mem_univ _)) old_snc

private theorem M_bar : barMarked M = M := by
  change coeffMarkedAlong (homMarkedAlong M) = M
  rw [homMarkedAlong_eq_of_mark_one M rfl M_domain.isWellFormed.isCoherent,
    coeffMarkedAlong_eq_of_mark_one M rfl M_domain.isWellFormed.isCoherent]

/-- The expanded ordered old boundary is SNC, and its actual first blowup
at the common origin is a test tower. -/
theorem joint_added_boundary_test : IsInvDomain 3 M ∧ IsGeoTestTower M B := by
  have hAd : P.IsAdmissibleCentre C := test.2
  exact ⟨M_domain, trivial, hAd.1, hAd.2.1, hasNormalCrossings_singleton p old_snc⟩

private theorem q_F : q ∈ F := by
  change π q ∈ C
  rw [q_proj]
  exact mem_singleton _

private theorem born_ne_retained_old : F ≠ D' 0 := by
  intro h
  let v := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  let z := yChart.invFun v
  have hz : z ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all v)
  have hCoord : yChart.toFun z = v := yChart.toPartialEquiv.right_inv (chart_all v)
  have hProj : (π z).val = monomial 0 (1 : Fin 3) v := by rw [chart_projection z hz, hCoord]
  have hzD : π z ∈ D 0 := by
    change (π z).val (0 : Fin 3) = 0
    rw [hProj, monomial_apply]
    simp [v]
  have hzC : π z ∉ C := by
    intro hp
    have heq := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp hp)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at heq
    rw [hProj, p_zero, monomial_apply] at heq
    simp [v] at heq
  have hzD' : z ∈ D' 0 := subset_closure (show π z ∈ D 0 \ C from ⟨hzD, hzC⟩)
  exact hzC ((h.symm ▸ hzD') : z ∈ F)

private abbrev O := maskA M B q
private abbrev L := lowerMarkedM M 1 B q

private theorem dropped_old_empty_on_mask : (Subtype.val : O → Y) ⁻¹' D' 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzO := (interior_subset z.property).1
  have hOld : D' 1 ∈ origMembers M B := by rw [old_members]; simp
  exact extra_misses_chart q chart_q.1 (hzO _ hOld hz)

private theorem retained_boundary_on_stage :
    (memberRestrict A (membersThrough A.E (origMembers M B) q)).E = [D' 1, F] := by
  classical
  rw [memberRestrict_E]
  change (((List.finRange 3).filter fun i =>
    i ∉ membersThrough [D' 0, D' 1, F] [D' 0, D' 1] q).map [D' 0, D' 1, F].get) = _
  have hm0 : (0 : Fin 3) ∈ membersThrough [D' 0, D' 1, F] [D' 0, D' 1] q :=
    mem_membersThrough.mpr (by simpa using q_D0)
  have hm1 : (1 : Fin 3) ∉ membersThrough [D' 0, D' 1, F] [D' 0, D' 1] q := by
    rw [mem_membersThrough]
    simp [extra_misses_chart q chart_q.1]
  have hF1 : F ≠ D' 1 := fun h => extra_misses_chart q chart_q.1 (h ▸ q_F)
  have hm2 : (2 : Fin 3) ∉ membersThrough [D' 0, D' 1, F] [D' 0, D' 1] q := by
    rw [mem_membersThrough]
    change ¬ (F ∈ [D' 0, D' 1] ∧ q ∈ F)
    intro h
    rcases List.mem_cons.mp h.1 with hl | hl
    · exact born_ne_retained_old hl
    · exact hF1 (List.mem_singleton.mp hl)
  rw [show List.finRange 3 = [(0 : Fin 3), 1, 2] from by decide]
  simp [hm0, hm1, hm2]

/-- The later lower record keeps the missing old slot as an empty member
on the mask, followed by the born divisor. -/
theorem joint_advanced_head_selected_boundary :
    L.E = [∅, (Subtype.val : O → Y) ⁻¹' F] := by
  change List.map (fun H => (Subtype.val : O → Y) ⁻¹' H)
    (memberRestrict A (membersThrough A.E (origMembers M B) q)).E = _
  rw [retained_boundary_on_stage]
  change [(Subtype.val : O → Y) ⁻¹' D' 1, (Subtype.val : O → Y) ⁻¹' F] = _
  rw [dropped_old_empty_on_mask]

/-- At the advanced head the anchor lies in the actual positive mask.
The born divisor gives the selected lower record level one at that anchor. -/
theorem joint_advanced_head_selected_anchor_level :
    ∃ hq : q ∈ O,
      level L (BlowupTower.refl (X := CMfd.of (n := 3) O)) (⟨q, hq⟩ : O) = 1 := by
  have hTest : IsGeoTestTower (barMarked M) B := M_bar.symm ▸ joint_added_boundary_test.2
  have hq : q ∈ O := mem_maskA M M_domain.isWellFormed M_domain.one_le_d (by decide) B hTest
      joint_added_boundary_upper_regime_advances.2.1.ge joint_added_boundary_survives_nonspecial.2
  refine ⟨hq, ?_⟩
  have hOrig : origMembers L (BlowupTower.refl (X := CMfd.of (n := 3) O)) = L.E := List.take_length
  unfold level
  rw [hOrig, joint_advanced_head_selected_boundary]
  classical
  unfold boundaryCount
  let E : List (Set O) := [∅, (Subtype.val : O → Y) ⁻¹' F]
  change (Finset.univ.filter (fun i : Fin E.length => (⟨q, hq⟩ : O) ∈ E.get i)).card = 1
  have hf : Finset.univ.filter (fun i : Fin E.length => (⟨q, hq⟩ : O) ∈ E.get i) = {1} := by
    ext i
    fin_cases i <;> simp [E, q_proj]
  rw [hf, Finset.card_singleton]

/-- The actual split at the advanced head reads the selected record at the
survivor with an empty tail. Its selected lower anchor has level one. -/
theorem joint_advanced_head_step_one {k : ℕ} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0, 0} 3 k Λ) :
    ∃ hq : q ∈ O,
      Seq.StepOneValueMasked.stepOneInvM R M B q =
        toLex (1, (↑(R.inv L (BlowupTower.refl (X := CMfd.of (n := 3) O))
          (⟨q, hq⟩ : O)) : WithTop Λ)) ∧
      level L (BlowupTower.refl (X := CMfd.of (n := 3) O)) (⟨q, hq⟩ : O) = 1 := by
  obtain ⟨hq, hLevel⟩ := joint_advanced_head_selected_anchor_level
  refine ⟨hq, ?_, hLevel⟩
  · have hNS := joint_added_boundary_survives_nonspecial.2
    have hUpper := joint_added_boundary_upper_regime_advances.2.1
    have hRun := joint_added_boundary_upper_regime_advances.2.2
    change Seq.StepOneValueMasked.stepOneInvL R M (lowerMarkedM M) B q = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R M (lowerMarkedM M) B hNS,
      hRun, hUpper]
    change toLex (1, Seq.StepOneValueMasked.lowerValueL R M (lowerMarkedM M) 1 B
      (BlowupTower.refl (X := Y)) q) = _
    unfold Seq.StepOneValueMasked.lowerValueL
    rw [dif_pos (show (BlowupTower.refl (X := Y)).proj q ∈
      lowerMask M 1 B ((BlowupTower.refl (X := Y)).proj q) from hq)]
    rfl

end
end Hironaka.HironakaG1LaterAdvancedHeadExample
