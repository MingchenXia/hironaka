import Hironaka.Resolution.HironakaG1LaterAdvancedHeadExample
import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead
import Hironaka.Resolution.HironakaG1LaterSelectedActualOrder

/-! Canonicality of the actual advanced-head example. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterAdvancedHeadCanonicalExample

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaRelativeNormalIdeal
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  HironakaG1LaterPositiveNormalExample HironakaG1LaterAdvancedHeadExample
  HironakaG1LaterPositiveSuccessorRead GermIdealPullbackCalculus
  RelativePrincipalizationSpan GermIdealOrder InvertibleIdealQuotient
  NormalCrossings HironakaPrincipalizationBoundary HironakaG1PositiveNormalPhase
  HironakaG1LaterSelectedActualOrder NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  GeneralValue MarkedIdealRestrictOpen MarkedIdealBiholomorphism CompanionRebase
  HomogenizedIdealAlong CoefficientIdeal InvDomainMemberRestriction InvDomainTowerAlong
  HironakaG1InitialPositiveGeneralRead CompanionReductionAlong BoundaryCount

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D (i : Fin 3) : Set X := {z | z.val i = 0}
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev M : MarkedIdeal 3 X := {P with E := [D 0, D 1]}
private abbrev T : BlowupTower X X := .refl
private abbrev O := maskA M B q
private abbrev L := lowerMarkedM M 1 B q

private theorem generator_member (j : Bool ⊕ Unit) (z : X) :
    M.ideal.mem z (paddedGenerator j ∘ (Subtype.val : X → ComplexModel 3)) := by
  change P.ideal.mem z _
  rw [proper_source_generators]
  have hHol : HolomorphicAt 3 (paddedGenerator j) z.val :=
    Eventually.of_forall fun w => paddedGenerator_hol j w
  exact GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self ⟨paddedGenerator j, isInSpanAt_self ⟨j, rfl⟩ hHol, rfl⟩
      (hHol.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)))

/-- The additional old boundary leaves the exact initial cosupport equal to
the singleton common origin. -/
theorem joint_advanced_initial_cosupport : M.cosupp = C := by
  ext z
  constructor
  · intro hz
    have hM : IsInvDomain 3 M := joint_added_boundary_test.1
    have hVan (j : Bool ⊕ Unit) : paddedGenerator j z.val = 0 := by
      have hg := generator_member j z
      exact (vanishesToOrderOn_one_iff hz.1
        (GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)).mp (hz.2 _ hg)
    have hp : p.val = 0 := map_zero (tangentInclusion 2 1)
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [hp]
    ext i
    fin_cases i
    · exact hVan (.inl true)
    · simpa [paddedGenerator] using hVan (.inl false)
    · exact hVan (.inr ())
  · intro hz
    have hTest : IsGeoTestTower M B := joint_added_boundary_test.2
    exact hTest.2.2.1 hz

/-- With a singleton initial cosupport the actual first point blowup is
canonical for any linearly ordered invariant on the upper record. -/
theorem joint_advanced_head_isCanonical {Λ : Type} [LinearOrder Λ]
    (I : ∀ {Z : CMfd.{0} 3}, BlowupTower X Z → Z → Λ) :
    IsCanonical M I B := by
  refine ⟨trivial, Or.inr ?_⟩
  change C = ResolutionDriver.maxLocus (I T) M.cosupp
  rw [joint_advanced_initial_cosupport]
  ext z
  constructor
  · intro hz
    refine ⟨hz, ?_⟩
    intro w hw
    rw [mem_singleton_iff.mp hw, mem_singleton_iff.mp hz]
  · exact fun hz => hz.1

private abbrev Dsrc (i : Fin 2) : Set U := {z | z.val i = 0}
private abbrev Q : MarkedIdeal 2 U := {sourceRecord with E := [Dsrc 0, Dsrc 1]}

private theorem source_snc : IsSNCDivisor 2 Q.E := by
  classical
  refine ⟨?_, ?_⟩
  · intro H hH
    change H ∈ [Dsrc 0, Dsrc 1] at hH
    rcases List.mem_cons.mp hH with rfl | hH
    · exact isClosed_eq ((EuclideanSpace.proj (𝕜 := ℂ) _).continuous.comp
        continuous_subtype_val) continuous_const
    rw [List.mem_singleton] at hH
    subst H
    exact isClosed_eq ((EuclideanSpace.proj (𝕜 := ℂ) _).continuous.comp
      continuous_subtype_val) continuous_const
  · intro x
    let idx : Fin Q.E.length → Fin 2 := fun i => ⟨i.val, i.isLt⟩
    have hGet (i : Fin Q.E.length) : Q.E.get i = Dsrc (idx i) := by fin_cases i <;> rfl
    have hChart (z : U) : (complexChartAt (n := 2) x).val z = z.val := rfl
    refine ⟨fun i => {idx i}, ?_, fun _ _ => Finset.card_singleton _, ?_⟩
    · let Φ : LocalHolomorphicEquivAt (n := 2) ((complexChartAt (n := 2) x).val x) :=
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
      refine ⟨Φ, ?_, by change _ - _ = 0; rw [hChart, sub_self], ?_⟩
      · intro w _
        let y : U := ⟨w, mem_univ _⟩
        change w ∈ (chartAt (ComplexModel 2) x).target
        rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
        exact (OpenPartialHomeomorph.refl (ComplexModel 2)).map_subtype_source
          ⟨x⟩ (x := y) (mem_univ _)
      · intro i hi y _ _
        change x ∈ Q.E.get i at hi
        change y ∈ Q.E.get i ↔ _
        rw [hGet] at hi ⊢
        have hi0 : x.val (idx i) = 0 := hi
        change y.val (idx i) = 0 ↔
          (complexChartAt (n := 2) x).val y - x.val ∈ coordSubspace {idx i}
        rw [hChart]
        simp [coordSubspace, hi0]
    · intro i _ j _ hij
      exact Fin.ext (congrArg (fun j : Fin 2 => j.val) (Finset.singleton_injective hij))

private theorem Q_domain : IsInvDomain 2 Q :=
  HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    sourceRecord_domain.isWellFormed.isCoherent
    (fun x => sourceRecord_domain.isNonzeroAlongAt x (mem_univ _)) source_snc

private abbrev A := CMfd.of (n := 3) O
private abbrev e : BlowupTower A A := .refl
private abbrev R₂ := invFamily (by decide : 0 < 3) 2
private abbrev R₁ := invFamily (by decide : 0 < 3) 1

private theorem upper_level : level M B q = 1 :=
  joint_added_boundary_upper_regime_advances.2.1
private theorem upper_run : regimeRun (stepRegime M 1) B q = 0 := by
  simpa only [upper_level] using joint_added_boundary_upper_regime_advances.2.2

private theorem isCanonical_stepOne :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM R₂ M) B :=
  joint_advanced_head_isCanonical _

private theorem bar_eq : barMarked M = M := by
  change coeffMarkedAlong (homMarkedAlong M) = M
  have hM : IsInvDomain 3 M := joint_added_boundary_test.1
  rw [homMarkedAlong_eq_of_mark_one M rfl hM.isWellFormed.isCoherent,
    coeffMarkedAlong_eq_of_mark_one M rfl hM.isWellFormed.isCoherent]

private abbrev G := geoTransformAlong (barMarked M) B
private abbrev K := memberRestrict G (membersThrough G.E (origMembers M B) q)

private theorem K_wellFormed : K.IsWellFormed := by
  have hM : IsInvDomain 3 M := joint_added_boundary_test.1
  have hG : G.IsWellFormed := by
    change (geoTransformAlong (barMarked M) B).IsWellFormed
    rw [bar_eq]
    exact MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed B
      joint_added_boundary_test.2
  exact isWellFormed_memberRestrict (by decide) hG _

private theorem mark_one : L.d = 1 := by
  have hG : G.d = 1 := by
    change (geoTransformAlong (barMarked M) B).d = 1
    rw [bar_eq]
    rfl
  have hM : IsInvDomain 3 M := joint_added_boundary_test.1
  have hGI : G.ideal.IsCoherent := by
    change (geoTransformAlong (barMarked M) B).ideal.IsCoherent
    rw [bar_eq]
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed B
      joint_added_boundary_test.2).isCoherent
  change (coeffMarkedAlong G).d = 1
  rw [coeffMarkedAlong_eq_of_mark_one G hG hGI, hG]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lower_data : ∃ hq : q ∈ O, (⟨q, hq⟩ : O) ∈ L.cosupp ∧ IsInvDomain 2 L := by
  have h := original_normal_positive_phase_head Q Q_domain (s := 0) B isCanonical_stepOne q
    joint_added_boundary_survives_nonspecial.1 upper_level joint_added_boundary_survives_nonspecial.2
  have hr : regimeRun (stepRegime (properNormalMarked Q) (0 + 1)) B q = 0 := upper_run
  dsimp only at h
  rw [hr] at h
  obtain ⟨_, _, _, _, hp, hCos, hDom, _, _⟩ := h
  exact ⟨hp, hCos, hDom⟩

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency false in
/-- At the new selected head the genuine nonmonomial order is one, the
actual mark of the selected record. -/
theorem joint_advanced_head_lower_true_order :
    ∀ z : O, z.val = q → nmOrd (M := A) L z = L.d ∧ L.d = 1 := by
  intro z hz
  obtain ⟨hq, hqCos, hL⟩ := lower_data
  have hqBar : q ∈ G.cosupp := by
    change q ∈ (geoTransformAlong (barMarked M) B).cosupp
    rw [bar_eq]
    exact joint_added_boundary_survives_nonspecial.1
  obtain ⟨W, _, hqW, hWO, _, _, _, _, hWOd⟩ :=
    exists_later_selected_actual_normal_order Q Q_domain (s := 0) B joint_added_boundary_test.2
      q hqBar upper_level joint_added_boundary_survives_nonspecial.2
  let J : MarkedIdeal 3 (CMfd.of (n := 3) W) := MarkedIdeal.pullback (Subtype.val : W → Y) K
  let qW : W := ⟨q, hqW⟩
  have hHol (x : Y) (g : Y → ℂ) (hg : K.ideal.mem x g) : HolomorphicAt 3 g x :=
    GermIdeal.IsCoherent.holomorphicAt_mem K_wellFormed.isCoherent hg
  have hqK : q ∈ K.cosupp := by
    change (⟨q, hq⟩ : O) ∈ (MarkedIdeal.pullback (Subtype.val : O → Y) K).cosupp at hqCos
    rw [cosupp_pullback_val K hHol O] at hqCos
    exact hqCos
  have hWcos : qW ∈ (geoTransformAlong J (BlowupTower.refl (X := CMfd.of (n := 3) W))).cosupp := by
    change qW ∈ (MarkedIdeal.pullback (Subtype.val : W → Y) K).cosupp
    rw [cosupp_pullback_val K hHol W]
    exact hqK
  have hOrdW : nmOrd (M := CMfd.of (n := 3) W) J qW = L.d :=
    hWOd (BlowupTower.refl (X := CMfd.of (n := 3) W)) trivial qW hWcos
  let W' := MaxLocusLocal.nestedOpens O W
  let J' : MarkedIdeal 3 (CMfd.of (n := 3) W') := MarkedIdeal.pullback (Subtype.val : W' → O) L
  let Φ := MaxLocusLocal.nestedOpensDiffeo (n := 3) hWO
  have hJ' : IsInvDomain 2 J' := isInvDomain_pullback_val W' hL
  have hEq : MarkedIdeal.pullback Φ.symm J' = J :=
    MaxLocusLocal.pullback_symm_nestedOpensDiffeo K_wellFormed.isCoherent hWO
  have hDiffeo := nmOrd_pullback_diffeo (by decide : 0 < 3) Φ.symm
    hJ'.isWellFormed hJ'.isNonzeroAlongAt qW
  rw [hEq] at hDiffeo
  have hOpen := nmOrd_pullback_val (M := A) (𝔪 := L) (by decide : 0 < 3)
    hL.isWellFormed hL.isNonzeroAlongAt W' (show W' from Φ.symm qW)
  have hPoint : (Φ.symm qW).val = z := Subtype.ext hz.symm
  refine ⟨?_, mark_one⟩
  exact (congrArg (nmOrd (M := A) L) hPoint).symm.trans (hOpen.symm.trans (hDiffeo.symm.trans hOrdW))

private abbrev W := ordMask (M := A) L 1
private abbrev J := compAt (X := A) L 1 e
private abbrev V := CMfd.of (n := 3) W
private abbrev E : BlowupTower V V := .refl

private theorem companion_boundary : J.E = L.E.map (fun H => (Subtype.val : W → O) ⁻¹' H) := by
  simp only [J, compAt, companionOf, companionAlong_E]
  rfl

private theorem companion_mark_one : J.d = 1 := by
  simp only [J, compAt, companionOf, companionAlong_d]
  change (if 1 < L.d then 1 * (L.d - 1) else 1) = _
  simp [mark_one]

set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
/-- The original canonical upper Step One at the advanced head reads the
genuine mark-one order companion. Its born divisor gives inner level one. -/
theorem joint_advanced_canonical_positive_successor :
    IsCanonical M (Seq.StepOneValueMasked.stepOneInvM R₂ M) B ∧
      ∃ (hq : q ∈ O) (hw : (⟨q, hq⟩ : O) ∈ W),
        J.d = 1 ∧ level J E (⟨⟨q, hq⟩, hw⟩ : W) = 1 ∧
          Seq.StepOneValueMasked.stepOneInvM R₂ M B q =
            toLex (1, (positiveSuccessorRead 1
              (Seq.StepOneValueMasked.stepOneInvM (X := V) R₁ J E (⟨⟨q, hq⟩, hw⟩ : W)) :
                WithTop (ValTy 2))) := by
  refine ⟨isCanonical_stepOne, ?_⟩
  have hr : regimeRun (stepRegime (properNormalMarked Q) (0 + 1)) B q = 0 := upper_run
  have hOrder := original_upper_positive_successor_read Q Q_domain (s := 0) B isCanonical_stepOne q
    joint_added_boundary_survives_nonspecial.1 upper_level joint_added_boundary_survives_nonspecial.2
    1 (by decide)
  dsimp only at hOrder
  rw [hr] at hOrder
  have hOrd : ∀ z : O, z.val = q → nmOrd (M := A) L z = 1 := by
    intro z hz
    obtain ⟨h, hm⟩ := joint_advanced_head_lower_true_order z hz
    exact h.trans hm
  obtain ⟨hq, _, h⟩ := hOrder hOrd
  obtain ⟨hw, _, _, _, _, hVal⟩ := h
  refine ⟨hq, hw, companion_mark_one, ?_, hVal⟩
  have hOrig : origMembers J E = J.E := List.take_length
  have hOriginal : origMembers L e = L.E := List.take_length
  obtain ⟨h₀, hLevel⟩ := joint_advanced_head_selected_anchor_level
  have hSame : (⟨q, h₀⟩ : O) = ⟨q, hq⟩ := rfl
  rw [hSame] at hLevel
  unfold level at hLevel ⊢
  rw [hOrig, companion_boundary, CodimOnePartCanonical.boundaryCount_map_preimage, ← hOriginal]
  exact hLevel

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency false in
/-- On this original canonical history, no level-zero inner letter at true
order one can produce the actual upper value. -/
theorem joint_advanced_canonical_not_level_zero_inner (w : WithTop (ValTy 1)) :
    Seq.StepOneValueMasked.stepOneInvM R₂ M B q ≠
      toLex (1, (positiveSuccessorRead 1 (toLex (0, w)) : WithTop (ValTy 2))) := by
  obtain ⟨_, hq, hw, _, hLevel, hRead⟩ := joint_advanced_canonical_positive_successor
  let z : W := ⟨⟨q, hq⟩, hw⟩
  let v := Seq.StepOneValueMasked.stepOneInvM (X := V) R₁ J E z
  have hv : (ofLex v).1 = 1 := by
    change (ofLex (Seq.StepOneValueMasked.stepOneInvL (X := V) R₁ J (lowerMarkedM J) E z)).1 = 1
    rw [Seq.StepOneValueMasked.stepOneInvL_fst]
    exact hLevel
  intro h
  have hOuter := congrArg (fun a : ℕ ×ₗ WithTop (ValTy 2) => (ofLex a).2) (hRead.symm.trans h)
  have hReadEq : positiveSuccessorRead 1 v = positiveSuccessorRead 1 (toLex (0, w)) :=
    WithTop.coe_injective hOuter
  have hLetter := congrArg (fun a : ValTy 2 => ofLex (ofLex a).2) hReadEq
  change Sum.inr (↑v : WithTop (ℕ ×ₗ WithTop (ValTy 1))) =
    Sum.inr (↑(toLex (0, w)) : WithTop (ℕ ×ₗ WithTop (ValTy 1))) at hLetter
  have hInner := WithTop.coe_injective (Sum.inr.inj hLetter)
  have hZero := congrArg (fun a : ℕ ×ₗ WithTop (ValTy 1) => (ofLex a).1) hInner
  exact (by decide : (1 : ℕ) ≠ 0) (hv.symm.trans hZero)

end
end Hironaka.HironakaG1LaterAdvancedHeadCanonicalExample
