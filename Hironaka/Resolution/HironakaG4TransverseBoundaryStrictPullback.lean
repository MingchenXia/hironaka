import Hironaka.Resolution.HironakaG4CommonMonomialChart
import Hironaka.Resolution.HironakaSharpActualFirstGoodExceptionalTraceDensity

set_option autoImplicit false

/-! The actual whole strict ideal for a genuinely transverse old boundary.
Source-first full proof: hironaka-g4-transverse-boundary-strict-pullback.tex.
No recursive future-state or residual-compatibility certificate is an input. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4TransverseBoundaryStrictPullback

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold BlowupStrictIdeal
  NormalCrossings SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG4CommonMonomialChart HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFirstGoodExceptionalTraceDensity
  HironakaSharpOriginalFirstMemberExceptionalFactor
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  GermIdealOrder IdealWeightPowers GermIdealPullbackCalculus MonomialPartAlong

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem not_germ_contained_of_transverse (hn : 0 < n) {C H : Set X}
    (hH : IsSNCDivisor n [H]) (hTr : IsTransverse n C [H])
    {x : X} (hxC : x ∈ C) (hxH : x ∈ H) :
    ¬∀ᶠ y in 𝓝 x,y ∈ C → y ∈ H := by
  obtain ⟨f,_hf,hfH,hnot⟩ := exists_actual_transverse_member_not_second_order
    hn hH hTr hxC (0 : Fin [H].length) hxH
  intro hContains
  apply hnot
  have hz : (idealPow (pointIdeal n x) 2).mem x (0 : X → ℂ) :=
    ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,(fun i => i.elim0),(fun i => i.elim0),
      Eventually.of_forall fun _ => by simp⟩
  refine ⟨0,hz,?_⟩
  filter_upwards [hContains,hfH.2] with y hy hyf hyC
  exact hyf (hy hyC)

/-- A genuinely transverse centre contributes no exceptional factor to the
WHOLE old boundary ideal: its actual pullback is the actual strict ideal. -/
theorem pullback_vanishingIdeal_eq_strict_of_transverse (hn : 0 < n) {C H : Set X}
    (hH : IsSNCDivisor n [H]) (hTr : IsTransverse n C [H])
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)=
      vanishingIdeal (n := n) (geoStrictTransform π C H) := by
  classical
  have hHsm : IsClosedSubmanifold n H :=
    MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcI := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hcP := isCoherent_pullback hπ.contMDiff hcI
  have hGet : ∀ i : Fin [H].length,[H].get i=H :=
    fun i => by simpa only [List.mem_singleton] using List.get_mem [H] i
  ext y g
  constructor
  · intro hg
    have hv := pullback_vanishingIdeal_le hπ.contMDiff.continuous H y g hg
    refine ⟨hv.1,?_⟩
    filter_upwards [hv.2] with z hz hzH
    exact hz (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hHsm.1 hzH)
  · intro hg
    by_cases hyC : π y ∈ C
    · by_cases hyH : π y ∈ H
      · obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hH (List.mem_singleton_self H) (π y)
        let M := markedRow (univ : Set X) [H] (vanishingIdeal (n := n) H) 0
        have hRaw : (M.geoTransform C π).ideal=
            GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H) := by
          rw [geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π]
          change restrictOn n (geoStrictTransform π C (univ : Set X))
            (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))=_
          rw [geoStrictTransform_univ hπ,restrictOn_univ hcP]
        have hC : M.IsAdmissibleCentre C := by
          refine ⟨hπ.1,?_,hTr.hasNormalCrossings⟩
          change C ⊆ cosupport n univ (vanishingIdeal (n := n) H) 0
          have hhol : ∀ z b,(vanishingIdeal (n := n) H).mem z b → HolomorphicAt n b z :=
            fun _ _ hh => hh.1
          rw [cosupport_zero hhol]
          exact subset_univ C
        have hprod : (fun w : X => ∏ i ∈ Finset.univ.filter
            (fun i : Fin [H].length => π y ∈ [H].get i),f w ^ (1 : ℕ))=f := by
          funext w
          simp only [hGet,hyH,Finset.filter_true,pow_one]
          change (∏ _ : Fin 1,f w)=f w
          exact Fin.prod_univ_one _
        have hgen : ∀ (_r : Unit) g,IsInSpanOnAt (n := n) univ
            ((vanishingIdeal (n := n) H).mem (π y)) (π y) g ↔
            IsInSpanOnAt (n := n) univ
              (·=fun w => ∏ i ∈ Finset.univ.filter
                (fun i : Fin [H].length => π y ∈ [H].get i),f w ^ (1 : ℕ)) (π y) g := by
          intro _r g
          rw [hprod]
          constructor
          · exact IsInSpanOnAt.trans fun a ha => IsInSpanAt.restrict ((hF a).mp ha)
          · exact IsInSpanOnAt.mono fun a ha => ha ▸ (hF f).mpr (isInSpanAt_self rfl hf)
        have hno := not_germ_contained_of_transverse hn hH hTr hyC hyH
        have hFilter : Finset.univ.filter
            (fun i : Fin [H].length => π y ∈ [H].get i ∧
              ∀ᶠ z in 𝓝 (π y),z ∈ C → z ∈ [H].get i)=∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro i _hi hcontains
          exact hno (by simpa only [hGet] using hcontains.2)
        obtain ⟨_k,_j,s,W,U,hU,hyU,_hWs,_hinj,_hjk,_hj0,_hD,hStrict,_hsinj,_hslt,_hNU,hWhole⟩ :=
          exists_common_monomial_chart hπ
            HomogenizedGlueingTower.isClosedSubmanifold_univ hH
            (isTransverse_univ_of_isSNCDivisor hH) (subset_univ C) hTr.hasNormalCrossings
            (fun _ : Unit => vanishingIdeal (n := n) H) (fun _ => 0) (fun _ => hcI)
            (fun _ => hC) (by rw [geoStrictTransform_univ hπ]; exact mem_univ y) hyC
            (fun _ _ => 1) (fun _ _ => f)
            (fun _ i _ => ⟨hf,by simpa only [hGet] using hF⟩) hgen
            (fun _ => Nat.zero_le _)
        have hWhole' (b : Y → ℂ) :
            (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)).mem y b ↔
              HolomorphicAt n b y ∧ IsInSpanOnAt (n := n) univ
                (·=fun w => ∏ i ∈ Finset.univ.filter
                  (fun i : Fin [H].length => y ∈ geoStrictTransform π C ([H].get i)),W w (s i)) y b := by
          have hh := hWhole () b
          change (M.geoTransform C π).ideal.mem y b ↔ _ at hh
          rw [hRaw] at hh
          simpa only [hFilter,Finset.sum_empty,Nat.sub_zero,pow_zero,one_mul,pow_one,
            geoStrictTransform_univ hπ] using hh
        have hyStrict : y ∈ geoStrictTransform π C H := by
          by_contra hyNot
          have hOne : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)).mem y (1 : Y → ℂ) := by
            apply (hWhole' 1).mpr
            refine ⟨holomorphicAt_const 1,?_⟩
            simp only [hGet,hyNot,Finset.filter_false,Finset.prod_empty]
            exact isInSpanOnAt_eq_iff.mpr
              ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩
          exact one_ne_zero ((pullback_vanishingIdeal_le hπ.contMDiff.continuous H y 1 hOne).2.self_of_nhds hyH)
        have hStrictDict : (vanishingIdeal (n := n) (geoStrictTransform π C H)).mem y g ↔
            IsInSpanAt (n := n) (·=fun w => W w (s (0 : Fin [H].length))) y g := by
          simpa only [hGet] using
            (hStrict (0 : Fin [H].length) (by simpa only [hGet] using hyStrict)).2.2.2 y hyU g
        have hStrictProd : (fun w : Y => ∏ i ∈ Finset.univ.filter
            (fun i : Fin [H].length => y ∈ geoStrictTransform π C ([H].get i)),W w (s i))=
            (fun w => W w (s (0 : Fin [H].length))) := by
          funext w
          simp only [hGet,hyStrict,Finset.filter_true]
          change (∏ i : Fin 1,W w (s i))=W w (s 0)
          exact Fin.prod_univ_one _
        apply (hWhole' g).mpr
        refine ⟨hg.1,?_⟩
        rw [hStrictProd]
        exact IsInSpanAt.restrict (hStrictDict.mp hg)
      · have hOneH : (vanishingIdeal (n := n) H).mem (π y) (1 : X → ℂ) := by
          refine ⟨holomorphicAt_const 1,?_⟩
          filter_upwards [hHsm.1.isOpen_compl.mem_nhds hyH] with z hz hzH
          exact (hz hzH).elim
        have hOne : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)).mem y (1 : Y → ℂ) :=
          GermIdeal.mem_pullback_iff.mpr
            (isInSpanAt_self ⟨(1 : X → ℂ),hOneH,rfl⟩ (holomorphicAt_const 1))
        apply HomogenizedIdeal.mem_of_isInSpanAt hcP
        exact isInSpanAt_of_eq_mul hOne hg.1 hg.1
          (Eventually.of_forall fun _ => by simp)
    · apply mem_pullback_vanishingIdeal_of_notMem hπ H hyC
      refine ⟨hg.1,?_⟩
      filter_upwards [hg.2,(hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hyC]
        with z hz hzC hzH
      exact hz ((mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hHsm.1 hzC).mpr hzH)

end

end Hironaka.HironakaG4TransverseBoundaryStrictPullback
