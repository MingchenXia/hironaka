import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates
import Hironaka.Resolution.HironakaG4ActiveMonomialSharpBad
import Hironaka.Resolution.HironakaSharpActualPrincipalSharedBranchDimension
import Hironaka.Analytic.PositiveDimensionalComponent

set_option autoImplicit false

/-! Actual lower-dimensional residual carriers and current-good avoidance.
Complete source-first chapter: hironaka-g4-residual-induction-inputs.tex.
First phase exit and subsequent history persistence remain separate. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4ResidualInductionInputs

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.RegularLocusDense BlowupTowers NormalCrossings NormalCrossingsComparison
  HironakaG4PreparedCentreCoordinates HironakaG4ActiveMonomialSharpBad
  HironakaSharpActualPrincipalOrderOneTrace HironakaSharpActualPrincipalSharedBranchDimension
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualRelativeProductOrder HironakaSharpActualTraceIncidence
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  MonomialPartAlong DivisorExponentAlong GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  AnalyticDimensionBasics PureDimension RegularPointDimension

variable {n : ℕ} {X : CMfd.{u} n}

/-- Delete exactly the chosen old position, retaining the order and every born member. -/
def remainingBoundary (old born : List (Set X)) (i : Fin old.length) : List (Set X) :=
  old.eraseIdx i.val ++ born

private theorem actual_residual_principal (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {x : X} (hx : x ∈ N) : ∃ c : X → ℂ,HolomorphicAt n c x ∧
      ∀ g,(oldResidualPart N old born i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g := by
  have hOld : IsSNCDivisor n old := isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  obtain ⟨hcI,hnzI,hcJ,_hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hOld (List.get_mem old i) x
  have hI : ∀ g,(oldTraceIdeal N old i).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g :=
    fun g => and_congr_right fun _ => HironakaSharpOriginalMemberProduct.restricted_span_iff_principal hf hF g
  obtain ⟨_m,c,_hm,_hmD,hcJmem,_hfc,hJ⟩ :=
    exists_actual_relative_principal_residual hn hN hBorn hTr hcI hnzI hx f hf hI
  exact ⟨c,GermIdeal.IsCoherent.holomorphicAt_mem hcJ hcJmem,hJ⟩

private theorem actual_old_trace_support_split (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {y : X} (hy : y ∈ N) : y ∈ old.get i ↔
      y ∈ (oldMonomialPart N old born i).zeroLocus ∨
      y ∈ (oldResidualPart N old born i).zeroLocus := by
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hOld i)
  obtain ⟨_hcI,_hnzI,hcJ,_hnzJ,hcD,_hnzD,_hmD,hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hIH : y ∈ (oldTraceIdeal N old i).zeroLocus ↔ y ∈ old.get i :=
    (zeroLocus_restrictOn_iff hcH hy).trans (by rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hOld i).1])
  have hProd : y ∈ (oldTraceIdeal N old i).zeroLocus ↔
      y ∈ ((oldMonomialPart N old born i).mul (oldResidualPart N old born i)).zeroLocus := by
    rw [hWhole]
    exact zeroLocus_restrictOn_iff (IdealWeightPowers.isCoherent_mul hcD hcJ) hy
  exact hIH.symm.trans (hProd.trans (by
    rw [HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hcD hcJ]; rfl))

/-- Actual order-one support geometry at the locally varying carrier
dimension. A boundary trace cannot meet a zero-dimensional component
because the original carrier is dense off the full boundary. -/
theorem actual_residual_support_local_geometry_of_row_order (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (i : Fin old.length)
    (hOrd : ∀ x ∈ N, ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1) :
    let Z := N ∩ (oldResidualPart N old born i).zeroLocus
    IsClosedSubmanifold n Z ∧ Z ⊆ old.get i ∧
      ∀ x ∈ Z,ordinaryTraceOrder N (oldResidualPart N old born i) x=1 ∧
        (∀ g,(oldResidualPart N old born i).mem x g ↔ (vanishingIdeal (n := n) Z).mem x g) ∧
        ∃ d,RegularAtDim (n := n) N x (d+1) ∧ RegularAtDim (n := n) Z x d := by
  let Z := N ∩ (oldResidualPart N old born i).zeroLocus
  obtain ⟨_hcI,_hnzI,hcJ,hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hPr := fun x (hx : x ∈ N) => actual_residual_principal hn hN hE hTr hdense i hx
  have hZsub : Z ⊆ old.get i := fun y hy =>
    (actual_old_trace_support_split hn hN hE hTr hdense i hy.1).mpr (Or.inr hy.2)
  have hPoint (x : X) (hx : x ∈ Z) :
      ordinaryTraceOrder N (oldResidualPart N old born i) x=1 ∧
      (∀ g,(oldResidualPart N old born i).mem x g ↔ (vanishingIdeal (n := n) Z).mem x g) ∧
      ∃ d,RegularAtDim (n := n) N x (d+1) ∧ RegularAtDim (n := n) Z x d := by
    obtain ⟨c,hc,hJ⟩ := hPr x hx.1
    have hcJmem := (hJ c).mpr ⟨hc,isInSpanOnAt_eq_iff.mpr
      ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
    have hc0 : c x=0 := hx.2 c hcJmem
    have hOne : x ∈ cosupport n N (oldResidualPart N old born i) 1 :=
      (cosupport_relative_principal_iff_vanishes hx.1 hc hJ 1).mpr
        ((vanishesToOrderOn_one_iff hx.1 hc).mpr hc0)
    have hOrder : ordinaryTraceOrder N (oldResidualPart N old born i) x=1 :=
      (hOrd x hx.1).antisymm ((ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx.1 1).mp hOne)
    obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,k,hNk,hZk⟩ :=
      actual_orderOne_relative_reduced_trace hN hcJ hnzJ hx.1 c hc hJ hOrder
    cases k with
    | zero =>
      obtain ⟨U,hU,hxU,hIso⟩ :=
        PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hNk
      obtain ⟨y,hy,hyU⟩ :=
        ((mem_closure_iff_frequently.mp (hdense hx.1)).and_eventually (hU.mem_nhds hxU)).exists
      have he : y = x := hIso ⟨hy.1,hyU⟩
      have hyOld : y ∈ old.get i := he.symm ▸ hZsub hx
      exact (hy.2 (mem_iUnion₂.mpr ⟨old.get i,List.mem_append_left _ (List.get_mem old i),hyOld⟩)).elim
    | succ d =>
      exact ⟨hOrder,hRed,d,hNk,by simpa only [Nat.succ_sub_one] using hZk⟩
  have hZclosed : IsClosed Z := hN.1.inter (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hcJ).isClosed
  refine ⟨⟨hZclosed,fun x hx => ?_⟩, hZsub, hPoint⟩
  obtain ⟨d,_,hZd⟩ := (hPoint x hx).2.2
  exact ⟨d,hZd⟩

theorem actual_residual_support_local_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ a,ordinaryTraceOrder N (oldResidualPart N old born a) x ≤ 1)
    (i : Fin old.length) :
    let Z := N ∩ (oldResidualPart N old born i).zeroLocus
    IsClosedSubmanifold n Z ∧ Z ⊆ old.get i ∧
      ∀ x ∈ Z,ordinaryTraceOrder N (oldResidualPart N old born i) x=1 ∧
        (∀ g,(oldResidualPart N old born i).mem x g ↔ (vanishingIdeal (n := n) Z).mem x g) ∧
        ∃ d,RegularAtDim (n := n) N x (d+1) ∧ RegularAtDim (n := n) Z x d :=
  actual_residual_support_local_geometry_of_row_order hn hN hE hTr hdense i
    (fun x hx => hOrd x hx i)


/-- Actual order-one residuals give genuine closed smooth lower-dimensional
carriers and the entire reduced whole-ideal dictionary, internally. -/
theorem actual_residual_support_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (d : ℕ)
    (hReg : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1))
    (hOrd : ∀ x ∈ N,∀ a,ordinaryTraceOrder N (oldResidualPart N old born a) x ≤ 1)
    (i : Fin old.length) :
    let Z := N ∩ (oldResidualPart N old born i).zeroLocus
    IsClosedSubmanifold n Z ∧ (∀ x ∈ Z,RegularAtDim (n := n) Z x d) ∧ Z ⊆ old.get i ∧
      ∀ x ∈ Z,ordinaryTraceOrder N (oldResidualPart N old born i) x=1 ∧
        ∀ g,(oldResidualPart N old born i).mem x g ↔ (vanishingIdeal (n := n) Z).mem x g := by
  obtain ⟨hZ, hOwn, hPoint⟩ := actual_residual_support_local_geometry hn hN hE hTr hdense hOrd i
  refine ⟨hZ, ?_, hOwn, fun x hx => ⟨(hPoint x hx).1,(hPoint x hx).2.1⟩⟩
  intro x hx
  obtain ⟨e,hNe,hZe⟩ := (hPoint x hx).2.2
  have he : e = d := Nat.add_right_cancel (eq_of_regularAtDim hNe (hReg x hx.1))
  exact he ▸ hZe

private theorem actual_orderOne_germ_eq_of_support_containment {N : Set X}
    (hN : IsClosedSubmanifold n N) {I J : GermIdeal n X} (hcI : I.IsCoherent) (hcJ : J.IsCoherent)
    (hnzI : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hnzJ : ∀ y ∈ N,IsNonzeroAlongAt N J y)
    {x : X} (hx : x ∈ N) (d : ℕ) (hReg : RegularAtDim (n := n) N x (d+1))
    (hPrI : ∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,I.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hPrJ : ∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,J.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hOrdI : ordinaryTraceOrder N I x=1) (hOrdJ : ordinaryTraceOrder N J x=1)
    (hcont : ∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus → y ∈ J.zeroLocus) :
    ∀ g,I.mem x g ↔ J.mem x g := by
  obtain ⟨f,hf,hF⟩ := hPrI
  obtain ⟨g,hg,hG⟩ := hPrJ
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,_hRed,k,hNk,hZk⟩ :=
    actual_orderOne_relative_reduced_trace hN hcI hnzI hx f hf hF hOrdI
  have hk : k=d+1 := eq_of_regularAtDim hNk hReg
  rw [hk,Nat.add_sub_cancel] at hZk
  have hs : ∀ᶠ y in 𝓝 x,y ∈ N ∩ I.zeroLocus ∩ J.zeroLocus ↔ y ∈ N ∩ I.zeroLocus := by
    filter_upwards [hcont] with y hy
    exact ⟨fun hh => hh.1,fun hh => ⟨hh,hy hh⟩⟩
  have hDim : LocDimGE (n := n) (N ∩ I.zeroLocus ∩ J.zeroLocus) x d :=
    locDimGE_of_regularAtDim (CodimOneSupport.regularAtDim_of_eventually_mem_iff
      (hs.mono fun _ hh => hh.symm) hZk)
  exact actual_orderOne_germ_eq_of_pair_locDimGE hN hcI hcJ hnzI hnzJ hx hReg
    f g hf hg hF hG hOrdI hOrdJ hDim

private theorem residual_support_not_germ_contained_in_born (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ a,ordinaryTraceOrder N (oldResidualPart N old born a) x ≤ 1)
    (i : Fin old.length) (j : Fin born.length) {x : X}
    (hx : x ∈ N ∩ (oldResidualPart N old born i).zeroLocus) :
    ¬∀ᶠ y in 𝓝 x,y ∈ N ∩ (oldResidualPart N old born i).zeroLocus → y ∈ born.get j := by
  intro hcont
  have hxB := hcont.self_of_nhds hx
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hB : IsSNCDivisor n [born.get j] := isSNCDivisor_of_sublist hBorn (by simp)
  have hTB : IsTransverse n N [born.get j] := isTransverse_of_forall_mem hTr (by simp)
  obtain ⟨hcA,hnzA,hPrA,hOrdA⟩ :=
    HironakaSharpActualFirstAmbientStrictExponent.actual_normalized_transverse_member_geometry hn hN hB hTB
  obtain ⟨hcI,hnzI,hcJ,hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hcB := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hBorn j)
  have hcontA : ∀ᶠ y in 𝓝 x,y ∈ N ∩ (oldResidualPart N old born i).zeroLocus →
      y ∈ (restrictOn n N (vanishingIdeal (n := n) (born.get j))).zeroLocus := by
    filter_upwards [hcont] with y hy hyZ
    apply (zeroLocus_restrictOn_iff hcB hyZ.1).mpr
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hBorn j).1]
    exact hy hyZ
  have hGeom := actual_residual_support_local_geometry hn hN hE hTr hdense hOrd i
  obtain ⟨hOrder,_,d,hReg,_⟩ := hGeom.2.2 x hx
  have hEq := actual_orderOne_germ_eq_of_support_containment hN hcJ hcA hnzJ hnzA hx.1 d
    hReg (actual_residual_principal hn hN hE hTr hdense i hx.1) (hPrA x hx.1)
    hOrder (hOrdA x ⟨hx.1,hxB⟩) hcontA
  obtain ⟨_hcJ,_hcD,_hnzD,_hmD,hNo,_hnzJ,_hFactor⟩ := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨N,born,oldTraceIdeal N old i,0⟩ : MarkedIdeal n X) ⟨hN,hcI,hBorn,hTr⟩ hnzI
  obtain ⟨a,ha,hnot⟩ := hNo x hx.1 j hxB
  exact hnot (((hEq a).mp ha).2)

private theorem residual_support_not_germ_contained_in_other (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ a,ordinaryTraceOrder N (oldResidualPart N old born a) x ≤ 1)
    (hDistinct : ∀ x ∈ N,∀ a b : Fin old.length,a ≠ b →
      ¬(oldResidualPart N old born a).mem x 1 → ¬(oldResidualPart N old born b).mem x 1 →
      ¬∀ g,(oldResidualPart N old born a).mem x g ↔ (oldResidualPart N old born b).mem x g)
    (i j : Fin old.length) (hij : i ≠ j) {x : X}
    (hx : x ∈ N ∩ (oldResidualPart N old born i).zeroLocus) :
    ¬∀ᶠ y in 𝓝 x,y ∈ N ∩ (oldResidualPart N old born i).zeroLocus →
      y ∈ N ∩ (oldResidualPart N old born j).zeroLocus := by
  intro hcont
  have hxJ := hcont.self_of_nhds hx
  obtain ⟨_hcIi,_hnzIi,hci,hnzi,_hcDi,_hnzDi,_hmDi,_hWholei⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  obtain ⟨_hcIj,_hnzIj,hcj,hnzj,_hcDj,_hnzDj,_hmDj,_hWholej⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense j
  have hGeomI := actual_residual_support_local_geometry hn hN hE hTr hdense hOrd i
  have hGeomJ := actual_residual_support_local_geometry hn hN hE hTr hdense hOrd j
  obtain ⟨hOrderI,_,d,hReg,_⟩ := hGeomI.2.2 x hx
  have hEq := actual_orderOne_germ_eq_of_support_containment hN hci hcj hnzi hnzj hx.1 d
    hReg (actual_residual_principal hn hN hE hTr hdense i hx.1)
    (actual_residual_principal hn hN hE hTr hdense j hx.1)
    hOrderI (hGeomJ.2.2 x hxJ).1
    (hcont.mono fun _ hy hyI => (hy hyI).2)
  exact hDistinct x hx.1 i j hij
    (fun hu => one_ne_zero (hx.2 1 hu)) (fun hu => one_ne_zero (hxJ.2 1 hu)) hEq

private theorem dense_diff_closed_list_of_no_germ_containment {Z : Set X} (L : List (Set X)) :
    (∀ H ∈ L,IsClosed H) →
    (∀ x ∈ Z,∀ H ∈ L,¬∀ᶠ y in 𝓝 x,y ∈ Z → y ∈ H) →
    Z ⊆ closure (Z \ ⋃ H ∈ L,H) := by
  induction L with
  | nil =>
    intro _hClosed _hNo x hx
    simpa using (subset_closure hx : x ∈ closure Z)
  | cons H L ih =>
    intro hClosed hNo x hx
    have hDenseTail := ih (fun K hK => hClosed K (List.mem_cons_of_mem _ hK))
      (fun y hy K hK => hNo y hy K (List.mem_cons_of_mem _ hK))
    apply mem_closure_iff_frequently.mpr
    apply frequently_iff.mpr
    intro U hU
    obtain ⟨V,hVU,hVo,hxV⟩ := mem_nhds_iff.mp hU
    have hFreq : ∃ᶠ y in 𝓝 x,y ∈ Z ∧ y ∉ H := by
      by_contra hnot
      apply hNo x hx H List.mem_cons_self
      filter_upwards [not_frequently.mp hnot] with y hy hyZ
      by_contra hyH
      exact hy ⟨hyZ,hyH⟩
    obtain ⟨z,⟨hzZ,hzH⟩,hzV⟩ := (hFreq.and_eventually (hVo.mem_nhds hxV)).exists
    have hFreqTail := mem_closure_iff_frequently.mp (hDenseTail hzZ)
    have hWindow : ∀ᶠ y in 𝓝 z,y ∈ V ∧ y ∉ H := by
      filter_upwards [hVo.mem_nhds hzV,(hClosed H List.mem_cons_self).isOpen_compl.mem_nhds hzH]
        with y hyV hyH
      exact ⟨hyV,hyH⟩
    obtain ⟨w,⟨hwZ,hwL⟩,hwV,hwH⟩ := (hFreqTail.and_eventually hWindow).exists
    refine ⟨w,hVU hwV,hwZ,?_⟩
    intro hwUnion
    obtain ⟨K,hK,hwK⟩ := mem_iUnion₂.mp hwUnion
    rcases List.mem_cons.mp hK with rfl | hKL
    · exact hwH hwK
    · exact hwL (mem_iUnion₂.mpr ⟨K,hKL,hwK⟩)

/-- Distinct actual proper whole residual germs construct density of the real
lower-dimensional carrier off every remaining original old and born member. -/
theorem residual_support_dense_off_remainingBoundary_of_local_dimension (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ a,ordinaryTraceOrder N (oldResidualPart N old born a) x ≤ 1)
    (hDistinct : ∀ x ∈ N,∀ a b : Fin old.length,a ≠ b →
      ¬(oldResidualPart N old born a).mem x 1 → ¬(oldResidualPart N old born b).mem x 1 →
      ¬∀ g,(oldResidualPart N old born a).mem x g ↔ (oldResidualPart N old born b).mem x g)
    (i : Fin old.length) :
    let Z := N ∩ (oldResidualPart N old born i).zeroLocus
    Z ⊆ closure (Z \ ⋃ H ∈ remainingBoundary old born i,H) := by
  classical
  let Z := N ∩ (oldResidualPart N old born i).zeroLocus
  let R : Fin old.length → Set X := fun j =>
    if j=i then ∅ else N ∩ (oldResidualPart N old born j).zeroLocus
  let L := List.ofFn R ++ born
  have hClosed : ∀ H ∈ L,IsClosed H := by
    intro H hH
    rcases List.mem_append.mp hH with hR | hB
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hR
      by_cases hji : j=i
      · simpa only [R,if_pos hji] using (isClosed_empty : IsClosed (∅ : Set X))
      · simpa only [R,if_neg hji] using
          (actual_residual_support_local_geometry hn hN hE hTr hdense hOrd j).1.1
    · exact hE.1 H (List.mem_append_right old hB)
  have hNo : ∀ x ∈ Z,∀ H ∈ L,¬∀ᶠ y in 𝓝 x,y ∈ Z → y ∈ H := by
    intro x hx H hH
    rcases List.mem_append.mp hH with hR | hB
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hR
      by_cases hji : j=i
      · simp only [R,if_pos hji]
        exact fun hh => hh.self_of_nhds hx
      · simpa only [R,if_neg hji] using
          residual_support_not_germ_contained_in_other hn hN hE hTr hdense hOrd hDistinct
            i j (Ne.symm hji) hx
    · obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hB
      exact residual_support_not_germ_contained_in_born hn hN hE hTr hdense hOrd i j hx
  have hDense := dense_diff_closed_list_of_no_germ_containment L hClosed hNo
  refine hDense.trans (closure_mono ?_)
  intro y hy
  refine ⟨hy.1,?_⟩
  intro hyBoundary
  obtain ⟨H,hH,hyH⟩ := mem_iUnion₂.mp hyBoundary
  rcases List.mem_append.mp hH with hOld | hBorn
  · obtain ⟨k,hk,hki,hget⟩ := List.mem_eraseIdx_iff_getElem.mp hOld
    let j : Fin old.length := ⟨k,hk⟩
    have hji : j ≠ i := fun hh => hki (congrArg Fin.val hh)
    have hget' : old.get j=H := hget
    have hyOld : y ∈ old.get j := by rw [hget']; exact hyH
    have hDunit : (oldMonomialPart N old born j).mem y 1 := by
      apply (one_mem_monomialPartAlong_iff (oldTraceIdeal N old j) born hy.1.1).mpr
      intro a hya
      exact False.elim (hy.2 (mem_iUnion₂.mpr
        ⟨born.get a,List.mem_append_right (List.ofFn R) (List.get_mem born a),hya⟩))
    rcases (actual_old_trace_support_split hn hN hE hTr hdense j hy.1.1).mp hyOld with hyD | hyJ
    · exact one_ne_zero (hyD 1 hDunit)
    · have hyR : y ∈ R j := by
        simp only [R,if_neg hji]
        exact ⟨hy.1.1,hyJ⟩
      exact hy.2 (mem_iUnion₂.mpr
        ⟨R j,List.mem_append_left born (List.mem_ofFn.mpr ⟨j,rfl⟩),hyR⟩)
  · exact hy.2 (mem_iUnion₂.mpr ⟨H,List.mem_append_right (List.ofFn R) hBorn,hyH⟩)

set_option linter.unusedVariables false in
/-- The pure-dimensional entry follows from the same local-dimension
density argument. -/
theorem residual_support_dense_off_remainingBoundary (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (d : ℕ)
    (hReg : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1))
    (hOrd : ∀ x ∈ N,∀ a,ordinaryTraceOrder N (oldResidualPart N old born a) x ≤ 1)
    (hDistinct : ∀ x ∈ N,∀ a b : Fin old.length,a ≠ b →
      ¬(oldResidualPart N old born a).mem x 1 → ¬(oldResidualPart N old born b).mem x 1 →
      ¬∀ g,(oldResidualPart N old born a).mem x g ↔ (oldResidualPart N old born b).mem x g)
    (i : Fin old.length) :
    let Z := N ∩ (oldResidualPart N old born i).zeroLocus
    Z ⊆ closure (Z \ ⋃ H ∈ remainingBoundary old born i,H) :=
  residual_support_dense_off_remainingBoundary_of_local_dimension hn hN hE hTr hdense hOrd hDistinct i

private theorem residual_support_germ_eq_old_trace_at_normalCrossings (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {x : X} (hx : x ∈ N) (hNC : normalCrossingsAt (n := n) N (old ++ born) x) :
    ∀ᶠ y in 𝓝 x,y ∈ N ∩ (oldResidualPart N old born i).zeroLocus ↔ y ∈ N ∩ old.get i := by
  let a : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append]; omega⟩
  have ha : (old ++ born).get a=old.get i := by
    simp only [List.get_eq_getElem,a,List.getElem_append_left i.isLt]
  have hDunit : (oldMonomialPart N old born i).mem x 1 := by
    apply (one_mem_monomialPartAlong_iff (oldTraceIdeal N old i) born hx).mpr
    intro j hxj
    let b : Fin (old ++ born).length :=
      ⟨old.length+j.val,by simp only [List.length_append]; omega⟩
    have hb : (old ++ born).get b=born.get j := by
      simp only [List.get_eq_getElem,b,List.getElem_append_right (by omega : old.length ≤ old.length+j.val),
        Nat.add_sub_cancel_left]
    have hab : a ≠ b := by
      intro h
      have hh := congrArg Fin.val h
      change i.val=old.length+j.val at hh
      omega
    have he := divExpAlong_restricted_member_eq_zero_at_normalCrossings
      hn hN hE hdense hx hNC a b hab (by rw [hb]; exact hxj)
    simpa only [ha,hb,oldTraceIdeal] using he
  obtain ⟨_hcI,_hnzI,_hcJ,_hnzJ,hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  filter_upwards [HadamardBridge.eventually_mem_of_isCoherent hcD hDunit] with y hy
  constructor
  · intro hyZ
    exact ⟨hyZ.1,(actual_old_trace_support_split hn hN hE hTr hdense i hyZ.1).mpr (Or.inr hyZ.2)⟩
  · intro hyH
    refine ⟨hyH.1,?_⟩
    rcases (actual_old_trace_support_split hn hN hE hTr hdense i hyH.1).mp hyH.2 with hyD | hyJ
    · exact False.elim (one_ne_zero (hyD 1 hy))
    · exact hyJ

private theorem normalCrossingsAt_residual_support_of_original (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {x : X} (hx : x ∈ N ∩ (oldResidualPart N old born i).zeroLocus)
    (hNC : normalCrossingsAt (n := n) N (old ++ born) x) :
    normalCrossingsAt (n := n) (N ∩ (oldResidualPart N old born i).zeroLocus)
      (remainingBoundary old born i) x := by
  classical
  let a : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append]; omega⟩
  have ha : (old ++ born).get a=old.get i := by
    simp only [List.get_eq_getElem,a,List.getElem_append_left i.isLt]
  have hxa : x ∈ (old ++ born).get a := by
    rw [ha]
    exact (actual_old_trace_support_split hn hN hE hTr hdense i hx.1).mpr (Or.inr hx.2)
  have hGerm := residual_support_germ_eq_old_trace_at_normalCrossings hn hN hE hTr hdense i hx.1 hNC
  obtain ⟨S₀,T,⟨Φ,hsrc,h0,hflat⟩,hcard⟩ := hNC
  have hFamily : IsCoordinateFamilyAt n
      (fun o : Option (Fin (old ++ born).length) => o.elim (N ∩ old.get i) ((old ++ born).get))
      (fun o => o.elim (S₀ ∪ T a) T) x := by
    refine ⟨Φ,hsrc,h0,?_⟩
    rintro (_ | k) hxi y hy hyΦ
    · change (y ∈ N ∧ y ∈ old.get i) ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S₀ ∪ T a)
      have hunion : ∀ w : ComplexModel n,w ∈ coordSubspace (S₀ ∪ T a) ↔
          w ∈ coordSubspace S₀ ∧ w ∈ coordSubspace (T a) := fun w => by
        simp only [coordSubspace,Finset.mem_union,mem_ofPred_eq]
        exact ⟨fun h => ⟨fun j hj => h j (Or.inl hj),fun j hj => h j (Or.inr hj)⟩,
          fun h j hj => hj.elim (h.1 j) (h.2 j)⟩
      rw [hunion]
      have hA : y ∈ (old ++ born).get a ↔
          Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (T a) :=
        hflat (some a) hxa hy hyΦ
      rw [ha] at hA
      exact and_congr (hflat none hx.1 hy hyΦ) hA
    · exact hflat (some k) hxi hy hyΦ
  have hResidualFamily : IsCoordinateFamilyAt n
      (fun o : Option (Fin (old ++ born).length) =>
        o.elim (N ∩ (oldResidualPart N old born i).zeroLocus) ((old ++ born).get))
      (fun o => o.elim (S₀ ∪ T a) T) x := by
    apply CodimOneAdmissibleAlong.isCoordinateFamilyAt_congr _ hFamily
    filter_upwards [hGerm] with y hy
    rintro (_ | k)
    · exact hy
    · exact Iff.rfl
  have hRemaining : ∀ H ∈ remainingBoundary old born i,H ∈ old ++ born := by
    intro H hH
    rcases List.mem_append.mp hH with hOld | hBorn
    · exact List.mem_append_left born (List.eraseIdx_subset hOld)
    · exact List.mem_append_right old hBorn
  have hIndex : ∀ k : Fin (remainingBoundary old born i).length,
      ∃ j : Fin (old ++ born).length,(old ++ born).get j=(remainingBoundary old born i).get k :=
    fun k => List.mem_iff_get.mp (hRemaining _ (List.get_mem _ k))
  choose index hIndex using hIndex
  refine ⟨S₀ ∪ T a,fun k => T (index k),?_,?_⟩
  · refine NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hResidualFamily
      (Option.map index) ?_ ?_
    · rintro (_ | k)
      · rfl
      · exact (hIndex k).symm
    · rintro (_ | k) <;> rfl
  · intro k hk
    exact hcard (index k) (by rw [hIndex]; exact hk)

/-- The literal sharp bad locus of the current actual residual carrier lies
inside the literal original sharp bad locus, with every other boundary position retained. -/
theorem originalSharpBadLocus_residual_subset (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length) :
    originalSharpBadLocus (n := n) (N ∩ (oldResidualPart N old born i).zeroLocus)
      (remainingBoundary old born i) ⊆ originalSharpBadLocus (n := n) N (old ++ born) := by
  intro x hx
  exact ⟨hx.1.1,fun hNC => hx.2
    (normalCrossingsAt_residual_support_of_original hn hN hE hTr hdense i hx.1 hNC)⟩

end

end Hironaka.HironakaG4ResidualInductionInputs


/-! Append-only public interface for the existing private relative-principality
proof. Every previous byte is retained; this export receives zero producer credit. -/
namespace Hironaka.HironakaG4ResidualInductionInputs

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings HironakaG4PreparedCentreCoordinates
  RelativePrincipalizationSpan RestrictedIdealExtension

variable {n : ℕ} {X : CMfd.{u} n}

theorem actual_residual_principal_native (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) (i : Fin old.length)
    {x : X} (hx : x ∈ N) : ∃ c : X → ℂ, HolomorphicAt n c x ∧
      ∀ g, (oldResidualPart N old born i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = c) x g :=
  actual_residual_principal hn hN hE hTr hdense i hx

end Hironaka.HironakaG4ResidualInductionInputs
