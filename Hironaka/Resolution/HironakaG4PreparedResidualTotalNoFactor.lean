import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary

set_option autoImplicit false

/-! Actual current prepared residuals acquire no factor along the ENTIRE next
born boundary on a genuine selected-stratum blowup. Complete source-first chapter:
hironaka-g4-prepared-residual-total-no-factor.tex. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4PreparedResidualTotalNoFactor

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings NormalCrossingsComparison
  HironakaG4PreparedCentreCoordinates HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpActualPrincipalOrderOneTrace
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualChronologicalNoOldFactor
  HironakaSharpActualChronologicalResidualDictionary HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  MonomialPartAlong DivisorExponentAlong GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal
  MemberInterAlong BoundaryCount

variable {n : ℕ} {X : CMfd.{u} n}

private theorem exists_actual_residual_generator (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (i : Fin old.length) {x : X} (hx : x ∈ N) :
    ∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,(oldResidualPart N old born i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g := by
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  obtain ⟨hcI,hnzI,hcJ,_hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hOld (List.get_mem old i) x
  have hI : ∀ g,(oldTraceIdeal N old i).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g :=
    fun g => and_congr_right fun _ =>
      HironakaSharpOriginalMemberProduct.restricted_span_iff_principal hf hF g
  obtain ⟨_m,c,_hm,_hmD,hcJmem,_hfc,hJ⟩ :=
    exists_actual_relative_principal_residual hn hN hBorn hTr hcI hnzI hx f hf hI
  exact ⟨c,GermIdeal.IsCoherent.holomorphicAt_mem hcJ hcJmem,hJ⟩

/-- Actual whole order-one residual coordinates provide a genuine residual
germ nonzero frequently on the literal selected born centre. -/
theorem exists_residual_nonzero_on_selected_born_centre (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : Finset (Fin born.length)) {x : X} (hx : x ∈ N ∩ memberInter born S)
    (hOrd : ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : IsPreparedResidualSNCAt N old born x) (i : Fin old.length) :
    ∃ c : X → ℂ,(oldResidualPart N old born i).mem x c ∧
      ∃ᶠ y in 𝓝 x,y ∈ N ∩ memberInter born S ∧ c y ≠ 0 := by
  obtain ⟨_hcI,_hnzI,hcJ,hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  obtain ⟨f,hf,hJ⟩ := exists_actual_residual_generator hn hN hE hTr hdense i hx.1
  have hfJ := (hJ f).mpr ⟨hf,isInSpanOnAt_eq_iff.mpr
    ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  by_cases hfx : f x=0
  · have hxJ : x ∈ N ∩ (oldResidualPart N old born i).zeroLocus := by
      refine ⟨hx.1,fun g hg => ?_⟩
      obtain ⟨a,_ha,hga⟩ := isInSpanOnAt_eq_iff.mp ((hJ g).mp hg).2
      simpa only [hfx,mul_zero] using hga.self_of_nhds hx.1
    have hOne : x ∈ cosupport n N (oldResidualPart N old born i) 1 :=
      (HironakaSharpActualRelativeProductOrder.cosupport_relative_principal_iff_vanishes
        hx.1 hf hJ 1).mpr
        ((vanishesToOrderOn_one_iff hx.1 hf).mpr hfx)
    have hOrder : ordinaryTraceOrder N (oldResidualPart N old born i) x=1 :=
      (hOrd i).antisymm ((ordinaryTraceOrder_cosupport_iff hN hcJ hnzJ hx.1 1).mp hOne)
    obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,_hreg⟩ :=
      actual_orderOne_relative_reduced_trace hN hcJ hnzJ hx.1 f hf hJ hOrder
    obtain ⟨S₀,p,⟨Φ,hsrc,h0,hflat⟩,hfree,hinj⟩ := hPrepared
    let q := p (Sum.inl i)
    have ha : x ∈ preparedSupport N old born (Sum.inl i) := hxJ
    have hqfree : q ∉ S₀ := hfree _ ha
    have hNflat := fun {y : X}
      (hy : y ∈ (complexChartAt (n := n) x).val.source)
      (hyΦ : (complexChartAt (n := n) x).val y ∈ Φ.source) => hflat none hx.1 hy hyΦ
    have hCoord : ∀ g,(oldResidualPart N old born i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N
          (·=BlowupFlatCoordinates.flatCoord Φ q) x g := by
      intro g
      exact (hRed g).trans (vanishingIdeal_coordinate_trace_mem_iff Φ S₀ q
        (hfree _ ha) hsrc h0 hNflat (hflat (some (Sum.inl i)) ha) g)
    have hrJ := (hCoord (BlowupFlatCoordinates.flatCoord Φ q)).mpr
      ⟨BlowupFlatCoordinates.holomorphicAt_flatCoord Φ q
        (BlowupFlatCoordinates.mem_flatDomain_self Φ),isInSpanOnAt_eq_iff.mpr
          ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
    refine ⟨BlowupFlatCoordinates.flatCoord Φ q,hrJ,?_⟩
    have hFreq := MonomialPart.frequently_flatMap_ne_zero hsrc
      (BlowupFlatCoordinates.mem_flatDomain_self Φ) ({q} : Finset (Fin n))
    refine hFreq.mono fun y ⟨hyD,hyne,hyeq⟩ => ?_
    have hZero (r : Fin n) (hr : r ≠ q) :
        Φ.toFun ((complexChartAt (n := n) x).val y) r=0 := by
      have he := hyeq r (by simpa only [Finset.mem_singleton] using hr)
      change Φ.toFun ((complexChartAt (n := n) x).val y) r=
        Φ.toFun ((complexChartAt (n := n) x).val x) r at he
      rw [he,h0]
      rfl
    have hyN : y ∈ N := (hNflat hyD.1 hyD.2).mpr fun r hr =>
      hZero r (fun he => hqfree (by simpa only [he,Option.elim] using hr))
    refine ⟨⟨hyN,?_⟩,hyne q (Finset.mem_singleton_self q)⟩
    intro j hj
    have hb : x ∈ preparedSupport N old born (Sum.inr j) := ⟨hx.1,hx.2 j hj⟩
    have hpq : p (Sum.inr j) ≠ q := by
      intro he
      have hh := hinj hb ha he
      cases hh
    have hyB : y ∈ preparedSupport N old born (Sum.inr j) := by
      apply (hflat (some (Sum.inr j)) hb hyD.1 hyD.2).mpr
      intro r hr
      rcases Finset.mem_union.mp hr with hr | hr
      · exact hZero r (fun he => hqfree (by simpa only [he] using hr))
      · rw [Finset.mem_singleton.mp hr]
        exact hZero _ hpq
    exact hyB.2
  · refine ⟨f,hfJ,?_⟩
    by_contra hnot
    rw [Filter.not_frequently] at hnot
    exact hnot.self_of_nhds ⟨hx,hfx⟩

private theorem total_outside_newborn_of_source_nonvanishing
    {N C : Set X} {I : GermIdeal n X} (hN : IsClosedSubmanifold n N)
    (hI : I.IsCoherent) {Y : CMfd.{u} n} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hSource : ∀ x ∈ C,∃ c : X → ℂ,I.mem x c ∧
      ∃ᶠ y in 𝓝 x,y ∈ C ∧ c y ≠ 0)
    {z : Y} (hz : z ∈ geoStrictTransform π C N) (hzC : π z ∈ C) :
    ∃ g : Y → ℂ,(nextTotalMarked N I C π).ideal.mem z g ∧
      ¬IsInSpanOnAt (n := n) (geoStrictTransform π C N)
        ((vanishingIdeal (n := n) (π ⁻¹' C)).mem z) z g := by
  by_contra hnot
  simp only [not_exists,not_and,not_not] at hnot
  obtain ⟨c,hc,hFreq⟩ := hSource (π z) hzC
  have hch := GermIdeal.IsCoherent.holomorphicAt_mem hI hc
  have hcp := hch.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  have hcP : (GermIdeal.pullback (m := n) π I).mem z (c ∘ π) :=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨c,hc,rfl⟩ hcp)
  have hRaw : (nextTotalMarked N I C π).ideal=
      restrictOn n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I) :=
    HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total
      (⟨N,[],I,0⟩ : MarkedIdeal n X) rfl C π
  have hcT : (nextTotalMarked N I C π).ideal.mem z (c ∘ π) := by
    rw [hRaw]
    exact le_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hI) z _ hcP
  have hSpan := hnot (c ∘ π) hcT
  have hExceptional : IsInSpanOnAt (n := n) (geoStrictTransform π C N)
      ((BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal.mem z) z (c ∘ π) :=
    IsInSpanOnAt.mono (fun s hs =>
      (MemberTraceIdealAlong.exceptionalDivisor_mem_iff_vanishingIdeal hπ hzC s).mpr hs) hSpan
  have hPower : IsInSpanOnAt (n := n) (geoStrictTransform π C N)
      ((IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 1).mem z)
      z (c ∘ π) := by
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ]
    exact hExceptional
  obtain ⟨r,s,a,hs,_ha,hSum⟩ :=
    ExceptionalPushforwardAlong.mem_idealPow_vanishingIdeal_along_of_pullback
      hπ hN hCN hzC hz hch hPower
  have hEach (j : Fin r) : ∀ᶠ y in 𝓝 (π z),y ∈ C → s j y=0 := by
    obtain ⟨_hhol,k,t,b,ht,_hb,hEq⟩ := hs j
    have hTerms (l : Fin k) : ∀ᶠ y in 𝓝 (π z),y ∈ C → t l y=0 := by
      obtain ⟨v,w,_hv,hw,hvw⟩ := ht l
      rw [hvw]
      filter_upwards [hw.2] with y hy hyC
      change v y*w y=0
      rw [hy hyC,mul_zero]
    filter_upwards [eventually_all.mpr hTerms,hEq] with y hy he hyC
    rw [he]
    exact Finset.sum_eq_zero fun l _ => by rw [hy l hyC,mul_zero]
  have hZero : ∀ᶠ y in 𝓝 (π z),y ∈ C → c y=0 := by
    filter_upwards [eventually_all.mpr hEach,hSum] with y hy he hyC
    rw [he (hCN hyC)]
    exact Finset.sum_eq_zero fun j _ => by rw [hy j hyC,mul_zero]
  obtain ⟨y,hy,hz⟩ := (hFreq.and_eventually hZero).exists
  exact hy.2 (hz hy.1)

/-- Genuine current prepared geometry gives true total-residual no-factor
germs along EVERY next born member on ANY actual selected-stratum blowup. -/
theorem prepared_residual_total_no_member_factor (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hOrd : ∀ x ∈ N ∩ memberInter born S,∀ i,
      ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N ∩ memberInter born S,IsPreparedResidualSNCAt N old born x) :
    let C := N ∩ memberInter born S
    IsClosedSubmanifold n C ∧ interior C = ∅ ∧
      ∀ {Y : CMfd.{u} n} (π : Y → X),IsBlowupAlong n C π →
      let N' := geoStrictTransform π C N
      let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
      ∀ i : Fin old.length,
        let T := (nextTotalMarked N (oldResidualPart N old born i) C π).ideal
        T.IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' T z) ∧
          (∀ z ∈ N',∀ j : Fin born'.length,z ∈ born'.get j →
            ∃ g : Y → ℂ,T.mem z g ∧
              ¬IsInSpanOnAt (n := n) N'
                ((vanishingIdeal (n := n) (born'.get j)).mem z) z g) ∧
          monomialPartAlong n N' T born' = IdealWeightPowers.unitIdeal n Y ∧
          nonmonomialPartAlong n N' T born' = T ∧
          nextRelativeStrict N (oldResidualPart N old born i) C π = T := by
  let C := N ∩ memberInter born S
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hC : IsClosedSubmanifold n C :=
    isClosedSubmanifold_inter_memberInter hn hN.1 hBorn hTr S
  have hCN : C ⊆ N := inter_subset_left
  have hCB : HasNormalCrossings n C born := hasNormalCrossings_inter_memberInter hTr S
  have hThin : interior C=∅ := by
    obtain ⟨j,hj⟩ := hS
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := interior_mono (show C ⊆ born.get j from fun y hy => hy.2 j hj) hx
    rw [MonomialCase.interior_get_eq_empty hn hBorn j] at hh
    exact hh
  refine ⟨hC,hThin,?_⟩
  intro Y π hπ
  dsimp only
  let N' := geoStrictTransform π C N
  let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  intro i
  let J := oldResidualPart N old born i
  let T := (nextTotalMarked N J C π).ideal
  obtain ⟨hcI,hnzI,hcJ,hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hcT : T.IsCoherent := isCoherent_geoTransform_ideal_without_inclusion
    (⟨N,[],J,0⟩ : MarkedIdeal n X) hN hcJ hπ hCN
  have hnzT : ∀ z ∈ N',IsNonzeroAlongAt N' T z :=
    isNonzeroAlongAt_geoTransform_without_admissibility
      (⟨N,[],J,0⟩ : MarkedIdeal n X) hN hcJ hπ hCN hnzJ
  obtain ⟨hBorn',hTr'⟩ := actual_accumulated_exceptional_geometry hN hcJ hBorn hTr hπ hCN hCB
  change IsSNCDivisor n born' at hBorn'
  change IsTransverse n N' born' at hTr'
  obtain ⟨_hcJ,_hcM,_hnzM,_hmM,hNoBorn,_hnzJ,_hFactor⟩ :=
    NonmonomialTransformAlong.parts_hypotheses hn
      (⟨N,born,oldTraceIdeal N old i,0⟩ : MarkedIdeal n X) ⟨hN,hcI,hBorn,hTr⟩ hnzI
  have hSource : ∀ x ∈ C,∃ c : X → ℂ,J.mem x c ∧
      ∃ᶠ y in 𝓝 x,y ∈ C ∧ c y ≠ 0 := by
    intro x hx
    exact exists_residual_nonzero_on_selected_born_centre hn hN hE hTr hdense S hx
      (hOrd x hx) (hPrepared x hx) i
  have hNoNew (z : Y) (hz : z ∈ N') (hzC : π z ∈ C) :
      ∃ g : Y → ℂ,T.mem z g ∧ ¬IsInSpanOnAt (n := n) N'
        ((vanishingIdeal (n := n) (π ⁻¹' C)).mem z) z g :=
    total_outside_newborn_of_source_nonvanishing hN hcJ hπ hCN hSource hz hzC
  have hNoAll : ∀ z ∈ N',∀ j : Fin born'.length,z ∈ born'.get j →
      ∃ g : Y → ℂ,T.mem z g ∧ ¬IsInSpanOnAt (n := n) N'
        ((vanishingIdeal (n := n) (born'.get j)).mem z) z g := by
    intro z hz j hzj
    have hget := BlowupSNCTransform.get_map_append_singleton born (geoStrictTransform π C)
      (π ⁻¹' C) j
    by_cases hj : j.val<born.length
    · rw [dif_pos hj] at hget
      rw [hget] at hzj ⊢
      exact nextTotal_old_strict_member_not_factor hN hBorn hTr hcJ hπ hCN hCB hNoBorn
        hz ⟨j.val,hj⟩ hzj
    · rw [dif_neg hj] at hget
      rw [hget] at hzj ⊢
      exact hNoNew z hz hzj
  have hNorm : restrictOn n N' T=T := by
    have hRaw : T=restrictOn n N' (GermIdeal.pullback (m := n) π J) :=
      HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total
        (⟨N,[],J,0⟩ : MarkedIdeal n X) rfl C π
    rw [hRaw]
    ext z g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  have hMono := monomialPartAlong_eq_unit_of_no_member_factor hBorn' hTr' hcT hNoAll
  have hNm := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hN' hBorn' hTr' hcT hNoAll
  have hNoSingle : ∀ z ∈ N',∀ j : Fin [π ⁻¹' C].length,z ∈ [π ⁻¹' C].get j →
      ∃ g : Y → ℂ,T.mem z g ∧ ¬IsInSpanOnAt (n := n) N'
        ((vanishingIdeal (n := n) ([π ⁻¹' C].get j)).mem z) z g := by
    intro z hz j hzj
    have hget : [π ⁻¹' C].get j=π ⁻¹' C := by
      simpa only [List.mem_singleton] using List.get_mem [π ⁻¹' C] j
    rw [hget] at hzj ⊢
    exact hNoNew z hz hzj
  have hSingleNm := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hN'
    (BlowupSNCTransform.isSNCDivisor_preimage_centre hπ)
    (BlowupSNCTransform.isTransverse_preimage_centre hπ hN hCN) hcT hNoSingle
  have hPr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,J.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g :=
    fun _ hx => exists_actual_residual_generator hn hN hE hTr hdense i hx
  have hStrict := (nextRelativeStrict_actual_geometry hn hN hcJ hnzJ hPr hπ hCN).1
  change nextRelativeStrict N J C π=nonmonomialPartAlong n N' T [π ⁻¹' C] at hStrict
  rw [hSingleNm,hNorm] at hStrict
  exact ⟨hcT,hnzT,hNoAll,hMono,hNm.trans hNorm,hStrict⟩

end
end Hironaka.HironakaG4PreparedResidualTotalNoFactor
