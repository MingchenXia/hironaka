import Hironaka.Resolution.HironakaG1LocalizedLaterBornCanonical
import Hironaka.Resolution.HironakaG1LaterSelectedNormalOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaG1LocalizedBornNormalOrder
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec NormalCrossings HomogenizedIdealAlong
  TangentDirectionAlong DerivativeIdealAlong DerivativeIdealAlongCoherent DerivativeIdealAlongEtale
  RelativePrincipalizationSpan InvertibleIdealQuotient IdealWeightPowers
  DivisorExponentAlong DivisorExponent CoefficientIdeal
  CompanionReductionAlong CompanionRebase NonmonomialOrderLocal MonomialPartAlong
  HironakaG1LaterSelectedNormalTangent HironakaG1LaterSelectedNormalOrder HironakaG1LaterContactFieldExistence
  HironakaG1LocalizedLaterBornCanonical HironakaG8LocalHistory HironakaG1RecursiveMemberValueTransport
  HironakaG8HomStable HironakaG8MixedBoundaryExponents MarkedIdealOperationsAlong StepOneValue StepOneValueMasked BoundaryCount InvDomainRebase InvDomainMemberRestriction
  HironakaMonomialBlowup HironakaG1ProperNormalInitialRegime NonmonomialOrderTail InvDomainTowerAlong
  RestrictLeCalculus MarkedIdealOperationsAlong.MarkedIdeal
  RestrictedIdealExtension GiraudAlong GermIdealOrder HomogenizedGlueingLiftAlong ContactEquivalenceAlong

private theorem born_bar_tangent {n k : ℕ} {X : CMfd.{0} n}
    (J : MarkedIdeal n X) (hJ : IsInvDomain k J) (W : Opens X) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hField : ∀ x ∈ W, ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField J.N e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) :
    IsTangentDirectionAlong (barMarked J).N (barMarked J).ideal (barMarked J).d W u := by
  let A := homMarkedAlong J
  have hA : A.IsWellFormed := ⟨hJ.isWellFormed.isClosedSubmanifold_N,
    isCoherent_homMarkedAlong hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N,
    hJ.isWellFormed.isSNCDivisor, hJ.isWellFormed.isTransverse⟩
  have hAu : IsTangentDirectionAlong A.N A.ideal A.d W u := by
    refine ⟨W.isOpen, fun x _ => ?_, fun x _ => hu.multiplicity_one x (mem_univ x)⟩
    exact iterDerivIdealAlong_mono (N := J.N)
      (le_homogenizedIdealAlong (fun _ _ hf =>
        GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hf) hJ.one_le_d)
      (J.d - 1) x u (hu.mem x (mem_univ x))
  have hEmpty : (memberRestrict A ∅).N = J.N := by
    rw [memberRestrict_N]
    change J.N ∩ memberInter A.E ∅ = J.N
    simp [memberInter]
  have hB := selected_tangent_of_current_contact A hA hJ.one_le_d ∅ W u hAu
    (fun x hx => by rw [hEmpty]; exact hField x hx)
  change IsTangentDirectionAlong (memberRestrict A ∅).N (barMarked J).ideal (barMarked J).d W u at hB
  rwa [hEmpty] at hB

private theorem true_normal_power_in_member {n : ℕ} {X : CMfd.{0} n}
    (B : MarkedIdeal n X) (hB : B.IsWellFormed) (hd : 0 < B.d)
    (I : Finset (Fin B.E.length)) (W : Opens X) (u : X → ℂ)
    (hu : IsTangentDirectionAlong B.N B.ideal B.d W u) {x : X} (hx : x ∈ W) :
    let K := memberRestrict B I
    HolomorphicAt n u x ∧ K.ideal.mem x (fun z => u z ^ K.d) := by
  let K := memberRestrict B I
  let i := B.d - 1
  let a := sumExp (fun j => B.d - j) B.d i
  have hMem := hu.mem x hx
  have hHol := holomorphicAt_of_mem_iterDerivIdealAlong
    (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hf) i x u hMem
  have hi : i < B.d := by dsimp [i]; omega
  have hOne : B.d - i = 1 := by dsimp [i]; omega
  have hMark : K.d = a := by
    change (Finset.range B.d).prod (fun j => B.d - j) = a
    simpa only [hOne, one_mul] using (mul_sumExp (fun j => B.d - j) hi).symm
  refine ⟨hHol, ?_⟩
  change IsInSpanAt (n := n) (fun f => ∃ j, j < B.d ∧
    (idealPow (iterDerivIdealAlong B.N B.ideal j) (sumExp (fun m => B.d - m) B.d j)).mem x f) x _
  rw [hMark]
  exact isInSpanAt_self ⟨i, hi, HomogenizedIdeal.pow_mem_idealPow hMem hHol a⟩
    (CompanionReduction.holomorphicAt_pow_of hHol a)

private theorem tangent_true_order_bound {n k : ℕ} {X : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain k K) {u : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u) :
    IsMaximalOrderAlong K.N K.ideal K.d := by
  intro x hx
  let i := K.d - 1
  have hi : 1 + i = K.d := by dsimp [i]; have := hK.one_le_d; omega
  have hHol : ∀ y f, K.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hf
  have hMem := hu.mem x (mem_univ x)
  have huH := holomorphicAt_of_mem_iterDerivIdealAlong hHol i x u hMem
  have hx1 := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 i
    (by rw [hi]; exact cosupport_anti (Nat.le_succ K.d) hx)
  have hu0 := (vanishesToOrderOn_one_iff hx1.1 huH).mp (hx1.2 _ hMem)
  obtain ⟨e, ξ, hξ, hD⟩ := hu.multiplicity_one x (mem_univ x) hu0
  have hGen : DerivGenAlong K.N (iterDerivIdealAlong K.N K.ideal i) x (fieldDeriv e ξ u) :=
    Or.inr (Or.inr ⟨e, ξ, u, hξ, hMem, rfl⟩)
  have hDH := holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt huH
  have hDMem : (iterDerivIdealAlong K.N K.ideal (i + 1)).mem x (fieldDeriv e ξ u) :=
    isInSpanAt_self hGen hDH
  have hNum : 1 + (i + 1) = K.d + 1 := by omega
  have hx2 := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 (i + 1)
    (by rw [hNum]; exact hx)
  exact hD ((vanishesToOrderOn_one_iff hx2.1 hDH).mp (hx2.2 _ hDMem))

set_option maxHeartbeats 1800000 in
/-- On a subwindow of a specified actual next-born mask the retained exponents vanish.
The incoming normal contributes its full power at the true mark of the
selected record, and its true-mark companion is the carrier restriction. -/
theorem exists_localized_born_normal_order_subwindow {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (a : X) (ha : a ∈ R.N) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {z | u z = 0} = R.N)
    (V : Opens X) (haV : a ∈ V)
    (hKV : IsInvDomain (k - 1) (positiveMemberOn J (.refl : BlowupTower X X) a V)) :
    let I : BlowupTower X X := .refl
    ∃ W : Opens X, a ∈ W ∧ W ≤ V ∧
      let A := CMfd.of (n := n) W
      let K := positiveMemberOn J I a W
      IsInvDomain (k - 1) K ∧ IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ Subtype.val) ∧
      (∀ z : W, K.ideal.mem z (fun w => u w.val ^ K.d)) ∧
      (∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0) ∧
      (∀ z ∈ K.cosupp, nmOrd (M := A) K z = K.d) ∧
      companionOf n (M := A) K K.d =
        (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n A) := by
  classical
  intro H
  let B := barMarked J
  let I := membersThrough B.E (origMembers J H) a
  let K₀ := memberRestrict B I
  have hB := HironakaCoherentTransformExtension.isInvDomain_barMarked J hJ
  have hK₀ : K₀.IsWellFormed := isWellFormed_memberRestrict hn hB.isWellFormed I
  have hRJ : R.N ⊆ J.N := fun z hz => (hTrace ▸ hz).1
  have hTD : IsTransverse n R.N B.E := by
    change IsTransverse n R.N J.E
    rw [hClass.wEquiv.1]
    exact hR.isWellFormed.isTransverse
  have ha0 := (hTrace ▸ ha).2
  obtain ⟨e, ξ, hξ, hDetect⟩ := hu.multiplicity_one a (mem_univ a) ha0
  have huV : (vanishingIdeal (n := n) R.N).mem a u :=
    ⟨holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hf)
      (J.d - 1) a u (hu.mem a (mem_univ a)),
      Eventually.of_forall fun _ hz => (hTrace ▸ hz).2⟩
  have hField (L : Finset (Fin B.E.length)) (hL : ∀ i ∈ L, a ∈ B.E.get i) :=
    exists_normalized_tangent_field_of_transverse_boundary hn B.E L hB.isWellFormed.isSNCDivisor
      hB.isWellFormed.isTransverse hTD hL ha hRJ huV hξ hDetect
  have hEmpty : B.N ∩ memberInter B.E ∅ = J.N := by change J.N ∩ memberInter B.E ∅ = J.N; simp [memberInter]
  have hI (i) (hi : i ∈ I) : a ∈ B.E.get i := (mem_membersThrough.mp hi).2
  have hBase := hField ∅ (by simp)
  rw [hEmpty] at hBase
  have hSlots (i : Fin B.E.length) :
      ∀ᶠ x in 𝓝 a, x ∈ B.E.get i →
        ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
          IsTangentField (K₀.N ∩ B.E.get i) e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1 := by
    by_cases hi : a ∈ B.E.get i
    · have hInsert (j) (hj : j ∈ insert i I) : a ∈ B.E.get j := by
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hi
        · exact hI j hj
      have h := hField (insert i I) hInsert
      have hSet : B.N ∩ memberInter B.E (insert i I) = K₀.N ∩ B.E.get i := by
        ext x
        change (x ∈ J.N ∧ (∀ j ∈ insert i I, x ∈ B.E.get j)) ↔
          (x ∈ J.N ∧ (∀ j ∈ I, x ∈ B.E.get j)) ∧ x ∈ B.E.get i
        simp only [Finset.forall_mem_insert]
        tauto
      rw [hSet] at h
      exact h.mono fun _ hx _ => hx
    · have hClosed := hB.isWellFormed.isSNCDivisor.1 _ (List.get_mem B.E i)
      filter_upwards [hClosed.isOpen_compl.mem_nhds hi] with x hx hxi
      exact (hx hxi).elim
  have hSelected := hField I hI
  obtain ⟨S, hS, hOpen, haS⟩ := mem_nhds_iff.mp
    (hBase.and (hSelected.and ((Filter.eventually_all.2 hSlots).and (V.isOpen.mem_nhds haV))))
  let W : Opens X := ⟨S, hOpen⟩
  have hWV : W ≤ V := fun _ hx => (hS hx).2.2.2
  let A := CMfd.of (n := n) W
  let K := positiveMemberOn J H a W
  have hKu₀ := born_bar_tangent J hJ W u hu (fun _ hx => (hS hx).1)
  have hSelectedU : IsTangentDirectionAlong K₀.N K₀.ideal K₀.d W u :=
    selected_tangent_of_current_contact B hB.isWellFormed hB.one_le_d I W u hKu₀
      (fun _ hx => (hS hx).2.1)
  have hKu : IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → X)) :=
    isTangentDirectionAlong_pullback_val W
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK₀.isCoherent hf) hSelectedU
  have hK : IsInvDomain (k - 1) K := by
    have hKV' : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : V → X) K₀) := hKV
    have h := isInvDomain_pullback_val (MaxLocusLocal.nestedOpens V W) hKV'
    have h' := isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hWV).symm h
    rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hK₀.isCoherent hWV] at h'
  have hPow (x : X) (hx : x ∈ W) : HolomorphicAt n u x ∧ K₀.ideal.mem x (fun z => u z ^ K₀.d) :=
    true_normal_power_in_member B hB.isWellFormed hB.one_le_d I W u hKu₀ hx
  have hPowW (z : W) : K.ideal.mem z (fun w => u w.val ^ K.d) := by
    obtain ⟨hh, hm⟩ := hPow z.val z.property
    exact comp_mem_pullback (isLocalInverseAt_val (n := n) W z).mdiff hm
      (CompanionReduction.holomorphicAt_pow_of hh K₀.d)
  have hExp₀ (x : X) (hx : x ∈ W) (F : Set X) (hF : F ∈ K₀.E) :
      divExpAlong n K₀.N K₀.ideal F x = 0 := by
    by_cases hxF : x ∈ K₀.N ∩ F
    · have hFB : F ∈ B.E := by
        rw [memberRestrict_membersThrough_E] at hF
        exact List.mem_of_mem_filter hF
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hFB
      obtain ⟨e', η, hη, hdη⟩ := (hS hx).2.2.1 i hxF.2
      obtain ⟨hh, hm⟩ := hPow x hx
      exact divExpAlong_eq_zero_of_normal_power_field hK₀.isCoherent hxF hh K₀.d hm hη
        (by rw [hdη.self_of_nhds]; exact one_ne_zero)
    · exact divExpAlong_eq_zero_of_notMem
        (hK₀.isClosedSubmanifold_N.1.inter (hK₀.isSNCDivisor.1 F hF)) hxF
  have hExp : ∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0 := by
    intro F hF z
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hF
    have hLen : K.E.length = K₀.E.length := List.length_map _
    have hi : i.val < K₀.E.length := lt_of_lt_of_le i.isLt hLen.le
    exact (divExpAlong_pullback_val_get K₀ hK₀.isCoherent W z i.isLt hi).trans
      (hExp₀ z.val z.property _ (List.get_mem K₀.E ⟨i.val, hi⟩))
  have hNm := nonmonomial_eq_restrictOn_of_boundary_zero (X := A) K hExp
  have hMax := tangent_true_order_bound K hK hKu
  have hOrder (z : W) (hz : z ∈ K.cosupp) : nmOrd (M := A) K z = K.d := by
    have hLow : z ∈ ordGe K K.d := by
      change z ∈ cosupport n K.N (nmPart K) K.d
      rw [hNm]
      exact cosupport_subset_of_restrictLe restrictLe_restrictOn K.d hz
    have hHigh : z ∉ ordGe K (K.d + 1) := by
      intro hh
      change z ∈ cosupport n K.N (nmPart K) (K.d + 1) at hh
      rw [hNm] at hh
      exact hMax z (cosupport_subset_of_restrictLe
        (restrictLe_self_restrictOn hK.isWellFormed.isCoherent) _ hh)
    have hd : K.d - 1 + 1 = K.d := by have := hK.one_le_d; omega
    have hLow' : z ∈ ordGe K (K.d - 1 + 1) := hd.symm ▸ hLow
    exact le_antisymm (nmOrd_le_of_notMem hHigh) (hd ▸ succ_le_nmOrd_of_mem ⟨K.d, hHigh⟩ hLow')
  refine ⟨W, haS, hWV, hK, hKu, hPowW, hExp, hOrder, ?_⟩
  change companionAlong K.N K.E (nmPart K) (monomialPartAlong n K.N K.ideal K.E) K.d K.d = _
  rw [hNm]
  simp only [companionAlong, lt_self_iff_false, if_false]
  rfl

/-- An actual next-born comparison has a common window with zero retained
exponents and a carrier-restricted companion at the true selected mark. -/
theorem exists_localized_born_normal_order {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (a : X) (ha : a ∈ R.N) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {z | u z = 0} = R.N)
    (hWitness : LocalizedBornWitness (k := k) (l := l) hn J R a u) :
    let I : BlowupTower X X := .refl
    ∃ W : Opens X, a ∈ W ∧ W ≤ maskA J I a ∧ W ≤ maskA R I a ∧
      let A := CMfd.of (n := n) W
      let K := positiveMemberOn J I a W
      IsInvDomain (k - 1) K ∧ IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ Subtype.val) ∧
      (∀ z : W, K.ideal.mem z (fun w => u w.val ^ K.d)) ∧
      (∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0) ∧
      (∀ z ∈ K.cosupp, nmOrd (M := A) K z = K.d) ∧
      companionOf n (M := A) K K.d =
        (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n A) := by
  intro I
  obtain ⟨V, haV, hVJ, hVR, hKV, _, _⟩ := hWitness
  obtain ⟨W, haW, hWV, hW⟩ :=
    exists_localized_born_normal_order_subwindow hn J R hJ hR hClass a ha u hu hTrace V haV hKV
  exact ⟨W, haW, hWV.trans hVJ, hWV.trans hVR, hW⟩

end
end Hironaka.HironakaG1LocalizedBornNormalOrder
