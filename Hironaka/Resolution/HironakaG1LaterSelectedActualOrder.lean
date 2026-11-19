import Hironaka.Resolution.HironakaG1LaterContactFieldExistence
import Hironaka.Resolution.HironakaG1LaterSelectedNormalOrder
import Hironaka.Invariant.StepOneTangentChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterSelectedActualOrder
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec NormalCrossings HomogenizedIdealAlong
  TangentDirectionAlong DerivativeIdealAlong RelativePrincipalizationSpan
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaActualOpenZeroSectionDifferentials
  HironakaActualRelativeNormalGeometry HironakaActualSectionBoundaryGeometry
  HironakaG1LaterSelectedNormalTangent HironakaG1LaterContactFieldExistence
  HironakaG1LaterSelectedNormalOrder HironakaG8HomStable HironakaG1PositiveNormalRepairCentres
  StepOneValue StepOneValueMasked StepOneLowerDomain BoundaryCount InvDomainMemberRestriction InvDomainRebase
  DerivativeIdealAlongCoherent InvertibleIdealQuotient IdealWeightPowers GiraudAlong GermIdealOrder
  DivisorExponentAlong CoefficientIdeal CompanionReductionAlong CompanionRebase NonmonomialOrderLocal
  MonomialPartAlong RestrictedIdealExtension NonmonomialOrderTail InvDomainCompanion InvDomainTowerAlong
  RestrictLeCalculus MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  ContactEquivalenceAlong HironakaMonomialBlowup HironakaG1ProperNormalInitialRegime
  HironakaG8MixedBoundaryExponents
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

set_option maxHeartbeats 1800000 in
/-- The current transformed contact has a single open subwindow of the
literal selected mask on which all touching retained slots admit normal
fields. Nonincident closed slots can be excluded from this subwindow. -/
theorem exists_later_selected_normal_slot_fields {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : p ∈ (geoTransformAlong (barMarked (properNormalMarked Q)) H).cosupp)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p) :
    let P := properNormalMarked Q
    let B := geoTransformAlong (barMarked P) H
    let I := membersThrough B.E (origMembers P H) p
    let K := memberRestrict B I
    let O := maskA P H p
    ∃ (W : Opens Y) (u : Y → ℂ), p ∈ W ∧ W ≤ O ∧
      IsTangentDirectionAlong B.N B.ideal B.d W u ∧
      (∀ x ∈ W, ∃ (e : ComplexChart (n + 1) Y) (ξ : Fin (n + 1) → Y → ℂ),
        IsTangentField K.N e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) ∧
      (∀ x ∈ W, ∀ D ∈ K.E, x ∈ K.N ∩ D →
        ∃ (e : ComplexChart (n + 1) Y) (ξ : Fin (n + 1) → Y → ℂ),
          IsTangentField (K.N ∩ D) e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) := by
  classical
  intro P B I K O
  let X := CMfd.of (n := n + 1) (productOpen U)
  let Sec := sectionMarked Q
  let S := geoTransformAlong Sec H
  let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hPBar := bar_local_any_boundary (X := X) P hP
  have hBT := (hPBar.wEquiv.2 H).1.mp hH
  have hB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBar.isWellFormed H hBT
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hPS := properNormalMarked_locWPEquiv_section Q hQ
  have hST := (hPS.wEquiv.2 H).1.mp hH
  have hS := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hSec.isWellFormed H hST
  have hSE : S.E = B.E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := Sec) (𝔫 := barMarked P) rfl H
  have hSD : S.N = D := by
    rw [N_geoTransformAlong]
    exact congrArg (strictAlong H) (normal_contact_carrier Q).symm
  have hDN : D ⊆ B.N := by
    change D ⊆ (geoTransformAlong (barMarked P) H).N
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono H (fun _ hy => hy.1)
  have hpS : p ∈ S.cosupp := (hPS.wEquiv.2 H).2 hH ▸ ((hPBar.wEquiv.2 H).2 hH).symm ▸ hp
  have hpD : p ∈ D := hSD ▸ S.cosupp_subset_N hpS
  have hpO : p ∈ O := mem_maskA (X := X) P hP.isWellFormed hP.one_le_d
    (Nat.succ_pos n) H hBT (hLevel ▸ Nat.succ_pos s) hNS
  obtain ⟨V, u, hpV, hu, hZero⟩ := later_normal_bar_contact Q hQ H hH (hDN hpD)
  have hpU : u p = 0 := ((Set.ext_iff.mp hZero p).mpr ⟨hpD, hpV⟩).1.2
  obtain ⟨e, ξ, hξ, hDetect⟩ := hu.multiplicity_one p hpV hpU
  have hUvan : (vanishingIdeal (n := n + 1) D).mem p u := by
    refine ⟨GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg)
      (B.d - 1) p u (hu.mem p hpV), ?_⟩
    filter_upwards [V.isOpen.mem_nhds hpV] with z hz hzD
    exact ((Set.ext_iff.mp hZero z).mpr ⟨hzD, hz⟩).1.2
  have hTransD : IsTransverse (n + 1) D B.E := hSD ▸ hSE ▸ hS.isTransverse
  have hI : ∀ i ∈ I, p ∈ B.E.get i := fun i hi => (mem_membersThrough.mp hi).2
  have hFields := exists_normalized_tangent_field_of_transverse_boundary (Nat.succ_pos n)
    B.E I hB.isSNCDivisor hB.isTransverse hTransD hI hpD hDN hUvan hξ hDetect
  have hSlots (i : Fin B.E.length) :
      ∀ᶠ x in 𝓝 p, x ∈ B.E.get i →
        ∃ (g : ComplexChart (n + 1) Y) (η : Fin (n + 1) → Y → ℂ),
          IsTangentField (K.N ∩ B.E.get i) g η x ∧ fieldDeriv g η u =ᶠ[𝓝 x] fun _ => 1 := by
    by_cases hi : p ∈ B.E.get i
    · have hIi (j) (hj : j ∈ insert i I) : p ∈ B.E.get j := by
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hi
        · exact hI j hj
      have hField := exists_normalized_tangent_field_of_transverse_boundary (Nat.succ_pos n)
        B.E (insert i I) hB.isSNCDivisor hB.isTransverse hTransD hIi hpD hDN hUvan hξ hDetect
      have hPerm : B.N ∩ memberInter B.E (insert i I) = K.N ∩ B.E.get i := by
        ext x
        change (x ∈ B.N ∧ (∀ j ∈ insert i I, x ∈ B.E.get j)) ↔
          (x ∈ B.N ∧ (∀ j ∈ I, x ∈ B.E.get j)) ∧ x ∈ B.E.get i
        simp only [Finset.forall_mem_insert]
        tauto
      rw [hPerm] at hField
      exact hField.mono fun _ h _ => h
    · have hClosed : IsClosed (B.E.get i) := hB.isSNCDivisor.1 (B.E.get i) (List.get_mem B.E i)
      filter_upwards [hClosed.isOpen_compl.mem_nhds hi] with x hx hxi
      exact (hx hxi).elim
  have hAll := Filter.eventually_all.2 hSlots
  have hVN : ∀ᶠ x in 𝓝 p, x ∈ V := V.isOpen.mem_nhds hpV
  have hON : ∀ᶠ x in 𝓝 p, x ∈ O := O.isOpen.mem_nhds hpO
  obtain ⟨D₀, hD₀, hOpen, hpD₀⟩ := mem_nhds_iff.mp
    ((hFields.and hAll).and (hVN.and hON))
  let W : Opens Y := ⟨D₀, hOpen⟩
  refine ⟨W, u, hpD₀, fun _ hx => (hD₀ hx).2.2,
    ⟨W.isOpen, fun x hx => hu.mem x (hD₀ hx).2.1, fun x hx => hu.multiplicity_one x (hD₀ hx).2.1⟩,
    fun x hx => (hD₀ hx).1.1, ?_⟩
  intro x hx A hA hIncident
  have hAB : A ∈ B.E := by
    rw [memberRestrict_membersThrough_E] at hA
    exact List.mem_of_mem_filter hA
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hAB
  exact (hD₀ hx).1.2 i hIncident.2

private theorem selected_normal_power_mem {n : ℕ} {X : CMfd.{0} n}
    (B : MarkedIdeal n X) (hd : 0 < B.d) (I : Finset (Fin B.E.length))
    (V : Opens X) (u : X → ℂ) (hu : IsTangentDirectionAlong B.N B.ideal B.d V u)
    (hHol : ∀ x f, B.ideal.mem x f → HolomorphicAt n f x) {x : X} (hx : x ∈ V) :
    let K := memberRestrict B I
    HolomorphicAt n u x ∧ K.ideal.mem x (fun z => u z ^ K.d) := by
  let K := memberRestrict B I
  let i := B.d - 1
  let a := sumExp (fun j => B.d - j) B.d i
  have hMem := hu.mem x hx
  have hUH := holomorphicAt_of_mem_iterDerivIdealAlong hHol i x u hMem
  have hi : i < B.d := by dsimp [i]; omega
  have hOne : B.d - i = 1 := by dsimp [i]; omega
  have hMark : K.d = a := by
    change (Finset.range B.d).prod (fun j => B.d - j) = a
    simpa only [hOne, one_mul] using (mul_sumExp (fun j => B.d - j) hi).symm
  refine ⟨hUH, ?_⟩
  change IsInSpanAt (n := n) (fun f => ∃ j, j < B.d ∧
    (idealPow (iterDerivIdealAlong B.N B.ideal j) (sumExp (fun m => B.d - m) B.d j)).mem x f) x _
  rw [hMark]
  exact isInSpanAt_self ⟨i, hi, HomogenizedIdeal.pow_mem_idealPow hMem hUH a⟩
    (CompanionReduction.holomorphicAt_pow_of hUH a)

private theorem tangent_order_bound {n : ℕ} {X : CMfd.{0} n} (L : MarkedIdeal n X)
    (hL : L.IsWellFormed) (hd : 0 < L.d) {V : Set X} {u : X → ℂ}
    (hu : IsTangentDirectionAlong L.N L.ideal L.d V u)
    {x : X} (hxV : x ∈ V) (hx : x ∈ L.cosupp) : x ∉ cosupport n L.N L.ideal (L.d + 1) := by
  intro hHigh
  let j := L.d - 1
  have hj : 1 + j = L.d := by dsimp [j]; omega
  have hHol : ∀ y f, L.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hL.isCoherent hf
  have hMem : (iterDerivIdealAlong L.N L.ideal j).mem x u := hu.mem x hxV
  have hUH := holomorphicAt_of_mem_iterDerivIdealAlong hHol j x u hMem
  have hx1 := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 j (by rw [hj]; exact hx)
  have hu0 := (vanishesToOrderOn_one_iff hx1.1 hUH).mp (hx1.2 _ hMem)
  obtain ⟨e, ξ, hξ, hD⟩ := hu.multiplicity_one x hxV hu0
  have hGen : DerivGenAlong L.N (iterDerivIdealAlong L.N L.ideal j) x (fieldDeriv e ξ u) :=
    Or.inr (Or.inr ⟨e, ξ, u, hξ, hMem, rfl⟩)
  have hDH := holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt hUH
  have hDMem : (iterDerivIdealAlong L.N L.ideal (j + 1)).mem x (fieldDeriv e ξ u) :=
    isInSpanAt_self hGen hDH
  have hNum : 1 + (j + 1) = L.d + 1 := by omega
  have hx2 := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 (j + 1)
    (by rw [hNum]; exact hHigh)
  exact hD ((vanishesToOrderOn_one_iff hx2.1 hDH).mp (hx2.2 _ hDMem))

private theorem tested_order_of_true_mark_companion {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (hL : IsInvDomain k L)
    (hMax : IsMaximalOrderAlong L.N L.ideal L.d)
    (hPart : nmPart L = restrictOn n L.N L.ideal)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T)
    (y : Y) (hy : y ∈ (geoTransformAlong L T).cosupp) :
    nmOrd (geoTransformAlong L T) y = L.d := by
  let C := companionOf n L L.d
  have hC := isInvDomain_companionAlong (X := X) (𝔪 := L) hn hL hL.one_le_d
  have hRE : RestrictEquiv C L := by
    change RestrictEquiv (companionAlong L.N L.E (nmPart L)
      (monomialPartAlong n L.N L.ideal L.E) L.d L.d) L
    simp only [companionAlong, lt_self_iff_false, if_false]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · rw [hPart]
      exact restrictLe_restrictOn
    · rw [hPart]
      exact restrictLe_self_restrictOn hL.isWellFormed.isCoherent
  have hW : WEquiv (X := X) C L := RestrictEquiv.wEquiv
    hRE hC.isWellFormed.isClosedSubmanifold_N.1 hC.isWellFormed.isCoherent hL.isWellFormed.isCoherent
  have hCT := (hW.2 T).1.mpr hT
  have hBound : ∀ x ∈ L.cosupp, x ∉ ordGe L (L.d + 1) := by
    intro x _ hx
    change x ∈ cosupport n L.N (nmPart L) (L.d + 1) at hx
    rw [hPart] at hx
    exact hMax x (cosupport_subset_of_restrictLe
      (restrictLe_self_restrictOn hL.isWellFormed.isCoherent) _ hx)
  have hFacts := companionOf_tower_facts hn hL hL.one_le_d hBound T hCT
  have hyC : y ∈ (geoTransformAlong C T).cosupp := ((hW.2 T).2 hCT).symm ▸ hy
  have hCur := isInvDomain_geoTransformAlong hL T hT
  exact Nat.le_antisymm (nmOrd_le_of_notMem (hFacts.2.1 y hy))
    ((mem_ordGe_iff hCur.isWellFormed hCur.isNonzeroAlongAt hy.1 L.d).mp (hFacts.2.2 hyC).1)


set_option maxHeartbeats 1800000 in
/-- On one genuine subwindow of the actual later selected mask, the
normal contact fields force vanishing exponents for every retained
slot. The true-mark companion and the order along all tests use the
literal selected record on that subwindow. -/
theorem exists_later_selected_actual_normal_order {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : p ∈ (geoTransformAlong (barMarked (properNormalMarked Q)) H).cosupp)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p) :
    let P := properNormalMarked Q
    let B := geoTransformAlong (barMarked P) H
    let I := membersThrough B.E (origMembers P H) p
    let K := memberRestrict B I
    let O := maskA P H p
    ∃ (W : Opens Y) (u : Y → ℂ), p ∈ W ∧ W ≤ O ∧
      let A := CMfd.of (n := n + 1) W
      let L : MarkedIdeal (n + 1) A := MarkedIdeal.pullback (Subtype.val : W → Y) K
      IsInvDomain k L ∧
      IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) ∧
      (∀ D ∈ L.E, ∀ x, divExpAlong (n + 1) L.N L.ideal D x = 0) ∧
      companionOf (n + 1) (M := A) L L.d =
        (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ : MarkedIdeal (n + 1) A) ∧
      ∀ {Z : CMfd.{0} (n + 1)} (S : BlowupTower A Z), IsGeoTestTower L S →
        ∀ x ∈ (geoTransformAlong L S).cosupp, nmOrd (geoTransformAlong L S) x = L.d := by
  intro P B I K O
  let X := CMfd.of (n := n + 1) (productOpen U)
  obtain ⟨W, u, hpW, hWO, hu, hField, hSlots⟩ :=
    exists_later_selected_normal_slot_fields Q hQ H hH p hp hLevel hNS
  let A := CMfd.of (n := n + 1) W
  let L : MarkedIdeal (n + 1) A := MarkedIdeal.pullback (Subtype.val : W → Y) K
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hBarTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hB := isInvDomain_geoTransformAlong hBar H hBarTest
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed I
  have hTan := selected_tangent_of_current_contact B hB.isWellFormed hB.one_le_d I W u hu hField
  have hTanL : IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) :=
    isTangentDirectionAlong_pullback_val W
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent hg) hTan
  have hO : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → Y) K) :=
    padded_lower_isInvDomain Q hQ H hH p hLevel
  have hNested := isInvDomain_pullback_val (MaxLocusLocal.nestedOpens O W) hO
  have hL : IsInvDomain k L := by
    have hSmall := isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n + 1) hWO).symm hNested
    rw [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hK.isCoherent hWO] at hSmall
    exact hSmall
  have hExpK : ∀ x ∈ W, ∀ D ∈ K.E, divExpAlong (n + 1) K.N K.ideal D x = 0 := by
    intro x hx D hD
    by_cases hxD : x ∈ K.N ∩ D
    · obtain ⟨e, ξ, hξ, hDeriv⟩ := hSlots x hx D hD hxD
      obtain ⟨huH, hPow⟩ := selected_normal_power_mem B hB.one_le_d I W u hu
        (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hf) hx
      exact divExpAlong_eq_zero_of_normal_power_field hK.isCoherent hxD huH K.d hPow hξ
        (by rw [hDeriv.self_of_nhds]; exact one_ne_zero)
    · exact divExpAlong_eq_zero_of_notMem
        (hK.isClosedSubmanifold_N.1.inter (hK.isSNCDivisor.1 D hD)) hxD
  have hExp : ∀ D ∈ L.E, ∀ x, divExpAlong (n + 1) L.N L.ideal D x = 0 := by
    intro D hD x
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hD
    have hi : i.val < K.E.length := by simpa only [L, MarkedIdeal.pullback, List.length_map] using i.isLt
    exact (divExpAlong_pullback_val_get K hK.isCoherent W x i.isLt hi).trans
      (hExpK x.val x.property _ (List.get_mem K.E ⟨i.val, hi⟩))
  have hNm := nonmonomial_eq_restrictOn_of_boundary_zero (X := A) L hExp
  have hMax : IsMaximalOrderAlong L.N L.ideal L.d := by
    intro x hx
    have hxCos : x ∈ L.cosupp := cosupport_anti (Nat.le_succ L.d) hx
    exact tangent_order_bound (X := A) L hL.isWellFormed hL.one_le_d hTanL (mem_univ x) hxCos hx
  refine ⟨W, u, hpW, hWO, hL, hTanL, hExp, ?_, ?_⟩
  · change companionAlong L.N L.E (nmPart (M := A) L) (monomialPartAlong (n + 1) L.N L.ideal L.E) L.d L.d = _
    rw [hNm]
    simp only [companionAlong, lt_self_iff_false, if_false]
    rfl
  · intro Z S hS z hz
    exact tested_order_of_true_mark_companion (Nat.succ_pos n) L hL hMax hNm S hS z hz

end
end Hironaka.HironakaG1LaterSelectedActualOrder
