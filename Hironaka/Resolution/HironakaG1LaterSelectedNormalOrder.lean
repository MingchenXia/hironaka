import Hironaka.Resolution.HironakaG1LaterSelectedNormalTangent
import Hironaka.Resolution.HironakaG1PositiveNormalRepairCentres
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaG1LaterSelectedNormalOrder
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec NormalCrossings HomogenizedIdealAlong
  TangentDirectionAlong DerivativeIdealAlong DerivativeIdealAlongCoherent
  RelativePrincipalizationSpan InvertibleIdealQuotient IdealWeightPowers
  DivisorExponentAlong DivisorExponent CoefficientIdeal
  CompanionReductionAlong CompanionRebase NonmonomialOrderLocal MonomialPartAlong
  HironakaG8E4cCompanion HironakaG8MixedOrderInvariance HironakaG8MixedBoundaryExponents
  HironakaSharpActualChronologicalResidualDictionary RestrictedIdealExtension
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualOpenZeroSectionDifferentials HironakaG1PositiveNormalRepairCentres
  HironakaG1LaterSelectedNormalTangent HironakaG8HomStable
  HironakaG1RecursiveMemberValueTransport
  StepOneValue StepOneValueMasked BoundaryCount InvDomainRebase InvDomainMemberRestriction
  MarkedIdealRestrictOpen GiraudAlong GermIdealOrder HironakaG8E4cProduct
  ContactEquivalenceAlong HironakaMonomialBlowup HironakaG1ProperNormalInitialRegime
  NonmonomialOrderTail InvDomainCompanion InvDomainTowerAlong RestrictLeCalculus
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal

/-- A normal power in the ideal excludes a boundary factor if a tangent
field of the carrier–boundary intersection detects its root. Only germ
membership and the derivative at the point are used. -/
theorem divExpAlong_eq_zero_of_normal_power_field {n : ℕ} {X : CMfd.{0} n}
    {N D : Set X} {I : GermIdeal n X} (hI : I.IsCoherent)
    {x : X} (hx : x ∈ N ∩ D) {u : X → ℂ} (hu : HolomorphicAt n u x)
    (d : ℕ) (hPow : I.mem x (fun z => u z ^ d))
    {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsTangentField (N ∩ D) e ξ x) (hDeriv : fieldDeriv e ξ u x ≠ 0) :
    divExpAlong n N I D x = 0 := by
  apply divExpAlong_eq_zero_of_not
  intro hDiv
  have hVan : (vanishingIdeal (n := n) (N ∩ D)).mem x u := by
    refine ⟨hu, ?_⟩
    filter_upwards [hDiv, HadamardBridge.eventually_mem_of_isCoherent hI hPow] with z hD hP hz
    have hHol := GermIdeal.IsCoherent.holomorphicAt_mem hI hP
    exact eq_zero_of_pow_eq_zero
      ((vanishesToOrderOn_one_iff hz.1 hHol).mp ((hD hz.1 hz.2).2 _ hP))
  exact hDeriv ((hξ.preserves _ hVan).2.self_of_nhds hx)

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

set_option maxHeartbeats 1600000 in
/-- At a later selected cut, the current upper tangent contributes its
normal power at the true coefficient mark. If tangents on the selected
carrier are normalized and touching retained slots admit a field
detecting the same coordinate, all divisor exponents vanish. The raw
order on cosupport is the mark and the true-mark companion is the
restriction of the original selected ideal to its own carrier. -/
theorem later_selected_normal_order_data {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1) (u : Y → ℂ) :
    let P := properNormalMarked Q
    let B := geoTransformAlong (barMarked P) H
    let I := membersThrough B.E (origMembers P H) p
    let K := memberRestrict B I
    let O := lowerMask P (s + 1) H p
    let L := lowerMarkedM P (s + 1) H p
    IsTangentDirectionAlong B.N B.ideal B.d O u →
    (∀ x ∈ O, ∃ (e : ComplexChart (n + 1) Y) (ξ : Fin (n + 1) → Y → ℂ),
      IsTangentField K.N e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) →
    (∀ x ∈ O, ∀ D ∈ K.E, x ∈ K.N ∩ D →
      ∃ (e : ComplexChart (n + 1) Y) (ξ : Fin (n + 1) → Y → ℂ),
        IsTangentField (K.N ∩ D) e ξ x ∧ fieldDeriv e ξ u x ≠ 0) →
    IsInvDomain k L ∧ (∀ D ∈ L.E, ∀ x, divExpAlong (n + 1) L.N L.ideal D x = 0) ∧
      (∀ x ∈ L.cosupp, nmOrd (M := CMfd.of (n := n + 1) O) L x = L.d) ∧
      companionOf (n + 1) (M := CMfd.of (n := n + 1) O) L L.d =
        (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ : MarkedIdeal (n + 1) O) ∧
      ∀ {Z : CMfd.{0} (n + 1)} (S : BlowupTower (CMfd.of (n := n + 1) O) Z),
        IsGeoTestTower L S → ∀ z ∈ (geoTransformAlong L S).cosupp,
          nmOrd (geoTransformAlong L S) z = L.d := by
  intro P B I K O L hu hField hSlots
  let X := CMfd.of (n := n + 1) (productOpen U)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hBarTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hBar H hBarTest
  have hLraw : L = MarkedIdeal.pullback (Subtype.val : O → Y) K := rfl
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed I
  have hTan := selected_tangent_of_current_contact B hB.isWellFormed hB.one_le_d I O u hu hField
  have hTanL : IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : O → Y)) :=
    isTangentDirectionAlong_pullback_val O
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent hg) hTan
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H hH p hLevel
  have hExpK : ∀ x ∈ O, ∀ D ∈ K.E, divExpAlong (n + 1) K.N K.ideal D x = 0 := by
    intro x hx D hD
    by_cases hxD : x ∈ K.N ∩ D
    · obtain ⟨e, ξ, hξ, hDeriv⟩ := hSlots x hx D hD hxD
      obtain ⟨huH, hPow⟩ := selected_normal_power_mem B hB.one_le_d I O u hu
        (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hf) hx
      exact divExpAlong_eq_zero_of_normal_power_field hK.isCoherent hxD huH K.d hPow hξ hDeriv
    · exact divExpAlong_eq_zero_of_notMem
        (hK.isClosedSubmanifold_N.1.inter (hK.isSNCDivisor.1 D hD)) hxD
  have hExp : ∀ D ∈ L.E, ∀ x, divExpAlong (n + 1) L.N L.ideal D x = 0 := by
    intro D hD x
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hD
    have hLen : L.E.length = K.E.length := by
      rw [hLraw]
      simp only [MarkedIdeal.pullback, List.length_map]
    have hi : i.val < K.E.length := lt_of_lt_of_le i.isLt hLen.le
    exact (divExpAlong_pullback_val_get K hK.isCoherent O x i.isLt hi).trans
      (hExpK x.val x.property _ (List.get_mem K.E ⟨i.val, hi⟩))
  have hNm := nonmonomial_eq_restrictOn_of_boundary_zero (X := CMfd.of (n := n + 1) O) L hExp
  have hMax : IsMaximalOrderAlong L.N L.ideal L.d := by
    intro x hx
    have hxCos : x ∈ L.cosupp := cosupport_anti (Nat.le_succ L.d) hx
    exact tangent_order_bound (X := CMfd.of (n := n + 1) O) L hL.isWellFormed hL.one_le_d
      hTanL (mem_univ x) hxCos hx
  refine ⟨hL, hExp, ?_, ?_, ?_⟩
  · intro x hx
    exact tested_order_of_true_mark_companion (Nat.succ_pos n)
      (X := CMfd.of (n := n + 1) O) (Y := CMfd.of (n := n + 1) O) L hL hMax hNm
      (.refl : BlowupTower (CMfd.of (n := n + 1) O) _) trivial x hx
  · change companionAlong L.N L.E (nmPart (M := CMfd.of (n := n + 1) O) L) (monomialPartAlong (n + 1) L.N L.ideal L.E) L.d L.d = _
    rw [hNm]
    simp only [companionAlong, lt_self_iff_false, if_false]
  · intro Z S hS z hz
    exact tested_order_of_true_mark_companion (Nat.succ_pos n) L hL hMax hNm S hS z hz

end
end Hironaka.HironakaG1LaterSelectedNormalOrder
