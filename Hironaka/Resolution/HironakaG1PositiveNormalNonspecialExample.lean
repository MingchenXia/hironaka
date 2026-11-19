import Hironaka.Resolution.HironakaG1PositiveNormalPhase
import Hironaka.Resolution.HironakaG8MixedOrderInvariance
import Hironaka.Blowup.BlowupExistenceOriginIdeal

/-!
# Mark-one positive member records

On the initial positive mask, a sole original member through the anchor is
deleted from the boundary. At mark one the two coefficient operations and
homogenization retain the whole ideal. The order dictionaries identify the
first entries on the actual masked records, including the native zero
plane. Coordinate models calculate the trace orders of \((x,y^2)\) and
\((x,y^2,t)\) along their first coordinate divisors.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalNonspecialExample

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  RelativePrincipalizationSpan GermIdealPullbackCalculus IdealWeightPowers
  HomogenizedIdealAlong HomogenizedEquivalence DerivativeIdealAlong HomogenizedGlueing
  CoefficientIdeal StepOneValue StepOneValueMasked InvDomainMemberRestriction InvDomainRebase
  ResolutionInvariantSpec NonmonomialOrderLocal MarkedIdealRestrictOpen
  HironakaSharpOriginalProductTraceOrder HironakaG8MixedOrderInvariance

/-- At mark one the coefficient operation retains the entire coherent marked ideal. -/
theorem coeffMarkedAlong_eq_of_mark_one {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X)
    (hd : M.d = 1) (hI : M.ideal.IsCoherent) :
    coeffMarkedAlong M = M := by
  have hPow : idealPow M.ideal 1 = M.ideal := by
    rw [idealPow_succ, idealPow_zero, BlowupControlledTransform.unitIdeal_mul hI]
  have hExp : sumExp (fun j : ℕ => 1 - j) 1 0 = 1 := by simp [sumExp]
  have hZero : idealPow (iterDerivIdealAlong M.N M.ideal 0)
      (sumExp (fun j : ℕ => 1 - j) 1 0) = M.ideal := by
    rw [hExp]
    exact hPow
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · rfl
  · change finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
      (sumExp (fun j => M.d - j) M.d i)) M.d = M.ideal
    rw [hd, finSumIdeal_one (hZero.symm ▸ hI), hZero]
  · change (Finset.range M.d).prod (fun j => M.d - j) = M.d
    simp [hd]

/-- At mark one homogenization retains the entire coherent marked ideal. -/
theorem homMarkedAlong_eq_of_mark_one {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X)
    (hd : M.d = 1) (hI : M.ideal.IsCoherent) :
    homMarkedAlong M = M := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · rfl
  · change homogenizedIdealAlong M.N M.ideal M.d = M.ideal
    rw [hd, homogenizedIdealAlong, homSum]
    have hZero : (iterDerivIdealAlong M.N M.ideal 0).mul
        (idealPow (tangentIdealAlong M.N M.ideal 1) 0) = M.ideal := by
      change M.ideal.mul (unitIdeal n X) = M.ideal
      exact RestrictLeCalculus.mul_unitIdeal hI
    exact (finSumIdeal_one (hZero.symm ▸ hI)).trans hZero
  · rfl

/-- The actual initial masked positive lower of a mark-one record with one
original member through the anchor retains the whole ideal on its member
intersection and has empty boundary. -/
theorem positive_mark_one_single_member_lower_eq {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hd : M.d = 1) (hI : M.ideal.IsCoherent)
    (D : Set X) (hE : M.E = [D]) (p : X) (hp : p ∈ D) :
    let T : BlowupTower X X := .refl
    let O := maskA M T p
    lowerMarkedM M 1 T p =
      MarkedIdeal.pullback (Subtype.val : O → X)
        (⟨M.N ∩ D, [], M.ideal, 1⟩ : MarkedIdeal n X) := by
  classical
  let T : BlowupTower X X := .refl
  let O := maskA M T p
  have hC := coeffMarkedAlong_eq_of_mark_one M hd hI
  have hBar : barMarked (X := X) M = M := by
    change coeffMarkedAlong (homMarkedAlong M) = M
    rw [homMarkedAlong_eq_of_mark_one M hd hI, hC]
  have hOr : origMembers M T = M.E := by
    simp [origMembers, T, hBar]
  change MarkedIdeal.pullback (Subtype.val : O → X)
    (memberRestrict (geoTransformAlong (barMarked M) T)
      (membersThrough (geoTransformAlong (barMarked M) T).E (origMembers M T) p)) = _
  rw [hOr, geoTransformAlong_refl, hBar]
  apply congrArg (MarkedIdeal.pullback (Subtype.val : O → X))
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rw [memberRestrict_membersThrough_N, hE]
    ext w
    simp [hp]
  · rw [memberRestrict_membersThrough_E, hE]
    simp [hp]
  · rw [memberRestrict_ideal, hC]
  · rw [memberRestrict_d, hC, hd]

/-- On the actual positive mask the initial raw nonmonomial order is exactly
the order along the single selected member intersection. -/
theorem positive_mark_one_single_member_nmOrd {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hd : M.d = 1) (hI : M.ideal.IsCoherent)
    (D : Set X) (hE : M.E = [D]) (p : X) (hp : p ∈ D) :
    let T : BlowupTower X X := .refl
    let O := maskA M T p
    let L := lowerMarkedM M 1 T p
    ∀ q : O, nmOrd (M := CMfd.of (n := n) O) L q =
      ordinaryTraceOrder (X := X) (M.N ∩ D) M.ideal q.val := by
  intro T O L q
  let A : MarkedIdeal n X := ⟨M.N ∩ D, [], M.ideal, 1⟩
  let AP := MarkedIdeal.pullback (Subtype.val : O → X) A
  have hEq : L = AP := positive_mark_one_single_member_lower_eq M hd hI D hE p hp
  have hEmpty : L.E = [] := hEq ▸ rfl
  refine (nmOrd_eq_ordinaryTraceOrder_of_nil (X := CMfd.of (n := n) O) L hEmpty q).trans ?_
  change ordinaryTraceOrder (X := CMfd.of (n := n) O) L.N L.ideal q = _
  have hAP : AP.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
  have hOrder : ordinaryTraceOrder (X := CMfd.of (n := n) O) AP.N AP.ideal q =
      ordinaryTraceOrder (X := X) A.N A.ideal q.val := by
    apply nmOrd_congr
    intro r
    rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := CMfd.of (n := n) O) AP.N AP.ideal hAP,
      ordGe_ordinaryTraceMarked_eq_cosupport (X := X) A.N A.ideal hI]
    let A' : MarkedIdeal n X := ⟨A.N, [], A.ideal, r⟩
    have hHol : ∀ x g, A'.ideal.mem x g → HolomorphicAt n g x :=
      fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg
    change q ∈ (MarkedIdeal.pullback (Subtype.val : O → X) A').cosupp ↔ q.val ∈ A'.cosupp
    rw [cosupp_pullback_val A' hHol O]
    rfl
  exact hEq ▸ hOrder

/-- The computed trace order is the actual first entry of the general
canonical invariant of the selected lower record at the empty history. -/
theorem positive_mark_one_single_member_fst {n : ℕ} {X : CMfd.{0} (n + 1)}
    (M : MarkedIdeal (n + 1) X) (hd : M.d = 1) (hI : M.ideal.IsCoherent)
    (D : Set X) (hE : M.E = [D]) (p : X) (hp : p ∈ D) :
    let T : BlowupTower X X := .refl
    let O := maskA M T p
    let L := lowerMarkedM M 1 T p
    ∀ q : O,
      fstEntry ((CanonicalCentres.canonicalInvariant (n + 1)).inv L
        (BlowupTower.refl (X := CMfd.of (n := n + 1) O)) q) =
      ordinaryTraceOrder (X := X) (M.N ∩ D) M.ideal q.val := by
  intro T O L q
  exact (canonicalInvariant_fst (X := CMfd.of (n := n + 1) O) L .refl q).trans
    (positive_mark_one_single_member_nmOrd M hd hI D hE p hp q)

open HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaActualSectionBoundaryGeometry

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- For normal padding of a full-carrier, mark-one source, the selected
lower first entries measure the whole padded ideal along the vertical
member and the whole section ideal along the section cut of that member. -/
theorem positive_normal_mark_one_single_member_fst {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (hd : Q.d = 1) (hN : Q.N = univ)
    (D : Set U) (hE : Q.E = [D]) (p : productOpen U) (hp : projection U p ∈ D) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let T : BlowupTower X X := .refl
    let P := properNormalMarked Q
    let S := sectionMarked Q
    let O := lowerMask P 1 T p
    let W := lowerMask S 1 T p
    let D' := projection U ⁻¹' D
    let L : MarkedIdeal (n + 1) O := lowerMarkedM P 1 T p
    let K : MarkedIdeal (n + 1) W := lowerMarkedM S 1 T p
    (∀ q : O, fstEntry ((CanonicalCentres.canonicalInvariant (n + 1)).inv L
      (BlowupTower.refl (X := CMfd.of (n := n + 1) O)) q) =
        ordinaryTraceOrder (X := X) D' P.ideal q.val) ∧
    (∀ q : W, fstEntry ((CanonicalCentres.canonicalInvariant (n + 1)).inv K
      (BlowupTower.refl (X := CMfd.of (n := n + 1) W)) q) =
        ordinaryTraceOrder (X := X) (zeroPlane U ∩ D') S.ideal q.val) := by
  intro X T P S O W D' L K
  have hP := properNormalMarked_isInvDomain Q hQ
  have hS := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hPN : P.N = univ := by
    change projection U ⁻¹' Q.N = univ
    rw [hN, preimage_univ]
  have hSN : S.N = zeroPlane U := by
    change liftedCarrier Q.N = liftedCarrier univ
    rw [hN]
  have hPE : P.E = [D'] := by
    change Q.E.map (projection U ⁻¹' ·) = [D']
    rw [hE, List.map_singleton]
  have hSE : S.E = [D'] := hPE
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have h := positive_mark_one_single_member_fst (X := X) P hd
      hP.isWellFormed.isCoherent D' hPE p hp q
    simpa only [hPN, univ_inter] using h
  · have h := positive_mark_one_single_member_fst (X := X) S hd
      hS.isWellFormed.isCoherent D' hSE p hp q
    simpa only [hSN] using h

open HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory NormalCrossings

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the native zero plane, the actual selected lower invariant has the
same first entry as the ordinary order of the whole section ideal along
the intersection with the sole original member. -/
theorem positive_normal_mark_one_native_fst {n k : ℕ} {U : Opens (ComplexModel (n + 1))}
    (Q : MarkedIdeal (n + 1) U) (hQ : IsInvDomain k Q) (hd : Q.d = 1)
    (hN : Q.N = univ) (D : Set U) (hE : Q.E = [D]) (p : zeroPlane U)
    (hp : projection U p.val ∈ D) :
    let X := CMfd.of (n := (n + 1) + 1) (productOpen U)
    let Z := nativeManifold (Y := X) (Nat.le_succ (n + 1)) (zeroPlane U) (zeroPlane_regular U)
    let S := sectionMarked Q
    let B : MarkedIdeal (n + 1) Z :=
      nativePullback (Y := X) (Nat.le_succ (n + 1)) (zeroPlane U) (zeroPlane_regular U) S
    let T : BlowupTower Z Z := .refl
    let O := lowerMask B 1 T p
    let L : MarkedIdeal (n + 1) O := lowerMarkedM B 1 T p
    ∀ q : O, fstEntry ((CanonicalCentres.canonicalInvariant (n + 1)).inv L
      (BlowupTower.refl (X := CMfd.of (n := n + 1) O)) q) =
        ordinaryTraceOrder (X := X) (zeroPlane U ∩ (projection U ⁻¹' D)) S.ideal q.val.val := by
  intro X Z S B T O L q
  let V := zeroPlane U
  let D' : Set X := projection U ⁻¹' D
  let D'' : Set Z := (Subtype.val : V → X) ⁻¹' D'
  let A : MarkedIdeal ((n + 1) + 1) X := ⟨V ∩ D', [], S.ideal, 1⟩
  let AN := nativePullback (Y := X) (Nat.le_succ (n + 1)) V (zeroPlane_regular U) A
  have hS := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hSI : S.ideal.IsCoherent := hS.isWellFormed.isCoherent
  have hBN : B.N = (Subtype.val : V → X) ⁻¹' V := by
    change (Subtype.val : V → X) ⁻¹' (liftedCarrier Q.N) = _
    rw [hN]
    rfl
  have hBE : B.E = [D''] := by
    change (Q.E.map (projection U ⁻¹' ·)).map ((Subtype.val : V → X) ⁻¹' ·) = _
    rw [hE, List.map_singleton, List.map_singleton]
  have hBI : B.ideal.IsCoherent := by
    let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ (n + 1)) (zeroPlane_regular U)
    have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ (n + 1)) (zeroPlane_regular U)
    exact isCoherent_pullback (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ _) (zeroPlane_regular U)) hSI
  have hAN : B.N ∩ D'' = AN.N := by
    rw [hBN]
    exact (preimage_inter ..).symm
  have hCut := positive_mark_one_single_member_fst (X := Z) B hd hBI D'' hBE p hp q
  have hTrans : IsTransverse ((n + 1) + 1) V ([] : List (Set X)) :=
    isTransverse_nil_of_isClosedSubmanifold (liftedCarrier_closed_submanifold
      (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n + 1) (M := U)))
  have hHol : ∀ x g, A.ideal.mem x g → HolomorphicAt ((n + 1) + 1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSI hg
  have hOrd := nmOrd_nativePullback (Y := X) (Nat.le_succ (n + 1)) V (zeroPlane_regular U) A
    (inter_subset_left (t := D')) (isSNCDivisor_nil (n := (n + 1) + 1)) hTrans hHol q.val
  have hANord := nmOrd_eq_ordinaryTraceOrder_of_nil (X := Z) AN rfl q.val
  have hAord := nmOrd_eq_ordinaryTraceOrder_of_nil (X := X) A rfl q.val.val
  change _ = ordinaryTraceOrder (X := X) A.N A.ideal q.val.val
  rw [← hAord, hOrd, hANord]
  change _ = ordinaryTraceOrder (X := Z) AN.N B.ideal q.val
  rw [← hAN]
  exact hCut

open Filter GermIdealOrder InvertibleIdealQuotient IdealOrderArithmetic MonomialPartEtale
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualCentreJointJets BlowupFlatCoordinates

private abbrev coordinate (i : Fin 2) (z : ComplexModel 2) : ℂ := z i
def coordinatePairGenerator (i : Bool) (z : ComplexModel 2) : ℂ :=
  if i then coordinate 0 z else coordinate 1 z ^ 2
def coordinatePairIdeal : GermIdeal 2 (ComplexModel 2) := finiteFunctionIdeal coordinatePairGenerator
def firstCoordinateDivisor : Set (ComplexModel 2) := {z | coordinate 0 z = 0}

private theorem holF (i : Fin 2) (z : ComplexModel 2) : HolomorphicAt 2 (coordinate i) z :=
  Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) i).mdifferentiableAt

theorem coordinatePairIdeal_coherent : coordinatePairIdeal.IsCoherent := by
  apply isCoherent_finiteFunctionIdeal
  intro i
  cases i
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).mdifferentiable.pow 2
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiable

private theorem secondCoord_not_pointSquare :
    ¬ (idealPow (pointIdeal 2 (0 : ComplexModel 2)) 2).mem 0 (coordinate 1) := by
  let Φ : LocalHolomorphicEquivAt (n := 2) (chartAt (ComplexModel 2) (0 : ComplexModel 2) 0) :=
    BlowupExistenceOriginIdeal.idEquivAt
  exact MonomialCase.flatCoord_notMem_idealPow_two Φ 1 (mem_flatDomain_self Φ)

private def selectY : ComplexModel 2 →L[ℂ] ComplexModel 2 :=
  (actualJointNormalInclusion 1 1).comp (actualJointNormalProjection 1 1)

private theorem selectY_mem (z : ComplexModel 2) : selectY z ∈ firstCoordinateDivisor := by
  change actualJointNormalInclusion 1 1 (actualJointNormalProjection 1 1 z) ((0 : Fin 1).castAdd 1) = 0
  rw [actualJointNormalInclusion_tangent]

private theorem selectY_second (z : ComplexModel 2) : coordinate 1 (selectY z) = coordinate 1 z := by
  change actualJointNormalInclusion 1 1 (actualJointNormalProjection 1 1 z) ((0 : Fin 1).natAdd 1) = z _
  rw [actualJointNormalInclusion_normal, actualJointNormalProjection_apply]
  rfl

/-- Cutting `(x, y²)` by its first coordinate divisor leaves order two. -/
theorem actual_coordinate_pair_selected_trace_order :
    ordinaryTraceOrder (X := CMfd.of (n := 2) (ComplexModel 2)) firstCoordinateDivisor coordinatePairIdeal 0 = 2 := by
  let X := CMfd.of (n := 2) (ComplexModel 2)
  have hD : (0 : ComplexModel 2) ∈ firstCoordinateDivisor := by simp [firstCoordinateDivisor, coordinate]
  have hTwo : (0 : ComplexModel 2) ∈ cosupport 2 firstCoordinateDivisor coordinatePairIdeal 2 := by
    refine ⟨hD, fun g hg => IsInSpanAt.vanishesToOrderOn hg ?_⟩
    rintro _ ⟨i, rfl⟩
    cases i
    · have hPow := HomogenizedIdeal.pow_mem_idealPow
        (mem_pointIdeal_of_apply_eq_zero (holF 1 0) (by simp [coordinate])) (holF 1 0) 2
      exact ⟨_, hPow, Eventually.of_forall fun _ _ => rfl⟩
    · refine ⟨0, GiraudAlong.zero_mem_idealPow _ 0 2, Eventually.of_forall fun z hz => ?_⟩
      exact hz
  have hThree : (0 : ComplexModel 2) ∉ cosupport 2 firstCoordinateDivisor coordinatePairIdeal 3 := by
    intro hc
    have hg : coordinatePairIdeal.mem 0 (fun z => coordinate 1 z ^ 2) :=
      isInSpanAt_self ⟨false, rfl⟩ (CompanionReduction.holomorphicAt_pow_of (holF 1 0) 2)
    have hv := hc.2 _ hg
    have hv0 : VanishesToOrderOn 2 firstCoordinateDivisor (selectY 0) 3 (fun z => coordinate 1 z ^ 2) := by
      rw [map_zero]
      exact hv
    have hComp := vanishesToOrderOn_comp (θ := selectY) (p := (0 : ComplexModel 2))
      (Eventually.of_forall fun _ => selectY.mdifferentiableAt) hv0
    obtain ⟨a, ha, hEq⟩ := hComp
    have hSame : (fun z => coordinate 1 z ^ 2) =ᶠ[𝓝 (0 : ComplexModel 2)] a := by
      filter_upwards [hEq] with z hz
      simpa [Function.comp_apply, selectY_second] using hz (selectY_mem z)
    have hn := CompanionReduction.pow_notMem_idealPow (holF 1 0) (o := 1) secondCoord_not_pointSquare 2
    exact hn (OrderTaylor.mem_idealPow_congr ha hSame.symm)
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport (X := X) _ _ coordinatePairIdeal_coherent] at hTwo hThree
  exact Nat.le_antisymm (nmOrd_le_of_notMem hThree) (succ_le_nmOrd_of_mem ⟨2, hThree⟩ hTwo)

private abbrev paddedCoordinate (i : Fin 3) (z : ComplexModel 3) : ℂ := z i

def paddedGenerator (i : Bool ⊕ Unit) (z : ComplexModel 3) : ℂ :=
  match i with
  | .inl false => paddedCoordinate 1 z ^ 2
  | .inl true => paddedCoordinate 0 z
  | .inr _ => paddedCoordinate 2 z

def paddedCoordinateIdeal : GermIdeal 3 (ComplexModel 3) :=
  finiteFunctionIdeal paddedGenerator

def paddedFirstCoordinateDivisor : Set (ComplexModel 3) :=
  {z | paddedCoordinate 0 z = 0}

theorem paddedGenerator_hol (i : Bool ⊕ Unit) :
    MDifferentiable 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) (paddedGenerator i) := by
  rcases i with (_ | _) | _
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).mdifferentiable.pow 2
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).mdifferentiable
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).mdifferentiable

private theorem paddedGenerator_zero (i : Bool ⊕ Unit) : paddedGenerator i 0 = 0 := by
  rcases i with (_ | _) | _
  all_goals simp [paddedGenerator, paddedCoordinate]

private def selectNormal : ComplexModel 3 →L[ℂ] ComplexModel 3 :=
  (actualJointNormalInclusion 2 1).comp (actualJointNormalProjection 2 1)

private theorem selectNormal_member (z : ComplexModel 3) : selectNormal z ∈ paddedFirstCoordinateDivisor := by
  change actualJointNormalInclusion 2 1 (actualJointNormalProjection 2 1 z) ((0 : Fin 2).castAdd 1) = 0
  rw [actualJointNormalInclusion_tangent]

private theorem selectNormal_coordinate (z : ComplexModel 3) :
    paddedCoordinate 2 (selectNormal z) = paddedCoordinate 2 z := by
  change actualJointNormalInclusion 2 1 (actualJointNormalProjection 2 1 z) ((0 : Fin 1).natAdd 2) = z _
  rw [actualJointNormalInclusion_normal, actualJointNormalProjection_apply]
  rfl

/-- Cutting `(x, y², t)` by its first coordinate divisor leaves order one. -/
theorem padded_coordinate_triple_selected_trace_order :
    ordinaryTraceOrder (X := CMfd.of (n := 3) (ComplexModel 3)) paddedFirstCoordinateDivisor
      paddedCoordinateIdeal 0 = 1 := by
  let X := CMfd.of (n := 3) (ComplexModel 3)
  have hcoh : paddedCoordinateIdeal.IsCoherent :=
    isCoherent_finiteFunctionIdeal paddedGenerator paddedGenerator_hol
  have hD : (0 : ComplexModel 3) ∈ paddedFirstCoordinateDivisor := by
    simp [paddedFirstCoordinateDivisor, paddedCoordinate]
  have hOne : (0 : ComplexModel 3) ∈ cosupport 3 paddedFirstCoordinateDivisor paddedCoordinateIdeal 1 := by
    refine ⟨hD, fun g hg => IsInSpanAt.vanishesToOrderOn hg ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (vanishesToOrderOn_one_iff hD
      (Eventually.of_forall fun z => paddedGenerator_hol i z)).mpr (paddedGenerator_zero i)
  have hTwo : (0 : ComplexModel 3) ∉ cosupport 3 paddedFirstCoordinateDivisor paddedCoordinateIdeal 2 := by
    intro hc
    have hg : paddedCoordinateIdeal.mem 0 (paddedCoordinate 2) :=
      isInSpanAt_self ⟨.inr (), rfl⟩ (Eventually.of_forall fun z => paddedGenerator_hol (.inr ()) z)
    have hv : VanishesToOrderOn 3 paddedFirstCoordinateDivisor (selectNormal 0) 2 (paddedCoordinate 2) := by
      rw [map_zero]
      exact hc.2 _ hg
    have hComp := vanishesToOrderOn_comp (θ := selectNormal) (p := (0 : ComplexModel 3))
      (Eventually.of_forall fun _ => selectNormal.mdifferentiableAt) hv
    obtain ⟨a, ha, hEq⟩ := hComp
    have hSame : paddedCoordinate 2 =ᶠ[𝓝 (0 : ComplexModel 3)] a := by
      filter_upwards [hEq] with z hz
      simpa [Function.comp_apply, selectNormal_coordinate] using hz (selectNormal_member z)
    let Φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) (0 : ComplexModel 3) 0) :=
      BlowupExistenceOriginIdeal.idEquivAt
    exact MonomialCase.flatCoord_notMem_idealPow_two Φ 2 (mem_flatDomain_self Φ)
      (OrderTaylor.mem_idealPow_congr ha hSame.symm)
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport (X := X) _ _ hcoh] at hOne hTwo
  exact Nat.le_antisymm (nmOrd_le_of_notMem hTwo) (succ_le_nmOrd_of_mem ⟨1, hTwo⟩ hOne)


/-- A nonzero finite raw order of the selected trace rules out specialness
on the original mark-one record at the member anchor. -/
theorem not_isSpecial_of_mark_one_single_member_trace_order {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hd : M.d = 1) (hI : M.ideal.IsCoherent)
    (D : Set X) (hE : M.E = [D]) (p : X) (hp : p ∈ D)
    (hOrd : ordinaryTraceOrder (X := X) (M.N ∩ D) M.ideal p ≠ 0) :
    ¬ IsSpecial M (BlowupTower.refl (X := X)) p := by
  classical
  let T : BlowupTower X X := .refl
  have hC := coeffMarkedAlong_eq_of_mark_one M hd hI
  have hBar : barMarked (X := X) M = M := by
    change coeffMarkedAlong (homMarkedAlong M) = M
    rw [homMarkedAlong_eq_of_mark_one M hd hI, hC]
  have hOr : origMembers M T = [D] := by simp [origMembers, T, hBar, hE]
  have hLevel : level M T p = 1 := by simp [level, hOr, BoundaryCount.boundaryCount, hp]
  rintro (⟨hZero, _⟩ | ⟨_, hSpec⟩)
  · exact Nat.one_ne_zero (hLevel.symm.trans hZero)
  · rw [hOr, geoTransformAlong_refl, hBar, MemberInterLocusAlong.mem_memberInterLocus_iff] at hSpec
    have hHol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
      fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg
    have hCos : M.cosupp = M.N ∩ M.ideal.zeroLocus := by
      change cosupport n M.N M.ideal M.d = _
      rw [hd, cosupport_one hHol]
    have hpC : p ∈ M.N ∩ D := ⟨M.cosupp_subset_N hSpec.1, hp⟩
    have hAll (r : ℕ) : p ∈ cosupport n (M.N ∩ D) M.ideal r := by
      refine ⟨hpC, fun g hg => ⟨fun _ => 0, GiraudAlong.zero_mem_idealPow _ _ _, ?_⟩⟩
      have hLoc := HadamardBridge.eventually_mem_of_isCoherent hI hg
      filter_upwards [hLoc, hSpec.2] with y hy hgerm hyD
      have hyS := hgerm hyD.1 (fun H hH _ => List.mem_singleton.mp hH ▸ hyD.2)
      have hyZero : y ∈ M.ideal.zeroLocus := (hCos ▸ hyS).2
      exact hyZero g hy
    apply hOrd
    change nmOrd (ordinaryTraceMarked (M.N ∩ D) M.ideal) p = 0
    unfold nmOrd
    have hEmpty : {q : ℕ | p ∉ ordGe (ordinaryTraceMarked (M.N ∩ D) M.ideal) (q + 1)} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      apply hr
      rw [ordGe_ordinaryTraceMarked_eq_cosupport _ _ hI]
      exact hAll (r + 1)
    rw [hEmpty, Nat.sInf_empty]

/-- Both coordinate marked records are nonspecial at the origin of their
empty histories. -/
theorem coordinate_pair_and_triple_nonspecial :
    let X := CMfd.of (n := 2) (ComplexModel 2)
    let Y := CMfd.of (n := 3) (ComplexModel 3)
    let M : MarkedIdeal 2 X := ⟨univ, [firstCoordinateDivisor], coordinatePairIdeal, 1⟩
    let P : MarkedIdeal 3 Y := ⟨univ, [paddedFirstCoordinateDivisor], paddedCoordinateIdeal, 1⟩
    ¬ IsSpecial M (BlowupTower.refl (X := X)) 0 ∧
      ¬ IsSpecial P (BlowupTower.refl (X := Y)) 0 := by
  intro X Y M P
  constructor
  · refine not_isSpecial_of_mark_one_single_member_trace_order M rfl coordinatePairIdeal_coherent
      firstCoordinateDivisor rfl 0 (show (0 : ComplexModel 2) ∈ firstCoordinateDivisor by simp [firstCoordinateDivisor, coordinate]) ?_
    change ordinaryTraceOrder (X := X) (univ ∩ firstCoordinateDivisor) coordinatePairIdeal 0 ≠ 0
    rw [univ_inter, actual_coordinate_pair_selected_trace_order]
    decide
  · refine not_isSpecial_of_mark_one_single_member_trace_order P rfl
      (isCoherent_finiteFunctionIdeal paddedGenerator paddedGenerator_hol)
      paddedFirstCoordinateDivisor rfl 0 (show (0 : ComplexModel 3) ∈ paddedFirstCoordinateDivisor by simp [paddedFirstCoordinateDivisor, paddedCoordinate]) ?_
    change ordinaryTraceOrder (X := Y) (univ ∩ paddedFirstCoordinateDivisor) paddedCoordinateIdeal 0 ≠ 0
    rw [univ_inter, padded_coordinate_triple_selected_trace_order]
    decide

end

end Hironaka.HironakaG1PositiveNormalNonspecialExample
