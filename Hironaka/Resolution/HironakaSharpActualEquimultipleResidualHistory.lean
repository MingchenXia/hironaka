import Hironaka.Resolution.HironakaSharpOriginalAmbientDynamicGoodPrefixes
import Hironaka.Resolution.HironakaSharpActualControlledAccumulatedResidual
import Hironaka.Invariant.NonmonomialStepAlong

/-! Actual equimultiple residuals retain ONE genuine controlled baseline.
Complete source-first mathematics is in
`hironaka-sharp-actual-equimultiple-residual-history-extension.tex`.
No reflexive/historical FULL equality, historical-centre ambient admissibility,
strict FULL decrease, FIRST erasure or terminating schedule is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualEquimultipleResidualHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaSharpOriginalAmbientDynamicGoodPrefixes HironakaSharpOriginalDynamicGoodPrefixes
  HironakaSharpActualDynamicDistinctCentre HironakaSharpActualOriginalControlledHistory
  HironakaSharpActualOriginalDynamicStep HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualFiniteProductResidual
  HironakaSharpActualChronologicalResidualDictionary HironakaSharpActualProductRelativeStrict
  HironakaSharpActualControlledAccumulatedResidual HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalFirstMemberRelativeStrict
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight
  RestrictLeCalculus MonomialPartAlong DivisorExponentAlong NonmonomialOrderLocal
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal GermIdealOrder IdealWeightPowers
  RestrictEmptyTower CanonicalCentres ResolutionDriver
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The literal current residual with its order mark and ENTIRE actual born list. -/
def residualMarked (W : Set X) (E : List (Set X)) (a : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : MarkedIdeal n Y :=
  ⟨(geoTransformAlong (geometricTemplate W []) T).N,
    (geoTransformAlong (geometricTemplate W []) T).E,chronologicalMemberProduct W E T,a⟩

/-- Actual upper centre order produces no new factor before the independently
proved controlled/relative-STRICT dictionary identifies the WHOLE restriction. -/
theorem equimultiple_geoTransform_restrictEquiv_nextRelativeStrict (hn : 0<n)
    (M : MarkedIdeal n X) (hw : M.IsWellFormed)
    (hnz : ∀ x∈M.N,IsNonzeroAlongAt M.N M.ideal x)
    (hp : ∀ x∈M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧ ∀ g,M.ideal.mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hUpper : ∀ c∈C,c∉cosupport n M.N M.ideal (M.d+1))
    (hNo : ∀ x∈M.N,∀ i : Fin M.E.length,x∈M.E.get i → ∃ f,M.ideal.mem x f ∧
      ¬IsInSpanOnAt (n := n) M.N ((vanishingIdeal (n := n) (M.E.get i)).mem x) x f) :
    RestrictEquiv (M.geoTransform C π)
      (⟨(M.geoTransform C π).N,(M.geoTransform C π).E,
        nextRelativeStrict M.N M.ideal C π,M.d⟩ : MarkedIdeal n Y) := by
  let Q := M.geoTransform C π
  have hwQ := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  have hNoQ : ∀ y∈Q.N,∀ i : Fin Q.E.length,y∈Q.E.get i → ∃ f,Q.ideal.mem y f ∧
      ¬IsInSpanOnAt (n := n) Q.N ((vanishingIdeal (n := n) (Q.E.get i)).mem y) y f := by
    intro y hy i hi
    exact NonmonomialStepAlong.exists_not_isInSpanOnAt_geoTransform hπ hw.isClosedSubmanifold_N
      hw.isSNCDivisor hw.isTransverse hw.isCoherent hC.2.2 hC.2.1 hUpper hNo hy i hi
  have hNorm := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hwQ.isClosedSubmanifold_N
    hwQ.isSNCDivisor hwQ.isTransverse hwQ.isCoherent hNoQ
  have hStrict := controlled_all_accumulated_nonmonomial_eq_nextStrict hn M hw hnz hp hC hπ hNo
  have hEq : restrictOn n Q.N Q.ideal=nextRelativeStrict M.N M.ideal C π := hNorm.symm.trans hStrict
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · change RestrictLe Q.N Q.ideal (nextRelativeStrict M.N M.ideal C π)
    rw [←hEq]
    exact restrictLe_self_restrictOn hwQ.isCoherent
  · change RestrictLe Q.N (nextRelativeStrict M.N M.ideal C π) Q.ideal
    rw [←hEq]
    exact restrictLe_restrictOn

private theorem residualMarked_wellFormed (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (a : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    (residualMarked W E a T).IsWellFormed := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  have hP := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  exact ⟨hwT.isClosedSubmanifold_N,hP.1,hwT.isSNCDivisor,hwT.isTransverse⟩

/-- Actual centre equimultiplicity supplies admissibility for the order mark,
then the COMPLETE next chronological datum on the SAME given blowup. -/
theorem original_equimultiple_residual_step (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (a : ℕ)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hC : (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C)
    (hOrd : ∀ c∈C,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) c=a) :
    (residualMarked W E a T).IsAdmissibleCentre C ∧
      RestrictEquiv ((residualMarked W E a T).geoTransform C π)
        (residualMarked W E a (.step T C π hπ)) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let M := residualMarked W E a T
  have hwM := residualMarked_wellFormed hn hW hE hdense a T hT
  obtain ⟨hcP,hnzP,hprP,_hProductOrder⟩ :=
    original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hAdm : M.IsAdmissibleCentre C := by
    refine ⟨hC.1,?_,hC.2.2⟩
    intro c hc
    exact (ordinaryTraceOrder_cosupport_iff hwM.isClosedSubmanifold_N hcP hnzP (hC.subset_N hc) a).mpr
      (by
        change a≤ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) c
        rw [hOrd c hc])
  have hUpper : ∀ c∈C,c∉cosupport n M.N M.ideal (M.d+1) := by
    intro c hc hh
    have hle := (ordinaryTraceOrder_cosupport_iff hwM.isClosedSubmanifold_N hcP hnzP
      (hC.subset_N hc) (a+1)).mp hh
    change a+1≤ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) c at hle
    rw [hOrd c hc] at hle
    omega
  have hNo := original_chronological_product_no_exceptional_factor hn hW hE hdense T hT
  have hDict := equimultiple_geoTransform_restrictEquiv_nextRelativeStrict hn M hwM hnzP hprP
    hAdm hπ hUpper hNo
  have hNext := original_next_chronological_product_eq_full_relative_strict hn hW hE hdense
    T hT hπ hC.subset_N
  change RestrictEquiv (M.geoTransform C π)
    (⟨(M.geoTransform C π).N,(M.geoTransform C π).E,
      nextRelativeStrict A.N (chronologicalMemberProduct W E T) C π,a⟩ : MarkedIdeal n Z) at hDict
  rw [hNext] at hDict
  exact ⟨hAdm,hDict⟩

/-- Each actual centre has the fixed actual residual order; empty steps and
all original/born positions stay in the literal finite tail. -/
def IsEquimultipleResidualTail (W : Set X) (E : List (Set X)) (a : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    {Z : CMfd.{u} n} → BlowupTower Y Z → Prop
  | _,.refl => True
  | _,.step S C _ _ => IsEquimultipleResidualTail W E a T S ∧
      ∀ c∈C,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
        (chronologicalMemberProduct W E (T.append S)) c=a

/-- ONE initial order-marked residual, its actual test history and COMPLETE
restricted datum are retained through an actual finite equimultiple tail. -/
theorem original_equimultiple_residual_history (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (a : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append S) → IsEquimultipleResidualTail W E a T S →
      IsGeoTestTower (residualMarked W E a T) S ∧
        RestrictEquiv (geoTransformAlong (residualMarked W E a T) S)
          (residualMarked W E a (T.append S))
  | _,.refl,_hTS,_hOrd => by
    exact ⟨trivial,RestrictEquiv.refl (residualMarked_wellFormed hn hW hE hdense a T hT).isCoherent⟩
  | _,.step S C π hπ,hTS,hOrd => by
    have hPre : IsGeoTestTower (geometricTemplate W []) (T.append S) := hTS.1
    obtain ⟨hTest,hEq⟩ := original_equimultiple_residual_history hn hW hE hdense a T hT S hPre hOrd.1
    obtain ⟨hAdm,hNext⟩ := original_equimultiple_residual_step hn hW hE hdense a
      (T.append S) hPre hπ hTS.2 hOrd.2
    have hAdmBase := hEq.isAdmissibleCentre_iff.mpr hAdm
    have hwBase := residualMarked_wellFormed hn hW hE hdense a T hT
    have hwCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwBase S hTest
    have hwActual := residualMarked_wellFormed hn hW hE hdense a (T.append S) hPre
    have hSame := hEq.geoTransform_eq (C := C) hwCurrent.isClosedSubmanifold_N.1 hwCurrent.isCoherent
      hwActual.isCoherent hπ.contMDiff
    refine ⟨⟨hTest,hAdmBase⟩,?_⟩
    change RestrictEquiv ((geoTransformAlong (residualMarked W E a T) S).geoTransform C π)
      (residualMarked W E a (.step (T.append S) C π hπ))
    rw [hSame]
    exact hNext

/-- The TRUE chosen nonempty current FULL FIRST maximum internally produces
its positive ordinary order, using only its literal first coordinate. -/
theorem exists_positive_order_of_actual_first_maximum (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    {C : Set Y} (hne : C.Nonempty)
    (hCeq : C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T)
      (.refl : BlowupTower Y Y)) (chronologicalDistinctDefect W E T)) :
    ∃ a : ℕ,1≤a ∧ ∀ c∈C,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) c=a := by
  obtain ⟨x,hx⟩ := hne
  let a := ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
    (chronologicalMemberProduct W E T) x
  have hxZ := (hCeq ▸ hx).1
  have hlt := hxZ.2
  rw [←chronological_product_eq_actual_family_product W E T] at hlt
  have hpos : 1≤a := by change 1≤ordinaryTraceOrder _ _ x;omega
  refine ⟨a,hpos,?_⟩
  intro c hc
  have hVal := ((hCeq ▸ hx).2 c (hCeq ▸ hc).1).antisymm ((hCeq ▸ hc).2 x (hCeq ▸ hx).1)
  have hFirst := congrArg (fun v : ValTy (n+1) => (ofLex v).1) hVal
  change nmOrd (geoTransformAlong (currentProductMarked W E T) (.refl : BlowupTower Y Y)) c=
    nmOrd (geoTransformAlong (currentProductMarked W E T) (.refl : BlowupTower Y Y)) x at hFirst
  rw [geoTransformAlong_refl,currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT,
    currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hT] at hFirst
  exact hFirst

/-- ONLY natural original compact-pure inputs produce the finite prefix,
SAME actual FULL successor and genuine order-marked whole residual dictionary.
All ambient trace state and WHOLE original-good isomorphisms are retained. -/
theorem exists_original_finite_prefix_equimultiple_residual_step (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1≤n)
    (hr : ∀ x∈W,RegularAtDim (n := n) W x (d+1)) (m : ℕ) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y) (C : Set Y)
      (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π) (a : ℕ),
      T.length=m ∧ 1≤a ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) T ∧ IsDynamicFirstPrefix hn W E T ∧
      CentresOver (originalSharpBadLocus (n := n) W E) T ∧ HasAmbientTraceState W E T ∧
      IsIsomorphismOver n T.proj (originalGoodLocus (n := n) W E) ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) (.step T C π hπ) ∧
      IsDynamicFirstPrefix hn W E (.step T C π hπ) ∧
      CentresOver (originalSharpBadLocus (n := n) W E) (.step T C π hπ) ∧
      HasAmbientTraceState W E (.step T C π hπ) ∧
      IsIsomorphismOver n (BlowupTower.step T C π hπ).proj (originalGoodLocus (n := n) W E) ∧
      (∀ c∈C,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) c=a) ∧
      RestrictEquiv ((residualMarked W E a T).geoTransform C π)
        (residualMarked W E a (.step T C π hπ)) := by
  obtain ⟨Y,T,hLen,hTest,hRule,hOver,hState,hGood,_hHeads⟩ :=
    exists_original_ambient_dynamic_first_prefix hn hW hE hdense hK hd hr m
  obtain ⟨C,Z,π,hπ,hTestNew,hRuleNew,hOverNew,hStateNew⟩ :=
    exists_joint_dynamic_successor hn hW hE hdense hK hd hr T hTest hRule hOver hState
  have hGoodNew : IsIsomorphismOver n (BlowupTower.step T C π hπ).proj (originalGoodLocus (n := n) W E) := by
    simpa only [originalSharpBadLocus_eq_compl_good,compl_compl] using
      isIsomorphismOver_proj_of_centresOver (originalSharpBadLocus (n := n) W E) (.step T C π hπ) hOverNew
  have hwOriginal : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template _ hwOriginal T hTest
  have hGeomNew := actual_original_test_history_template _ hwOriginal (.step T C π hπ) hTestNew
  have hOrder : ∃ a : ℕ,1≤a ∧ ∀ c∈C,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) c=a := by
    by_cases hZ : chronologicalDistinctDefect W E T=∅
    · have hEmpty : C=∅ := by simpa only [hZ,ite_true] using hRuleNew.2
      refine ⟨1,le_rfl,?_⟩
      intro c hc
      rw [hEmpty] at hc
      exact hc.elim
    · have hCeq : C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T)
          (.refl : BlowupTower Y Y)) (chronologicalDistinctDefect W E T) := by
        simpa only [hZ,ite_false] using hRuleNew.2
      obtain ⟨C0,hne0,_hCZ0,_hAdm0,_hTemp0,hC0eq⟩ :=
        exists_actual_dynamic_distinct_max_centre hn hW hE hdense hK hd hr T hGeom
          (Set.nonempty_iff_ne_empty.mpr hZ)
      have hCC0 : C=C0 := hCeq.trans hC0eq.symm
      have hne : C.Nonempty := hCC0.symm ▸ hne0
      exact exists_positive_order_of_actual_first_maximum hn hW hE hdense T hGeom hne hCeq
  obtain ⟨a,hpos,hOrd⟩ := hOrder
  have hDict := (original_equimultiple_residual_step hn hW hE hdense a T hGeom hπ hGeomNew.2 hOrd).2
  exact ⟨Y,T,C,Z,π,hπ,a,hLen,hpos,hTest,hRule,hOver,hState,hGood,
    hTestNew,hRuleNew,hOverNew,hStateNew,hGoodNew,hOrd,hDict⟩

end
end Hironaka.HironakaSharpActualEquimultipleResidualHistory
