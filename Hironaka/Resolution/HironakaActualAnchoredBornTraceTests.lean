import Hironaka.Resolution.HironakaActualAnchoredRecursivePointTests
import Hironaka.Resolution.HironakaActualLocalBornExponent
import Hironaka.Invariant.MemberInterAlong
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels

/-! Actual singleton point cuts and all-point newest-born proper traces.
The genuine born engine is reused at its native universe-zero scope.
The original family supplies its own nonempty trace, never an input packet. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredBornTraceTests
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  NormalCrossings BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec DivisorExponentAlong HironakaSharpOriginalProductTraceOrder
  HironakaActualProjectionTestRecord HironakaActualProjectionVerticalBlowupChart
  HironakaActualAnchoredVerticalChart HironakaActualAnchoredRecursivePointTests
  HironakaActualLocalBornExponent InvDomainTowerAlong MemberInterAlong
  BoundaryCount GermIdealOrder GermIdealPullbackCalculus RelativePrincipalizationSpan
open scoped ProductComplexManifold

theorem singleton_divisibility_iff_cosupport {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (N : Set X) (I : GermIdeal n X) (x : X) (hxN : x∈N) (e : ℕ) :
    IsDivNearAlong n N I ({x} : Set X) e x ↔ x∈cosupport n N I e := by
  constructor
  · intro h
    exact h.self_of_nhds hxN (mem_singleton x)
  · intro h
    exact Eventually.of_forall fun y _hyN hyx=>by
      rw [mem_singleton_iff.mp hyx]
      exact h

theorem singleton_exponent_eq_ordinary_order {n k : ℕ} {X : CMfd.{u} n}
    (S : MarkedIdeal n X) (hS : IsInvDomain k S) (x : X) (hxN : x∈S.N) :
    divExpAlong n S.N S.ideal ({x} : Set X) x =
      ordinaryTraceOrder S.N S.ideal x := by
  have hN:=hS.isWellFormed.isClosedSubmanifold_N
  have hI:=hS.isWellFormed.isCoherent
  have hHol : ∀y f,S.ideal.mem y f→HolomorphicAt n f y :=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf
  obtain ⟨dim,hReg⟩:=hN.2 x hxN
  obtain ⟨r,hr⟩:=exists_isLocalRetraction hReg
  have hCrit:=ordinaryTraceOrder_cosupport_iff hN hI hS.isNonzeroAlongAt hxN
  have hDivCrit:=isDivNearAlong_iff_le_divExpAlong (e:=ordinaryTraceOrder S.N S.ideal x) hr (mem_singleton x)
    (hS.isNonzeroAlongAt x hxN) hHol
  apply le_antisymm
  · exact (hCrit _).mp ((singleton_divisibility_iff_cosupport S.N S.ideal x hxN _).mp
      (isDivNearAlong_divExpAlong hHol x))
  · exact hDivCrit.mp ((singleton_divisibility_iff_cosupport S.N S.ideal x hxN _).mpr
      ((hCrit _).mpr le_rfl))

/-- The given native singleton map has the actual born value at EVERY
proper trace point. Empty traces are retained in the exact centre criterion. -/
theorem actual_singleton_born_trace {n k : ℕ} {X Y : CMfd.{0} (n+1)}
    (S : MarkedIdeal (n+1) X) (hS : IsInvDomain k S)
    (x : X) (hx : x∈S.cosupp) {π : Y→X}
    (hπ : IsBlowupAlong (n+1) ({x} : Set X) π) :
    let S' := S.geoTransform ({x} : Set X) π
    let D : Set Y := π ⁻¹' ({x} : Set X)
    let C : Set Y := S'.N∩D
    let ρ := ordinaryTraceOrder S.N S.ideal x
    S.IsAdmissibleCentre ({x} : Set X) ∧
    IsInvDomain k S' ∧ S'.d=S.d ∧
    S'.E=S.E.map (geoStrictTransform π ({x} : Set X))++[D] ∧
    S.d≤ρ ∧
    (∀y∈C, divExpAlong (n+1) S'.N S'.ideal D y=ρ-S.d) ∧
    IsClosedSubmanifold (n+1) C ∧
    HasNormalCrossings (n+1) C S'.E ∧
    (S'.IsAdmissibleCentre C ↔ C=∅ ∨ S.d≤ρ-S.d) := by
  dsimp only
  let S' := S.geoTransform ({x} : Set X) π
  let D : Set Y := π ⁻¹' ({x} : Set X)
  let C : Set Y := S'.N∩D
  let ρ := ordinaryTraceOrder S.N S.ideal x
  have hxN:=S.cosupp_subset_N hx
  have hC0 : S.IsAdmissibleCentre ({x} : Set X) :=
    ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1,
      fun y hy=>by rw [mem_singleton_iff.mp hy];exact hx,
      HironakaOneDimensionalCanonicalSuperlevels.hasNormalCrossings_singleton x
        hS.isWellFormed.isSNCDivisor⟩
  have hTest : IsGeoTestTower S
      (BlowupTower.step (Z:=Y) .refl ({x} : Set X) π hπ) := ⟨True.intro,hC0⟩
  have hS' : IsInvDomain k S' :=
    isInvDomain_geoTransformAlong hS _ hTest
  have hρ : S.d≤ρ :=
    (ordinaryTraceOrder_cosupport_iff hS.isWellFormed.isClosedSubmanifold_N
      hS.isWellFormed.isCoherent hS.isNonzeroAlongAt hxN S.d).mp hx
  have hExp : ∀y∈C,divExpAlong (n+1) S'.N S'.ideal D y=ρ-S.d := by
    intro y hy
    have hBirth:=original_history_born_exponent S hS
      (BlowupTower.refl : BlowupTower X X) True.intro hC0 (Z:=Y) hπ hy.1 hy.2
    have hπy : π y=x:=mem_singleton_iff.mp hy.2
    rw [hπy] at hBirth
    change S.d≤divExpAlong (n+1) S.N S.ideal ({x} : Set X) x ∧
      divExpAlong (n+1) S'.N S'.ideal D y=
        divExpAlong (n+1) S.N S.ideal ({x} : Set X) x-S.d at hBirth
    rw [singleton_exponent_eq_ordinary_order S hS x hxN] at hBirth
    exact hBirth.2
  let i : Fin S'.E.length := ⟨S.E.length,by simp [S',geoTransform]⟩
  have hGet : S'.E.get i=D := by
    simp [i,S',geoTransform,List.get_eq_getElem,D]
  have hTrace : S'.N∩memberInter S'.E {i}=C := by
    rw [memberInter_singleton i,hGet]
  have hClosed : IsClosedSubmanifold (n+1) C := by
    rw [←hTrace]
    exact isClosedSubmanifold_inter_memberInter (Nat.succ_pos n)
      hS'.isWellFormed.isClosedSubmanifold_N.1 hS'.isWellFormed.isSNCDivisor
      hS'.isWellFormed.isTransverse {i}
  have hNC : HasNormalCrossings (n+1) C S'.E := by
    rw [←hTrace]
    exact hasNormalCrossings_inter_memberInter hS'.isWellFormed.isTransverse {i}
  have hHol' : ∀y f,S'.ideal.mem y f→HolomorphicAt (n+1) f y :=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hS'.isWellFormed.isCoherent hf
  have hCriterion : S'.IsAdmissibleCentre C ↔ C=∅ ∨ S.d≤ρ-S.d := by
    constructor
    · intro hAdm
      by_cases hEmpty : C=∅
      · exact Or.inl hEmpty
      · obtain ⟨y,hy⟩:=Set.nonempty_iff_ne_empty.mpr hEmpty
        obtain ⟨dim,hReg⟩:=hS'.isWellFormed.isClosedSubmanifold_N.2 y hy.1
        obtain ⟨r,hr⟩:=exists_isLocalRetraction hReg
        have hDiv : IsDivNearAlong (n+1) S'.N S'.ideal D S.d y :=
          Eventually.of_forall fun z hzN hzD=>hAdm.2.1 ⟨hzN,hzD⟩
        have hBound:=(isDivNearAlong_iff_le_divExpAlong hr hy.2
          (hS'.isNonzeroAlongAt y hy.1) hHol').mp hDiv
        exact Or.inr (by simpa only [hExp y hy] using hBound)
    · rintro (hEmpty | hBound)
      · rw [hEmpty]
        exact MarkedIdeals.MarkedIdeal.isAdmissibleCentre_empty S'
      · refine ⟨hClosed,?_,hNC⟩
        intro y hy
        have hDiv:=isDivNearAlong_divExpAlong (N:=S'.N) (𝔞:=S'.ideal)
          (H:=D) hHol' y
        rw [hExp y hy] at hDiv
        exact cosupport_anti hBound (hDiv.self_of_nhds hy.1 hy.2)
  exact ⟨hC0,hS',rfl,rfl,hρ,hExp,hClosed,hNC,hCriterion⟩

private instance point_closed_fact {a : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X] (x : X) :
    Fact (IsClosedSubmanifold a ({x} : Set X)) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1⟩

private abbrev NativeTail {n : ℕ} {Y1 : CMfd.{0} (n+1)}
    (Q1 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))) : Type 1 :=
  Σ Z : CMfd.{0} (n+1), Σ R : BlowupTower Y1 Z,
    Σ e : OpenPartialHomeomorph Z (ComplexModel (n+1)),
      {z : Z // AnchoredInheritedLastChartChain a R e ∧
        IsGeoTestTower Q1 R ∧ z∈e.source ∧ e z=0}

private abbrev tailPoint {n : ℕ} {Y1 : CMfd.{0} (n+1)}
    {Q1 : MarkedIdeal (n+1) Y1}
    {a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))}
    (s : NativeTail Q1 a) : s.1 := s.2.2.2.val

private abbrev bornTraceDictionary {n k : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTail
      (Y1:=CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo) : Prop :=
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C0
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 π1
    (isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
      (projection_point_centre M hM x hx).2)
  let T:=A.append s.2.1
  let Q:=(projectionTest M).geoTransformAlong T
  let D : Set s.1:=Q.E.getLastD ∅
  let C : Set s.1:=Q.N∩D
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let q:=s.2.1.length+1
  IsGeoTestTower (projectionTest M) T ∧ IsInvDomain (k+1) Q ∧
  Q.d=M.d ∧ Q.E.length=M.E.length+1+q ∧
  tailPoint s∈Q.cosupp ∧ tailPoint s∈D ∧ C.Nonempty ∧
  (∀y∈C, divExpAlong (n+1) Q.N Q.ideal D y=q*(ρ-M.d)) ∧
  IsClosedSubmanifold (n+1) C ∧ HasNormalCrossings (n+1) C Q.E ∧
  (Q.IsAdmissibleCentre C ↔ M.d≤q*(ρ-M.d))

private abbrev currentDictionary {n k : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTail
      (Y1:=CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo) : Prop :=
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C0
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 π1
    (isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
      (projection_point_centre M hM x hx).2)
  let T:=A.append s.2.1
  let Q:=(projectionTest M).geoTransformAlong T
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let q:=s.2.1.length+1
  IsGeoTestTower (projectionTest M) T ∧ IsInvDomain (k+1) Q ∧
  Q.d=M.d ∧ Q.E.length=M.E.length+1+q ∧ tailPoint s∈Q.cosupp ∧
  ordinaryTraceOrder Q.N Q.ideal (tailPoint s)=ρ+q*(ρ-M.d)

private theorem exists_same_native_family {n k : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    let C0 : Set (projectionAmbient X):={(x,0)}
    let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
    let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C0
    let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C0 π1
    let P:=projectionTest M
    let p : projectionAmbient X:=(x,0)
    let ρ:=ordinaryTraceOrder M.N M.ideal x
    IsInvDomain (k+1) P ∧ P.d=M.d ∧ p∈P.cosupp ∧
    ordinaryTraceOrder P.N P.ideal p=ρ ∧ M.d≤ρ ∧
    ∃c : FlatChart (n+1) C0, π1 (c.invFun 0)=p ∧
    ∃h0 : AnchoredInheritedLastChartChain c.homeo
        (BlowupTower.refl : BlowupTower Y1 Y1) c.homeo ∧
      IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower Y1 Y1) ∧
      c.invFun 0∈c.homeo.source ∧ c.homeo (c.invFun 0)=0,
    ∃F : ℕ→NativeTail Q1 c.homeo,
      F 0=⟨Y1,BlowupTower.refl,c.homeo,⟨c.invFun 0,h0⟩⟩ ∧
      (∀r : ℕ,(F r).2.1.length=r) ∧
      (∀r : ℕ,
        ∃(π : (F (r+1)).1→(F r).1)
          (hπ : IsBlowupAlong (n+1) ({tailPoint (F r)} : Set (F r).1) π),
          (F (r+1)).2.1=BlowupTower.step (Z:=(F (r+1)).1)
            (F r).2.1 ({tailPoint (F r)} : Set (F r).1) π hπ ∧
          π (tailPoint (F (r+1)))=tailPoint (F r)) ∧
      ∀r : ℕ,currentDictionary M hM x hx c (F r) := by
  dsimp only
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C0
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C0 π1
  obtain ⟨Φ,Φs,c,SN,SE,U,hOriginal⟩:=
    HironakaActualAnchoredRecursivePointTests.exists_original_anchored_recursive_point_tests M hM x hx
  rcases hOriginal with ⟨hFirst,g,_hg,_hgBad,h0,chooseNext,hData⟩
  extract_lets s0 F at hData
  change ℕ→NativeTail Q1 c.homeo at F
  rcases hData with ⟨hZero,hLen,hSucc,hAll⟩
  rcases hFirst.2.1 with ⟨_hQueries,hP,_hPN,_hPI,hPd,_hPE,_hPLen,_hpN,
    hpCos,hdρ,_hSourceOrder,hPNat,_hPOrder,_hRest⟩
  have hpBase:=hFirst.2.2.2.2.2.1
  refine ⟨hP,hPd,hpCos,hPNat,hdρ,c,hpBase,h0,F,hZero,hLen,?_,?_⟩
  · intro r
    rw [hSucc r]
    rcases hWitness : chooseNext (F r) with
      ⟨c2,hπ2,_hCentre,_hCodim,_hPivot,_hSource,_hZero,hProjects,_hVector,_hTest,_hChain⟩
    exact ⟨blowupProj (n+1) ({tailPoint (F r)} : Set (F r).1),hπ2,rfl,hProjects⟩
  · intro r
    have hCurrent:=hAll r
    rcases hCurrent with ⟨_hCuts,_hSharp,hControl,_hHistory⟩
    rcases hControl with ⟨hT,hEq,hDom,hMark,hELen,_hB,_hLeft,_hRight,
      _hFSpan,_hFGood,_hFBad,_hFOrder,_hSum,_hGood,_hBad,hNat,_hOrder,
      _hdCurrent,hCos,_hAdmiss⟩
    dsimp only [currentDictionary]
    rw [←hEq]
    refine ⟨hT,hDom,hMark,?_,hCos,hNat⟩
    calc _=M.E.length+2+(F r).2.1.length:=hELen
         _=M.E.length+1+((F r).2.1.length+1):=by omega

private theorem born_dictionary_of_actual_last_step {n k j : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTail
      (Y1:=CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    {W : CMfd.{0} (n+1)} (S : MarkedIdeal (n+1) W) (hS : IsInvDomain j S)
    (y : W) (hy : y∈S.cosupp) (π : s.1→W)
    (hπ : IsBlowupAlong (n+1) ({y} : Set W) π)
    (hRecord :
      let C0 : Set (projectionAmbient X):={(x,0)}
      let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
      let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0
        (blowupProj (n+1) C0)
        (isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
          (projection_point_centre M hM x hx).2)
      (projectionTest M).geoTransformAlong (A.append s.2.1)=S.geoTransform ({y} : Set W) π)
    (hOrigin : π (tailPoint s)=y)
    (hCurrent : currentDictionary M hM x hx c s)
    (hBeta : ordinaryTraceOrder S.N S.ideal y-S.d=
      (s.2.1.length+1)*(ordinaryTraceOrder M.N M.ideal x-M.d)) :
    bornTraceDictionary M hM x hx c s := by
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0
    (blowupProj (n+1) C0)
    (isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
      (projection_point_centre M hM x hx).2)
  let Q:=(projectionTest M).geoTransformAlong (A.append s.2.1)
  let D : Set s.1:=Q.E.getLastD ∅
  change Q=S.geoTransform ({y} : Set W) π at hRecord
  have hD : D=π ⁻¹' ({y} : Set W) := by
    change Q.E.getLastD ∅=π ⁻¹' ({y} : Set W)
    rw [hRecord]
    simp [geoTransform]
  rcases hCurrent with ⟨hT,hDom,hMark,hELen,hCos,_hOrder⟩
  have hBorn:=actual_singleton_born_trace S hS y hy hπ
  rcases hBorn with ⟨_hCentre,_hDom,_hMark,_hWord,_hFinite,hExp,hClosed,hNC,hCriterion⟩
  have hzD : tailPoint s∈D := by
    rw [hD]
    exact mem_singleton_iff.mpr hOrigin
  have hNonempty : (Q.N∩D).Nonempty :=
    ⟨tailPoint s,MarkedIdeal.cosupp_subset_N Q hCos,hzD⟩
  have hMarkS : S.d=M.d := by
    have hm:=hMark
    change Q.d=M.d at hm
    rw [hRecord] at hm
    exact hm
  have hNotEmpty : (S.geoTransform ({y} : Set W) π).N∩π ⁻¹' ({y} : Set W)≠∅ := by
    have hn:=hNonempty.ne_empty
    rw [hD,hRecord] at hn
    exact hn
  rw [hBeta] at hExp hCriterion
  rw [hMarkS] at hCriterion
  simp only [hNotEmpty,false_or] at hCriterion
  dsimp only [bornTraceDictionary]
  refine ⟨hT,hDom,hMark,hELen,hCos,hzD,hNonempty,?_,?_,?_,?_⟩
  · change ∀z∈Q.N∩D,divExpAlong (n+1) Q.N Q.ideal D z=
      (s.2.1.length+1)*(ordinaryTraceOrder M.N M.ideal x-M.d)
    rw [hD,hRecord]
    exact hExp
  · change IsClosedSubmanifold (n+1) (Q.N∩D)
    rw [hD,hRecord]
    exact hClosed
  · change HasNormalCrossings (n+1) (Q.N∩D) Q.E
    rw [hD,hRecord]
    exact hNC
  · change Q.IsAdmissibleCentre (Q.N∩D) ↔
      M.d≤(s.2.1.length+1)*(ordinaryTraceOrder M.N M.ideal x-M.d)
    rw [hD,hRecord]
    exact hCriterion

/-- One ordinary original record gives all newest-born trace exponents on
the SAME actual anchored family, with its derived nonempty selected origins. -/
theorem exists_original_anchored_born_trace_tests {n k : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    let C0 : Set (projectionAmbient X):={(x,0)}
    let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
    let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C0
    let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C0 π1
    ∃c : FlatChart (n+1) C0,
    ∃h0 : AnchoredInheritedLastChartChain c.homeo
        (BlowupTower.refl : BlowupTower Y1 Y1) c.homeo ∧
      IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower Y1 Y1) ∧
      c.invFun 0∈c.homeo.source ∧ c.homeo (c.invFun 0)=0,
    ∃F : ℕ→NativeTail Q1 c.homeo,
      F 0=⟨Y1,BlowupTower.refl,c.homeo,⟨c.invFun 0,h0⟩⟩ ∧
      (∀r : ℕ,(F r).2.1.length=r) ∧
      (∀r : ℕ,
        ∃(π : (F (r+1)).1→(F r).1)
          (hπ : IsBlowupAlong (n+1) ({tailPoint (F r)} : Set (F r).1) π),
          (F (r+1)).2.1=BlowupTower.step (Z:=(F (r+1)).1)
            (F r).2.1 ({tailPoint (F r)} : Set (F r).1) π hπ ∧
          π (tailPoint (F (r+1)))=tailPoint (F r)) ∧
      ∀r : ℕ,bornTraceDictionary M hM x hx c (F r) := by
  dsimp only
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{0} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C0
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C0 π1
  let P:=projectionTest M
  let p : projectionAmbient X:=(x,0)
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
    (projection_point_centre M hM x hx).2
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 π1 hπ1
  obtain ⟨hP,hPd,hpCos,hPNat,hdρ,c,hpBase,h0,F,hZero,hLen,hSucc,hCurrent⟩:=
    exists_same_native_family M hM x hx
  refine ⟨c,h0,F,hZero,hLen,hSucc,?_⟩
  intro r
  cases r with
  | zero =>
    have hi:=hCurrent 0
    rw [hZero] at hi ⊢
    apply born_dictionary_of_actual_last_step M hM x hx c _ P hP p hpCos π1 hπ1
    · rfl
    · exact hpBase
    · exact hi
    · dsimp only [tailPoint]
      rw [hPNat,hPd]
      simp only [BlowupTower.length_refl,Nat.zero_add,Nat.one_mul]
  | succ r =>
    obtain ⟨π,hπ,hRStep,hOrigin⟩:=hSucc r
    let S:=(projectionTest M).geoTransformAlong (A.append (F r).2.1)
    have hiPrev:=hCurrent r
    rcases hiPrev with ⟨_hPrevTest,hPrevDom,hPrevMark,_hPrevLength,hPrevCos,hPrevOrder⟩
    apply born_dictionary_of_actual_last_step M hM x hx c (F (r+1)) S hPrevDom
      (tailPoint (F r)) hPrevCos π hπ
    · change (projectionTest M).geoTransformAlong (A.append (F (r+1)).2.1)=_
      rw [hRStep,BlowupTower.append_step]
      rfl
    · exact hOrigin
    · exact hCurrent (r+1)
    · rw [hPrevOrder,hPrevMark,hLen r,hLen (r+1)]
      simp only [Nat.add_mul,Nat.one_mul]
      omega

end
end Hironaka.HironakaActualAnchoredBornTraceTests
