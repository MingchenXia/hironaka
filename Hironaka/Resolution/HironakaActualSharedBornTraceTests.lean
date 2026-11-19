import Hironaka.Resolution.HironakaActualSharedRecursivePointTests
import Hironaka.Resolution.HironakaActualPolymorphicBornExponent
import Hironaka.Resolution.HironakaActualAnchoredBornTraceTests
import Hironaka.Invariant.MemberInterAlong

/-!
# Both whole born traces on one actual original point family

The polymorphic native local birth law is applied at EVERY point of the
ENTIRE newest proper trace. The original two records retain ONE S01 family,
its SAME literal original histories, all whole ideals/marks, and all ordered
old/horizontal/born/empty slots. No query-specific geometry is selected.
Blueprint FIRST: `hironaka-actual-shared-born-trace-tests.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSharedBornTraceTests
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  NormalCrossings BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec RelativePrincipalizationSpan InvertibleIdealQuotient
  GiraudAlong GermIdealTotalTransform GermIdealPullbackCalculus GermIdealOrder
  IdealOrderArithmetic IdealWeightPowers CompanionReductionAlong
  HironakaSharpOriginalProductTraceOrder HironakaActualAnchoredVerticalChart
  HironakaActualAnchoredOriginalIdealOrder HironakaActualAnchoredSeedTotalFactor
  HironakaActualProperOriginalTowerFactor HironakaActualProjectionTestRecord
  HironakaActualProjectionVerticalBlowupChart HironakaActualProjectionVerticalOrder
  HironakaOneDimensionalCanonicalSuperlevels InvDomainTowerAlong
  BlowupExceptionalDivisor BlowupFunctionTransform MarkedIdealOperationsAlong
  RestrictedIdealWeight NonmonomialOrderLocal
open HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci
open scoped ProductComplexManifold

open DivisorExponentAlong HironakaActualPolymorphicBornExponent MemberInterAlong
  BoundaryCount HironakaActualSharedRecursivePointTests
theorem actual_singleton_born_trace {n k : ℕ} {X Y : CMfd.{u} (n+1)}
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
    (∀y∈C, divExpAlong (n+1) S'.N S'.ideal D y=ρ-S.d ∧
      ∀e : ℕ, IsDivNearAlong (n+1) S'.N S'.ideal D e y ↔ e≤ρ-S.d) ∧
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
    rw [HironakaActualAnchoredBornTraceTests.singleton_exponent_eq_ordinary_order S hS x hxN] at hBirth
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
  have hAllCuts : ∀y∈C,divExpAlong (n+1) S'.N S'.ideal D y=ρ-S.d ∧
      ∀e : ℕ,IsDivNearAlong (n+1) S'.N S'.ideal D e y ↔ e≤ρ-S.d := by
    intro y hy
    refine ⟨hExp y hy,?_⟩
    intro e
    obtain ⟨dim,hReg⟩:=hS'.isWellFormed.isClosedSubmanifold_N.2 y hy.1
    obtain ⟨r,hr⟩:=exists_isLocalRetraction hReg
    have hCut:=isDivNearAlong_iff_le_divExpAlong (e:=e) hr hy.2
      (hS'.isNonzeroAlongAt y hy.1) hHol'
    simpa only [hExp y hy] using hCut
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
  exact ⟨hC0,hS',rfl,rfl,hρ,hAllCuts,hClosed,hNC,hCriterion⟩

private instance point_closed_fact {a : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X] (x : X) :
    Fact (IsClosedSubmanifold a ({x} : Set X)) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1⟩

private abbrev recordMark {a : ℕ} (X : CMfd.{u} a) (Q : MarkedIdeal a X) : ℕ :=
  @MarkedIdeal.d a X.carrier X.topologicalSpace X.chartedSpace Q

private abbrev recordBoundary {a : ℕ} (X : CMfd.{u} a) (Q : MarkedIdeal a X) : List (Set X) :=
  @MarkedIdeal.E a X.carrier X.topologicalSpace X.chartedSpace Q

private abbrev wholeTailCuts {n : ℕ} {X : CMfd.{u} n}
    {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    {Z : CMfd.{u} (n+1)} (N : Set X) (Nt : Set Z) (x : X) (z : Z)
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z) : Prop :=
  let κ : Z→X := (Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj
  let B : GermIdeal n X→GermIdeal (n+1) Z:=fun I=>
    GermIdeal.pullback (m:=n+1) R.proj (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I))
  κ z=x ∧ z∈Nt ∧ ∀(I : GermIdeal n X),I.IsCoherent→
    B I=GermIdeal.pullback (m:=n+1) κ I ∧ (B I).IsCoherent ∧
    ∀a : ℕ,(z∈cosupport (n+1) Nt (B I) ((R.length+2)*a) ↔ x∈cosupport n N I a) ∧
      ∀b : ℕ,b≤R.length+1→
        (z∈cosupport (n+1) Nt (B I) ((R.length+2)*a+b+1) ↔
          x∈cosupport n N I (a+1))

private abbrev controlledTailOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1))) (z : Z) : Prop :=
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let P:=projectionTest M
  let Q1:=P.geoTransform C π1
  let A : BlowupTower (CMfd.of (projectionAmbient X)) Y1:=
    .step .refl C π1 (isBlowupAlong_blowupProj (n:=n+1) (C:=C)
      (projection_point_centre M hM x hx).2)
  let T:=A.append R
  let Q:=Q1.geoTransformAlong R
  let B:=GermIdeal.pullback (m:=n+1) R.proj
    (GermIdeal.pullback (m:=n+1) π1
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal))
  let F:=idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let q:=R.length+1
  let ν:=q*M.d
  let μ:=(q+1)*ρ
  let s:=ρ+q*(ρ-M.d)
  IsGeoTestTower P T ∧ Q=P.geoTransformAlong T ∧ IsInvDomain (k+1) Q ∧
  Q.d=M.d ∧ Q.E.length=M.E.length+2+R.length ∧
  B=GermIdeal.pullback (m:=n+1) T.proj P.ideal ∧
  RestrictLe Q.N B (F.mul Q.ideal) ∧ RestrictLe Q.N (F.mul Q.ideal) B ∧
  (∀g : Z→ℂ,F.mem z g↔IsInSpanAt (n:=n+1)
    (·=fun v=>e v (Fin.last n)^ν) z g) ∧
  z∈cosupport (n+1) Q.N F ν ∧ z∉cosupport (n+1) Q.N F (ν+1) ∧
  GermIdealOrder.order (n+1) Q.N F z=(ν : ℕ∞) ∧
  ν+s=μ ∧
  z∈cosupport (n+1) Q.N Q.ideal s ∧
  z∉cosupport (n+1) Q.N Q.ideal (s+1) ∧
  ordinaryTraceOrder Q.N Q.ideal z=s ∧
  GermIdealOrder.order (n+1) Q.N Q.ideal z=(s : ℕ∞) ∧
  M.d≤s ∧ z∈Q.cosupp ∧ Q.IsAdmissibleCentre ({z} : Set Z)



private def oldMask {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter fun i=>i.castAdd 1∈S

private abbrev wholeCutsOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  let p : projectionAmbient X := (x,0)
  let C : Set (projectionAmbient X) := {p}
  let _ : Fact (IsClosedSubmanifold (n+1) C) := ⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X := blowupProj (n+1) C
  let Q : MarkedIdeal (n+1) Y := (projectionTest M).geoTransform C π
  let z := c.invFun 0
  Φ.source⊆(chartAt (ComplexModel n) x).target ∧ Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
  c.y₀=p ∧ c.k=0 ∧ c.j=Fin.last n ∧
  (∀(y : projectionAmbient X)(i : Fin n),flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1) ∧
  (∀y : projectionAmbient X,flatCoord c.Φ (Fin.last n) y=y.2 0) ∧
  (∀y∈flatDomain c.Φ,y∈(projectionTest M).N ↔
    c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace SN) ∧
  (∀i,x∈M.E.get i→∀y∈flatDomain c.Φ,y∈(Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i ↔
    c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace (SE i)) ∧
  Fin.last n∉SN ∧ (∀i,Fin.last n∉SE i) ∧ (0 : ComplexModel (n+1))∈c.target ∧
  z∈c.source ∧ π z=p ∧ c.toFun z=0 ∧ IsBlowupAlong (n+1) C π ∧
  c.homeo∈atlas (ComplexModel (n+1)) Y ∧ IsInvDomain (k+1) Q ∧ z∈Q.cosupp ∧
  recordMark Y Q=M.d ∧
  recordBoundary Y Q=M.E.map (fun H=>geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' H))++
    [geoStrictTransform π C (horizontal X),π ⁻¹' C] ∧
  (recordBoundary Y Q).length=M.E.length+2 ∧
  IsOpen U ∧ z∈U ∧ U⊆c.source ∧
  (∀v∈U,v∈Q.N↔c.toFun v∈coordSubspace SN) ∧
  (∀i,(x∈M.E.get i→∀v∈U,v∈geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i)↔
      c.toFun v∈coordSubspace (SE i)) ∧
    (x∉M.E.get i→∀v∈U,v∉geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i))) ∧
  (∀v∈U,v∉geoStrictTransform π C (horizontal X)) ∧
  (∀v∈U,v∈π ⁻¹' C↔c.toFun v (Fin.last n)=0) ∧

  Φs.toFun=Φ.toFun ∧ Φs.invFun=Φ.invFun ∧
  Φs.source⊆Φ.source ∧ Φs.target⊆Φ.target ∧
  Φs.source⊆(chartAt (ComplexModel n) x).target ∧
  Φs.toFun (chartAt (ComplexModel n) x x)=0 ∧
  flatDomain Φs=flatDomain Φ∩(fun y : X=>((y,0) : projectionAmbient X)) ⁻¹' flatDomain c.Φ ∧
  (∀y∈flatDomain Φs,y∈M.N↔flatMap Φs y∈coordSubspace (oldMask SN)) ∧

  ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (_hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (_hz : z∈e.source) (_he0 : e z=0),
    wholeTailCuts M.N (Q.geoTransformAlong R).N x z R

private abbrev projectionQueriesOutput {n : ℕ} {X : CMfd.{u} n}
    (N : Set X) (x : X) : Prop :=
  let p : projectionAmbient X:=(x,0)
  let hf:=ProductComplexManifold.contMDiff_fst
    (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
  let τ:=actualHolomorphicGermPullback hf p
  (∀I : GermIdeal n X,I.IsCoherent→
    Ideal.map τ.toRingHom (wholeChartStalkIdeal I x x (mem_chart_source _ x))=
      wholeChartStalkIdeal (GermIdeal.pullback (m:=n+1)
        (Prod.fst : projectionAmbient X→X) I) p p (mem_chart_source _ p) ∧
    (∀b : ℕ,p∈cosupport (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I) b ↔
        x∈cosupport n N I b) ∧
    GermIdealOrder.order (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' N)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I) p=
        GermIdealOrder.order n N I x) ∧
  (∀(f : X→ℂ) (hf0 : HolomorphicAt n f x),
    τ (chartTranslatedGerm x x (mem_chart_source _ x) f hf0)=
      chartTranslatedGerm p p (mem_chart_source _ p) (f∘Prod.fst)
        (hf0.comp_contMDiff (Eventually.of_forall fun _=>hf.contMDiffAt))) ∧
  ∀(c : ℂ) (a : HolGerm (ComplexModel n)),τ (c • a)=c • τ a

private abbrev NativeTailState {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    (Q1 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))) : Type (u+1) :=
  Σ Z : CMfd.{u} (n+1), Σ R : BlowupTower Y1 Z,
    Σ e : OpenPartialHomeomorph Z (ComplexModel (n+1)),
      {z : Z // AnchoredInheritedLastChartChain a R e ∧
        IsGeoTestTower Q1 R ∧ z∈e.source ∧ e z=0}

private abbrev tailPoint {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    {Q1 : MarkedIdeal (n+1) Y1}
    {a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))}
    (s : NativeTailState Q1 a) : s.1 := s.2.2.2.val

private abbrev initialQueryOutput {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X) (I : GermIdeal n X) (d : ℕ)
    (_hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (_hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let P:=projectionTest M
  let p : projectionAmbient X:=(x,0)
  let ρ:=ordinaryTraceOrder M.N I x
  let H:=HironakaActualProjectionTowerHistory.projectionTowerHistory M0
    (BlowupTower.refl : BlowupTower (projectionAmbient X) (projectionAmbient X))
  projectionQueriesOutput M0.N x ∧ IsInvDomain (k+1) P ∧ p∈P.cosupp ∧
  P.N=(Prod.fst : projectionAmbient X→X) ⁻¹' M0.N ∧
  P.ideal=GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I ∧
  P.d=d ∧ P.E=M0.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·)++[horizontal X] ∧
  P.E.length=M0.E.length+1 ∧ d≤ρ ∧
  GermIdealOrder.order n M.N I x=(ρ : ℕ∞) ∧
  ordinaryTraceOrder P.N P.ideal p=ρ ∧ GermIdealOrder.order (n+1) P.N P.ideal p=(ρ : ℕ∞) ∧
  P.IsAdmissibleCentre ({p} : Set (projectionAmbient X)) ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H ∧
  HironakaActualMixedTestPowerNormalization.record M H=P ∧
  HironakaActualMixedTestPowerNormalization.length H=1 ∧
  HironakaActualMixedTestPowerNormalization.projections H=1 ∧
  HironakaActualMixedTestPowerNormalization.baseMap H=(Prod.fst : projectionAmbient X→X)

private abbrev queryAtState {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState
      (Y1:=CMfd.of (n:=n+1) (BlowupSpace (n+1)
        ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let Z:=s.1
  let R:=s.2.1
  let e:=s.2.2.1
  let z:=tailPoint s
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let T:=A.append R
  let Q:=((projectionTest M).geoTransform C π1).geoTransformAlong R
  let Q0:=((projectionTest M0).geoTransform C π1).geoTransformAlong R
  let H:=HironakaActualProjectionTowerHistory.projectionTowerHistory M0 T
  let V:=e.source∩R.proj ⁻¹' (U∩c.source)
  let B:=GermIdeal.pullback (m:=n+1) R.proj
    (GermIdeal.pullback (m:=n+1) π1
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) I))
  let ρ:=ordinaryTraceOrder M.N I x
  let q:=R.length+1
  IsGeoTestTower ((projectionTest M).geoTransform C π1) R ∧
  wholeTailCuts M0.N Q.N x z R ∧
  ordinaryTraceOrder Q.N B z=(q+1)*ρ ∧
  GermIdealOrder.order (n+1) Q.N B z=(((q+1)*ρ : ℕ) : ℕ∞) ∧
  controlledTailOutput M hM x hx R e z ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H ∧
  HironakaActualMixedTestPowerNormalization.record M H=Q ∧
  Q.N=Q0.N ∧ Q.E=Q0.E ∧
  HironakaActualMixedTestPowerNormalization.baseMap H=
    (Prod.fst : projectionAmbient X→X)∘T.proj ∧
  HironakaActualMixedTestPowerNormalization.baseMap H z=x ∧
  HironakaActualMixedTestPowerNormalization.length H=q+1 ∧
  HironakaActualMixedTestPowerNormalization.projections H=1 ∧
  T.length=q ∧ Q.d=d ∧ Q.E.length=M0.E.length+1+q ∧
  (ρ=d→ ordinaryTraceOrder Q.N Q.ideal z=d) ∧
  IsOpen V ∧ z∈V ∧
  Q.E.map (fun K=>V∩K)=
    List.ofFn (fun i : Fin M0.E.length=>
      {v : Z | v∈V ∧ x∈M0.E.get i ∧ e v∈coordSubspace (SE i)}) ++
      [(∅ : Set Z)] ++ List.replicate R.length (∅ : Set Z) ++
      [V∩{v | e v (Fin.last n)=0}]

private abbrev sameNextGeometry {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    (Q0 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1)))
    (s t : NativeTailState Q0 a) : Prop :=
  ∃ (c2 : FlatChart (n+1) ({tailPoint s} : Set s.1))
    (hπ2 : IsBlowupAlong (n+1) ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1))),
    c2.y₀=tailPoint s ∧ c2.k=0 ∧ c2.j=Fin.last n ∧
    c2.invFun 0∈c2.source ∧ c2.toFun (c2.invFun 0)=0 ∧
    blowupProj (n+1) ({tailPoint s} : Set s.1) (c2.invFun 0)=tailPoint s ∧
    (∀v∈c2.source,
      blowupProj (n+1) ({tailPoint s} : Set s.1) v∈s.2.2.1.source ∧
      s.2.2.1 (blowupProj (n+1) ({tailPoint s} : Set s.1) v)=
        monomial 0 (Fin.last n) (c2.toFun v)) ∧
    HEq t.1 (CMfd.of (n:=n+1) (BlowupSpace (n+1) ({tailPoint s} : Set s.1))) ∧
    HEq t.2.1 (BlowupTower.step
      (Z:=CMfd.of (n:=n+1) (BlowupSpace (n+1) ({tailPoint s} : Set s.1)))
      s.2.1 ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1)) hπ2) ∧
    HEq t.2.2.1 c2.homeo ∧ HEq (tailPoint t) (c2.invFun 0)
private abbrev bornAtState {n : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 (blowupProj (n+1) C0) hπ1
  let T:=A.append s.2.1
  let Q:=(projectionTest M).geoTransformAlong T
  let Q0:=(projectionTest M0).geoTransformAlong T
  let D : Set s.1:=Q0.E.getLastD ∅
  let C : Set s.1:=Q0.N∩D
  let β:=(s.2.1.length+1)*(ordinaryTraceOrder M.N I x-d)
  Q.N=Q0.N ∧ Q.E=Q0.E ∧ tailPoint s∈D ∧ C.Nonempty ∧
  IsClosedSubmanifold (n+1) C ∧ HasNormalCrossings (n+1) C Q0.E ∧
  (∀y∈C, divExpAlong (n+1) Q.N Q.ideal D y=β ∧
    (∀e : ℕ,IsDivNearAlong (n+1) Q.N Q.ideal D e y ↔ e≤β) ∧
    IsDivNearAlong (n+1) Q.N Q.ideal D β y ∧
    ¬IsDivNearAlong (n+1) Q.N Q.ideal D (β+1) y ∧
    ∀f : s.1→ℂ,Q.ideal.mem y f→
      ∃g,(idealPow (vanishingIdeal (n:=n+1) C) β).mem y g ∧
        ∀ᶠz in 𝓝 y,z∈Q.N→f z=g z) ∧
  (Q.IsAdmissibleCentre C ↔ d≤β)

private abbrev queryWithBornAtState {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp) : Prop :=
  queryAtState M0 x hπ1 c SE U s I d hM hx ∧ bornAtState M0 x hπ1 c s I d

private abbrev sharedBornFamilyOutput {n k0 : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (hM0 : IsInvDomain k0 M0) (x : X) (hx0 : x∈M0.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M0 hM0 x hx0 Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M0).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M0 hM0 x hx0).2
  ∃ h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
    IsGeoTestTower Q0 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0,
  ∃ Next : NativeTailState Q0 a→NativeTailState Q0 a,
    (∀s,sameNextGeometry Q0 a s (Next s)) ∧
    let s0 : NativeTailState Q0 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
    let F : ℕ→NativeTailState Q0 a:=Nat.rec s0 (fun _ s=>Next s)
    F 0=s0 ∧ (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=Next (F r)) ∧
    ∀ (I : GermIdeal n X) (d k : ℕ)
      (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
      (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp),
      initialQueryOutput M0 x I d hM hx ∧
      ∀r : ℕ,queryWithBornAtState M0 x hπ1 c SE U (F r) I d hM hx




private abbrev twoRecordBornFamilyOutput {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 : MarkedIdeal n X) (hM1 : IsInvDomain k1 M1) (x : X) (hx1 : x∈M1.cosupp)
    (M2 : MarkedIdeal n X) (hM2 : IsInvDomain k2 M2) (hx2 : x∈M2.cosupp)
    (h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M1.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M1 hM1 x hx1 Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M1).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M1 hM1 x hx1).2
  ∃ h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
    IsGeoTestTower Q0 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0,
  ∃ Next : NativeTailState Q0 a→NativeTailState Q0 a,
    (∀s,sameNextGeometry Q0 a s (Next s)) ∧
    let s0 : NativeTailState Q0 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
    let F : ℕ→NativeTailState Q0 a:=Nat.rec s0 (fun _ s=>Next s)
    F 0=s0 ∧ (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=Next (F r)) ∧
    initialQueryOutput M1 x M1.ideal M1.d hM1 hx1 ∧
    initialQueryOutput M1 x M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2) ∧
    ∀r : ℕ,
      queryWithBornAtState M1 x hπ1 c SE U (F r) M1.ideal M1.d hM1 hx1 ∧
      queryWithBornAtState M1 x hπ1 c SE U (F r) M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2)



private abbrev sharedFamilyOutput {n k0 : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (hM0 : IsInvDomain k0 M0) (x : X) (hx0 : x∈M0.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M0 hM0 x hx0 Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M0).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M0 hM0 x hx0).2
  ∃ h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
    IsGeoTestTower Q0 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0,
  ∃ Next : NativeTailState Q0 a→NativeTailState Q0 a,
    (∀s,sameNextGeometry Q0 a s (Next s)) ∧
    let s0 : NativeTailState Q0 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
    let F : ℕ→NativeTailState Q0 a:=Nat.rec s0 (fun _ s=>Next s)
    F 0=s0 ∧ (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=Next (F r)) ∧
    ∀ (I : GermIdeal n X) (d k : ℕ)
      (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
      (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp),
      initialQueryOutput M0 x I d hM hx ∧
      ∀r : ℕ,queryAtState M0 x hπ1 c SE U (F r) I d hM hx




/-- The actual reference successor supplies this SAME native map. Dependent
ambient/tower/point equalities are eliminated, never replaced by a new choice. -/
private theorem actual_successor {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    (Q0 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1)))
    (s t : NativeTailState Q0 a) (h : sameNextGeometry Q0 a s t) :
    ∃(π : t.1→s.1)
      (hπ : IsBlowupAlong (n+1) ({tailPoint s} : Set s.1) π),
      t.2.1=BlowupTower.step (Z:=t.1) s.2.1 ({tailPoint s} : Set s.1) π hπ ∧
      π (tailPoint t)=tailPoint s := by
  rcases t with ⟨Z,R,e,z,hz⟩
  rcases h with ⟨c2,hπ2,_hCentre,_hCodim,_hPivot,_hSource,_hZero,hProjects,
    _hVector,hZ,hR,_he,hPoint⟩
  have hZ' : Z=CMfd.of (n:=n+1) (BlowupSpace (n+1) ({tailPoint s} : Set s.1)) :=
    eq_of_heq hZ
  cases hZ'
  have hR' : R=BlowupTower.step
      (Z:=CMfd.of (n:=n+1) (BlowupSpace (n+1) ({tailPoint s} : Set s.1)))
      s.2.1 ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1)) hπ2 := eq_of_heq hR
  have hPoint' : z=c2.invFun 0 := eq_of_heq hPoint
  exact ⟨blowupProj (n+1) ({tailPoint s} : Set s.1),hπ2,hR',hPoint' ▸ hProjects⟩

private abbrev currentQuery {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ) : Prop :=
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 (blowupProj (n+1) C0) hπ1
  let T:=A.append s.2.1
  let Q:=(projectionTest M).geoTransformAlong T
  let ρ:=ordinaryTraceOrder M.N I x
  let q:=s.2.1.length+1
  IsGeoTestTower (projectionTest M) T ∧ IsInvDomain (k+1) Q ∧
  Q.d=d ∧ tailPoint s∈Q.cosupp ∧
  ordinaryTraceOrder Q.N Q.ideal (tailPoint s)=ρ+q*(ρ-d)

private theorem current_dictionary {n k : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp)
    (hQuery : queryAtState M0 x hπ1 c SE U s I d hM hx) :
    currentQuery (k:=k) M0 x hπ1 c s I d := by
  have hCtl:=hQuery.2.2.2.2.1
  rcases hCtl with ⟨hT,hRecord,hDom,hMark,_hELen,_hB,_hLeft,_hRight,
    _hSpan,_hFGood,_hFBad,_hFOrd,_hSum,_hGood,_hBad,hNat,_hOrd,_hd,hCos,_hAdmiss⟩
  dsimp only [currentQuery]
  rw [←hRecord]
  exact ⟨hT,hDom,hMark,hCos,hNat⟩

/-- Every birth assertion is derived from the SAME actual last native step;
all premises are internally supplied by the ordinary shared-family producer. -/
private theorem born_at_actual_step {n k j : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SE : Fin M0.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M0).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo)
    (I : GermIdeal n X) (d : ℕ)
    (hM : IsInvDomain k (⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X))
    (hx : x∈(⟨M0.N,M0.E,I,d⟩ : MarkedIdeal n X).cosupp)
    (hQuery : queryAtState M0 x hπ1 c SE U s I d hM hx)
    {W : CMfd.{u} (n+1)} (S : MarkedIdeal (n+1) W) (hS : IsInvDomain j S)
    (y : W) (hy : y∈S.cosupp) (π : s.1→W)
    (hπ : IsBlowupAlong (n+1) ({y} : Set W) π)
    (hRecord :
      let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
      let C0 : Set (projectionAmbient X):={(x,0)}
      let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
      let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0
        (blowupProj (n+1) C0) hπ1
      (projectionTest M).geoTransformAlong (A.append s.2.1)=S.geoTransform ({y} : Set W) π)
    (hOrigin : π (tailPoint s)=y)
    (hBeta : ordinaryTraceOrder S.N S.ideal y-S.d=
      (s.2.1.length+1)*(ordinaryTraceOrder M0.N I x-d)) :
    bornAtState M0 x hπ1 c s I d := by
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0
    (blowupProj (n+1) C0) hπ1
  let T:=A.append s.2.1
  let Q:=(projectionTest M).geoTransformAlong T
  let Q0:=(projectionTest M0).geoTransformAlong T
  let D : Set s.1:=Q0.E.getLastD ∅
  let C : Set s.1:=Q0.N∩D
  let β:=(s.2.1.length+1)*(ordinaryTraceOrder M0.N I x-d)
  change Q=S.geoTransform ({y} : Set W) π at hRecord
  have hGeometry : Q.N=Q0.N ∧ Q.E=Q0.E := by
    have hG:=hQuery.2.2.2.2.2.2.2.1
    have hE:=hQuery.2.2.2.2.2.2.2.2.1
    constructor
    · simpa only [Q,Q0,T,geoTransformAlong_append,A,geoTransformAlong_step,geoTransformAlong_refl] using hG
    · simpa only [Q,Q0,T,geoTransformAlong_append,A,geoTransformAlong_step,geoTransformAlong_refl] using hE
  have hD : D=π ⁻¹' ({y} : Set W) := by
    change Q0.E.getLastD ∅=π ⁻¹' ({y} : Set W)
    rw [←hGeometry.2,hRecord]
    simp [geoTransform]
  have hTrace : C=(S.geoTransform ({y} : Set W) π).N∩π ⁻¹' ({y} : Set W) := by
    change Q0.N∩D=_
    rw [←hGeometry.1,hD,hRecord]
  have hCurrent:=current_dictionary M0 x hπ1 c SE U s I d hM hx hQuery
  rcases hCurrent with ⟨_hT,hDom,hMark,hCos,_hOrder⟩
  have hzD : tailPoint s∈D := by rw [hD];exact mem_singleton_iff.mpr hOrigin
  have hNonempty : C.Nonempty :=
    ⟨tailPoint s,hGeometry.1 ▸ MarkedIdeal.cosupp_subset_N Q hCos,hzD⟩
  have hMarkS : S.d=d := by
    have hh:=hMark
    change Q.d=d at hh
    rw [hRecord] at hh
    exact hh
  have hBorn:=actual_singleton_born_trace S hS y hy hπ
  rcases hBorn with ⟨_hCentre,_hDom,_hMark,_hWord,_hFinite,hExp,hClosed,hNC,hCriterion⟩
  rw [hBeta] at hExp hCriterion
  rw [hMarkS] at hCriterion
  have hNotEmpty : (S.geoTransform ({y} : Set W) π).N∩π ⁻¹' ({y} : Set W)≠∅ := by
    rw [←hTrace]
    exact hNonempty.ne_empty
  simp only [hNotEmpty,false_or] at hCriterion
  have hClosedC : IsClosedSubmanifold (n+1) C := by rw [hTrace];exact hClosed
  have hNCC : HasNormalCrossings (n+1) C Q0.E := by
    rw [hTrace,←hGeometry.2,hRecord]
    exact hNC
  have hAll : ∀z∈C,divExpAlong (n+1) Q.N Q.ideal D z=β ∧
      ∀e : ℕ,IsDivNearAlong (n+1) Q.N Q.ideal D e z ↔ e≤β := by
    rw [hTrace,hD,hRecord]
    exact hExp
  have hIdeal : ∀z∈C,∀f : s.1→ℂ,Q.ideal.mem z f→
      ∃g,(idealPow (vanishingIdeal (n:=n+1) C) β).mem z g ∧
        ∀ᶠv in 𝓝 z,v∈Q.N→f v=g v := by
    intro z hz f hf
    have hzN : z∈Q.N := hGeometry.1.symm ▸ hz.1
    obtain ⟨rN,hrN⟩:=hDom.isWellFormed.isClosedSubmanifold_N.2 z hzN
    obtain ⟨r,hr⟩:=exists_isLocalRetraction hrN
    obtain ⟨rC,hrC⟩:=hClosedC.2 z hz
    have hSet : Q.N∩D=C := congrArg (fun A : Set s.1=>A∩D) hGeometry.1
    have hrC' : RegularAtDim (n:=n+1) (Q.N∩D) z rC := hSet.symm ▸ hrC
    have hDiv : IsDivNearAlong (n+1) Q.N Q.ideal D β z := ((hAll z hz).2 β).mpr le_rfl
    obtain ⟨g,hg,hEq⟩:=(isDivNearAlong_iff hDom.isWellFormed.isCoherent hr hrC').mp hDiv f hf
    rw [hSet] at hg
    exact ⟨g,hg,hEq⟩
  dsimp only [bornAtState]
  refine ⟨hGeometry.1,hGeometry.2,hzD,hNonempty,hClosedC,hNCC,?_,?_⟩
  · intro z hz
    have hh:=hAll z hz
    exact ⟨hh.1,hh.2,(hh.2 β).mpr le_rfl,
      (fun h=>Nat.not_succ_le_self β ((hh.2 (β+1)).mp h)),hIdeal z hz⟩
  · change Q.IsAdmissibleCentre C ↔ d≤β
    rw [hTrace,hRecord]
    exact hCriterion

/-- The actual S01 geometry is retained before all queried ideals and marks;
only the EVERY-point whole-born-trace conclusions are new. -/
private theorem exists_shared_born_family {n k0 : ℕ} {X : CMfd.{u} n}
    (M0 : MarkedIdeal n X) (hM0 : IsInvDomain k0 M0) (x : X) (hx0 : x∈M0.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M0.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      sharedBornFamilyOutput M0 hM0 x hx0 Φ Φs c SN SE U := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hFamily⟩:=
    HironakaActualSharedRecursivePointTests.exists_shared_recursive_point_tests M0 hM0 x hx0
  change sharedFamilyOutput M0 hM0 x hx0 Φ Φs c SN SE U at hFamily
  let C0 : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C0)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C0
  let Q0 : MarkedIdeal (n+1) Y1:=(projectionTest M0).geoTransform C0 π1
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
    (projection_point_centre M0 hM0 x hx0).2
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C0 π1 hπ1
  rcases hFamily with ⟨hWhole,h0,Next,hNext,hData⟩
  extract_lets s0 F at hData
  change ℕ→NativeTailState Q0 c.homeo at F
  rcases hData with ⟨hZero,hLen,hSucc,hQueries⟩
  have hWholeCopy:=hWhole
  rcases hWholeCopy with ⟨_hΦsrc,_hΦ0,_hcp,_hck,_hcj,_hOld,_hLast,_hSourceN,_hSourceE,
    _hSN,_hSE,_h0c,_hzSource,hFirstOrigin,_hRest⟩
  have hActualSucc (r : ℕ) :
      ∃(π : (F (r+1)).1→(F r).1)
        (hπ : IsBlowupAlong (n+1) ({tailPoint (F r)} : Set (F r).1) π),
        (F (r+1)).2.1=BlowupTower.step (Z:=(F (r+1)).1)
          (F r).2.1 ({tailPoint (F r)} : Set (F r).1) π hπ ∧
        π (tailPoint (F (r+1)))=tailPoint (F r) := by
    rw [hSucc r]
    exact actual_successor Q0 c.homeo (F r) (Next (F r)) (hNext (F r))
  refine ⟨Φ,Φs,c,SN,SE,U,hWhole,?_⟩
  dsimp only [sharedBornFamilyOutput]
  refine ⟨h0,Next,hNext,hZero,hLen,hSucc,?_⟩
  intro I d k hM hx
  let M : MarkedIdeal n X:=⟨M0.N,M0.E,I,d⟩
  let P:=projectionTest M
  let p : projectionAmbient X:=(x,0)
  obtain ⟨hInit,hAll⟩:=hQueries I d k hM hx
  have hInitCopy:=hInit
  rcases hInitCopy with ⟨_hQueries,hP,hpCos,_hPN,_hPI,hPd,_hPE,_hPLen,hdρ,
    _hSourceOrder,hPNat,_hPOrder,_hRest⟩
  change d≤ordinaryTraceOrder M0.N I x at hdρ
  refine ⟨hInit,?_⟩
  intro r
  refine ⟨hAll r,?_⟩
  cases r with
  | zero =>
    have hq:=hAll 0
    rw [hZero] at hq
    change bornAtState M0 x hπ1 c s0 I d
    apply born_at_actual_step M0 x hπ1 c SE U _ I d hM hx hq P hP p hpCos π1 hπ1
    · rfl
    · exact hFirstOrigin
    · dsimp only [tailPoint]
      rw [hPNat,hPd]
      change ordinaryTraceOrder M0.N I x-d=1*(ordinaryTraceOrder M0.N I x-d)
      exact (Nat.one_mul _).symm
  | succ r =>
    obtain ⟨π,hπ,hRStep,hOrigin⟩:=hActualSucc r
    let S:=(projectionTest M).geoTransformAlong (A.append (F r).2.1)
    have hPrev:=current_dictionary M0 x hπ1 c SE U (F r) I d hM hx (hAll r)
    rcases hPrev with ⟨_hPrevTest,hPrevDom,hPrevMark,hPrevCos,hPrevOrder⟩
    change ordinaryTraceOrder S.N S.ideal (tailPoint (F r))=
      ordinaryTraceOrder M0.N I x+((F r).2.1.length+1)*(ordinaryTraceOrder M0.N I x-d) at hPrevOrder
    apply born_at_actual_step M0 x hπ1 c SE U (F (r+1)) I d hM hx (hAll (r+1))
      S hPrevDom (tailPoint (F r)) hPrevCos π hπ
    · change (projectionTest M).geoTransformAlong (A.append (F (r+1)).2.1)=_
      rw [hRStep,BlowupTower.append_step]
      rfl
    · exact hOrigin
    · rw [hPrevOrder,hPrevMark,hLen r,hLen (r+1)]
      simp only [Nat.add_mul,Nat.one_mul]
      omega

/-- Only the TWO ordinary original records, identical whole N/E, and common
original cosupport point are inputs. BOTH whole trace laws use the SAME F/Hq. -/
theorem exists_two_record_shared_born_trace_tests {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 M2 : MarkedIdeal n X) (hM1 : IsInvDomain k1 M1) (hM2 : IsInvDomain k2 M2)
    (x : X) (hx1 : x∈M1.cosupp) (hx2 : x∈M2.cosupp)
    (hN : M2.N=M1.N) (hE : M2.E=M1.E) :
    ∃(h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2)
      (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M1.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      twoRecordBornFamilyOutput M1 hM1 x hx1 M2 hM2 hx2 h2 Φ Φs c SN SE U := by
  have h2 : (⟨M1.N,M1.E,M2.ideal,M2.d⟩ : MarkedIdeal n X)=M2 := by
    cases M2 with
    | mk N2 E2 I2 d2 =>
      change N2=M1.N at hN
      change E2=M1.E at hE
      cases hN
      cases hE
      rfl
  obtain ⟨Φ,Φs,c,SN,SE,U,hFamily⟩:=exists_shared_born_family M1 hM1 x hx1
  rcases hFamily with ⟨hWhole,h0,Next,hNext,hZero,hLen,hSucc,hQueries⟩
  refine ⟨h2,Φ,Φs,c,SN,SE,U,hWhole,?_⟩
  dsimp only [twoRecordBornFamilyOutput]
  refine ⟨h0,Next,hNext,hZero,hLen,hSucc,?_⟩
  have hQuery1:=hQueries M1.ideal M1.d k1 hM1 hx1
  have hQuery2:=hQueries M2.ideal M2.d k2 (h2.symm ▸ hM2) (h2.symm ▸ hx2)
  exact ⟨hQuery1.1,hQuery2.1,fun r=>⟨hQuery1.2 r,hQuery2.2 r⟩⟩

end
end Hironaka.HironakaActualSharedBornTraceTests
