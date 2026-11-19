import Hironaka.Resolution.HironakaActualSharedCartierTraceTests
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProjectedNormalizedOrderDetection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  ResolutionInvariantSpec RelativePrincipalizationSpan DivisorExponentAlong
  HironakaSharpOriginalProductTraceOrder HironakaActualProjectionTestRecord
  HironakaActualSharedCartierTraceTests
open MarkedIdealEquivalence.MarkedIdeal
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
  RestrictedIdealWeight RestrictedIdealQuotient NonmonomialOrderLocal
  HironakaActualCartierTraceSuccessor HironakaActualPolymorphicBornExponent
  MemberInterAlong DivisorExponentAlong
open HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci
open scoped ProductComplexManifold

/-! Native P09 count geometry and whole-record outputs. The recursive
geometric state has no ideal, mark, admissibility or native-test field.
Blueprint FIRST: `hironaka-actual-shared-cartier-trace-tests.tex`. -/


/-- OUTPUT ONLY: true finite ordinary order from the original native domain.
This predicate is never an ordinary caller premise. -/
abbrev OriginalFiniteOrderOutput {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (x : X) : Prop :=
  let rho := ordinaryTraceOrder M.N M.ideal x
  M.d≤rho ∧ GermIdealOrder.order n M.N M.ideal x=(rho : ℕ∞) ∧
  x∈cosupport n M.N M.ideal rho ∧ x∉cosupport n M.N M.ideal (rho+1) ∧
  ∃ g : X→ℂ,M.ideal.mem x g ∧ ¬VanishesToOrderOn n M.N x (rho+1) g

/-- OUTPUT ONLY: the SAME deterministic original projection history and
whole record dictionaries for a genuine controlled witness T. B is the
actual original record; h2 is produced from the given whole N/E equalities. -/
abbrev ProjectedWitnessDictionary {n : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X)
    (_h2 : (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)=B)
    {Y : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Y) : Prop :=
  let Br : MarkedIdeal n X := ⟨A.N,A.E,B.ideal,B.d⟩
  let H := HironakaActualProjectionTowerHistory.projectionTowerHistory A T
  let QA := (projectionTest A).geoTransformAlong T
  let QB := (projectionTest B).geoTransformAlong T
  HironakaActualMixedTestPowerNormalization.record A H=QA ∧
  HironakaActualMixedTestPowerNormalization.record Br H=QB ∧
  (HironakaActualMixedTestPowerNormalization.IsTest A H ↔ IsGeoTestTower (projectionTest A) T) ∧
  (HironakaActualMixedTestPowerNormalization.IsTest Br H ↔ IsGeoTestTower (projectionTest B) T) ∧
  QA.N=QB.N ∧ QA.E=QB.E ∧ QA.d=A.d ∧ QB.d=B.d ∧
  HironakaActualMixedTestPowerNormalization.projections H=1 ∧
  HironakaActualMixedTestPowerNormalization.length H=T.length+1 ∧
  HironakaActualMixedTestPowerNormalization.baseMap H=
    (Prod.fst : projectionAmbient X→X)∘T.proj ∧
  QA.E.length=A.E.length+1+T.length ∧ QB.E.length=A.E.length+1+T.length


private theorem original_finite_order {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    OriginalFiniteOrderOutput M x := by
  let rho := ordinaryTraceOrder M.N M.ideal x
  have hxN := M.cosupp_subset_N hx
  have hI := hM.isWellFormed.isCoherent
  have hCrit (e : ℕ) : x∈cosupport n M.N M.ideal e ↔ e≤rho :=
    ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N hI hM.isNonzeroAlongAt hxN e
  have hGood := (hCrit rho).mpr le_rfl
  have hBad : x∉cosupport n M.N M.ideal (rho+1) :=
    fun h=>Nat.not_succ_le_self rho ((hCrit (rho+1)).mp h)
  have hOrder : GermIdealOrder.order n M.N M.ideal x=(rho : ℕ∞) := by
    apply le_antisymm
    · apply ENat.lt_natCast_add_one_iff.mp
      apply lt_of_not_ge
      intro h
      exact hBad ⟨hGood.1,(le_order_iff (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg)).mp
        (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
    · exact (le_order_iff (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg)).mpr hGood.2
  refine ⟨(hCrit M.d).mp hx,hOrder,hGood,hBad,?_⟩
  by_contra hn
  push Not at hn
  exact hBad ⟨hxN,hn⟩

private theorem projected_witness_dictionary {n : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (h2 : (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)=B)
    {Y : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Y) :
    ProjectedWitnessDictionary A B h2 T := by
  let Br : MarkedIdeal n X := ⟨A.N,A.E,B.ideal,B.d⟩
  let H := HironakaActualProjectionTowerHistory.projectionTowerHistory A T
  let QA := (projectionTest A).geoTransformAlong T
  let QB := (projectionTest B).geoTransformAlong T
  have hRA : HironakaActualMixedTestPowerNormalization.record A H=QA :=
    HironakaActualSharedRecursivePointTests.shared_projection_history_record A A.ideal A.d T
  have hBr : (projectionTest Br).geoTransformAlong T=QB :=
    congrArg (fun M : MarkedIdeal n X=>(projectionTest M).geoTransformAlong T) h2
  have hRB : HironakaActualMixedTestPowerNormalization.record Br H=QB :=
    (HironakaActualSharedRecursivePointTests.shared_projection_history_record A B.ideal B.d T).trans hBr
  have hTestA := HironakaActualSharedRecursivePointTests.shared_projection_history_test_iff A A.ideal A.d T
  have hTestB := HironakaActualSharedRecursivePointTests.shared_projection_history_test_iff A B.ideal B.d T
  have hBTest : IsGeoTestTower (projectionTest Br) T = IsGeoTestTower (projectionTest B) T :=
    congrArg (fun M : MarkedIdeal n X=>IsGeoTestTower (projectionTest M) T) h2
  have hN : QA.N=QB.N := by
    calc
      _ = (HironakaActualMixedTestPowerNormalization.record A H).N :=
        congrArg (fun M : MarkedIdeal (n+1) Y=>M.N) hRA.symm
      _ = (HironakaActualMixedTestPowerNormalization.record Br H).N := rfl
      _ = QB.N := congrArg (fun M : MarkedIdeal (n+1) Y=>M.N) hRB
  have hE : QA.E=QB.E := by
    calc
      _ = (HironakaActualMixedTestPowerNormalization.record A H).E :=
        congrArg (fun M : MarkedIdeal (n+1) Y=>M.E) hRA.symm
      _ = (HironakaActualMixedTestPowerNormalization.record Br H).E := rfl
      _ = QB.E := congrArg (fun M : MarkedIdeal (n+1) Y=>M.E) hRB
  have hDict := HironakaActualProjectionTowerHistory.projectionTowerHistory_dictionary A T
  refine ⟨hRA,hRB,hTestA,hTestB.trans (Iff.of_eq hBTest),hN,hE,?_,?_,
    hDict.2.1,hDict.1,hDict.2.2.1,hDict.2.2.2,?_⟩
  · exact d_geoTransformAlong (projectionTest A) T
  · exact d_geoTransformAlong (projectionTest B) T
  · calc
      _ = QA.E.length := congrArg List.length hE.symm
      _ = A.E.length+1+T.length := hDict.2.2.2

private theorem product_count_arithmetic (dA dB rhoA rhoB : ℕ)
    (hdA : 0<dA) (hdB : 0<dB) (hA : dA≤rhoA) (hB : dB≤rhoB) :
    let q := dA*dB
    let a := dB*(rhoA-dA)
    let b := dA*(rhoB-dB)
    q*(rhoA-dA)=a*dA ∧ q*(rhoB-dB)=b*dB ∧
    (q*(rhoA-dA))/dA=a ∧ (q*(rhoB-dB))/dB=b ∧
    (dB*rhoA=dA*rhoB ↔ a=b) := by
  let q := dA*dB
  let a := dB*(rhoA-dA)
  let b := dA*(rhoB-dB)
  have hFA : q*(rhoA-dA)=a*dA := by dsimp [q,a];ring
  have hFB : q*(rhoB-dB)=b*dB := by dsimp [q,b];ring
  have hOA : dB*rhoA=dA*dB+a := by
    calc
      _ = dB*(dA+(rhoA-dA)) := congrArg (fun t=>dB*t) (Nat.add_sub_of_le hA).symm
      _ = dA*dB+a := by dsimp [a];ring
  have hOB : dA*rhoB=dA*dB+b := by
    calc
      _ = dA*(dB+(rhoB-dB)) := congrArg (fun t=>dA*t) (Nat.add_sub_of_le hB).symm
      _ = dA*dB+b := by dsimp [b];ring
  refine ⟨hFA,hFB,?_,?_,?_⟩
  · rw [hFA,Nat.mul_div_cancel _ hdA]
  · rw [hFB,Nat.mul_div_cancel _ hdB]
  · rw [hOA,hOB]
    omega

private theorem multiply_cut_iff (s a d : ℕ) (hd : 0<d) :
    s*d≤a*d ↔ s≤a := by
  constructor
  · intro h
    by_contra hn
    have hlt := Nat.mul_lt_mul_of_pos_right (show a<s by omega) hd
    omega
  · exact Nat.mul_le_mul_right d

/- Exact PRIVATE copies of accepted complete P09 output descriptors and
current dictionary. No imported private declaration is called; no engine
or duplicate leaf credit is attached to these definition/proof copies. -/
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




private abbrev p08TwoRecordOutput {n k1 k2 : ℕ} {X : CMfd.{u} n}
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


private abbrev cartierAtState {n k1 k2 : ℕ} {X : CMfd.{u} n}
    (M1 M2 : MarkedIdeal n X) (x : X)
    (hπ1 : IsBlowupAlong (n+1) ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (s : NativeTailState (Y1:=CMfd.of (n:=n+1)
      (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M1).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo) : Prop :=
  let C0 : Set (projectionAmbient X) := {(x,0)}
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C0)
  let A : BlowupTower (projectionAmbient X) Y1 := .step .refl C0 (blowupProj (n+1) C0) hπ1
  let T := A.append s.2.1
  let Q1 := (projectionTest M1).geoTransformAlong T
  let Q2 := (projectionTest M2).geoTransformAlong T
  let beta1 := (s.2.1.length+1)*(ordinaryTraceOrder M1.N M1.ideal x-M1.d)
  let beta2 := (s.2.1.length+1)*(ordinaryTraceOrder M1.N M2.ideal x-M2.d)
  ∃ G : CartierGeometryFamily s.1,
    HEq (G.state 0).N Q1.N ∧ HEq (G.state 0).E Q1.E ∧
    ((G.state 0).i).val+1=(G.state 0).E.length ∧ HEq (G.state 0).z (tailPoint s) ∧
    CartierQueryCountOutput (k:=k1+1) Q1 beta1 G ∧
    CartierQueryCountOutput (k:=k2+1) Q2 beta2 G ∧
    CartierOriginalHistoryCountOutput M1 M1.ideal M1.d T beta1 (s.2.1.length+1) G ∧
    CartierOriginalHistoryCountOutput M1 M2.ideal M2.d T beta2 (s.2.1.length+1) G

private abbrev twoRecordCartierCountOutput {n k1 k2 : ℕ} {X : CMfd.{u} n}
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
      queryWithBornAtState M1 x hπ1 c SE U (F r) M2.ideal M2.d (h2.symm ▸ hM2) (h2.symm ▸ hx2) ∧
      cartierAtState (k1:=k1) (k2:=k2) M1 M2 x hπ1 c (F r)




private theorem retained_q_counts {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (x : X) (hxA : x∈A.cosupp) (hxB : x∈B.cosupp)
    (hN : B.N=A.N) (hE : B.E=A.E) (q : ℕ) (hq : 0<q) :
    ∃ (_h2 : (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)=B)
      (Yq : CMfd.{u} (n+1)) (Tq : BlowupTower (projectionAmbient X) Yq)
      (G : CartierGeometryFamily Yq),
      Tq.length=q ∧ IsGeoTestTower (projectionTest A) Tq ∧ IsGeoTestTower (projectionTest B) Tq ∧
      CartierQueryCountOutput (k:=kA+1) ((projectionTest A).geoTransformAlong Tq)
        (q*(ordinaryTraceOrder A.N A.ideal x-A.d)) G ∧
      CartierQueryCountOutput (k:=kB+1) ((projectionTest B).geoTransformAlong Tq)
        (q*(ordinaryTraceOrder B.N B.ideal x-B.d)) G ∧
      CartierOriginalHistoryCountOutput A A.ideal A.d Tq
        (q*(ordinaryTraceOrder A.N A.ideal x-A.d)) q G ∧
      CartierOriginalHistoryCountOutput A B.ideal B.d Tq
        (q*(ordinaryTraceOrder B.N B.ideal x-B.d)) q G := by
  obtain ⟨h2,Φ,Φs,c,SN,SE,U,hFamily⟩ :=
    HironakaActualSharedCartierTraceTests.exists_two_record_shared_cartier_trace_test_counts
      A B hA hB x hxA hxB hN hE
  change twoRecordCartierCountOutput A hA x hxA B hB hxB h2 Φ Φs c SN SE U at hFamily
  let C0 : Set (projectionAmbient X) := {(x,0)}
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C0)
  let Q0 := (projectionTest A).geoTransform C0 (blowupProj (n+1) C0)
  let hπ1 := isBlowupAlong_blowupProj (n:=n+1) (C:=C0)
    (projection_point_centre A hA x hxA).2
  rcases hFamily with ⟨_hWhole,h0,Next,_hNext,hData⟩
  extract_lets s0 F at hData
  change ℕ→NativeTailState (Y1:=Y1) Q0 c.homeo at F
  rcases hData with ⟨_hZero,hLen,_hSucc,_hInit1,_hInit2,hAll⟩
  let r := q-1
  have hr : r+1=q := by dsimp [r];omega
  obtain ⟨hq1,hq2,hCartier⟩ := hAll r
  let AF : BlowupTower (projectionAmbient X) Y1 :=
    .step .refl C0 (blowupProj (n+1) C0) hπ1
  let T := AF.append (F r).2.1
  have hTLen : T.length=q := by
    calc
      _ = AF.length+(F r).2.1.length := BlowupTower.length_append AF (F r).2.1
      _ = 1+r := by change 1+(F r).2.1.length=1+r;rw [hLen r]
      _ = q := by omega
  have hCurrA := current_dictionary A x hπ1 c SE U (F r) A.ideal A.d hA hxA hq1.1
  have hCurrB := current_dictionary A x hπ1 c SE U (F r) B.ideal B.d
    (h2.symm ▸ hB) (h2.symm ▸ hxB) hq2.1
  have hTA : IsGeoTestTower (projectionTest A) T := hCurrA.1
  have hTestEq : IsGeoTestTower (projectionTest (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)) T =
      IsGeoTestTower (projectionTest B) T :=
    congrArg (fun M : MarkedIdeal n X=>IsGeoTestTower (projectionTest M) T) h2
  have hTB : IsGeoTestTower (projectionTest B) T := hTestEq ▸ hCurrB.1
  change ∃ G : CartierGeometryFamily (F r).1,
    HEq (G.state 0).N ((projectionTest A).geoTransformAlong T).N ∧
    HEq (G.state 0).E ((projectionTest A).geoTransformAlong T).E ∧
    ((G.state 0).i).val+1=(G.state 0).E.length ∧ HEq (G.state 0).z (tailPoint (F r)) ∧
    CartierQueryCountOutput (k:=kA+1) ((projectionTest A).geoTransformAlong T)
      (((F r).2.1.length+1)*(ordinaryTraceOrder A.N A.ideal x-A.d)) G ∧
    CartierQueryCountOutput (k:=kB+1) ((projectionTest B).geoTransformAlong T)
      (((F r).2.1.length+1)*(ordinaryTraceOrder A.N B.ideal x-B.d)) G ∧
    CartierOriginalHistoryCountOutput A A.ideal A.d T
      (((F r).2.1.length+1)*(ordinaryTraceOrder A.N A.ideal x-A.d)) ((F r).2.1.length+1) G ∧
    CartierOriginalHistoryCountOutput A B.ideal B.d T
      (((F r).2.1.length+1)*(ordinaryTraceOrder A.N B.ideal x-B.d)) ((F r).2.1.length+1) G at hCartier
  obtain ⟨G,_hGN,_hGE,_hLast,_hGz,hCountsA,hCountsB,hOrigA,hOrigB⟩ := hCartier
  have hCount : (F r).2.1.length+1=q := by rw [hLen r,hr]
  rw [hCount] at hCountsA hCountsB hOrigA hOrigB
  rw [←hN] at hCountsB hOrigB
  exact ⟨h2,(F r).1,T,G,hTLen,hTA,hTB,hCountsA,hCountsB,hOrigA,hOrigB⟩

private theorem full_tail_dictionary {n : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (h2 : (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)=B)
    {Yq : CMfd.{u} (n+1)} (Tq : BlowupTower (projectionAmbient X) Yq)
    (G : CartierGeometryFamily Yq) (q a b betaA betaB : ℕ)
    (hLen : Tq.length=q) (hdA : 0<A.d) (hdB : 0<B.d)
    (hFA : betaA=a*A.d) (hFB : betaB=b*B.d)
    (hOrigA : CartierOriginalHistoryCountOutput A A.ideal A.d Tq betaA q G)
    (hOrigB : CartierOriginalHistoryCountOutput A B.ideal B.d Tq betaB q G) :
    ∀ s,let T := Tq.append (G.state s).R
      T.length=q+s ∧ ProjectedWitnessDictionary A B h2 T ∧
      (IsGeoTestTower (projectionTest A) T ↔ s≤a) ∧
      (IsGeoTestTower (projectionTest B) T ↔ s≤b) := by
  intro s
  let T := Tq.append (G.state s).R
  have hTestA := (hOrigA s).2.2.1
  have hTestB := (hOrigB s).2.2.1
  have hTestEq :
      IsGeoTestTower (projectionTest (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)) T =
      IsGeoTestTower (projectionTest B) T :=
    congrArg (fun M : MarkedIdeal n X=>IsGeoTestTower (projectionTest M) T) h2
  have hActualB : IsGeoTestTower (projectionTest B) T ↔ s*B.d≤betaB :=
    (Iff.of_eq hTestEq).symm.trans hTestB
  refine ⟨?_,projected_witness_dictionary A B h2 T,?_,?_⟩
  · calc
      _ = Tq.length+(G.state s).R.length := BlowupTower.length_append Tq (G.state s).R
      _ = q+s := by rw [hLen,G.towerLength]
  · exact hTestA.trans (by rw [hFA];exact multiply_cut_iff s a A.d hdA)
  · exact hActualB.trans (by rw [hFB];exact multiply_cut_iff s b B.d hdB)

/-- ONE actual accepted P09 family is retained at q=dA*dB. Both ordinary
records receive the same native/control history, exact finite counts and
first asymmetric witness; no projected equivalence is assumed. -/
theorem exists_projected_normalized_order_detection_family
    {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (x : X) (hxA : x∈A.cosupp) (hxB : x∈B.cosupp)
    (hN : B.N=A.N) (hE : B.E=A.E) :
    let rhoA := ordinaryTraceOrder A.N A.ideal x
    let rhoB := ordinaryTraceOrder B.N B.ideal x
    let q := A.d*B.d
    let a := B.d*(rhoA-A.d)
    let b := A.d*(rhoB-B.d)
    ∃ h2 : (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)=B,
      OriginalFiniteOrderOutput A x ∧ OriginalFiniteOrderOutput B x ∧ 0<q ∧
      q*(rhoA-A.d)=a*A.d ∧ q*(rhoB-B.d)=b*B.d ∧
      (q*(rhoA-A.d))/A.d=a ∧ (q*(rhoB-B.d))/B.d=b ∧
      (B.d*rhoA=A.d*rhoB ↔ a=b) ∧
      ∃ (Yq : CMfd.{u} (n+1)) (Tq : BlowupTower (projectionAmbient X) Yq)
        (G : CartierGeometryFamily Yq),
        Tq.length=q ∧ IsGeoTestTower (projectionTest A) Tq ∧ IsGeoTestTower (projectionTest B) Tq ∧
        CartierQueryCountOutput (k:=kA+1) ((projectionTest A).geoTransformAlong Tq)
          (q*(rhoA-A.d)) G ∧
        CartierQueryCountOutput (k:=kB+1) ((projectionTest B).geoTransformAlong Tq)
          (q*(rhoB-B.d)) G ∧
        CartierOriginalHistoryCountOutput A A.ideal A.d Tq (q*(rhoA-A.d)) q G ∧
        CartierOriginalHistoryCountOutput A B.ideal B.d Tq (q*(rhoB-B.d)) q G ∧
        (∀ s,
          let T := Tq.append (G.state s).R
          T.length=q+s ∧ ProjectedWitnessDictionary A B h2 T ∧
          (IsGeoTestTower (projectionTest A) T ↔ s≤a) ∧
          (IsGeoTestTower (projectionTest B) T ↔ s≤b)) ∧
        (∀ s≤min a b,
          IsGeoTestTower (projectionTest A) (Tq.append (G.state s).R) ∧
          IsGeoTestTower (projectionTest B) (Tq.append (G.state s).R)) ∧
        (a<b →
          let T := Tq.append (G.state (a+1)).R
          T.length=q+(a+1) ∧ ProjectedWitnessDictionary A B h2 T ∧
          IsGeoTestTower (projectionTest B) T ∧ ¬IsGeoTestTower (projectionTest A) T) ∧
        (b<a →
          let T := Tq.append (G.state (b+1)).R
          T.length=q+(b+1) ∧ ProjectedWitnessDictionary A B h2 T ∧
          IsGeoTestTower (projectionTest A) T ∧ ¬IsGeoTestTower (projectionTest B) T) ∧
        (rhoA=A.d → ∀ s,IsGeoTestTower (projectionTest A) (Tq.append (G.state s).R) ↔ s=0) ∧
        (rhoB=B.d → ∀ s,IsGeoTestTower (projectionTest B) (Tq.append (G.state s).R) ↔ s=0) := by
  let rhoA := ordinaryTraceOrder A.N A.ideal x
  let rhoB := ordinaryTraceOrder B.N B.ideal x
  let q := A.d*B.d
  let a := B.d*(rhoA-A.d)
  let b := A.d*(rhoB-B.d)
  have hFiniteA := original_finite_order A hA x hxA
  have hFiniteB := original_finite_order B hB x hxB
  have hdA : 0<A.d := by have h:=hA.one_le_d;omega
  have hdB : 0<B.d := by have h:=hB.one_le_d;omega
  have hq : 0<q := Nat.mul_pos hdA hdB
  have hMath := product_count_arithmetic A.d B.d rhoA rhoB hdA hdB hFiniteA.1 hFiniteB.1
  rcases hMath with ⟨hFA,hFB,hQA,hQB,hNorm⟩
  obtain ⟨h2,Yq,Tq,G,hLen,hTA,hTB,hCountsA,hCountsB,hOrigA,hOrigB⟩ :=
    retained_q_counts A B hA hB x hxA hxB hN hE q hq
  have hAll := full_tail_dictionary A B h2 Tq G q a b (q*(rhoA-A.d)) (q*(rhoB-B.d))
    hLen hdA hdB hFA hFB hOrigA hOrigB
  refine ⟨h2,hFiniteA,hFiniteB,hq,hFA,hFB,hQA,hQB,hNorm,
    Yq,Tq,G,hLen,hTA,hTB,hCountsA,hCountsB,hOrigA,hOrigB,hAll,?_,?_,?_,?_,?_⟩
  · intro s hs
    exact ⟨((hAll s).2.2.1).mpr (hs.trans (Nat.min_le_left a b)),
      ((hAll s).2.2.2).mpr (hs.trans (Nat.min_le_right a b))⟩
  · intro hab
    change a<b at hab
    have hh := hAll (a+1)
    exact ⟨hh.1,hh.2.1,(hh.2.2.2).mpr (by omega),
      fun h=>Nat.not_succ_le_self a ((hh.2.2.1).mp h)⟩
  · intro hba
    change b<a at hba
    have hh := hAll (b+1)
    exact ⟨hh.1,hh.2.1,(hh.2.2.1).mpr (by omega),
      fun h=>Nat.not_succ_le_self b ((hh.2.2.2).mp h)⟩
  · intro heq s
    have ha0 : a=0 := by dsimp [a,rhoA];rw [heq];simp
    exact ((hAll s).2.2.1).trans (by rw [ha0];omega)
  · intro heq s
    have hb0 : b=0 := by dsimp [b,rhoB];rw [heq];simp
    exact ((hAll s).2.2.2).trans (by rw [hb0];omega)
/-- A normalized mismatch constructs a genuine ordinary controlled tower
on the actual projection ambient, first asymmetric in the SAME returned
Cartier family. Both ACTUAL projected records and all shorter tails remain
explicit; the original history is computed on that very tower. -/
theorem exists_projected_controlled_order_witness
    {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (x : X) (hxA : x∈A.cosupp) (hxB : x∈B.cosupp)
    (hN : B.N=A.N) (hE : B.E=A.E)
    (hDifferent : B.d*ordinaryTraceOrder A.N A.ideal x ≠
      A.d*ordinaryTraceOrder B.N B.ideal x) :
    let rhoA := ordinaryTraceOrder A.N A.ideal x
    let rhoB := ordinaryTraceOrder B.N B.ideal x
    let q := A.d*B.d
    let a := B.d*(rhoA-A.d)
    let b := A.d*(rhoB-B.d)
    ∃ (h2 : (⟨A.N,A.E,B.ideal,B.d⟩ : MarkedIdeal n X)=B)
      (Yq : CMfd.{u} (n+1)) (Tq : BlowupTower (projectionAmbient X) Yq)
      (G : CartierGeometryFamily Yq),
      OriginalFiniteOrderOutput A x ∧ OriginalFiniteOrderOutput B x ∧ Tq.length=q ∧
      (∀ r<min a b+1,
        IsGeoTestTower (projectionTest A) (Tq.append (G.state r).R) ∧
        IsGeoTestTower (projectionTest B) (Tq.append (G.state r).R)) ∧
      let T := Tq.append (G.state (min a b+1)).R
      T.length=q+(min a b+1) ∧ ProjectedWitnessDictionary A B h2 T ∧
      ((IsGeoTestTower (projectionTest A) T ∧ ¬IsGeoTestTower (projectionTest B) T) ∨
       (IsGeoTestTower (projectionTest B) T ∧ ¬IsGeoTestTower (projectionTest A) T)) := by
  let rhoA := ordinaryTraceOrder A.N A.ideal x
  let rhoB := ordinaryTraceOrder B.N B.ideal x
  let a := B.d*(rhoA-A.d)
  let b := A.d*(rhoB-B.d)
  obtain ⟨h2,hFiniteA,hFiniteB,_hq,_hFA,_hFB,_hQA,_hQB,hNorm,
    Yq,Tq,G,hLen,_hTA,_hTB,_hCountsA,_hCountsB,_hOrigA,_hOrigB,
    hAll,hSmall,_hLeft,_hRight,_hZeroA,_hZeroB⟩ :=
    exists_projected_normalized_order_detection_family A B hA hB x hxA hxB hN hE
  have hab : a≠b := fun h=>hDifferent (hNorm.mpr h)
  refine ⟨h2,Yq,Tq,G,hFiniteA,hFiniteB,hLen,?_,?_⟩
  · intro r hr
    have hr' : r≤min a b := by change r<min a b+1 at hr;omega
    exact hSmall r hr'
  · have hh := hAll (min a b+1)
    refine ⟨hh.1,hh.2.1,?_⟩
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have hmin : min a b=a := Nat.min_eq_left (Nat.le_of_lt hlt)
      apply Or.inr
      have hsB : min a b+1≤b := by rw [hmin];omega
      refine ⟨(hh.2.2.2).mpr hsB,?_⟩
      intro ht
      have hsA : min a b+1≤a := (hh.2.2.1).mp ht
      rw [hmin] at hsA
      omega
    · have hmin : min a b=b := Nat.min_eq_right (Nat.le_of_lt hlt)
      apply Or.inl
      have hsA : min a b+1≤a := by rw [hmin];omega
      refine ⟨(hh.2.2.1).mpr hsA,?_⟩
      intro ht
      have hsB : min a b+1≤b := (hh.2.2.2).mp ht
      rw [hmin] at hsB
      omega

/-- Existing weak equivalence of the ACTUAL projected records is used only
on the already constructed actual ordinary controlled witness. No transfer
from ordinary weak equivalence of the original records is asserted. -/
theorem normalized_ordinary_order_of_projected_wEquiv
    {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (x : X) (hxA : x∈A.cosupp) (hxB : x∈B.cosupp)
    (hN : B.N=A.N) (hE : B.E=A.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B)) :
    OriginalFiniteOrderOutput A x ∧ OriginalFiniteOrderOutput B x ∧
      B.d*ordinaryTraceOrder A.N A.ideal x=A.d*ordinaryTraceOrder B.N B.ideal x := by
  refine ⟨original_finite_order A hA x hxA,original_finite_order B hB x hxB,?_⟩
  by_contra hDifferent
  obtain ⟨h2,Yq,Tq,G,_hFiniteA,_hFiniteB,_hLen,_hSmall,hResult⟩ :=
    exists_projected_controlled_order_witness A B hA hB x hxA hxB hN hE hDifferent
  let a := B.d*(ordinaryTraceOrder A.N A.ideal x-A.d)
  let b := A.d*(ordinaryTraceOrder B.N B.ideal x-B.d)
  let T := Tq.append (G.state (min a b+1)).R
  rcases hResult with ⟨_hLength,_hDict,hAsym⟩
  rcases hAsym with hOnlyA | hOnlyB
  · exact hOnlyA.2 (((hProjected.2 T).1).mp hOnlyA.1)
  · exact hOnlyB.2 (((hProjected.2 T).1).mpr hOnlyB.1)

end
end Hironaka.HironakaActualProjectedNormalizedOrderDetection
