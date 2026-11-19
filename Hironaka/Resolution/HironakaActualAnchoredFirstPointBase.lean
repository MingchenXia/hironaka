import Hironaka.Resolution.HironakaActualAnchoredSuccessorTest
import Hironaka.Resolution.HironakaActualProjectionTowerHistory
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeOrder
import Hironaka.Resolution.HironakaActualAnchoredBoundaryMasks
import Hironaka.Resolution.HironakaActualInheritedVerticalPointChart

/-! The genuine original projection and FIRST point test are derived BEFORE
the empty-tail test. ONE accepted G04 seed retains all callbacks for later
recursion; no all-q family or normalized-order/CAN claim is made. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredFirstPointBase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  NormalCrossings BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec RelativePrincipalizationSpan InvertibleIdealQuotient
  GiraudAlong GermIdealTotalTransform GermIdealPullbackCalculus GermIdealOrder
  IdealOrderArithmetic IdealWeightPowers CompanionReductionAlong RestrictedIdealWeight
  HironakaSharpOriginalProductTraceOrder HironakaActualAnchoredVerticalChart
  HironakaActualAnchoredControlledOrder HironakaActualAnchoredStrictCarrierMask
  HironakaActualAnchoredBoundaryMasks HironakaActualInheritedVerticalPointChart
  HironakaActualProjectionTestRecord HironakaActualProjectionVerticalBlowupChart
open scoped ProductComplexManifold

open HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetRankLoci
  HironakaSmoothSubmersionRelativeOrder HironakaAuxiliaryGraphGeometry InvDomainTowerAlong

private instance point_closed_fact {a : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X] (x : X) :
    Fact (IsClosedSubmanifold a ({x} : Set X)) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1⟩

private def oldMask {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter fun i=>i.castAdd 1∈S

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

private abbrev sharpTailOutput {n : ℕ} {X : CMfd.{u} n}
    {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    {Z : CMfd.{u} (n+1)} (M : MarkedIdeal n X) (g : X→ℂ) (ρ : ℕ)
    (Nt : Set Z) (z : Z) (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z) : Prop :=
  let κ : Z→X:=(Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj
  let B:=GermIdeal.pullback (m:=n+1) R.proj
    (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
      (GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal))
  let μ:=(R.length+2)*ρ
  z∈cosupport (n+1) Nt B μ ∧ z∉cosupport (n+1) Nt B (μ+1) ∧
    ordinaryTraceOrder Nt B z=μ ∧ GermIdealOrder.order (n+1) Nt B z=(μ : ℕ∞) ∧
    B.mem z (g∘κ) ∧ VanishesToOrderOn (n+1) Nt z μ (g∘κ) ∧
      ¬VanishesToOrderOn (n+1) Nt z (μ+1) (g∘κ)

/- OUTPUT only: BOTH dictionaries are constructed on ONE retained seed. -/

private abbrev wholeOrderOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeCutsOutput M hM x hx Φ Φs c SN SE U ∧
  let p : projectionAmbient X := (x,0)
  let C : Set (projectionAmbient X) := {p}
  let _ : Fact (IsClosedSubmanifold (n+1) C) := ⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X := blowupProj (n+1) C
  let Q : MarkedIdeal (n+1) Y := (projectionTest M).geoTransform C π
  let _z := c.invFun 0
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  M.d≤ρ ∧ GermIdealOrder.order n M.N M.ideal x=(ρ : ℕ∞) ∧
    ∃g : X→ℂ,M.ideal.mem x g ∧ ¬VanishesToOrderOn n M.N x (ρ+1) g ∧
    ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y Z)
      (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
      (_hA : AnchoredInheritedLastChartChain c.homeo R e)
      (z : Z) (_hz : z∈e.source) (_he0 : e z=0),
      sharpTailOutput M g ρ (Q.geoTransformAlong R).N z R

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

private abbrev controlledSeedOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  wholeOrderOutput M hM x hx Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1:=(projectionTest M).geoTransform C π1
  ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y1 Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (_hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (_hz : z∈e.source) (_he0 : e z=0),
    IsGeoTestTower Q1 R → controlledTailOutput M hM x hx R e z

private abbrev successorTailOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (x : X)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1)
      ({(x,0)} : Set (projectionAmbient X)))) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1))) (z : Z) : Prop :=
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1:=(projectionTest M).geoTransform C π1
  let Q:=Q1.geoTransformAlong R
  let V:=e.source∩R.proj ⁻¹' (U∩c.source)
  let Cz : Set Z:={z}
  let Z2 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) Cz)
  let π2 : Z2→Z:=blowupProj (n+1) Cz
  let Q2:=Q.geoTransform Cz π2
  z∈Q.cosupp ∧ IsInvDomain (k+1) Q ∧ IsOpen V ∧ z∈V ∧
  (∀v∈V,v∈Q.N↔e v∈coordSubspace SN) ∧
  ∃S : Fin Q.E.length→Finset (Fin (n+1)),
    (∀i,z∈Q.E.get i→∀v∈V,v∈Q.E.get i↔e v∈coordSubspace (S i)) ∧
    ∃(c2 : FlatChart (n+1) Cz) (hπ2 : IsBlowupAlong (n+1) Cz π2),
      c2.y₀=z ∧ c2.k=0 ∧ c2.j=Fin.last n ∧
      (0 : ComplexModel (n+1))∈c2.target ∧
      let z2:=c2.invFun 0
      let R2 : BlowupTower Y1 Z2:=.step R Cz π2 hπ2
      z2∈c2.source ∧ π2 z2=z ∧ c2.toFun z2=0 ∧
      Q.IsAdmissibleCentre Cz ∧ IsGeoTestTower Q1 R2 ∧
      c2.homeo∈atlas (ComplexModel (n+1)) Z2 ∧
      AnchoredInheritedLastChartChain c.homeo R2 c2.homeo ∧
      (∀v∈c2.source,π2 v∈V ∧
        e (π2 v)=monomial 0 (Fin.last n) (c2.toFun v)) ∧
      z2∈Q2.N ∧ IsInvDomain (k+1) Q2 ∧
      (∀v∈c2.source,v∈Q2.N↔c2.toFun v∈coordSubspace SN) ∧
      (∀i,z∈Q.E.get i→∀v∈c2.source,
        v∈geoStrictTransform π2 Cz (Q.E.get i)↔
          Fin.last n∉S i ∧ c2.toFun v∈coordSubspace (S i)) ∧
      (∀i,z∉Q.E.get i→∀v∈c2.source,
        v∉geoStrictTransform π2 Cz (Q.E.get i)) ∧
      (∀v∈c2.source,v∈π2 ⁻¹' Cz↔c2.toFun v (Fin.last n)=0) ∧
      recordMark Z2 Q2=M.d ∧
      recordBoundary Z2 Q2=Q.E.map (geoStrictTransform π2 Cz)++[π2 ⁻¹' Cz] ∧
      (recordBoundary Z2 Q2).length=M.E.length+3+R.length

private abbrev successorSeedOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  controlledSeedOutput M hM x hx Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1:=(projectionTest M).geoTransform C π1
  ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y1 Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (_hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (_hz : z∈e.source) (_he0 : e z=0),
    IsGeoTestTower Q1 R→successorTailOutput (k:=k) M x c SN U R e z

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

private abbrev firstPointBaseOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) : Prop :=
  let P:=projectionTest M
  let p : projectionAmbient X:=(x,0)
  let C : Set (projectionAmbient X):={p}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M hM x hx).2
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let Q1:=P.geoTransform C π1
  let H0:=HironakaActualProjectionTowerHistory.projectionTowerHistory M
    (BlowupTower.refl : BlowupTower (projectionAmbient X) (projectionAmbient X))
  let H1:=HironakaActualProjectionTowerHistory.projectionTowerHistory M A
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  projectionQueriesOutput M.N x ∧
  IsInvDomain (k+1) P ∧ P.N=(Prod.fst : projectionAmbient X→X) ⁻¹' M.N ∧
  P.ideal=GermIdeal.pullback (m:=n+1) (Prod.fst : projectionAmbient X→X) M.ideal ∧
  P.d=M.d ∧ P.E=M.E.map ((Prod.fst : projectionAmbient X→X) ⁻¹' ·)++[horizontal X] ∧
  P.E.length=M.E.length+1 ∧ p∈P.N ∧ p∈P.cosupp ∧
  M.d≤ρ ∧ GermIdealOrder.order n M.N M.ideal x=(ρ : ℕ∞) ∧
  ordinaryTraceOrder P.N P.ideal p=ρ ∧
  GermIdealOrder.order (n+1) P.N P.ideal p=(ρ : ℕ∞) ∧
  P.IsAdmissibleCentre C ∧ interior C=∅ ∧ IsBlowupAlong (n+1) C π1 ∧
  IsGeoTestTower P A ∧ A.length=1 ∧ A.proj=π1 ∧ P.geoTransformAlong A=Q1 ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H0 ∧
  HironakaActualMixedTestPowerNormalization.record M H0=P ∧
  HironakaActualMixedTestPowerNormalization.length H0=1 ∧
  HironakaActualMixedTestPowerNormalization.projections H0=1 ∧
  HironakaActualMixedTestPowerNormalization.baseMap H0=(Prod.fst : projectionAmbient X→X) ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H1 ∧
  HironakaActualMixedTestPowerNormalization.record M H1=Q1 ∧
  HironakaActualMixedTestPowerNormalization.length H1=2 ∧
  HironakaActualMixedTestPowerNormalization.projections H1=1 ∧
  HironakaActualMixedTestPowerNormalization.baseMap H1=(Prod.fst : projectionAmbient X→X)∘π1 ∧
  IsInvDomain (k+1) Q1 ∧ recordMark Y1 Q1=M.d ∧
  recordBoundary Y1 Q1=P.E.map (geoStrictTransform π1 C)++[π1 ⁻¹' C] ∧
  recordBoundary Y1 Q1=
    M.E.map (fun H=>geoStrictTransform π1 C
      ((Prod.fst : projectionAmbient X→X) ⁻¹' H)) ++
      [geoStrictTransform π1 C (horizontal X),π1 ⁻¹' C] ∧
  (recordBoundary Y1 Q1).length=M.E.length+2 ∧
  IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower Y1 Y1)

/-- No chart/frame is chosen here. The full ACTUAL first P-test is derived
from original M/domain/xcosupp BEFORE the final empty-tail True clause. -/
theorem projection_first_point_base {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    firstPointBaseOutput M hM x hx
 := by
  let P:=projectionTest M
  let p : projectionAmbient X:=(x,0)
  let C : Set (projectionAmbient X):={p}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  have hCentre:=projection_point_centre M hM x hx
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C) hCentre.2
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let Q1:=P.geoTransform C π1
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  have hQueries : projectionQueriesOutput M.N x := by
    dsimp only [projectionQueriesOutput]
    let hf:=ProductComplexManifold.contMDiff_fst
      (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
    let hs:=HironakaAuxiliaryGraphGeometry.isSubmersion_fst
      (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)
    refine ⟨?_,?_,?_⟩
    · intro I hI
      refine ⟨map_wholeChartStalkIdeal_actual_pullback hf I hI p,?_,?_⟩
      · intro a
        exact Set.ext_iff.mp (cosupport_preimage_eq hs hI M.N a) p
      · exact order_preimage_eq (hs.isSubmersionAt p)
          (fun _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg) M.N
    · intro f hf0
      exact actualHolomorphicGermPullback_original_function hf p f hf0
    · intro c a
      exact (actualHolomorphicGermPullback hf p).toLinearMap.map_smul c a
  have hP : IsInvDomain (k+1) P:=projection_test_isInvDomain M hM
  rcases projection_test_dictionary M hM with
    ⟨hPN,hPI,hPd,hPE,hPLen,_hPLast,_hPOld,hPCosupp⟩
  have hpN : p∈P.N:=by
    rw [hPN]
    exact M.cosupp_subset_N hx
  have hpCosupp : p∈P.cosupp:=by rw [hPCosupp];exact hx
  have hI:=hM.isWellFormed.isCoherent
  have hCrit (a : ℕ) : x∈cosupport n M.N M.ideal a ↔ a≤ρ :=
    ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N hI
      hM.isNonzeroAlongAt (M.cosupp_subset_N hx) a
  have hGood : x∈cosupport n M.N M.ideal ρ:=(hCrit ρ).mpr le_rfl
  have hBad : x∉cosupport n M.N M.ideal (ρ+1):=
    fun h=>Nat.not_succ_le_self ρ ((hCrit (ρ+1)).mp h)
  have hdρ : M.d≤ρ:=(hCrit M.d).mp hx
  have hSourceOrder : GermIdealOrder.order n M.N M.ideal x=(ρ : ℕ∞) := by
    apply le_antisymm
    · apply ENat.lt_natCast_add_one_iff.mp
      apply lt_of_not_ge
      intro h
      exact hBad ⟨hGood.1,(le_order_iff (fun _ hg=>
        GermIdeal.IsCoherent.holomorphicAt_mem hI hg)).mp
          (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
    · exact (le_order_iff (fun _ hg=>
        GermIdeal.IsCoherent.holomorphicAt_mem hI hg)).mpr hGood.2
  have hQI:=hQueries.1 M.ideal hI
  have hPCrit (a : ℕ) : p∈cosupport (n+1) P.N P.ideal a ↔ a≤ρ :=
    (hQI.2.1 a).trans (hCrit a)
  have hPActualCrit (a : ℕ) : p∈cosupport (n+1) P.N P.ideal a ↔
      a≤ordinaryTraceOrder P.N P.ideal p :=
    ordinaryTraceOrder_cosupport_iff hP.isWellFormed.isClosedSubmanifold_N
      hP.isWellFormed.isCoherent hP.isNonzeroAlongAt hpN a
  have hPNat : ordinaryTraceOrder P.N P.ideal p=ρ :=
    le_antisymm ((hPCrit _).mp ((hPActualCrit _).mpr le_rfl))
      ((hPActualCrit _).mp ((hPCrit _).mpr le_rfl))
  have hPOrder : GermIdealOrder.order (n+1) P.N P.ideal p=(ρ : ℕ∞) :=
    hQI.2.2.trans hSourceOrder
  -- FIRST native test: the predecessor is the initial P tower, not the Q1 tail.
  have hA : IsGeoTestTower P A:=⟨True.intro,hCentre.1⟩
  have hQ1 : IsInvDomain (k+1) Q1:=isInvDomain_geoTransformAlong hP A hA
  have hEword : recordBoundary Y1 Q1=
      M.E.map (fun H=>geoStrictTransform π1 C
        ((Prod.fst : projectionAmbient X→X) ⁻¹' H)) ++
        [geoStrictTransform π1 C (horizontal X),π1 ⁻¹' C] := by
    change P.E.map (geoStrictTransform π1 C)++[π1 ⁻¹' C]=_
    rw [hPE]
    simp only [List.map_append,List.map_map,List.map_cons,List.map_nil,
      List.append_assoc,Function.comp_def,List.cons_append,List.nil_append]
  have hLength : (recordBoundary Y1 Q1).length=M.E.length+2 := by
    rw [hEword]
    simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]
  have h0Test:=
    (HironakaActualProjectionTowerHistory.isTest_projectionTowerHistory_iff M
      (BlowupTower.refl : BlowupTower (projectionAmbient X) (projectionAmbient X))).mpr True.intro
  have h1Test:=(HironakaActualProjectionTowerHistory.isTest_projectionTowerHistory_iff M A).mpr hA
  have h0Rec:=HironakaActualProjectionTowerHistory.record_projectionTowerHistory M
    (BlowupTower.refl : BlowupTower (projectionAmbient X) (projectionAmbient X))
  have h1Rec:=HironakaActualProjectionTowerHistory.record_projectionTowerHistory M A
  have h0Dict:=HironakaActualProjectionTowerHistory.projectionTowerHistory_dictionary M
    (BlowupTower.refl : BlowupTower (projectionAmbient X) (projectionAmbient X))
  have h1Dict:=HironakaActualProjectionTowerHistory.projectionTowerHistory_dictionary M A
  dsimp only [firstPointBaseOutput]
  exact ⟨hQueries,hP,hPN,hPI,hPd,hPE,hPLen,hpN,hpCosupp,hdρ,hSourceOrder,hPNat,hPOrder,
    hCentre.1,hCentre.2,hπ1,hA,rfl,rfl,rfl,
    h0Test,h0Rec,h0Dict.1,h0Dict.2.1,h0Dict.2.2.1,
    h1Test,h1Rec,h1Dict.1,h1Dict.2.1,h1Dict.2.2.1,
    hQ1,hPd,rfl,hEword,hLength,True.intro⟩

private abbrev initialSeedStateOutput {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (x : X)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X))) : Prop :=
  let p : projectionAmbient X:=(x,0)
  let C : Set (projectionAmbient X):={p}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1:=(projectionTest M).geoTransform C π1
  let z1:=c.invFun 0
  c.homeo∈atlas (ComplexModel (n+1)) Y1 ∧ z1∈c.source ∧
  c.toFun z1=0 ∧ π1 z1=p ∧ z1∈Q1.cosupp ∧
  AnchoredInheritedLastChartChain c.homeo (BlowupTower.refl : BlowupTower Y1 Y1) c.homeo ∧
  IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower Y1 Y1)

private abbrev firstPointSeedOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  successorSeedOutput M hM x hx Φ Φs c SN SE U ∧
  firstPointBaseOutput M hM x hx ∧ initialSeedStateOutput M x c

/-- ONE G04 seed before all future queries/states; the generic first-base
producer chooses NOTHING and uses the SAME canonical first map/centre. -/
theorem exists_original_anchored_first_point_base {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      firstPointSeedOutput M hM x hx Φ Φs c SN SE U
 := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hSeed⟩:=
    HironakaActualAnchoredSuccessorTest.exists_original_anchored_successor_test M hM x hx
  change successorSeedOutput M hM x hx Φ Φs c SN SE U at hSeed
  have hWhole:=hSeed.1.1.1
  rcases hWhole with ⟨_hΦs,_hΦ0,_hcp,_hck,_hcj,_hOld,_hLast,_hSourceN,_hSourceE,
    _hSN,_hSE,_h0c,hzSource,hzp,hWz,_hπ,hAtlas,_hQ1,hzQ1,_hdQ1,_hEword,_hLength,
    _hU,_hzU,_hUc,_hNmask,_hEmask,_hEmptyH,_hBorn,_hTo,_hInv,_hSub,_hTSub,
    _hSrc,_hZero,_hDom,_hSource,_hWholeTails⟩
  refine ⟨Φ,Φs,c,SN,SE,U,hSeed,projection_first_point_base M hM x hx,?_⟩
  dsimp only [initialSeedStateOutput]
  exact ⟨hAtlas,hzSource,hWz,hzp,hzQ1,⟨rfl,hAtlas⟩,True.intro⟩

end
end Hironaka.HironakaActualAnchoredFirstPointBase
