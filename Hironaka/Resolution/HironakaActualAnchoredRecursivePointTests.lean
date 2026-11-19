import Hironaka.Resolution.HironakaActualAnchoredFirstPointBase
import Hironaka.Resolution.HironakaActualProjectionTowerHistory
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeOrder
import Hironaka.Resolution.HironakaActualAnchoredBoundaryMasks
import Hironaka.Resolution.HironakaActualInheritedVerticalPointChart

/-! One same-seed recursive family of genuine anchored native point tests. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredRecursivePointTests
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
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C π1
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
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C π1
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
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C π1
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

private abbrev initialSeedStateOutput {n : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (x : X)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X))) : Prop :=
  let p : projectionAmbient X:=(x,0)
  let C : Set (projectionAmbient X):={p}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C π1
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

private structure ActualNext {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    (Q1 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1)))
    (s : NativeTailState Q1 a) where
  c2 : FlatChart (n+1) ({tailPoint s} : Set s.1)
  hπ2 : IsBlowupAlong (n+1) ({tailPoint s} : Set s.1)
    (blowupProj (n+1) ({tailPoint s} : Set s.1))
  centre : c2.y₀=tailPoint s
  codim : c2.k=0
  pivot : c2.j=Fin.last n
  origin_source : c2.invFun 0∈c2.source
  origin_zero : c2.toFun (c2.invFun 0)=0
  origin_projects : blowupProj (n+1) ({tailPoint s} : Set s.1) (c2.invFun 0)=tailPoint s
  inherited_vector : ∀v∈c2.source,
    blowupProj (n+1) ({tailPoint s} : Set s.1) v∈s.2.2.1.source ∧
    s.2.2.1 (blowupProj (n+1) ({tailPoint s} : Set s.1) v)=
      monomial 0 (Fin.last n) (c2.toFun v)
  actual_test : IsGeoTestTower Q1
    (BlowupTower.step (Z:=CMfd.of (BlowupSpace (n+1) ({tailPoint s} : Set s.1)))
      s.2.1 ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1)) hπ2)
  actual_chain : AnchoredInheritedLastChartChain a
    (BlowupTower.step (Z:=CMfd.of (BlowupSpace (n+1) ({tailPoint s} : Set s.1)))
      s.2.1 ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1)) hπ2) c2.homeo

private def nextState {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    {Q1 : MarkedIdeal (n+1) Y1}
    {a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))}
    (s : NativeTailState Q1 a) (w : ActualNext Q1 a s) : NativeTailState Q1 a :=
  ⟨CMfd.of (BlowupSpace (n+1) ({tailPoint s} : Set s.1)),
    .step s.2.1 ({tailPoint s} : Set s.1)
      (blowupProj (n+1) ({tailPoint s} : Set s.1)) w.hπ2,
    w.c2.homeo,⟨w.c2.invFun 0,w.actual_chain,w.actual_test,w.origin_source,w.origin_zero⟩⟩

private abbrev familyTailDictionary {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (g : X→ℂ) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (s : NativeTailState
      (Y1:=CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M).geoTransform ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo) : Prop :=
  let Z:=s.1
  let R:=s.2.1
  let e:=s.2.2.1
  let z:=tailPoint s
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let hπ1:=isBlowupAlong_blowupProj (n:=n+1) (C:=C)
    (projection_point_centre M hM x hx).2
  let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1 hπ1
  let T:=A.append R
  let Q:=((projectionTest M).geoTransform C π1).geoTransformAlong R
  let H:=HironakaActualProjectionTowerHistory.projectionTowerHistory M T
  let V:=e.source∩R.proj ⁻¹' (U∩c.source)
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  let q:=R.length+1
  wholeTailCuts M.N Q.N x z R ∧
  sharpTailOutput M g ρ Q.N z R ∧
  controlledTailOutput M hM x hx R e z ∧
  HironakaActualMixedTestPowerNormalization.IsTest M H ∧
  HironakaActualMixedTestPowerNormalization.record M H=Q ∧
  HironakaActualMixedTestPowerNormalization.baseMap H=
    (Prod.fst : projectionAmbient X→X)∘T.proj ∧
  HironakaActualMixedTestPowerNormalization.baseMap H z=x ∧
  HironakaActualMixedTestPowerNormalization.length H=q+1 ∧
  HironakaActualMixedTestPowerNormalization.projections H=1 ∧
  T.length=q ∧ recordMark Z Q=M.d ∧
  (recordBoundary Z Q).length=M.E.length+1+q ∧
  (ρ=M.d→ ordinaryTraceOrder Q.N Q.ideal z=M.d) ∧
  IsOpen V ∧ z∈V ∧
  (recordBoundary Z Q).map (fun K=>V∩K)=
    List.ofFn (fun i : Fin M.E.length=>
      {v : Z | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) ++
      [(∅ : Set Z)] ++ List.replicate R.length (∅ : Set Z) ++
      [V∩{v | e v (Fin.last n)=0}]

private abbrev familySeedOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  firstPointSeedOutput M hM x hx Φ Φs c SN SE U ∧
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C (blowupProj (n+1) C)
  let a:=c.homeo
  let z1:=c.invFun 0
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  ∃g : X→ℂ,M.ideal.mem x g ∧ ¬VanishesToOrderOn n M.N x (ρ+1) g ∧
  ∃h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
    IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0,
  ∃chooseNext : (s : NativeTailState Q1 a)→ActualNext Q1 a s,
    let s0 : NativeTailState Q1 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
    let F : ℕ→NativeTailState Q1 a:=Nat.rec s0 (fun _ s=>nextState s (chooseNext s))
    F 0=s0 ∧
    (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=nextState (F r) (chooseNext (F r))) ∧
    ∀r : ℕ,familyTailDictionary M hM x hx c g SE U (F r)

private theorem derivedNextWitness {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (hSeed : firstPointSeedOutput M hM x hx Φ Φs c SN SE U)
    (s : NativeTailState
      (Y1:=CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M).geoTransform
      ({(x,0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo) :
    Nonempty (ActualNext
      (Y1:=CMfd.of (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
      ((projectionTest M).geoTransform ({(x,0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x,0)} : Set (projectionAmbient X)))) c.homeo s) := by
  have hs:=s.2.2.2.property
  have hNext:=hSeed.1.2 s.2.1 s.2.2.1 hs.1 (tailPoint s)
    hs.2.2.1 hs.2.2.2 hs.2.1
  rcases hNext with ⟨_hCos,_hDom,_hV,_hzV,_hN,S,_hS,c2,hπ2,
    hCentre,hCodim,hPivot,_hTarget,hOriginSource,hOriginProj,hOriginZero,
    _hAdmiss,hTest,_hAtlas,hChain,hVector,_hRest⟩
  exact ⟨{
    c2:=c2
    hπ2:=hπ2
    centre:=hCentre
    codim:=hCodim
    pivot:=hPivot
    origin_source:=hOriginSource
    origin_zero:=hOriginZero
    origin_projects:=hOriginProj
    inherited_vector:=fun v hv=>⟨(hVector v hv).1.1,(hVector v hv).2⟩
    actual_test:=hTest
    actual_chain:=hChain }⟩

private theorem nextState_length {n : ℕ} {Y1 : CMfd.{u} (n+1)}
    {Q1 : MarkedIdeal (n+1) Y1}
    {a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))}
    (s : NativeTailState Q1 a) (w : ActualNext Q1 a s) :
    (nextState s w).2.1.length=s.2.1.length+1 := rfl

private theorem sameSeedBoundary {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X))))
    (hSeed : firstPointSeedOutput M hM x hx Φ Φs c SN SE U) :
    let C : Set (projectionAmbient X):={(x,0)}
    let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
    let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C (blowupProj (n+1) C)
    ∀{Y : CMfd.{u} (n+1)} (R : BlowupTower Y1 Y)
      (e : OpenPartialHomeomorph Y (ComplexModel (n+1))),
      AnchoredInheritedLastChartChain c.homeo R e →
      let V := e.source∩R.proj ⁻¹' (U∩c.source)
      IsOpen V ∧
      ((Q1.geoTransformAlong R).E.map (fun K=>V∩K) =
        List.ofFn (fun i : Fin M.E.length =>
          {v | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) ++
        [(∅ : Set Y)] ++ List.replicate R.length (∅ : Set Y) ++
        [V∩{v | e v (Fin.last n)=0}]) ∧
      (∀z∈e.source,e z=0→z∈V) := by
  dsimp only
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C π1
  have hWhole:=hSeed.1.1.1.1
  rcases hWhole with ⟨_hΦs,_hΦ0,_hcp,_hck,_hcj,_hOld,_hLast,_hSourceN,_hSourceE,
    _hSN,hSE,_h0c,hzSource,_hzp,hWz,_hπ,_hAtlas,_hQ,_hzQ,_hdQ,hEword,_hLength,
    hU,hzU,_hUc,_hNmask,hEmask,hEmptyH,hBorn,_hTo,_hInv,_hSub,_hTSub,
    _hSrc,_hZero,_hDom,_hSource,_hTails⟩
  let L : List (Set Y1) := M.E.map (fun K=>geoStrictTransform π1 C
    ((Prod.fst : projectionAmbient X→X) ⁻¹' K)) ++ [geoStrictTransform π1 C (horizontal X)]
  have hLenL : L.length=M.E.length+1 := by simp [L]
  have hE0 : Q1.E=L++[π1 ⁻¹' C] := by
    simpa only [L,List.append_assoc,List.cons_append,List.nil_append] using hEword
  let S : Fin L.length→Finset (Fin (n+1)) := fun i=>
    if hi : i.val<M.E.length then SE ⟨i.val,hi⟩ else ∅
  let P : Fin L.length→Prop := fun i=>
    if hi : i.val<M.E.length then x∈M.E.get ⟨i.val,hi⟩ else False
  have hS : ∀i,Fin.last n∉S i := by
    intro i
    dsimp only [S]
    split_ifs with hi
    · exact hSE ⟨i.val,hi⟩
    · simp
  have hSource : ∀i,∀v∈U∩c.homeo.source,
      v∈L.get i ↔ P i ∧ c.homeo v∈coordSubspace (S i) := by
    intro i v hv
    by_cases hi : i.val<M.E.length
    · have hGet : L.get i=geoStrictTransform π1 C
          ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get ⟨i.val,hi⟩) := by
        simp only [L,List.get_eq_getElem]
        rw [List.getElem_append_left (by simpa using hi),List.getElem_map]
      rw [hGet]
      simp only [S,P,dif_pos hi]
      constructor
      · intro hvK
        by_cases hxi : x∈M.E.get ⟨i.val,hi⟩
        · exact ⟨hxi,((hEmask ⟨i.val,hi⟩).1 hxi v hv.1).mp hvK⟩
        · exact False.elim ((hEmask ⟨i.val,hi⟩).2 hxi v hv.1 hvK)
      · rintro ⟨hxi,hvS⟩
        exact ((hEmask ⟨i.val,hi⟩).1 hxi v hv.1).mpr hvS
    · have hi0 : i.val=M.E.length := by
        have hil : i.val<M.E.length+1 := lt_of_lt_of_eq i.isLt hLenL
        omega
      have hGet : L.get i=geoStrictTransform π1 C (horizontal X) := by
        simp only [L,List.get_eq_getElem]
        rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
        simp [hi0]
      rw [hGet]
      simp only [S,P,dif_neg hi]
      constructor
      · exact fun hvK=>False.elim (hEmptyH v hv.1 hvK)
      · exact fun hvK=>False.elim hvK.1
  intro Y R e hAnchor
  let V : Set Y := e.source∩R.proj ⁻¹' (U∩c.source)
  have hh := anchored_boundary_word_masks Q1 L (π1 ⁻¹' C) hE0 c.homeo (c.invFun 0)
    hzSource hWz U hU hzU S P hS hSource (fun v hv=>hBorn v hv.1) R e hAnchor
  rcases hh with ⟨_hd,_hLen,hOpen,hWord,hOrigin⟩
  have hMasks : List.ofFn (fun i : Fin L.length=>
      {v : Y | v∈V ∧ P i ∧ e v∈coordSubspace (S i)}) =
      List.ofFn (fun i : Fin M.E.length=>
        {v : Y | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) ++ [∅] := by
    rw [List.ofFn_congr hLenL,List.ofFn_succ']
    have hHead : (fun i : Fin M.E.length=>
        {v : Y | v∈V ∧ P (Fin.cast hLenL.symm i.castSucc) ∧
          e v∈coordSubspace (S (Fin.cast hLenL.symm i.castSucc))}) =
        (fun i : Fin M.E.length=>
          {v : Y | v∈V ∧ x∈M.E.get i ∧ e v∈coordSubspace (SE i)}) := by
      funext i
      simp [S,P,i.isLt]
    have hLast : {v : Y | v∈V ∧ P (Fin.cast hLenL.symm (Fin.last M.E.length)) ∧
        e v∈coordSubspace (S (Fin.cast hLenL.symm (Fin.last M.E.length)))}=∅ := by
      ext v
      simp [S,P]
    rw [hHead,hLast,List.concat_eq_append]
  refine ⟨hOpen,?_,hOrigin⟩
  change (Q1.geoTransformAlong R).E.map (fun K=>V∩K)=
    List.ofFn (fun i : Fin L.length=>{v | v∈V ∧ P i ∧ e v∈coordSubspace (S i)}) ++
      List.replicate R.length (∅ : Set Y) ++ [V∩{v | e v (Fin.last n)=0}] at hWord
  rw [hMasks] at hWord
  simpa only [List.append_assoc] using hWord

/-- The same original first seed produces one literal recursively coherent
family. Every current dictionary is derived after its actual test exists. -/
theorem exists_original_anchored_recursive_point_tests {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      familySeedOutput M hM x hx Φ Φs c SN SE U := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hSeed⟩:=
    HironakaActualAnchoredFirstPointBase.exists_original_anchored_first_point_base M hM x hx
  change firstPointSeedOutput M hM x hx Φ Φs c SN SE U at hSeed
  refine ⟨Φ,Φs,c,SN,SE,U,hSeed,?_⟩
  dsimp only
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1 : MarkedIdeal (n+1) Y1:=(projectionTest M).geoTransform C π1
  let a:=c.homeo
  let z1:=c.invFun 0
  let ρ:=ordinaryTraceOrder M.N M.ideal x
  have hWholeOrder:=hSeed.1.1.1
  rcases hWholeOrder.2.2.2 with ⟨g,hgMem,hgSharp,hgTails⟩
  have hInit:=hSeed.2.2
  let h0 : AnchoredInheritedLastChartChain a (BlowupTower.refl : BlowupTower Y1 Y1) a ∧
      IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower Y1 Y1) ∧ z1∈a.source ∧ a z1=0 :=
    ⟨hInit.2.2.2.2.2.1,hInit.2.2.2.2.2.2,hInit.2.1,hInit.2.2.1⟩
  let chooseNext : (s : NativeTailState Q1 a)→ActualNext Q1 a s :=
    fun s=>Classical.choice (derivedNextWitness M hM x hx Φ Φs c SN SE U hSeed s)
  refine ⟨g,hgMem,hgSharp,h0,chooseNext,?_⟩
  let s0 : NativeTailState Q1 a:=⟨Y1,BlowupTower.refl,a,⟨z1,h0⟩⟩
  let F : ℕ→NativeTailState Q1 a:=Nat.rec s0 (fun _ s=>nextState s (chooseNext s))
  change F 0=s0 ∧ (∀r : ℕ,(F r).2.1.length=r) ∧
    (∀r : ℕ,F (r+1)=nextState (F r) (chooseNext (F r))) ∧
    ∀r : ℕ,familyTailDictionary M hM x hx c g SE U (F r)
  refine ⟨rfl,?_,fun _=>rfl,?_⟩
  · intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      change (nextState (F r) (chooseNext (F r))).2.1.length=r+1
      rw [nextState_length,ih]
  · intro r
    let s:=F r
    let Z:=s.1
    let R:=s.2.1
    let e:=s.2.2.1
    let z:=tailPoint s
    have hs:=s.2.2.2.property
    have hAnchor : AnchoredInheritedLastChartChain c.homeo R e:=hs.1
    have hR : IsGeoTestTower Q1 R:=hs.2.1
    have hz : z∈e.source:=hs.2.2.1
    have he0 : e z=0:=hs.2.2.2
    have hWhole:=hSeed.1.1.1.1
    rcases hWhole with ⟨_hΦs,_hΦ0,_hcp,_hck,_hcj,_hOld,_hLast,_hSourceN,_hSourceE,
      _hSN,_hSE,_h0c,_hzSource,_hzp,_hWz,_hπ,_hAtlas,_hQ1,_hzQ1,_hdQ1,_hEword,_hLength,
      _hU,_hzU,_hUc,_hNmask,_hEmask,_hEmptyH,_hBorn,_hTo,_hInv,_hSub,_hTSub,
      _hSrc,_hZero,_hDom,_hSource,hWholeTails⟩
    have hCuts:=hWholeTails R e hAnchor z hz he0
    have hSharp:=hgTails R e hAnchor z hz he0
    have hControlled:=hSeed.1.1.2 R e hAnchor z hz he0 hR
    let A : BlowupTower (projectionAmbient X) Y1:=.step .refl C π1
      (isBlowupAlong_blowupProj (n:=n+1) (C:=C)
        (projection_point_centre M hM x hx).2)
    let T:=A.append R
    let Q:=Q1.geoTransformAlong R
    have hControlCopy:=hControlled
    rcases hControlCopy with ⟨hT,hQ,_hDom,hMark,hELen,_hB,_hLeft,_hRight,
      _hFSpan,_hFGood,_hFBad,_hFOrder,_hSum,_hGood,_hBad,hNat,_hOrder,
      _hdCurrent,_hCosCurrent,_hAdmiss⟩
    have hHistTest:=(HironakaActualProjectionTowerHistory.isTest_projectionTowerHistory_iff M T).mpr hT
    have hHistRecord:=
      (HironakaActualProjectionTowerHistory.record_projectionTowerHistory M T).trans hQ.symm
    have hHist:=HironakaActualProjectionTowerHistory.projectionTowerHistory_dictionary M T
    have hTLen : T.length=R.length+1 := by
      rw [BlowupTower.length_append]
      change 1+R.length=R.length+1
      omega
    have hHistLen : HironakaActualMixedTestPowerNormalization.length
        (HironakaActualProjectionTowerHistory.projectionTowerHistory M T)=
        (R.length+1)+1 := by rw [hHist.1,hTLen]
    have hBasePoint : HironakaActualMixedTestPowerNormalization.baseMap
        (HironakaActualProjectionTowerHistory.projectionTowerHistory M T) z=x := by
      rw [hHist.2.2.1]
      change (Prod.fst : projectionAmbient X→X) ((A.append R).proj z)=x
      rw [BlowupTower.proj_append]
      exact hCuts.1
    have hBoundary:=sameSeedBoundary M hM x hx Φ Φs c SN SE U hSeed R e hAnchor
    dsimp only [familyTailDictionary]
    refine ⟨hCuts,hSharp,hControlled,hHistTest,hHistRecord,hHist.2.2.1,hBasePoint,
      hHistLen,hHist.2.1,hTLen,hMark,?_,?_,hBoundary.1,
      hBoundary.2.2 z hz he0,hBoundary.2.1⟩
    · change Q.E.length=M.E.length+1+(R.length+1)
      calc Q.E.length=M.E.length+2+R.length:=hELen
           _=M.E.length+1+(R.length+1):=by omega
    · intro hρ
      rw [hNat,hρ,Nat.sub_self,Nat.mul_zero,Nat.add_zero]

end
end Hironaka.HironakaActualAnchoredRecursivePointTests


