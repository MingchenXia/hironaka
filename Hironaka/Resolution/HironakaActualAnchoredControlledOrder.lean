import Hironaka.Resolution.HironakaActualAnchoredOriginalIdealOrder
import Hironaka.Resolution.HironakaActualAnchoredSeedTotalFactor
import Hironaka.Resolution.HironakaActualProperOriginalTowerFactor
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels

/-! Controlled order on a GIVEN genuine anchored native test prefix.
ONE ordinary seed is retained; local TOTAL sharpness is proved on its actual
proper carrier. No successor/all-q history, raw invariant or CAN is claimed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredControlledOrder
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
  RestrictedIdealWeight
open scoped ProductComplexManifold

private theorem chart_smooth {r : ℕ} {X : CMfd.{u} r}
    (e : OpenPartialHomeomorph X (ComplexModel r))
    (he : e∈atlas (ComplexModel r) X) :
    ∀z∈e.source,ContMDiffAt 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel r) ∞ e z := by
  have hmax:=IsManifold.subset_maximalAtlas (I:=𝓘(ℂ,ComplexModel r)) (n:=∞) he
  intro z hz
  exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (e.open_source.mem_nhds hz)

/-- LOCAL whole TOTAL-power sharpness. Every current guard is genuine geometry
or derived from the actual existing test; no whole chart mask is required. -/
private theorem same_seed_total_power_sharp {n : ℕ} {X : CMfd.{u} (n+1)}
    {C : Set X} [Fact (IsClosedSubmanifold (n+1) C)]
    (P : MarkedIdeal (n+1) X) (hN : IsClosedSubmanifold (n+1) P.N)
    (hI : P.ideal.IsCoherent) (hC : P.IsAdmissibleCentre C)
    (c : FlatChart (n+1) C)
    (hπ : IsBlowupAlong (n+1) C (blowupProj (n+1) C)) (hj : c.j=Fin.last n)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z)
    (hR : IsGeoTestTower (P.geoTransform C (blowupProj (n+1) C)) R)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (hz : z∈e.source)
    (hzN : z∈((P.geoTransform C (blowupProj (n+1) C)).geoTransformAlong R).N)
    (he0 : e z=0) (d : ℕ) :
    let A : BlowupTower X (CMfd.of (BlowupSpace (n+1) C)):=
      .step .refl C (blowupProj (n+1) C) hπ
    let F:=idealPow (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal d
    let Nt:=((P.geoTransform C (blowupProj (n+1) C)).geoTransformAlong R).N
    z∈cosupport (n+1) Nt F ((R.length+1)*d) ∧
      z∉cosupport (n+1) Nt F ((R.length+1)*d+1) := by
  dsimp only
  let A : BlowupTower X (CMfd.of (BlowupSpace (n+1) C)):=
    .step .refl C (blowupProj (n+1) C) hπ
  have hTotal:=anchored_seed_total_factor c hπ hj R e hA z hz
  cases R with
  | refl =>
    rcases hA with ⟨rfl,hAtlas⟩
    simp only [BlowupTower.length_refl,Nat.zero_add,Nat.one_mul,geoTransformAlong_refl] at hTotal ⊢
    have hzC : blowupProj (n+1) C z∈C := by
      apply (c.toFun_j_eq_zero_iff hz).mp
      rw [hj]
      exact congrArg (fun w : ComplexModel (n+1)=>w (Fin.last n)) he0
    have hSmooth : ∀v∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1))
        𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun v := by
      intro v hv
      exact chart_smooth (X:=CMfd.of (BlowupSpace (n+1) C)) c.homeo hAtlas v hv
    have hBorn:=GlueingTrivialAction.isLocalEquation_monomial hπ c.hsrc c.hflat c.hj
      c.isOpen_source (W:=c.toFun) hSmooth
      (fun v hv=>⟨hv.1,c.monomial_toFun hv⟩)
    rw [hj] at hBorn
    have hSharp:=exceptional_power_order_at_strict hπ hN hC.subset_N z hzN hzC d
    have hWhole (g : _→ℂ) :
        (idealPow (BlowupTowerTransforms.exceptionalDivisor (A.append .refl)).ideal d).mem z g ↔
        (idealPow (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
          (vanishingIdeal (n:=n+1) C)) d).mem z g := by
      have hh:=((hTotal.2 d g).trans (hBorn.idealPow_mem_iff d z hz g).symm)
      simpa only [BlowupTower.length_refl,Nat.zero_add,Nat.one_mul,hj,exceptionalDivisor_ideal] using hh
    constructor
    · exact ⟨hzN,fun g hg=>hSharp.1.2 g ((hWhole g).mp hg)⟩
    · intro h
      exact hSharp.2.1 ⟨hzN,fun g hg=>h.2 g ((hWhole g).mpr hg)⟩
  | step R C2 π2 hπ2 =>
    obtain ⟨he,eold,y,Φ,hPrev,hC2,hy,hy0,hsrc,hflat,_hInherited,hNative⟩:=hA
    have hBorn:=GlueingTrivialAction.isLocalEquation_monomial hπ2 hsrc hflat
      (Nat.zero_le (Fin.last n).val) e.open_source (chart_smooth e he) hNative
    have hzC : π2 z∈C2 := by
      apply (hflat (hNative z hz).1.1 (hNative z hz).1.2).mpr
      rw [←(hNative z hz).2,he0]
      intro i hi
      simp [monomial_apply]
    have hFirst : IsGeoTestTower P A:=⟨trivial,hC⟩
    have hQ1:=MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hN hI A hFirst
    have hQprev:=MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hQ1.1 hQ1.2 R hR.1
    have hCN : C2⊆((P.geoTransform C (blowupProj (n+1) C)).geoTransformAlong R).N :=
      fun v hv=>(hR.2.2.1 hv).1
    let a:=((BlowupTower.step R C2 π2 hπ2).length+1)*d
    have hSharp:=exceptional_power_order_at_strict hπ2 hQprev.1 hCN z hzN hzC a
    have hWhole (g : _→ℂ) :
        (idealPow (BlowupTowerTransforms.exceptionalDivisor
          (A.append (.step R C2 π2 hπ2))).ideal d).mem z g ↔
        (idealPow (GermIdeal.pullback (m:=n+1) π2 (vanishingIdeal (n:=n+1) C2)) a).mem z g := by
      have hh:=((hTotal.2 d g).trans (hBorn.idealPow_mem_iff a z hz g).symm)
      simpa only [exceptionalDivisor_ideal] using hh
    constructor
    · exact ⟨hzN,fun g hg=>hSharp.1.2 g ((hWhole g).mp hg)⟩
    · intro h
      exact hSharp.2.1 ⟨hzN,fun g hg=>h.2 g ((hWhole g).mpr hg)⟩

private theorem enat_from_sharp {r : ℕ} {X : CMfd.{u} r}
    (N : Set X) (I : GermIdeal r X) (x : X) (a : ℕ)
    (hHol : ∀g,I.mem x g→HolomorphicAt r g x)
    (hGood : x∈cosupport r N I a) (hBad : x∉cosupport r N I (a+1)) :
    GermIdealOrder.order r N I x=(a : ℕ∞) := by
  apply le_antisymm
  · apply ENat.lt_natCast_add_one_iff.mp
    apply lt_of_not_ge
    intro h
    exact hBad ⟨hGood.1,(le_order_iff hHol).mp
      (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
  · exact (le_order_iff hHol).mpr hGood.2

private def oldMask {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter fun i=>i.castAdd 1∈S

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

theorem exists_original_anchored_controlled_order {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      controlledSeedOutput M hM x hx Φ Φs c SN SE U
 := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hSeed⟩:=exists_original_anchored_whole_ideal_order M hM x hx
  change wholeOrderOutput M hM x hx Φ Φs c SN SE U at hSeed
  have hKeep:=hSeed
  rcases hSeed with ⟨hWhole,hdρ,_hSourceOrder,g,_hg,_hgBad,hSharp⟩
  rcases hWhole with ⟨_hΦs,_hΦ0,_hcp,_hck,hcj,_hOld,_hLast,_hSourceN,_hSourceE,
    _hSN,_hSE,_h0c,_hzSource,_hzp,_hWz,hπ,_hAtlas,hQ1,_hzQ1,hdQ1,_hEword,hLength,
    _hU,_hzU,_hUc,_hNmask,_hEmask,_hEmptyH,_hBorn,_hTo,_hInv,_hSub,_hTSub,
    _hSrc,_hZero,_hDom,_hSource,hWholeTails⟩
  refine ⟨Φ,Φs,c,SN,SE,U,?_⟩
  dsimp only [controlledSeedOutput]
  refine ⟨hKeep,?_⟩
  intro Z R e hA z hz he0 hR
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let P:=projectionTest M
  let Q1:=P.geoTransform C π1
  let A : BlowupTower (CMfd.of (projectionAmbient X)) Y1:=.step .refl C π1 hπ
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
  have hP:=projection_test_isInvDomain M hM
  have hC : P.IsAdmissibleCentre C:=(projection_point_centre M hM x hx).1
  have hFirst : IsGeoTestTower P A:=⟨trivial,hC⟩
  have hT : IsGeoTestTower P T:=
    (isGeoTestTower_append_iff P A R).mpr ⟨hFirst,hR⟩
  have hRecord : Q=P.geoTransformAlong T:=(geoTransformAlong_append P A R).symm
  have hQ : IsInvDomain (k+1) Q:=isInvDomain_geoTransformAlong hQ1 R hR
  have hdQ : Q.d=M.d:=(d_geoTransformAlong Q1 R).trans hdQ1
  have hLen : Q.E.length=M.E.length+2+R.length := by
    rw [length_E_geoTransformAlong, hLength]
  have hBComp : B=GermIdeal.pullback (m:=n+1) T.proj P.ideal := by
    change GermIdeal.pullback (m:=n+1) R.proj
      (GermIdeal.pullback (m:=n+1) π1 P.ideal)=_
    have hProj : T.proj=π1∘R.proj := by
      simp only [T,A,BlowupTower.proj_append,BlowupTower.proj_step,
        BlowupTower.proj_refl,Function.id_comp]
    rw [hProj,pullback_comp hπ.contMDiff R.contMDiff_proj hP.isWellFormed.isCoherent]
  have hdP : P.d=M.d:=(projection_test_dictionary M hM).2.2.1
  have hFactors:=original_tower_factor P hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent T hT
  have hBProd : RestrictLe Q.N B (F.mul Q.ideal) := by
    simpa only [←hRecord,←hBComp,hdP] using hFactors.1
  have hProdB : RestrictLe Q.N (F.mul Q.ideal) B := by
    simpa only [←hRecord,←hBComp,hdP] using hFactors.2
  have hWholeAt:=hWholeTails R e hA z hz he0
  have hzN : z∈Q.N:=hWholeAt.2.1
  have hSharpAt:=hSharp R e hA z hz he0
  rcases hSharpAt with ⟨hBGood,hBBad,_hBNat,_hBOrd,_hgB,_hgGood,_hgBad⟩
  have hTotal:=anchored_seed_total_factor c hπ hcj R e hA z hz
  have hFGen : ∀f : Z→ℂ,F.mem z f↔IsInSpanAt (n:=n+1)
      (·=fun v=>e v (Fin.last n)^ν) z f := hTotal.2 M.d
  obtain ⟨hFGood,hFBad⟩:=same_seed_total_power_sharp P hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent hC c hπ hcj R hR e hA z hz hzN he0 M.d
  have hFOrd:=enat_from_sharp Q.N F z ν
    (fun _ hf=>GermIdealOrder.holomorphicAt_of_mem_idealPow hf) hFGood hFBad
  have hSplit : M.d+(ρ-M.d)=ρ:=Nat.add_sub_of_le hdρ
  have hSum : ν+s=μ := by
    dsimp only [ν,s,μ]
    calc
      q*M.d+(ρ+q*(ρ-M.d))=ρ+q*(M.d+(ρ-M.d)) := by ring
      _=ρ+q*ρ := by rw [hSplit]
      _=(q+1)*ρ := by ring
  have hνμ : ν≤μ:=by omega
  have hDiff : μ-ν=s:=by omega
  have hProductGood : z∈cosupport (n+1) Q.N (F.mul Q.ideal) μ:=
    cosupport_subset_of_restrictLe hProdB μ hBGood
  have hQGood : z∈cosupport (n+1) Q.N Q.ideal s := by
    have hh:=mem_cosupport_of_mem_cosupport_mul_along hQ.isWellFormed.isClosedSubmanifold_N.2
      (fun _ _ hf=>GermIdealOrder.holomorphicAt_of_mem_idealPow hf)
      (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hf)
      hνμ hProductGood hFBad
    simpa only [hDiff] using hh
  have hQBad : z∉cosupport (n+1) Q.N Q.ideal (s+1) := by
    intro h
    have hProd:=inter_cosupport_subset_cosupport_mul ν (s+1) ⟨hFGood,h⟩
    have hAdd : ν+(s+1)=μ+1:=by omega
    rw [hAdd] at hProd
    exact hBBad (cosupport_subset_of_restrictLe hBProd (μ+1) hProd)
  have hQOrd:=enat_from_sharp Q.N Q.ideal z s
    (fun _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hf)
    hQGood hQBad
  have hCrit (a : ℕ) : z∈cosupport (n+1) Q.N Q.ideal a ↔
      a≤ordinaryTraceOrder Q.N Q.ideal z :=
    ordinaryTraceOrder_cosupport_iff hQ.isWellFormed.isClosedSubmanifold_N
      hQ.isWellFormed.isCoherent hQ.isNonzeroAlongAt hzN a
  have hQNat : ordinaryTraceOrder Q.N Q.ideal z=s := by
    apply Nat.le_antisymm
    · by_contra h
      exact hQBad ((hCrit (s+1)).mpr (by omega))
    · exact (hCrit s).mp hQGood
  have hds : M.d≤s:=by dsimp only [s];omega
  have hzQ : z∈Q.cosupp := by
    change z∈cosupport (n+1) Q.N Q.ideal Q.d
    rw [hdQ]
    exact cosupport_anti hds hQGood
  have hPoint : Q.IsAdmissibleCentre ({z} : Set Z) :=
    ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence z).1,
      (fun y hy=>by rw [mem_singleton_iff.mp hy];exact hzQ),
      hasNormalCrossings_singleton z hQ.isWellFormed.isSNCDivisor⟩
  dsimp only [controlledTailOutput]
  exact ⟨hT,hRecord,hQ,hdQ,hLen,hBComp,hBProd,hProdB,hFGen,hFGood,hFBad,hFOrd,
    hSum,hQGood,hQBad,hQNat,hQOrd,hds,hzQ,hPoint⟩

end
end Hironaka.HironakaActualAnchoredControlledOrder
