import Hironaka.Resolution.HironakaActualAnchoredControlledOrder
import Hironaka.Resolution.HironakaActualAnchoredBoundaryMasks
import Hironaka.Resolution.HironakaActualInheritedVerticalPointChart

/-! ONE genuine successor from the SAME original anchored seed and an
ALREADY BUILT native test prefix. Incident masks retain EVERY native E slot.
No next-point cosupport from505, mixed base, all-q family or CAN is claimed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredSuccessorTest
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

private instance point_closed_fact {a : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X] (x : X) :
    Fact (IsClosedSubmanifold a ({x} : Set X)) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1⟩

private def masksOfTraceWord {n ℓ : ℕ} {Z : Type u}
    (E : List (Set Z)) (r : ℕ) (S : Fin ℓ→Finset (Fin (n+1))) :
    Fin E.length→Finset (Fin (n+1)) := fun i=>
  if h : i.val<ℓ then S ⟨i.val,h⟩
  else if i.val<ℓ+r then ∅ else {Fin.last n}

/-- The conclusion is INCIDENT-only. An EMPTY divisor is never represented
unconditionally by coordSubspace EMPTY (which would be the full carrier). -/
private theorem incident_masks_of_full_trace_word {n ℓ : ℕ} {Z : Type u}
    (E : List (Set Z)) (V : Set Z) (e : Z→ComplexModel (n+1))
    (S : Fin ℓ→Finset (Fin (n+1))) (P : Fin ℓ→Prop) (r : ℕ)
    (hWord : E.map (fun K=>V∩K)=
      List.ofFn (fun i : Fin ℓ=>{v | v∈V ∧ P i ∧ e v∈coordSubspace (S i)}) ++
      List.replicate r (∅ : Set Z) ++ [V∩{v | e v (Fin.last n)=0}])
    (z : Z) (hzV : z∈V) (_hz0 : e z=0) :
    E.length=ℓ+r+1 ∧
    ∀i : Fin E.length,z∈E.get i→∀v∈V,
      (v∈E.get i ↔ e v∈coordSubspace (masksOfTraceWord E r S i)) := by
  have hLen : E.length=ℓ+r+1 := by
    have hh:=congrArg List.length hWord
    simp only [List.length_map,List.length_append,List.length_ofFn,List.length_replicate,
      List.length_singleton] at hh
    omega
  refine ⟨hLen,?_⟩
  intro i hzi
  have hiW : i.val<(List.ofFn (fun j : Fin ℓ=>
      {v | v∈V ∧ P j ∧ e v∈coordSubspace (S j)}) ++
      List.replicate r (∅ : Set Z) ++ [V∩{v | e v (Fin.last n)=0}]).length := by
    rw [←hWord,List.length_map]
    exact i.isLt
  have hAt : V∩E.get i=(List.ofFn (fun j : Fin ℓ=>
      {v | v∈V ∧ P j ∧ e v∈coordSubspace (S j)}) ++
      List.replicate r (∅ : Set Z) ++ [V∩{v | e v (Fin.last n)=0}])[i.val]'hiW := by
    simp only [←hWord,List.getElem_map,List.get_eq_getElem]
  simp only [List.append_assoc] at hAt
  by_cases hi : i.val<ℓ
  · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hi),
      List.getElem_ofFn] at hAt
    have hPi : P ⟨i.val,hi⟩ := by
      have hh : z∈V∩E.get i:=⟨hzV,hzi⟩
      rw [hAt] at hh
      exact hh.2.1
    intro v hv
    simp only [masksOfTraceWord,dif_pos hi]
    constructor
    · intro h
      have hh : v∈V∩E.get i:=⟨hv,h⟩
      rw [hAt] at hh
      exact hh.2.2
    · intro h
      have hh : v∈{v | v∈V ∧ P ⟨i.val,hi⟩ ∧ e v∈coordSubspace (S ⟨i.val,hi⟩)}:=
        ⟨hv,hPi,h⟩
      rw [←hAt] at hh
      exact hh.2
  · rw [List.getElem_append_right (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)] at hAt
    by_cases hm : i.val<ℓ+r
    · rw [List.getElem_append_left (by simp only [List.length_ofFn,List.length_replicate];omega),
        List.getElem_replicate] at hAt
      have hh : z∈V∩E.get i:=⟨hzV,hzi⟩
      rw [hAt] at hh
      exact False.elim hh
    · have hlast : i.val=ℓ+r:=by have:=i.isLt;omega
      rw [List.getElem_append_right (by simp only [List.length_ofFn,List.length_replicate];omega)] at hAt
      simp only [List.length_ofFn,List.length_replicate,hlast,Nat.add_sub_cancel_left,
        Nat.sub_self,List.getElem_cons_zero] at hAt
      intro v hv
      simp only [masksOfTraceWord,dif_neg hi,if_neg hm]
      constructor
      · intro h
        have hh : v∈V∩E.get i:=⟨hv,h⟩
        rw [hAt] at hh
        intro j hj
        rw [Finset.mem_singleton.mp hj]
        exact hh.2
      · intro h
        have ht : e v (Fin.last n)=0:=h (Fin.last n) (Finset.mem_singleton_self _)
        have hh : v∈V∩{v | e v (Fin.last n)=0}:=⟨hv,ht⟩
        rw [←hAt] at hh
        exact hh.2

/-- The actual new FlatChart's OWN flattening equivalence builds the native
step predicate; the inherited full vector is the genuine generic505 output. -/
private theorem anchored_step_of_flat_chart {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (a : OpenPartialHomeomorph X (ComplexModel (n+1))) (R : BlowupTower X Y)
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1)))
    (hA : AnchoredInheritedLastChartChain a R e)
    (z : Y) (hz : z∈e.source) (he0 : e z=0)
    (c2 : FlatChart (n+1) ({z} : Set Y))
    (hc : c2.y₀=z) (hk : c2.k=0) (hj : c2.j=Fin.last n)
    (hπ2 : IsBlowupAlong (n+1) ({z} : Set Y) (blowupProj (n+1) ({z} : Set Y)))
    (hInh : ∀v∈c2.source,
      blowupProj (n+1) ({z} : Set Y) v∈e.source ∧
      e (blowupProj (n+1) ({z} : Set Y) v)=monomial 0 (Fin.last n) (c2.toFun v)) :
    AnchoredInheritedLastChartChain a
      (BlowupTower.step (Z:=CMfd.of (BlowupSpace (n+1) ({z} : Set Y)))
        R ({z} : Set Y) (blowupProj (n+1) ({z} : Set Y)) hπ2) c2.homeo := by
  have hAtlas:=atlasHomeo_mem_atlas c2.toPartialEquiv (Or.inl ⟨c2,rfl⟩)
  have hNative : ∀v∈c2.source,
      blowupProj (n+1) ({z} : Set Y) v∈flatDomain c2.Φ ∧
      monomial c2.k c2.j (c2.toFun v)=
        c2.Φ.toFun (chartAt (ComplexModel (n+1)) c2.y₀ (blowupProj (n+1) ({z} : Set Y) v)) :=
    fun v hv=>⟨hv.1,c2.monomial_toFun hv⟩
  rcases c2 with ⟨y0,k,Φ,hsrc,hflat,j,hj0⟩
  change y0=z at hc
  change k=0 at hk
  change j=Fin.last n at hj
  subst y0
  subst k
  subst j
  exact ⟨hAtlas,e,z,Φ,hA,rfl,hz,he0,hsrc,hflat,hInh,hNative⟩

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

theorem exists_original_anchored_successor_test {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      successorSeedOutput M hM x hx Φ Φs c SN SE U
 := by
  obtain ⟨Φ,Φs,c,SN,SE,U,hSeed⟩:=exists_original_anchored_controlled_order M hM x hx
  change controlledSeedOutput M hM x hx Φ Φs c SN SE U at hSeed
  have hKeep:=hSeed
  rcases hSeed with ⟨hOrder,hControlTails⟩
  rcases hOrder with ⟨hWhole,_hdρ,_hSourceOrder,_g,_hg,_hgBad,_hSharp⟩
  rcases hWhole with ⟨_hΦs,_hΦ0,_hcp,_hck,_hcj,_hOld,_hLast,_hSourceN,_hSourceE,
    hSN,hSE,_h0c,hzSource,_hzp,hWz,_hπ,_hAtlas,_hQ1,_hzQ1,_hdQ1,hEword,_hLength,
    hU,hzU,_hUc,hNmask,hEmask,hEmptyH,hBorn,_hTo,_hInv,_hSub,_hTSub,
    _hSrc,_hZero,_hDom,_hSource,_hWholeTails⟩
  let C : Set (projectionAmbient X):={(x,0)}
  let Y1 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X:=blowupProj (n+1) C
  let Q1:=(projectionTest M).geoTransform C π1
  let L : List (Set Y1):=M.E.map (fun K=>geoStrictTransform π1 C
    ((Prod.fst : projectionAmbient X→X) ⁻¹' K)) ++ [geoStrictTransform π1 C (horizontal X)]
  have hLenL : L.length=M.E.length+1:=by simp [L]
  have hE0 : Q1.E=L++[π1 ⁻¹' C] := by
    simpa only [L,List.append_assoc,List.cons_append,List.nil_append] using hEword
  let S0 : Fin L.length→Finset (Fin (n+1)):=fun i=>
    if hi : i.val<M.E.length then SE ⟨i.val,hi⟩ else ∅
  let P0 : Fin L.length→Prop:=fun i=>
    if hi : i.val<M.E.length then x∈M.E.get ⟨i.val,hi⟩ else False
  have hS0 : ∀i,Fin.last n∉S0 i := by
    intro i
    dsimp only [S0]
    split_ifs with hi
    · exact hSE ⟨i.val,hi⟩
    · simp
  have hSource : ∀i,∀v∈U∩c.homeo.source,
      v∈L.get i↔P0 i ∧ c.homeo v∈coordSubspace (S0 i) := by
    intro i v hv
    by_cases hi : i.val<M.E.length
    · have hGet : L.get i=geoStrictTransform π1 C
          ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get ⟨i.val,hi⟩) := by
        simp only [L,List.get_eq_getElem]
        rw [List.getElem_append_left (by simpa using hi),List.getElem_map]
      rw [hGet]
      simp only [S0,P0,dif_pos hi]
      constructor
      · intro hvK
        by_cases hxi : x∈M.E.get ⟨i.val,hi⟩
        · exact ⟨hxi,((hEmask ⟨i.val,hi⟩).1 hxi v hv.1).mp hvK⟩
        · exact False.elim ((hEmask ⟨i.val,hi⟩).2 hxi v hv.1 hvK)
      · rintro ⟨hxi,hvS⟩
        exact ((hEmask ⟨i.val,hi⟩).1 hxi v hv.1).mpr hvS
    · have hi0 : i.val=M.E.length := by
        have hil : i.val<M.E.length+1:=lt_of_lt_of_eq i.isLt hLenL
        omega
      have hGet : L.get i=geoStrictTransform π1 C (horizontal X) := by
        simp only [L,List.get_eq_getElem]
        rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
        simp [hi0]
      rw [hGet]
      simp only [S0,P0,dif_neg hi]
      constructor
      · exact fun hvK=>False.elim (hEmptyH v hv.1 hvK)
      · exact fun hvK=>False.elim hvK.1
  refine ⟨Φ,Φs,c,SN,SE,U,?_⟩
  dsimp only [successorSeedOutput]
  refine ⟨hKeep,?_⟩
  intro Z R e hA z hz he0 hR
  let Q:=Q1.geoTransformAlong R
  let V : Set Z:=e.source∩R.proj ⁻¹' (U∩c.source)
  have hCurrent:=hControlTails R e hA z hz he0 hR
  rcases hCurrent with ⟨_hT,_hRec,hQ,hdQ,hLenQ,_hBComp,_hBProd,_hProdB,_hFGen,
    _hFGood,_hFBad,_hFOrder,_hSum,_hQGood,_hQBad,_hQNat,_hQOrder,_hds,hzQ,_hPoint⟩
  have hStrict:=anchored_strict_carrier_mask Q1 c.homeo (c.invFun 0) hzSource hWz
    U hU hzU SN hSN (fun v hv=>hNmask v hv.1) R e hA
  rcases hStrict with ⟨hV,hN,hOrigin⟩
  have hzV : z∈V:=(hOrigin z hz he0).1
  have hBoundary:=anchored_boundary_word_masks Q1 L (π1 ⁻¹' C) hE0 c.homeo (c.invFun 0)
    hzSource hWz U hU hzU S0 P0 hS0 hSource (fun v hv=>hBorn v hv.1) R e hA
  rcases hBoundary with ⟨_hd,_hLen,_hVo,hWord,_hOrigin⟩
  have hIncident:=incident_masks_of_full_trace_word Q.E V e S0 P0 R.length hWord z hzV he0
  let SR : Fin Q.E.length→Finset (Fin (n+1)):=masksOfTraceWord Q.E R.length S0
  have he : e∈atlas (ComplexModel (n+1)) Z := by
    cases R with
    | refl => rcases hA with ⟨rfl,ha⟩;exact ha
    | step R C π hπ => exact hA.1
  obtain ⟨c2,hGeometry⟩:=exists_inherited_vertical_point_chart Q hQ z hzQ
    e he hz he0 V hV hzV inter_subset_left SN hSN hN SR hIncident.2
  rcases hGeometry with ⟨hcy0,hck,hcj,hTarget0,hz2,hz2π,hz20,hCz,hπ2,hz2N,
    _hWs,_hLift,hInh,hTargetN,hTargetE,hAbsent,hBorn2,hDomain2,hdNext,hEword2,hLength2⟩
  let Cz : Set Z:={z}
  let Z2 : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) Cz)
  let π2 : Z2→Z:=blowupProj (n+1) Cz
  let Q2:=Q.geoTransform Cz π2
  let R2 : BlowupTower Y1 Z2:=.step R Cz π2 hπ2
  have hR2 : IsGeoTestTower Q1 R2:=⟨hR,hCz⟩
  have hAtlas2:=atlasHomeo_mem_atlas c2.toPartialEquiv (Or.inl ⟨c2,rfl⟩)
  have hStepVector : ∀v∈c2.source,π2 v∈e.source ∧
      e (π2 v)=monomial 0 (Fin.last n) (c2.toFun v) :=
    fun v hv=>⟨(hInh v hv).1.1,(hInh v hv).2⟩
  have hA2:=anchored_step_of_flat_chart c.homeo R e hA z hz he0 c2 hcy0 hck hcj hπ2 hStepVector
  have hd2 : recordMark Z2 Q2=M.d:=hdNext.trans hdQ
  have hLen2 : (recordBoundary Z2 Q2).length=M.E.length+3+R.length := by
    change Q2.E.length=_
    calc
      Q2.E.length=Q.E.length+1:=hLength2
      _=M.E.length+3+R.length:=by omega
  dsimp only [successorTailOutput]
  exact ⟨hzQ,hQ,hV,hzV,hN,SR,hIncident.2,c2,hπ2,hcy0,hck,hcj,hTarget0,
    hz2,hz2π,hz20,hCz,hR2,hAtlas2,hA2,hInh,hz2N,hDomain2,hTargetN,hTargetE,
    hAbsent,hBorn2,hd2,hEword2,hLen2⟩

end
end Hironaka.HironakaActualAnchoredSuccessorTest
