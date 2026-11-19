import Hironaka.Resolution.HironakaActualInheritedVerticalTotalFactor
import Hironaka.Resolution.HironakaActualIteratedVerticalTaylor
import Hironaka.Analytic.PointSupportedIdealPrincipalization

/-! One ACTUAL native first chart anchors every GIVEN primitive tail frame.
This constructs neither future tests nor future selected-point cosupport.
The source-mask window is derived from ordinary original inputs. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredVerticalChart
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts BlowupStrictSubmanifold NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaActualInheritedVerticalTotalFactor HironakaActualIteratedVerticalTaylor
  HironakaActualAnalyticBlowupTaylor HironakaRelativeNormalIdeal
  HironakaActualProjectionVerticalOrder HironakaActualProjectionVerticalBlowupChart
  HironakaActualProjectionTestRecord PointSupportedIdealPrincipalization
open scoped ProductComplexManifold

/-- The base chart is fixed; all successor fields are primitive geometry.
There is no ideal/order/factor/test/cosupport/presentation field. -/
def AnchoredInheritedLastChartChain {n : ℕ} {X : CMfd.{u} (n+1)}
    (a : OpenPartialHomeomorph X (ComplexModel (n+1))) :
    {Y : CMfd.{u} (n+1)} → (R : BlowupTower X Y) →
      OpenPartialHomeomorph Y (ComplexModel (n+1)) → Prop
  | _,.refl,e => e=a ∧ a∈atlas (ComplexModel (n+1)) X
  | _,.step R C π _,e' =>
      e'∈atlas (ComplexModel (n+1)) _ ∧
      ∃(e : OpenPartialHomeomorph _ (ComplexModel (n+1))) (x : _)
        (Φ : LocalHolomorphicEquivAt (n:=n+1) (chartAt (ComplexModel (n+1)) x x)),
        AnchoredInheritedLastChartChain a R e ∧ C={x} ∧ x∈e.source ∧ e x=0 ∧
        Φ.source⊆(chartAt (ComplexModel (n+1)) x).target ∧
        (∀{y},y∈(chartAt (ComplexModel (n+1)) x).source →
          chartAt (ComplexModel (n+1)) x y∈Φ.source →
          (y∈C ↔ Φ.toFun (chartAt (ComplexModel (n+1)) x y)∈complexCoordinatePlane (n+1) 0)) ∧
        (∀v∈e'.source,π v∈e.source ∧ e (π v)=monomial 0 (Fin.last n) (e' v)) ∧
        (∀v∈e'.source,π v∈flatDomain Φ ∧
          monomial 0 (Fin.last n) (e' v)=Φ.toFun (chartAt (ComplexModel (n+1)) x (π v)))

/-- Forget only the base equality, retaining every actual geometric field. -/
theorem anchored_chain_to_unanchored {n : ℕ} {X : CMfd.{u} (n+1)}
    (a : OpenPartialHomeomorph X (ComplexModel (n+1))) :
    {Y : CMfd.{u} (n+1)} → (R : BlowupTower X Y) →
      (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) →
      AnchoredInheritedLastChartChain a R e → InheritedLastChartChain R e
  | _,.refl,e,h => by rcases h with ⟨rfl,ha⟩;exact ha
  | _,.step R C π hπ,e',h => by
      obtain ⟨he',e,x,Φ,hPrev,hC,hx,h0,hSrc,hFlat,hInh,hNative⟩ := h
      exact ⟨he',e,x,Φ,anchored_chain_to_unanchored a R e hPrev,
        hC,hx,h0,hSrc,hFlat,hInh,hNative⟩

private theorem monomial_eq_actual {n : ℕ} (w : ComplexModel (n+1)) :
    monomial 0 (Fin.last n) w=actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0) w := by
  ext i
  by_cases hi : i=Fin.last n
  · simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]
  · simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,mul_comm]

private theorem projection_vector {n : ℕ} {X : CMfd.{u} (n+1)}
    (a : OpenPartialHomeomorph X (ComplexModel (n+1))) :
    {Y : CMfd.{u} (n+1)} → (R : BlowupTower X Y) →
      (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) →
      AnchoredInheritedLastChartChain a R e →
      ∀v∈e.source,R.proj v∈a.source ∧
        a (R.proj v)=(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length] (e v)
  | _,.refl,e,h,v,hv => by
      rcases h with ⟨rfl,_ha⟩
      exact ⟨hv,rfl⟩
  | _,.step R C π hπ,e',h,v,hv => by
      obtain ⟨_he',e,x,Φ,hPrev,_hC,_hx,_h0,_hSrc,_hFlat,hInh,_hNative⟩ := h
      have hOld := projection_vector a R e hPrev (π v) (hInh v hv).1
      refine ⟨hOld.1,?_⟩
      change a (R.proj (π v))=
        (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length+1] (e' v)
      rw [Function.iterate_succ_apply,hOld.2,(hInh v hv).2,monomial_eq_actual]

/-- WHOLE anchored vector and all source inclusions, with genuine closed coordinates. -/
theorem anchored_chart_projection {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (a : OpenPartialHomeomorph X (ComplexModel (n+1))) (R : BlowupTower X Y)
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) (h : AnchoredInheritedLastChartChain a R e) :
    ∀v∈e.source,R.proj v∈a.source ∧
      a (R.proj v)=(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length] (e v) ∧
      (∀i : Fin n,a (R.proj v) (i.castAdd 1)=(e v (Fin.last n))^R.length*e v (i.castAdd 1)) ∧
      a (R.proj v) (Fin.last n)=e v (Fin.last n) := by
  intro v hv
  obtain ⟨hSource,hVector⟩ := projection_vector a R e h v hv
  have hCoords := iterated_vertical_base_coordinates n R.length (e v)
  refine ⟨hSource,hVector,?_,?_⟩
  · intro i
    rw [hVector]
    exact hCoords.1 i
  · rw [hVector]
    exact hCoords.2

private theorem iterate_zero (n r : ℕ) :
    (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[r] (0 : ComplexModel (n+1))=0 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply,actualAnalyticBlowupMap_zero,ih]

/-- The actual origin and its source-mask preimage window are derived, not assumed. -/
theorem anchored_origin_preimage_window {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (a : OpenPartialHomeomorph X (ComplexModel (n+1))) (R : BlowupTower X Y)
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) (h : AnchoredInheritedLastChartChain a R e)
    (a0 : X) (ha0 : a0∈a.source) (haZero : a a0=0)
    (z : Y) (hz : z∈e.source) (heZero : e z=0) (U : Set X) (hU : IsOpen U) (haU : a0∈U) :
    R.proj z=a0 ∧ ∃V : Set Y,V=e.source∩R.proj ⁻¹' (U∩a.source) ∧
      IsOpen V ∧ z∈V ∧ V⊆e.source ∧
      ∀v∈V,R.proj v∈U∩a.source ∧
        a (R.proj v)=(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length] (e v) := by
  have hVector := anchored_chart_projection a R e h z hz
  have hImage : R.proj z=a0 := a.injOn hVector.1 ha0 (by
    rw [hVector.2.1,heZero,iterate_zero,haZero])
  refine ⟨hImage,e.source∩R.proj ⁻¹' (U∩a.source),rfl,
    e.open_source.inter ((hU.inter a.open_source).preimage R.contMDiff_proj.continuous),
    ⟨hz,by change R.proj z∈U∩a.source;rw [hImage];exact ⟨haU,ha0⟩⟩,inter_subset_left,?_⟩
  intro v hv
  exact ⟨hv.2,(anchored_chart_projection a R e h v hv.1).2.1⟩

private instance point_closed_fact {r : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel r) X] [IsComplexManifold r X] (x : X) :
    Fact (IsClosedSubmanifold r ({x} : Set X)) := ⟨(singleton_geometry_and_coherence x).1⟩

private abbrev recordMark {r : ℕ} (X : CMfd.{u} r) (Q : MarkedIdeal r X) : ℕ :=
  @MarkedIdeal.d r X.carrier X.topologicalSpace X.chartedSpace Q

private abbrev recordBoundary {r : ℕ} (X : CMfd.{u} r) (Q : MarkedIdeal r X) : List (Set X) :=
  @MarkedIdeal.E r X.carrier X.topologicalSpace X.chartedSpace Q

/- Reducible OUTPUT notation only. Every ordinary source, full N/E/mark,
derived window and conditional anchored-tail field is written out below.
Phi/c/SN/SE/U are existential outputs, never incoming certificates. -/
private abbrev firstFrameOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
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
  AnchoredInheritedLastChartChain c.homeo (BlowupTower.refl : BlowupTower Y Y) c.homeo ∧
  ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1))),
    AnchoredInheritedLastChartChain c.homeo R e →
    (∀v∈e.source,R.proj v∈c.source ∧
      c.toFun (R.proj v)=(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length] (e v)) ∧
    ∀w∈e.source,e w=0 → R.proj w=z ∧
      ∃V : Set Z,V=e.source∩R.proj ⁻¹' (U∩c.source) ∧ IsOpen V ∧ w∈V ∧ V⊆e.source ∧
        ∀v∈V,R.proj v∈U∩c.source ∧
          c.toFun (R.proj v)=(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length] (e v)

/-- ONLY original M/domain/xcosupp choose the actual first native frame and
source-mask window before ALL given tails, functions and ideal queries. -/
theorem exists_original_anchored_vertical_frame {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      firstFrameOutput M hM x hx Φ c SN SE U := by
  obtain ⟨Φ,c,SN,SE,hGeometry,hOrder⟩ := exists_projection_vertical_order M hM x hx
  rcases hGeometry with ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,_hzN,_hWs,_hInv,_hMon,hTargetN,hTargetE,hEmptyH,hBorn,
    hWindow,hQ,hdQ,hEword,hLength⟩
  rcases hOrder with ⟨_hWhole,_hdρ,_hSourceOrder,_hBGood,_hBBad,_hBNat,_hBOrder,
    _hFGen,_hτGood,_hτBad,_hQGood,_hQBad,_hQNat,_hQOrder,_hdr,hzQ⟩
  obtain ⟨U,hU,hzU,hUc,hAbsent⟩ := hWindow
  have hAtlas := atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩)
  refine ⟨Φ,c,SN,SE,U,?_⟩
  dsimp only [firstFrameOutput]
  refine ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,?_,?_,?_,?_,⟨rfl,hAtlas⟩,?_⟩
  · exact fun v hv=>hTargetN v (hUc hv)
  · intro i
    exact ⟨fun hi v hv=>hTargetE i hi v (hUc hv),hAbsent i⟩
  · exact fun v hv=>hEmptyH v (hUc hv)
  · exact fun v hv=>hBorn v (hUc hv)
  · intro Z R e hAnchor
    constructor
    · intro v hv
      have hh := anchored_chart_projection c.homeo R e hAnchor v hv
      exact ⟨hh.1,hh.2.1⟩
    · intro w hw hw0
      have hSeedZero : c.homeo (c.invFun 0)=0 := hWz
      have hSeedSource : c.invFun 0∈c.homeo.source := hzSource
      exact anchored_origin_preimage_window (n:=n) c.homeo R e hAnchor (c.invFun 0) hSeedSource hSeedZero
        w hw hw0 U hU hzU

end
end Hironaka.HironakaActualAnchoredVerticalChart
