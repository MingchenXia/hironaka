import Hironaka.Resolution.HironakaActualAnchoredVerticalChart
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Analytic.PointSupportedIdealPrincipalization

/-! Actual strict-carrier masks from SOURCE masks and primitive anchored
charts. No current mask, inverse-lift, test/order/cosupport packet is input.
The original source restriction and proper-mask germ square remain separate. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredStrictCarrierMask
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold BlowupSNCTransform NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaActualAnchoredVerticalChart HironakaActualProjectionVerticalBlowupChart
  HironakaActualProjectionTestRecord PointSupportedIdealPrincipalization
  HironakaActualAnalyticBlowupTaylor
open scoped ProductComplexManifold

/-- The target ACTUAL chart/inverse proves strict membership by closure and
LAST perturbation. Only the SOURCE mask is a premise. -/
theorem strict_point_chart_mask {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (N : Set X) (x : X) {π : Y→X} (hπ : IsBlowupAlong (n+1) ({x} : Set X) π)
    (a : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1)))
    (U : Set X) (hU : IsOpen U) (_hxU : x∈U) (hxa : x∈a.source) (ha0 : a x=0)
    (S : Finset (Fin (n+1))) (hS : Fin.last n∉S)
    (hSource : ∀v∈U∩a.source,v∈N↔a v∈coordSubspace S)
    (hNative : ∀v∈e.source,π v∈a.source ∧ a (π v)=monomial 0 (Fin.last n) (e v)) :
    ∀v∈e.source∩π ⁻¹' (U∩a.source),
      v∈geoStrictTransform π ({x} : Set X) N ↔ e v∈coordSubspace S := by
  let W : Set Y := e.source∩π ⁻¹' (U∩a.source)
  have hW : IsOpen W := e.open_source.inter
    ((hU.inter a.open_source).preimage hπ.contMDiff.continuous)
  have hCentre (v : Y) (hv : v∈W) : π v∈({x} : Set X)↔e v (Fin.last n)=0 := by
    rw [mem_singleton_iff]
    constructor
    · intro h
      have hc := congrArg (fun w : ComplexModel (n+1)=>w (Fin.last n)) (hNative v hv.1).2
      rw [h,ha0] at hc
      simpa [monomial_apply] using hc.symm
    · intro h
      have hz : monomial 0 (Fin.last n) (e v)=0 := by
        ext i
        simp [monomial_apply,h]
        rintro rfl
        exact h
      exact a.injOn (hNative v hv.1).1 hxa (by rw [(hNative v hv.1).2,hz,ha0])
  have hOff (v : Y) (hv : v∈W) :
      v∈π ⁻¹' (N\({x} : Set X)) ↔ e v∈coordSubspace S ∧ e v (Fin.last n)≠0 := by
    constructor
    · intro h
      have ht : e v (Fin.last n)≠0 := fun hz=>h.2 ((hCentre v hv).mpr hz)
      have hm := (hSource (π v) hv.2).mp h.1
      rw [(hNative v hv.1).2] at hm
      exact ⟨((monomial_mem_coordSubspace_iff ht).mp hm).2,ht⟩
    · rintro ⟨hvS,hv0⟩
      refine ⟨(hSource (π v) hv.2).mpr ?_,fun hxC=>hv0 ((hCentre v hv).mp hxC)⟩
      rw [(hNative v hv.1).2]
      exact monomial_mem_coordSubspace hvS
  intro v hv
  change v∈W at hv
  constructor
  · intro hcl
    by_contra hn
    have hev : ∀ᶠw in 𝓝 v,w∈W ∧ e w∉coordSubspace S :=
      Filter.Eventually.and (hW.mem_nhds hv) ((e.continuousAt hv.1).eventually_mem
        ((isClosed_coordSubspace S).isOpen_compl.mem_nhds hn))
    obtain ⟨w,hw,hOffN⟩ := mem_closure_iff_nhds.mp hcl _ hev
    exact hw.2 ((hOff w hw.1).mp hOffN).1
  · intro hvS
    by_cases hv0 : e v (Fin.last n)=0
    · change v∈closure (π ⁻¹' (N\({x} : Set X)))
      rw [mem_closure_iff_nhds]
      intro A hA
      have hPre : e.symm ⁻¹' (A∩W)∈𝓝 (e v) := by
        apply e.tendsto_symm hv.1
        exact Filter.inter_mem hA (hW.mem_nhds hv)
      have hT : e.target∩e.symm ⁻¹' (A∩W)∈𝓝 (e v) :=
        Filter.inter_mem (e.open_target.mem_nhds (e.map_source hv.1)) hPre
      let ej : ComplexModel (n+1) := EuclideanSpace.single (Fin.last n) 1
      have hCurve : Tendsto (fun t : ℂ=>e v+t•ej) (𝓝 0) (𝓝 (e v)) := by
        have hc : Continuous (fun t : ℂ=>e v+t•ej) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa using hc.tendsto 0
      have hEv : ∀ᶠt in 𝓝[≠] (0 : ℂ),
          e v+t•ej∈e.target∩e.symm ⁻¹' (A∩W) ∧ t≠0 :=
        (show ∀ᶠt in 𝓝[≠] (0 : ℂ),e v+t•ej∈e.target∩e.symm ⁻¹' (A∩W) from
          mem_nhdsWithin_of_mem_nhds (hCurve.eventually hT)).and self_mem_nhdsWithin
      obtain ⟨t,⟨htTarget,htAW⟩,ht0⟩ := hEv.exists
      refine ⟨e.symm (e v+t•ej),htAW.1,(hOff _ htAW.2).mpr ⟨?_,?_⟩⟩
      · rw [e.right_inv htTarget]
        intro i hi
        have hij : i≠Fin.last n := fun he=>hS (he ▸ hi)
        simp [ej,hvS i hi,hij]
      · rw [e.right_inv htTarget]
        simpa [ej,hv0] using ht0
    · exact subset_closure ((hOff v hv).mpr ⟨hvS,hv0⟩)

private theorem mask_along {n : ℕ} {X : CMfd.{u} (n+1)}
    (M0 : MarkedIdeal (n+1) X) (a : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (a0 : X) (ha0 : a0∈a.source) (haZero : a a0=0)
    (U : Set X) (hU : IsOpen U) (haU : a0∈U)
    (S : Finset (Fin (n+1))) (hS : Fin.last n∉S)
    (hSource : ∀v∈U∩a.source,v∈M0.N↔a v∈coordSubspace S) :
    {Y : CMfd.{u} (n+1)} → (R : BlowupTower X Y) →
      (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) → AnchoredInheritedLastChartChain a R e →
      ∀v∈e.source∩R.proj ⁻¹' (U∩a.source),
        v∈(M0.geoTransformAlong R).N ↔ e v∈coordSubspace S
  | _,.refl,e,h,v,hv => by
      rcases h with ⟨rfl,_ha⟩
      exact hSource v hv.2
  | _,.step R C π hπ,e',h,v,hv => by
      obtain ⟨_he',e,x,Φ,hPrev,hC,hx,h0,_hSrc,_hFlat,hInh,_hNative⟩ := h
      let Uold : Set _ := e.source∩R.proj ⁻¹' (U∩a.source)
      have hUold : IsOpen Uold := e.open_source.inter
        ((hU.inter a.open_source).preimage R.contMDiff_proj.continuous)
      have hOrigin := anchored_origin_preimage_window a R e hPrev a0 ha0 haZero x hx h0 U hU haU
      have hxUold : x∈Uold := ⟨hx,by
        change R.proj x∈U∩a.source
        rw [hOrigin.1]
        exact ⟨haU,ha0⟩⟩
      have hOldMask := mask_along M0 a a0 ha0 haZero U hU haU S hS hSource R e hPrev
      have hπx : IsBlowupAlong (n+1) ({x} : Set _) π := by simpa only [hC] using hπ
      have hStep := strict_point_chart_mask (M0.geoTransformAlong R).N x hπx e e' Uold hUold
        hxUold hx h0 S hS (fun w hw=>hOldMask w hw.1) hInh
      have hOldV : π v∈Uold := ⟨(hInh v hv.1).1,hv.2⟩
      have hh := hStep v ⟨hv.1,hOldV,(hInh v hv.1).1⟩
      change v∈geoStrictTransform π C (M0.geoTransformAlong R).N ↔ e' v∈coordSubspace S
      simpa only [hC] using hh

/-- Exact OUTPUT window/current carrier mask, with ACTUAL origin incidence.
No native test or ideal/order/cosupport datum is needed by this geometry. -/
theorem anchored_strict_carrier_mask {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (M0 : MarkedIdeal (n+1) X) (a : OpenPartialHomeomorph X (ComplexModel (n+1)))
    (a0 : X) (ha0 : a0∈a.source) (haZero : a a0=0)
    (U : Set X) (hU : IsOpen U) (haU : a0∈U)
    (S : Finset (Fin (n+1))) (hS : Fin.last n∉S)
    (hSource : ∀v∈U∩a.source,v∈M0.N↔a v∈coordSubspace S)
    (R : BlowupTower X Y) (e : OpenPartialHomeomorph Y (ComplexModel (n+1)))
    (h : AnchoredInheritedLastChartChain a R e) :
    let V := e.source∩R.proj ⁻¹' (U∩a.source)
    IsOpen V ∧ (∀v∈V,v∈(M0.geoTransformAlong R).N↔e v∈coordSubspace S) ∧
      ∀z∈e.source,e z=0 → z∈V ∧ z∈(M0.geoTransformAlong R).N := by
  dsimp only
  have hMask := mask_along M0 a a0 ha0 haZero U hU haU S hS hSource R e h
  refine ⟨e.open_source.inter ((hU.inter a.open_source).preimage R.contMDiff_proj.continuous),hMask,?_⟩
  intro z hz he0
  have hOrigin := anchored_origin_preimage_window a R e h a0 ha0 haZero z hz he0 U hU haU
  have hzV : z∈e.source∩R.proj ⁻¹' (U∩a.source) := ⟨hz,by
    change R.proj z∈U∩a.source
    rw [hOrigin.1]
    exact ⟨haU,ha0⟩⟩
  exact ⟨hzV,(hMask z hzV).mpr (by rw [he0];intro i hi;rfl)⟩

private instance point_closed_fact {r : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel r) X] [IsComplexManifold r X] (x : X) :
    Fact (IsClosedSubmanifold r ({x} : Set X)) := ⟨(singleton_geometry_and_coherence x).1⟩

private abbrev recordMark {r : ℕ} (X : CMfd.{u} r) (Q : MarkedIdeal r X) : ℕ :=
  @MarkedIdeal.d r X.carrier X.topologicalSpace X.chartedSpace Q

private abbrev recordBoundary {r : ℕ} (X : CMfd.{u} r) (Q : MarkedIdeal r X) : List (Set X) :=
  @MarkedIdeal.E r X.carrier X.topologicalSpace X.chartedSpace Q

/- Fully reducible OUTPUT notation: retain EVERY actual ordinary seed field,
then add the derived CURRENT native mask at each given anchored tail. No packet is input. -/
private abbrev currentMaskOutput {n k : ℕ} {X : CMfd.{u} n}
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
    (let V := e.source∩R.proj ⁻¹' (U∩c.source);
      IsOpen V ∧ (∀v∈V,v∈(Q.geoTransformAlong R).N↔e v∈coordSubspace SN) ∧
        ∀w∈e.source,e w=0 → w∈V ∧ w∈(Q.geoTransformAlong R).N) ∧
    (∀v∈e.source,R.proj v∈c.source ∧
      c.toFun (R.proj v)=(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length] (e v)) ∧
    ∀w∈e.source,e w=0 → R.proj w=z ∧
      ∃V : Set Z,V=e.source∩R.proj ⁻¹' (U∩c.source) ∧ IsOpen V ∧ w∈V ∧ V⊆e.source ∧
        ∀v∈V,R.proj v∈U∩c.source ∧
          c.toFun (R.proj v)=(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0))^[R.length] (e v)

/-- ONLY original M/domain/xcosupp derive the SOURCE seed and ALL conditional
current carrier masks; no current mask, test/order/cosupport packet is supplied. -/
theorem exists_original_anchored_current_carrier_mask {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      currentMaskOutput M hM x hx Φ c SN SE U := by
  obtain ⟨Φ,c,SN,SE,U,hSeed⟩ := exists_original_anchored_vertical_frame M hM x hx
  rcases hSeed with ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
    hEmask,hEmptyH,hBorn,hAnchor0,hTails⟩
  refine ⟨Φ,c,SN,SE,U,?_⟩
  dsimp only [currentMaskOutput]
  refine ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
    hEmask,hEmptyH,hBorn,hAnchor0,?_⟩
  intro Z R e hAnchor
  refine ⟨?_,hTails R e hAnchor⟩
  let C : Set (projectionAmbient X) := {(x,0)}
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π1 : Y1→projectionAmbient X := blowupProj (n+1) C
  let Q1 : MarkedIdeal (n+1) Y1 := (projectionTest M).geoTransform C π1
  have hSeedZero : c.homeo (c.invFun 0)=0 := hWz
  have hSeedSource : c.invFun 0∈c.homeo.source := hzSource
  exact anchored_strict_carrier_mask (n:=n) Q1 c.homeo (c.invFun 0) hSeedSource hSeedZero
    U hU hzU SN hSN (fun v hv=>hNmask v hv.1) R e hAnchor

end
end Hironaka.HironakaActualAnchoredStrictCarrierMask
