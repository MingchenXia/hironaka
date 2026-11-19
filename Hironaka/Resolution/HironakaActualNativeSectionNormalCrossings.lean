import Hironaka.Resolution.HironakaDisjointEmbeddedBoundaryLift
import Hironaka.Resolution.HironakaActualNativeSectionCoefficientRecords
import Hironaka.Resolution.HironakaActualNativeSectionPositiveLowerRecords
import Hironaka.Invariant.BoundaryCount
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Resolution.HironakaActualNativeSectionContactChoices

/-! Ambient normal crossings restrict to the ACTUAL induced native atlas.
The source chart dimension is derived, k=0 is retained, and actual native
TESTs are produced from ambient TESTs on the SAME geometry-only Lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionNormalCrossings
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  SimultaneousNormalCrossings BlowupSNCTransform BlowupFlatCoordinates GiraudAlong
  RegularPatchPullback RegularPointDimension SubmanifoldChartedSpace BoundaryCount
  HironakaActualSingularChartTransport HironakaRelativeNormalIdeal
  HironakaDisjointMatchedControlledTrace HironakaDisjointEmbeddedBoundaryLift
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionCoefficientRecords HironakaActualRawRecordPullbacks
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualNativeSectionContactChoices HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue

/-- The existing joint adapted chart, centred at zero and with its native
plane dimension INTERNALLY identified with the actual supplied regular dimension. -/
theorem exists_centered_native_joint_coordinates {n k : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (hn : 0<n) {C W : Set X} {E : List (Set X)} {x : X}
    (hWx : RegularAtDim (n:=n) W x k) (hCW : C⊆W)
    (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (hNC : HasNormalCrossings n C E) (hx : x∈C) :
    ∃a≤n,∃(Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (s : Fin E.length→Fin n),
      Θ.source⊆(chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      (∀i,x∈E.get i → (s i).val<k) ∧ Set.InjOn s {i | x∈E.get i} ∧
      ∀y∈flatDomain Θ,
        (y∈C ↔ flatMap Θ y∈complexCoordinatePlane n a) ∧
        (y∈W ↔ flatMap Θ y∈complexCoordinatePlane n k) ∧
        ∀i,x∈E.get i → (y∈E.get i ↔ flatCoord Θ (s i) y=0) := by
  obtain ⟨a,b,Φ,s,hsrc,hs,hinj,hflat⟩:=
    isAdaptedAt_of_hasNormalCrossings hn hCW hE hTrans hNC hx
  let c:=flatMap Φ x
  have hxD:=mem_flatDomain_self Φ
  have hcC : c∈complexCoordinatePlane n a:=(hflat hxD.1 hxD.2).1.mp hx
  have hcW : c∈complexCoordinatePlane n b:=(hflat hxD.1 hxD.2).2.1.mp (hCW hx)
  have hcE : ∀i,x∈E.get i → c (s i)=0:=
    fun i hi=>(hflat hxD.1 hxD.2).2.2 i hi |>.mp hi
  have hSubPlane (r : ℕ) (z : ComplexModel n) (hc : c∈complexCoordinatePlane n r) :
      z-c∈complexCoordinatePlane n r ↔ z∈complexCoordinatePlane n r:=by
    constructor
    · intro hz j hj
      have he:=hz j hj
      simpa only [PiLp.sub_apply,hc j hj,sub_zero] using he
    · intro hz j hj
      change z j-c j=0
      rw [hz j hj,hc j hj,sub_self]
  let Θ:=subConst Φ c
  have hΘsrc : Θ.source⊆(chartAt (ComplexModel n) x).target:=hsrc
  have hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0:=sub_self _
  have hFlatW : ∀{y : X},y∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y∈Θ.source →
      (y∈W ↔ flatMap Θ y∈complexCoordinatePlane n b):=by
    intro y hy hyΘ
    exact (hflat hy hyΘ).2.1.trans (hSubPlane b (flatMap Φ y) hcW).symm
  have hWb : RegularAtDim (n:=n) W x (min b n):=by
    refine ⟨Nat.min_le_right _ _,hCW hx,Θ,hΘsrc,hΘ0,?_⟩
    intro y hy hyΘ
    rw [complexCoordinatePlane_min]
    exact hFlatW hy hyΘ
  have hb : min b n=k:=eq_of_regularAtDim hWb hWx
  refine ⟨min a n,Nat.min_le_right _ _,Θ,s,hΘsrc,hΘ0,?_,hinj,?_⟩
  · intro i hi
    have hiB:=hs i hi
    have hiN:=(s i).isLt
    omega
  · intro y hy
    refine ⟨?_,?_,?_⟩
    · rw [complexCoordinatePlane_min]
      exact (hflat hy.1 hy.2).1.trans (hSubPlane a (flatMap Φ y) hcC).symm
    · rw [←hb,complexCoordinatePlane_min]
      exact hFlatW hy.1 hy.2
    · intro i hi
      have he:=(hflat hy.1 hy.2).2.2 i hi
      change (y∈E.get i ↔ (Φ.toFun (chartAt (ComplexModel n) x y)-c) (s i)=0)
      simpa only [PiLp.sub_apply,hcE i hi,sub_zero] using he

private theorem tangent_plane_iff {d t : ℕ} (a : ℕ) (z : ComplexModel d) :
    tangentInclusion d t z∈complexCoordinatePlane (d+t) a ↔ z∈complexCoordinatePlane d a:=by
  constructor
  · intro h j hj
    simpa only [tangentInclusion_tangent] using h (j.castAdd t) hj
  · intro h i hi
    by_cases hid : i.val<d
    · let j : Fin d:=⟨i.val,hid⟩
      have hji : j.castAdd t=i:=Fin.ext rfl
      rw [←hji,tangentInclusion_tangent]
      exact h j hi
    · let j : Fin t:=⟨i.val-d,by have hlt:=i.isLt;omega⟩
      have hji : j.natAdd d=i:=by apply Fin.ext;dsimp only [j,Fin.natAdd];omega
      rw [←hji,tangentInclusion_normal]

private theorem native_crossings_core {d t : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    {W : Set X} (hW : ∀x∈W,RegularAtDim (n:=d+t) W x d)
    (hn : 0<d+t) {E : List (Set X)} (hE : IsSNCDivisor (d+t) E)
    (hTrans : IsTransverse (d+t) W E) :
    letI:=chartedSpace (Nat.le_add_right d t) hW
    letI:=isComplexManifold_chartedSpace (Nat.le_add_right d t) hW
    ∀D : Set W,HasNormalCrossings (d+t) ((Subtype.val : W→X) '' D) E →
      HasNormalCrossings d D (E.map ((Subtype.val : W→X) ⁻¹' ·)) := by
  classical
  let := chartedSpace (Nat.le_add_right d t) hW
  have := isComplexManifold_chartedSpace (Nat.le_add_right d t) hW
  intro D hNC p hp
  let C:=(Subtype.val : W→X) '' D
  have hCW : C⊆W:=by rintro _ ⟨q,_hq,rfl⟩;exact q.property
  obtain ⟨a,_ha,Θ,s,hΘsrc,hΘ0,hs,_hinj,hflat⟩:=
    exists_centered_native_joint_coordinates hn (hW p.val p.property) hCW hE hTrans hNC ⟨p,hp,rfl⟩
  have hFlatW : ∀y,y∈(chartAt (ComplexModel (d+t)) p.val).source →
      chartAt (ComplexModel (d+t)) p.val y∈Θ.source →
      (y∈W ↔ Θ.toFun (chartAt (ComplexModel (d+t)) p.val y)∈complexCoordinatePlane (d+t) d):=
    fun y hy hyΘ=>(hflat y ⟨hy,hyΘ⟩).2.1
  obtain ⟨Ψ,hΨ0,hMatch⟩:=exists_matched_coordinates hW p Θ hΘsrc hΘ0 hFlatW
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel d) W ∞)
  let e:=chartAt (ComplexModel d) p
  let Γ:=Ψ.restrict e.target e.open_target (e p) ⟨Ψ.center_mem_source,mem_chart_target _ p⟩
  have hΓsrc : Γ.source⊆e.target:=inter_subset_right
  have hΓ0 : Γ.toFun (e p)=0:=hΨ0
  have hMatchΓ : ∀ᶠ u in 𝓝 (0 : ComplexModel d),
      (inverseCoordinates Γ u).val=inverseCoordinates Θ (tangentInclusion d t u):=hMatch
  have hForward : Tendsto (flatMap Γ) (𝓝 p) (𝓝 0):=by
    have hc : ContinuousAt (flatMap Γ) p:=
      (Γ.toFun_holomorphic.differentiableAt (Γ.isOpen_source.mem_nhds Γ.center_mem_source)).continuousAt.comp
        (e.continuousAt (mem_chart_source _ p))
    have hc0 : flatMap Γ p=0:=hΓ0
    simpa only [hc0] using hc.tendsto
  have hInc : Tendsto (fun y : W=>tangentInclusion d t (flatMap Γ y)) (𝓝 p) (𝓝 0):=by
    simpa only [Function.comp_def,map_zero] using
      ((tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)).comp hForward
  have hΘtarget : (0 : ComplexModel (d+t))∈Θ.target:=hΘ0 ▸ Θ.mapsTo_toFun Θ.center_mem_source
  have hDomainΘ : ∀ᶠ y : W in 𝓝 p,y.val∈flatDomain Θ:=
    ((isOpen_flatDomain Θ).preimage continuous_subtype_val).mem_nhds (mem_flatDomain_self Θ)
  have hNear : ∀ᶠ y : W in 𝓝 p,y.val∈flatDomain Θ ∧
      flatMap Θ y.val=tangentInclusion d t (flatMap Γ y):=by
    filter_upwards [(isOpen_flatDomain Γ).mem_nhds (mem_flatDomain_self Γ),hDomainΘ,
      hForward.eventually hMatchΓ,hInc.eventually (Θ.isOpen_target.mem_nhds hΘtarget)] with y hyΓ hyΘ hm ht
    have hyRound : inverseCoordinates Γ (flatMap Γ y)=y:=flatInverse_flat Γ hyΓ
    rw [hyRound] at hm
    refine ⟨hyΘ,?_⟩
    rw [hm]
    exact (flatInverse_mem Θ ht hΘsrc).2
  have hDimage (y : W) : y∈D ↔ y.val∈C:=by
    constructor
    · intro hy;exact ⟨y,hy,rfl⟩
    · rintro ⟨q,hq,hqy⟩
      exact (Subtype.ext hqy : q=y) ▸ hq
  let A : Option (Fin E.length)→Set W:=fun o=>o.elim D (fun i=>(Subtype.val : W→X) ⁻¹' E.get i)
  let S0 : Finset (Fin d):=Finset.univ.filter (fun j=>a≤j.val)
  let S : Fin E.length→Finset (Fin d):=fun i=>
    if hi : p.val∈E.get i then {⟨(s i).val,hs i hi⟩} else ∅
  have hFamily : IsCoordinateFamilyAt d A (fun o=>o.elim S0 S) p:=by
    apply coordinate_family_of_eventual_native A (fun o=>o.elim S0 S) p Γ hΓsrc hΓ0
    rintro (_|i) hi
    · filter_upwards [hNear] with y hy
      change y∈D ↔ flatMap Γ y∈coordSubspace S0
      rw [show S0=Finset.univ.filter (fun j : Fin d=>a≤j.val) from rfl,
        coordSubspace_eq_complexCoordinatePlane]
      apply (hDimage y).trans
      apply (hflat y.val hy.1).1.trans
      rw [hy.2]
      exact tangent_plane_iff a (flatMap Γ y)
    · have hpEi : p.val∈E.get i:=hi
      let j : Fin d:=⟨(s i).val,hs i hpEi⟩
      have hji : j.castAdd t=s i:=Fin.ext rfl
      filter_upwards [hNear] with y hy
      have he:=(hflat y.val hy.1).2.2 i hpEi
      change y.val∈E.get i ↔ flatMap Γ y∈coordSubspace (S i)
      rw [show S i={j} from dif_pos hpEi,mem_coordSubspace_singleton]
      have hCoord : flatCoord Θ (s i) y.val=flatMap Γ y j:=by
        change flatMap Θ y.val (s i)=_
        rw [hy.2,←hji,tangentInclusion_tangent]
      rwa [hCoord] at he
  let c : Fin (E.map ((Subtype.val : W→X) ⁻¹' ·)).length→Fin E.length:=Fin.cast (List.length_map _)
  refine ⟨S0,fun i=>S (c i),?_,?_⟩
  · refine NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hFamily (Option.map c) ?_ ?_
    · rintro (_|i)
      · rfl
      · exact get_map_preimage E i
    · rintro (_|i) <;> rfl
  · intro i hi
    have hpEi : p.val∈E.get (c i):=by
      rw [get_map_preimage E i] at hi
      exact hi
    change (S (c i)).card=1
    rw [show S (c i)={⟨(s (c i)).val,hs (c i) hpEi⟩} from dif_pos hpEi,Finset.card_singleton]

/-- Ambient-image NC with the ENTIRE boundary gives native NC on the ACTUAL
induced atlas, in every native dimension including zero. -/
theorem hasNormalCrossings_native_preimage {n k : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hn : 0<n) (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (D : Set (nativeManifold hk W hW))
    (hNC : HasNormalCrossings n ((Subtype.val : W→X) '' D) E) :
    HasNormalCrossings k D (E.map ((Subtype.val : W→X) ⁻¹' ·)) := by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le hk
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  exact native_crossings_core hW hn hE hTrans D hNC

/-- Native TESThood is DERIVED from the ambient TEST on the SAME actual
geometry-only Lift for every supported raw holomorphic marked record.
Neither native TEST/WF/CAN nor a record comparison is supplied. -/
theorem Lift.native_test {n k : ℕ} {X : CMfd.{0} n} {hk : k≤n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    {E : List (Set X)} {Y : CMfd.{0} n} {T : BlowupTower X Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x a,M.ideal.mem x a → HolomorphicAt n a x) :
    IsGeoTestTower M T → IsGeoTestTower (nativePullback hk W hW M) Q := by
  induction h with
  | refl => intro _hT;trivial
  | @step Y Z T V hVc hV Q h D hD _hint π hπ hNC ih =>
    intro hT
    refine ⟨ih hT.1,hD,?_,?_⟩
    · have hCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport h
        hn hE hTrans M hME hMN hhol
      intro z hz
      rw [hCos]
      exact hT.2.2.1 ⟨z,hz,rfl⟩
    · obtain ⟨hEC,hTC⟩:=h.geometry hn hE hTrans
      have hNativeNC:=hasNormalCrossings_native_preimage hn hk hV hEC hTC D hNC
      have hRec:=h.whole_records hn hE hTrans M hME hMN hhol
      have hCurrentE : (geoTransformAlong M T).E=boundary E T:=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
          (𝔪:=M) (𝔫:=(⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) hME T
      have he:=congrArg (fun A : MarkedIdeal k (nativeManifold hk V hV)=>A.E) hRec
      change (geoTransformAlong (nativePullback hk W hW M) Q).E=
        (geoTransformAlong M T).E.map ((Subtype.val : V→Y) ⁻¹' ·) at he
      rw [hCurrentE] at he
      rw [he]
      exact hNativeNC

/-- The ORIGINAL full native upper TEST is produced from the ambient original
bar TEST on the SAME actual split histories, including every pre-cut born slot. -/
theorem actual_split_native_original_test {n k : ℕ} {X : CMfd.{0} n} {hk : k≤n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    {E : List (Set X)} {Y Z : CMfd.{0} n} {T : BlowupTower X Y} {S : BlowupTower Y Z}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {V' : Set Z} {hV'c : IsClosed V'} {hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')}
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hTail : Lift hk V hVc hV (boundary E T) S V' hV'c hV' R)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hd : 1≤M.d) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hUpper : IsGeoTestTower (barMarked M) (T.append S)) :
    IsGeoTestTower (nativePullback hk W hW M) (Q.append R) := by
  let K:=nativePullback hk W hW M
  have hhol : ∀x a,M.ideal.mem x a → HolomorphicAt n a x:=
    fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI ha
  have hBar:=nativePullback_barMarked hk hW M hMN hhol
  obtain ⟨hT,hS⟩:=(isGeoTestTower_append_iff (barMarked M) T S).mp hUpper
  have hHead:=Lift.native_test h hn hE hTrans (barMarked M) hME hMN (fun _ _ ha=>ha.1) hT
  rw [hBar] at hHead
  obtain ⟨hEC,hTC⟩:=h.geometry hn hE hTrans
  have hEN : (geoTransformAlong (barMarked M) T).E=boundary E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=(⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) hME T
  have hCurrentHol:=holomorphic_geoTransformAlong (barMarked M) (fun _ _ ha=>ha.1) T
  have hTailTest:=Lift.native_test hTail hn hEC hTC (geoTransformAlong (barMarked M) T) hEN
    (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h (barMarked M) hMN) hCurrentHol hS
  have hRec:=h.whole_records hn hE hTrans (barMarked M) hME hMN (fun _ _ ha=>ha.1)
  rw [hBar] at hRec
  have hTailK : IsGeoTestTower (geoTransformAlong (barMarked K) Q) R:=by rw [hRec];exact hTailTest
  have hNativeBar : IsGeoTestTower (barMarked K) (Q.append R):=
    (isGeoTestTower_append_iff (barMarked K) Q R).mpr ⟨hHead,hTailK⟩
  obtain ⟨hKN,hKI,_hKmax,_hKcos⟩:=native_source_geometry hk hW M hMN hN hI hmax
  exact ((coeff_homAlong_wEquiv K hKN hKI hd).2 (Q.append R)).1.mp hNativeBar

end
end Hironaka.HironakaActualNativeSectionNormalCrossings
