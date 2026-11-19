import Hironaka.Resolution.HironakaActualNativeHistoryExistence
import Hironaka.Resolution.HironakaActualCleanupDensityCompactness
import Hironaka.Resolution.HironakaNormalCrossingsTransversality

/-! Native invariant-domain data are produced from the ORIGINAL supported
ambient record. The whole ordered boundary remains SNC and native carrier
transversality is derived from ORIGINAL density, with native dimension zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeInvariantDomain
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  BlowupFlatCoordinates BlowupSNCTransform SubmanifoldChartedSpace GiraudAlong
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionNormalCrossings HironakaActualNativeHistoryExistence
  HironakaDisjointMatchedControlledTrace HironakaDisjointEmbeddedBoundaryLift
  HironakaActualSingularChartTransport HironakaRelativeNormalIdeal
  HironakaActualCleanupDensityCompactness HironakaNormalCrossingsTransversality
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec BlowupTowers
  GermIdealOrder GermIdealPullbackCalculus RelativePrincipalizationSpan

private theorem native_snc_core {d t : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    {W : Set X} (hW : ∀x∈W,RegularAtDim (n:=d+t) W x d)
    (hn : 0<d+t) {E : List (Set X)} (hE : IsSNCDivisor (d+t) E)
    (hTrans : IsTransverse (d+t) W E) :
    letI:=chartedSpace (Nat.le_add_right d t) hW
    letI:=isComplexManifold_chartedSpace (Nat.le_add_right d t) hW
    IsSNCDivisor d (E.map ((Subtype.val : W→X) ⁻¹' ·)) := by
  classical
  let := chartedSpace (Nat.le_add_right d t) hW
  have := isComplexManifold_chartedSpace (Nat.le_add_right d t) hW
  refine ⟨?_,?_⟩
  · intro H hH
    obtain ⟨H0,hH0,rfl⟩:=List.mem_map.mp hH
    exact (hE.1 H0 hH0).preimage continuous_subtype_val
  · intro p
    obtain ⟨_a,_ha,Θ,s,hΘsrc,hΘ0,hs,hinj,hflat⟩:=
      exists_centered_native_joint_coordinates hn (hW p.val p.property)
        (Subset.refl W) hE hTrans hTrans.hasNormalCrossings p.property
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
      simpa only [show flatMap Γ p=0 from hΓ0] using hc.tendsto
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
    let S : Fin E.length→Finset (Fin d):=fun i=>
      if hi : p.val∈E.get i then {⟨(s i).val,hs i hi⟩} else ∅
    have hFamily : IsCoordinateFamilyAt d (fun i : Fin E.length=>(Subtype.val : W→X) ⁻¹' E.get i) S p:=by
      apply coordinate_family_of_eventual_native _ S p Γ hΓsrc hΓ0
      intro i hi
      have hpEi : p.val∈E.get i:=hi
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
    refine ⟨fun i=>S (c i),?_,?_,?_⟩
    · exact NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hFamily c
        (fun i=>get_map_preimage E i) (fun _=>rfl)
    · intro i hi
      have hpEi : p.val∈E.get (c i):=by
        rw [get_map_preimage E i] at hi
        exact hi
      change (S (c i)).card=1
      rw [show S (c i)={⟨(s (c i)).val,hs (c i) hpEi⟩} from dif_pos hpEi,Finset.card_singleton]
    · intro i hi j hj he
      change p∈(E.map ((Subtype.val : W→X) ⁻¹' ·)).get i at hi
      change p∈(E.map ((Subtype.val : W→X) ⁻¹' ·)).get j at hj
      have hpEi : p.val∈E.get (c i):=by
        rw [get_map_preimage E i] at hi
        exact hi
      have hpEj : p.val∈E.get (c j):=by
        rw [get_map_preimage E j] at hj
        exact hj
      change S (c i)=S (c j) at he
      rw [show S (c i)={⟨(s (c i)).val,hs (c i) hpEi⟩} from dif_pos hpEi,
        show S (c j)={⟨(s (c j)).val,hs (c j) hpEj⟩} from dif_pos hpEj] at he
      have hFin : (⟨(s (c i)).val,hs (c i) hpEi⟩ : Fin d)=⟨(s (c j)).val,hs (c j) hpEj⟩:=
        Finset.singleton_injective he
      have hsEq : s (c i)=s (c j):=Fin.ext (congrArg (fun q : Fin d=>q.val) hFin)
      exact Fin.cast_injective _ (hinj hpEi hpEj hsEq)

/-- The ENTIRE original SNC boundary restricts to the ACTUAL native atlas,
retaining the distinct incident chronological positions, including k=0. -/
theorem isSNCDivisor_native_preimage {n k : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hn : 0<n) (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E) :
    letI:=chartedSpace hk hW
    letI:=isComplexManifold_chartedSpace hk hW
    IsSNCDivisor k (E.map ((Subtype.val : W→X) ⁻¹' ·)) := by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le hk
  exact native_snc_core hW hn hE hTrans

/-- Native carrier transversality is PRODUCED from ORIGINAL transversality
and actual support, using its derived density off the WHOLE original boundary. -/
theorem isTransverse_native_preimage {n k : ℕ} {X : CMfd.{0} n} {W N : Set X}
    (hn : 0<n) (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (hN : IsClosedSubmanifold n N) (hNW : N⊆W)
    {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hWTrans : IsTransverse n W E) (hNTrans : IsTransverse n N E) :
    letI:=chartedSpace hk hW
    letI:=isComplexManifold_chartedSpace hk hW
    IsTransverse k ((Subtype.val : W→X) ⁻¹' N) (E.map ((Subtype.val : W→X) ⁻¹' ·)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let D : Set W:=(Subtype.val : W→X) ⁻¹' N
  have hImage : (Subtype.val : W→X) '' D=N:=by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hx;exact ⟨⟨x,hNW hx⟩,hx,rfl⟩
  have hOld : N⊆closure (N \ ⋃H∈([] : List (Set X)),H):=by
    simpa using (subset_closure : N⊆closure N)
  have hDense : N⊆closure (N \ ⋃H∈E,H):=by
    simpa only [List.nil_append] using
      actual_cleanup_source_full_density hn hN (O:=[]) (B:=E) hE hNTrans hOld
  have hAwayImage : (Subtype.val : W→X) ''
      (D \ ⋃H∈E.map ((Subtype.val : W→X) ⁻¹' ·),H)=N \ ⋃H∈E,H:=by
    ext x
    constructor
    · rintro ⟨q,⟨hqN,hqE⟩,rfl⟩
      refine ⟨hqN,?_⟩
      intro hxBoundary
      obtain ⟨H,hH,hxH⟩:=mem_iUnion₂.mp hxBoundary
      exact hqE (mem_iUnion₂.mpr ⟨(Subtype.val : W→X) ⁻¹' H,List.mem_map.mpr ⟨H,hH,rfl⟩,hxH⟩)
    · rintro ⟨hxN,hxE⟩
      refine ⟨⟨x,hNW hxN⟩,⟨hxN,?_⟩,rfl⟩
      intro hqBoundary
      obtain ⟨H,hH,hqH⟩:=mem_iUnion₂.mp hqBoundary
      obtain ⟨H0,hH0,rfl⟩:=List.mem_map.mp hH
      exact hxE (mem_iUnion₂.mpr ⟨H0,hH0,hqH⟩)
  have hNativeDense : D⊆closure (D \ ⋃H∈E.map ((Subtype.val : W→X) ⁻¹' ·),H):=by
    intro q hq
    apply closure_subtype.mpr
    rw [hAwayImage]
    exact hDense hq
  have hNativeNC : HasNormalCrossings k D (E.map ((Subtype.val : W→X) ⁻¹' ·)):=by
    apply hasNormalCrossings_native_preimage hn hk hW hE hWTrans D
    rw [hImage]
    exact hNTrans.hasNormalCrossings
  exact isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNativeNC hNativeDense

/-- The ORIGINAL invariant domain internally constructs the native domain on
its literal supported carrier. No native WF/domain/density/TEST is a premise. -/
theorem isInvDomain_nativePullback {n k r : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hn : 0<n) (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W)
    (hWTrans : IsTransverse n W M.E) :
    IsInvDomain r (nativePullback hk W hW M) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K:=nativePullback hk W hW M
  have hImage : (Subtype.val : W→X) '' K.N=M.N:=by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hx;exact ⟨⟨x,hMN hx⟩,hx,rfl⟩
  have hReg (q : nativeManifold hk W hW) (j : ℕ) :
      RegularAtDim (n:=n) M.N q.val j ↔ RegularAtDim (n:=k) K.N q j:=by
    have h:=regularAtDim_native_image_iff hk hW K.N q j
    rw [hImage] at h
    exact h
  have hKN : IsClosedSubmanifold k K.N:=by
    refine ⟨hM.isWellFormed.isClosedSubmanifold_N.1.preimage continuous_subtype_val,?_⟩
    intro q hq
    obtain ⟨j,hj⟩:=hM.isWellFormed.isClosedSubmanifold_N.2 q.val hq
    exact ⟨j,(hReg q j).mp hj⟩
  have hKI : K.ideal.IsCoherent:=isCoherent_pullback (contMDiff_val hk hW) hM.isWellFormed.isCoherent
  have hKE : IsSNCDivisor k K.E:=isSNCDivisor_native_preimage hn hk hW
    hM.isWellFormed.isSNCDivisor hWTrans
  have hKT : IsTransverse k K.N K.E:=isTransverse_native_preimage hn hk hW
    hM.isWellFormed.isClosedSubmanifold_N hMN hM.isWellFormed.isSNCDivisor hWTrans hM.isWellFormed.isTransverse
  refine ⟨⟨hKN,hKI,hKE,hKT⟩,?_,hM.one_le_d,?_⟩
  · intro q hq
    obtain ⟨j,hjr,hj⟩:=hM.dimLE q.val hq
    exact ⟨j,hjr,(hReg q j).mp hj⟩
  · exact nonzero_native_pullback hk hW M hMN
      (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)
      hM.isNonzeroAlongAt

end
end Hironaka.HironakaActualNativeInvariantDomain
