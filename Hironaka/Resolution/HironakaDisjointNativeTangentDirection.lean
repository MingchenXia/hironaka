import Hironaka.Resolution.HironakaActualNativeSectionDifferentialIdeals
import Hironaka.MarkedIdeal.TangentDirectionAlong

/-! Genuine tangent directions and contact neighbourhoods on an actual
native regular section, retaining the original function and carrier. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointNativeTangentDirection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongCoherent
  GermIdealOrder IdealWeightPowers GiraudAlong OrderTaylor BlowupFlatCoordinates HolomorphicTaylorTail
  HadamardBridgeAlong
  TangentDirectionAlong RelativePrincipalizationSpan InvertibleIdealQuotient
  GermIdealPullbackCalculus SubmanifoldChartedSpace
  HironakaActualNativeSectionOrder HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionDifferentialIdeals
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Scalar second-order vanishing annihilates every actual tangent derivation. -/
theorem tangent_derivative_eq_zero_of_order_two {N : Set X} {x : X} {u : X → ℂ}
    (hx : x∈N) (hu : HolomorphicAt n u x) (horder : VanishesToOrderOn n N x 2 u)
    {e : ComplexChart n X} {ξ : Fin n → X → ℂ} (hξ : IsTangentField N e ξ x) :
    fieldDeriv e ξ u x=0 := by
  obtain ⟨f,hf,huf⟩ := horder
  have hfh : HolomorphicAt n f x := holomorphicAt_of_mem_idealPow hf
  have hdiff : (vanishingIdeal (n := n) N).mem x (fun y => u y-f y) :=
    ⟨GiraudAlong.holomorphicAt_sub hu hfh,huf.mono fun y hy hyN => by
      change u y-f y=0
      rw [hy hyN,sub_self]⟩
  have hdiff0 := (hξ.preserves _ hdiff).2.self_of_nhds hx
  have hpoint : (idealPow (pointIdeal n x) 1).mem x (fieldDeriv e ξ f) :=
    mem_idealPow_sum Finset.univ fun i _ => mul_mem_idealPow (hξ.holomorphicAt i)
      (chartDeriv_mem_idealPow (v := EuclideanSpace.single i 1) hξ.mem_source 1 f hf)
  have hpoint0 : fieldDeriv e ξ f x=0 := apply_eq_zero_of_mem_idealPow_pointIdeal (by decide) hpoint
  have hadd := GiraudAlong.fieldDeriv_add_eventuallyEq (ξ := ξ) hξ.mem_source hdiff.1 hfh
  have heq : (fun y => (u y-f y)+f y)=u := funext fun y => sub_add_cancel _ _
  rw [heq] at hadd
  rw [hadd.self_of_nhds,hdiff0,hpoint0,zero_add]

/-- At a regular carrier, zero value and vanishing of every tangent derivative
produce actual scalar order at least two. -/
theorem order_two_of_tangent_derivatives_zero {N : Set X} {x : X} {u : X → ℂ}
    {r : ℕ} (hN : RegularAtDim (n := n) N x r) (hu : HolomorphicAt n u x)
    (hu0 : u x=0)
    (hkill : ∀(e : ComplexChart n X)(ξ : Fin n → X → ℂ),
      IsTangentField N e ξ x → fieldDeriv e ξ u x=0) :
    VanishesToOrderOn n N x 2 u := by
  obtain ⟨_hr,_hx,Φ,hsrc,hΦ0,hflat⟩ := hN
  apply vanishesToOrderOn_of_iterDeriv_flatten_eq_zero hsrc hΦ0 hflat hu 2
  intro L hL
  rcases List.eq_nil_or_concat L with rfl | ⟨L',v,rfl⟩
  · change flatten Φ r u 0=0
    simp only [flatten,map_zero,flatInv_zero hΦ0,hu0]
  · have hlen : L'.length=0 := by simp only [List.length_concat] at hL;omega
    have hnil : L'=[] := List.length_eq_zero_iff.mp hlen
    subst L'
    change dirDeriv v (flatten Φ r u) 0=0
    rw [(dirDeriv_flatten_eventuallyEq hsrc hΦ0 (k := r) hu v).self_of_nhds]
    change fieldDeriv (complexChartAt (n := n) x) (flatField Φ (planeRetract r v)) u
      (flatInv Φ (planeRetract r 0))=0
    rw [map_zero,flatInv_zero hΦ0]
    exact hkill _ _ (isTangentField_flatField hsrc hflat (planeRetract_mem r v) (mem_flatDomain_self Φ))

/-- The original nonzero ambient tangent derivative produces an actual native
tangent derivative of the same function, using exact scalar order transport. -/
theorem exists_native_tangent_derivative {m : ℕ} {W : Set X} (hk : m≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x m) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(N : Set X)(_hNW : N⊆W)(p : W)(r : ℕ)
      (_hN : RegularAtDim (n := n) N p.val r)(u : X → ℂ)
      (_hu : HolomorphicAt n u p.val)(_hu0 : u p.val=0)
      (e : ComplexChart n X)(ξ : Fin n → X → ℂ)
      (_hξ : IsTangentField N e ξ p.val)(_hne : fieldDeriv e ξ u p.val≠0),
      ∃(a : ComplexChart m W)(η : Fin m → W → ℂ),
        IsTangentField ((Subtype.val : W → X) ⁻¹' N) a η p ∧
          fieldDeriv a η (u∘Subtype.val) p≠0 := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro N hNW p r hN u hu hu0 e ξ hξ hne
  let A : Set W := (Subtype.val : W → X) ⁻¹' N
  have hImage : (Subtype.val : W → X) '' A=N := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hx;exact ⟨⟨x,hNW hx⟩,hx,rfl⟩
  have hNative : RegularAtDim (n := m) A p r := by
    apply (regularAtDim_native_image_iff hk hW A p r).mp
    rwa [hImage]
  have hU : HolomorphicAt m (u∘(Subtype.val : W → X)) p :=
    hu.comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_val hk hW).contMDiffAt)
  by_contra hall
  push Not at hall
  have horder := order_two_of_tangent_derivatives_zero hNative hU hu0 hall
  have horder' := (vanishesToOrderOn_native_iff hk hW A p 2 u).mpr horder
  rw [hImage] at horder'
  exact hne (tangent_derivative_eq_zero_of_order_two hN.2.1 hu horder' hξ)

private theorem native_closed_carrier {m : ℕ} {W : Set X} (hk : m≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x m) (N : Set X) (hNW : N⊆W)
    (hN : IsClosedSubmanifold n N) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    IsClosedSubmanifold m ((Subtype.val : W → X) ⁻¹' N) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let A : Set W := (Subtype.val : W → X) ⁻¹' N
  have hImage : (Subtype.val : W → X) '' A=N := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩;exact hq
    · intro hx;exact ⟨⟨x,hNW hx⟩,hx,rfl⟩
  refine ⟨hN.1.preimage continuous_subtype_val,?_⟩
  intro p hp
  obtain ⟨r,hr⟩ := hN.2 p.val hp
  refine ⟨r,(regularAtDim_native_image_iff hk hW A p r).mp ?_⟩
  rwa [hImage]

/-- The same original tangent function is a true native tangent direction on
one internally chosen actual open neighbourhood of the original point. -/
theorem exists_native_tangent_neighbourhood {m : ℕ} {W : Set X} (hk : m≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x m) (N : Set X) (hNW : N⊆W)
    (hN : IsClosedSubmanifold n N) (J : GermIdeal n X)
    (hJ : ∀x f,J.mem x f → HolomorphicAt n f x)
    {μ : ℕ} {O : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N J μ O u) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(p : W)(_hpN : p.val∈N)(_hpO : p.val∈O)(_hu0 : u p.val=0),
      ∃ V : Opens W,p∈V ∧ (V : Set W)⊆(Subtype.val : W → X) ⁻¹' O ∧
        IsTangentDirectionAlong ((Subtype.val : W → X) ⁻¹' N)
          (GermIdeal.pullback (m := m) (Subtype.val : W → X) J) μ V (u∘Subtype.val) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro p hpN hpO hu0
  let A : Set W := (Subtype.val : W → X) ⁻¹' N
  have hA : IsClosedSubmanifold m A := native_closed_carrier hk hW N hNW hN
  have huh (x : X) (hx : x∈O) : HolomorphicAt n u x :=
    holomorphicAt_of_mem_iterDerivIdealAlong hJ (μ-1) x u (hu.mem x hx)
  have hU : HolomorphicAt m (u∘(Subtype.val : W → X)) p :=
    (huh p.val hpO).comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_val hk hW).contMDiffAt)
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one p.val hpO hu0
  obtain ⟨r,hr⟩ := hN.2 p.val hpN
  obtain ⟨a,η,hη,hηne⟩ := exists_native_tangent_derivative hk hW N hNW p r hr u (huh _ hpO) hu0 e ξ hξ hne
  obtain ⟨k,hkm,_hp,Φ,hsrc,_hΦ0,hflat⟩ := hA.2 p hpN
  obtain ⟨j,hjk,hj⟩ := exists_flatPartial_ne_zero hsrc hflat (mem_flatDomain_self Φ) hpN hU hη hηne
  have hcont := (holomorphicAt_flatPartial j (mem_flatDomain_self Φ) hU).self_of_nhds.continuousAt
  obtain ⟨Z,hZsub,hZo,hpZ⟩ := mem_nhds_iff.mp (hcont.eventually (isOpen_ne.mem_nhds hj))
  let V : Opens W := ⟨(Z∩(Subtype.val : W → X) ⁻¹' O)∩flatDomain Φ,
    (hZo.inter (hu.isOpen.preimage continuous_subtype_val)).inter (isOpen_flatDomain Φ)⟩
  refine ⟨V,⟨⟨hpZ,hpO⟩,mem_flatDomain_self Φ⟩,fun _ hy => hy.1.2,⟨V.isOpen,?_,?_⟩⟩
  · intro q hq
    rw [←pullback_native_iterDerivIdealAlong hk hW N hNW J hJ (μ-1)]
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨u,hu.mem q.val hq.1.2,rfl⟩
      ((huh _ hq.1.2).comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_val hk hW).contMDiffAt))
  · intro q hq _hq0
    exact ⟨complexChartAt p,flatField Φ (EuclideanSpace.single j 1),
      isTangentField_flatField hsrc hflat (single_mem_complexCoordinatePlane hjk) hq.2,hZsub hq.1.1⟩

/-- The native contact is an actual closed regular submanifold on the same
chosen open, and its literal image is the original ambient contact there. -/
theorem exists_native_regular_contact {m : ℕ} {W : Set X} (hk : m≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x m) (N : Set X) (hNW : N⊆W)
    (hN : IsClosedSubmanifold n N) (J : GermIdeal n X)
    (hJ : ∀x f,J.mem x f → HolomorphicAt n f x)
    {μ : ℕ} {O : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N J μ O u) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(p : W)(_hpN : p.val∈N)(_hpO : p.val∈O)(_hu0 : u p.val=0),
      ∃ V : Opens W,p∈V ∧ (V : Set W)⊆(Subtype.val : W → X) ⁻¹' O ∧
        IsTangentDirectionAlong ((Subtype.val : W → X) ⁻¹' N)
          (GermIdeal.pullback (m := m) (Subtype.val : W → X) J) μ V (u∘Subtype.val) ∧
        IsClosedSubmanifold m ((Subtype.val : V → W) ⁻¹'
          (((Subtype.val : W → X) ⁻¹' N)∩{q | u q.val=0}∩(V : Set W))) ∧
        (Subtype.val : W → X) '' (((Subtype.val : W → X) ⁻¹' N)∩{q | u q.val=0}∩(V : Set W))=
          N∩{x | u x=0}∩(Subtype.val : W → X) '' (V : Set W) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro p hpN hpO hu0
  obtain ⟨V,hpV,hVO,hv⟩ := exists_native_tangent_neighbourhood hk hW N hNW hN J hJ hu p hpN hpO hu0
  have hA := native_closed_carrier hk hW N hNW hN
  have hJP : ∀q f,(GermIdeal.pullback (m := m) (Subtype.val : W → X) J).mem q f →
      HolomorphicAt m f q := fun _ _ hf => (GermIdeal.mem_pullback_iff.mp hf).holomorphicAt
  have huh : ∀q∈(V : Set W),HolomorphicAt m (u∘(Subtype.val : W → X)) q :=
    fun q hq => holomorphicAt_of_mem_iterDerivIdealAlong hJP (μ-1) q _ (hv.mem q hq)
  refine ⟨V,hpV,hVO,hv,⟨isClosed_preimage_val_inter_zeroSet hA.1 huh,?_⟩,?_⟩
  · intro q hq
    obtain ⟨k,_hk,hcontact⟩ := hv.regularAtDim_contact hJP hA hq
    exact ⟨k-1,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hcontact⟩
  · ext x
    constructor
    · rintro ⟨q,⟨⟨hqN,hqu⟩,hqV⟩,rfl⟩
      exact ⟨⟨hqN,hqu⟩,⟨q,hqV,rfl⟩⟩
    · rintro ⟨⟨hxN,hxu⟩,⟨q,hqV,rfl⟩⟩
      exact ⟨q,⟨⟨hxN,hxu⟩,hqV⟩,rfl⟩

end
end Hironaka.HironakaDisjointNativeTangentDirection
