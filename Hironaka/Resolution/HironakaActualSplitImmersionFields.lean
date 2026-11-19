import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale

/-! Actual mixed-dimension chain rule and split-immersion field transfer.
Only holomorphic point maps and the actual native left round trip are
input; no desired derivative/coefficient/invariant comparison is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSplitImmersionFields
noncomputable section
open Hironaka.HolomorphicIdealSheaves DerivativeIdeal DerivativeIdealAlong
  HadamardBridge
variable {n m : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel m) M'] [IsComplexManifold m M']

def chainCoeff (e : ComplexChart n M) (e' : ComplexChart m M')
    (φ : M'→M) (v : ComplexModel m) (j : Fin n) : M'→ℂ:=
  fun y=>fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) (e'.val y) v j

private theorem eventually_differentiableAt_chartMap
    (e : ComplexChart n M) (e' : ComplexChart m M') {φ : M'→M} {y : M'}
    (hφ : ∀ᶠp in 𝓝 y,MDifferentiableAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) φ p)
    (hy' : y∈e'.val.source) (hy : φ y∈e.val.source) :
    ∀ᶠz in 𝓝 (e'.val y),DifferentiableAt ℂ (e.val ∘ φ ∘ e'.val.symm) z := by
  have hT : Tendsto e'.val.symm (𝓝 (e'.val y)) (𝓝 y):=by
    have :=e'.val.continuousAt_symm (e'.val.map_source hy')
    rwa [ContinuousAt,e'.val.left_inv hy'] at this
  have hφT : Tendsto (φ ∘ e'.val.symm) (𝓝 (e'.val y)) (𝓝 (φ y)):=
    hφ.self_of_nhds.continuousAt.tendsto.comp hT
  filter_upwards [e'.val.open_target.mem_nhds (e'.val.map_source hy'),
    hφT.eventually (e.val.open_source.mem_nhds hy),hT.eventually hφ] with z hz hze hzφ
  rw [←mdifferentiableAt_iff_differentiableAt]
  exact (mdifferentiableAt_atlas (I:=𝓘(ℂ,ComplexModel n)) e.property hze).comp z
    (hzφ.comp z (mdifferentiableAt_atlas_symm (I:=𝓘(ℂ,ComplexModel m)) e'.property hz))

theorem holomorphicAt_chainCoeff
    (e : ComplexChart n M) (e' : ComplexChart m M') {φ : M'→M} {y : M'}
    (hφ : ∀ᶠp in 𝓝 y,MDifferentiableAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) φ p)
    (hy' : y∈e'.val.source) (hy : φ y∈e.val.source) (v : ComplexModel m) (j : Fin n) :
    HolomorphicAt m (chainCoeff e e' φ v j) y := by
  obtain ⟨U,hU,hUo,hyU⟩:=eventually_nhds_iff.mp
    (eventually_differentiableAt_chartMap e e' hφ hy' hy)
  have hd : DifferentiableOn ℂ (e.val ∘ φ ∘ e'.val.symm) U:=
    fun z hz=>(hU z hz).differentiableWithinAt
  have hd':=Hironaka.differentiableOn_fderiv_apply_of_isOpen hd hUo v
  refine holomorphicAt_comp_chart e'
    (W:=fun z=>fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) z v j) hy' ?_
  filter_upwards [hUo.mem_nhds hyU] with z hz
  have hlin : DifferentiableAt ℂ (fun w : ComplexModel n=>w j)
      (fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) z v):=
    (EuclideanSpace.proj (𝕜:=ℂ) j).differentiableAt
  exact hlin.comp z ((hd' z hz).differentiableAt (hUo.mem_nhds hz))

theorem chartDeriv_comp_eventuallyEq_sum
    (e : ComplexChart n M) (e' : ComplexChart m M') {φ : M'→M} {y : M'}
    (hφ : ∀ᶠp in 𝓝 y,MDifferentiableAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) φ p)
    (hy' : y∈e'.val.source) (hy : φ y∈e.val.source) {f : M→ℂ}
    (hf : HolomorphicAt n f (φ y)) (v : ComplexModel m) :
    chartDeriv e' v (f ∘ φ)=ᶠ[𝓝 y] fun p=>
      ∑j,chainCoeff e e' φ v j p * chartDeriv e (EuclideanSpace.single j 1) f (φ p) := by
  have hφc : ContinuousAt φ y:=hφ.self_of_nhds.continuousAt
  filter_upwards [hφc.eventually hf.eventually_nhds,e'.val.open_source.mem_nhds hy',
    hφc.eventually (e.val.open_source.mem_nhds hy),hφ.eventually_nhds] with p hfp hpe' hpe hpφ
  have hT:=(eventually_differentiableAt_chartMap (y:=p) e e' hpφ hpe' hpe).self_of_nhds
  have hF : DifferentiableAt ℂ (f ∘ e.val.symm) ((e.val ∘ φ ∘ e'.val.symm) (e'.val p)):=by
    simp only [Function.comp_apply,e'.val.left_inv hpe']
    exact (eventually_differentiableAt_comp_symm e hpe hfp).self_of_nhds
  have hloc : (f ∘ φ) ∘ e'.val.symm=ᶠ[𝓝 (e'.val p)]
      (f ∘ e.val.symm) ∘ (e.val ∘ φ ∘ e'.val.symm):=by
    have hTc : Tendsto e'.val.symm (𝓝 (e'.val p)) (𝓝 p):=by
      have :=e'.val.continuousAt_symm (e'.val.map_source hpe')
      rwa [ContinuousAt,e'.val.left_inv hpe'] at this
    have hφp : Tendsto (φ ∘ e'.val.symm) (𝓝 (e'.val p)) (𝓝 (φ p)):=
      hpφ.self_of_nhds.continuousAt.tendsto.comp hTc
    filter_upwards [hφp.eventually (e.val.open_source.mem_nhds hpe)] with z hz
    simp only [Function.comp_apply] at hz ⊢
    rw [e.val.left_inv hz]
  simp only [chartDeriv]
  rw [hloc.fderiv_eq,fderiv_comp _ hF hT,ContinuousLinearMap.comp_apply]
  simp only [Function.comp_apply,e'.val.left_inv hpe']
  conv_lhs => rw [←sum_smul_single (fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) (e'.val p) v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _=>?_
  rw [map_smul,smul_eq_mul]
  simp only [chainCoeff]

structure SplitAt (φ : M'→M) (ψ : M→M') (y : M') : Prop where
  mdiff : ∀ᶠp in 𝓝 y,MDifferentiableAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) φ p
  mdiff_inv : ∀ᶠq in 𝓝 (φ y),MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ψ q
  left_inv : ∀ᶠp in 𝓝 y,ψ (φ p)=p

def transferField (φ : M'→M) (ψ : M→M')
    (e : ComplexChart n M) (e' : ComplexChart m M') (ξ : Fin n→M→ℂ) : Fin m→M'→ℂ:=
  fun j p=>∑i,ξ i (φ p)*chainCoeff e' e ψ (EuclideanSpace.single i 1) j (φ p)

theorem fieldDeriv_transfer {φ : M'→M} {ψ : M→M'} {y : M'} (h : SplitAt (n:=n) (m:=m) φ ψ y)
    {e : ComplexChart n M} {e' : ComplexChart m M'}
    (hy' : y∈e'.val.source) (hy : φ y∈e.val.source)
    (ξ : Fin n→M→ℂ) {g : M'→ℂ} (hg : HolomorphicAt m g y) :
    fieldDeriv e' (transferField φ ψ e e' ξ) g=ᶠ[𝓝 y]
      fun p=>fieldDeriv e ξ (g ∘ ψ) (φ p) := by
  have hψy : ψ (φ y)=y:=h.left_inv.self_of_nhds
  have hg' : HolomorphicAt m g (ψ (φ y)):=by rw [hψy];exact hg
  have hy'' : ψ (φ y)∈e'.val.source:=by rw [hψy];exact hy'
  have hchain : ∀i,chartDeriv e (EuclideanSpace.single i 1) (g ∘ ψ)=ᶠ[𝓝 (φ y)]
      fun q=>∑j,chainCoeff e' e ψ (EuclideanSpace.single i 1) j q *
        chartDeriv e' (EuclideanSpace.single j 1) g (ψ q):=
    fun i=>chartDeriv_comp_eventuallyEq_sum e' e h.mdiff_inv hy hy'' hg' _
  have hφc : ContinuousAt φ y:=h.mdiff.self_of_nhds.continuousAt
  filter_upwards [hφc.eventually (eventually_all.2 hchain),h.left_inv] with p hp hpψ
  simp only [fieldDeriv,transferField,hp,hpψ,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>by ring

theorem holomorphicAt_transferField {φ : M'→M} {ψ : M→M'} {y : M'} (h : SplitAt (n:=n) (m:=m) φ ψ y)
    {e : ComplexChart n M} {e' : ComplexChart m M'}
    (hy' : y∈e'.val.source) (hy : φ y∈e.val.source)
    {ξ : Fin n→M→ℂ} (hξ : ∀i,HolomorphicAt n (ξ i) (φ y)) (j : Fin m) :
    HolomorphicAt m (transferField φ ψ e e' ξ j) y := by
  have hψy : ψ (φ y)=y:=h.left_inv.self_of_nhds
  refine HolomorphicAt.sum _ fun i _=>?_
  refine (holomorphicAt_comp_map (f:=ξ i) h.mdiff (hξ i)).mul
    (holomorphicAt_comp_map (f:=chainCoeff e' e ψ (EuclideanSpace.single i 1) j) h.mdiff ?_)
  exact holomorphicAt_chainCoeff e' e h.mdiff_inv hy (by rw [hψy];exact hy') _ j

end
end Hironaka.HironakaActualSplitImmersionFields
