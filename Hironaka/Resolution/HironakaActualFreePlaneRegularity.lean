import Hironaka.Resolution.HironakaActualZeroSectionCentreGeometry
import Hironaka.Manifold.LocalHolomorphicInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Genuine zero-section regularity reflection. The free immersion, its
linear completion, and the inverse used for flattening are constructed
internally from the actual ambient regular chart. No supplied free chart,
rank, complement, or desired compatibility certificate is used.
Blueprint: hironaka-actual-inherited-free-product-flattening-extension.tex.
Source draft only: no elaboration or kernel acceptance is claimed. -/
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Manifold

namespace Hironaka.HironakaActualFreePlaneRegularity
noncomputable section
open HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance

private def prefixProjection (k n : ℕ) (h : k ≤ n) :
    ComplexModel n →L[ℂ] ComplexModel k :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin k => EuclideanSpace.proj (Fin.castLE h i))

private def prefixInclusion (k n : ℕ) (h : k ≤ n) :
    ComplexModel k →L[ℂ] ComplexModel n :=
  ∑ i : Fin k, (EuclideanSpace.proj i).smulRight
    (EuclideanSpace.single (Fin.castLE h i) (1 : ℂ))

private theorem prefixProjection_apply (k n : ℕ) (h : k ≤ n)
    (z : ComplexModel n) (i : Fin k) :
    prefixProjection k n h z i = z (Fin.castLE h i) := rfl

private theorem prefixInclusion_apply (k n : ℕ) (h : k ≤ n)
    (z : ComplexModel k) (i : Fin n) :
    prefixInclusion k n h z i = if hi : i.val < k then z ⟨i.val, hi⟩ else 0 := by
  classical
  by_cases hi : i.val < k
  · let j : Fin k := ⟨i.val, hi⟩
    have hij : i = Fin.castLE h j := Fin.ext rfl
    rw [dif_pos hi]
    calc
      prefixInclusion k n h z i = prefixInclusion k n h z (Fin.castLE h j) :=
        congrArg (fun l => prefixInclusion k n h z l) hij
      _ = z j := by
        simp [prefixInclusion, sum_apply, ContinuousLinearMap.smulRight_apply,
          Pi.single_apply, Fin.castLE_inj]
  · have hne : ∀ j : Fin k, i ≠ Fin.castLE h j := by
      intro j he
      exact hi (by simpa only [he, Fin.val_castLE] using j.isLt)
    simp [prefixInclusion, sum_apply, ContinuousLinearMap.smulRight_apply,
      hne, hi]

private theorem prefixProjection_inclusion (k n : ℕ) (h : k ≤ n)
    (z : ComplexModel k) :
    prefixProjection k n h (prefixInclusion k n h z) = z := by
  ext i
  simp [prefixProjection_apply, prefixInclusion_apply, i.isLt]

private theorem prefixInclusion_injective (k n : ℕ) (h : k ≤ n) :
    Function.Injective (prefixInclusion k n h) := by
  intro u v huv
  have := congrArg (prefixProjection k n h) huv
  simpa only [prefixProjection_inclusion] using this

private theorem prefixInclusion_mem_plane (k n : ℕ) (h : k ≤ n)
    (z : ComplexModel k) :
    prefixInclusion k n h z ∈ complexCoordinatePlane n k := by
  intro i hi
  rw [prefixInclusion_apply, dif_neg (by omega)]

private theorem prefixInclusion_projection (k n : ℕ) (h : k ≤ n)
    {z : ComplexModel n} (hz : z ∈ complexCoordinatePlane n k) :
    prefixInclusion k n h (prefixProjection k n h z) = z := by
  ext i
  by_cases hi : i.val < k
  · simp [prefixInclusion_apply, hi, prefixProjection_apply]
  · rw [prefixInclusion_apply, dif_neg hi]
    exact (hz i (by omega)).symm

private theorem model_regular_iff (n k : ℕ) (C : Set (ComplexModel n)) :
    RegularAtDim (n := n) C 0 k ↔
      k ≤ n ∧ (0 : ComplexModel n) ∈ C ∧
        ∃ Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n),
          Φ.toFun 0 = 0 ∧ ∀ {y}, y ∈ Φ.source →
            (y ∈ C ↔ Φ.toFun y ∈ complexCoordinatePlane n k) := by
  simp [RegularAtDim, complexChartAt, chartAt_self_eq]
  intro _ _
  rfl

/-- The finite-dimensional extension theorem constructs an actual square
linear completion of an actual injective rectangular map. -/
theorem exists_linear_completion_of_injective_prefix {k m : ℕ}
    (L : ComplexModel k →ₗ[ℂ] ComplexModel m) (hL : Function.Injective L) :
    ∃ hkm : k ≤ m, ∃ A : ComplexModel m ≃L[ℂ] ComplexModel m,
      ∀ s, A (prefixInclusion k m hkm s) = L s := by
  have hkm : k ≤ m := by
    simpa only [finrank_euclideanSpace_fin] using
      (LinearMap.finrank_le_finrank_of_injective hL)
  let i := (prefixInclusion k m hkm).toLinearMap
  let ei := LinearEquiv.ofInjective i (prefixInclusion_injective k m hkm)
  let eL := LinearEquiv.ofInjective L hL
  let e := ei.symm.trans eL
  obtain ⟨A, hA⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨hkm, A.toContinuousLinearEquiv, ?_⟩
  intro s
  have hh := hA (ei s)
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
  change A (i s) = L s
  change L s = A (i s) at hh
  exact hh.symm

private def inverseAtZero {n : ℕ}
    (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (hΦ0 : Φ.toFun 0 = 0) : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := Φ.target
  target := Φ.source
  isOpen_source := Φ.isOpen_target
  isOpen_target := Φ.isOpen_source
  center_mem_source := by
    simpa only [hΦ0] using Φ.mapsTo_toFun Φ.center_mem_source
  toFun := Φ.invFun
  invFun := Φ.toFun
  toFun_holomorphic := Φ.invFun_holomorphic
  invFun_holomorphic := Φ.toFun_holomorphic
  mapsTo_toFun := Φ.mapsTo_invFun
  mapsTo_invFun := Φ.mapsTo_toFun
  left_inv := Φ.right_inv
  right_inv := Φ.left_inv

private theorem ambient_inverse_derivative {n : ℕ}
    (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0 = 0)
    (v : ComplexModel n) :
    fderiv ℂ Φ.toFun 0 (fderiv ℂ Φ.invFun 0 v) = v := by
  have ht : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [hΦ0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hcomp : Φ.toFun ∘ Φ.invFun =ᶠ[𝓝 (0 : ComplexModel n)] id := by
    filter_upwards [Φ.isOpen_target.mem_nhds ht] with z hz
    exact Φ.right_inv z hz
  have hto := (local_toFun_holomorphic Φ).self_of_nhds
  have hinv := (local_invFun_holomorphic Φ hΦ0).self_of_nhds
  have hd := hcomp.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp 0 (by simpa only [local_invFun_zero Φ hΦ0] using hto) hinv,
    fderiv_id] at hd
  simpa only [local_invFun_zero Φ hΦ0, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun T => T v) hd

private theorem exists_free_chart_of_image_chart {m e k : ℕ}
    (D : Set (ComplexModel m)) (hkn : k ≤ m+e)
    (Φ : LocalHolomorphicEquivAt (n := m+e) (0 : ComplexModel (m+e)))
    (hΦ0 : Φ.toFun 0 = 0)
    (hflat : ∀ {z}, z ∈ Φ.source →
      (z ∈ (tangentInclusion m e) '' D ↔
        Φ.toFun z ∈ complexCoordinatePlane (m+e) k)) :
    ∃ _hkm : k ≤ m, ∃ χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m),
      χ.toFun 0 = 0 ∧ ∀ {u}, u ∈ χ.source →
        (u ∈ D ↔ χ.toFun u ∈ complexCoordinatePlane m k) := by
  let ia := prefixInclusion k (m+e) hkn
  let pa := prefixProjection k (m+e) hkn
  let V : Set (ComplexModel k) := ia ⁻¹' Φ.target
  have hV : IsOpen V := Φ.isOpen_target.preimage ia.continuous
  have h0t : (0 : ComplexModel (m+e)) ∈ Φ.target := by
    simpa only [hΦ0] using Φ.mapsTo_toFun Φ.center_mem_source
  have h0V : (0 : ComplexModel k) ∈ V := by
    simpa only [V, mem_preimage, map_zero] using h0t
  let θ : ComplexModel k → ComplexModel (m+e) := Φ.invFun ∘ ia
  let θf : ComplexModel k → ComplexModel m := tangentProjection m e ∘ θ
  have hθ : DifferentiableOn ℂ θ V :=
    Φ.invFun_holomorphic.comp ia.differentiable.differentiableOn (fun _ hz => hz)
  have hθf : DifferentiableOn ℂ θf V :=
    (tangentProjection m e).differentiable.comp_differentiableOn hθ
  have hθ0 : θ 0 = 0 := by
    simp only [θ, Function.comp_apply, map_zero, local_invFun_zero Φ hΦ0]
  have hθf0 : θf 0 = 0 := by simp only [θf, Function.comp_apply, hθ0, map_zero]
  have hθmem (s : ComplexModel k) (hs : s ∈ V) :
      θ s ∈ (tangentInclusion m e) '' D := by
    apply (hflat (Φ.mapsTo_invFun hs)).mpr
    rw [Φ.right_inv (ia s) hs]
    exact prefixInclusion_mem_plane k (m+e) hkn s
  have hfactor (s : ComplexModel k) (hs : s ∈ V) :
      tangentInclusion m e (θf s) = θ s := by
    obtain ⟨u, _hu, heq⟩ := hθmem s hs
    change tangentInclusion m e (tangentProjection m e (θ s)) = θ s
    rw [← heq, tangentProjection_tangentInclusion]
  have hfactorEv : (tangentInclusion m e) ∘ θf =ᶠ[𝓝 (0 : ComplexModel k)] θ := by
    filter_upwards [hV.mem_nhds h0V] with s hs
    exact hfactor s hs
  have hdθ := hθ.differentiableAt (hV.mem_nhds h0V)
  have hdθf := hθf.differentiableAt (hV.mem_nhds h0V)
  have hdfactor : (tangentInclusion m e).comp (fderiv ℂ θf 0) = fderiv ℂ θ 0 := by
    have hh := hfactorEv.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_comp 0 (tangentInclusion m e).differentiableAt hdθf,
      ContinuousLinearMap.fderiv] at hh
    exact hh
  have hdθformula : fderiv ℂ θ 0 = (fderiv ℂ Φ.invFun 0).comp ia := by
    have hi := (local_invFun_holomorphic Φ hΦ0).self_of_nhds
    simpa only [θ, map_zero, ContinuousLinearMap.fderiv] using
      fderiv_comp 0 (by simpa only [map_zero] using hi) ia.differentiableAt
  have hL : Function.Injective (fderiv ℂ θf 0) := by
    intro s t hst
    apply prefixInclusion_injective k (m+e) hkn
    have hh := congrArg (fun u => fderiv ℂ Φ.toFun 0 (tangentInclusion m e u)) hst
    have hf (u : ComplexModel k) :
        fderiv ℂ Φ.toFun 0 (tangentInclusion m e (fderiv ℂ θf 0 u)) = ia u := by
      change fderiv ℂ Φ.toFun 0 (((tangentInclusion m e).comp (fderiv ℂ θf 0)) u) = _
      rw [hdfactor, hdθformula,
        ContinuousLinearMap.comp_apply]
      exact ambient_inverse_derivative Φ hΦ0 (ia u)
    simpa only [hf] using hh
  obtain ⟨hkm, A, hA⟩ := exists_linear_completion_of_injective_prefix
    (fderiv ℂ θf 0).toLinearMap hL
  let i := prefixInclusion k m hkm
  let p := prefixProjection k m hkm
  let N : Set (ComplexModel m) := p ⁻¹' V
  let H : ComplexModel m → ComplexModel m := fun u => θf (p u) + A (u - i (p u))
  have hN : IsOpen N := hV.preimage p.continuous
  have h0N : (0 : ComplexModel m) ∈ N := by simpa only [N, mem_preimage, map_zero] using h0V
  have hH : DifferentiableOn ℂ H N := by
    exact (hθf.comp p.differentiable.differentiableOn (fun _ hu => hu)).add
      (A.differentiable.comp (differentiable_id.sub
        (i.differentiable.comp p.differentiable))).differentiableOn
  have hH0 : H 0 = 0 := by simp only [H, map_zero, hθf0, sub_self, add_zero]
  have hHi (s : ComplexModel k) : H (i s) = θf s := by
    simp only [H, i, p, prefixProjection_inclusion, sub_self, map_zero, add_zero]
  have hdH : fderiv ℂ H 0 = A.toContinuousLinearMap := by
    have hdθf' : HasFDerivAt θf (fderiv ℂ θf 0) (p 0) := by
      simpa only [map_zero] using hdθf.hasFDerivAt
    have hd : HasFDerivAt H ((fderiv ℂ θf 0).comp p + A.toContinuousLinearMap.comp
        (ContinuousLinearMap.id ℂ (ComplexModel m) - i.comp p)) 0 :=
      (hdθf'.comp 0 p.hasFDerivAt).add
        (A.toContinuousLinearMap.hasFDerivAt.comp 0
          ((hasFDerivAt_id (𝕜 := ℂ) (0 : ComplexModel m)).sub
            (i.hasFDerivAt.comp 0 p.hasFDerivAt)))
    have heq : ((fderiv ℂ θf (p 0)).comp p + A.toContinuousLinearMap.comp
        (ContinuousLinearMap.id ℂ (ComplexModel m) - i.comp p)) = A.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro u
      have hh : A (i (p u)) = fderiv ℂ θf 0 (p u) := hA (p u)
      change fderiv ℂ θf (p 0) (p u) + A (u - i (p u)) = A u
      rw [map_zero, map_sub]
      rw [← hh]
      abel
    rw [← heq]
    exact hd.fderiv
  obtain ⟨Θ, hΘN, hΘH, _hΘinj⟩ := exists_localHolomorphicEquivAt hN h0N hH
    (by rw [hdH]; exact A.injective)
  have hΘ0 : Θ.toFun 0 = 0 := by rw [hΘH]; exact hH0
  let χ := inverseAtZero Θ hΘ0
  have hχ0 : χ.toFun 0 = 0 := local_invFun_zero Θ hΘ0
  let param : ComplexModel m → ComplexModel k := pa ∘ Φ.toFun ∘ tangentInclusion m e
  have hparam0 : param 0 = 0 := by simp only [param, Function.comp_apply, map_zero, hΦ0]
  have hdparam : DifferentiableAt ℂ param 0 := by
    have hto : DifferentiableAt ℂ Φ.toFun (tangentInclusion m e 0) := by
      simpa only [map_zero] using (local_toFun_holomorphic Φ).self_of_nhds
    exact pa.differentiableAt.comp 0
      (hto.comp 0 (tangentInclusion m e).differentiableAt)
  have hlegal : ∀ᶠ u in 𝓝 (0 : ComplexModel m), i (param u) ∈ Θ.source := by
    have ht := (i.continuous.continuousAt.comp hdparam.continuousAt).tendsto
    apply ht.eventually
    exact Θ.isOpen_source.mem_nhds (by
      simpa only [Function.comp_apply, hparam0, map_zero] using Θ.center_mem_source)
  have hambient : ∀ᶠ u in 𝓝 (0 : ComplexModel m), tangentInclusion m e u ∈ Φ.source := by
    apply (tangentInclusion m e).continuous.continuousAt.tendsto.eventually
    exact Φ.isOpen_source.mem_nhds (by simpa only [map_zero] using Φ.center_mem_source)
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp (hlegal.and hambient)
  let χ' := χ.restrict U hU 0 ⟨χ.center_mem_source, h0U⟩
  refine ⟨hkm, χ', hχ0, ?_⟩
  intro u hu
  have huχ : u ∈ χ.source := hu.1
  have hulegal := (hUsub hu.2).1
  have huambient := (hUsub hu.2).2
  change u ∈ D ↔ χ.toFun u ∈ complexCoordinatePlane m k
  constructor
  · intro huD
    have hp : Φ.toFun (tangentInclusion m e u) ∈ complexCoordinatePlane (m+e) k :=
      (hflat huambient).mp ⟨u, huD, rfl⟩
    have hpar : ia (param u) = Φ.toFun (tangentInclusion m e u) :=
      prefixInclusion_projection k (m+e) hkn hp
    have hθu : θf (param u) = u := by
      change tangentProjection m e (Φ.invFun (ia (param u))) = u
      rw [hpar, Φ.left_inv _ huambient, tangentProjection_tangentInclusion]
    have hHu : Θ.toFun (i (param u)) = u := by rw [hΘH, hHi, hθu]
    have hχu : χ.toFun u = i (param u) := by
      change Θ.invFun u = _
      calc
        Θ.invFun u = Θ.invFun (Θ.toFun (i (param u))) := congrArg Θ.invFun hHu.symm
        _ = i (param u) := Θ.left_inv _ hulegal
    rw [hχu]
    exact prefixInclusion_mem_plane k m hkm _
  · intro huplane
    have hiu : i (p (χ.toFun u)) = χ.toFun u :=
      prefixInclusion_projection k m hkm huplane
    have hrange : χ.toFun u ∈ Θ.source := Θ.mapsTo_invFun huχ
    have hsV : p (χ.toFun u) ∈ V := hΘN hrange
    have hθD : θf (p (χ.toFun u)) ∈ D := by
      obtain ⟨v, hv, heq⟩ := hθmem _ hsV
      have hh := congrArg (tangentProjection m e) heq
      have hvθ : v = θf (p (χ.toFun u)) := by
        simpa only [θf, Function.comp_apply, tangentProjection_tangentInclusion] using hh
      exact hvθ ▸ hv
    have huθ : u = θf (p (χ.toFun u)) := by
      have hi := Θ.right_inv u huχ
      change Θ.toFun (χ.toFun u) = u at hi
      rw [← hiu, hΘH, hHi] at hi
      exact hi.symm
    exact huθ.symm ▸ hθD

/-- Actual smoothness of the whole zero-section image yields actual
smoothness downstairs, with the free inverse constructed by the IFT. -/
theorem regularAtDim_zeroSection_reflects {m e k : ℕ} {D : Set (ComplexModel m)}
    (hreg : RegularAtDim (n := m+e) ((tangentInclusion m e) '' D) 0 k) :
    RegularAtDim (n := m) D 0 k := by
  obtain ⟨hkn, h0D, Φ, hΦ0, hflat⟩ := (model_regular_iff _ _ _).mp hreg
  obtain ⟨hkm, χ, hχ0, hχflat⟩ := exists_free_chart_of_image_chart D hkn Φ hΦ0 hflat
  have hzD : (0 : ComplexModel m) ∈ D := by
    obtain ⟨u, hu, heq⟩ := h0D
    have hu0 := congrArg (tangentProjection m e) heq
    simp only [tangentProjection_tangentInclusion, map_zero] at hu0
    exact hu0 ▸ hu
  exact (model_regular_iff _ _ _).mpr ⟨hkm, hzD, χ, hχ0, hχflat⟩

end
end Hironaka.HironakaActualFreePlaneRegularity
