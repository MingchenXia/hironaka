/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.RegularPatchPushforward
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.LocalHolomorphicInverse
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Nested flattening coordinates for a submanifold of a submanifold

Source: standard (the rank theorem); used by Wlodarczyk 2005 (`wlodarczyk05-hironaka`) and Bierstone--Milman 2008
(`bierstone-milman08-functoriality`) whenever a centre `C` of a blowup lies in a submanifold `N` (the strict
transform of `N` is then the blowup of `N` along `C`).

If `C ⊆ N` are regular of dimensions `k_C ≤ k_N` at `x ∈ C`, there are holomorphic coordinates at
`x` (the preferred chart followed by a local biholomorphism, centred at `0`) in which, near `x`,

  `C = ℂ^{k_C} × 0`   and   `N = ℂ^{k_N} × 0`

simultaneously (`exists_nested_flattening`), in the convention of `RegularAtDim` and of the
monomial charts of a blowup (the normal coordinates are the LAST ones).

Proof.  In coordinates flattening `N`, let `Θ` flatten `C`, and let `φ(v) = Θ⁻¹(v, 0)`
(`v ∈ ℂ^{k_C}`) parametrize `C`; it takes values in `ℂ^{k_N} × 0`, so `φ = ι ∘ φ'` with
`φ' : ℂ^{k_C} → ℂ^{k_N}` of injective differential `D` at `0`.  Choose a linear `J` from the middle
coordinates `ℂ^{k_N - k_C}` onto a complement of the range of `D`, and put

  `F(v, s, t) = (φ'(v) + J s, t)`.

Its differential at `0` is invertible, and `F(v, 0, 0) = φ(v)`, `F(w) ∈ ℂ^{k_N} × 0 ⟺ t = 0`.  The
local inverse of `F` (inverse function theorem) is the required coordinate system
(`exists_nested_flattening_model`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.NestedFlattening

open Hironaka.RegularLocusDense RegularAtDimTransport RegularPatchPushforward

noncomputable section

variable {n : ℕ}

/-! ### Linear coordinates -/

section Linear

/-- The middle coordinates `(z_{k}, …, z_{m-1})` of `z ∈ ℂ^m`. -/
def midCoords (k m : ℕ) : ComplexModel m →L[ℂ] ComplexModel (m - k) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i : Fin (m - k) =>
        if h : k + i.1 < m then z ⟨k + i.1, h⟩ else 0)
      map_add' := by
        intro z z'
        ext i
        by_cases h : k + i.1 < m <;> simp [h]
      map_smul' := by
        intro c z
        ext i
        by_cases h : k + i.1 < m <;> simp [h] }

theorem midCoords_apply {k m : ℕ} (z : ComplexModel m) (i : Fin (m - k)) :
    midCoords k m z i = if h : k + i.1 < m then z ⟨k + i.1, h⟩ else 0 := rfl

/-- The middle coordinates of a point of `ℂ^k × 0` vanish. -/
theorem midCoords_coordinateInclusion {k m : ℕ} (v : ComplexModel k) :
    midCoords k m (coordinateInclusion m k v) = 0 := by
  ext i
  simp only [midCoords_apply, coordinateInclusion_apply]
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl

/-- A point whose first `k` and middle coordinates vanish is `0`. -/
theorem eq_zero_of_projection_midCoords {k m : ℕ} (hkm : k ≤ m) {z : ComplexModel m}
    (h1 : coordinateProjection m k z = 0) (h2 : midCoords k m z = 0) : z = 0 := by
  ext i
  by_cases hi : i.1 < k
  · have := congrArg (fun w : ComplexModel k => w ⟨i.1, hi⟩) h1
    simpa [coordinateProjection_apply, i.2] using this
  · have hlt : i.1 - k < m - k := by omega
    have := congrArg (fun w : ComplexModel (m - k) => w ⟨i.1 - k, hlt⟩) h2
    have hk : k + (i.1 - k) = i.1 := by omega
    have hi' : k + (i.1 - k) < m := by omega
    simp only [midCoords_apply, dif_pos hi', PiLp.zero_apply] at this
    simpa [hk] using this

/-- `ℂ^{k} × 0 ⊆ ℂ^{m} × 0` through `ℂ^m`: the two-step inclusion. -/
theorem coordinateInclusion_comp {k m : ℕ} (hkm : k ≤ m) (v : ComplexModel k) :
    coordinateInclusion n m (coordinateInclusion m k v) = coordinateInclusion n k v := by
  ext i
  simp only [coordinateInclusion_apply]
  by_cases hm : i.1 < m
  · by_cases hk : i.1 < k
    · simp [hm, hk]
    · simp [hm, hk]
  · have hk : ¬ i.1 < k := fun h => hm (lt_of_lt_of_le h hkm)
    simp [hm, hk]

/-- The first `k` coordinates through `ℂ^m`. -/
theorem coordinateProjection_comp {k m : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (z : ComplexModel n) :
    coordinateProjection m k (coordinateProjection n m z) = coordinateProjection n k z := by
  ext a
  have ham : a.1 < m := lt_of_lt_of_le a.2 hkm
  have han : a.1 < n := lt_of_lt_of_le ham hmn
  simp [coordinateProjection_apply, ham, han]

/-- The last `n - m` coordinates of `z - ι(π z)` are those of `z`, the first `m` vanish. -/
theorem sub_inclusion_projection_apply {m : ℕ} (z : ComplexModel n) (i : Fin n) :
    (z - coordinateInclusion n m (coordinateProjection n m z)) i = if i.1 < m then 0 else z i := by
  by_cases h : i.1 < m
  · simp [coordinateInclusion_apply, coordinateProjection_apply, h, i.2]
  · simp [coordinateInclusion_apply, h]

end Linear

/-! ### The model case in `ℂⁿ` -/

section Model

/-- The map `F(w) = ι(φ'(π_{k_C} w) + J(mid w)) + (w - ι(π_{k_N} w))`. -/
def nestedMap (kC kN : ℕ) (φ' : ComplexModel kC → ComplexModel kN)
    (J : ComplexModel (kN - kC) →L[ℂ] ComplexModel kN) (w : ComplexModel n) : ComplexModel n :=
  coordinateInclusion n kN (φ' (coordinateProjection n kC w) +
      J (midCoords kC kN (coordinateProjection n kN w))) +
    (w - coordinateInclusion n kN (coordinateProjection n kN w))

/-- `F(w) ∈ ℂ^{k_N} × 0 ⟺ w ∈ ℂ^{k_N} × 0`. -/
theorem nestedMap_mem_plane_iff {kC kN : ℕ} (φ' : ComplexModel kC → ComplexModel kN)
    (J : ComplexModel (kN - kC) →L[ℂ] ComplexModel kN) (w : ComplexModel n) :
    nestedMap kC kN φ' J w ∈ complexCoordinatePlane n kN ↔ w ∈ complexCoordinatePlane n kN := by
  have key : ∀ i : Fin n, kN ≤ i.1 → nestedMap kC kN φ' J w i = w i := by
    intro i hi
    have h1 := coordinateInclusion_mem_complexCoordinatePlane (n := n)
      (φ' (coordinateProjection n kC w) + J (midCoords kC kN (coordinateProjection n kN w))) i hi
    have h2 := sub_inclusion_projection_apply (m := kN) w i
    simp only [nestedMap, PiLp.add_apply, h1, zero_add, h2, if_neg (not_lt.mpr hi)]
  constructor
  · intro h i hi
    rw [← key i hi]
    exact h i hi
  · intro h i hi
    rw [key i hi]
    exact h i hi

/-- `F(v, 0, 0) = ι(φ'(v))`. -/
theorem nestedMap_coordinateInclusion {kC kN : ℕ} (hkC : kC ≤ kN) (hkN : kN ≤ n)
    (φ' : ComplexModel kC → ComplexModel kN)
    (J : ComplexModel (kN - kC) →L[ℂ] ComplexModel kN) (v : ComplexModel kC) :
    nestedMap kC kN φ' J (coordinateInclusion n kC v) = coordinateInclusion n kN (φ' v) := by
  have hv : coordinateInclusion n kC v = coordinateInclusion n kN (coordinateInclusion kN kC v) :=
    (coordinateInclusion_comp hkC v).symm
  have hp : coordinateProjection n kN (coordinateInclusion n kC v) =
      coordinateInclusion kN kC v := by
    rw [hv, coordinateProjection_coordinateInclusion hkN]
  have hq : coordinateProjection n kC (coordinateInclusion n kC v) = v :=
    coordinateProjection_coordinateInclusion (le_trans hkC hkN) v
  simp only [nestedMap, hp, hq, midCoords_coordinateInclusion, map_zero, add_zero]
  rw [← hv, sub_self, add_zero]

/-- **Nested flattening in the model space.**  Let `Θ` (centred at `0`, `Θ 0 = 0`) flatten
`C ⊆ ℂⁿ` onto `ℂ^{k_C} × 0`, and let `C ⊆ ℂ^{k_N} × 0` on the source of `Θ`.  Then some `Φ`
(centred at `0`, `Φ 0 = 0`, source inside that of `Θ`) flattens `C` onto `ℂ^{k_C} × 0` and
preserves `ℂ^{k_N} × 0`. -/
theorem exists_nested_flattening_model {kC kN : ℕ} (hkC : kC ≤ kN) (hkN : kN ≤ n)
    {C : Set (ComplexModel n)} (Θ : LocalHolomorphicEquivAt (n := n) 0) (hΘ0 : Θ.toFun 0 = 0)
    (hΘC : ∀ u ∈ Θ.source, u ∈ C ↔ Θ.toFun u ∈ complexCoordinatePlane n kC)
    (hCN : ∀ u ∈ Θ.source, u ∈ C → u ∈ complexCoordinatePlane n kN) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) 0, Φ.source ⊆ Θ.source ∧ Φ.toFun 0 = 0 ∧
      ∀ u ∈ Φ.source, (u ∈ C ↔ Φ.toFun u ∈ complexCoordinatePlane n kC) ∧
        (u ∈ complexCoordinatePlane n kN ↔ Φ.toFun u ∈ complexCoordinatePlane n kN) := by
  classical
  have hkCn : kC ≤ n := le_trans hkC hkN
  -- the parametrization `φ v = Θ⁻¹(v, 0)` of `C`, and its reading `φ'` in `ℂ^{k_N}`
  set ιC := coordinateInclusion n kC with hιC
  set ιN := coordinateInclusion n kN with hιN
  set V : Set (ComplexModel kC) := ιC ⁻¹' Θ.target with hV
  have hVo : IsOpen V := Θ.isOpen_target.preimage ιC.continuous
  have hΘinv0 : Θ.invFun 0 = 0 := by
    have := Θ.left_inv 0 Θ.center_mem_source
    rwa [hΘ0] at this
  have h0t : (0 : ComplexModel n) ∈ Θ.target := by
    have := Θ.mapsTo_toFun Θ.center_mem_source
    rwa [hΘ0] at this
  have h0V : (0 : ComplexModel kC) ∈ V := by
    show ιC 0 ∈ Θ.target
    rw [map_zero]; exact h0t
  set φ : ComplexModel kC → ComplexModel n := fun v => Θ.invFun (ιC v) with hφ
  set φ' : ComplexModel kC → ComplexModel kN := fun v => coordinateProjection n kN (φ v)
    with hφ'
  have hφsrc : ∀ v ∈ V, φ v ∈ Θ.source := fun v hv => Θ.mapsTo_invFun hv
  have hφC : ∀ v ∈ V, φ v ∈ C := fun v hv => (hΘC _ (hφsrc v hv)).mpr (by
    show Θ.toFun (Θ.invFun (ιC v)) ∈ _
    rw [Θ.right_inv _ hv]
    exact coordinateInclusion_mem_complexCoordinatePlane v)
  have hφN : ∀ v ∈ V, ιN (φ' v) = φ v := fun v hv =>
    coordinateInclusion_coordinateProjection (hCN _ (hφsrc v hv) (hφC v hv))
  have hφd : DifferentiableOn ℂ φ V :=
    Θ.invFun_holomorphic.comp ιC.differentiableOn fun v hv => hv
  have hφ'd : DifferentiableOn ℂ φ' V :=
    (coordinateProjection n kN).differentiableOn.comp hφd (mapsTo_univ _ _)
  have hφ'0 : φ' 0 = 0 := by
    simp only [hφ', hφ, map_zero, hΘinv0]
  -- the differential `D` of `φ'` at `0` is injective
  set D := fderiv ℂ φ' 0 with hD
  have hφ'diff : DifferentiableAt ℂ φ' 0 := hφ'd.differentiableAt (hVo.mem_nhds h0V)
  have hΘdiff : DifferentiableAt ℂ Θ.toFun 0 :=
    Θ.toFun_holomorphic.differentiableAt (Θ.isOpen_source.mem_nhds Θ.center_mem_source)
  have hDinj : Function.Injective D := by
    have hcomp : HasFDerivAt (fun v => Θ.toFun (ιN (φ' v)))
        ((fderiv ℂ Θ.toFun 0).comp (ιN.comp D)) 0 := by
      have h1 : HasFDerivAt (fun v => ιN (φ' v)) (ιN.comp D) 0 :=
        ιN.hasFDerivAt.comp 0 hφ'diff.hasFDerivAt
      have h2 : HasFDerivAt Θ.toFun (fderiv ℂ Θ.toFun 0) (ιN (φ' 0)) := by
        rw [hφ'0, map_zero]; exact hΘdiff.hasFDerivAt
      exact h2.comp 0 h1
    have heq : (fun v => Θ.toFun (ιN (φ' v))) =ᶠ[𝓝 0] fun v => ιC v := by
      filter_upwards [hVo.mem_nhds h0V] with v hv
      rw [hφN v hv]
      exact Θ.right_inv _ hv
    have hι : HasFDerivAt (fun v => Θ.toFun (ιN (φ' v))) ιC 0 :=
      ιC.hasFDerivAt.congr_of_eventuallyEq heq
    have hEq := hcomp.unique hι
    intro v w hvw
    have : ιC v = ιC w := by
      rw [← hEq]
      simp only [ContinuousLinearMap.comp_apply, hvw]
    have h := congrArg (coordinateProjection n kC) this
    rwa [coordinateProjection_coordinateInclusion hkCn,
      coordinateProjection_coordinateInclusion hkCn] at h
  -- a linear complement of the range of `D`, parametrized by the middle coordinates
  set R := LinearMap.range (D : ComplexModel kC →ₗ[ℂ] ComplexModel kN) with hR
  obtain ⟨Q, hRQ⟩ := Submodule.exists_isCompl R
  have hRdim : Module.finrank ℂ R = kC := by
    rw [hR, LinearMap.finrank_range_of_inj hDinj, finrank_euclideanSpace_fin]
  have hQdim : Module.finrank ℂ Q = kN - kC := by
    have := Submodule.finrank_add_eq_of_isCompl hRQ
    rw [finrank_euclideanSpace_fin, hRdim] at this
    omega
  have hQdim' : Module.finrank ℂ (ComplexModel (kN - kC)) = Module.finrank ℂ Q := by
    rw [finrank_euclideanSpace_fin, hQdim]
  set J₀ : ComplexModel (kN - kC) ≃ₗ[ℂ] Q := LinearEquiv.ofFinrankEq _ _ hQdim' with hJ₀
  set J : ComplexModel (kN - kC) →L[ℂ] ComplexModel kN :=
    LinearMap.toContinuousLinearMap (Q.subtype ∘ₗ (J₀ : ComplexModel (kN - kC) →ₗ[ℂ] Q))
    with hJ
  have hJQ : ∀ s, J s ∈ Q := fun s => (J₀ s).2
  have hJinj : Function.Injective J := by
    intro s t hst
    have : (J₀ s : ComplexModel kN) = J₀ t := hst
    exact J₀.injective (Subtype.ext this)
  -- the map `F` and its differential at `0`
  set F : ComplexModel n → ComplexModel n := nestedMap kC kN φ' J with hF
  set S : Set (ComplexModel n) := coordinateProjection n kC ⁻¹' V with hS
  have hSo : IsOpen S := hVo.preimage (coordinateProjection n kC).continuous
  have h0S : (0 : ComplexModel n) ∈ S := by
    show coordinateProjection n kC 0 ∈ V
    rw [map_zero]; exact h0V
  have hFd : DifferentiableOn ℂ F S := by
    have h1 : DifferentiableOn ℂ (fun w => φ' (coordinateProjection n kC w)) S :=
      hφ'd.comp (coordinateProjection n kC).differentiableOn fun w hw => hw
    have h2 : DifferentiableOn ℂ
        (fun w => J (midCoords kC kN (coordinateProjection n kN w))) S :=
      ((J.comp ((midCoords kC kN).comp (coordinateProjection n kN))).differentiable).differentiableOn
    exact (ιN.differentiable.comp_differentiableOn (h1.add h2)).add
      (differentiableOn_id.sub (ιN.comp (coordinateProjection n kN)).differentiable.differentiableOn)
  set L : ComplexModel n →L[ℂ] ComplexModel n :=
    ιN.comp ((D.comp (coordinateProjection n kC)) +
        J.comp ((midCoords kC kN).comp (coordinateProjection n kN))) +
      (ContinuousLinearMap.id ℂ _ - ιN.comp (coordinateProjection n kN)) with hL
  have hFL : HasFDerivAt F L 0 := by
    have h1 : HasFDerivAt (fun w => φ' (coordinateProjection n kC w))
        (D.comp (coordinateProjection n kC)) 0 := by
      have : HasFDerivAt φ' D (coordinateProjection n kC 0) := by
        rw [map_zero]; exact hφ'diff.hasFDerivAt
      exact this.comp 0 (coordinateProjection n kC).hasFDerivAt
    have h2 : HasFDerivAt (fun w => J (midCoords kC kN (coordinateProjection n kN w)))
        (J.comp ((midCoords kC kN).comp (coordinateProjection n kN))) 0 :=
      (J.comp ((midCoords kC kN).comp (coordinateProjection n kN))).hasFDerivAt
    have h3 := ιN.hasFDerivAt.comp 0 (h1.add h2)
    have h4 : HasFDerivAt (fun w => w - ιN (coordinateProjection n kN w))
        (ContinuousLinearMap.id ℂ _ - ιN.comp (coordinateProjection n kN)) 0 :=
      (hasFDerivAt_id 0).sub (ιN.comp (coordinateProjection n kN)).hasFDerivAt
    exact h3.add h4
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    set z := coordinateProjection n kN w with hz
    -- project to the first `k_N` coordinates
    have hproj := congrArg (coordinateProjection n kN) hw
    have hpz : coordinateProjection n kC w = coordinateProjection kN kC z :=
      (coordinateProjection_comp hkC hkN w).symm
    simp only [hL, _root_.add_apply, ContinuousLinearMap.comp_apply,
      _root_.sub_apply, ContinuousLinearMap.id_apply, map_add, map_sub, hιN,
      coordinateProjection_coordinateInclusion hkN, map_zero] at hproj
    rw [← hz, hpz, sub_self, add_zero] at hproj
    have hsum : D (coordinateProjection kN kC z) + J (midCoords kC kN z) = 0 := hproj
    have hDz : D (coordinateProjection kN kC z) ∈ R := LinearMap.mem_range_self _ _
    have hJz : J (midCoords kC kN z) ∈ Q := hJQ _
    have hboth : D (coordinateProjection kN kC z) = 0 ∧ J (midCoords kC kN z) = 0 := by
      have hneg : D (coordinateProjection kN kC z) = -J (midCoords kC kN z) :=
        eq_neg_of_add_eq_zero_left hsum
      have hmemQ : D (coordinateProjection kN kC z) ∈ Q := by rw [hneg]; exact Q.neg_mem hJz
      have hzero : D (coordinateProjection kN kC z) = 0 :=
        (Submodule.disjoint_def.mp hRQ.disjoint) _ hDz hmemQ
      refine ⟨hzero, ?_⟩
      rw [hzero, zero_add] at hsum
      exact hsum
    have hz1 : coordinateProjection kN kC z = 0 := hDinj (by rw [hboth.1, map_zero])
    have hz2 : midCoords kC kN z = 0 := hJinj (by rw [hboth.2, map_zero])
    have hz0 : z = 0 := eq_zero_of_projection_midCoords hkC hz1 hz2
    -- then `L w = w - ι(π w) = w`
    have hw' := hw
    simp only [hL, _root_.add_apply, ContinuousLinearMap.comp_apply,
      _root_.sub_apply, ContinuousLinearMap.id_apply] at hw'
    rw [← hz, hpz, hz0] at hw'
    simpa using hw'
  have hFinj : Function.Injective (fderiv ℂ F 0) := by
    rw [hFL.fderiv]; exact hLinj
  -- the inverse function theorem
  obtain ⟨Φ₁, hΦ₁S, hΦ₁F, -⟩ := exists_localHolomorphicEquivAt hSo h0S hFd hFinj
  have hF0 : F 0 = 0 := by
    simp only [hF, nestedMap, map_zero, hφ'0, sub_zero, add_zero]
  have h0t₁ : (0 : ComplexModel n) ∈ Φ₁.target := by
    have := Φ₁.mapsTo_toFun Φ₁.center_mem_source
    rw [hΦ₁F, hF0] at this
    exact this
  have hFiota : ∀ v, F (ιC v) = ιN (φ' v) := fun v =>
    nestedMap_coordinateInclusion hkC hkN φ' J v
  -- shrink so that every point of `C` is `F (v, 0, 0)` with `(v, 0, 0)` in the source of `Φ₁`
  set s : Set (ComplexModel n) :=
    Θ.source ∩ (fun u => ιC (coordinateProjection n kC (Θ.toFun u))) ⁻¹' Φ₁.source with hs
  have hso : IsOpen s :=
    ((ιC.continuous.comp (coordinateProjection n kC).continuous).comp_continuousOn
      Θ.toFun_holomorphic.continuousOn).isOpen_inter_preimage Θ.isOpen_source Φ₁.isOpen_source
  have h0s : (0 : ComplexModel n) ∈ s := by
    refine ⟨Θ.center_mem_source, ?_⟩
    show ιC (coordinateProjection n kC (Θ.toFun 0)) ∈ Φ₁.source
    rw [hΘ0, map_zero, map_zero]; exact Φ₁.center_mem_source
  set Φ₂ := symmAt Φ₁ h0t₁ with hΦ₂
  refine ⟨Φ₂.restrict s hso 0 ⟨h0t₁, h0s⟩, fun u hu => hu.2.1, ?_, ?_⟩
  · show Φ₁.invFun 0 = 0
    have := Φ₁.left_inv 0 Φ₁.center_mem_source
    rwa [hΦ₁F, hF0] at this
  intro u hu
  obtain ⟨hut, hus⟩ := hu
  have hut' : u ∈ Φ₁.target := hut
  set w := Φ₁.invFun u with hw
  have hwsrc : w ∈ Φ₁.source := Φ₁.mapsTo_invFun hut'
  have hFw : F w = u := by
    have := Φ₁.right_inv u hut'
    rwa [hΦ₁F] at this
  show (u ∈ C ↔ w ∈ complexCoordinatePlane n kC) ∧
    (u ∈ complexCoordinatePlane n kN ↔ w ∈ complexCoordinatePlane n kN)
  refine ⟨⟨fun huC => ?_, fun hwC => ?_⟩, ?_⟩
  · -- `u = φ v = F (v, 0, 0)` with `(v, 0, 0)` in the source of `Φ₁`
    set v := coordinateProjection n kC (Θ.toFun u) with hv
    have hΘu : Θ.toFun u ∈ complexCoordinatePlane n kC := (hΘC u hus.1).mp huC
    have hιv : ιC v = Θ.toFun u := coordinateInclusion_coordinateProjection hΘu
    have hvV : v ∈ V := by
      show ιC v ∈ Θ.target
      rw [hιv]; exact Θ.mapsTo_toFun hus.1
    have huφ : u = φ v := by
      show u = Θ.invFun (ιC v)
      rw [hιv, Θ.left_inv u hus.1]
    have hFv : F (ιC v) = u := by rw [hFiota, hφN v hvV, ← huφ]
    have hιvsrc : ιC v ∈ Φ₁.source := hus.2
    have : w = ιC v := by
      rw [hw, ← hFv, ← hΦ₁F, Φ₁.left_inv _ hιvsrc]
    rw [this]
    exact coordinateInclusion_mem_complexCoordinatePlane v
  · -- `w = (v, 0, 0)`, so `u = F w = φ v ∈ C`
    set v := coordinateProjection n kC w with hv
    have hιv : ιC v = w := coordinateInclusion_coordinateProjection hwC
    have hvV : v ∈ V := hΦ₁S hwsrc
    rw [← hFw, ← hιv, hFiota, hφN v hvV]
    exact hφC v hvV
  · rw [← hFw]
    exact nestedMap_mem_plane_iff φ' J w

end Model

/-! ### On a complex manifold -/

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Nested flattening coordinates.**  If `C ⊆ N` are regular at `x` of dimensions
`k_C ≤ k_N`, one local biholomorphism `Φ` after the preferred chart at `x` (centred, `Φ(e x) = 0`)
flattens `C` onto `ℂ^{k_C} × 0` and `N` onto `ℂ^{k_N} × 0` simultaneously. -/
theorem exists_nested_flattening {C N : Set M} {x : M} {kC kN : ℕ} (hkC : kC ≤ kN)
    (hC : RegularAtDim (n := n) C x kC) (hN : RegularAtDim (n := n) N x kN) (hCN : C ⊆ N) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x),
      Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
      ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kC) ∧
          (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kN) := by
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨hkNn, -, Ψ, hΨt, hΨ0, hΨN⟩ := hN
  obtain ⟨-, -, Θ, hΘt, hΘ0, hΘC⟩ := hC
  have h0Ψ : (0 : ComplexModel n) ∈ Ψ.target := by
    rw [← hΨ0]; exact Ψ.mapsTo_toFun Ψ.center_mem_source
  have hΨinv0 : Ψ.invFun 0 = e x := by
    have := Ψ.left_inv _ Ψ.center_mem_source
    rwa [hΨ0] at this
  -- `Θ` read in the coordinates of `Ψ`
  set Θ' := LocalHolomorphicEquivAt.comp (symmAt Ψ h0Ψ) Θ hΨinv0 with hΘ'
  have hΘ'0 : Θ'.toFun 0 = 0 := by
    show Θ.toFun (Ψ.invFun 0) = 0
    rw [hΨinv0, hΘ0]
  set C₀ : Set (ComplexModel n) := {u | e.symm (Ψ.invFun u) ∈ C} with hC₀
  have hsrc : ∀ u ∈ Θ'.source, u ∈ Ψ.target ∧ Ψ.invFun u ∈ Θ.source := fun u hu => hu
  have hΘ'C : ∀ u ∈ Θ'.source, u ∈ C₀ ↔ Θ'.toFun u ∈ complexCoordinatePlane n kC := by
    intro u hu
    obtain ⟨hut, huΘ⟩ := hsrc u hu
    have hey : e.symm (Ψ.invFun u) ∈ e.source := e.map_target (hΘt huΘ)
    have heey : e (e.symm (Ψ.invFun u)) = Ψ.invFun u := e.right_inv (hΘt huΘ)
    have := hΘC (y := e.symm (Ψ.invFun u)) hey (by rw [heey]; exact huΘ)
    rw [heey] at this
    exact this
  have hΘ'N : ∀ u ∈ Θ'.source, u ∈ C₀ → u ∈ complexCoordinatePlane n kN := by
    intro u hu huC
    obtain ⟨hut, huΘ⟩ := hsrc u hu
    have hey : e.symm (Ψ.invFun u) ∈ e.source := e.map_target (hΘt huΘ)
    have heey : e (e.symm (Ψ.invFun u)) = Ψ.invFun u := e.right_inv (hΘt huΘ)
    have hΨsrc : Ψ.invFun u ∈ Ψ.source := Ψ.mapsTo_invFun hut
    have := (hΨN (y := e.symm (Ψ.invFun u)) hey (by rw [heey]; exact hΨsrc)).mp (hCN huC)
    rwa [heey, Ψ.right_inv u hut] at this
  obtain ⟨Φ₀, hΦ₀Θ, hΦ₀0, hΦ₀⟩ :=
    exists_nested_flattening_model hkC hkNn Θ' hΘ'0 hΘ'C hΘ'N
  refine ⟨LocalHolomorphicEquivAt.comp Ψ Φ₀ hΨ0, fun z hz => hΨt hz.1, ?_, ?_⟩
  · show Φ₀.toFun (Ψ.toFun (e x)) = 0
    rw [hΨ0, hΦ₀0]
  intro y hy hyΦ
  obtain ⟨hyΨ, hyΦ₀⟩ := hyΦ
  set u := Ψ.toFun (e y) with hu
  have hus : u ∈ Φ₀.source := hyΦ₀
  have hΨu : Ψ.invFun u = e y := Ψ.left_inv _ hyΨ
  have hyC : y ∈ C ↔ u ∈ C₀ := by
    show y ∈ C ↔ e.symm (Ψ.invFun u) ∈ C
    rw [hΨu, e.left_inv hy]
  refine ⟨?_, ?_⟩
  · rw [hyC]
    exact (hΦ₀ u hus).1
  · rw [hΨN hy hyΨ]
    exact (hΦ₀ u hus).2

end Manifold

end

end Hironaka.NestedFlattening
