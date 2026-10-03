/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.NestedFlattening
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.RegularPatchPullback
import Hironaka.Blowup.RegularPatchPushforward
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The strict transform of a submanifold through the centre is a submanifold

Source: Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), §2 (a marked ideal `(M, N, E, 𝓘, d)` is
transformed by a blowup of `M` with centre `C ⊆ N`, and `N'` is the strict transform of `N`); Wlodarczyk 2005
(`wlodarczyk05-hironaka`), §2 (restriction of a multiple test blow-up to a smooth subvariety containing the
centres); Demailly, CADG VII.12 (monomial charts).

Let `π : Y → X` be the blowup along `C`, and `N ⊇ C` a closed subset regular of dimension `k_N`
at each of its points.  Its (geometric) strict transform

  `N' = closure (π⁻¹ (N \ C))`

Is regular of dimension `k_N` at each of its points.

Proof.  Off `π⁻¹ C` the map `π` is a local biholomorphism and `N' = π⁻¹ N` there.  At a point
`z` over `C`, take nested flattening coordinates `Φ` for `C ⊆ N` at `π z`
(`NestedFlattening.exists_nested_flattening`: `C = ℂ^{k_C} × 0`, `N = ℂ^{k_N} × 0`) and a monomial
chart `j ≥ k_C` of the blowup around `z` with local inverse `W` (`σ_j ∘ W = Φ ∘ e ∘ π`,
`BlowupLocalSurjectivity.exists_monomialLocalInverse`).  Since `σ_j(w)_i = w_i w_j` (`i ≥ k_C`,
`i ≠ j`), `σ_j(w)_j = w_j`:
* `π u ∈ C ⟺ (W u)_j = 0`;
* if `j < k_N`: `π u ∈ N ⟺ (W u)_j = 0 ∨ W u ∈ ℂ^{k_N} × 0`;
* if `j ≥ k_N`: `π u ∈ N ⟹ (W u)_j = 0`.
So near `z`, `N' = W⁻¹(ℂ^{k_N} × 0)` if `j < k_N` (the points `ℓ_j(W u + t e_j)`, `t ≠ 0` small,
lie in `π⁻¹(N \ C)`), and `N'` misses a neighbourhood of `z` if `j ≥ k_N`.  `W` is a local
biholomorphism at `z` (its derivative is injective, `BlowupFibreDirection`), which flattens `N'`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupStrictSubmanifold

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupFibreDirection NestedFlattening Hironaka.RegularPatchPullback Hironaka.RegularLocusDense

noncomputable section

variable {n : ℕ}

/-! ### The monomial map and coordinate planes -/

section Monomial

variable {k : ℕ} {j : Fin n} {w : ComplexModel n}

/-- `σ_j(w) ∈ ℂ^{k} × 0 ⟺ w_j = 0`, for a normal index `j ≥ k`. -/
theorem monomial_mem_plane_iff (hj : k ≤ j.1) :
    monomial k j w ∈ complexCoordinatePlane n k ↔ w j = 0 := by
  constructor
  · intro h
    have := h j hj
    simpa [monomial_apply] using this
  · intro h i hi
    rw [monomial_apply]
    split_ifs with hij
    · rw [h, mul_zero]
    · have : i = j := by
        by_contra hne
        exact hij ⟨hi, hne⟩
      rw [this, h]

/-- For `k ≤ j < m`: `σ_j(w) ∈ ℂ^{m} × 0 ⟺ w_j = 0 ∨ w ∈ ℂ^{m} × 0`. -/
theorem monomial_mem_plane_iff_of_lt {m : ℕ} (hj : k ≤ j.1) (hjm : j.1 < m) :
    monomial k j w ∈ complexCoordinatePlane n m ↔ w j = 0 ∨ w ∈ complexCoordinatePlane n m := by
  constructor
  · intro h
    by_cases hwj : w j = 0
    · exact Or.inl hwj
    · refine Or.inr fun i hi => ?_
      have hik : k ≤ i.1 := le_trans hj (le_trans hjm.le hi)
      have hij : i ≠ j := fun hij => by rw [hij] at hi; omega
      have := h i hi
      rw [monomial_apply, if_pos ⟨hik, hij⟩] at this
      exact (mul_eq_zero.mp this).resolve_right hwj
  · rintro (hwj | hw) i hi
    · rw [monomial_apply]
      split_ifs with hij
      · rw [hwj, mul_zero]
      · have : i = j := by
          by_contra hne
          exact hij ⟨le_trans hj (le_trans hjm.le hi), hne⟩
        rw [this, hwj]
    · rw [monomial_apply]
      split_ifs <;> simp [hw i hi]

/-- For `m ≤ j`: `σ_j(w) ∈ ℂ^{m} × 0 ⟹ w_j = 0`. -/
theorem eq_zero_of_monomial_mem_plane {m : ℕ} (hjm : m ≤ j.1)
    (h : monomial k j w ∈ complexCoordinatePlane n m) : w j = 0 := by
  have := h j hjm
  simpa [monomial_apply] using this

end Monomial

/-! ### Dimension of a submanifold of a submanifold -/

section Dimension

/-- In the model space: if `Θ` flattens `C` onto `ℂ^{k_C} × 0` and `C ⊆ ℂ^{k_N} × 0` near `0`,
then `k_C ≤ k_N` (the parametrization `Θ⁻¹(·, 0)` read in `ℂ^{k_N}` has injective
differential). -/
theorem le_of_flattening_model {kC kN : ℕ} (hkCn : kC ≤ n) {C : Set (ComplexModel n)}
    (Θ : LocalHolomorphicEquivAt (n := n) 0) (hΘ0 : Θ.toFun 0 = 0)
    (hΘC : ∀ u ∈ Θ.source, u ∈ C ↔ Θ.toFun u ∈ complexCoordinatePlane n kC)
    (hCN : ∀ u ∈ Θ.source, u ∈ C → u ∈ complexCoordinatePlane n kN) : kC ≤ kN := by
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
  have := LinearMap.finrank_le_finrank_of_injective
    (f := (D : ComplexModel kC →ₗ[ℂ] ComplexModel kN)) hDinj
  simpa [finrank_euclideanSpace_fin] using this

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A submanifold of a submanifold has smaller dimension**: if `C ⊆ N` are regular at `x` of
dimensions `k_C` and `k_N`, then `k_C ≤ k_N`. -/
theorem le_of_regularAtDim_subset {C N : Set M} {x : M} {kC kN : ℕ}
    (hC : RegularAtDim (n := n) C x kC) (hN : RegularAtDim (n := n) N x kN) (hCN : C ⊆ N) :
    kC ≤ kN := by
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨-, -, Ψ, hΨt, hΨ0, hΨN⟩ := hN
  obtain ⟨hkCn, -, Θ, hΘt, hΘ0, hΘC⟩ := hC
  have h0Ψ : (0 : ComplexModel n) ∈ Ψ.target := by
    have := Ψ.mapsTo_toFun Ψ.center_mem_source
    rwa [hΨ0] at this
  have hΨinv0 : Ψ.invFun 0 = e x := by
    have := Ψ.left_inv _ Ψ.center_mem_source
    rwa [hΨ0] at this
  set Θ' := RegularAtDimTransport.LocalHolomorphicEquivAt.comp
    (RegularPatchPushforward.symmAt Ψ h0Ψ) Θ hΨinv0 with hΘ'
  have hΘ'0 : Θ'.toFun 0 = 0 := by
    show Θ.toFun (Ψ.invFun 0) = 0
    rw [hΨinv0, hΘ0]
  set C₀ : Set (ComplexModel n) := {u | e.symm (Ψ.invFun u) ∈ C} with hC₀
  have hsrc : ∀ u ∈ Θ'.source, u ∈ Ψ.target ∧ Ψ.invFun u ∈ Θ.source := fun u hu => hu
  refine le_of_flattening_model hkCn Θ' hΘ'0 (C := C₀) (fun u hu => ?_) (fun u hu huC => ?_)
  · obtain ⟨hut, huΘ⟩ := hsrc u hu
    have hey : e.symm (Ψ.invFun u) ∈ e.source := e.map_target (hΘt huΘ)
    have heey : e (e.symm (Ψ.invFun u)) = Ψ.invFun u := e.right_inv (hΘt huΘ)
    have := hΘC (y := e.symm (Ψ.invFun u)) hey (by rw [heey]; exact huΘ)
    rw [heey] at this
    exact this
  · obtain ⟨hut, huΘ⟩ := hsrc u hu
    have hey : e.symm (Ψ.invFun u) ∈ e.source := e.map_target (hΘt huΘ)
    have heey : e (e.symm (Ψ.invFun u)) = Ψ.invFun u := e.right_inv (hΘt huΘ)
    have hΨsrc : Ψ.invFun u ∈ Ψ.source := Ψ.mapsTo_invFun hut
    have := (hΨN (y := e.symm (Ψ.invFun u)) hey (by rw [heey]; exact hΨsrc)).mp (hCN huC)
    rwa [heey, Ψ.right_inv u hut] at this

end Dimension

/-! ### The geometric strict transform -/

/-- **The (geometric) strict transform** `closure (π⁻¹ (N \ C))` of `N` under `π`. -/
def geoStrictTransform {X Y : Type*} [TopologicalSpace Y] (π : Y → X) (C N : Set X) : Set Y :=
  closure (π ⁻¹' (N \ C))

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- The strict transform of a closed set lies over it. -/
theorem geoStrictTransform_subset_preimage {N : Set X} (hπ : Continuous π) (hN : IsClosed N) :
    geoStrictTransform π C N ⊆ π ⁻¹' N :=
  closure_minimal (fun _ hu => hu.1) (hN.preimage hπ)

/-- **Away from the centre the strict transform is the preimage.** -/
theorem mem_geoStrictTransform_iff_of_notMem {N : Set X} (hπ : Continuous π) (hN : IsClosed N)
    {u : Y} (hu : π u ∉ C) : u ∈ geoStrictTransform π C N ↔ π u ∈ N :=
  ⟨fun h => geoStrictTransform_subset_preimage hπ hN h, fun h => subset_closure ⟨h, hu⟩⟩

/-- **Regularity of the strict transform off the centre**: there `π` is a local biholomorphism
and the strict transform is the preimage. -/
theorem regularAtDim_geoStrictTransform_of_notMem (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosed N) {z : Y} (hz : π z ∉ C) {k : ℕ} (hNz : RegularAtDim (n := n) N (π z) k) :
    RegularAtDim (n := n) (geoStrictTransform π C N) z k := by
  have hzE : z ∉ exceptionalLocus n π := fun h =>
    hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  refine RegularAtDimTransport.regularAtDim_of_preimage hπ.contMDiff hzE
    (hπ.1.1.preimage hπ.contMDiff.continuous).isOpen_compl hz (fun u hu => ?_) hNz
  exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN hu

/-- **The strict transform in a monomial chart.**  At a point `z` over the flat domain of
nested coordinates `Φ` (`C = ℂ^{k_C} × 0`, `N = ℂ^{k_N} × 0`) there is a monomial chart `j ≥ k_C`
with local inverse `W` on an open `O ∋ z`, in which `u ∈ N' ⟺ j < k_N ∧ W u ∈ ℂ^{k_N} × 0`. -/
theorem exists_local_geoStrictTransform (hπ : IsBlowupAlong n C π) {N : Set X}
    {y₀ : X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}
    {kC kN : ℕ}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n kC))
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n kN))
    {z : Y} (hz : π z ∈ flatDomain Φ) :
    ∃ j : Fin n, kC ≤ j.1 ∧ ∃ O : Set Y, IsOpen O ∧ z ∈ O ∧ ∃ W : Y → ComplexModel n,
      (∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') ∧
      (∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j) ∧
      (∀ ℓ : LiftedOpen.{u} (monomialDomain Φ kC j) → Y,
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ →
          π ∘ ℓ = monomialChart Φ kC j → ∀ z' ∈ O, ∀ hw : W z' ∈ monomialDomain Φ kC j,
            ℓ (LiftedOpen.mk _ (W z') hw) = z') ∧
      ∀ u ∈ O, (u ∈ geoStrictTransform π C N ↔
        (j.1 < kN ∧ W u ∈ complexCoordinatePlane n kN)) := by
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflatC hz
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  -- membership of `π u` in `C` and `N` read through `W`
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  have hNu : ∀ u ∈ O, (π u ∈ N ↔ monomial kC j (W u) ∈ complexCoordinatePlane n kN) :=
    fun u hu => by rw [hflatN (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2]
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflatC hj
  refine ⟨j, hj, O, hO, hzO, W, hWs, hWmem, hℓ, fun u hu => ?_⟩
  by_cases hjN : j.1 < kN
  · simp only [hjN, true_and]
    constructor
    · -- the closure lies in the closed set `W ∈ ℂ^{k_N} × 0`, near `u`
      intro hcl
      by_contra hWu
      have hWc : ContinuousAt W u := (hWs u hu).continuousAt
      have hopen : IsOpen (complexCoordinatePlane n kN)ᶜ := by
        have : IsClosed (complexCoordinatePlane n kN) := by
          have : complexCoordinatePlane n kN = ⋂ i : Fin n, ⋂ (_ : kN ≤ i.1), {w | w i = 0} := by
            ext w; simp [complexCoordinatePlane]
          rw [this]
          exact isClosed_iInter fun i => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply i |>.comp (PiLp.continuous_ofLp 2 _)) continuous_const
        exact this.isOpen_compl
      have hev : ∀ᶠ u' in 𝓝 u, u' ∈ O ∧ W u' ∉ complexCoordinatePlane n kN :=
        (hO.eventually_mem hu).and (hWc.eventually_mem (hopen.mem_nhds hWu))
      obtain ⟨u', hu'mem, hu'A⟩ := mem_closure_iff_nhds.mp hcl _ hev
      obtain ⟨hu'O, hu'W⟩ := hu'mem
      obtain ⟨hNu', hCu'⟩ := hu'A
      have h1 := (hNu u' hu'O).mp hNu'
      rcases (monomial_mem_plane_iff_of_lt hj hjN).mp h1 with h0 | hP
      · exact hCu' ((hCu u' hu'O).mpr h0)
      · exact hu'W hP
    · -- points `ℓ (W u + t e_j)`, `t ≠ 0` small, lie in `π⁻¹ (N \ C)`
      intro hWu
      by_cases hWj : W u j = 0
      · rw [geoStrictTransform, mem_closure_iff_nhds]
        intro U hU
        have hp : W u ∈ monomialDomain Φ kC j := hWmem u hu
        set p : LiftedOpen.{u} (monomialDomain Φ kC j) := LiftedOpen.mk _ (W u) hp with hpdef
        have hℓp : ℓ p = u := hℓ ℓ hℓs hℓπ u hu hp
        have hpre : ℓ ⁻¹' U ∈ 𝓝 p := hℓs.continuous.continuousAt.preimage_mem_nhds (by
          rw [hℓp]; exact hU)
        have himg : LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∈ 𝓝 (W u) := by
          have := (LiftedOpen.isOpenEmbedding_toModel (S := monomialDomain Φ kC j)).map_nhds_eq p
          rw [← LiftedOpen.toModel_mk (S := monomialDomain Φ kC j) (W u) hp, ← this]
          exact image_mem_map hpre
        set e_j : ComplexModel n := EuclideanSpace.single j 1 with he_j
        have hcurve : Tendsto (fun t : ℂ => W u + t • e_j) (𝓝 0) (𝓝 (W u)) := by
          have : Continuous (fun t : ℂ => W u + t • e_j) := continuous_const.add
            (continuous_id.smul continuous_const)
          simpa using this.tendsto 0
        have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), W u + t • e_j ∈ LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∧
            t ≠ 0 :=
          (show ∀ᶠ t in 𝓝[≠] (0 : ℂ), W u + t • e_j ∈ LiftedOpen.toModel _ '' (ℓ ⁻¹' U) from
            mem_nhdsWithin_of_mem_nhds (hcurve himg)).and self_mem_nhdsWithin
        obtain ⟨t, ⟨q, hqU, hqt⟩, ht0⟩ := hev.exists
        refine ⟨ℓ q, hqU, ?_⟩
        have hπq : π (ℓ q) = monomialChart Φ kC j q := congrFun hℓπ q
        have hqmem : LiftedOpen.toModel _ q ∈ monomialDomain Φ kC j := LiftedOpen.toModel_mem _ q
        have hmon : monomial kC j (LiftedOpen.toModel _ q) ∈ Φ.target := hqmem
        -- `π (ℓ q)` lies in the flattening domain, with coordinates `σ_j (W u + t e_j)`
        have hsrc : π (ℓ q) ∈ flatDomain Φ := by
          rw [hπq]; exact monomialChart_mem_flatDomain hΦsrc q
        have hcoord : Φ.toFun (chartAt (ComplexModel n) y₀ (π (ℓ q))) =
            monomial kC j (LiftedOpen.toModel _ q) := by
          rw [hπq, monomialChart, (chartAt (ComplexModel n) y₀).right_inv (hΦsrc
            (Φ.mapsTo_invFun hmon)), Φ.right_inv _ hmon]
        have hwq : LiftedOpen.toModel _ q = W u + t • e_j := hqt
        have hwqj : LiftedOpen.toModel _ q j = t := by
          rw [hwq]; simp [he_j, hWj]
        have hwqP : LiftedOpen.toModel _ q ∈ complexCoordinatePlane n kN := by
          rw [hwq]
          intro i hi
          have hij : i ≠ j := fun h => by rw [h] at hi; omega
          simp [he_j, hWu i hi, hij]
        refine ⟨?_, ?_⟩
        · rw [hflatN hsrc.1 hsrc.2, hcoord, monomial_mem_plane_iff_of_lt hj hjN]
          exact Or.inr hwqP
        · rw [hflatC hsrc.1 hsrc.2, hcoord, monomial_mem_plane_iff hj, hwqj]
          exact ht0
      · exact subset_closure ⟨(hNu u hu).mpr ((monomial_mem_plane_iff_of_lt hj hjN).mpr
          (Or.inr hWu)), fun hC' => hWj ((hCu u hu).mp hC')⟩
  · -- `j ≥ k_N`: over `O`, `π⁻¹ N ⊆ π⁻¹ C`, so the strict transform misses `O`
    simp only [hjN, false_and, iff_false]
    intro hcl
    obtain ⟨u', hu'O, hu'A⟩ := mem_closure_iff_nhds.mp hcl O (hO.mem_nhds hu)
    obtain ⟨hNu', hCu'⟩ := hu'A
    exact hCu' ((hCu u' hu'O).mpr
      (eq_zero_of_monomial_mem_plane (not_lt.mp hjN) ((hNu u' hu'O).mp hNu')))

/-- `w - c ∈ ℂ^{k} × 0 ⟺ w ∈ ℂ^{k} × 0` for `c ∈ ℂ^{k} × 0`. -/
theorem sub_mem_plane_iff {k : ℕ} {w c : ComplexModel n} (hc : c ∈ complexCoordinatePlane n k) :
    w - c ∈ complexCoordinatePlane n k ↔ w ∈ complexCoordinatePlane n k := by
  constructor
  · intro h i hi
    have := h i hi
    rw [PiLp.sub_apply, hc i hi, sub_zero] at this
    exact this
  · intro h i hi
    rw [PiLp.sub_apply, h i hi, hc i hi, sub_zero]

/-- **Regularity of the strict transform over the centre**: at a point `z` of `N'` with
`π z ∈ C`, where `C ⊆ N` are regular of dimensions `k_C ≤ k_N`, the strict transform is regular
of dimension `k_N`; the local inverse `W` of the monomial chart, recentred, flattens it. -/
theorem regularAtDim_geoStrictTransform_of_mem (hπ : IsBlowupAlong n C π) {N : Set X}
    {z : Y} {kC kN : ℕ} (hk : kC ≤ kN) (hCz : RegularAtDim (n := n) C (π z) kC)
    (hNz : RegularAtDim (n := n) N (π z) kN) (hCN : C ⊆ N)
    (hz : z ∈ geoStrictTransform π C N) :
    RegularAtDim (n := n) (geoStrictTransform π C N) z kN := by
  obtain ⟨Φ, hΦt, hΦ0, hflat⟩ := exists_nested_flattening hk hCz hNz hCN
  have hz' : π z ∈ flatDomain Φ :=
    ⟨mem_chart_source _ (π z), by
      show chartAt (ComplexModel n) (π z) (π z) ∈ Φ.source
      exact Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kN) :=
    fun hy hyΦ => (hflat hy hyΦ).2
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWmem, hℓ, hiff⟩ :=
    exists_local_geoStrictTransform hπ hΦt hflatC hflatN hz'
  obtain ⟨hjN, hWz⟩ := (hiff z hzO).mp hz
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦt hflatC hj
  -- the chart reading `F = W ∘ e_z⁻¹` of the local inverse
  set ez := chartAt (ComplexModel n) z with hez
  set F : ComplexModel n → ComplexModel n := fun ζ => W (ez.symm ζ) with hF
  set Nset : Set (ComplexModel n) := ez.target ∩ ez.symm ⁻¹' O with hNset
  have hNo : IsOpen Nset := ez.continuousOn_symm.isOpen_inter_preimage ez.open_target hO
  have hzN : ez z ∈ Nset :=
    ⟨ez.map_source (mem_chart_source _ z), by
      show ez.symm (ez z) ∈ O
      rw [ez.left_inv (mem_chart_source _ z)]; exact hzO⟩
  have hFd : DifferentiableOn ℂ F Nset := by
    intro ζ hζ
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) z) hζ.1
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W (ez.symm ζ) :=
      (hWs _ hζ.2).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)).differentiableWithinAt
  have hFinj : Function.Injective (fderiv ℂ F (ez z)) := by
    have hdiff : DifferentiableAt ℂ F (ez z) := (hFd _ hzN).differentiableAt (hNo.mem_nhds hzN)
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    by_contra hv0
    apply fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hzO hv0
    rw [hdiff.fderiv_restrictScalars ℝ]
    exact hv
  obtain ⟨Θ, hΘN, hΘF, -⟩ := Hironaka.exists_localHolomorphicEquivAt hNo hzN hFd hFinj
  refine ⟨hNz.1, hz, subConst Θ (W z), fun ζ hζ => (hΘN hζ).1, ?_, ?_⟩
  · show Θ.toFun (ez z) - W z = 0
    rw [hΘF]
    show W (ez.symm (ez z)) - W z = 0
    rw [ez.left_inv (mem_chart_source _ z), sub_self]
  intro y hy hyΦ
  have hyO : y ∈ O := by
    have h : ez.symm (ez y) ∈ O := (hΘN hyΦ).2
    rwa [ez.left_inv hy] at h
  show y ∈ geoStrictTransform π C N ↔ Θ.toFun (ez y) - W z ∈ complexCoordinatePlane n kN
  rw [hΘF]
  show y ∈ geoStrictTransform π C N ↔ W (ez.symm (ez y)) - W z ∈ complexCoordinatePlane n kN
  rw [ez.left_inv hy, sub_mem_plane_iff hWz, hiff y hyO]
  exact ⟨fun h => h.2, fun h => ⟨hjN, h⟩⟩

end Blowup

end

end Hironaka.BlowupStrictSubmanifold
