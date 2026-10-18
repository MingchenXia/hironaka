/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticSubsetPresentationsExact
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.ImageDimensionBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The dimension of an image

Blueprint `rem:analytic-image-dimension` (Demailly, *Complex analytic and differential geometry*,
II.8.6; step M8 of the route to Remmert's proper mapping theorem, `blueprint/src/remmert.tex`).

Let `G : X → Y` be holomorphic, `T ⊆ X` analytic with `dim T ≤ a`, and suppose every fibre
`T ∩ G⁻¹(G x)` (`x ∈ T`) has local dimension `≥ b` at `x`.  Then every regular point of `G(T)` has
a dimension `d` with `d + b ≤ a` (`add_le_of_regularAtDim_image`), so `dim G(T) ≤ a - b`
(`dimLE_image`); if moreover `G(T)` is analytic and `b > a`, then `T = ∅` (`eq_empty_of_lt`).

Proof: at a regular point `y` of `G(T)` of dimension `d`, the flattening `Φ ∘ e` of `G(T)` followed
by the first `d` coordinates is a holomorphic `φ` on the open set `N₀ = e.source ∩ e⁻¹(Φ.source)`,
injective on `G(T) ∩ N₀` with open image.  On the open submanifold `U = G⁻¹(N₀)` of `X`
(`AnalyticSubsetOpens`) apply the image dimension bound (`ImageDimensionBound`) to `T ∩ U` and
`g = φ ∘ G`: its fibres on `T ∩ U` are those of `G`, and `g(T ∩ U)` is open.

Sorry-free.
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.AnalyticImageDimension

open Hironaka.RegularLocusDense AnalyticDimensionBasics AnalyticSubsetOpens
  ImageDimensionBound

/-! ### The first `d` coordinates of `ℂ^m` -/

/-- The first `d` coordinates. -/
def headCLM {d m : ℕ} (hdm : d ≤ m) : ComplexModel m →L[ℂ] ComplexModel d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => v (Fin.castLE hdm i))
      map_add' := fun v w => by ext i; simp
      map_smul' := fun c v => by ext i; simp }

@[simp] theorem headCLM_apply {d m : ℕ} (hdm : d ≤ m) (v : ComplexModel m) (i : Fin d) :
    headCLM hdm v i = v (Fin.castLE hdm i) := rfl

/-- `ℂ^d` as the coordinate plane `ℂ^d × 0` of `ℂ^m`. -/
def inclCLM {d m : ℕ} : ComplexModel d →L[ℂ] ComplexModel m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun j : Fin m => if h : j.1 < d then w ⟨j.1, h⟩ else 0)
      map_add' := fun v w => by
        ext j
        by_cases h : j.1 < d <;> simp [h]
      map_smul' := fun c v => by
        ext j
        by_cases h : j.1 < d <;> simp [h] }

theorem inclCLM_apply {d m : ℕ} (w : ComplexModel d) (j : Fin m) :
    (inclCLM w : ComplexModel m) j = if h : j.1 < d then w ⟨j.1, h⟩ else 0 := rfl

theorem inclCLM_mem_plane {d m : ℕ} (w : ComplexModel d) :
    (inclCLM w : ComplexModel m) ∈ complexCoordinatePlane m d := by
  intro j hj
  rw [inclCLM_apply, dif_neg (not_lt.mpr hj)]

theorem headCLM_inclCLM {d m : ℕ} (hdm : d ≤ m) (w : ComplexModel d) :
    headCLM hdm (inclCLM w : ComplexModel m) = w := by
  ext i
  rw [headCLM_apply, inclCLM_apply, dif_pos (by simp)]
  rfl

theorem inclCLM_headCLM {d m : ℕ} (hdm : d ≤ m) {v : ComplexModel m}
    (hv : v ∈ complexCoordinatePlane m d) : (inclCLM (headCLM hdm v) : ComplexModel m) = v := by
  ext j
  rw [inclCLM_apply]
  by_cases h : j.1 < d
  · rw [dif_pos h, headCLM_apply]
    rfl
  · rw [dif_neg h, hv j (not_lt.mp h)]

/-! ### The bound -/

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

/-- **The dimension of an image** (`rem:analytic-image-dimension`, `demailly-cadg:II.8.6`).  If
`T` is analytic with `dim T ≤ a` and every fibre of `G` on `T` has local dimension `≥ b`, then every
regular point of `G(T)` has a dimension `d` with `d + b ≤ a`. -/
theorem add_le_of_regularAtDim_image {G : X → Y}
    (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ G) {T : Set X} {a b : ℕ}
    (hT : IsComplexAnalyticSubset (n := n) T) (hdim : DimLE (n := n) T a)
    (hfib : ∀ x ∈ T, LocDimGE (n := n) (T ∩ G ⁻¹' {G x}) x b) {y : Y} {d : ℕ}
    (hy : RegularAtDim (n := m) (G '' T) y d) : d + b ≤ a := by
  obtain ⟨hdm, -, Φ, hΦt, hΦ0, hΦA⟩ := hy
  set e := chartAt (ComplexModel m) y with he
  -- the flat coordinates `φ` on `N₀`
  set N₀ : Set Y := e.source ∩ e ⁻¹' Φ.source with hN₀
  have hN₀o : IsOpen N₀ := e.isOpen_inter_preimage Φ.isOpen_source
  set φ : Y → ComplexModel d := fun z => headCLM hdm (Φ.toFun (e z)) with hφ
  set U : Opens X := ⟨G ⁻¹' N₀, hG.continuous.isOpen_preimage _ hN₀o⟩ with hU
  set g : U → ComplexModel d := fun x => φ (G x) with hg
  -- `g` is holomorphic on the open submanifold `U`
  have hφs : ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ φ N₀ := by
    intro z hz
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ Φ.toFun (e z) :=
      (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
        hz.2).contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ e z :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt (e.open_source.mem_nhds hz.1)
    exact ((headCLM hdm).contDiff.contMDiff.contMDiffAt.comp z (h1.comp z h2)).contMDiffWithinAt
  have hgs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel d) ∞ g :=
    contMDiff_restrict (U := U) (hφs.comp hG.contMDiffOn fun x hx => hx)
  -- `φ` is injective on `G(T) ∩ N₀`
  have hplane : ∀ z ∈ N₀, z ∈ G '' T → Φ.toFun (e z) ∈ complexCoordinatePlane m d :=
    fun z hz hzT => (hΦA hz.1 hz.2).mp hzT
  have hinj : ∀ z ∈ N₀, z ∈ G '' T → ∀ z' ∈ N₀, z' ∈ G '' T → φ z = φ z' → z = z' := by
    intro z hz hzT z' hz' hzT' hφzz
    have h1 : Φ.toFun (e z) = Φ.toFun (e z') := by
      rw [← inclCLM_headCLM hdm (hplane z hz hzT), ← inclCLM_headCLM hdm (hplane z' hz' hzT')]
      exact congrArg _ hφzz
    have h2 : e z = e z' := by
      rw [← Φ.left_inv _ hz.2, ← Φ.left_inv _ hz'.2, h1]
    exact e.injOn hz.1 hz'.1 h2
  -- the data on `U`
  set T' : Set U := (↑) ⁻¹' T with hT'
  have hT'a : IsComplexAnalyticSubset (n := n) T' := isComplexAnalyticSubset_preimage_val hT U
  have hT'd : DimLE (n := n) T' a := dimLE_preimage_val hdim U
  -- `g(T')` contains a nonempty open set
  have hO : ∃ O : Set (ComplexModel d), IsOpen O ∧ O.Nonempty ∧ O ⊆ g '' T' := by
    refine ⟨inclCLM ⁻¹' Φ.target, Φ.isOpen_target.preimage inclCLM.continuous,
      ⟨0, ?_⟩, ?_⟩
    · rw [mem_preimage, map_zero, ← hΦ0]
      exact Φ.mapsTo_toFun Φ.center_mem_source
    · intro w hw
      set v : ComplexModel m := inclCLM w with hv
      have hvs : Φ.invFun v ∈ Φ.source := Φ.mapsTo_invFun hw
      have hvt : Φ.invFun v ∈ e.target := hΦt hvs
      set z := e.symm (Φ.invFun v) with hz
      have hzs : z ∈ e.source := e.map_target hvt
      have hez : e z = Φ.invFun v := e.right_inv hvt
      have hzN : z ∈ N₀ := ⟨hzs, by rw [mem_preimage, hez]; exact hvs⟩
      have hΦz : Φ.toFun (e z) = v := by rw [hez]; exact Φ.right_inv _ hw
      have hzT : z ∈ G '' T := (hΦA hzs hzN.2).mpr (by
        change Φ.toFun (e z) ∈ _
        rw [hΦz]; exact inclCLM_mem_plane w)
      obtain ⟨x, hxT, hxz⟩ := hzT
      have hxU : x ∈ U := by
        change G x ∈ N₀
        rw [hxz]; exact hzN
      refine ⟨⟨x, hxU⟩, hxT, ?_⟩
      change headCLM hdm (Φ.toFun (e (G x))) = w
      rw [hxz, hΦz, hv, headCLM_inclCLM]
  -- the fibres of `g` on `T'` are those of `G`
  have hfib' : ∀ x ∈ T', LocDimGE (n := n) (T' ∩ g ⁻¹' {g x}) x b := by
    intro x hx
    have hset : T' ∩ g ⁻¹' {g x} = (↑) ⁻¹' (T ∩ G ⁻¹' {G x}) := by
      ext x'
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨hx'T, hgx'⟩
        refine ⟨hx'T, hinj _ x'.2 ⟨x', hx'T, rfl⟩ _ x.2 ⟨x, hx, rfl⟩ hgx'⟩
      · rintro ⟨hx'T, hGx'⟩
        refine ⟨hx'T, ?_⟩
        change φ (G x') = φ (G x)
        rw [hGx']
    rw [hset]
    exact locDimGE_preimage_val_iff.mpr (hfib x hx)
  exact add_le_of_isOpen_subset_image d hT'a hT'd hgs hO hfib'

/-- `dim G(T) ≤ a - b`. -/
theorem dimLE_image {G : X → Y}
    (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ G) {T : Set X} {a b : ℕ}
    (hT : IsComplexAnalyticSubset (n := n) T) (hdim : DimLE (n := n) T a)
    (hfib : ∀ x ∈ T, LocDimGE (n := n) (T ∩ G ⁻¹' {G x}) x b) :
    DimLE (n := m) (G '' T) (a - b) := fun y d hy => by
  have := add_le_of_regularAtDim_image hG hT hdim hfib hy
  omega

/-- If `G(T)` is analytic and the fibres have local dimension `≥ b > a ≥ dim T`, then `T = ∅`. -/
theorem eq_empty_of_lt {G : X → Y}
    (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ G) {T : Set X} {a b : ℕ}
    (hT : IsComplexAnalyticSubset (n := n) T) (hdim : DimLE (n := n) T a)
    (hfib : ∀ x ∈ T, LocDimGE (n := n) (T ∩ G ⁻¹' {G x}) x b)
    (hGT : IsComplexAnalyticSubset (n := m) (G '' T)) (hab : a < b) : T = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨y, -, k, hy⟩ := exists_regularAtDim_mem_nhds hGT ⟨x, hx, rfl⟩ univ_mem
  have := add_le_of_regularAtDim_image hG hT hdim hfib hy
  omega

end Hironaka.AnalyticImageDimension
