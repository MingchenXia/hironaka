/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.LiftedOpenModel
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Exceptional points of a blowup and the codimension of the centre

Let `π : Z → M` be a blowup along `C` (`IsBlowupAlong`), and let `C` be flattened near `y₀`
onto `ℂᵏ × 0` by `Φ ∘ e`.  For `z` with `π z` in the flattening domain, the local inverse `W`
of a monomial lift (`BlowupLocalSurjectivity.exists_monomialLocalInverse`) satisfies
`σⱼ ∘ W = Φ ∘ e ∘ π` near `z` for some `j ≥ k`.

* `lt_of_mem_flatDomain`: `k < n` as soon as some point of `Z` lies over the flattening domain.
* `mem_exceptionalLocus_of_mem` (codimension `≥ 2`): if `π z ∈ C`, then `z` is exceptional.
  Indeed `W(z)ⱼ = 0`, so `σⱼ` is constant along the line through `W z` in a direction
  `e_l` (`l ≥ k`, `l ≠ j`); hence `dσⱼ(W z)` is not injective.  Writing
  `π = e⁻¹ ∘ Φ⁻¹ ∘ σⱼ ∘ W` near `z`, surjectivity of `dπ_z` would force `dσⱼ(W z)` to be
  surjective, hence injective.
* `not_mem_exceptionalLocus` (codimension `1`): `σⱼ = id`, so `y ↦ ℓⱼ (Φ (e y))` is a
  holomorphic section of `π` near `π z` through `z`, and `dπ_z` is surjective, hence bijective.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ExceptionalImageCodimension

open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity

noncomputable section

variable {n : ℕ}

/-- If `w j = 0`, the monomial map `σⱼ` is constant along the line through `w` in the
direction of a basis vector `e_l` with `l ≥ k`, `l ≠ j`. -/
theorem monomial_add_smul_single {k : ℕ} {j l : Fin n} (hl : k ≤ l.1) (hlj : l ≠ j)
    {w : ComplexModel n} (hw : w j = 0) (t : ℂ) :
    monomial k j (w + t • EuclideanSpace.single l (1 : ℂ)) = monomial k j w := by
  ext i
  simp only [monomial_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hw,
    smul_eq_mul]
  by_cases hi : k ≤ i.1 ∧ i ≠ j
  · simp [hi, hlj.symm]
  · have hil : i ≠ l := fun h => hi ⟨h ▸ hl, h ▸ hlj⟩
    simp [hi, hil]

/-- The derivative of `σⱼ` at a point with `w j = 0` kills `e_l` for `l ≥ k`, `l ≠ j`. -/
theorem fderiv_monomial_single_eq_zero {k : ℕ} {j l : Fin n} (hl : k ≤ l.1) (hlj : l ≠ j)
    {w : ComplexModel n} (hw : w j = 0) :
    fderiv ℂ (monomial k j) w (EuclideanSpace.single l (1 : ℂ)) = 0 := by
  have hd : HasFDerivAt (monomial k j) (fderiv ℂ (monomial k j) w) w :=
    ((contDiff_monomial k j).differentiable (by simp) w).hasFDerivAt
  have hline : HasDerivAt (fun t : ℂ => w + t • EuclideanSpace.single l (1 : ℂ))
      (EuclideanSpace.single l (1 : ℂ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const
      (EuclideanSpace.single l (1 : ℂ))).const_add w
  have h1 := hd.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have hconst : (monomial k j ∘ fun t : ℂ => w + t • EuclideanSpace.single l (1 : ℂ)) =
      fun _ => monomial k j w := funext fun t => monomial_add_smul_single hl hlj hw t
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const _ _)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M} {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- A flattening dimension realised over a point of the blowup is `< n`. -/
theorem lt_of_mem_flatDomain (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {z : Z} (hz : π z ∈ flatDomain Φ) : k < n := by
  obtain ⟨j, hj, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflat hz
  exact lt_of_le_of_lt hj j.2

/-- **Codimension at least two**: every point over the centre is exceptional. -/
theorem mem_exceptionalLocus_of_mem (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (hk : k + 2 ≤ n) {z : Z} (hzC : π z ∈ C) (hz : π z ∈ flatDomain Φ) :
    z ∈ exceptionalLocus n π := by
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, -, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflat hz
  have hplane : Φ.toFun (chartAt (ComplexModel n) y₀ (π z)) ∈ complexCoordinatePlane n k :=
    (hflat hz.1 hz.2).mp hzC
  have hWj : W z j = 0 := by
    have := congrArg (fun u : ComplexModel n => u j) (hWeq z hzO).2
    simp only [monomial_apply, ne_eq, not_true_eq_false, and_false, if_false] at this
    rw [this]
    exact hplane j hj
  obtain ⟨l, hl, hlj⟩ : ∃ l : Fin n, k ≤ l.1 ∧ l ≠ j := by
    by_cases hjk : j.1 = k
    · exact ⟨⟨k + 1, by omega⟩, by simp, fun h => by
        have := congrArg Fin.val h
        simp at this
        omega⟩
    · exact ⟨⟨k, by omega⟩, le_rfl, fun h => hjk (congrArg Fin.val h).symm⟩
  set f₁ : ComplexModel n → M := fun u => (chartAt (ComplexModel n) y₀).symm (Φ.invFun u)
    with hf₁_def
  have heq : π =ᶠ[𝓝 z] f₁ ∘ (monomial k j ∘ W) := by
    filter_upwards [hO.mem_nhds hzO] with z' hz'
    simp only [Function.comp_apply, hf₁_def, (hWeq z' hz').2]
    exact (flatInverse_flat Φ (hWeq z' hz').1).symm
  have hu : monomial k j (W z) ∈ Φ.target := by
    rw [(hWeq z hzO).2]
    exact Φ.mapsTo_toFun hz.2
  have hf₁ : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f₁
      (monomial k j (W z)) :=
    (mdifferentiableAt_chart_symm (hΦsrc (Φ.mapsTo_invFun hu))).comp _
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hu)).mdifferentiableAt
  have hσ : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (monomial k j) (W z) :=
    ((contDiff_monomial k j).differentiable (by simp) _).mdifferentiableAt
  have hW : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W z :=
    (hWs z hzO).mdifferentiableAt (by simp)
  have hchain : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z =
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f₁ (monomial k j (W z))).comp
        ((fderiv ℂ (monomial k j) (W z)).comp
          (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W z)) := by
    rw [heq.mfderiv_eq, mfderiv_comp z hf₁ (hσ.comp z hW), mfderiv_comp z hσ hW,
      mfderiv_eq_fderiv]
    rfl
  set A : ComplexModel n →L[ℂ] ComplexModel n :=
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f₁ (monomial k j (W z)) with hA
  set B : ComplexModel n →L[ℂ] ComplexModel n := fderiv ℂ (monomial k j) (W z) with hB
  set D : ComplexModel n →L[ℂ] ComplexModel n :=
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W z with hD
  show ¬ Function.Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z)
  intro hbij
  have hsurj : ∀ v, ∃ u, A (B (D u)) = v := fun v => by
    obtain ⟨u, hu⟩ := hbij.2 v
    exact ⟨u, by rw [hchain] at hu; exact hu⟩
  have hAs : Function.Surjective A.toLinearMap := fun v => by
    obtain ⟨u, hu⟩ := hsurj v
    exact ⟨B (D u), hu⟩
  have hAi : Function.Injective A.toLinearMap := LinearMap.injective_iff_surjective.mpr hAs
  have hBs : Function.Surjective B.toLinearMap := fun v => by
    obtain ⟨u, hu⟩ := hsurj (A v)
    exact ⟨D u, hAi hu⟩
  have hBi : Function.Injective B.toLinearMap := LinearMap.injective_iff_surjective.mpr hBs
  have h0 : B (EuclideanSpace.single l (1 : ℂ)) = B 0 := by
    rw [map_zero]
    exact fderiv_monomial_single_eq_zero hl hlj hWj
  have := hBi h0
  have h1 := congrArg (fun u : ComplexModel n => u l) this
  simp at h1

/-- **Codimension one**: no point over the flattening domain is exceptional. -/
theorem not_mem_exceptionalLocus (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (hk : k + 1 = n) {z : Z} (hz : π z ∈ flatDomain Φ) :
    z ∉ exceptionalLocus n π := by
  obtain ⟨j, hj, O, -, hzO, W, -, hWeq, hℓW, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflat hz
  have hσ : ∀ w, monomial k j w = w := by
    intro w
    ext i
    simp only [monomial_apply]
    rw [if_neg]
    rintro ⟨hi, hij⟩
    exact hij (Fin.ext (by omega))
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hdom : ∀ y ∈ flatDomain Φ,
      Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ monomialDomain Φ k j := fun y hy => by
    show monomial k j _ ∈ Φ.target
    rw [hσ]
    exact Φ.mapsTo_toFun hy.2
  have hwz : W z ∈ monomialDomain Φ k j := by
    show monomial k j (W z) ∈ Φ.target
    rw [(hWeq z hzO).2]
    exact Φ.mapsTo_toFun hz.2
  classical
  set s' : M → LiftedOpen.{u} (monomialDomain Φ k j) := fun y =>
    if h : Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ monomialDomain Φ k j then
      LiftedOpen.mk _ _ h else LiftedOpen.mk _ _ hwz with hs'_def
  have hWz : W z = Φ.toFun (chartAt (ComplexModel n) y₀ (π z)) := by
    rw [← (hWeq z hzO).2, hσ]
  have hsz : ℓ (s' (π z)) = z := by
    have h := hℓW ℓ hℓs hℓπ z hzO hwz
    simp only [hs'_def, dif_pos (hdom _ hz)]
    convert h using 2
    simp only [LiftedOpen.mk, hWz]
  have hπs : π ∘ (ℓ ∘ s') =ᶠ[𝓝 (π z)] id := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hz] with y hy
    have h := congrFun hℓπ (s' y)
    simp only [Function.comp_apply] at h ⊢
    rw [h]
    simp only [hs'_def, dif_pos (hdom y hy), monomialChart, LiftedOpen.toModel_mk, hσ, id]
    exact flatInverse_flat Φ hy
  have hflatsmooth : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y => Φ.toFun (chartAt (ComplexModel n) y₀ y)) (π z) := by
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ.toFun
        (chartAt (ComplexModel n) y₀ (π z)) :=
      (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
        hz.2).contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (chartAt (ComplexModel n) y₀) (π z) :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt
        ((chartAt (ComplexModel n) y₀).open_source.mem_nhds hz.1)
    exact h1.comp (π z) h2
  have hs' : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s' (π z) := by
    refine LiftedOpen.contMDiffAt_of_toModel _ (hflatsmooth.congr_of_eventuallyEq ?_)
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hz] with y hy
    simp only [hs'_def, Function.comp_apply, dif_pos (hdom y hy), LiftedOpen.toModel_mk]
  have hsd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (ℓ ∘ s') (π z) :=
    ((hℓs (s' (π z))).comp (π z) hs').mdifferentiableAt (by simp)
  have hπd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π ((ℓ ∘ s') (π z)) :=
    (hπ.contMDiff _).mdifferentiableAt (by simp)
  have h1 := mfderiv_comp (π z) hπd hsd
  rw [hπs.mfderiv_eq, mfderiv_id] at h1
  have hsurj' : Function.Surjective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π ((ℓ ∘ s') (π z))) := fun v =>
    ⟨mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (ℓ ∘ s') (π z) v,
      (DFunLike.congr_fun h1 v).symm⟩
  have hsz' : (ℓ ∘ s') (π z) = z := hsz
  rw [hsz'] at hsurj'
  intro hexc
  apply hexc
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z) := hsurj'
  set L : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (show ComplexModel n →L[ℂ] ComplexModel n from
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z).toLinearMap
  have hinj : Function.Injective L :=
    LinearMap.injective_iff_surjective (V := ComplexModel n) (f := L) |>.mpr hsurj
  exact ⟨hinj, hsurj⟩

end

end Hironaka.ExceptionalImageCodimension
