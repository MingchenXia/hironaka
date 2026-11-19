import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlanchardForm

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A blowup is unramified over the points where the centre has codimension at most one

Let `π : Z → M` be the blowup along `C`, and let `Φ` flatten `C` onto `ℂᵏ × 0` near `y₀` with
`k + 1 ≥ n`.  Every `z` over the flattening domain lies off the exceptional locus: the only
index `j ≥ k` is `j = k = n - 1`, so for `v ∈ ker dπ_z` all components of the derivative `D v` of
the monomial local inverse vanish (`BlowupFibreDirection.fderiv_monomialInverse_apply_eq_zero`),
while `D v ≠ 0` for `v ≠ 0` (`BlowupFibreDirection.fderiv_monomialInverse_ne_zero`).

Conversely (`mem_exceptionalLocus_of_codim_ge_two`), over a point of the centre of codimension
`≥ 2` every point is exceptional: `D` is bijective, and for `i ≥ k`, `i ≠ j` the monomial map
`σⱼ` is constant along `W z + t eᵢ`, so `v = D⁻¹ eᵢ` is killed by `d(Φ ∘ e ∘ π) = dσⱼ ∘ D`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupCodimOne

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.HolomorphicMaps BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity
  BlowupFibreDirection BlanchardForm

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M} {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- **Over a codimension-`≤ 1` part of the centre a blowup is unramified.** -/
theorem notMem_exceptionalLocus_of_codim_le_one (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (hk : n ≤ k + 1) {z : Z} (hz : π z ∈ flatDomain Φ) :
    z ∉ exceptionalLocus n π := by
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflat hz
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j := fun z' hz' => by
    show monomial k j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  have hinj : Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z) := by
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    by_contra hv0
    apply fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hzO hv0
    ext i
    refine fderiv_monomialInverse_apply_eq_zero hπ hO hWs hWeq hzO hv i ?_
    rintro ⟨hki, hij⟩
    apply hij
    ext
    have := i.2; have := j.2
    omega
  simp only [exceptionalLocus, mem_ofPred_eq, not_not]
  set L : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (show ComplexModel n →L[ℂ] ComplexModel n from
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z).toLinearMap
  have hsurj : Function.Surjective L :=
    LinearMap.injective_iff_surjective (V := ComplexModel n) (f := L) |>.mp hinj
  exact ⟨hinj, hsurj⟩


/-- **Over a codimension-`≥ 2` part of the centre every point of a blowup is exceptional.** -/
theorem mem_exceptionalLocus_of_codim_ge_two (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (hk : k + 2 ≤ n) {z : Z} (hz : π z ∈ flatDomain Φ) (hzC : π z ∈ C) :
    z ∈ exceptionalLocus n π := by
  classical
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflat hz
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j := fun z' hz' => by
    show monomial k j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  have hw₀j : W z j = 0 := by
    have h1 := congrArg (fun w : ComplexModel n => w j) (hWeq z hzO).2
    simp only [monomial_apply, ne_eq, not_true_eq_false, and_false, if_false] at h1
    rw [h1]
    exact ((hflat hz.1 hz.2).mp hzC) j hj
  -- a normal index `i ≠ j`
  obtain ⟨i, hki, hij⟩ : ∃ i : Fin n, k ≤ i.1 ∧ i ≠ j := by
    by_cases hjk : j.1 = k
    · exact ⟨⟨k + 1, by omega⟩, by simp, fun h => by
        have := congrArg Fin.val h; simp at this; omega⟩
    · exact ⟨⟨k, by omega⟩, le_rfl, fun h => hjk (congrArg Fin.val h).symm⟩
  set ζ₀ := chartAt (ComplexModel n) z z
  set G := fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)
  set D := fderiv ℝ G ζ₀
  have hDinj : Function.Injective D := by
    refine (injective_iff_map_eq_zero D).mpr fun v hv => ?_
    by_contra hv0
    exact fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hzO hv0 hv
  have hDsurj : Function.Surjective D :=
    LinearMap.injective_iff_surjective (f := D.toLinearMap) |>.mp hDinj
  set ei : ComplexModel n := EuclideanSpace.single i 1
  obtain ⟨v, hv⟩ := hDsurj ei
  have hv0 : v ≠ 0 := by
    rintro rfl
    have := congrArg (fun w : ComplexModel n => w i) hv
    simp [ei] at this
  intro hbij
  apply hv0
  apply hbij.1
  refine Eq.trans ?_ (ContinuousLinearMap.map_zero _).symm
  -- `dπ v = 0`
  set e := complexChartAt (n := n) z
  set d : ComplexChart n M := ⟨chartAt (ComplexModel n) y₀, chart_mem_atlas _ y₀⟩
  have hζt : ζ₀ ∈ e.val.target := e.val.map_source (mem_complexChartAt_source z)
  have hsymm : e.val.symm ζ₀ = z := e.val.left_inv (mem_complexChartAt_source z)
  have hzd : ζ₀ ∈ coordinateDomain π e d :=
    ⟨hζt, by show π (e.val.symm ζ₀) ∈ d.val.source; rw [hsymm]; exact hz.1⟩
  have hzp : ζ₀ ∈ coordinateDomain π e (complexChartAt (n := n) (π z)) :=
    ⟨hζt, by
      show π (e.val.symm ζ₀) ∈ (complexChartAt (n := n) (π z)).val.source
      rw [hsymm]; exact mem_complexChartAt_source _⟩
  set T := coordinateMap π e d
  suffices hT : fderiv ℝ T ζ₀ v = 0 by
    rw [← fderiv_coordinateMap_eq_mfderiv hπ.contMDiff z v,
      coordinateMap_fderiv_change_target hπ.contMDiff e d _ hzd hzp,
      ContinuousLinearMap.comp_apply]
    change _ = (0 : ComplexModel n) at hT
    rw [hT, map_zero]
    rfl
  have hTd : DifferentiableAt ℝ T ζ₀ :=
    (coordinateMap_contDiffAt_real hπ.contMDiff e d hzd).differentiableAt (by simp)
  have hTmem : T ζ₀ ∈ Φ.source := by
    show chartAt (ComplexModel n) y₀ (π (e.val.symm ζ₀)) ∈ Φ.source
    rw [hsymm]; exact hz.2
  have hΦd : DifferentiableAt ℂ Φ.toFun (T ζ₀) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hTmem)
  have hΦt : Φ.toFun (T ζ₀) ∈ Φ.target := Φ.mapsTo_toFun hTmem
  have hinvd : DifferentiableAt ℂ Φ.invFun (Φ.toFun (T ζ₀)) :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hΦt)
  -- `dΦ` is injective
  have hΦinj : Function.Injective (fderiv ℝ Φ.toFun (T ζ₀)) := by
    have hid : (Φ.invFun ∘ Φ.toFun) =ᶠ[𝓝 (T ζ₀)] id := by
      filter_upwards [Φ.isOpen_source.mem_nhds hTmem] with w hw
      exact Φ.left_inv w hw
    have hc := (hinvd.restrictScalars ℝ).hasFDerivAt.comp (T ζ₀) (hΦd.restrictScalars ℝ).hasFDerivAt
    have hu := hc.unique ((hasFDerivAt_id (T ζ₀)).congr_of_eventuallyEq hid)
    intro a b hab
    have := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L a) hu
    have h2 := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L b) hu
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
    rw [← this, ← h2, hab]
  apply hΦinj
  rw [map_zero]
  -- `Φ ∘ T = σⱼ ∘ G` near `ζ₀`
  have hGev : (fun ζ => Φ.toFun (T ζ)) =ᶠ[𝓝 ζ₀] fun ζ => monomial k j (G ζ) := by
    have hcont : ContinuousAt e.val.symm ζ₀ := e.val.continuousAt_symm hζt
    rw [← hsymm] at hzO
    filter_upwards [hcont.eventually (hO.mem_nhds hzO)] with ζ hζ
    exact (hWeq _ hζ).2.symm
  have hGd : DifferentiableAt ℝ G ζ₀ := (differentiableAt_chart_comp (hWs z hzO)).restrictScalars ℝ
  have hσd : DifferentiableAt ℝ (monomial k j) (G ζ₀) :=
    ((contDiff_monomial k j).differentiable (by simp) _).restrictScalars ℝ
  have h1 : fderiv ℝ (fun ζ => Φ.toFun (T ζ)) ζ₀ v = fderiv ℝ Φ.toFun (T ζ₀) (fderiv ℝ T ζ₀ v) := by
    rw [fderiv_fun_comp ζ₀ (hΦd.restrictScalars ℝ) hTd]; rfl
  have h2 : fderiv ℝ (fun ζ => monomial k j (G ζ)) ζ₀ v = fderiv ℝ (monomial k j) (G ζ₀) ei := by
    rw [fderiv_fun_comp ζ₀ hσd hGd]; simp only [ContinuousLinearMap.comp_apply]; rw [← hv]
  rw [← h1, hGev.fderiv_eq, h2]
  -- `σⱼ` is constant along `W z + t eᵢ`
  have hGz : G ζ₀ = W z := by simp only [G, ζ₀]; rw [(chartAt (ComplexModel n) z).left_inv (mem_chart_source _ z)]
  have hline : ∀ t : ℝ, monomial k j (G ζ₀ + (t : ℂ) • ei) = monomial k j (G ζ₀) := fun t => by
    rw [hGz]
    exact monomial_line hw₀j (by simp [ei, hij.symm]) (fun l hl => by
      have : l ≠ i := fun h => by subst h; omega
      simp [ei, this]) t
  have hderiv : HasDerivAt (fun t : ℝ => monomial k j (G ζ₀ + (t : ℂ) • ei))
      (fderiv ℝ (monomial k j) (G ζ₀) ei) 0 := by
    have hl : HasDerivAt (fun t : ℝ => G ζ₀ + (t : ℂ) • ei) ei 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const ei).const_add (G ζ₀)
      simpa using this
    have hσd' : HasFDerivAt (monomial k j) (fderiv ℝ (monomial k j) (G ζ₀))
        (G ζ₀ + ((0 : ℝ) : ℂ) • ei) := by simpa using hσd.hasFDerivAt
    exact hσd'.comp_hasDerivAt (0 : ℝ) hl
  have hconst : HasDerivAt (fun t : ℝ => monomial k j (G ζ₀ + (t : ℂ) • ei)) 0 0 := by
    simp only [hline]; exact hasDerivAt_const _ _
  exact hderiv.unique hconst

end

end Hironaka.BlowupCodimOne
