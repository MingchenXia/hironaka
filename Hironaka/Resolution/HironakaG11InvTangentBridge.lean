import Hironaka.Resolution.HironakaG11InvMinimalWindow
import Hironaka.Resolution.HironakaHilbertSamuelTangentValue

/-!
# The coordinate tangent space is the tangent space of the vanishing ideal

Lane G11B (run 0080, round 2), G11 route step 4 (`ROUTE-r2.md` §4).  For an analytic local model `C ⊆ U ⊆ ℂⁿ` and `c ∈ U`,
the coordinate tangent space `HironakaG11InvAmbientIso.vanishingTangent (coordinateCarrier C) c` (functions on `ℂⁿ`) equals
`RankDegeneracy.tangentSpaceIn (complexChartAt c) C c` (germs on `U` read in the preferred chart); so its dimension is
`HironakaCurrentEmbeddingDimension.embeddingDimension C c`, and for analytic `C` and `c ∈ C` it is `HS_c(1) - 1`
(`HironakaHilbertSamuelTangentValue.hilbertSamuelAt_vanishing_one_eq_embeddingDimension_add_one`).  Hence the flattening
dimension of `HironakaG11InvMinimalWindow.exists_flattening` is the embedding dimension, constant (`= H(1) - 1`) on a
Hilbert--Samuel stratum `{HS = H}`.

* `vanishingTangent_eq_tangentSpaceIn`, **`finrank_vanishingTangent_eq_embeddingDimension`**,
  **`finrank_vanishingTangent_add_one_eq_hilbertSamuel`**.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11InvTangentBridge

open Hironaka.HolomorphicIdealSheaves HironakaActualIntrinsicIsoPairedWindows RankDegeneracy
  HironakaCurrentEmbeddingDimension HironakaG11InvAmbientIso

noncomputable section

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The preferred chart of an open of `ℂⁿ` is the identity on its target. -/
private theorem chart_symm_val (c : U) {w : ComplexModel n}
    (hw : w ∈ (complexChartAt (n := n) c).val.target) :
    (((complexChartAt (n := n) c).val.symm w : U) : ComplexModel n) = w :=
  (chartAt (ComplexModel n) (c : ComplexModel n)).subtypeRestr_symm_apply ⟨c⟩ hw

private theorem chart_target_mem_nhds (c : U) :
    (complexChartAt (n := n) c).val.target ∈ 𝓝 (c : ComplexModel n) :=
  (complexChartAt (n := n) c).val.open_target.mem_nhds
    ((complexChartAt (n := n) c).val.map_source (mem_complexChartAt_source c))

/-- **The coordinate tangent space is the tangent space of the vanishing ideal** (open of `ℂⁿ`, preferred chart). -/
theorem vanishingTangent_eq_tangentSpaceIn (C : Set U) (c : U) :
    vanishingTangent (coordinateCarrier C) (c : ComplexModel n) =
      tangentSpaceIn (complexChartAt (n := n) c) C c := by
  set e := complexChartAt (n := n) c
  have hec : e.val c = (c : ComplexModel n) := rfl
  ext v
  rw [mem_vanishingTangent_iff, mem_tangentSpaceIn]
  constructor
  · intro H g hg
    -- `h = g ∘ e.symm` is holomorphic near `c` and vanishes on the carrier
    let h : ComplexModel n → ℂ := fun w => g (e.val.symm w)
    have hvan : IsVanishingNear (coordinateCarrier C) (c : ComplexModel n) h := by
      have hcont : Tendsto (fun w => e.val.symm w) (𝓝 (c : ComplexModel n)) (𝓝 c) := by
        have h1 := (e.val.continuousAt_symm (e.val.map_source (mem_complexChartAt_source c))).tendsto
        rw [e.val.left_inv (mem_complexChartAt_source c)] at h1
        exact h1
      refine ⟨?_, ?_⟩
      · filter_upwards [hcont.eventually hg.1, chart_target_mem_nhds c] with w hw hwt
        have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (fun w => g (e.val.symm w)) w :=
          hw.comp w (mdifferentiableAt_atlas_symm e.2 hwt)
        exact mdifferentiableAt_iff_differentiableAt.mp h1
      · filter_upwards [hcont.eventually hg.2, chart_target_mem_nhds c] with w hw hwt hwC
        obtain ⟨y, hyC, hyw⟩ := hwC
        apply hw
        have hy : e.val.symm w = y := Subtype.ext ((chart_symm_val c hwt).trans hyw.symm)
        rw [hy]
        exact hyC
    have := H h hvan
    rw [hec]
    exact this
  · intro H h hh
    let g : U → ℂ := fun u => h u.val
    have hcont : Tendsto (Subtype.val : U → ComplexModel n) (𝓝 c) (𝓝 (c : ComplexModel n)) :=
      continuous_subtype_val.continuousAt
    have hg : (vanishingIdeal (n := n) C).mem c g := by
      refine ⟨?_, ?_⟩
      · filter_upwards [hcont.eventually hh.1] with y hy
        exact hy.mdifferentiableAt.comp y
          ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      · filter_upwards [hcont.eventually hh.2] with y hy hyC
        exact hy ⟨y, hyC, rfl⟩
    have hv := H g hg
    have hloc : (fun w => g (e.val.symm w)) =ᶠ[𝓝 (c : ComplexModel n)] h := by
      filter_upwards [chart_target_mem_nhds c] with w hw
      show h ((e.val.symm w : U) : ComplexModel n) = h w
      rw [chart_symm_val c hw]
    rw [hec, hloc.fderiv_eq] at hv
    exact hv

/-- **The coordinate tangent dimension is the embedding dimension.** -/
theorem finrank_vanishingTangent_eq_embeddingDimension (C : Set U) (c : U) :
    Module.finrank ℂ (vanishingTangent (coordinateCarrier C) (c : ComplexModel n)) =
      embeddingDimension (n := n) C c := by
  rw [vanishingTangent_eq_tangentSpaceIn]
  rfl

/-- **The coordinate tangent dimension is `HS(1) - 1`** at the points of an analytic carrier: so the flattening dimension
of `HironakaG11InvMinimalWindow.exists_flattening` is constant on a Hilbert--Samuel stratum. -/
theorem finrank_vanishingTangent_add_one_eq_hilbertSamuel {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C) {c : U} (hc : c ∈ C) :
    Module.finrank ℂ (vanishingTangent (coordinateCarrier C) (c : ComplexModel n)) + 1 =
      HironakaHolomorphicJetChartInvariance.hilbertSamuelAt (vanishingIdeal (n := n) C) c 1 := by
  rw [finrank_vanishingTangent_eq_embeddingDimension,
    HironakaHilbertSamuelTangentValue.hilbertSamuelAt_vanishing_one_eq_embeddingDimension_add_one hC hc]

end

end Hironaka.HironakaG11InvTangentBridge
