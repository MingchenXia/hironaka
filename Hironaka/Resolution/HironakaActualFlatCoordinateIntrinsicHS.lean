/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualFlatCoordinateIntrinsicHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates
  HironakaHolomorphicJetChartInvariance HironakaActualVanishingIntrinsicHSTransport
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {x₀ : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))

private theorem contMDiff_flat_forward :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun x : (⟨flatDomain Φ,isOpen_flatDomain Φ⟩ : Opens M) =>
        Φ.toFun (chartAt (ComplexModel n) x₀ x)) := by
  intro x
  have hmd : ∀ᶠ q in 𝓝 (x : M), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (fun q : M => Φ.toFun (chartAt (ComplexModel n) x₀ q)) q :=
    eventually_of_mem ((isOpen_flatDomain Φ).mem_nhds x.2) fun q hq =>
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hq.2)).mdifferentiableAt.comp q
        (mdifferentiableAt_chart hq.1)
  exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp x (contMDiff_subtype_val x)

private theorem contMDiff_flat_inverse
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun u : (⟨Φ.target,Φ.isOpen_target⟩ : Opens (ComplexModel n)) =>
        (chartAt (ComplexModel n) x₀).symm (Φ.invFun u)) := by
  intro u
  have hmd : ∀ᶠ w in 𝓝 (u : ComplexModel n), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (fun w : ComplexModel n => (chartAt (ComplexModel n) x₀).symm (Φ.invFun w)) w :=
    eventually_of_mem (Φ.isOpen_target.mem_nhds u.2) fun w hw =>
      (mdifferentiableAt_chart_symm (hΦsrc (Φ.mapsTo_invFun hw))).comp w
        (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).mdifferentiableAt
  exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp u (contMDiff_subtype_val u)

/-- The actual original flat domain and actual model target are biholomorphic by their true coordinate functions. -/
def actualFlatCoordinateDiffeomorph
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target) :
    (⟨flatDomain Φ,isOpen_flatDomain Φ⟩ : Opens M)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        (⟨Φ.target,Φ.isOpen_target⟩ : Opens (ComplexModel n)) where
  toFun x := ⟨Φ.toFun (chartAt (ComplexModel n) x₀ x),Φ.mapsTo_toFun x.2.2⟩
  invFun u := ⟨(chartAt (ComplexModel n) x₀).symm (Φ.invFun u),(flatInverse_mem Φ u.2 hΦsrc).1⟩
  left_inv x := Subtype.ext (flatInverse_flat Φ x.2)
  right_inv u := Subtype.ext (flatInverse_mem Φ u.2 hΦsrc).2
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_flat_forward Φ) (fun x => Φ.mapsTo_toFun x.2.2)
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_flat_inverse Φ hΦsrc)
    (fun u => (flatInverse_mem Φ u.2 hΦsrc).1)

theorem actualFlatCoordinateDiffeomorph_apply
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (x : (⟨flatDomain Φ,isOpen_flatDomain Φ⟩ : Opens M)) :
    (actualFlatCoordinateDiffeomorph Φ hΦsrc x : ComplexModel n)=Φ.toFun (chartAt (ComplexModel n) x₀ x) := rfl

theorem actualFlatCoordinateDiffeomorph_symm_apply
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (u : (⟨Φ.target,Φ.isOpen_target⟩ : Opens (ComplexModel n))) :
    ((actualFlatCoordinateDiffeomorph Φ hΦsrc).symm u : M)=
      (chartAt (ComplexModel n) x₀).symm (Φ.invFun u) := rfl

/-- The actual inverse flat-coordinate embedding is holomorphic on the entire true target subtype. -/
theorem contMDiff_actual_flat_inverse
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun u : (⟨Φ.target,Φ.isOpen_target⟩ : Opens (ComplexModel n)) =>
        (chartAt (ComplexModel n) x₀).symm (Φ.invFun u)) :=
  contMDiff_subtype_val.comp (actualFlatCoordinateDiffeomorph Φ hΦsrc).symm.contMDiff

/-- Genuine inverse coordinates followed by the true open inclusion are an actual open embedding. -/
theorem isOpenEmbedding_actual_flat_inverse
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target) :
    Topology.IsOpenEmbedding
      (fun u : (⟨Φ.target,Φ.isOpen_target⟩ : Opens (ComplexModel n)) =>
        (chartAt (ComplexModel n) x₀).symm (Φ.invFun u)) :=
  (isOpen_flatDomain Φ).isOpenEmbedding_subtypeVal.comp
    (actualFlatCoordinateDiffeomorph Φ hΦsrc).symm.toHomeomorph.isOpenEmbedding

/-- ANY original subset retains ALL unchanged intrinsic HS values under the actual inverse coordinates. -/
theorem hilbertSamuelAt_vanishing_actual_flat_inverse
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (W : Set M) (u : (⟨Φ.target,Φ.isOpen_target⟩ : Opens (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n)
      ((fun q : (⟨Φ.target,Φ.isOpen_target⟩ : Opens (ComplexModel n)) =>
        (chartAt (ComplexModel n) x₀).symm (Φ.invFun q)) ⁻¹' W)) u ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W)
        ((chartAt (ComplexModel n) x₀).symm (Φ.invFun u)) ℓ := by
  let D : Opens M := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let E := actualFlatCoordinateDiffeomorph Φ hΦsrc
  have hbi := hilbertSamuelAt_vanishing_actual_biholomorphic_any E.symm
    ((Subtype.val : D → M) ⁻¹' W) u ℓ
  have hopen := hilbertSamuelAt_vanishing_actual_open_any (n := n) D W (E.symm u) ℓ
  exact hbi.trans hopen

end
end Hironaka.HironakaActualFlatCoordinateIntrinsicHS
