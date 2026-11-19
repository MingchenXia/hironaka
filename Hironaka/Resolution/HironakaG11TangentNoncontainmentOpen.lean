import Hironaka.Resolution.HironakaG11ContainingFibreVariation

set_option autoImplicit false

/-!
# Openness of tangent noncontainment along a smooth carrier

A germ vanishing on the old set whose differential detects a carrier
tangent vector yields a holomorphic coordinate representative with a
nonzero derivative in a fixed carrier direction. Continuity of that
derivative propagates noncontainment to nearby carrier points.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11TangentNoncontainmentOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupSpaceTangent BlowupStrictSubmanifold BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Tangent noncontainment at a point of a smooth carrier persists at nearby
points of that carrier, for an arbitrary old set. -/
theorem eventually_tangent_noncontainment {P H : Set X} (hP : IsClosedSubmanifold n P)
    {x : X} (hxP : x ∈ P) (hnt : ¬ tangentSpace n P x ≤ tangentSpace n H x) :
    ∀ᶠ y in 𝓝 x, y ∈ P → ¬ tangentSpace n P y ≤ tangentSpace n H y := by
  obtain ⟨ξ, hξP, hξH⟩ : ∃ ξ ∈ tangentSpace n P x, ξ ∉ tangentSpace n H x := by
    by_contra h
    apply hnt
    intro ξ hξ
    by_contra hξH
    exact h ⟨ξ, hξ, hξH⟩
  obtain ⟨f, hfH, hfξ⟩ : ∃ f, (vanishingIdeal (n := n) H).mem x f ∧ germDiff n f x ξ ≠ 0 := by
    by_contra h
    apply hξH
    apply mem_tangentSpace.mpr
    intro f hf
    by_contra hne
    exact h ⟨f, hf, hne⟩
  obtain ⟨k, hk⟩ := hP.2 x hxP
  obtain ⟨-, -, Φ, hΦsrc, hΦ0, hΦflat⟩ := hk
  have hxΦ : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  let A := fderiv ℂ (flatMap Φ x) (chartAt (ComplexModel n) x x)
  have hAsurj : Function.Surjective A := fun v =>
    ⟨flatVec Φ x v, fderiv_flatMap_flatVec hΦsrc hxΦ v⟩
  have hAinj : Function.Injective A :=
    (LinearMap.injective_iff_surjective (f := (A : ComplexModel n →ₗ[ℂ] ComplexModel n))).mpr hAsurj
  have hξflat : flatVec Φ x (A ξ) = ξ := by
    apply hAinj
    exact fderiv_flatMap_flatVec hΦsrc hxΦ (A ξ)
  let v := A ξ
  have hvPlane : v ∈ complexCoordinatePlane n k := by
    intro i hi
    have hz := (mem_tangentSpace_iff hΦsrc hΦflat hxΦ hxP).mp hξP i hi
    rw [germDiff_flatCoord hΦsrc hxΦ, ContinuousLinearMap.comp_apply] at hz
    exact hz
  let F : ComplexModel n → ℂ := fun z => f ((chartAt (ComplexModel n) x).symm (Φ.invFun z))
  let z₀ := Φ.toFun (chartAt (ComplexModel n) x x)
  have hzT : z₀ ∈ Φ.target := Φ.mapsTo_toFun hxΦ.2
  have hFd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ F z := by
    filter_upwards [Φ.isOpen_target.mem_nhds hzT,
      (tendsto_flatInverse Φ hxΦ).eventually hfH.1.eventually] with z hz hfz
    have hzChart := hΦsrc (Φ.mapsTo_invFun hz)
    exact (differentiableAt_comp_chart_symm hzChart hfz.mdifferentiableAt).comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hFd
  have hFdiff : DifferentiableOn ℂ F U := fun z hz => (hUsub hz).differentiableWithinAt
  have hFcont : ContinuousOn (fderiv ℂ F) U :=
    (Hironaka.contDiffOn_of_differentiableOn_complex hFdiff hUopen).continuousOn_fderiv_of_isOpen hUopen
      (by simp)
  have hFval : fderiv ℂ F z₀ v ≠ 0 := by
    have h := germDiff_flatVec hΦsrc hxΦ hfH.1 v
    rw [hξflat] at h
    exact h.symm ▸ hfξ
  have hFvalcont : ContinuousAt (fun z => fderiv ℂ F z v) z₀ :=
    (hFcont.clm_apply continuousOn_const).continuousAt (hUopen.mem_nhds hzU)
  have hFnear : ∀ᶠ z in 𝓝 z₀, fderiv ℂ F z v ≠ 0 :=
    hFvalcont.tendsto (isOpen_ne.mem_nhds hFval)
  have hcoord : ContinuousAt (fun y => Φ.toFun (chartAt (ComplexModel n) x y)) x :=
    ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hxΦ.2)).continuousAt).comp
      ((chartAt (ComplexModel n) x).continuousAt hxΦ.1)
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxΦ, hcoord.tendsto hFnear,
    hfH.1.eventually_nhds, hfH.2.eventually_nhds] with y hy hne hyHol hyVan hyP hle
  have hvP : flatVec Φ y v ∈ tangentSpace n P y := by
    apply (mem_tangentSpace_iff hΦsrc hΦflat hy hyP).mpr
    intro i hi
    rw [germDiff_flatCoord_flatVec hΦsrc hy]
    exact hvPlane i hi
  have hyH : (vanishingIdeal (n := n) H).mem y f := ⟨hyHol, hyVan⟩
  have hz := germDiff_eq_zero_of_mem_tangentSpace (hle hvP) hyH
  rw [germDiff_flatVec hΦsrc hy hyHol] at hz
  exact hne hz

end

end Hironaka.HironakaG11TangentNoncontainmentOpen
