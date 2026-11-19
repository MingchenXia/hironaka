import Hironaka.Resolution.HironakaActualNativeSectionColon
import Hironaka.Resolution.HironakaActualClosedContactBlowupRestriction

/-!
This produces the actual one-step controlled-ideal
comparison on the strict transform of an arbitrary native regular contact.
It also compares the born boundary support, without identifying old strict
boundary traces or chronological recursive values.  No G1 closure is claimed.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualNativeSectionControlledTransform
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
  SubmanifoldChartedSpace SubmanifoldCodRestrict
  HironakaActualNativeSectionColon HironakaActualClosedContactBlowupRestriction
  HironakaSmoothSubmersionOrderedChoiceImageTrace IdealWeightPowers
  GermIdealPullbackCalculus

variable {n k : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {W : Set X}

omit [IsComplexManifold n X] [IsComplexManifold n Y] in
/-- The literal born divisor support restricts to the literal intrinsic one. -/
theorem bornBoundary_preimage (hWc : IsClosed W) (D : Set W)
    {π : Y → X} (hπ : IsBlowupAlong n ((Subtype.val : W → X) '' D) π) :
    (Subtype.val : geoStrictTransform π ((Subtype.val : W → X) '' D) W → Y) ⁻¹'
        (π ⁻¹' ((Subtype.val : W → X) '' D)) =
      (restrictedProjection hWc D hπ) ⁻¹' D := by
  ext y
  constructor
  · rintro ⟨x,hxD,he⟩
    have hx : x = restrictedProjection hWc D hπ y := Subtype.ext he
    change restrictedProjection hWc D hπ y ∈ D
    exact hx ▸ hxD
  · intro hy
    exact ⟨restrictedProjection hWc D hπ y,hy,rfl⟩

/-- Actual restricted-projection geometry and native germ extension identify
the entire controlled ideal.  There is no desired comparison among the inputs. -/
theorem pullback_actual_restricted_geoTransform_ideal
    (hk : k ≤ n) (hWc : IsClosed W)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (D A : Set W) (J : GermIdeal n X)
    (hJ : ∀ x g, J.mem x g → HolomorphicAt n g x) (d : ℕ)
    {π : Y → X} (hπ : IsBlowupAlong n ((Subtype.val : W → X) '' D) π) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    letI := strictChartedSpace hk hWc hW hπ
    letI := strict_isComplexManifold hk hWc hW hπ
    let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
    let σ := restrictedProjection hWc D hπ
    let M : MarkedIdeal n X := ⟨(Subtype.val : W → X) '' A,[],J,d⟩
    let B : MarkedIdeal k W :=
      ⟨A,[],GermIdeal.pullback (m := k) (Subtype.val : W → X) J,d⟩
    GermIdeal.pullback (m := k) (Subtype.val : S → Y)
        (M.geoTransform ((Subtype.val : W → X) '' D) π).ideal =
      (B.geoTransform D σ).ideal := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := strictChartedSpace hk hWc hW hπ
  have := strict_isComplexManifold hk hWc hW hπ
  let S := geoStrictTransform π ((Subtype.val : W → X) '' D) W
  let σ := restrictedProjection hWc D hπ
  let C := (Subtype.val : W → X) '' D
  let A' := geoStrictTransform σ D A
  have hReg : ∀ y ∈ S, RegularAtDim (n := n) S y k := by
    intro y hy
    exact regularAtDim_geoStrictTransform hπ hWc hW
      (fun _ ⟨x,_hx,he⟩ => he ▸ x.property) hy
  have hval : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : S → Y) := contMDiff_val hk hReg
  have hσ : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ σ :=
    restrictedProjection_contMDiff hk hWc hW hπ
  have hJcomp :
      GermIdeal.pullback (m := k) (Subtype.val : S → Y) (GermIdeal.pullback (m := n) π J) =
        GermIdeal.pullback (m := k) σ
          (GermIdeal.pullback (m := k) (Subtype.val : W → X) J) := by
    rw [← whole_pullback_comp hπ.contMDiff hval J hJ,
      restrictedProjection_factor hWc hπ,
      whole_pullback_comp (contMDiff_val hk hW) hσ J hJ]
  have hCcomp :
      GermIdeal.pullback (m := k) (Subtype.val : S → Y)
          (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) =
        GermIdeal.pullback (m := k) σ (vanishingIdeal (n := k) D) := by
    rw [← whole_pullback_comp hπ.contMDiff hval (vanishingIdeal (n := n) C)
      (fun _ _ h => h.1),restrictedProjection_factor hWc hπ,
      whole_pullback_comp (contMDiff_val hk hW) hσ (vanishingIdeal (n := n) C)
        (fun _ _ h => h.1),centre_pullback hk hW D]
  have hA : (Subtype.val : S → Y) '' A' =
      geoStrictTransform π C ((Subtype.val : W → X) '' A) :=
    strictTransform_image hWc hπ A
  change GermIdeal.pullback (m := k) (Subtype.val : S → Y)
      (RestrictedIdealQuotient.colonAlong n
        (geoStrictTransform π C ((Subtype.val : W → X) '' A))
        (GermIdeal.pullback (m := n) π J)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d)) =
    RestrictedIdealQuotient.colonAlong k A'
      (GermIdeal.pullback (m := k) σ
        (GermIdeal.pullback (m := k) (Subtype.val : W → X) J))
      (idealPow (GermIdeal.pullback (m := k) σ (vanishingIdeal (n := k) D)) d)
  rw [← hA]
  rw [pullback_native_colonAlong hk hReg A'
    (GermIdeal.pullback (m := n) π J)
    (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d)
    (fun _ _ hg => hg.1)
    (fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)]
  rw [hJcomp,HironakaActualNonregularCoefficientNaturality.pullback_idealPow hval
    (I := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C))
    (fun hg => hg.1) d,hCcomp]

end
end Hironaka.HironakaActualNativeSectionControlledTransform
