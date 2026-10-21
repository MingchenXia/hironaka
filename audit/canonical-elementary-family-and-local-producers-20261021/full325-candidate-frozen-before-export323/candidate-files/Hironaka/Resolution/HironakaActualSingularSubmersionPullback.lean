/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualSingularChartTransport
import Hironaka.Resolution.HironakaSmoothSubmersionNormalCrossings

/-!
# Entire original singular vanishing ideals under actual submersions

Actual lifted product coordinates are constructed internally. Whole original
functional spans, arbitrary-set inverse-chart membership and true singular
product division then prove the independently defined ENTIRE ideal pullback.
No regularity/coherence/equality/coordinate-square certificate is input to
the original submersion endpoint.
Blueprint: `hironaka-actual-singular-submersion-pullback-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSingularSubmersionPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan InvertibleIdealQuotient
  BlowupFlatCoordinates NormalCrossings HironakaRelativeNormalIdeal
  HironakaActualCylinderRelativeHadamard HironakaActualCylinderVanishingIdealExtension
  HironakaActualCylinderPullbackOrigin HironakaActualSingularChartTransport
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionMonomialOrdering
variable {n t : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel (n+t)) Y] [IsComplexManifold (n+t) Y]

/-- Genuine original submersion geometry constructs the SAME-target-chart actual inverse product commutation. -/
theorem exists_inverse_product_coordinates {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel (n+t)) 𝓘(ℂ,ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y))=0) :
    ∃ Ξ : LocalHolomorphicEquivAt (n := n+t) (chartAt (ComplexModel (n+t)) y y),
      Ξ.source⊆(chartAt (ComplexModel (n+t)) y).target ∧
      Ξ.toFun (chartAt (ComplexModel (n+t)) y y)=0 ∧
      ∀ᶠ u in 𝓝 (0 : ComplexModel (n+t)),
        f (inverseCoordinates Ξ u)=inverseCoordinates Φ (tangentProjection n t u) := by
  let Ξ := liftedCoordinatesAdd hf Φ h0
  obtain ⟨hΞsrc,hΞ0,hdict⟩ := liftedCoordinatesAdd_dictionary hf Φ h0
  refine ⟨Ξ,hΞsrc,hΞ0,?_⟩
  have htar : (0 : ComplexModel (n+t))∈Ξ.target := by
    have hc := Ξ.mapsTo_toFun Ξ.center_mem_source
    have hzero : Ξ.toFun (chartAt (ComplexModel (n+t)) y y)=0 := hΞ0
    rw [hzero] at hc
    exact hc
  filter_upwards [Ξ.isOpen_target.mem_nhds htar] with u hu
  let z := inverseCoordinates Ξ u
  have hz : z∈flatDomain Ξ := (flatInverse_mem Ξ hu hΞsrc).1
  have hzu : forwardCoordinates Ξ z=u := (flatInverse_mem Ξ hu hΞsrc).2
  have hfx := (hdict z hz).1
  have he : tangentProjection n t u=forwardCoordinates Φ (f z) := by
    ext j
    calc
      tangentProjection n t u j = u (j.castAdd t) := rfl
      _ = forwardCoordinates Ξ z (j.castAdd t) := congrArg (fun w : ComplexModel (n+t) => w (j.castAdd t)) hzu.symm
      _ = forwardCoordinates Φ (f z) j := (hdict z hz).2 j
  change f z=inverseCoordinates Φ (tangentProjection n t u)
  rw [he]
  exact (flatInverse_flat Φ hfx).symm

/-- Whole original functional membership follows from actual local product-map commutation in genuine supplied charts. -/
theorem pullback_membership_of_inverse_product_coordinates {f : Y → X} {y : Y}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel (n+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) (f y)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y))=0)
    (Ξ : LocalHolomorphicEquivAt (n := n+t) (chartAt (ComplexModel (n+t)) y y))
    (hΞ0 : Ξ.toFun (chartAt (ComplexModel (n+t)) y y)=0)
    (hcomm : ∀ᶠ u in 𝓝 (0 : ComplexModel (n+t)),
      f (inverseCoordinates Ξ u)=inverseCoordinates Φ (tangentProjection n t u))
    (N : Set X) (F : Y → ℂ) :
    (GermIdeal.pullback (m := n+t) f (vanishingIdeal (n := n) N)).mem y F ↔
      (vanishingIdeal (n := n+t) (f ⁻¹' N)).mem y F := by
  let W : Set (ComplexModel n) := inverseCoordinates Φ ⁻¹' N
  let S : (Y → ℂ) → Prop := fun s => ∃ a,(vanishingIdeal (n := n) N).mem (f y) a ∧ s=a∘f
  let T : (ComplexModel (n+t) → ℂ) → Prop := fun g => ∃ s,S s ∧ g=s∘inverseCoordinates Ξ
  let A := actualPullbackFunctionFamily n t W
  have hp : ContMDiff 𝓘(ℂ,ComplexModel (n+t)) 𝓘(ℂ,ComplexModel n) ∞ (tangentProjection n t) :=
    (tangentProjection n t).contDiff.contMDiff
  have hspan : IsInSpanAt (n := n+t) T 0 (F∘inverseCoordinates Ξ) ↔
      IsInSpanAt (n := n+t) A 0 (F∘inverseCoordinates Ξ) := by
    constructor
    · intro hF
      refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hF
      rintro _ ⟨s,⟨a,ha,rfl⟩,rfl⟩
      let b := a∘inverseCoordinates Φ
      have hb : (vanishingIdeal (n := n) W).mem 0 b :=
        (vanishingIdeal_inverseCoordinates_iff Φ h0 N a).mp ha
      have hh : HolomorphicAt (n+t) (b∘tangentProjection n t) 0 :=
        hb.1.comp_contMDiff (f := tangentProjection n t)
          (by simpa only [map_zero] using Eventually.of_forall fun _ => hp.contMDiffAt)
      have hs : IsInSpanAt (n := n+t) A 0 (b∘tangentProjection n t) :=
        isInSpanAt_self ⟨b,hb,rfl⟩ hh
      refine InvertibleIdealQuotient.IsInSpanAt.congr' hs ?_
      exact hcomm.mono fun z hz => congrArg a hz.symm
    · intro hF
      refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hF
      rintro _ ⟨b,hb,rfl⟩
      let a := b∘forwardCoordinates Φ
      obtain ⟨ha,he⟩ := original_representative_of_model_vanishing Φ hsrc h0 N b hb
      have hhol : HolomorphicAt (n+t) (a∘f) y :=
        ha.1.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)
      have hh := (holomorphicAt_inverseCoordinates_iff Ξ hΞ0 (a∘f)).mp hhol
      have hs : IsInSpanAt (n := n+t) T 0 ((a∘f)∘inverseCoordinates Ξ) :=
        isInSpanAt_self ⟨a∘f,⟨a,ha,rfl⟩,rfl⟩ hh
      refine InvertibleIdealQuotient.IsInSpanAt.congr' hs ?_
      have ht : Tendsto (tangentProjection n t) (𝓝 0) (𝓝 0) := by
        simpa only [map_zero] using (tangentProjection n t).continuous.tendsto (0 : ComplexModel (n+t))
      filter_upwards [hcomm,ht.eventually he] with z hz hez
      calc
        a (f (inverseCoordinates Ξ z)) = a (inverseCoordinates Φ (tangentProjection n t z)) := congrArg a hz
        _ = b (tangentProjection n t z) := hez
  have hproduct : IsInSpanAt (n := n+t) A 0 (F∘inverseCoordinates Ξ) ↔
      (vanishingIdeal (n := n+t) (cylinderCarrier n t W)).mem 0 (F∘inverseCoordinates Ξ) := by
    have h := HironakaActualCylinderPullbackPoints.pullback_vanishingIdeal_mem_iff n t W 0 (F∘inverseCoordinates Ξ)
    change IsInSpanAt (n := n+t)
      (fun g => ∃ a,(vanishingIdeal (n := n) W).mem (tangentProjection n t 0) a ∧
        g=a∘tangentProjection n t) 0 (F∘inverseCoordinates Ξ) ↔ _ at h
    change IsInSpanAt (n := n+t)
      (fun g => ∃ a,(vanishingIdeal (n := n) W).mem 0 a ∧ g=a∘tangentProjection n t)
      0 (F∘inverseCoordinates Ξ) ↔ _
    simpa only [map_zero] using h
  have hsets : ∀ᶠ z in 𝓝 (0 : ComplexModel (n+t)),
      z∈cylinderCarrier n t W ↔ z∈inverseCoordinates Ξ ⁻¹' (f ⁻¹' N) := by
    filter_upwards [hcomm] with z hz
    change inverseCoordinates Φ (tangentProjection n t z)∈N ↔ f (inverseCoordinates Ξ z)∈N
    rw [hz]
  have hvan : (vanishingIdeal (n := n+t) (cylinderCarrier n t W)).mem 0 (F∘inverseCoordinates Ξ) ↔
      (vanishingIdeal (n := n+t) (inverseCoordinates Ξ ⁻¹' (f ⁻¹' N))).mem 0 (F∘inverseCoordinates Ξ) := by
    constructor
    · rintro ⟨hF,hzero⟩
      refine ⟨hF,?_⟩
      filter_upwards [hzero,hsets] with z hz he hzN
      exact hz (he.mpr hzN)
    · rintro ⟨hF,hzero⟩
      refine ⟨hF,?_⟩
      filter_upwards [hzero,hsets] with z hz he hzN
      exact hz (he.mp hzN)
  change IsInSpanAt (n := n+t) S y F ↔ _
  exact (isInSpanAt_inverseCoordinates_iff Ξ hΞ0 S F).trans
    (hspan.trans (hproduct.trans (hvan.trans (vanishingIdeal_inverseCoordinates_iff Ξ hΞ0 (f ⁻¹' N) F).symm)))

/-- ONLY genuine original submersion geometry, with ANY original subset, internally proves ENTIRE original vanishing-ideal pullback. -/
theorem pullback_vanishingIdeal_submersion {m n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (N : Set X) :
    GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) N)=vanishingIdeal (n := m) (f ⁻¹' N) := by
  apply GermIdeal.ext
  funext y F
  apply propext
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt (hf.isSubmersionAt y))
  obtain ⟨Φ,hsrc,h0⟩ := exists_centred_coordinates (n := n) (f y)
  obtain ⟨Ξ,_hΞsrc,hΞ0,hcomm⟩ := exists_inverse_product_coordinates (hf.isSubmersionAt y) Φ h0
  exact pullback_membership_of_inverse_product_coordinates hf.contMDiff Φ hsrc h0 Ξ hΞ0 hcomm N F

end
end Hironaka.HironakaActualSingularSubmersionPullback
