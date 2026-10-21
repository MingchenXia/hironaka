/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCylinderPullbackPoints
import Hironaka.Analytic.ManifoldFiniteSpanChartTransport
import Hironaka.Blowup.BlowupFlatCoordinates

/-!
# Actual original arbitrary-set functional ideals in supplied genuine coordinates

The SAME supplied chart transports arbitrary entire generating families,
actual vanishing membership for every original subset and literal original
function representatives of model vanishing germs. No coherence, analytic
presentation, original representative or ideal-equality certificate is input.
Blueprint: `hironaka-actual-singular-chart-transport-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold
namespace Hironaka.HironakaActualSingularChartTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  InvertibleIdealQuotient BlowupFlatCoordinates ManifoldFiniteSpanChartTransport
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {x : X}

/-- The literal original inverse coordinate function; inverse identities use its genuine domain. -/
def inverseCoordinates (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    ComplexModel n → X := fun u => (chartAt (ComplexModel n) x).symm (Φ.invFun u)

/-- The literal original forward coordinate function, with its real open domain retained separately. -/
def forwardCoordinates (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    X → ComplexModel n := fun z => Φ.toFun (chartAt (ComplexModel n) x z)

/-- ENTIRE original families transport through the SAME actual supplied chart using only finite original relations. -/
theorem isInSpanAt_inverseCoordinates_iff
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (S : (X → ℂ) → Prop) (F : X → ℂ) :
    IsInSpanAt (n := n) S x F ↔ IsInSpanAt (n := n)
      (fun g => ∃ f,S f ∧ g=f∘inverseCoordinates Φ) 0 (F∘inverseCoordinates Φ) := by
  constructor
  · rintro ⟨hF,N,G,a,hG,ha,he⟩
    have hsmall : IsInSpanAt (n := n) (·∈range G) x F :=
      ⟨hF,N,G,a,fun i => ⟨i,rfl⟩,ha,he⟩
    have ht := (isInSpanAt_comp_adapted_iff x Φ h0 G F).mp hsmall
    refine IsInSpanAt.mono ?_ ht
    rintro _ ⟨i,rfl⟩
    exact ⟨G i,hG i,rfl⟩
  · rintro ⟨hF,N,G,a,hG,ha,he⟩
    choose s hs hse using hG
    have hsmall : IsInSpanAt (n := n) (·∈range G) 0 (F∘inverseCoordinates Φ) :=
      ⟨hF,N,G,a,fun i => ⟨i,rfl⟩,ha,he⟩
    have ht : IsInSpanAt (n := n) (·∈range fun i => s i∘inverseCoordinates Φ) 0
        (F∘inverseCoordinates Φ) := by
      refine IsInSpanAt.mono ?_ hsmall
      rintro _ ⟨i,rfl⟩
      exact ⟨i,(hse i).symm⟩
    have ho := (isInSpanAt_comp_adapted_iff x Φ h0 s F).mpr ht
    refine IsInSpanAt.mono ?_ ho
    rintro _ ⟨i,rfl⟩
    exact hs i

/-- Actual holomorphy in the SAME supplied original chart, including both literal function directions. -/
theorem holomorphicAt_inverseCoordinates_iff
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) (F : X → ℂ) :
    HolomorphicAt n F x ↔ HolomorphicAt n (F∘inverseCoordinates Φ) 0 := by
  let G : Fin 1 → X → ℂ := fun _ => F
  have h := isInSpanAt_comp_adapted_iff x Φ h0 G F
  constructor
  · intro hF
    exact (h.mp (isInSpanAt_self ⟨0,rfl⟩ hF)).1
  · intro hF
    exact (h.mpr (isInSpanAt_self ⟨0,rfl⟩ hF)).1

omit [IsComplexManifold n X] in
private theorem forward_tendsto
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    Tendsto (forwardCoordinates Φ) (𝓝 x) (𝓝 0) := by
  have hc : ContinuousAt (forwardCoordinates Φ) x :=
    (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.comp
      ((chartAt (ComplexModel n) x).continuousAt (mem_chart_source _ x))
  simpa only [forwardCoordinates,h0] using hc.tendsto

/-- Original arbitrary-set vanishing membership is equivalent to actual inverse-chart vanishing membership. -/
theorem vanishingIdeal_inverseCoordinates_iff
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) (N : Set X) (F : X → ℂ) :
    (vanishingIdeal (n := n) N).mem x F ↔
      (vanishingIdeal (n := n) (inverseCoordinates Φ ⁻¹' N)).mem 0 (F∘inverseCoordinates Φ) := by
  constructor
  · intro hF
    refine ⟨(holomorphicAt_inverseCoordinates_iff Φ h0 F).mp hF.1,?_⟩
    have hq : Tendsto (inverseCoordinates Φ) (𝓝 0) (𝓝 x) := by
      change Tendsto (fun u => (chartAt (ComplexModel n) x).symm (Φ.invFun u)) (𝓝 0) (𝓝 x)
      have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
      rw [h0] at h
      exact h
    exact (hq.eventually hF.2).mono fun z hz hzN => hz hzN
  · intro hF
    refine ⟨(holomorphicAt_inverseCoordinates_iff Φ h0 F).mpr hF.1,?_⟩
    filter_upwards [(forward_tendsto Φ h0).eventually hF.2,
      (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with z hz hzdom hzN
    have he : inverseCoordinates Φ (forwardCoordinates Φ z)=z := flatInverse_flat Φ hzdom
    have hzpre : forwardCoordinates Φ z∈inverseCoordinates Φ ⁻¹' N := by
      change inverseCoordinates Φ (forwardCoordinates Φ z)∈N
      rw [he]
      exact hzN
    simpa only [Function.comp_apply,he] using hz hzpre

omit [IsComplexManifold n X] in
private theorem vanishing_congr {N : Set X} {F G : X → ℂ}
    (hF : (vanishingIdeal (n := n) N).mem x F) (he : F=ᶠ[𝓝 x]G) :
    (vanishingIdeal (n := n) N).mem x G := by
  refine ⟨hF.1.congr he,?_⟩
  filter_upwards [hF.2,he] with z hz hez hzN
  rw [← hez]
  exact hz hzN

/-- EVERY original model vanishing function has its literal SAME-chart original representative, not a global holomorphic extension. -/
theorem original_representative_of_model_vanishing
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (N : Set X) (g : ComplexModel n → ℂ)
    (hg : (vanishingIdeal (n := n) (inverseCoordinates Φ ⁻¹' N)).mem 0 g) :
    (vanishingIdeal (n := n) N).mem x (g∘forwardCoordinates Φ) ∧
      (g∘forwardCoordinates Φ)∘inverseCoordinates Φ=ᶠ[𝓝 0]g := by
  have htar : (0 : ComplexModel n)∈Φ.target := by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have he : (g∘forwardCoordinates Φ)∘inverseCoordinates Φ=ᶠ[𝓝 0]g := by
    filter_upwards [Φ.isOpen_target.mem_nhds htar] with u hu
    exact congrArg g (flatInverse_mem Φ hu hsrc).2
  refine ⟨(vanishingIdeal_inverseCoordinates_iff Φ h0 N (g∘forwardCoordinates Φ)).mpr ?_,he⟩
  exact vanishing_congr hg he.symm

end
end Hironaka.HironakaActualSingularChartTransport
