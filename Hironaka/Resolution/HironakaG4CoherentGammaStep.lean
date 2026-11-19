import Hironaka.Resolution.HironakaG4CoherentTowerActions
import Hironaka.Resolution.HironakaG4UniformScalingDomain
import Hironaka.Resolution.HironakaG4WeightedGammaParameter

/-!
# Joint local properties of a coherent Gamma history

Coherent history maps are continuous on their varying sources individually.
The uniform scaling-source lemma makes the same facts hold jointly near any
point over the initial coordinate window, without assuming joint continuity
of the actions in the parameter.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CoherentGammaStep
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates HironakaG34CoordinateScaling HironakaG4UniformScalingDomain
  HironakaG4WeightedGammaParameter HironakaG4CoherentTowerActions

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- The terminal map of a coherent history is continuous on its source. -/
theorem coherentHistory_continuous {A : Type*} (U V : A → Opens X)
    (φ : ∀ a, CMfd.of (n := n) (U a) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (V a)) (T : BlowupTower X Y) (act : A → Y → Y)
    (h : CoherentHistory U V φ T act) (a : A) (y : Y) (hy : T.proj y ∈ U a) :
    ContinuousAt (act a) y := by
  cases T with
  | refl => exact (h a y hy).2
  | step T C π hπ =>
    obtain ⟨_, _, _, hstep⟩ := h
    exact (hstep a y hy).2

/-- At every step of a coherent weighted history over a coordinate window,
the predecessor action and successor action satisfy the joint eventual
hypotheses for the next actual toric chart. -/
theorem coherent_gamma_step_joint {T : BlowupTower X Y} {C : Set Y} {π : Z → Y}
    {hπ : IsBlowupAlong n C π} {x₀ : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (s t : Fin n) (c : Fin n → ℕ)
    (act' : weightedScalings s t c → Z → Z)
    (h : CoherentHistory (fun a : weightedScalings s t c => scaleDomain Φ O a)
      (fun a => scaleDomain Φ O (invScale a))
      (fun a => scaleDiffeo hΦsrc hOt a.2.1) (.step T C π hπ) act')
    {z : Z} (hz : T.proj (π z) ∈ flatDomain Φ) (hzO : flatMap Φ (T.proj (π z)) ∈ O) :
    let A := weightedScalings s t c
    let F : Filter A := 𝓝 (weightedIdentity s t c)
    let U : A → Opens X := fun a => scaleDomain Φ O a
    let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
    let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
    ∃ act : A → Y → Y, CoherentHistory U V φ T act ∧
      (∀ᶠ p in F ×ˢ 𝓝 (π z), ContinuousAt (act p.1) p.2 ∧
        (act p.1 p.2 ∈ C ↔ p.2 ∈ C)) ∧
      ∀ᶠ p in F ×ˢ 𝓝 z,
        π (act' p.1 p.2) = act p.1 (π p.2) ∧ ContinuousAt (act' p.1) p.2 := by
  let A := weightedScalings s t c
  let F : Filter A := 𝓝 (weightedIdentity s t c)
  let U : A → Opens X := fun a => scaleDomain Φ O a
  let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
  let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
  obtain ⟨act, hhist, hC, hcomm⟩ := h
  have hμ : Tendsto (Subtype.val : A → Fin n → ℂ) F (𝓝 1) :=
    continuous_subtype_val.continuousAt
  have hpref : Tendsto (fun p : A × Y => ((p.1 : Fin n → ℂ), p.2))
      (F ×ˢ 𝓝 (π z)) (𝓝 1 ×ˢ 𝓝 (π z)) := (hμ.comp tendsto_fst).prodMk tendsto_snd
  have hfull : Tendsto (fun p : A × Z => ((p.1 : Fin n → ℂ), p.2))
      (F ×ˢ 𝓝 z) (𝓝 1 ×ˢ 𝓝 z) := (hμ.comp tendsto_fst).prodMk tendsto_snd
  have hy := hpref.eventually (eventually_preimage_mem_scaleDomain Φ O T.proj
    T.contMDiff_proj.continuous.continuousAt hz hzO)
  have hz' := hfull.eventually (eventually_preimage_mem_scaleDomain Φ O (T.proj ∘ π)
    (T.contMDiff_proj.continuous.continuousAt.comp hπ.contMDiff.continuous.continuousAt) hz hzO)
  refine ⟨act, hhist, ?_, ?_⟩
  · filter_upwards [hy] with p hp
    exact ⟨coherentHistory_continuous U V φ T act hhist p.1 p.2 hp, hC p.1 p.2 hp⟩
  · filter_upwards [hz'] with p hp
    exact hcomm p.1 p.2 hp

end
end Hironaka.HironakaG4CoherentGammaStep
