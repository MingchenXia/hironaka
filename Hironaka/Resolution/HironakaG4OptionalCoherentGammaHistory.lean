import Hironaka.Resolution.HironakaG4CoherentTowerActions
import Hironaka.Resolution.HironakaG4WeightedGammaParameter

/-!
# Coherent weighted Gamma actions along an entire history

The Gamma coordinate dictionary supplies data-preserving weighted scalings;
equivariance then gives a single compatible family of actions at every stage.
The explicit weighted section realizes the coordinates outside the mask.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OptionalCoherentGammaHistory
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates NormalCrossings HironakaG34MaskFoldEquivariance
  HironakaG34CoordinateScaling HironakaG4WeightedGammaParameter HironakaG4CoherentTowerActions

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A Gamma coordinate dictionary and equivariance produce coherent
weighted actions on every stage, together with the free-character section. -/
theorem exists_optional_coherent_gamma_history {N : Set X} {E : List (Set X)}
    (T : BlowupTower X Y) (hEq : IsEquivariant N E T)
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (s t : Fin n) (c : Fin n → ℕ) (S S₀ : Finset (Fin n))
    (hs : s ∈ S₀) (hst : t ≠ s) (hcs : c s = 0)
    (hNcoords : ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
      (y ∈ N ↔ flatMap Φ y ∈ coordSubspace S))
    (hEcoords : ∀ H ∈ E,
      (∃ R : Finset (Fin n), ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
        (y ∈ H ↔ flatMap Φ y ∈ coordSubspace R)) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
        (y ∈ H ↔ flatMap Φ y ∈ {w | binomial s t c w = 0})) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → y ∉ H)) :
    let A := weightedScalings s t c
    let F : Filter A := 𝓝 (weightedIdentity s t c)
    let U : A → Opens X := fun a => scaleDomain Φ O a
    let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
    let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
    ∃ (act : A → Y → Y), CoherentHistory U V φ T act ∧
      Tendsto (weightedSection s t c hst hcs) (𝓝 1) F ∧
      ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S₀,
        (weightedSection s t c hst hcs b : Fin n → ℂ) i = b i := by
  let A := weightedScalings s t c
  let F : Filter A := 𝓝 (weightedIdentity s t c)
  let U : A → Opens X := fun a => scaleDomain Φ O a
  let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
  let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
  have hpresN : ∀ a (p : U a), ((φ a p : V a) : X) ∈ N ↔ (p : X) ∈ N := by
    intro a p
    apply scaleDiffeo_mem_iff hΦsrc hOt a.2.1 hNcoords
    intro w hw hw'
    exact diagonal_mem_coordSubspace_iff a.2.1 S w
  have hpresE : ∀ a H, H ∈ E → ∀ p : U a, ((φ a p : V a) : X) ∈ H ↔ (p : X) ∈ H := by
    intro a H hH p
    rcases hEcoords H hH with ⟨R, hR⟩ | hR | hR
    · apply scaleDiffeo_mem_iff hΦsrc hOt a.2.1 hR
      intro w hw hw'
      exact diagonal_mem_coordSubspace_iff a.2.1 R w
    · apply scaleDiffeo_mem_iff hΦsrc hOt a.2.1 hR
      intro w hw hw'
      exact diagonal_mem_binomialLocus_iff a.2.1 a.2.2 w
    · have hempty : ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
          (y ∈ H ↔ flatMap Φ y ∈ (∅ : Set (ComplexModel n))) := by
        intro y hy hyO
        simp [hR y hy hyO]
      apply scaleDiffeo_mem_iff hΦsrc hOt a.2.1 hempty
      intro w hw hw'
      simp
  obtain ⟨act, hact⟩ := exists_coherent_of_equivariant U V φ T hEq hpresN hpresE
  exact ⟨act, hact, (weightedSection_partial_realization s t c S₀ hs hst hcs).2⟩

end
end Hironaka.HironakaG4OptionalCoherentGammaHistory
