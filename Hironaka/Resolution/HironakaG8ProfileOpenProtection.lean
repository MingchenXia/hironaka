import Hironaka.Resolution.HironakaActualCompactHSMaximalProfile
import Hironaka.Resolution.HironakaResolutionSpace

/-! Strict singular profile bounds persist over a neighborhood of a proper fibre. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold

universe u v

namespace Hironaka.HironakaG8ProfileOpenProtection

open Hironaka.HolomorphicIdealSheaves HironakaEmbeddedAnalytic
  HironakaActualCompactHSMaximalProfile HironakaHolomorphicJetChartInvariance

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The inverse image of any upper set for the entire coherent
Hilbert–Samuel profile is closed. -/
theorem isClosed_actual_hs_profile_preimage_upper
    (I : GermIdeal n Y) (hI : I.IsCoherent)
    (B : Set (Lex (ℕ → ℕ))) (hB : IsUpperSet B) :
    IsClosed ((fun y => toLex (hilbertSamuelAt I y)) ⁻¹' B) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨V, hyV, _, hV⟩ := exists_actual_entire_hs_pointwise_upper_window I hI y
  exact Filter.mem_of_superset (V.isOpen.mem_nhds hyV)
    (fun z hz h => hy (hB (hV z hz) h))

/-- After a proper map, avoidance of an upper set of singular profiles on
the full inverse image of a prescribed set holds on an open neighborhood
inside any allowed base open. The prescribed set need not be closed. -/
theorem exists_open_singular_hs_profile_avoid {X : Type v} [TopologicalSpace X]
    {p : Y → X} (hp : IsProperMap p) {A : Set Y} (hA : IsComplexAnalyticSubset (n := n) A)
    (B : Set (Lex (ℕ → ℕ))) (hB : IsUpperSet B)
    (K : Set X) (O : Opens X) (hKO : K ⊆ O)
    (hAvoid : ∀ y ∈ p ⁻¹' K ∩ singularSet (n := n) A,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) y) ∉ B) :
    ∃ U : Opens X, K ⊆ U ∧ U ≤ O ∧
      ∀ y ∈ p ⁻¹' (U : Set X) ∩ singularSet (n := n) A,
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) y) ∉ B := by
  let F := singularSet (n := n) A ∩
    (fun y => toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) y)) ⁻¹' B
  have hF : IsClosed F := (isClosed_singularSet hA.isClosed).inter
    (isClosed_actual_hs_profile_preimage_upper _ (CartanIrreducible.cartanCoherence A hA) B hB)
  let U : Opens X := ⟨(O : Set X) ∩ (p '' F)ᶜ, O.isOpen.inter (hp.isClosedMap _ hF).isOpen_compl⟩
  refine ⟨U, ?_, fun x hx => hx.1, ?_⟩
  · intro x hx
    refine ⟨hKO hx, ?_⟩
    rintro ⟨y, hy, rfl⟩
    exact hAvoid y ⟨hx, hy.1⟩ hy.2
  · intro y hy hyB
    exact hy.1.2 (mem_image_of_mem _ ⟨hy.2, hyB⟩)

/-- A strict bound for the entire singular profile persists on a base
neighborhood of the original fibres. -/
theorem exists_open_singular_hs_profile_drop {X : Type v} [TopologicalSpace X]
    {p : Y → X} (hp : IsProperMap p) {A : Set Y} (hA : IsComplexAnalyticSubset (n := n) A)
    (H : ℕ → ℕ) (K : Set X) (O : Opens X) (hKO : K ⊆ O)
    (hDrop : ∀ y ∈ p ⁻¹' K ∩ singularSet (n := n) A,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) y) < toLex H) :
    ∃ U : Opens X, K ⊆ U ∧ U ≤ O ∧
      ∀ y ∈ p ⁻¹' (U : Set X) ∩ singularSet (n := n) A,
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) y) < toLex H := by
  obtain ⟨U, hKU, hUO, hAvoid⟩ := exists_open_singular_hs_profile_avoid (n := n)
    hp hA (Ici (toLex H)) (isUpperSet_Ici (toLex H)) K O hKO
    (fun y hy h => (not_le_of_gt (hDrop y hy)) h)
  refine ⟨U, hKU, hUO, fun y hy => lt_of_not_ge ?_⟩
  exact hAvoid y hy

/-- A weak bound for the entire singular profile persists on a base
neighborhood of the original fibres. -/
theorem exists_open_singular_hs_profile_upper_bound {X : Type v} [TopologicalSpace X]
    {p : Y → X} (hp : IsProperMap p) {A : Set Y} (hA : IsComplexAnalyticSubset (n := n) A)
    (H : ℕ → ℕ) (K : Set X) (O : Opens X) (hKO : K ⊆ O)
    (hBound : ∀ y ∈ p ⁻¹' K ∩ singularSet (n := n) A,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) y) ≤ toLex H) :
    ∃ U : Opens X, K ⊆ U ∧ U ≤ O ∧
      ∀ y ∈ p ⁻¹' (U : Set X) ∩ singularSet (n := n) A,
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) A) y) ≤ toLex H := by
  simpa only [mem_Ioi, not_lt] using
    exists_open_singular_hs_profile_avoid hp hA (Ioi (toLex H)) (isUpperSet_Ioi (toLex H)) K O hKO
      (fun y hy => not_lt_of_ge (hBound y hy))

end Hironaka.HironakaG8ProfileOpenProtection
