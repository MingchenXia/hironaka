import Hironaka.Resolution.HironakaBaseChange
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism

/-! Entire vanishing ideals pull back along genuine open holomorphic embeddings.
Blueprint: hironaka-actual-open-embedding-vanishing-ideal-20261102.tex. -/
set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualOpenEmbeddingVanishingIdeal

open Hironaka.HolomorphicIdealSheaves HironakaBaseChange

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The entire vanishing ideal of ANY subset transports by the actual biholomorphism. -/
theorem pullback_vanishingIdeal_of_biholomorphism
    (e : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (C : Set X) :
    GermIdeal.pullback (m := n) e (vanishingIdeal (n := n) C) =
      vanishingIdeal (n := n) (e ⁻¹' C) := by
  have hi : GermIdeal.pullback (m := n) (id : Y → Y)
      (vanishingIdeal (n := n) (e ⁻¹' C)) = vanishingIdeal (n := n) (e ⁻¹' C) :=
    GermIdeal.ext (funext fun _ => funext fun _ =>
      propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)
  have h := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
    (φ := e) (ψ := e.symm) e.contMDiff e.symm.contMDiff
    e.apply_symm_apply e.symm_apply_apply (g := (id : Y → Y)) contMDiff_id C
  simpa only [Function.comp_id, hi] using h.symm

/-- An actual open holomorphic embedding pulls back the ENTIRE vanishing ideal
of any original subset, with no ideal extension or comparison hypothesis. -/
theorem pullback_vanishingIdeal_of_isOpenHoloEmbedding
    (b : Y → X) (hb : IsOpenHoloEmbedding n b) (C : Set X) :
    GermIdeal.pullback (m := n) b (vanishingIdeal (n := n) C) =
      vanishingIdeal (n := n) (b ⁻¹' C) := by
  obtain ⟨O, e, he⟩ := hb
  have hbEq : b = Subtype.val ∘ e := funext he
  rw [hbEq, ← BlowupRestrictOpen.pullback_vanishingIdeal_opens O e C]
  exact pullback_vanishingIdeal_of_biholomorphism e (Subtype.val ⁻¹' C)

end Hironaka.HironakaActualOpenEmbeddingVanishingIdeal
