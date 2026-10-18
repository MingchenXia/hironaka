/- Complete original prerequisites; statements and mathematical proofs are unchanged. -/
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false



open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealTowerTransport

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.NormalCrossingsInvariance
  Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism
  Hironaka.GermIdealPullbackCalculus

noncomputable section



section Transport


variable {n : ℕ}


variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)


/-- **The transported tower has the same length.** -/
theorem length_transport : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (transport Φ T).tower.length = T.length
  | _, .refl => rfl
  | _, .step T _ _ _ => congrArg (· + 1) (length_transport T)

/-- **The stages correspond by biholomorphisms commuting with the projections**:
`Φ ∘ T'.proj = T.proj ∘ back`. -/
theorem proj_transport : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → ∀ p : (transport Φ T).target,
    Φ ((transport Φ T).tower.proj p) = T.proj ((transport Φ T).back p)
  | _, .refl, _ => rfl
  | _, .step T _ π _, p => by
      have := proj_transport T ((transport Φ T).back.symm (π p))
      rw [Diffeomorph.apply_symm_apply] at this
      exact this

end Transport


end


end Hironaka.MarkedIdealTowerTransport
