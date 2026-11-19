import Hironaka.Resolution.HironakaG3UniverseSubmersionConjugate
import Hironaka.Resolution.HironakaSmoothSubmersionInvertibleQuotients
set_option autoImplicit false
open scoped Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseSubmersionConjugate
open BlowupTowers HironakaSmoothSubmersionInvertibleQuotients
noncomputable section
variable {n : ℕ}
/-- Pullback along an actual cross-universe biholomorphism preserves invertibility. -/
theorem diffeo_pullback_invertible {A : CMfd.{u} n} {B : CMfd.{v} n}
    (e : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A)
    {I : Hironaka.HolomorphicIdealSheaves.GermIdeal n A} (hI : I.IsInvertible) :
    (Hironaka.HolomorphicIdealSheaves.GermIdeal.pullback (m := n) e I).IsInvertible :=
  isInvertible_pullback_submersion (diffeo_isSubmersion e) hI

end
end Hironaka.G3UniverseSubmersionConjugate
