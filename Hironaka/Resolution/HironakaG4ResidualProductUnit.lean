import Hironaka.Resolution.HironakaG4RelativeGeneratorUnit
import Hironaka.Resolution.HironakaSharpActualRelativeProductOrder

/-! Unit coefficient from the actual relative residual-factor identity. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ResidualProductUnit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan DivisorExponentAlong MonomialPartAlong
  HironakaG4RelativeGeneratorUnit HironakaSharpActualRelativeProductOrder
  BlowupTowers RestrictedIdealExtension

variable {n : ℕ} {X : CMfd.{u} n}

/-- The residual product identity and local relative generators imply the
selected original generator equals a unit times their product on the carrier. -/
theorem unit_of_relative_residual_product {N : Set X} {I D J : GermIdeal n X}
    {x : X} {f d r : X → ℂ}
    (hf : HolomorphicAt n f x) (hd : HolomorphicAt n d x) (hr : HolomorphicAt n r x)
    (hnz : IsNonzeroAlongAt N I x)
    (hfactor : I = restrictOn n N (D.mul J))
    (hI : ∀ g, I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = f) x g)
    (hD : ∀ g, D.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = d) x g)
    (hJ : ∀ g, J.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = r) x g) :
    ∃ a : X → ℂ, HolomorphicAt n a x ∧ a x ≠ 0 ∧
      ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * (d y * r y) := by
  have hProd : ∀ g, I.mem x g ↔ HolomorphicAt n g x ∧
      IsInSpanOnAt (n := n) N (· = d * r) x g := by
    intro g
    rw [hfactor]
    exact restrictOn_mul_relative_principal_mem_iff hd hr hD hJ g
  obtain ⟨a, ha, hax, heq⟩ := exists_unit_of_same_nonzero_relative_generator hf (hd.mul hr) hnz hI hProd
  exact ⟨a, ha, hax, heq⟩

end
end Hironaka.HironakaG4ResidualProductUnit
