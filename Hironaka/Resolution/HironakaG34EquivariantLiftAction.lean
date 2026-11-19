import Hironaka.Resolution.HironakaG34ExtensionEquivariance

/-!
# The lifted action on an equivariant tower (first consumption brick, route note §3.3, §8.3(a))

Lane G34 (run 0080, round 10).  Blueprint: `hironaka-g34-resume-equivariant-lift-action.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §3 step 3, §8 item 3(a).

The consumption of EQ (route note §3) lets the data-preserving automorphisms of an open `V` (the coordinate rotations at a
Gamma point) act on the restriction of an equivariant tower over `V`.  This module records the formal content of that
action: lifts are unique, compose, the identity lifts to the identity, prefixes of equivariant towers are equivariant, and
EVERY lift (at every stage) carries the trace of the next centre to itself — so the centres over `V` are invariant under
the lifted action, the starting point of the toric lift.

## Main results

* `IsEquivariant.of_step`, `IsEquivariant.of_append`: prefixes of equivariant towers are equivariant;
* **`IsEquivariant.centre_iff`**: along an equivariant tower `T C`, every isomorphism `χ : T|_U ≅ T|_{U'}` over a
  data-preserving `φ` satisfies `χ p ∈ C ↔ p ∈ C`;
* `lift_eq`, `lift_trans`, **`lift_trans_eq`**, `lift_refl_eq`: uniqueness, composition and identity of lifts (the lifts
  of the automorphisms of one open form an action).

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34EquivariantLiftAction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-! ### Prefixes -/

/-- **A prefix of an equivariant tower is equivariant** (one step). -/
theorem IsEquivariant.of_step {N : Set X} {E : List (Set X)} {T : BlowupTower X Y} {C : Set Y} {π : Z → Y}
    {hπ : IsBlowupAlong n C π} (h : IsEquivariant N E (.step T C π hπ)) : IsEquivariant N E T := by
  intro U U' φ hφN hφE
  obtain ⟨χ₁, h₁⟩ := h U U' φ hφN hφE
  obtain ⟨χ, hχ, -, -⟩ := IsTowerIso.step_inv h₁
  exact ⟨χ, hχ⟩

/-- **A prefix of an equivariant tower is equivariant.** -/
theorem IsEquivariant.of_append {N : Set X} {E : List (Set X)} {T : BlowupTower X Y} :
    ∀ {Z : CMfd.{u} n} (R : BlowupTower Y Z), IsEquivariant N E (T.append R) → IsEquivariant N E T
  | _, .refl, h => h
  | _, .step R _ _ _, h => IsEquivariant.of_append R (IsEquivariant.of_step h)

/-! ### Centres -/

/-- **The centres of an equivariant tower are carried to themselves by EVERY lift**: if `T` followed by the blow-up along
`C` is equivariant for `(N, E)` and `φ : U ≅ U'` preserves `N` and every member of `E`, then every isomorphism
`χ : T|_U ≅ T|_{U'}` over `φ` satisfies `χ p ∈ C ↔ p ∈ C` (uniqueness of tower isomorphisms over a fixed base). -/
theorem IsEquivariant.centre_iff {N : Set X} {E : List (Set X)} {T : BlowupTower X Y} {C : Set Y} {π : Z → Y}
    {hπ : IsBlowupAlong n C π} (h : IsEquivariant N E (.step T C π hπ)) {U U' : Opens X}
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U')
    (hφN : ∀ p : U, ((φ p : U') : X) ∈ N ↔ (p : X) ∈ N)
    (hφE : ∀ H ∈ E, ∀ p : U, ((φ p : U') : X) ∈ H ↔ (p : X) ∈ H)
    {χ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U')} (hχ : IsTowerIso φ (restrict U T) (restrict U' T) χ) :
    ∀ p : openPreimage T U, ((χ p : openPreimage T U') : Y) ∈ C ↔ (p : Y) ∈ C := by
  obtain ⟨χ₁, h₁⟩ := h U U' φ hφN hφE
  obtain ⟨χ', hχ', -, hC⟩ := IsTowerIso.step_inv h₁
  obtain rfl := HironakaG34ExtensionEquivariance.IsTowerIso.eq_of_isTowerIso hχ' hχ
  intro p
  exact Set.ext_iff.mp hC p

/-! ### The action -/

section Action

variable {T : BlowupTower X Y} {U U' U'' : Opens X}

/-- **Lifts are unique.** -/
theorem lift_eq {φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U'}
    {χ χ' : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U')} (h : IsTowerIso φ (restrict U T) (restrict U' T) χ)
    (h' : IsTowerIso φ (restrict U T) (restrict U' T) χ') : χ = χ' :=
  HironakaG34ExtensionEquivariance.IsTowerIso.eq_of_isTowerIso h h'

/-- **Lifts compose**: the composite of a lift of `φ` and a lift of `ψ` is a lift of `φ` followed by `ψ`. -/
theorem lift_trans {φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U'}
    {ψ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U''}
    {χ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U')}
    {χ' : CMfd.of (n := n) (openPreimage T U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U'')}
    (h : IsTowerIso φ (restrict U T) (restrict U' T) χ) (h' : IsTowerIso ψ (restrict U' T) (restrict U'' T) χ') :
    IsTowerIso (φ.trans ψ) (restrict U T) (restrict U'' T) (χ.trans χ') :=
  IsTowerIso.trans h h'

/-- **The lifted action is multiplicative**: the lift of `φ` followed by `ψ` is the composite of the lifts. -/
theorem lift_trans_eq {φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U'}
    {ψ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U''}
    {χ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U')}
    {χ' : CMfd.of (n := n) (openPreimage T U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U'')}
    {χ'' : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U'')}
    (h : IsTowerIso φ (restrict U T) (restrict U' T) χ) (h' : IsTowerIso ψ (restrict U' T) (restrict U'' T) χ')
    (h'' : IsTowerIso (φ.trans ψ) (restrict U T) (restrict U'' T) χ'') : χ'' = χ.trans χ' :=
  lift_eq h'' (lift_trans h h')

/-- **The identity lifts to the identity.** -/
theorem lift_refl_eq
    {χ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (h : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) (restrict U T) (restrict U T) χ) :
    χ = Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) (openPreimage T U)) ∞ :=
  lift_eq h (IsTowerIso.refl_self (restrict U T))

end Action

end
end Hironaka.HironakaG34EquivariantLiftAction
