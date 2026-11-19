import Hironaka.Analytic.PotentialTheory.Basic
import Hironaka.Analytic.HolomorphicPullback

/-!
# Source holomorphic pullback dichotomy

The main branch now proves singular holomorphic pullback from actual radial
regularizations and smooth Levi naturality. Reuse that checked producer and
retain the source's non-bottom alternative explicitly. The namespace of an
import does not substitute for a transitive axiom audit.
-/

namespace Hironaka.Analytic.PotentialTheory

open Set
open Hironaka

/-- The actual singular pullback satisfies the genuine disc criterion. -/
theorem discPshOn_comp_holomorphic {k n : ℕ}
    {F : ComplexModel k → ComplexModel n} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : DifferentiableOn ℂ F U)
    (hFV : MapsTo F U V) (hu : PSHOn u V) :
    Hironaka.DiscPshOn (fun x ↦ u (F x)) U :=
  (Hironaka.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    hU hF hFV (hu.disc.plurisubharmonicOn hV)).discPshOn

/-- SGPT `prop:func_domain`: source PSH pulls back to source PSH or the
identically bottom function on the actual source domain. -/
theorem pshOn_comp_holomorphic_or_eqOn_bot {k n : ℕ}
    {F : ComplexModel k → ComplexModel n} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : DifferentiableOn ℂ F U)
    (hFV : MapsTo F U V) (hu : PSHOn u V) :
    PSHOn (fun x ↦ u (F x)) U ∨ EqOn (fun x ↦ u (F x)) (fun _ ↦ ⊥) U := by
  classical
  by_cases hn : ∃ x ∈ U, u (F x) ≠ ⊥
  · exact Or.inl ⟨discPshOn_comp_holomorphic hU hV hF hFV hu, hn⟩
  · right
    intro x hx
    by_contra h
    exact hn ⟨x, hx, h⟩

/-- The two source alternatives are disjoint, including on empty domains. -/
theorem not_pshOn_and_eqOn_bot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} :
    ¬ (PSHOn u U ∧ EqOn u (fun _ ↦ ⊥) U) := by
  rintro ⟨hu, hb⟩
  obtain ⟨x, hx, hn⟩ := hu.nontrivial
  exact hn (hb hx)

end Hironaka.Analytic.PotentialTheory
