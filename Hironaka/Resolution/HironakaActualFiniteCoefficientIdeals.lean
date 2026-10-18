/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Hironaka.Resolution.HironakaActualLocalCoefficientStrictGenerators

/-! Internally constructed genuine local coherent coefficient ideals of actual analytic families. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualFiniteCoefficientIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualCoefficientPresentationCentrePower InvertibleIdealQuotient

/-- The genuine principal original germ span of the actual function, without an extension hypothesis. -/
def actualPrincipalCoefficientIdeal (d : ℕ) (c : ComplexModel d → ℂ) :
    GermIdeal d (ComplexModel d) where
  mem x g := IsInSpanAt (n := d) (· = c) x g

/-- Its actual single generator proves coherence on precisely the real holomorphic domain. -/
theorem coherentOn_actualPrincipalCoefficientIdeal (d : ℕ) (c : ComplexModel d → ℂ)
    (U : Set (ComplexModel d)) (hU : IsOpen U)
    (hc : MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) c U) :
    CoherentOn (actualPrincipalCoefficientIdeal d c) U := by
  intro x hx
  refine ⟨U,hU,hx,subset_rfl,1,fun _ => c,fun _ => hc,?_⟩
  intro y hy g
  have hr : range (fun _ : Fin 1 => c)={c} := by
    ext f
    simp
  change IsInSpanAt (n := d) (· = c) y g ↔
    IsInSpanAt (n := d) (· ∈ range (fun _ : Fin 1 => c)) y g
  rw [hr]
  rfl

/-- The original generator belongs to its true ideal on its actual holomorphic domain. -/
theorem mem_actualPrincipalCoefficientIdeal (d : ℕ) (c : ComplexModel d → ℂ)
    (U : Set (ComplexModel d)) (hU : IsOpen U)
    (hc : MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) c U)
    (x : ComplexModel d) (hx : x ∈ U) :
    (actualPrincipalCoefficientIdeal d c).mem x c := by
  change IsInSpanAt (n := d) (fun f => f=c) x c
  exact isInSpanAt_self (n := d) (S := fun f => f=c) rfl
    (holomorphicAt_of_mdifferentiableOn hU hc hx)

/-- Actual analytic families internally supply genuine coherent low-coefficient ideals and whole Taylor identities. -/
theorem exists_actual_finite_local_coefficient_ideals (d t q : ℕ)
    {ι : Type*} [Fintype ι] (g : ι → HolGerm (ComplexModel (d+t))) :
    ∃ (U : Set (ComplexModel d)), IsOpen U ∧ (0 : ComplexModel d) ∈ U ∧
      ∃ (c : ι → (Fin t →₀ ℕ) → ComplexModel d → ℂ) (hc : ∀ i α, HolAt (c i α) 0),
        (∀ i α, normalExponentDegree α < q →
          MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) (c i α) U ∧
          CoherentOn (actualPrincipalCoefficientIdeal d (c i α)) U ∧
          (actualPrincipalCoefficientIdeal d (c i α)).mem 0 (c i α)) ∧
        (∀ i α, actualFormalNormalCoefficient (actualUnshiftedTaylorAlgHom (d+t) (g i)) α=
          actualUnshiftedTaylorAlgHom d (HolGerm.mk (c i α) (hc i α))) ∧
        ∀ i r α, normalExponentDegree α < r →
          MvPolynomial.coeff α (actualNormalTaylorPolynomial d t r (g i))=
            HolGerm.mk (c i α) (hc i α) := by
  obtain ⟨U,hU,h0,c,hc,hhol,he,hstable⟩ :=
    exists_actual_finite_coefficient_common_domain_with_Taylor d t q g
  refine ⟨U,hU,h0,c,hc,?_,he,hstable⟩
  intro i α hα
  exact ⟨hhol i α hα,coherentOn_actualPrincipalCoefficientIdeal d (c i α) U hU (hhol i α hα),
    mem_actualPrincipalCoefficientIdeal d (c i α) U hU (hhol i α hα) 0 h0⟩

end
end Hironaka.HironakaActualFiniteCoefficientIdeals
