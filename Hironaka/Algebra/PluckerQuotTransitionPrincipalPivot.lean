import Hironaka.Algebra.PluckerQuotTransitionLocalPivotBasis
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.FinitePresentation

/-!
# SAME original quotient columns give genuine principal pivot neighborhoods

Every selected original column and the actual entire selected-column map are
retained. Native localization uniqueness and same-map inversion openness
produce the actual neighborhood; no pivot or local frame is an input.
-/

noncomputable section

open Module

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w

variable {A : Type u} [CommRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  [Module.FinitePresentation A M] [Module.Flat A M]
  {E : Type w} [Fintype E] [DecidableEq E]

/-- EVERY original prime has an actual principal neighborhood where the SAME finite subfamily of ORIGINAL quotient columns gives a bijective native localized map, of actual native stalk rank. -/
theorem originalQuotient_exists_principalPivot (q : (E → A) →ₗ[A] M)
    (hq : Function.Surjective q) (p : PrimeSpectrum A) :
    ∃ (I : Type w) (_ : Finite I) (a : I ↪ E) (g : A),
      g ∉ p.asIdeal ∧ Nat.card I = Module.rankAtStalk M p ∧
        Function.Bijective (LocalizedModule.map (Submonoid.powers g)
          (Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A))))) := by
  classical
  let S := p.asIdeal.primeCompl
  let Aₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule S M
  let f : M →ₗ[A] Mₚ := LocalizedModule.mkLinearMap S M
  let v : E → M := fun i => q (Pi.single i (1 : A))
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    have h := congrArg (Submodule.map q) (Pi.basisFun A E).span_eq
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Pi.basisFun_apply, Submodule.map_top, LinearMap.range_eq_top.mpr hq, v] using h
  let vₚ : E → Mₚ := f ∘ v
  have hvₚ : Submodule.span Aₚ (Set.range vₚ) = ⊤ := by
    simpa only [← Set.range_comp] using span_eq_top_of_isLocalizedModule Aₚ S f hv
  obtain ⟨I, a, b, hb⟩ := Module.exists_basis_of_span_of_flat vₚ hvₚ
  let : Finite I := Module.Finite.finite_basis b
  have ha : Function.Injective a := by
    intro i j h
    apply b.injective
    rw [hb i, hb j, h]
  let c : (I →₀ A) →ₗ[A] M := Finsupp.linearCombination A (v ∘ a)
  let fI : (I →₀ A) →ₗ[A] I →₀ Aₚ :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A Aₚ)
  have hm : IsLocalizedModule.map S fI f c = b.repr.symm.toLinearMap.restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext S fI f
    apply (Finsupp.basisSingleOne (ι := I) (R := A)).ext
    intro i
    change IsLocalizedModule.map S fI f c (fI (Finsupp.single i 1)) =
      b.repr.symm (fI (Finsupp.single i 1))
    rw [IsLocalizedModule.map_apply]
    simp only [c, Finsupp.linearCombination_single, one_smul, fI,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Algebra.linearMap_apply, map_one, Basis.repr_symm_single_one, hb]
    rfl
  have hc : Function.Bijective (IsLocalizedModule.map S fI f c) := by
    rw [hm]
    exact b.repr.symm.bijective
  obtain ⟨g, hg, hgc⟩ := Module.FinitePresentation.exists_notMem_bijective c p.asIdeal fI f hc
  have hcard : Nat.card I = Module.rankAtStalk M p :=
    (Module.finrank_eq_nat_card_basis b).symm
  exact ⟨I, inferInstance, ⟨a, ha⟩, g, hg, hcard, hgc⟩

end Hironaka.Algebra.PluckerQuotTransition
