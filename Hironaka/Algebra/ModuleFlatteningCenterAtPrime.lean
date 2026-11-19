import Hironaka.Algebra.ModuleFlatteningCenterBasis
import Hironaka.Algebra.ModuleFlatteningCenterLocalization
import Hironaka.Algebra.ModuleFlatteningCenterSpreading

/-!
# The same original minor ideal is nonzero principal at every actual original free point

Original generic coordinates are retained. Native local basis selection
and the actual matrix factorization internally choose an original minor
generating the exact localized original ideal; no principal ideal or
isomorphism certificate is supplied.
-/

noncomputable section

open Module
open scoped TensorProduct

namespace Hironaka.Algebra.ModuleFlatteningCenter

open ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R M : Type u} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M]

/-- At an actual original free point, one internally selected original minor
generates the exact original localized maximal-minor ideal and is nonzero. -/
theorem exists_atPrime_nonzero_minor_generator
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (V : Matrix (Fin r) (Fin n) R)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (V i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s₀ : Fin r → Fin n) (hs₀ : columnMinor V s₀ ≠ 0)
    (p : Ideal R) [p.IsPrime]
    [Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] M)] :
    ∃ s : Fin r → Fin n, columnMinor V s ≠ 0 ∧
      (minorIdeal V).map (algebraMap R (Localization.AtPrime p)) =
        Ideal.span ({algebraMap R (Localization.AtPrime p) (columnMinor V s)} :
          Set (Localization.AtPrime p)) := by
  let := atPrimeFractionAlgebra p
  let := atPrimeFractionScalarTower p
  let := atPrimeFraction_isFractionRing p
  obtain ⟨s, c, hc⟩ := exists_original_generator_basis (S := Localization.AtPrime p) m hm b
  have hf := coordinateMatrix_factorization m b δ V hcoord s c hc
    (IsFractionRing.injective (Localization.AtPrime p) (FractionRing R))
  have hprincipal := minorIdeal_eq_span_of_selected_factorization
    (V.map (algebraMap R (Localization.AtPrime p))) s
    (fun j a ↦ c.repr ((1 : Localization.AtPrime p) ⊗ₜ[R] m a) j) hf
  rw [minorIdeal_map, columnMinor_map] at hprincipal
  refine ⟨s, ?_, hprincipal⟩
  intro hs
  have hmem := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p))
    (columnMinor_mem_minorIdeal V s₀)
  rw [hprincipal, hs, map_zero, Ideal.span_singleton_zero, Ideal.mem_bot] at hmem
  exact hs₀ (IsLocalization.injective (Localization.AtPrime p)
    (primeCompl_le_nonZeroDivisors p) (by simpa using hmem))

/-- Every actual original free point has an actual original principal neighborhood
where the same original minor ideal is exactly nonzero principal. -/
theorem exists_away_nonzero_minor_generator
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (V : Matrix (Fin r) (Fin n) R)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (V i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s₀ : Fin r → Fin n) (hs₀ : columnMinor V s₀ ≠ 0)
    (p : Ideal R) [p.IsPrime]
    [Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] M)] :
    ∃ (a : R) (s : Fin r → Fin n), a ∉ p ∧ columnMinor V s ≠ 0 ∧
      (minorIdeal V).map (algebraMap R (Localization.Away a)) =
        Ideal.span ({algebraMap R (Localization.Away a) (columnMinor V s)} :
          Set (Localization.Away a)) := by
  obtain ⟨s, hs, hI⟩ := exists_atPrime_nonzero_minor_generator m hm b δ V hcoord s₀ hs₀ p
  obtain ⟨a, hap, ha⟩ := exists_away_minorIdeal_eq_span_of_atPrime V p s hI
  exact ⟨a, s, hap, hs, ha⟩

end Hironaka.Algebra.ModuleFlatteningCenter
