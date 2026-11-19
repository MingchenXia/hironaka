import Hironaka.Algebra.ModuleFlatteningMinorsChart

/-!
# An internally constructed nonzero minor ideal flattens the actual finite-module pure transform

Only the original domain and original finite module are inputs. Generators,
generic basis, common denominator, integral matrix, nonzero minor ideal and
all actual chart bases are constructed inside the proof.
-/

noncomputable section

open Module
open scoped TensorProduct

namespace Hironaka.Algebra.ModuleFlatteningMinorsExistence

open ModuleFlatteningMinors ModuleFlatteningMinorsCoordinates
  ModuleFlatteningMinorsPureTransform ModuleFlatteningMinorsChart

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite module internally constructs a nonzero finitely generated actual minor ideal
whose original minor blowup charts have free actual canonical pure transform, with literal
original module-generator bases. No transform basis or flattening certificate is an input. -/
theorem exists_nonzero_minorIdeal_free_pureTransform
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    ∃ (n r : ℕ) (m : Fin n → M) (A : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal A).FG ∧ minorIdeal A ≠ ⊥ ∧
      ∀ (s : Fin r → Fin n), columnMinor A s ≠ 0 →
        ∃ B : Basis (Fin r) (affineBlowupFractionChart (minorIdeal A) (columnMinor A s))
          (pureTransform R M (affineBlowupFractionChart (minorIdeal A) (columnMinor A s))),
          ∀ j, (B j : FractionRing R ⊗[R] M) = (1 : FractionRing R) ⊗ₜ[R] m (s j) := by
  classical
  obtain ⟨n, r, m, b, s₀, δ, A, hm, hs₀, hδ, hcoord, hminor⟩ :=
    exists_integral_generic_coordinates R M
  have hfg : (minorIdeal A).FG := Submodule.fg_span (Set.finite_range (columnMinor A))
  have hI : minorIdeal A ≠ ⊥ := by
    intro hzero
    have hmem := columnMinor_mem_minorIdeal A s₀
    rw [hzero, Ideal.mem_bot] at hmem
    exact hminor hmem
  exact ⟨n, r, m, A, hm, hfg, hI, fun s hs ↦
    exists_basis_pureTransform_minorChart m hm b δ A hδ hcoord s hs⟩


/-- Native freeness, finiteness and rank of the actual canonical pure transform on
all internally constructed nonzero minor charts. -/
theorem exists_nonzero_minorIdeal_free_finite_rank_pureTransform
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    ∃ (n r : ℕ) (m : Fin n → M) (A : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal A).FG ∧ minorIdeal A ≠ ⊥ ∧
      ∀ (s : Fin r → Fin n), columnMinor A s ≠ 0 →
        let S := affineBlowupFractionChart (minorIdeal A) (columnMinor A s)
        Module.Free S (pureTransform R M S) ∧ Module.Finite S (pureTransform R M S) ∧
          Module.finrank S (pureTransform R M S) = r := by
  obtain ⟨n, r, m, A, hm, hfg, hI, hB⟩ := exists_nonzero_minorIdeal_free_pureTransform R M
  refine ⟨n, r, m, A, hm, hfg, hI, fun s hs ↦ ?_⟩
  obtain ⟨B, hBimage⟩ := hB s hs
  exact ⟨Module.Free.of_basis B, Module.Finite.of_basis B,
    (Module.finrank_eq_card_basis B).trans (Fintype.card_fin r)⟩

end Hironaka.Algebra.ModuleFlatteningMinorsExistence
