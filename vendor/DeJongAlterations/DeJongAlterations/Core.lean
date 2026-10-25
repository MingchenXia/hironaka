import DeJongAlterations.Basic
import DeJongAlterations.Regular

/-!
# The regular alteration core and its dimension-zero case

The general proposition below is a proof target, not an assumption or a theorem.
It omits the compactification and prescribed boundary in Theorem 4.1.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace DeJongAlterations

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The regular-alteration conclusion, without the compactification or boundary. -/
def HasRegularAlteration (p : X ⟶ Spec (.of k)) : Prop :=
  ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (f : Y ⟶ X),
    IsVariety q ∧ f ≫ p = q ∧ IsAlteration f ∧ IsRegularScheme Y

/-- A generically étale regular alteration, still omitting the compactification and boundary. -/
def HasRegularGenericallyEtaleAlteration (p : X ⟶ Spec (.of k)) : Prop :=
  ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (f : Y ⟶ X),
    IsVariety q ∧ f ≫ p = q ∧ IsAlteration f ∧ IsRegularScheme Y ∧ IsGenericallyEtale f

/-- An unproved general target. Defining this proposition does not prove it. -/
def RegularAlterationTheorem (k : Type u) [Field k] : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)), IsVariety p → HasRegularAlteration p

/-- The dimension-zero case of the regular-alteration core is realized by the identity. -/
theorem hasRegularGenericallyEtaleAlteration_of_topologicalKrullDim_le_zero
    (p : X ⟶ Spec (.of k)) [IsVariety p] (hdim : topologicalKrullDim X ≤ 0) :
    HasRegularGenericallyEtaleAlteration p := by
  refine ⟨X, p, 𝟙 X, inferInstance, Category.id_comp p, inferInstance, ?_, ?_⟩
  · exact isRegularScheme_of_topologicalKrullDim_le_zero X hdim
  · exact isGenericallyEtale_of_etale _

theorem hasRegularAlteration_of_topologicalKrullDim_le_zero
    (p : X ⟶ Spec (.of k)) [IsVariety p] (hdim : topologicalKrullDim X ≤ 0) :
    HasRegularAlteration p := by
  obtain ⟨Y, q, f, hq, hcomm, hf, hreg, _⟩ :=
    hasRegularGenericallyEtaleAlteration_of_topologicalKrullDim_le_zero p hdim
  exact ⟨Y, q, f, hq, hcomm, hf, hreg⟩

end DeJongAlterations
