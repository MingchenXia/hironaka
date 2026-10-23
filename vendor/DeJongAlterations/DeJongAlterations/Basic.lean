import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Properties

/-!
# Alterations of schemes

Native scheme foundations for de Jong 1996, Definition 2.20.
-/

open CategoryTheory TopologicalSpace

universe u

namespace DeJongAlterations

open AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- Finiteness over some nonempty open of the target (de Jong 2.20). -/
def IsGenericallyFinite (f : X ⟶ Y) : Prop :=
  ∃ U : Y.Opens, Nonempty U ∧ IsFinite (f ∣_ U)

/-- An alteration between integral schemes. In de Jong 2.20 the target is
Noetherian; the same morphism condition makes sense without that hypothesis. -/
class IsAlteration (f : X ⟶ Y) : Prop extends IsProper f, IsDominant f where
  sourceIntegral : IsIntegral X
  targetIntegral : IsIntegral Y
  genericallyFinite : IsGenericallyFinite f

/-- Étaleness on a dense open of the source, exactly as in de Jong 2.6. -/
def IsGenericallyEtale (f : X ⟶ Y) : Prop :=
  ∃ U : X.Opens, Dense (U : Set X) ∧ Etale (U.ι ≫ f)

/-- De Jong's convention for a variety (2.9) does not require geometric integrality. -/
class IsVariety {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) : Prop extends
    IsIntegral X, IsSeparated p, LocallyOfFiniteType p, QuasiCompact p

theorem isGenericallyFinite_of_isFinite (f : X ⟶ Y) [Nonempty Y] [IsFinite f] :
    IsGenericallyFinite f := by
  refine ⟨⊤, ?_, inferInstance⟩
  exact ⟨⟨Classical.choice inferInstance, trivial⟩⟩

/-- A finite morphism can be prepended to a generically finite morphism. -/
theorem IsGenericallyFinite.comp_finite (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] (hg : IsGenericallyFinite g) : IsGenericallyFinite (f ≫ g) := by
  obtain ⟨U, hU, hfin⟩ := hg
  have hfU : IsFinite (f ∣_ (g ⁻¹ᵁ U)) := inferInstance
  refine ⟨U, hU, ?_⟩
  rw [morphismRestrict_comp]
  exact MorphismProperty.comp_mem (@IsFinite) _ _ hfU hfin

theorem isAlteration_of_isFinite (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsFinite f] [IsDominant f] : IsAlteration f where
  sourceIntegral := inferInstance
  targetIntegral := inferInstance
  genericallyFinite := isGenericallyFinite_of_isFinite f

instance isAlteration_id (X : Scheme.{u}) [IsIntegral X] : IsAlteration (𝟙 X) :=
  isAlteration_of_isFinite _

/-- Alteration after a finite dominant map, a first case of the alteration calculus. -/
theorem IsAlteration.comp_finite (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsFinite f] [IsDominant f] [hg : IsAlteration g] :
    IsAlteration (f ≫ g) where
  sourceIntegral := inferInstance
  targetIntegral := hg.targetIntegral
  genericallyFinite := hg.genericallyFinite.comp_finite f g

theorem IsAlteration.surjective (f : X ⟶ Y) [IsAlteration f] :
    Function.Surjective f :=
  f.surjective

theorem IsAlteration.preimage_ne_univ (f : X ⟶ Y) [IsAlteration f]
    {T : Set Y} (hT : T ≠ Set.univ) : f ⁻¹' T ≠ Set.univ := by
  intro h
  apply hT
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨x, rfl⟩ := IsAlteration.surjective f y
  have hx : x ∈ f ⁻¹' T := h ▸ Set.mem_univ x
  exact hx

theorem IsAlteration.preimage_proper_closed (f : X ⟶ Y) [IsAlteration f]
    {T : Set Y} (hclosed : IsClosed T) (hT : T ≠ Set.univ) :
    IsClosed (f ⁻¹' T) ∧ f ⁻¹' T ≠ Set.univ :=
  ⟨hclosed.preimage f.continuous, IsAlteration.preimage_ne_univ f hT⟩

theorem isGenericallyEtale_of_etale (f : X ⟶ Y) [Etale f] :
    IsGenericallyEtale f := by
  exact ⟨⊤, by simp, inferInstance⟩

end DeJongAlterations
