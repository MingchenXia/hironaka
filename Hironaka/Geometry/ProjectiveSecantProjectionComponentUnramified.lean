import Hironaka.Geometry.ProjectiveSecantProjectionUnramifiedOpen
import Hironaka.Geometry.ProjectiveSecantProjectionComponentBirational

/-!
# Actual original componentwise stalks produce a dense formally unramified source open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original formally unramified source restrictions glue over their entire actual original union. -/
theorem original_formallyUnramified_source_iSup {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type*} (A : I → X.Opens) (hA : ∀ a, FormallyUnramified ((A a).ι ≫ f)) :
    FormallyUnramified ((⨆ a, A a).ι ≫ f) := by
  let U : X.Opens := ⨆ a, A a
  have hc : (⨆ a, U.ι ⁻¹ᵁ A a) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp x.property
    exact Opens.mem_iSup.mpr ⟨a, ha⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @FormallyUnramified) (fun a => U.ι ⁻¹ᵁ A a) hc
  intro a
  let b := U.ι.resLE (A a) (U.ι ⁻¹ᵁ A a) le_rfl
  have ht : (U.ι ⁻¹ᵁ A a).ι ≫ (U.ι ≫ f) = b ≫ ((A a).ι ≫ f) := by
    simp only [b, ← Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [ht]
  exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance (hA a)

/-- Actual original unramified stalk points on every original component internally produce a dense original unramified source open, without any reducedness or integrality assumption. -/
theorem exists_dense_formallyUnramified_open_of_component_stalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hpoints : ∀ C ∈ irreducibleComponents X, ∃ x ∈ C, (f.stalkMap x).hom.FormallyUnramified) :
    ∃ A : X.Opens, Dense (A : Set X) ∧ FormallyUnramified (A.ι ≫ f) := by
  let I := {C : Set X // C ∈ irreducibleComponents X}
  choose x hx hfu using (fun C : I => hpoints C.1 C.2)
  choose A hxA hA using (fun C : I => exists_formallyUnramified_open_of_stalk f (x C) (hfu C))
  refine ⟨⨆ C : I, A C, ?_, original_formallyUnramified_source_iSup f A hA⟩
  apply original_open_dense_of_meets_components
  intro C hC
  exact ⟨x ⟨C, hC⟩, hx ⟨C, hC⟩, (le_iSup A ⟨C, hC⟩) (hxA ⟨C, hC⟩)⟩

end Hironaka.Geometry.ProjectiveSecant
