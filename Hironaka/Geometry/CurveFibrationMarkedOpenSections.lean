import Hironaka.Geometry.CartierBoundarySectionDescent

/-! # Deduplicate the ORIGINAL closed sections and construct their actual dense distinctness open. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Hironaka.Geometry.CurveFibrationMarkedOpen
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equal ORIGINAL generic values force equality of the original closed section scheme morphisms. -/
theorem closedSections_eq_of_genericPoint_eq {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) (σ τ : S ⟶ X) [IsClosedImmersion τ]
    (hσ : σ ≫ f = 𝟙 S) (hτ : τ ≫ f = 𝟙 S)
    (hη : σ (genericPoint S) = τ (genericPoint S)) : σ = τ := by
  let a := CartierBoundarySection.closedLift τ σ ⟨genericPoint S, hη.symm⟩
  have ha : a ≫ τ = σ := CartierBoundarySection.closedLift_fac _ _ _
  have hi : a = 𝟙 S := by
    calc
      a = a ≫ (τ ≫ f) := by rw [hτ, Category.comp_id]
      _ = σ ≫ f := by rw [← Category.assoc, ha]
      _ = 𝟙 S := hσ
  calc
    σ = a ≫ τ := ha.symm
    _ = τ := by rw [hi, Category.id_comp]

/-- Reindex by actual ORIGINAL section morphisms, preserving all identities, closedness and image coverage. -/
theorem exists_deduplicated_closed_sections {X S : Scheme.{u}}
    (f : X ⟶ S) {ι : Type u} [Finite ι] (σ : ι → (S ⟶ X))
    (hσ : ∀ i, σ i ≫ f = 𝟙 S) [∀ i, IsClosedImmersion (σ i)] :
    ∃ (κ : Type u) (_ : Finite κ) (τ : κ → (S ⟶ X)),
      Function.Injective τ ∧ (∀ j, τ j ≫ f = 𝟙 S ∧ IsClosedImmersion (τ j)) ∧
      Set.range τ = Set.range σ ∧ ⋃ j, Set.range (τ j) = ⋃ i, Set.range (σ i) := by
  let κ := Set.range σ
  let τ : κ → (S ⟶ X) := Subtype.val
  let : Finite κ := Finite.of_surjective (fun i : ι => (⟨σ i, ⟨i, rfl⟩⟩ : κ)) (by
    rintro ⟨s, i, rfl⟩
    exact ⟨i, rfl⟩)
  refine ⟨κ, inferInstance, τ, Subtype.val_injective, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := j.property
    change j.val ≫ f = 𝟙 S ∧ IsClosedImmersion j.val
    rw [← hi]
    exact ⟨hσ i, inferInstance⟩
  · ext s
    constructor
    · rintro ⟨j, rfl⟩
      exact j.property
    · intro hs
      exact ⟨⟨s, hs⟩, rfl⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨i, hi⟩ := j.property
      apply Set.mem_iUnion.mpr
      refine ⟨i, y, ?_⟩
      change j.val y = x at hy
      rwa [hi]
    · intro hx
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨σ i, ⟨i, rfl⟩⟩, y, hy⟩

/-- Equality of ORIGINAL closed-section values is exactly a closed original-base condition. -/
theorem closedSections_equalizer_isClosed {X S : Scheme.{u}}
    (f : X ⟶ S) (σ τ : S ⟶ X) [IsClosedImmersion τ]
    (hσ : σ ≫ f = 𝟙 S) (hτ : τ ≫ f = 𝟙 S) :
    IsClosed {s : S | σ s = τ s} := by
  have he : {s : S | σ s = τ s} = σ ⁻¹' Set.range τ := by
    ext s
    constructor
    · intro hs
      exact ⟨s, hs.symm⟩
    · rintro ⟨t, ht⟩
      have hst : s = t := by
        have hσs : f (σ s) = s := by
          simpa using congrArg (fun m => m s) hσ
        have hτt : f (τ t) = t := by
          simpa using congrArg (fun m => m t) hτ
        exact hσs.symm.trans ((congrArg f ht).symm.trans hτt)
      simpa only [Set.mem_ofPred_eq, hst] using ht.symm
  rw [he]
  exact τ.isClosedEmbedding.isClosed_range.preimage σ.continuous

/-- An actual internally constructed dense BASE open separates the SAME finite distinct ORIGINAL sections. -/
theorem exists_nonempty_dense_sections_distinct_open {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) {ι : Type u} [Finite ι] (σ : ι → (S ⟶ X))
    (hσ : ∀ i, σ i ≫ f = 𝟙 S) [∀ i, IsClosedImmersion (σ i)]
    (hinj : Function.Injective σ) :
    ∃ V : S.Opens, Nonempty V ∧ Dense (V : Set S) ∧
      ∀ s : V, Function.Injective (fun i => σ i s.val) := by
  let B : Set S := ⋃ i : ι, ⋃ j : {j : ι // j ≠ i}, {s : S | σ i s = σ j.val s}
  have hB : IsClosed B := isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun j => closedSections_equalizer_isClosed f _ _ (hσ i) (hσ j.val)
  let V : S.Opens := ⟨Bᶜ, hB.isOpen_compl⟩
  have hη : genericPoint S ∈ V := by
    intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    exact j.property (hinj (closedSections_eq_of_genericPoint_eq f _ _ (hσ i) (hσ j.val) hj)).symm
  refine ⟨V, ⟨⟨genericPoint S, hη⟩⟩, V.isOpen.dense ⟨genericPoint S, hη⟩, ?_⟩
  intro s i j hij
  by_contra hne
  exact s.property (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨⟨j, Ne.symm hne⟩, hij⟩⟩)

end Hironaka.Geometry.CurveFibrationMarkedOpen
