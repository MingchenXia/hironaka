import DeJongAlterations.Geometry.ModificationCenterBirational
import DeJongAlterations.Geometry.ModificationCenterBaseChange

/-!
# Actual centers and composition calculus for native modifications

The center is the exact closed nonisomorphism subset of the original target.
The native birational witness internally proves its complement dense and
nonempty. Under composition its center lies in the actual closed union of
the second center and the image of the first center.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ModificationCenter

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : Scheme.{u}}

/-- The exact intrinsic center is empty precisely for an actual global isomorphism. -/
theorem center_eq_bot_iff (f : X ⟶ Y) : center f = ⊥ ↔ IsIso f := by
  constructor
  · intro h
    have H := (center_le_iff f ⊥).mp h.le
    have he : (⊥ : Closeds Y).compl = ⊤ := by
      ext y
      simp [TopologicalSpace.Closeds.compl]
    rw [he] at H
    have ht : IsIso (f ∣_ ⊤) := H
    change (MorphismProperty.isomorphisms Scheme) f
    apply IsZariskiLocalAtTarget.of_iSup_eq_top (fun _ : PUnit.{0} => ⊤) (by simp)
    intro _
    exact ht
  · intro h
    have := h
    exact center_eq_bot_of_isIso f

/-- The maximal actual isomorphism open of a native modification is dense. -/
theorem dense_isomorphismOpen (f : X ⟶ Y) [IsModification f] :
    Dense (isomorphismOpen f : Set Y) := by
  obtain ⟨U, hd, hi⟩ := exists_dense_isomorphism_open f
  have := hi
  exact hd.mono (le_isomorphismOpen_of_isIso f U)

/-- Its actual center complement is nonempty, internally from the integral target. -/
theorem nonempty_isomorphismOpen (f : X ⟶ Y) [hf : IsModification f] :
    Nonempty (isomorphismOpen f) := by
  let := hf.targetIntegral
  exact Set.nonempty_coe_sort.mpr (dense_isomorphismOpen f).nonempty

/-- The exact nonisomorphism center of a native modification is a proper closed subset. -/
theorem center_ne_top (f : X ⟶ Y) [hf : IsModification f] : center f ≠ ⊤ := by
  let := hf.targetIntegral
  obtain ⟨y, hy⟩ := (dense_isomorphismOpen f).nonempty
  intro heq
  have hc : y ∈ center f := by rw [heq]; trivial
  exact hc hy

/-- The actual center complement itself is a nonempty dense isomorphism open. -/
theorem modification_complement (f : X ⟶ Y) [IsModification f] :
    Nonempty (center f).compl ∧ Dense ((center f).compl : Set Y) ∧
      IsIso (f ∣_ (center f).compl) := by
  rw [center_compl]
  exact ⟨nonempty_isomorphismOpen f, dense_isomorphismOpen f, inferInstance⟩

/-- The genuine closed union controlling the center of the original composition. -/
def compositionBound (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed g] : Closeds Z :=
  center g ⊔ ⟨g '' (center f : Set Y), g.isClosedMap _ (center f).isClosed⟩

/-- The original composition is an isomorphism off the actual closed union of the
second center and the image of the first center. -/
theorem isIso_comp_compositionBound_compl (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed g] : IsIso ((f ≫ g) ∣_ (compositionBound f g).compl) := by
  have hg : (compositionBound f g).compl ≤ isomorphismOpen g := by
    intro z hz
    by_contra hnot
    exact hz (Or.inl hnot)
  have hf : g ⁻¹ᵁ (compositionBound f g).compl ≤ isomorphismOpen f := by
    intro y hy
    by_contra hnot
    exact hy (Or.inr ⟨y, hnot, rfl⟩)
  have := (le_isomorphismOpen_iff g _).mp hg
  have := (le_isomorphismOpen_iff f _).mp hf
  rw [morphismRestrict_comp]
  infer_instance

/-- The exact native center of a composition is contained in the genuine closed center union. -/
theorem center_comp_le_compositionBound (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed g] :
    center (f ≫ g) ≤ compositionBound f g :=
  (center_le_iff _ _).mpr (isIso_comp_compositionBound_compl f g)

/-- Set-theoretic form of the native center union containment. -/
theorem center_comp_subset_union (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed g] :
    (center (f ≫ g) : Set Z) ⊆ (center g : Set Z) ∪ g '' (center f : Set Y) :=
  center_comp_le_compositionBound f g

/-- Centers lying over the same actual closed target set remain there under composition. -/
theorem center_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed g]
    (C : Closeds Z) (hg : center g ≤ C)
    (hf : (center f : Set Y) ⊆ g ⁻¹' (C : Set Z)) : center (f ≫ g) ≤ C := by
  apply (center_comp_le_compositionBound f g).trans
  intro z hz
  rcases hz with hz | ⟨y, hy, rfl⟩
  · exact hg hz
  · exact hf hy

/-- The original native composition is genuinely an isomorphism on the entire
complement of any closed set containing both actual centers in the proper way. -/
theorem isIso_comp_compl_of_centers (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed g]
    (C : Closeds Z) (hg : center g ≤ C)
    (hf : (center f : Set Y) ⊆ g ⁻¹' (C : Set Z)) : IsIso ((f ≫ g) ∣_ C.compl) :=
  (center_le_iff _ _).mp (center_comp_le f g C hg hf)

end DeJongAlterations.Geometry.ModificationCenter
