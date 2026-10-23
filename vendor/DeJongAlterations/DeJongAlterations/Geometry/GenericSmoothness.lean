import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Native smooth loci and generic smoothness

The perfect-field case of de Jong 2.10, with an actual dense source open.
The regular-locus equivalence and the imperfect-field separably-generated
case are separate obligations.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace DeJongAlterations.Geometry.GenericSmoothness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- The actual morphism on its smooth locus is smooth. -/
theorem smooth_smoothLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Smooth (f.smoothLocus.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact f.smoothLocus.ι_preimage_self

/-- A reduced scheme locally of finite type over a perfect field has a dense smooth source open. -/
theorem exists_dense_smooth_open_of_perfectField {k : Type u} [Field k] [PerfectField k]
    [IsReduced X] (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    ∃ U : X.Opens, Dense (U : Set X) ∧ Smooth (U.ι ≫ p) := by
  exact ⟨p.smoothLocus, p.dense_smoothLocus_of_perfectField, smooth_smoothLocus p⟩

end DeJongAlterations.Geometry.GenericSmoothness
