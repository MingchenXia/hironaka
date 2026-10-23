import DeJongAlterations.Geometry.ProjectiveIdeal
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Same-degree forms as an actual nonempty finite family

The native projective ideal representation supplies a finite set. Enumerating
that set and adjoining the zero form produces Fin(m+1) without a nonemptiness
assumption or an additional representation certificate.
-/

open AlgebraicGeometry MvPolynomial

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

open ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {X : Scheme.{u}}

/-- The original ideal has an internally produced nonempty finite same-degree form family. -/
theorem exists_fin_sameDegree_representation (D : X.IdealSheafData)
    (j : X ⟶ projectiveSpace R n) [IsClosedImmersion j] :
    ∃ (m d : ℕ) (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
      (J : HomogeneousIdeal (ProjectiveGrading R n)),
      (∀ a, (F a).IsHomogeneous d) ∧ Ideal.span (Set.range F) = J.toIdeal ∧
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j = D := by
  classical
  obtain ⟨d, s, J, hd, hs, hD⟩ :=
    exists_sameDegree_homogeneous_generators_of_isClosedImmersion D j
  let e := (Fintype.equivFin s).symm
  let g : Fin (Fintype.card s) → MvPolynomial (Fin (n + 1)) R := fun a => (e a).1
  have hg : Set.range g = (s : Set (MvPolynomial (Fin (n + 1)) R)) := by
    ext P
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hP
      refine ⟨e.symm ⟨P, hP⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨P, hP⟩)
  refine ⟨Fintype.card s, d, Fin.cons 0 g, J, ?_, ?_, hD⟩
  · intro a
    refine Fin.cases (MvPolynomial.isHomogeneous_zero (Fin (n + 1)) R d) ?_ a
    intro b
    exact hd _ (e b).2
  · rw [Fin.range_cons, Ideal.span_insert_zero, hg]
    exact hs

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
