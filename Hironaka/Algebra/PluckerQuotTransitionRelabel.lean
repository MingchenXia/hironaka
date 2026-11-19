import Hironaka.Algebra.PluckerQuotRelations

/-!
# Original coordinate relabeling preserves the whole homogeneous minor ideal

The actual evaluation homomorphisms intertwine and the literal whole ideals
are carried to each other by an actual variable equivalence. Concrete Cramer
polynomials therefore belong to the same originally named projective ideal.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

universe u v w

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι η : Type u) [Fintype ι] [DecidableEq ι]
  {σ : Type v} {τ : Type w}

/-- The actual two polynomial evaluation maps agree on every original renamed coordinate. -/
theorem genericMinorEval_comp_rename (s : σ → ι → η) (t : τ → ι → η)
    (f : σ → τ) (h : ∀ j, t (f j) = s j) :
    (genericMinorEval R ι η τ t).comp (MvPolynomial.rename f) =
      genericMinorEval R ι η σ s := by
  ext j
  simp only [AlgHom.comp_apply, MvPolynomial.rename_X, genericMinorEval, MvPolynomial.aeval_X]
  rw [h]

/-- Actual original homogeneous relations are carried into the corresponding whole ideal. -/
theorem minorRelationIdeal_map_rename_le (s : σ → ι → η) (t : τ → ι → η)
    (f : σ → τ) (h : ∀ j, t (f j) = s j) :
    (minorRelationIdeal R ι η σ s).toIdeal.map (MvPolynomial.rename f).toRingHom ≤
      (minorRelationIdeal R ι η τ t).toIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro F hF
  change MvPolynomial.rename f F ∈ (minorRelationIdeal R ι η τ t).toIdeal
  apply mem_minorRelationIdeal R ι η τ t
  · obtain ⟨d, hd⟩ := hF.1
    exact ⟨d, hd.rename_isHomogeneous⟩
  · have he := AlgHom.congr_fun (genericMinorEval_comp_rename R ι η s t f h) F
    exact he.trans hF.2

/-- An actual coordinate equivalence carries the entire original homogeneous ideal exactly. -/
theorem minorRelationIdeal_map_rename_equiv (s : σ → ι → η) (t : τ → ι → η)
    (e : σ ≃ τ) (h : ∀ j, t (e j) = s j) :
    (minorRelationIdeal R ι η σ s).toIdeal.map (MvPolynomial.rename e).toRingHom =
      (minorRelationIdeal R ι η τ t).toIdeal := by
  apply le_antisymm (minorRelationIdeal_map_rename_le R ι η s t e h)
  have hinv := minorRelationIdeal_map_rename_le R ι η t s e.symm (fun j ↦ by
    simpa using (h (e.symm j)).symm)
  have he : (MvPolynomial.rename (R := R) e).comp (MvPolynomial.rename e.symm) =
      AlgHom.id R (MvPolynomial τ R) := by
    ext j
    simp
  intro F hF
  have hback := hinv (Ideal.mem_map_of_mem (MvPolynomial.rename e.symm).toRingHom hF)
  have hforward := Ideal.mem_map_of_mem (MvPolynomial.rename e).toRingHom hback
  have hval : MvPolynomial.rename e (MvPolynomial.rename e.symm F) = F :=
    AlgHom.congr_fun he F
  exact hval ▸ hforward

/-- The original named homogeneous ideal contains the actual Cramer polynomial with those names. -/
theorem renamed_cramerRelation_mem [Nonempty ι] (β : σ ≃ (ι → η)) (s t : ι → η) :
    MvPolynomial.rename β.symm (cramerRelation (R := R) s t) ∈
      (minorRelationIdeal R ι η σ β).toIdeal :=
  minorRelationIdeal_map_rename_le R ι η id β β.symm (fun j ↦ β.apply_symm_apply j)
    (Ideal.mem_map_of_mem (MvPolynomial.rename β.symm).toRingHom
      (cramerRelation_mem_minorRelationIdeal s t))

end Hironaka.Algebra.PluckerQuot
