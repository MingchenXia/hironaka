import Hironaka.Analytic.Unibranch.Resolution

/-!
# The same ORIGINAL modification after an ORIGINAL source isomorphism

Reuse the actual original isoLeft/isoHomeomorph APIs. These adapters
prove the original clauses with SAME target exceptional set and FULL
maps; no new space category or geometric milestone credit.
Blueprint FIRST: `original-bimeromorphic-source-iso.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

noncomputable section

/-- Actual original source isomorphisms preserve the full original
isomorphism-over condition on the SAME target set. -/
theorem IsIsoOver.precomp_iso {A B X : SourceReducedComplexSpace}
    {F : B ⟶ X} {U : Set X.obj.left} (hF : IsIsoOver F U) (E : A ≅ B) :
    IsIsoOver (E.hom ≫ F) U := by
  obtain ⟨V, j, hj, hrange, hjF, hrangeF⟩ := hF
  let e := isoLeft E
  let J := j ≫ e.inv
  have hJ : LocallyRingedSpace.IsOpenImmersion J :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ j hj e.inv (inferInstance)
  have hcomp : J ≫ (E.hom ≫ F).hom.left = j ≫ F.hom.left := by
    change (j ≫ e.inv) ≫ (e.hom ≫ F.hom.left) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  refine ⟨V, J, hJ, ?_, hcomp.symm ▸ hjF, ?_⟩
  · change range ((isoHomeomorph E).symm ∘ j.base) = _
    rw [range_comp, hrange, (isoHomeomorph E).image_symm]
    rfl
  · exact (congrArg (fun H : V ⟶ X.obj.left => range H.base) hcomp).trans hrangeF

/-- No original modification certificate is assumed for the composite;
properness, both thinness clauses and the full good-open map are derived. -/
theorem IsProperBimeromorphic.precomp_iso {A B X : SourceReducedComplexSpace}
    {F : B ⟶ X} (hF : IsProperBimeromorphic F) (E : A ≅ B) :
    IsProperBimeromorphic (E.hom ≫ F) := by
  obtain ⟨hp, Z, hZa, hZt, hpre, hiso⟩ := hF
  refine ⟨hp.comp (isoHomeomorph E).isProperMap, Z, hZa, hZt, ?_, hiso.precomp_iso E⟩
  change interior ((isoHomeomorph E) ⁻¹' (F.hom.left.base ⁻¹' Z)) = ∅
  rw [← (isoHomeomorph E).preimage_interior, hpre, preimage_empty]

end

end Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
