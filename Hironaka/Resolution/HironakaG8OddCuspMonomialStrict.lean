import Hironaka.Resolution.HironakaG8OddCuspStrictChart
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Blowup.BlowupMonomialCharts

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8OddCuspMonomialStrict
noncomputable section

open Hironaka.BlowupSequences HironakaBaseChange BlowupRestrictOpen
  BlowupExistenceOriginModel BlowupExistenceOriginGenerator BlowupMonomialCharts
  StrictTransformComposition HironakaG8OddCuspStrictChart HironakaG8OddCuspVanishingStalk

/-- The actual chart introduction map is an open holomorphic embedding. -/
theorem originMk_isOpenHoloEmbedding {d : ℕ} (j : Fin d) :
    IsOpenHoloEmbedding d (originMk (d := d) j) := by
  let U : Opens (OriginBlowup d) := ⟨originSource j,isOpen_originSource j⟩
  have hImage (z : ComplexModel d) : originMk j z ∈ U := originMk_mem_originSource j z
  let e : ComplexModel d ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ U :=
    { toFun := fun z => ⟨originMk j z,hImage z⟩
      invFun := fun z => originCoord j z.val
      left_inv := originCoord_originMk j
      right_inv := fun z => Subtype.ext (originMk_originCoord z.property)
      contMDiff_toFun := contMDiff_opens_mk (contMDiff_originMk j) hImage
      contMDiff_invFun := by
        intro z
        exact (contMDiffAt_originCoord z.property).comp z contMDiff_subtype_val.contMDiffAt }
  exact ⟨U,e,fun _ => rfl⟩

/-- The genuine point-blowup projection, read on any normalized chart,
is the standard monomial map for a point centre. -/
theorem originProj_comp_originMk_eq_monomial {d : ℕ} (j : Fin d) :
    (originProj (d := d)) ∘ originMk j = monomial 0 j := by
  funext z
  apply PiLp.ext
  intro i
  by_cases hi : i = j
  · subst i
    simp
  · simp [hi,mul_comm]

/-- On the actual point chart the strict-transform operation for the
monomial map reduces the odd cusp exponent by two. -/
theorem strictTransform_monomial_cusp (p : ℕ) (hp : 2 < p) :
    strictTransform 3 (monomial 0 (0 : Fin 3)) (embeddedCuspSet p) = embeddedCuspSet (p-2) := by
  rw [← originProj_comp_originMk_eq_monomial,strictTransform_comp contMDiff_originProj (contMDiff_originMk _)]
  have h0 := (originMk_isOpenHoloEmbedding (0 : Fin 3)).exceptionalLocus_eq_empty
  change closure ((originMk (0 : Fin 3)) ⁻¹'
    strictTransform 3 originProj (embeddedCuspSet p) \ exceptionalLocus 3 (originMk (0 : Fin 3))) = _
  rw [h0,sdiff_empty,first_chart_strictTransform_cusp p hp]
  exact (HironakaG8OddCuspGeometricSource.embedded_cusp_isAnalytic (p-2)).isClosed.closure_eq

end
end Hironaka.HironakaG8OddCuspMonomialStrict

#print axioms Hironaka.HironakaG8OddCuspMonomialStrict.strictTransform_monomial_cusp
