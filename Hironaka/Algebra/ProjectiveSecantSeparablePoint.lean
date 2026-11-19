import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Original nonzero polynomial data internally produce finite separable nonvanishing coordinates
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

universe u

/-- Even over imperfect original fields, the actual separably closed ambient field is infinite. -/
theorem separablyClosed_infinite (K : Type u) [Field K] [IsSepClosed K] : Infinite K := by
  apply not_finite_iff_infinite.mp
  intro h
  let : Finite K := h
  let : PerfectField K := PerfectField.ofFinite
  let : IsAlgClosed K := inferInstance
  let : Infinite K := inferInstance
  exact not_finite K

/-- The original nonzero polynomial, over ANY original field, internally produces an actual finite separable field and actual nonvanishing coordinates; no field-point or separability certificate is supplied. -/
theorem exists_finite_separable_nonvanishing
    (k : Type u) (I : Type*) [Field k] [Finite I] (F : MvPolynomial I k) (hF : F ≠ 0) :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧
      Algebra.IsSeparable k L ∧ ∃ v : I → L, MvPolynomial.aeval v F ≠ 0 := by
  let E := SeparableClosure k
  let : Infinite E := separablyClosed_infinite E
  have hmap : MvPolynomial.map (algebraMap k E) F ≠ 0 := by
    intro h
    apply hF
    apply MvPolynomial.map_injective _ (algebraMap k E).injective
    simpa only [map_zero] using h
  obtain ⟨w, hw⟩ : ∃ w : I → E, MvPolynomial.eval w (MvPolynomial.map (algebraMap k E) F) ≠ 0 := by
    by_contra! h
    apply hmap
    exact MvPolynomial.funext fun w => by simpa only [map_zero] using h w
  have hw' : MvPolynomial.aeval w F ≠ 0 := by
    change MvPolynomial.eval₂ (algebraMap k E) w F ≠ 0
    simpa only [MvPolynomial.eval₂_eq_eval_map] using hw
  let L := IntermediateField.adjoin k (Set.range w)
  let v : I → L := fun j => ⟨w j, IntermediateField.subset_adjoin k _ (Set.mem_range_self j)⟩
  let := Fintype.ofFinite I
  let := (Set.finite_range w).fintype
  have hfin : FiniteDimensional k L := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsSeparable.isIntegral k x)
  have he : L.val.comp (MvPolynomial.aeval v) = MvPolynomial.aeval w := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  refine ⟨L, hfin, inferInstance, v, ?_⟩
  intro hz
  apply hw'
  rw [← AlgHom.congr_fun he F, AlgHom.comp_apply, hz, map_zero]

/-- An original nonzero polynomial internally gives a finite separable nonvanishing point with a genuinely nonzero distinguished original coordinate. -/
theorem exists_finite_separable_nonvanishing_with_coordinate
    (k : Type u) (I : Type*) [Field k] [Finite I] (j : I) (F : MvPolynomial I k) (hF : F ≠ 0) :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧
      Algebra.IsSeparable k L ∧ ∃ v : I → L, v j ≠ 0 ∧ MvPolynomial.aeval v F ≠ 0 := by
  obtain ⟨L, hfin, hsep, v, hv⟩ := exists_finite_separable_nonvanishing k I (F * X j)
    (mul_ne_zero hF (MvPolynomial.X_ne_zero j))
  rw [map_mul, MvPolynomial.aeval_X] at hv
  exact ⟨L, hfin, hsep, v, (mul_ne_zero_iff.mp hv).2, (mul_ne_zero_iff.mp hv).1⟩

end Hironaka.Algebra.ProjectiveSecant
