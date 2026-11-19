import Hironaka.Resolution.HironakaG1RDimensionBaseChange
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral

/-!
# Krull dimension of a finitely generated domain is the transcendence degree of its fraction field

* `exists_ringKrullDim_eq_trdeg`: for a domain `A` of finite type over a field `k` and any field
  `K` with `IsFractionRing A K` (compatibly with `k`), there is `d : ℕ` with `dim A = d` and
  `trdeg_k K = d` (Noether normalization `k[X₁..X_d] ↪ A` integral; transcendence degree is
  additive in towers and vanishes on algebraic extensions);
* `ringKrullDim_eq_of_isFractionRing`: two finite type `k`-domains with the same fraction field
  (over `k`) have the same Krull dimension.  This is the algebraic input for "the dimension of an
  integral scheme of finite type over a field is the dimension of every nonempty affine open"
  (`HironakaG1RIntegralSchemeDimension`).

The proof of `exists_ringKrullDim_eq_trdeg` follows the Mathlib-only argument of
`Hironaka/Algebra/FunctionFieldDimension.lean` (`exists_dimension_and_trdeg`), here
rewritten on top of `HironakaG1RDimensionBaseChange.ringKrullDim_eq_of_ringHom_isIntegral`.
Only Mathlib and that module are imported; no named input.
Blueprint: `hironaka-g1-r-integral-scheme-dimension.tex` (node `g1r:dimension-trdeg`).
-/

set_option autoImplicit false

namespace Hironaka.HironakaG1RFunctionFieldDimension

open HironakaG1RDimensionBaseChange

universe u

/-- Transcendence degree is unchanged along an algebraic extension of domains. -/
theorem trdeg_eq_of_isAlgebraic (k A K : Type u) [Field k] [CommRing A] [IsDomain A]
    [CommRing K] [NoZeroDivisors K] [Algebra k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] :
    Algebra.trdeg k A = Algebra.trdeg k K := by
  have h := trdeg_add_eq k A (A := K)
  rwa [trdeg_eq_zero (R := A) (A := K), add_zero] at h

/-- **Dimension = transcendence degree.**  For a domain `A` of finite type over a field `k` with
fraction field `K`, `dim A = trdeg_k K`, a natural number. -/
theorem exists_ringKrullDim_eq_trdeg (k A K : Type u) [Field k] [CommRing A] [IsDomain A]
    [Field K] [Algebra k A] [Algebra.FiniteType k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] :
    ∃ d : ℕ, ringKrullDim A = d ∧ Algebra.trdeg k K = d := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  have hdim : ringKrullDim A = s := by
    rw [ringKrullDim_eq_of_ringHom_isIntegral g.toRingHom hint hinj, ringKrullDim_mvPolynomial_fin]
  let P := MvPolynomial (Fin s) k
  let _ : Algebra P A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral P A := ⟨hint⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have htrA : Algebra.trdeg k A = s := by
    rw [← trdeg_eq_of_isAlgebraic k P A]
    simp [P]
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  exact ⟨s, hdim, (trdeg_eq_of_isAlgebraic k A K).symm.trans htrA⟩

/-- **Finite type domains with the same fraction field have the same dimension.** -/
theorem ringKrullDim_eq_of_isFractionRing (k A B K : Type u) [Field k] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Algebra k A] [Algebra k B] [Algebra.FiniteType k A]
    [Algebra.FiniteType k B] [Algebra k K] [Algebra A K] [Algebra B K] [IsScalarTower k A K]
    [IsScalarTower k B K] [IsFractionRing A K] [IsFractionRing B K] :
    ringKrullDim A = ringKrullDim B := by
  obtain ⟨d, hA, hd⟩ := exists_ringKrullDim_eq_trdeg k A K
  obtain ⟨e, hB, he⟩ := exists_ringKrullDim_eq_trdeg k B K
  have hde : d = e := by exact_mod_cast hd.symm.trans he
  rw [hA, hB, hde]

end Hironaka.HironakaG1RFunctionFieldDimension
