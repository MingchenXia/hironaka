/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHomogeneousInitialHS

/-! The unchanged entire actual homogeneous initial ideal is the extension of its literal polynomial contraction. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInitialPolynomialContraction
noncomputable section
open HironakaActualHomogeneousInitialHS

/-- Every true homogeneous component is EXACTLY the whole inclusion of its genuine finite polynomial truncation. -/
theorem homogeneousComponent_truncTotal_coe {n : ℕ} (q : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) :
    (MvPowerSeries.truncTotal (q+1) (MvPowerSeries.homogeneousComponent q F) :
      MvPowerSeries (Fin n) ℂ) = MvPowerSeries.homogeneousComponent q F := by
  apply MvPowerSeries.ext
  intro α
  rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with hα
  · rfl
  · rw [MvPowerSeries.coeff_homogeneousComponent, if_neg]
    omega

/-- BOTH whole directions retain the SAME actual initial ideal and the literal polynomial contraction; ALL true initial forms are included. -/
theorem actualHomogeneousInitialIdeal_eq_map_polynomial_comap {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualHomogeneousInitialIdeal K = Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom
      (Ideal.comap MvPolynomial.coeToMvPowerSeries.ringHom (actualHomogeneousInitialIdeal K)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨F, rfl⟩
    let q := actualHomogeneousInitialDegree F.val F.property.2
    let P := MvPowerSeries.truncTotal (q+1) (MvPowerSeries.homogeneousComponent q F.val)
    have he : (P : MvPowerSeries (Fin n) ℂ) = actualHomogeneousInitialForm F.val F.property.2 :=
      homogeneousComponent_truncTotal_coe q F.val
    change actualHomogeneousInitialForm F.val F.property.2 ∈ _
    rw [← he]
    apply Ideal.mem_map_of_mem
    change (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K
    rw [he]
    exact Ideal.subset_span ⟨F, rfl⟩
  · exact Ideal.map_comap_le

end
end Hironaka.HironakaActualInitialPolynomialContraction
