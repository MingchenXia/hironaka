/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualInitialSymbolRegularity

/-!
# Whole initial ideals after a tangent coordinate quotient

The initial ideal of the actual coordinate quotient is proved equal to the
coordinate quotient of the actual initial ideal. Compatibility is derived from
the original regular-symbol theorem, rather than assumed.
-/

set_option autoImplicit false

namespace Hironaka.HironakaActualInitialCoordinateQuotient

noncomputable section

open HironakaActualHomogeneousInitialHS HironakaActualHomogeneousInitialTangentDerivatives
  HironakaActualInitialSymbolRegularity HironakaStrictFilteredRegularElement
  HironakaActualFormalIdealContraction HironakaActualOriginalFormalHSTransfer
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualFormalInitialDiagram

variable {n : ℕ}

/-- Entire actual initial ideals retain inclusion of entire actual ideals. -/
theorem actualInitialIdeal_mono
    {K L : Ideal (MvPowerSeries (Fin n) ℂ)} (hKL : K ≤ L) :
    actualHomogeneousInitialIdeal K ≤ actualHomogeneousInitialIdeal L := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨F, hFK, hFne⟩, rfl⟩
  exact Ideal.subset_span ⟨⟨F, hKL hFK, hFne⟩, rfl⟩

private theorem variable_isHomogeneous (i : Fin n) :
    (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ).IsHomogeneous 1 := by
  intro α hα
  by_cases he : α = Finsupp.single i 1
  · subst α
    simp [Finsupp.weight_single]
  · simp [MvPowerSeries.coeff_X, he] at hα

private theorem mem_power_actualInitialDegree
    (F : MvPowerSeries (Fin n) ℂ) (hFne : F ≠ 0) :
    F ∈ genuineFormalVariables n ^ actualHomogeneousInitialDegree F hFne := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ F).mpr
  intro α hα
  apply MvPowerSeries.coeff_of_lt_order
  rw [← actualHomogeneousInitialDegree_eq_order F hFne]
  have hd : Finsupp.degree α < actualHomogeneousInitialDegree F hFne := by
    simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hα
  exact_mod_cast hd

/-- Adding an actual coordinate whose actual initial symbol is regular commutes
with the ENTIRE homogeneous initial ideal; no compatibility equality is assumed. -/
theorem actualInitialIdeal_add_coordinate_of_regular_symbol
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hregular : ∀ (q : ℕ) (b : MvPowerSeries (Fin n) ℂ),
      b ∈ genuineFormalVariables n ^ q →
      MvPowerSeries.X i * b ∈ K ⊔ genuineFormalVariables n ^ (q+2) →
      b ∈ K ⊔ genuineFormalVariables n ^ (q+1)) :
    actualHomogeneousInitialIdeal
        (K ⊔ Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))) =
      actualHomogeneousInitialIdeal K ⊔
        Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ)) := by
  let m := genuineFormalVariables n
  let J := actualHomogeneousInitialIdeal K
  let V := Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))
  have hX : (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) ∈ m :=
    Ideal.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨F, hFK, hFne⟩, rfl⟩
    obtain ⟨G, hGK, Q, hQ, hGQ⟩ := Submodule.mem_sup.mp hFK
    obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton.mp hQ
    have hFP := mem_power_actualInitialDegree F hFne
    change MvPowerSeries.homogeneousComponent (actualHomogeneousInitialDegree F hFne) F ∈ _
    cases hr : actualHomogeneousInitialDegree F hFne with
    | zero =>
        have hzero : MvPowerSeries.homogeneousComponent 0
            (MvPowerSeries.X i * H) = 0 := by
          rw [mul_comm]
          exact homogeneousComponent_mul_homogeneous_of_lt 0 1 H
            (MvPowerSeries.X i) (variable_isHomogeneous i) (by omega)
        rw [← hGQ, map_add, hzero, add_zero]
        exact (le_sup_left : J ≤ J ⊔ V)
          (homogeneousComponent_mem_actual_initial_of_mem_power K 0 G hGK (by simp))
    | succ q =>
        rw [hr] at hFP
        have hXH : MvPowerSeries.X i * H ∈ K ⊔ m^(q+1) := by
          have he : MvPowerSeries.X i * H = F - G := by rw [← hGQ]; ring
          rw [he]
          exact (K ⊔ m^(q+1)).sub_mem (Ideal.mem_sup_right hFP) (Ideal.mem_sup_left hGK)
        have hH : H ∈ K ⊔ m^q :=
          (mem_successor_iff_mem_current_of_regular_symbol K m _ hX hregular q H).mp hXH
        obtain ⟨A, hAK, B, hB, hAB⟩ := Submodule.mem_sup.mp hH
        let L := G + MvPowerSeries.X i * A
        have hLK : L ∈ K := K.add_mem hGK (K.mul_mem_left _ hAK)
        have hLF : L + MvPowerSeries.X i * B = F := by
          rw [← hGQ, ← hAB]
          dsimp only [L]
          ring
        have hXB : MvPowerSeries.X i * B ∈ m^(q+1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul hX hB
        have hLP : L ∈ m^(q+1) := by
          have he : L = F - MvPowerSeries.X i * B := by rw [← hLF]; ring
          rw [he]
          exact (m^(q+1)).sub_mem hFP hXB
        have hcomp : MvPowerSeries.homogeneousComponent (q+1) (MvPowerSeries.X i * B) =
            MvPowerSeries.X i * MvPowerSeries.homogeneousComponent q B := by
          rw [mul_comm, homogeneousComponent_mul_homogeneous_of_le (q+1) 1 B
            (MvPowerSeries.X i) (variable_isHomogeneous i) (by omega)]
          simp only [Nat.add_sub_cancel, mul_comm]
        rw [← hLF, map_add, hcomp]
        exact (J ⊔ V).add_mem
          ((le_sup_left : J ≤ J ⊔ V)
            (homogeneousComponent_mem_actual_initial_of_mem_power K (q+1) L hLK hLP))
          ((le_sup_right : V ≤ J ⊔ V)
            (V.mul_mem_right _ (Ideal.mem_span_singleton_self _)))
  · apply sup_le (actualInitialIdeal_mono le_sup_left)
    apply Ideal.span_le.mpr
    rintro _ rfl
    have hXV : (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) ∈ K ⊔ V :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    have hcomp := homogeneousComponent_mem_actual_initial_of_mem_power (K ⊔ V) 1
      (MvPowerSeries.X i) hXV (by simpa only [pow_one] using hX)
    rw [← MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp
      (variable_isHomogeneous i)] at hcomp
    exact hcomp

/-- Actual tangent partial stability internally supplies the regular symbol for
the entire coordinate-quotient initial-ideal equality. -/
theorem actualInitialIdeal_add_coordinate
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hD : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈
        actualHomogeneousInitialIdeal K) :
    actualHomogeneousInitialIdeal
        (K ⊔ Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))) =
      actualHomogeneousInitialIdeal K ⊔
        Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ)) :=
  actualInitialIdeal_add_coordinate_of_regular_symbol K i
    (formal_regular_symbol_of_initial_pderiv K i hD)

private theorem pderiv_mem_other_coordinate_principal (i j : Fin n) (hij : i ≠ j)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))) :
    MvPowerSeries.pderiv ℂ j F ∈
      Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ)) := by
  let V := Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain rfl : F = MvPowerSeries.X i := Set.mem_singleton_iff.mp hF
      rw [MvPowerSeries.pderiv_X_of_ne hij]
      exact V.zero_mem
  | zero => simp
  | add F G _ _ hF hG => simpa only [map_add] using V.add_mem hF hG
  | smul A F hF ih =>
      change MvPowerSeries.pderiv ℂ j (A*F) ∈ V
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact V.add_mem (V.mul_mem_left A ih) (V.mul_mem_right _ hF)

/-- After the actual coordinate quotient, every other whole initial-ideal
partial stability is preserved. This is the induction step for successive cuts. -/
theorem actualInitialIdeal_add_coordinate_pderiv
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (i j : Fin n) (hij : i ≠ j)
    (hDi : ∀ P : MvPolynomial (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K →
      (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈
        actualHomogeneousInitialIdeal K)
    (hDj : ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ j F ∈ actualHomogeneousInitialIdeal K)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualHomogeneousInitialIdeal
      (K ⊔ Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ)))) :
    MvPowerSeries.pderiv ℂ j F ∈ actualHomogeneousInitialIdeal
      (K ⊔ Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))) := by
  rw [actualInitialIdeal_add_coordinate K i hDi] at hF ⊢
  obtain ⟨G, hG, H, hH, rfl⟩ := Submodule.mem_sup.mp hF
  rw [map_add]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hDj G hG))
    (Ideal.mem_sup_right (pderiv_mem_other_coordinate_principal i j hij H hH))

/-- Successively quotient the SAME actual ideal by the listed actual coordinate
classes; the intermediate actual ideals are retained. -/
def successiveCoordinateQuotient (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    List (Fin n) → Ideal (MvPowerSeries (Fin n) ℂ)
  | [] => K
  | i :: L => successiveCoordinateQuotient
      (K ⊔ Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))) L

/-- Exact initial-ideal compatibility is internally produced at EVERY distinct
ordered tangent cut, together with all remaining whole partial stabilities. -/
theorem actualInitialIdeal_successive_coordinate_quotients
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (L : List (Fin n)) (hL : L.Nodup)
    (hD : ∀ i ∈ L, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K) :
    actualHomogeneousInitialIdeal (successiveCoordinateQuotient K L) =
        successiveCoordinateQuotient (actualHomogeneousInitialIdeal K) L ∧
      ∀ j : Fin n, j ∉ L →
        (∀ F ∈ actualHomogeneousInitialIdeal K,
          MvPowerSeries.pderiv ℂ j F ∈ actualHomogeneousInitialIdeal K) →
        ∀ F ∈ actualHomogeneousInitialIdeal (successiveCoordinateQuotient K L),
          MvPowerSeries.pderiv ℂ j F ∈
            actualHomogeneousInitialIdeal (successiveCoordinateQuotient K L) := by
  induction L generalizing K with
  | nil => exact ⟨rfl, fun _ _ hDj => hDj⟩
  | cons i L ih =>
      obtain ⟨hiL, hLn⟩ := List.nodup_cons.mp hL
      let V := Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ))
      have hDi : ∀ P : MvPolynomial (Fin n) ℂ,
          (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal K →
          (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈
            actualHomogeneousInitialIdeal K := by
        intro P hP
        rw [← MvPowerSeries.pderiv_coe]
        exact hD i List.mem_cons_self P hP
      have hDtail : ∀ j ∈ L, ∀ F ∈ actualHomogeneousInitialIdeal (K ⊔ V),
          MvPowerSeries.pderiv ℂ j F ∈ actualHomogeneousInitialIdeal (K ⊔ V) := by
        intro j hj F hF
        have hij : i ≠ j := by rintro rfl; exact hiL hj
        exact actualInitialIdeal_add_coordinate_pderiv K i j hij hDi
          (hD j (List.mem_cons_of_mem i hj)) F hF
      obtain ⟨heq, hremain⟩ := ih (K ⊔ V) hLn hDtail
      constructor
      · change actualHomogeneousInitialIdeal (successiveCoordinateQuotient (K ⊔ V) L) =
          successiveCoordinateQuotient (actualHomogeneousInitialIdeal K ⊔ V) L
        rw [heq, actualInitialIdeal_add_coordinate K i hDi]
      · intro j hj hDj F hF
        have hij : i ≠ j := by
          rintro rfl
          exact hj List.mem_cons_self
        have hjL : j ∉ L := fun hjL => hj (List.mem_cons_of_mem i hjL)
        exact hremain j hjL
          (actualInitialIdeal_add_coordinate_pderiv K i j hij hDi hDj) F hF

end

end Hironaka.HironakaActualInitialCoordinateQuotient
