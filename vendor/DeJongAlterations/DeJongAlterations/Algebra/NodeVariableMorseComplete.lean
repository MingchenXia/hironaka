import DeJongAlterations.Algebra.NodeVariableMorseContraction

/-!
# The actual original variable-adic fixed point and quadratic normal form

The limit is constructed in the original complete variable ideal. An actual
unipotent native substitution from this fixed point solves the original
quadratic equation; its actual inverse gives the same-field Morse form.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K] (Q : Quadratic K)

/-- The actual native variable-adic limit of the original deterministic approximations. -/
def fixedPoint (H : Series K) (hH : H ∈ variableIdeal K ^ 3) : Series K :=
  Classical.choose (exists_approximation_limit Q H hH)

/-- Every actual original approximation agrees with the actual limit to its native variable order. -/
theorem fixedPoint_congruence (H : Series K) (hH : H ∈ variableIdeal K ^ 3) (n : ℕ) :
    approximation Q H n - fixedPoint Q H hH ∈ variableIdeal K ^ n :=
  Classical.choose_spec (exists_approximation_limit Q H hH) n

/-- The constructed actual limit remains in the original cubic variable ideal. -/
theorem fixedPoint_mem_pow (H : Series K) (hH : H ∈ variableIdeal K ^ 3) :
    fixedPoint Q H hH ∈ variableIdeal K ^ 3 := by
  have he : fixedPoint Q H hH = approximation Q H 3 -
      (approximation Q H 3 - fixedPoint Q H hH) := by abel
  rw [he]
  exact Ideal.sub_mem _ (approximation_mem_pow Q H hH 3) (fixedPoint_congruence Q H hH 3)

/-- The original actual limit solves the original quadratic fixed-point equation. -/
theorem fixedPoint_equation (H : Series K) (hH : H ∈ variableIdeal K ^ 3) :
    fixedPoint Q H hH = H + quadraticError Q (fixedPoint Q H hH) := by
  apply sub_eq_zero.mp
  apply IsHausdorff.haus (inferInstance : IsHausdorff (variableIdeal K) (Series K))
  intro n
  rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
  have h0 : fixedPoint Q H hH - approximation Q H (n + 4) ∈ variableIdeal K ^ (n + 4) := by
    simpa only [neg_sub] using
      (variableIdeal K ^ (n + 4)).neg_mem (fixedPoint_congruence Q H hH (n + 4))
  have hq := quadraticError_sub_mem_pow Q (n := n)
    (approximation_mem_pow Q H hH (n + 3)) (fixedPoint_mem_pow Q H hH)
    (fixedPoint_congruence Q H hH (n + 3))
  have he : fixedPoint Q H hH - (H + quadraticError Q (fixedPoint Q H hH)) =
      (fixedPoint Q H hH - approximation Q H (n + 4)) +
        (quadraticError Q (approximation Q H (n + 3)) -
          quadraticError Q (fixedPoint Q H hH)) := by
    change fixedPoint Q H hH - (H + quadraticError Q (fixedPoint Q H hH)) =
      (fixedPoint Q H hH - (H + quadraticError Q (approximation Q H (n + 3)))) + _
    abel
  rw [he]
  exact Ideal.add_mem _
    (Ideal.pow_le_pow_right (by omega : n ≤ n + 4) h0)
    (Ideal.pow_le_pow_right (by omega : n ≤ n + 4) hq)

/-- The actual tangent-identity original automorphism mapping the original quadratic onto its deformation. -/
def deformationEquiv (H : Series K) (hH : H ∈ variableIdeal K ^ 3) : Series K ≃ₐ[K] Series K :=
  correctionEquiv Q (by decide : 2 ≤ 2) (fixedPoint Q H hH) (fixedPoint_mem_pow Q H hH)

/-- The original quadratic is sent to the original deformed equation, over the same field. -/
theorem deformationEquiv_equation (H : Series K) (hH : H ∈ variableIdeal K ^ 3) :
    deformationEquiv Q H hH Q.series = Q.series - H := by
  have hmul : deformationEquiv Q H hH Q.series =
      Q.series - X 0 * firstPart (fixedPoint Q H hH) -
        X 1 * secondPart (fixedPoint Q H hH) + quadraticError Q (fixedPoint Q H hH) := by
    have he := (Q.map C).expansion (X 0) (X 1)
      (firstPart (fixedPoint Q H hH)) (secondPart (fixedPoint Q H hH))
    rw [← leftCorrection_eq, ← rightCorrection_eq, ← quadraticError_eq] at he
    change (Q.map C).value (X 0 - leftCorrection Q (fixedPoint Q H hH))
        (X 1 - rightCorrection Q (fixedPoint Q H hH)) =
      Q.series - X 0 * firstPart (fixedPoint Q H hH) -
        X 1 * secondPart (fixedPoint Q H hH) + quadraticError Q (fixedPoint Q H hH) at he
    rw [← he]
    simp only [deformationEquiv, Quadratic.series, Quadratic.value, Quadratic.map,
      map_add, map_mul, map_pow, correctionEquiv_C, correctionEquiv_X_zero, correctionEquiv_X_one]
  have hc : constantCoeff (fixedPoint Q H hH) = 0 :=
    constantCoeff_zero_of_mem_pow (by decide : 1 ≤ 3) (fixedPoint_mem_pow Q H hH)
  have hd := decomposition (fixedPoint Q H hH)
  rw [hc, map_zero, zero_add] at hd
  rw [hmul]
  have hfix := fixedPoint_equation Q H hH
  linear_combination hd - hfix

/-- The actual inverse of the original constructed deformation map gives the normal form. -/
def normalFormEquiv (H : Series K) (hH : H ∈ variableIdeal K ^ 3) : Series K ≃ₐ[K] Series K :=
  (deformationEquiv Q H hH).symm

/-- The actual original inverse sends the original deformed equation to the original quadratic. -/
theorem normalFormEquiv_equation (H : Series K) (hH : H ∈ variableIdeal K ^ 3) :
    normalFormEquiv Q H hH (Q.series - H) = Q.series := by
  rw [← deformationEquiv_equation Q H hH]
  exact (deformationEquiv Q H hH).symm_apply_apply Q.series

/-- The actual deformation coordinates retain the original identity linear part. -/
theorem deformationEquiv_coordinate (H : Series K) (hH : H ∈ variableIdeal K ^ 3) (i : Fin 2) :
    deformationEquiv Q H hH (X i) - X i ∈ variableIdeal K ^ 2 := by
  change substAlgHom (R := K)
    (correctionCoordinates_hasSubst Q (by decide : 2 ≤ 2) (fixedPoint_mem_pow Q H hH))
    (X i) - X i ∈ variableIdeal K ^ 2
  rw [substAlgHom_X]
  exact correctionCoordinates_sub_mem Q (fixedPoint_mem_pow Q H hH) i

/-- The actual normal-form coordinates have the same original identity linear part. -/
theorem normalFormEquiv_coordinate (H : Series K) (hH : H ∈ variableIdeal K ^ 3) (i : Fin 2) :
    normalFormEquiv Q H hH (X i) - X i ∈ variableIdeal K ^ 2 :=
  unipotentEquiv_symm_coordinate
    (NodeNonsplit.correctionCoordinates Q (fixedPoint Q H hH))
    (correctionCoordinates_hasSubst Q (by decide : 2 ≤ 2) (fixedPoint_mem_pow Q H hH))
    (fun j => correctionCoordinates_sub_mem Q (fixedPoint_mem_pow Q H hH) j) i

/-- The actual same-field automorphism for the original `Q+F` convention. -/
def plusNormalFormEquiv (F : Series K) (hF : F ∈ variableIdeal K ^ 3) :
    Series K ≃ₐ[K] Series K := normalFormEquiv Q (-F) ((variableIdeal K ^ 3).neg_mem hF)

/-- The original full series is actually sent to its original nondegenerate quadratic. -/
theorem plusNormalFormEquiv_equation (F : Series K) (hF : F ∈ variableIdeal K ^ 3) :
    plusNormalFormEquiv Q F hF (Q.series + F) = Q.series := by
  simpa only [plusNormalFormEquiv, sub_neg_eq_add] using
    normalFormEquiv_equation Q (-F) ((variableIdeal K ^ 3).neg_mem hF)

/-- The actual same-field quadratic hypersurface quotient isomorphism. -/
def normalFormQuotientEquiv (F : Series K) (hF : F ∈ variableIdeal K ^ 3) :
    (Series K ⧸ Ideal.span {Q.series + F}) ≃ₐ[K] Series K ⧸ Ideal.span {Q.series} :=
  Ideal.quotientEquivAlg _ _ (plusNormalFormEquiv Q F hF) (by
    rw [Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    change Q.series = plusNormalFormEquiv Q F hF (Q.series + F)
    exact (plusNormalFormEquiv_equation Q F hF).symm)

/-- Source-facing original variable-adic Morse theorem with both original tangent identities. -/
theorem exists_quadratic_normal_form (F : Series K) (hF : F ∈ variableIdeal K ^ 3) :
    ∃ e : Series K ≃ₐ[K] Series K,
      e (Q.series + F) = Q.series ∧
      (∀ i : Fin 2, e (X i) - X i ∈ variableIdeal K ^ 2) ∧
      (∀ i : Fin 2, e.symm (X i) - X i ∈ variableIdeal K ^ 2) := by
  refine ⟨plusNormalFormEquiv Q F hF, plusNormalFormEquiv_equation Q F hF, ?_, ?_⟩
  · exact normalFormEquiv_coordinate Q (-F) ((variableIdeal K ^ 3).neg_mem hF)
  · exact deformationEquiv_coordinate Q (-F) ((variableIdeal K ^ 3).neg_mem hF)

/-- The original three quadratic coefficients require only their original nonzero discriminant. -/
theorem exists_original_quadratic_normal_form (a0 a1 a2 : K)
    (hΔ : a1 ^ 2 - 4 * a0 * a2 ≠ 0) (F : Series K) (hF : F ∈ variableIdeal K ^ 3) :
    ∃ e : Series K ≃ₐ[K] Series K,
      e (C a0 * X 0 ^ 2 + C a1 * X 0 * X 1 + C a2 * X 1 ^ 2 + F) =
        C a0 * X 0 ^ 2 + C a1 * X 0 * X 1 + C a2 * X 1 ^ 2 ∧
      (∀ i : Fin 2, e (X i) - X i ∈ variableIdeal K ^ 2) ∧
      (∀ i : Fin 2, e.symm (X i) - X i ∈ variableIdeal K ^ 2) := by
  simpa only [Quadratic.series, Quadratic.value, Quadratic.map, Quadratic.ofCoefficients] using
    exists_quadratic_normal_form (Quadratic.ofCoefficients a0 a1 a2 (isUnit_iff_ne_zero.mpr hΔ)) F hF

end DeJongAlterations.Algebra.NodeVariableMorse
