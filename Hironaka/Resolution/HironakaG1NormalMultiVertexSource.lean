import Hironaka.Resolution.HironakaActualWeightedNativeRadical

/-! Equal-weight multi-vertex compression under independent generator changes. -/

set_option autoImplicit false

open Set

namespace Hironaka.HironakaG1NormalMultiVertexSource

noncomputable section

open HironakaActualWeightedCoefficientCompression HironakaActualWeightedNativeRadical

private abbrev R := MvPowerSeries (Fin 2) ℂ
private def x : R := MvPowerSeries.X 0
private def y : R := MvPowerSeries.X 1

private def original : Fin 2 → R := ![x, y]
private def changed : Fin 2 → R := ![x + y, y]
private def weights : Fin 2 → ℕ := fun _ => 2

private theorem range_pair {A : Type*} (f : Fin 2 → A) : range f = {f 0, f 1} := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp only [mem_insert_iff, mem_singleton_iff, mem_range]
    rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem compression_pair {S : Type*} [CommRing S] (f : Fin 2 → S) :
    weightedCompression weights f = Ideal.span ({f 0 ^ 2, f 1 ^ 2} : Set S) := by
  unfold weightedCompression
  have hM : weightedCommonMark weights = 4 := by
    norm_num [weightedCommonMark, Fin.prod_univ_two, weights]
  rw [hM, range_pair]
  rfl

private def xyDegree : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

private theorem coeff_mul_x_sq (p : R) :
    MvPowerSeries.coeff xyDegree (x ^ 2 * p) = 0 := by
  rw [x, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, if_neg]
  intro h
  have hh := h 0
  norm_num [xyDegree] at hh

private theorem coeff_mul_y_sq (p : R) :
    MvPowerSeries.coeff xyDegree (y ^ 2 * p) = 0 := by
  rw [y, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, if_neg]
  intro h
  have hh := h 1
  norm_num [xyDegree] at hh

private theorem coeff_xy : MvPowerSeries.coeff xyDegree (x * y) = 1 := by
  rw [x, y, MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial]
  simp [xyDegree]

private theorem coeff_changed_sq : MvPowerSeries.coeff xyDegree ((x + y) ^ 2) = 2 := by
  rw [show (x + y) ^ 2 = x ^ 2 * 1 + x * y + x * y + y ^ 2 * 1 by ring]
  simp only [map_add, coeff_mul_x_sq, coeff_mul_y_sq, coeff_xy]
  norm_num

/-- Equal original generator spans and equal weights do not determine the
whole compressed ideal even in the two-variable formal source stalk. -/
theorem same_span_same_weights_compression_obstruction :
    Ideal.span (range original) = Ideal.span (range changed) ∧
    weightedCompression weights original ≠ weightedCompression weights changed := by
  constructor
  · rw [range_pair, range_pair]
    exact (Ideal.span_pair_add_right (x := x) (y := y)).symm
  · rw [compression_pair, compression_pair]
    intro h
    change Ideal.span ({x ^ 2, y ^ 2} : Set R) = Ideal.span ({(x + y) ^ 2, y ^ 2} : Set R) at h
    have hmem : (x + y) ^ 2 ∈ Ideal.span ({x ^ 2, y ^ 2} : Set R) := by
      rw [h]
      exact Ideal.subset_span (Set.mem_insert _ _)
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    have hCoeff := congrArg (MvPowerSeries.coeff (R := ℂ) xyDegree) hab
    rw [map_add, mul_comm a, mul_comm b, coeff_mul_x_sq, coeff_mul_y_sq, coeff_changed_sq] at hCoeff
    norm_num at hCoeff

/-- The same two presentations nevertheless have the same radical after
compression. -/
theorem same_span_same_weights_compression_radical :
    (weightedCompression weights original).radical =
      (weightedCompression weights changed).radical := by
  rw [weightedCompression_radical weights (by norm_num [weights]) original,
    weightedCompression_radical weights (by norm_num [weights]) changed]
  exact congrArg Ideal.radical same_span_same_weights_compression_obstruction.1


private theorem lattice_cube {A : Type*} [SemilatticeSup A] (a b c d : A) :
    a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (c ⊔ b) ⊔ (c ⊔ b ⊔ (b ⊔ d)) := by
  calc
    a ⊔ b ⊔ (c ⊔ d) = a ⊔ ((b ⊔ b) ⊔ b) ⊔ (((c ⊔ c) ⊔ c) ⊔ d) := by
      simp only [sup_idem]
    _ = _ := by ac_rfl

/-- For two weight-two generators, the compressed ideal times the
uncompressed ideal is the cube of the uncompressed ideal. -/
theorem compression_two_weight_two_mul_span {S : Type*} [CommRing S] (c : Fin 2 → S) :
    weightedCompression (fun _ => 2) c * Ideal.span (range c) =
      (Ideal.span (range c)) ^ 3 := by
  change weightedCompression weights c * Ideal.span (range c) = _
  rw [compression_pair, range_pair]
  simp only [Ideal.span_insert, pow_succ, pow_zero, one_mul,
    Ideal.sup_mul, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
  have h1 : c 1 * c 0 * c 0 = c 0 * c 0 * c 1 := by ring
  have h2 : c 0 * c 1 * c 0 = c 0 * c 0 * c 1 := by ring
  have h3 : c 1 * c 0 * c 1 = c 1 * c 1 * c 0 := by ring
  have h4 : c 0 * c 1 * c 1 = c 1 * c 1 * c 0 := by ring
  rw [h1, h2, h3, h4]
  exact lattice_cube _ _ _ _

/-- The two compressed ideals have the same product with their common source
ideal for arbitrary changes of two generators with the same source span. -/
theorem compression_two_weight_two_mul_span_eq {S : Type*} [CommRing S] (c c' : Fin 2 → S)
    (hSpan : Ideal.span (range c) = Ideal.span (range c')) :
    weightedCompression (fun _ => 2) c * Ideal.span (range c) =
      weightedCompression (fun _ => 2) c' * Ideal.span (range c) := by
  rw [compression_two_weight_two_mul_span c, hSpan, compression_two_weight_two_mul_span c']

/-- Explicit two-variable formal witness that equality of source spans and
weights alone does not imply equality of compressed ideals. -/
theorem exists_same_span_different_two_weight_two_compression :
    ∃ c c' : Fin 2 → MvPowerSeries (Fin 2) ℂ,
      Ideal.span (range c) = Ideal.span (range c') ∧
      weightedCompression (fun _ => 2) c ≠ weightedCompression (fun _ => 2) c' :=
  ⟨original, changed, same_span_same_weights_compression_obstruction⟩

end

end Hironaka.HironakaG1NormalMultiVertexSource
