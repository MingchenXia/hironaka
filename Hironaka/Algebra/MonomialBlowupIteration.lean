import Hironaka.Algebra.NodeBlowupChart
import Hironaka.Algebra.ReesPrincipalFactor

/-!
# Exact actual prefix-centre recurrences for monomial node blowups

The finite maps below are actual composites of quotient algebra maps.
Their compatibility with native saturated charts is proved, not assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped Pointwise

namespace Hironaka.Algebra.MonomialBlowupIteration

open NodeBlowupChart

variable {A : Type*} [CommRing A]

/-- The actual prefix centre in the literal node quotient. -/
def prefixCenter (c s : A) : Ideal (Node A c) :=
  Ideal.span {coordinate c 0, algebraMap A (Node A c) s}

theorem coordinate_product (c : A) :
    coordinate c 0 * coordinate c 1 = algebraMap A (Node A c) c :=
  NodeDomain.nodeCoordinateProduct c

/-- The actual continuation substitution, defined without a nonvanishing hypothesis. -/
def continuationMap (p q : A) : Node A (p * q) →ₐ[A] Node A q :=
  Ideal.Quotient.liftₐ _
    (MvPolynomial.aeval ![algebraMap A (Node A q) p * coordinate q 0, coordinate q 1]) (by
      change NodeChart.uChartIdeal A (p * q) ≤ RingHom.ker
        (MvPolynomial.aeval ![algebraMap A (Node A q) p * coordinate q 0, coordinate q 1]).toRingHom
      rw [NodeChart.uChartIdeal]
      apply Ideal.span_le.mpr
      rintro x (rfl : x = _)
      change (MvPolynomial.aeval
        ![algebraMap A (Node A q) p * coordinate q 0, coordinate q 1])
          (X 0 * X 1 - C (p * q)) = 0
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [mul_assoc, coordinate_product, ← map_mul, sub_self])

@[simp]
theorem continuationMap_coordinate0 (p q : A) :
    continuationMap p q (coordinate (p * q) 0) =
      algebraMap A (Node A q) p * coordinate q 0 := by
  simp [continuationMap, coordinate]

@[simp]
theorem continuationMap_coordinate1 (p q : A) :
    continuationMap p q (coordinate (p * q) 1) = coordinate q 1 := by
  simp [continuationMap, coordinate]

/-- Maps from the actual node quotient agree if their actual coordinate images agree. -/
theorem node_algHom_ext {B : Type*} [CommRing B] [Algebra A B] {c : A}
    {f g : Node A c →ₐ[A] B}
    (h0 : f (coordinate c 0) = g (coordinate c 0))
    (h1 : f (coordinate c 1) = g (coordinate c 1)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

section NativeChart

variable [IsDomain A] (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)]

/-- The substitution is exactly the genuine saturated parameter chart, with coordinates reoriented. -/
theorem continuationMap_eq_native :
    continuationMap t q = (nodeSwap q).toAlgHom.comp (tChartOriginalMap t q) := by
  apply node_algHom_ext <;> simp

/-- The next original prefix centre is actually principal on the finished native chart. -/
theorem prefixCenter_map_uChart (s : A) :
    (prefixCenter (t * q) (t * s)).map (uChartOriginalMap t q).toRingHom =
      Ideal.span {coordinate t 0} := by
  rw [prefixCenter, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    uChartOriginalMap_coordinate0, AlgHom.commutes]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  refine ⟨coordinate t 1 * algebraMap A (Node A t) s, ?_⟩
  rw [map_mul, ← coordinate_product, mul_assoc]

end NativeChart

/-- The exact next-centre factorization on the actual continuation quotient. -/
theorem prefixCenter_map_continuation (p q s : A) :
    (prefixCenter (p * q) (p * s)).map (continuationMap p q).toRingHom =
      ReesPrincipalFactor.scaledIdeal (algebraMap A (Node A q) p) (prefixCenter q s) := by
  rw [prefixCenter, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    continuationMap_coordinate0, AlgHom.commutes, map_mul]
  rw [ReesPrincipalFactor.scaledIdeal, prefixCenter, Ideal.span_mul_span']
  congr 1
  simp only [Set.singleton_mul, Set.image_insert_eq, Set.image_singleton]

/-- The actual finite composition removing the specified prefix, one entry at a time. -/
def prefixMap : (a b : List A) → Node A (a ++ b).prod →ₐ[A] Node A b.prod
  | [], _ => AlgHom.id A _
  | t :: a, b => (prefixMap a b).comp (continuationMap t (a ++ b).prod)

@[simp]
theorem prefixMap_coordinate0 (a b : List A) :
    prefixMap a b (coordinate (a ++ b).prod 0) =
      algebraMap A (Node A b.prod) a.prod * coordinate b.prod 0 := by
  induction a with
  | nil => simp [prefixMap]
  | cons t a ih =>
    simp only [prefixMap, List.cons_append, List.prod_cons, AlgHom.comp_apply,
      continuationMap_coordinate0, map_mul, AlgHom.commutes, ih, mul_assoc]

@[simp]
theorem prefixMap_coordinate1 (a b : List A) :
    prefixMap a b (coordinate (a ++ b).prod 1) = coordinate b.prod 1 := by
  induction a with
  | nil => rfl
  | cons t a ih =>
    simpa only [prefixMap, List.cons_append, List.prod_cons, AlgHom.comp_apply,
      continuationMap_coordinate1] using ih

/-- The original prefix centre has the exact accumulated principal factor after any finite prefix. -/
theorem prefixCenter_map_prefix (a b : List A) (s : A) :
    (prefixCenter (a ++ b).prod (a.prod * s)).map (prefixMap a b).toRingHom =
      ReesPrincipalFactor.scaledIdeal (algebraMap A (Node A b.prod) a.prod)
        (prefixCenter b.prod s) := by
  rw [prefixCenter, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    prefixMap_coordinate0, AlgHom.commutes, map_mul]
  rw [ReesPrincipalFactor.scaledIdeal, prefixCenter, Ideal.span_mul_span']
  congr 1
  simp only [Set.singleton_mul, Set.image_insert_eq, Set.image_singleton]

section FinishedPrefix

variable [IsDomain A] (a : List A) (t : A) (b : List A)
    [Fact (t ≠ 0)] [Fact (b.prod ≠ 0)]

/-- The actual finite prefix composition followed by its actual finished native chart map. -/
def finishedPrefixMap : Node A (a ++ t :: b).prod →ₐ[A] Node A t :=
  (uChartOriginalMap t b.prod).comp (prefixMap a (t :: b))

@[simp]
theorem finishedPrefixMap_coordinate0 :
    finishedPrefixMap a t b (coordinate (a ++ t :: b).prod 0) =
      algebraMap A (Node A t) a.prod * coordinate t 0 := by
  change uChartOriginalMap t b.prod
    (prefixMap a (t :: b) (coordinate (a ++ t :: b).prod 0)) = _
  rw [prefixMap_coordinate0]
  simp

@[simp]
theorem finishedPrefixMap_coordinate1 :
    finishedPrefixMap a t b (coordinate (a ++ t :: b).prod 1) =
      coordinate t 1 * algebraMap A (Node A t) b.prod := by
  change uChartOriginalMap t b.prod
    (prefixMap a (t :: b) (coordinate (a ++ t :: b).prod 1)) = _
  rw [prefixMap_coordinate1]
  exact uChartOriginalMap_coordinate1 t b.prod

/-- Every later original prefix centre is exactly principal on the actual finished finite-prefix chart. -/
theorem prefixCenter_map_finishedPrefix (s : A) :
    (prefixCenter (a ++ t :: b).prod (a.prod * (t * s))).map
      (finishedPrefixMap a t b).toRingHom =
        Ideal.span {algebraMap A (Node A t) a.prod * coordinate t 0} := by
  rw [prefixCenter, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    finishedPrefixMap_coordinate0, AlgHom.commutes]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  refine ⟨coordinate t 1 * algebraMap A (Node A t) s, ?_⟩
  rw [map_mul, map_mul, ← coordinate_product]
  ring

end FinishedPrefix

end Hironaka.Algebra.MonomialBlowupIteration
