import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeIntersections
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCFlatHeight
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCIndependence
import Hironaka.Algebra.NodeFamilyFlat

/-! Exact actual minimal-prime heights of mixed native SNC node intersections. -/

noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeHeights

open Algebra.NodeBlowupChart MonomialBlowupRegularBaseSNCNodeAlgebra
open MonomialBlowupRegularBaseSNCIntersection MonomialBlowupRegularBaseSNCIndependence
open MonomialBlowupRegularBaseSNCQuotientParameters MonomialBlowupRegularBaseSNCNodeIntersections
open MonomialBlowupRegularBaseSNCFlatHeight SpecIdealSheaf Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

local instance componentDecidableEq (D : (Spec (CommRingCat.of A)).IdealSheafData) :
    DecidableEq (DivisorComponent D) := Classical.typeDecidableEq _

/-- Every genuine containing prime has at least the intrinsic pure codimension. -/
theorem le_height_of_hasPureCodimension (I : Ideal A) (r : ℕ)
    (hI : HasPureCodimension (specIdealSheaf A I).support r)
    (p : Ideal A) [p.IsPrime] (hIp : I ≤ p) : (r : ℕ∞) ≤ p.height := by
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hIp
  rw [← minimalPrime_height_of_hasPureCodimension I r hI q hq]
  exact Ideal.height_mono hqp

/-- The literal surviving coordinate is a nonzerodivisor in the full mixed first-axis quotient. -/
theorem coordinate1_regular_mod_mixedAxis0 (I : Ideal A) (t : A) :
    IsRegular (Ideal.Quotient.mk (mixedIdeal I t {0}) (coordinate t 1)) := by
  have hl : IsLeftRegular (Ideal.Quotient.mk (mixedIdeal I t {0}) (coordinate t 1)) := by
    intro a b hab
    apply (mixedAxis0QuotientEquiv I t).injective
    have h := congrArg (mixedAxis0QuotientEquiv I t) hab
    rw [map_mul, map_mul, mixedAxis0QuotientEquiv_coordinate1] at h
    exact Polynomial.isRegular_X.left h
  exact ⟨hl, hl.right_of_commute (fun a => Commute.all _ a)⟩

/-- A genuinely regular quotient class avoids every actual minimal prime over its ideal. -/
theorem not_mem_minimalPrime_of_regular_quotient {R : Type*} [CommRing R]
    (I : Ideal R) (x : R) (hx : IsRegular (Ideal.Quotient.mk I x))
    (Q : Ideal R) (hQ : Q ∈ I.minimalPrimes) : x ∉ Q := by
  rw [Ideal.minimalPrimes_eq_comap] at hQ
  obtain ⟨q, hq, hqQ⟩ := hQ
  intro hv
  have hvq : Ideal.Quotient.mk I x ∈ q := by
    change x ∈ q.comap (Ideal.Quotient.mk I)
    rw [hqQ]
    exact hv
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hvq hq
    (isRegular_iff_mem_nonZeroDivisors.mp hx)

/-- No actual minimal prime of the full mixed first-axis ideal contains the original surviving coordinate. -/
theorem coordinate1_not_mem_minimalPrime_mixedAxis0 (I : Ideal A) (t : A)
    (Q : Ideal (Node A t)) (hQ : Q ∈ (mixedIdeal I t {0}).minimalPrimes) :
    coordinate t 1 ∉ Q :=
  not_mem_minimalPrime_of_regular_quotient (mixedIdeal I t {0}) (coordinate t 1)
    (coordinate1_regular_mod_mixedAxis0 I t) Q hQ

variable [IsNoetherianRing A]

/-- A selected original node coordinate forces the actual contracted prime over one more base component. -/
theorem mixed_nonempty_height_lower_bound
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ J)
    (t : A) (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (s : Finset (Fin 2)) (P : Ideal (Node A t)) [P.IsPrime]
    (hIP : mixedIdeal (intersectionIdeal D J) t s ≤ P)
    (i : Fin 2) (hi : i ∈ s) : ((J.card + 1 : ℕ) : ℕ∞) ≤ P.height := by
  classical
  let I := intersectionIdeal D J
  let : Module.Flat A (Node A t) := Algebra.NodeFamilyFlat.node_flat t
  have hIunder : I ≤ P.under A := Ideal.map_le_iff_le_comap.mp (le_trans le_sup_left hIP)
  have hcoord : coordinate t i ∈ P := hIP ((show nodeIdeal t s ≤ mixedIdeal I t s from le_sup_right)
    (Ideal.subset_span (Set.mem_image_of_mem _ hi)))
  have ht : t ∈ P.under A := by
    change algebraMap A (Node A t) t ∈ P
    rw [← Algebra.NodeDomain.nodeCoordinateProduct t]
    fin_cases i
    · exact P.mul_mem_right _ hcoord
    · exact P.mul_mem_left _ hcoord
  have hnew : intersectionIdeal D (insert C J) ≤ P.under A := by
    rw [intersectionIdeal_insert_equation D J C t heq]
    exact sup_le (Ideal.span_le.mpr (by simpa using ht)) hIunder
  have hc : HasPureCodimension (specIdealSheaf A (intersectionIdeal D (insert C J))).support
      (insert C J).card := by
    rw [intersectionIdeal_spec]
    exact hD.intersectionsCodimension _ (Finset.insert_nonempty C J)
  have h := (le_height_of_hasPureCodimension _ _ hc (P.under A) hnew).trans
    (height_under_le_of_flat P)
  simpa only [Finset.card_insert_of_notMem hC] using h

/-- Flatness and the original SNC codimension give the actual lower bound without choosing component primes. -/
theorem mixed_height_lower_bound
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ J)
    (t : A) (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (s : Finset (Fin 2)) (P : Ideal (Node A t)) [P.IsPrime]
    (hIP : mixedIdeal (intersectionIdeal D J) t s ≤ P) :
    ((J.card + s.card : ℕ) : ℕ∞) ≤ P.height := by
  classical
  let I := intersectionIdeal D J
  let : Module.Flat A (Node A t) := Algebra.NodeFamilyFlat.node_flat t
  have hIunder : I ≤ P.under A := Ideal.map_le_iff_le_comap.mp (le_trans le_sup_left hIP)
  have hbase : (J.card : ℕ∞) ≤ P.height := by
    by_cases hJ : J.Nonempty
    · have hc : HasPureCodimension (specIdealSheaf A I).support J.card := by
        rw [intersectionIdeal_spec]
        exact hD.intersectionsCodimension J hJ
      exact (le_height_of_hasPureCodimension I J.card hc (P.under A) hIunder).trans
        (height_under_le_of_flat P)
    · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      simp [he]
  by_cases h0 : 0 ∈ s <;> by_cases h1 : 1 ∈ s
  · have hs : s = Finset.univ := by ext i; fin_cases i <;> simp_all
    have haxis : mixedIdeal I t {0} ≤ P := by
      apply le_trans ?_ hIP
      exact sup_le_sup_left (nodeIdeal_mono t (by simp [hs])) _
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le haxis
    let : Q.IsPrime := hQ.isPrime
    have hQlower := mixed_nonempty_height_lower_bound D hD J C hC t heq {0} Q hQ.le 0 (by simp)
    have hvP : coordinate t 1 ∈ P := hIP ((show nodeIdeal t s ≤ mixedIdeal I t s from le_sup_right)
      (Ideal.subset_span (Set.mem_image_of_mem _ h1)))
    have hQPstrict : Q < P := lt_of_le_of_ne hQP (by
      intro he
      exact coordinate1_not_mem_minimalPrime_mixedAxis0 I t Q hQ (he.symm ▸ hvP))
    have hstrict := Ideal.height_add_one_le_of_lt_of_isPrime hQPstrict
    have hc : ((J.card + 2 : ℕ) : ℕ∞) ≤ P.height := by
      calc
        ((J.card + 2 : ℕ) : ℕ∞) = ((J.card + 1 : ℕ) : ℕ∞) + 1 := by norm_num [Nat.cast_add, add_assoc]
        _ ≤ Q.height + 1 := by simpa only [add_comm] using add_le_add_right hQlower 1
        _ ≤ P.height := hstrict
    simpa [hs] using hc
  · have hs : s = {0} := by ext i; fin_cases i <;> simp_all
    simpa [hs] using mixed_nonempty_height_lower_bound D hD J C hC t heq s P hIP 0 h0
  · have hs : s = {1} := by ext i; fin_cases i <;> simp_all
    simpa [hs] using mixed_nonempty_height_lower_bound D hD J C hC t heq s P hIP 1 h1
  · have hs : s = ∅ := by ext i; fin_cases i <;> simp_all
    simpa [hs] using hbase

/-- The original specified component equations and node coordinates give the genuine Krull upper bound. -/
theorem mixed_height_upper_bound
    (D : (Spec (CommRingCat.of A)).IdealSheafData)
    (J : Finset (DivisorComponent D)) (a : J → A)
    (ha : ∀ j, specIdealSheaf A (Ideal.span {a j}) = vanishingIdeal j.val.val)
    (t : A) (s : Finset (Fin 2)) (P : Ideal (Node A t))
    (hP : P ∈ (mixedIdeal (intersectionIdeal D J) t s).minimalPrimes) :
    P.height ≤ ((J.card + s.card : ℕ) : ℕ∞) := by
  classical
  let f : J → Node A t := fun j ↦ algebraMap A (Node A t) (a j)
  let T := (Finset.univ.image f) ∪ s.image (coordinate t)
  have hJ : Finset.univ.image (fun j : J ↦ j.val) = J := by ext j; simp
  have hI : intersectionIdeal D J = Ideal.span (Set.range a) := by
    simpa only [hJ] using intersectionIdeal_eq_span D (fun j : J ↦ j.val) a ha
  have hspan : mixedIdeal (intersectionIdeal D J) t s = Ideal.span (T : Set (Node A t)) := by
    rw [mixedIdeal, hI, Ideal.map_span, ← Set.range_comp]
    change Ideal.span (Set.range f) ⊔ Ideal.span (coordinate t '' (s : Set (Fin 2))) = _
    rw [← Ideal.span_union]
    congr 1
    ext x
    simp [T]
  have hupper : P.height ≤ (T.card : ℕ∞) :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset (by rw [← hspan]; exact hP)
  have hcard : T.card ≤ J.card + s.card := by
    calc
      T.card ≤ (Finset.univ.image f).card + (s.image (coordinate t)).card := Finset.card_union_le _ _
      _ ≤ (Finset.univ : Finset J).card + s.card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = J.card + s.card := by simp
  exact hupper.trans (by exact_mod_cast hcard)

/-- Every actual mixed minimal prime has the exact expected number of original component equations. -/
theorem mixed_minimalPrime_height
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (a : J → A)
    (ha : ∀ j, specIdealSheaf A (Ideal.span {a j}) = vanishingIdeal j.val.val)
    (C : DivisorComponent D) (hC : C ∉ J) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (s : Finset (Fin 2)) (P : Ideal (Node A t))
    (hP : P ∈ (mixedIdeal (intersectionIdeal D J) t s).minimalPrimes) :
    P.height = ((J.card + s.card : ℕ) : ℕ∞) := by
  let : P.IsPrime := hP.isPrime
  exact le_antisymm (mixed_height_upper_bound D J a ha t s P hP)
    (mixed_height_lower_bound D hD J C hC t heq s P hP.le)

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeHeights
