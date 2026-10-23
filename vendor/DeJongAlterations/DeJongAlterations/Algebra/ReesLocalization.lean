import DeJongAlterations.Geometry.AffineBlowup
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Tactic.Ring

/-!
# Coefficient localization of the actual Rees algebra

Coefficientwise polynomial mapping produces the graded Rees map. Localized
ideal membership supplies genuine homogeneous numerators, and finite sums
give the localization denominator for every target Rees element.
-/

open Polynomial

noncomputable section

namespace DeJongAlterations.Algebra.ReesLocalization

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Coefficientwise polynomial mapping on actual Rees subalgebras. -/
def reesMap (I : Ideal R) (f : R →+* S) : reesAlgebra I →+* reesAlgebra (I.map f) where
  toFun p := ⟨Polynomial.map f p, by
    intro n
    rw [Polynomial.coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f (p.property n)⟩
  map_one' := Subtype.ext (Polynomial.map_one f)
  map_mul' p q := Subtype.ext (Polynomial.map_mul f)
  map_zero' := Subtype.ext (Polynomial.map_zero f)
  map_add' p q := Subtype.ext (Polynomial.map_add f)

@[simp]
theorem reesMap_algebraMap (I : Ideal R) (f : R →+* S) (a : R) :
    reesMap I f (algebraMap R (reesAlgebra I) a) =
      algebraMap S (reesAlgebra (I.map f)) (f a) := by
  apply Subtype.ext
  exact Polynomial.map_C f

/-- The actual coefficient map preserves the native homogeneous Rees pieces. -/
def reesGradedMap (I : Ideal R) (f : R →+* S) :
    reesGrading I →+*ᵍ reesGrading (I.map f) where
  __ := reesMap I f
  map_mem := by
    intro n p hp
    rw [mem_reesGrading_iff] at hp ⊢
    change Polynomial.map f (p : R[X]) =
      monomial n ((Polynomial.map f (p : R[X])).coeff n)
    rw [hp, Polynomial.map_monomial]
    simp

/-- The target Rees ring's canonical algebra structure is the actual coefficient map. -/
instance reesLocalizationAlgebra (I : Ideal R) (s : R) :
    Algebra (reesAlgebra I)
      (reesAlgebra (I.map (algebraMap R (Localization.Away s)))) :=
  (reesMap I (algebraMap R (Localization.Away s))).toAlgebra

private theorem clearDenominator_zero {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (t : A) :
    ∃ (n : ℕ) (a : A), (0 : B) * f t ^ n = f a := by
  exact ⟨0, 0, by simp⟩

private theorem clearDenominator_add {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (t : A) {x y : B}
    (hx : ∃ (n : ℕ) (a : A), x * f t ^ n = f a)
    (hy : ∃ (n : ℕ) (a : A), y * f t ^ n = f a) :
    ∃ (n : ℕ) (a : A), (x + y) * f t ^ n = f a := by
  obtain ⟨n, a, ha⟩ := hx
  obtain ⟨m, b, hb⟩ := hy
  refine ⟨n + m, a * t ^ m + b * t ^ n, ?_⟩
  calc
    (x + y) * f t ^ (n + m) =
      (x * f t ^ n) * f t ^ m + (y * f t ^ m) * f t ^ n := by
        rw [pow_add]
        ring
    _ = f (a * t ^ m + b * t ^ n) := by rw [ha, hb, map_add, map_mul, map_mul, map_pow, map_pow]

private theorem clearDenominator_sum {A B : Type u} {ι : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (t : A) (F : Finset ι) (z : ι → B)
    (hz : ∀ i ∈ F, ∃ (n : ℕ) (a : A), z i * f t ^ n = f a) :
    ∃ (n : ℕ) (a : A), (∑ i ∈ F, z i) * f t ^ n = f a := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using clearDenominator_zero f t
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi]
    exact clearDenominator_add f t (hz i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hz j (Finset.mem_insert_of_mem hj)))

variable (I : Ideal R) (s : R)

/-- Every actual target homogeneous component has a denominator with numerator
in the original Rees algebra. -/
theorem reesLocalization_component_surj
    (p : reesAlgebra (I.map (algebraMap R (Localization.Away s)))) (n : ℕ) :
    ∃ (k : ℕ) (a : reesAlgebra I),
      (reesComponent (I.map (algebraMap R (Localization.Away s))) n p :
          reesAlgebra (I.map (algebraMap R (Localization.Away s)))) *
        reesMap I (algebraMap R (Localization.Away s))
          (algebraMap R (reesAlgebra I) s) ^ k =
      reesMap I (algebraMap R (Localization.Away s)) a := by
  have hc : (p : (Localization.Away s)[X]).coeff n ∈
      (I ^ n).map (algebraMap R (Localization.Away s)) := by
    rw [Ideal.map_pow]
    exact p.property n
  obtain ⟨⟨a, d⟩, hd⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) (Localization.Away s)).mp hc
  obtain ⟨k, hk⟩ := d.property
  refine ⟨k, ⟨monomial n a, reesAlgebra.monomial_mem.mpr a.property⟩, ?_⟩
  rw [reesMap_algebraMap]
  apply Subtype.ext
  change monomial n ((p : (Localization.Away s)[X]).coeff n) *
      C (algebraMap R (Localization.Away s) s) ^ k =
    Polynomial.map (algebraMap R (Localization.Away s)) (monomial n (a : R))
  rw [← C_pow, monomial_mul_C, Polynomial.map_monomial]
  apply congrArg (monomial n)
  simpa only [← hk, map_pow] using hd

/-- A single power of the original degree-zero constant clears any target Rees polynomial. -/
theorem reesLocalization_surj
    (p : reesAlgebra (I.map (algebraMap R (Localization.Away s)))) :
    ∃ (n : ℕ) (a : reesAlgebra I),
      p * algebraMap (reesAlgebra I)
          (reesAlgebra (I.map (algebraMap R (Localization.Away s))))
          (algebraMap R (reesAlgebra I) s) ^ n =
        algebraMap (reesAlgebra I)
          (reesAlgebra (I.map (algebraMap R (Localization.Away s)))) a := by
  have hp : p = ∑ n ∈ (p : (Localization.Away s)[X]).support,
      (reesComponent (I.map (algebraMap R (Localization.Away s))) n p :
        reesAlgebra (I.map (algebraMap R (Localization.Away s)))) := by
    apply Subtype.ext
    change (p : (Localization.Away s)[X]) =
      (reesAlgebra (I.map (algebraMap R (Localization.Away s)))).val _
    rw [map_sum]
    exact (p : (Localization.Away s)[X]).as_sum_support
  change ∃ (n : ℕ) (a : reesAlgebra I),
    p * reesMap I (algebraMap R (Localization.Away s))
      (algebraMap R (reesAlgebra I) s) ^ n =
    reesMap I (algebraMap R (Localization.Away s)) a
  rw [hp]
  exact clearDenominator_sum (A := reesAlgebra I)
    (B := reesAlgebra (I.map (algebraMap R (Localization.Away s))))
    (reesMap I (algebraMap R (Localization.Away s)))
    (algebraMap R (reesAlgebra I) s) _ _ (fun n _ => reesLocalization_component_surj I s p n)

attribute [local instance] Polynomial.algebra

/-- Equal coefficient-localized Rees elements are equal after a power of the
original degree-zero constant is multiplied on the source. -/
theorem reesLocalization_exists_of_eq (p q : reesAlgebra I)
    (h : algebraMap (reesAlgebra I)
      (reesAlgebra (I.map (algebraMap R (Localization.Away s)))) p =
      algebraMap (reesAlgebra I)
        (reesAlgebra (I.map (algebraMap R (Localization.Away s)))) q) :
    ∃ n : ℕ, algebraMap R (reesAlgebra I) s ^ n * p =
      algebraMap R (reesAlgebra I) s ^ n * q := by
  let : IsLocalization.Away (C s) ((Localization.Away s)[X]) := by
    have H := Polynomial.isLocalization (Submonoid.powers s) (Localization.Away s)
    rw [Submonoid.map_powers] at H
    exact H
  have hpoly : algebraMap R[X] ((Localization.Away s)[X]) (p : R[X]) =
      algebraMap R[X] ((Localization.Away s)[X]) (q : R[X]) :=
    congrArg (fun z : reesAlgebra (I.map (algebraMap R (Localization.Away s))) =>
      (z : (Localization.Away s)[X])) h
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (C s) hpoly
  exact ⟨n, Subtype.ext hn⟩

/-- The actual localized Rees ring is the localization at the actual
degree-zero coefficient s, including for zero divisors and s=0. -/
instance reesLocalization_isLocalization :
    IsLocalization.Away (algebraMap R (reesAlgebra I) s)
      (reesAlgebra (I.map (algebraMap R (Localization.Away s)))) := by
  apply IsLocalization.Away.mk (algebraMap R (reesAlgebra I) s)
  · change IsUnit (reesMap I (algebraMap R (Localization.Away s))
      (algebraMap R (reesAlgebra I) s))
    rw [reesMap_algebraMap]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s).map
      (algebraMap (Localization.Away s)
        (reesAlgebra (I.map (algebraMap R (Localization.Away s)))))
  · exact reesLocalization_surj I s
  · exact reesLocalization_exists_of_eq I s

end DeJongAlterations.Algebra.ReesLocalization
