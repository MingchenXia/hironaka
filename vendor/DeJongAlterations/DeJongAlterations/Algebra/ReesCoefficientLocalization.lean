import DeJongAlterations.Algebra.ReesLocalization

/-!
# Rees localization for arbitrary coefficient localization rings

The actual polynomial coefficient map makes the extended-ideal Rees ring a
localization of the original Rees ring. The coefficient localization ring is
arbitrary, and no comparison with a canonical localization is supplied.
-/

open Polynomial
open DeJongAlterations.Algebra.ReesLocalization

noncomputable section

namespace DeJongAlterations.Algebra.ReesCoefficientLocalization

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual coefficient map, with no chosen coefficient-localization comparison. -/
instance reesCoefficientAlgebra (I : Ideal R) :
    Algebra (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) :=
  (ReesLocalization.reesMap I (algebraMap R S)).toAlgebra

@[simp]
theorem reesCoefficient_algebraMap (I : Ideal R) :
    algebraMap (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) =
      ReesLocalization.reesMap I (algebraMap R S) := rfl

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
    _ = f (a * t ^ m + b * t ^ n) := by
      rw [ha, hb, map_add, map_mul, map_mul, map_pow, map_pow]

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

variable (I : Ideal R) (s : R) [IsLocalization.Away s S]

/-- An actual localized homogeneous Rees component has an original homogeneous numerator. -/
theorem reesCoefficient_component_surj
    (p : reesAlgebra (I.map (algebraMap R S))) (n : ℕ) :
    ∃ (k : ℕ) (a : reesAlgebra I),
      (reesComponent (I.map (algebraMap R S)) n p :
          reesAlgebra (I.map (algebraMap R S))) *
        reesMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s) ^ k =
      reesMap I (algebraMap R S) a := by
  have hc : (p : S[X]).coeff n ∈ (I ^ n).map (algebraMap R S) := by
    rw [Ideal.map_pow]
    exact p.property n
  obtain ⟨⟨a, d⟩, hd⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) S).mp hc
  obtain ⟨k, hk⟩ := d.property
  refine ⟨k, ⟨monomial n a, reesAlgebra.monomial_mem.mpr a.property⟩, ?_⟩
  rw [reesMap_algebraMap]
  apply Subtype.ext
  change monomial n ((p : S[X]).coeff n) * C (algebraMap R S s) ^ k =
    Polynomial.map (algebraMap R S) (monomial n (a : R))
  rw [← C_pow, monomial_mul_C, Polynomial.map_monomial]
  apply congrArg (monomial n)
  simpa only [← hk, map_pow] using hd

/-- One power of the source coefficient clears an arbitrary actual target Rees polynomial. -/
theorem reesCoefficient_surj (p : reesAlgebra (I.map (algebraMap R S))) :
    ∃ (n : ℕ) (a : reesAlgebra I),
      p * algebraMap (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S)))
          (algebraMap R (reesAlgebra I) s) ^ n =
        algebraMap (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) a := by
  have hp : p = ∑ n ∈ (p : S[X]).support,
      (reesComponent (I.map (algebraMap R S)) n p :
        reesAlgebra (I.map (algebraMap R S))) := by
    apply Subtype.ext
    change (p : S[X]) = (reesAlgebra (I.map (algebraMap R S))).val _
    rw [map_sum]
    exact (p : S[X]).as_sum_support
  change ∃ (n : ℕ) (a : reesAlgebra I),
    p * reesMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s) ^ n =
    reesMap I (algebraMap R S) a
  rw [hp]
  exact clearDenominator_sum (A := reesAlgebra I)
    (B := reesAlgebra (I.map (algebraMap R S))) (reesMap I (algebraMap R S))
    (algebraMap R (reesAlgebra I) s) _ _
    (fun n _ => reesCoefficient_component_surj I s p n)

attribute [local instance] Polynomial.algebra

/-- The actual coefficient map detects equality after a source coefficient power. -/
theorem reesCoefficient_exists_of_eq (p q : reesAlgebra I)
    (h : algebraMap (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) p =
      algebraMap (reesAlgebra I) (reesAlgebra (I.map (algebraMap R S))) q) :
    ∃ n : ℕ, algebraMap R (reesAlgebra I) s ^ n * p =
      algebraMap R (reesAlgebra I) s ^ n * q := by
  let : IsLocalization.Away (C s) S[X] := by
    have H := Polynomial.isLocalization (Submonoid.powers s) S
    rw [Submonoid.map_powers] at H
    exact H
  have hpoly : algebraMap R[X] S[X] (p : R[X]) =
      algebraMap R[X] S[X] (q : R[X]) :=
    congrArg (fun z : reesAlgebra (I.map (algebraMap R S)) => (z : S[X])) h
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (C s) hpoly
  exact ⟨n, Subtype.ext hn⟩

/-- Any actual coefficient localization induces the actual Rees coefficient localization. -/
instance reesCoefficient_isLocalization :
    IsLocalization.Away (algebraMap R (reesAlgebra I) s)
      (reesAlgebra (I.map (algebraMap R S))) := by
  apply IsLocalization.Away.mk (algebraMap R (reesAlgebra I) s)
  · change IsUnit (reesMap I (algebraMap R S) (algebraMap R (reesAlgebra I) s))
    rw [reesMap_algebraMap]
    exact (IsLocalization.Away.algebraMap_isUnit (S := S) s).map
      (algebraMap S (reesAlgebra (I.map (algebraMap R S))))
  · exact reesCoefficient_surj I s
  · exact reesCoefficient_exists_of_eq I s

end DeJongAlterations.Algebra.ReesCoefficientLocalization
