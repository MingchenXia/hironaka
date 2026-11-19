import Hironaka.Algebra.ProjectiveLinearCoordinates

/-!
# Actual remaining-coordinate automorphisms induced from the original centre-line stabilizer
-/

noncomputable section

namespace Hironaka.Algebra.ProjectiveLinearCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The literal remaining-coordinate linear map. -/
def tailLinearMap : (Fin (n + 2) → k) →ₗ[k] (Fin (n + 1) → k) where
  toFun x i := x i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal linear section inserting a zero first coordinate. -/
def zeroSectionLinearMap : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 2) → k) where
  toFun x := Fin.cases 0 x
  map_add' x y := by ext i; exact Fin.cases (by simp) (fun j => by simp) i
  map_smul' a x := by ext i; exact Fin.cases (by simp) (fun j => by simp) i

/-- Every original vector decomposes into its original first-coordinate centre part and its literal remaining coordinates. -/
theorem vector_eq_head_add_zeroSection (x : Fin (n + 2) → k) :
    x = x 0 • Pi.single 0 1 + zeroSectionLinearMap k n (tailLinearMap k n x) := by
  ext i
  exact Fin.cases (by simp [zeroSectionLinearMap])
    (fun j => by simp [zeroSectionLinearMap, tailLinearMap]) i

/-- The actual remaining-coordinate map of the original whole linear automorphism. -/
def remainingLinearMap (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) :
    (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k) where
  toFun x := tailLinearMap k n (e (zeroSectionLinearMap k n x))
  map_add' x y := by simp only [map_add]
  map_smul' a x := by simp only [map_smul, RingHom.id_apply]

/-- Preservation of the original centre line yields the literal whole-vector remaining-coordinate triangle. -/
theorem remainingLinearMap_tail
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) (x : Fin (n + 2) → k) :
    tailLinearMap k n (e x) = remainingLinearMap k n e (tailLinearMap k n x) := by
  have h := vector_eq_head_add_zeroSection k n x
  apply congrArg (fun y => tailLinearMap k n (e y)) at h
  ext i
  have hi := congrFun h i
  simpa only [map_add, map_smul, he, tailLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero _),
    smul_zero, zero_add, remainingLinearMap, LinearMap.comp_apply] using hi

/-- The inverse of the SAME actual entire linear automorphism preserves the same original centre line with the actual inverse coefficient. -/
theorem inverse_apply_centre_line
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k) (hc : c ≠ 0)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) :
    e.symm (Pi.single 0 1) = c⁻¹ • Pi.single 0 1 := by
  apply e.injective
  simp only [e.apply_symm_apply, map_smul, he, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The whole original inverse identities internally prove inverse identities of the actual remaining-coordinate maps. -/
theorem remainingLinearMap_inverse
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k) (hc : c ≠ 0)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) (x : Fin (n + 1) → k) :
    remainingLinearMap k n e.symm (remainingLinearMap k n e x) = x := by
  have h := remainingLinearMap_tail k n e.symm c⁻¹ (inverse_apply_centre_line k n e c hc he)
    (e (zeroSectionLinearMap k n x))
  rw [e.symm_apply_apply] at h
  ext i
  exact congrFun h.symm i

/-- The actual invertible remaining-coordinate comparison is constructed internally from the original entire automorphism and original centre-line equality. -/
def remainingLinearEquiv
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k) (hc : c ≠ 0)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) :
    (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k) where
  __ := remainingLinearMap k n e
  invFun := remainingLinearMap k n e.symm
  left_inv := remainingLinearMap_inverse k n e c hc he
  right_inv := by
    intro x
    exact remainingLinearMap_inverse k n e.symm c⁻¹
      (inv_ne_zero hc) (inverse_apply_centre_line k n e c hc he) x

/-- The entire induced invertible map retains the literal original whole-vector triangle. -/
theorem remainingLinearEquiv_tail
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k) (hc : c ≠ 0)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) (x : Fin (n + 2) → k) :
    tailLinearMap k n (e x) = remainingLinearEquiv k n e c hc he (tailLinearMap k n x) :=
  remainingLinearMap_tail k n e c he x

end Hironaka.Algebra.ProjectiveLinearCoordinates
