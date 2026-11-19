import Hironaka.Resolution.Algebraic.PolynomialTranslationIdealDescent
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coordinated polynomial centre descent along the actual zero section

Source-first proof: `mv-polynomial-coordinate-translation-descent-20261102.tex`.
This is the finite-coordinate ring-theoretic producer needed on actual padded
affine charts. Native same-stage translation equivariance and history descent
are separate consumers, not conclusions of this module.
-/

set_option autoImplicit false

namespace Hironaka.Resolution.Algebraic.MvPolynomialCoordinateTranslationDescent

noncomputable section
open MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R]

/-- The actual one-unit shift of one original polynomial coordinate. -/
def coordinateShift {σ : Type*} (j : σ) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + if i = j then 1 else 0)

@[simp] private theorem coordinateShift_C {σ : Type*} (j : σ) (r : R) :
    coordinateShift j (C r) = C r := by
  simp [coordinateShift]

@[simp] private theorem coordinateShift_X {σ : Type*} (j i : σ) :
    coordinateShift j (X i : MvPolynomial σ R) = X i + if i = j then 1 else 0 := by
  simp [coordinateShift]

private theorem finSucc_rename (n : ℕ) (f : MvPolynomial (Fin n) R) :
    finSuccEquiv R n (rename Fin.succ f) = Polynomial.C f := by
  have h : (finSuccEquiv R n).toRingHom.comp (rename Fin.succ).toRingHom =
      (Polynomial.C : MvPolynomial (Fin n) R →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [finSuccEquiv_apply]
    · intro j
      simp [finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h f

private theorem finSucc_shift_zero (n : ℕ) (f : MvPolynomial (Fin (n+1)) R) :
    finSuccEquiv R n (coordinateShift 0 f) = Polynomial.taylor 1 (finSuccEquiv R n f) := by
  have h : (finSuccEquiv R n).toRingHom.comp (coordinateShift 0) =
      (Polynomial.taylorAlgHom (1 : MvPolynomial (Fin n) R)).toRingHom.comp
        (finSuccEquiv R n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [finSuccEquiv_X_zero, Polynomial.taylor_X]
      · simp [finSuccEquiv_X_succ, Polynomial.taylor_C]
  exact DFunLike.congr_fun h f

private theorem shift_succ_rename (n : ℕ) (j : Fin n) (f : MvPolynomial (Fin n) R) :
    coordinateShift j.succ (rename Fin.succ f) = rename Fin.succ (coordinateShift j f) := by
  have h : (coordinateShift (R := R) j.succ).comp
      (rename Fin.succ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin (n+1)) R).toRingHom =
      (rename Fin.succ).toRingHom.comp (coordinateShift j) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      change coordinateShift j.succ (rename Fin.succ (X i : MvPolynomial (Fin n) R)) =
        rename Fin.succ (coordinateShift j (X i : MvPolynomial (Fin n) R))
      by_cases hij : i = j
      · subst i
        simp
      · simp [hij]
  exact DFunLike.congr_fun h f

/-- Each coefficient of each member of the SAME coordinate-shift-stable ideal
is derived internally by induction on the actual number of coordinates. -/
theorem fin_coefficient_mem_of_coordinate_shift_stable (K : Type*)
    [Field K] [CharZero K] [Algebra K R] (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) R))
    (hshift : ∀ j, ∀ f ∈ J, coordinateShift j f ∈ J)
    (f : MvPolynomial (Fin n) R) (hf : f ∈ J) (m : Fin n →₀ ℕ) : C (f.coeff m) ∈ J := by
  classical
  induction n with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    rw [hm, ← f.eq_C_of_isEmpty]
    exact hf
  | succ n ih =>
    let e := finSuccEquiv R n
    let J' := J.comap e.symm.toRingHom
    let J₀ := J.comap (rename Fin.succ).toRingHom
    have hshift' : ∀ g ∈ J', Polynomial.taylor 1 g ∈ J' := by
      intro g hg
      change e.symm (Polynomial.taylor 1 g) ∈ J
      have hs := hshift 0 (e.symm g) hg
      convert hs using 1
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      change Polynomial.taylor 1 g =
        finSuccEquiv R n (coordinateShift 0 ((finSuccEquiv R n).symm g))
      rw [finSucc_shift_zero, AlgEquiv.apply_symm_apply]
    have hshift₀ : ∀ j, ∀ g ∈ J₀, coordinateShift j g ∈ J₀ := by
      intro j g hg
      change rename Fin.succ (coordinateShift j g) ∈ J
      rw [← shift_succ_rename]
      exact hshift j.succ _ hg
    have he : e f ∈ J' := by
      change e.symm (e f) ∈ J
      simpa only [AlgEquiv.symm_apply_apply] using hf
    have hc := PolynomialTranslationIdealDescent.coefficient_mem_of_shift_stable
      K J' hshift' (e f) he (m 0)
    have hbase : (e f).coeff (m 0) ∈ J₀ := by
      change rename Fin.succ ((e f).coeff (m 0)) ∈ J
      change e.symm (Polynomial.C ((e f).coeff (m 0))) ∈ J at hc
      rw [← finSucc_rename] at hc
      simpa only [e, AlgEquiv.symm_apply_apply] using hc
    have h := ih J₀ hshift₀ ((e f).coeff (m 0)) hbase m.tail
    change rename Fin.succ (C (((e f).coeff (m 0)).coeff m.tail)) ∈ J at h
    change rename Fin.succ (C (((finSuccEquiv R n f).coeff (m 0)).coeff m.tail)) ∈ J at h
    simpa only [rename_C, finSuccEquiv_coeff_coeff, Finsupp.cons_tail] using h

private theorem fin_ideal_eq_map_comap (K : Type*)
    [Field K] [CharZero K] [Algebra K R] (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) R))
    (hshift : ∀ j, ∀ f ∈ J, coordinateShift j f ∈ J) :
    J = Ideal.map (C : R →+* MvPolynomial (Fin n) R) (J.comap C) := by
  apply le_antisymm
  · intro f hf
    apply MvPolynomial.mem_map_C_iff.mpr
    exact fin_coefficient_mem_of_coordinate_shift_stable K n J hshift f hf
  · exact Ideal.map_comap_le

private theorem rename_shift {σ τ : Type*} (e : σ ≃ τ) (j : σ)
    (f : MvPolynomial σ R) :
    renameEquiv R e (coordinateShift j f) =
      coordinateShift (e j) (renameEquiv R e f) := by
  have h : (renameEquiv R e).toRingHom.comp (coordinateShift j) =
      (coordinateShift (e j)).comp (renameEquiv R e).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp [renameEquiv_apply, e.injective.eq_iff]
  exact DFunLike.congr_fun h f

/-- Actual stability under ALL original coordinate shifts constructs the
descended ideal on the base. No contracted ideal is supplied as input. -/
theorem ideal_eq_map_comap_of_coordinate_shift_stable (K : Type*)
    [Field K] [CharZero K] [Algebra K R] (σ : Type*) [Finite σ]
    (J : Ideal (MvPolynomial σ R))
    (hshift : ∀ j, ∀ f ∈ J, coordinateShift j f ∈ J) :
    J = Ideal.map (C : R →+* MvPolynomial σ R) (J.comap C) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  let E := renameEquiv R e
  let J' := J.comap E.symm.toRingHom
  have hs : ∀ j, ∀ f ∈ J', coordinateShift j f ∈ J' := by
    intro j f hf
    change E.symm (coordinateShift j f) ∈ J
    have h := hshift (e.symm j) (E.symm f) hf
    convert h using 1
    apply E.injective
    rw [AlgEquiv.apply_symm_apply]
    change coordinateShift j f =
      renameEquiv R e (coordinateShift (e.symm j) ((renameEquiv R e).symm f))
    rw [rename_shift, Equiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hfin := fin_ideal_eq_map_comap K (Fintype.card σ) J' hs
  have hC : E.symm.toRingHom.comp (C : R →+* MvPolynomial (Fin (Fintype.card σ)) R) =
      (C : R →+* MvPolynomial σ R) := by
    ext r
    simp [E]
  calc
    J = J'.map E.symm.toRingHom :=
      (Ideal.map_comap_of_surjective _ E.symm.surjective _).symm
    _ = (Ideal.map C (J'.comap C)).map E.symm.toRingHom := congrArg (Ideal.map _) hfin
    _ = Ideal.map C (J.comap C) := by
      rw [Ideal.map_map, hC]
      congr 1
      exact Ideal.comap_comap _ _ |>.trans (congrArg (Ideal.comap · J) hC)

/-- The SAME actual ideal is extended from its OWN image under evaluation of
ALL coordinates at zero, the genuine affine zero section. -/
theorem ideal_eq_extension_of_zero_section_of_coordinate_shift_stable (K : Type*)
    [Field K] [CharZero K] [Algebra K R] (σ : Type*) [Finite σ]
    (J : Ideal (MvPolynomial σ R))
    (hshift : ∀ j, ∀ f ∈ J, coordinateShift j f ∈ J) :
    J = Ideal.map (C : R →+* MvPolynomial σ R)
      (Ideal.map (eval (fun _ => (0 : R))) J) := by
  have h := ideal_eq_map_comap_of_coordinate_shift_stable K σ J hshift
  have hzero : (eval (fun _ : σ => (0 : R))).comp C = RingHom.id R := by
    ext r
    simp
  have hc : Ideal.map (eval (fun _ : σ => (0 : R))) J = J.comap C := by
    conv_lhs => rw [h]
    rw [Ideal.map_map, hzero, Ideal.map_id]
  exact h.trans (congrArg (Ideal.map C) hc.symm)

end
end Hironaka.Resolution.Algebraic.MvPolynomialCoordinateTranslationDescent
