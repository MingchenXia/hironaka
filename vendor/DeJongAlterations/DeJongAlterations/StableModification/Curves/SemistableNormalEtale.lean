import DeJongAlterations.StableModification.Curves.SemistableOpenPlane
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Jacobian criteria on a surface étale over the plane

Let `A` be a ring and `T` an `A`-algebra which is formally étale over the plane `A[X₀, X₁]`, with
coordinates `uᵢ` and partial derivatives `∂ᵢ` (`SemistableOpen.planeDerivation`). This file proves
the Jacobian criteria used for the étale local structure of nodal curves (blueprint
`sm-semistable-normal.tex`):

* `formallyEtale_of_bijective_mapBaseChange` (Jacobi–Zariski): if `T` is formally smooth over `R`
  and `T ⊗_S Ω_{S/R} → Ω_{T/R}` is bijective, then `T` is formally étale over `S`;
* `formallyEtale_recoord`: two functions `w₀, w₁ ∈ T` whose Jacobian determinant
  `jacobian A T w = ∂₀w₀ ∂₁w₁ - ∂₁w₀ ∂₀w₁` is a unit are again étale coordinates: `T` is formally
  étale over `A[Y₀, Y₁]` via `Yⱼ ↦ wⱼ` (the type synonym `Recoord A w` carries this structure);
* `derivation_eq_sum` (chain rule), and `jacobian_mul_newJacobian`: the matrix of the new partial
  derivatives of the old coordinates is inverse to the Jacobian matrix;
* `formallyEtale_quotient_coord`: the zero locus `T/(u₀, u₁)` of the coordinates is formally étale
  over `A`.

These are the relative-dimension-two cases of Stacks, Tag 00T7 (Jacobian criterion) and Tag 0CBY
(the Hessian of the equation of a node gives étale coordinates on the critical locus).
-/

noncomputable section

open KaehlerDifferential TensorProduct

namespace DeJongAlterations.StableModification.Curves.SemistableNormal

open SemistableOpen (coord planeDerivation kaehlerBasis kaehlerBasis_apply planeDerivation_apply
  planeDerivation_coord span_D_coord derivation_ext hessian)

universe u

section JacobiZariski

/-- **Jacobi–Zariski criterion for formal étaleness.** Let `R → S → T` with `T` formally smooth over
`R`. If `T ⊗_S Ω_{S/R} → Ω_{T/R}` is bijective, then `T` is formally étale over `S`: the
Jacobi–Zariski sequence `H₁(L_{T/R}) → H₁(L_{T/S}) → T ⊗_S Ω_{S/R} → Ω_{T/R} → Ω_{T/S} → 0` gives
`H₁(L_{T/S}) = 0` and `Ω_{T/S} = 0`. -/
theorem formallyEtale_of_bijective_mapBaseChange {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T] (h : Function.Bijective (mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hΩ : Subsingleton Ω[T⁄S] := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective R S T x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R S T y
    obtain ⟨x', rfl⟩ := h.2 x
    obtain ⟨y', rfl⟩ := h.2 y
    rw [(exact_mapBaseChange_map R S T).apply_apply_eq_zero x',
      (exact_mapBaseChange_map R S T).apply_apply_eq_zero y']
  have : Algebra.FormallyUnramified S T := ⟨hΩ⟩
  have hH : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun x y => ?_⟩
    have hδ : Function.Injective (Algebra.H1Cotangent.δ R S T) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T a).mp ha
      rw [Subsingleton.elim b 0, map_zero]
    apply hδ
    exact h.1 (((Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero x).trans
      ((Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero y).symm)
  have : Algebra.FormallySmooth S T := (Algebra.formallySmooth_iff S T).mpr ⟨inferInstance, hH⟩
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

end JacobiZariski

section Plane

variable (A : Type u) [CommRing A] (T : Type u) [CommRing T] [Algebra A T]
  [Algebra (MvPolynomial (Fin 2) A) T] [IsScalarTower A (MvPolynomial (Fin 2) A) T]

/-- The Jacobian determinant `det (∂ᵢ wⱼ) = ∂₀w₀ · ∂₁w₁ - ∂₁w₀ · ∂₀w₁` of two functions `w₀, w₁`. -/
def jacobian [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T] (w : Fin 2 → T) : T :=
  planeDerivation A T 0 (w 0) * planeDerivation A T 1 (w 1) -
    planeDerivation A T 1 (w 0) * planeDerivation A T 0 (w 1)

variable [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T]

/-- **Chain rule in `Ω`**: `dp = ∂₀p du₀ + ∂₁p du₁`. -/
theorem D_eq_sum (p : T) :
    D A T p = ∑ i, planeDerivation A T i p • D A T (coord A T i) := by
  conv_lhs => rw [← (kaehlerBasis A T).sum_repr (D A T p)]
  simp only [← kaehlerBasis_apply, planeDerivation_apply, Module.Basis.coord_apply]

/-- **Chain rule**: every `A`-derivation `D'` of `T` satisfies `D' p = ∂₀p · D'u₀ + ∂₁p · D'u₁`. -/
theorem derivation_eq_sum {M : Type*} [AddCommGroup M] [Module T M] [Module A M]
    [IsScalarTower A T M] (D' : Derivation A T M) (p : T) :
    D' p = ∑ i, planeDerivation A T i p • D' (coord A T i) := by
  rw [← D'.liftKaehlerDifferential_comp_D, D_eq_sum A T p, map_sum]
  simp only [map_smul, Derivation.liftKaehlerDifferential_comp_D]

/-- The Hessian of `g` is the Jacobian determinant of its two partial derivatives. -/
theorem hessian_eq_jacobian (g : T) :
    hessian A T g = jacobian A T (fun i => planeDerivation A T i g) := by
  simp only [hessian, jacobian]
  ring

section Map

variable {A : Type u} [CommRing A] {T : Type u} [CommRing T] [Algebra A T]
  [Algebra (MvPolynomial (Fin 2) A) T] [IsScalarTower A (MvPolynomial (Fin 2) A) T]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T]
  {A' : Type u} [CommRing A'] [Algebra A A'] {T' : Type u} [CommRing T'] [Algebra A' T']
  [Algebra A T'] [IsScalarTower A A' T']
  [Algebra (MvPolynomial (Fin 2) A') T'] [IsScalarTower A' (MvPolynomial (Fin 2) A') T']
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) A') T']

/-- The Jacobian determinant commutes with coordinate-preserving maps. -/
theorem jacobian_map (φ : T →ₐ[A] T') (hφ : ∀ j, φ (coord A T j) = coord A' T' j)
    (w : Fin 2 → T) : jacobian A' T' (fun i => φ (w i)) = φ (jacobian A T w) := by
  simp only [jacobian, SemistableOpen.planeDerivation_map φ hφ, map_sub, map_mul]

end Map

end Plane

section Recoord

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type u) [CommRing A] {T : Type u} [CommRing T] [Algebra A T]

/-- The algebra `T` regarded as an algebra over the plane `A[Y₀, Y₁]` through `Yⱼ ↦ wⱼ`
(a type synonym, so that this structure does not clash with other plane structures on `T`). -/
@[nolint unusedArguments]
def Recoord (A : Type u) [CommRing A] {T : Type u} [CommRing T] [Algebra A T] (_w : Fin 2 → T) :
    Type u := T

variable (w : Fin 2 → T)

instance : CommRing (Recoord A w) := inferInstanceAs (CommRing T)
instance : Algebra A (Recoord A w) := inferInstanceAs (Algebra A T)
instance : Algebra (MvPolynomial (Fin 2) A) (Recoord A w) :=
  (MvPolynomial.aeval (R := A) (S₁ := T) w).toRingHom.toAlgebra
instance : IsScalarTower A (MvPolynomial (Fin 2) A) (Recoord A w) :=
  .of_algebraMap_eq fun a => ((MvPolynomial.aeval (R := A) (S₁ := T) w).commutes a).symm

/-- The identity `T ≃ Recoord A w`. -/
def Recoord.equiv : T ≃ₐ[A] Recoord A w := AlgEquiv.refl

@[simp]
theorem Recoord.equiv_apply (t : T) : Recoord.equiv A w t = t := rfl

theorem coord_recoord (j : Fin 2) : coord A (Recoord A w) j = Recoord.equiv A w (w j) := by
  change MvPolynomial.aeval w (MvPolynomial.X j) = w j
  simp

variable [Algebra (MvPolynomial (Fin 2) A) T] [IsScalarTower A (MvPolynomial (Fin 2) A) T]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T]

instance [Algebra.FormallySmooth A T] : Algebra.FormallySmooth A (Recoord A w) :=
  inferInstanceAs (Algebra.FormallySmooth A T)

omit [Algebra (MvPolynomial (Fin 2) A) T] [IsScalarTower A (MvPolynomial (Fin 2) A) T]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T] in
/-- The differential of the new plane structure sends `1 ⊗ dYⱼ` to `dwⱼ`. -/
theorem mapBaseChange_recoord_basis (j : Fin 2) :
    mapBaseChange A (MvPolynomial (Fin 2) A) (Recoord A w)
      (((mvPolynomialBasis A (Fin 2)).baseChange (Recoord A w)) j) =
      D A (Recoord A w) (Recoord.equiv A w (w j)) := by
  have hX : mvPolynomialBasis A (Fin 2) j =
      D A (MvPolynomial (Fin 2) A) (MvPolynomial.X j) := by
    apply (mvPolynomialBasis A (Fin 2)).repr.injective
    rw [Module.Basis.repr_self, mvPolynomialBasis_repr_D_X]
  rw [Module.Basis.baseChange_apply, hX, mapBaseChange_tmul, one_smul, map_D]
  congr 1
  change MvPolynomial.aeval w (MvPolynomial.X j) = w j
  simp

/-- If the Jacobian determinant of `w₀, w₁` is a unit, then `(x₀, x₁) ↦ x₀ dw₀ + x₁ dw₁` is a
bijection `T² → Ω_{T/A}`. -/
theorem bijective_linearCombination_D (hw : IsUnit (jacobian A T w)) :
    Function.Bijective (Fintype.linearCombination T (fun j => D A T (w j))) := by
  obtain ⟨J, hJ⟩ := hw.exists_left_inv
  have hJ' : J * (planeDerivation A T 0 (w 0) * planeDerivation A T 1 (w 1) -
      planeDerivation A T 1 (w 0) * planeDerivation A T 0 (w 1)) = 1 := hJ
  have hc : ∀ i j, (kaehlerBasis A T).repr (D A T (w j)) i = planeDerivation A T i (w j) :=
    fun _ _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [Fintype.linearCombination_apply, Fin.sum_univ_two] at hx
    have h0 := congrArg (fun ω => (kaehlerBasis A T).repr ω 0) hx
    have h1 := congrArg (fun ω => (kaehlerBasis A T).repr ω 1) hx
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hc,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at h0 h1
    funext j
    fin_cases j
    · change x 0 = 0
      linear_combination (J * planeDerivation A T 1 (w 1)) * h0 -
        (J * planeDerivation A T 0 (w 1)) * h1 - (x 0) * hJ'
    · change x 1 = 0
      linear_combination (J * planeDerivation A T 0 (w 0)) * h1 -
        (J * planeDerivation A T 1 (w 0)) * h0 - (x 1) * hJ'
  · intro ω
    set t := fun i => (kaehlerBasis A T).repr ω i
    refine ⟨![J * (planeDerivation A T 1 (w 1) * t 0 - planeDerivation A T 0 (w 1) * t 1),
      J * (planeDerivation A T 0 (w 0) * t 1 - planeDerivation A T 1 (w 0) * t 0)], ?_⟩
    apply (kaehlerBasis A T).repr.injective
    ext i
    rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
    fin_cases i
    · simp only [Fin.zero_eta, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul, hc, Matrix.cons_val_zero, Matrix.cons_val_one]
      change _ = t 0
      linear_combination (t 0) * hJ'
    · simp only [Fin.mk_one, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul, hc, Matrix.cons_val_zero, Matrix.cons_val_one]
      change _ = t 1
      linear_combination (t 1) * hJ'

/-- **New étale coordinates.** If the Jacobian determinant of `w₀, w₁` is a unit, then `T` is
formally étale over `A[Y₀, Y₁]` via `Yⱼ ↦ wⱼ`. -/
theorem formallyEtale_recoord (hw : IsUnit (jacobian A T w)) :
    Algebra.FormallyEtale (MvPolynomial (Fin 2) A) (Recoord A w) := by
  have : Algebra.FormallySmooth A T :=
    Algebra.FormallySmooth.comp A (MvPolynomial (Fin 2) A) T
  apply formallyEtale_of_bijective_mapBaseChange (R := A)
  set b := (mvPolynomialBasis A (Fin 2)).baseChange (Recoord A w)
  have key : ∀ x : Fin 2 → Recoord A w,
      mapBaseChange A (MvPolynomial (Fin 2) A) (Recoord A w) (b.equivFun.symm x) =
        Fintype.linearCombination T (fun j => D A T (w j)) x := by
    intro x
    rw [Module.Basis.equivFun_symm_apply, map_sum, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, mapBaseChange_recoord_basis]
    rfl
  have hbij : Function.Bijective
      (fun x => mapBaseChange A (MvPolynomial (Fin 2) A) (Recoord A w) (b.equivFun.symm x)) := by
    rw [funext key]
    exact bijective_linearCombination_D A w hw
  exact (Function.Bijective.of_comp_iff _ b.equivFun.symm.bijective).mp hbij

/-- **New étale coordinates**, étale version: if `T` is étale over `A[X₀, X₁]` and the Jacobian
determinant of `w₀, w₁` is a unit, then `T` is étale over `A[Y₀, Y₁]` via `Yⱼ ↦ wⱼ`. -/
theorem etale_recoord [Algebra.FinitePresentation A T] (hw : IsUnit (jacobian A T w)) :
    Algebra.Etale (MvPolynomial (Fin 2) A) (Recoord A w) := by
  have := formallyEtale_recoord A w hw
  have : Algebra.FinitePresentation A (Recoord A w) :=
    inferInstanceAs (Algebra.FinitePresentation A T)
  exact ⟨inferInstance,
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A _ (Recoord A w)⟩

variable [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) (Recoord A w)]

/-- The partial derivatives `∂'ₖ` of the new coordinates `w`, as derivations of `T`. -/
def newDeriv (k : Fin 2) : Derivation A T T := planeDerivation A (Recoord A w) k

omit [Algebra (MvPolynomial (Fin 2) A) T] [IsScalarTower A (MvPolynomial (Fin 2) A) T]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T] in
theorem newDeriv_apply (k : Fin 2) (p : T) :
    newDeriv A w k p = planeDerivation A (Recoord A w) k (Recoord.equiv A w p) := rfl

omit [Algebra (MvPolynomial (Fin 2) A) T] [IsScalarTower A (MvPolynomial (Fin 2) A) T]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T] in
/-- The new partial derivatives of the new coordinates: `∂'ₖ wⱼ = δⱼₖ`. -/
theorem newDeriv_w (k j : Fin 2) : newDeriv A w k (w j) = if j = k then 1 else 0 := by
  rw [newDeriv_apply, ← coord_recoord, planeDerivation_coord]

/-- **Chain rule** between the two coordinate systems: `∂'ₖ p = ∂₀p · ∂'ₖu₀ + ∂₁p · ∂'ₖu₁`. -/
theorem newDeriv_eq_sum (k : Fin 2) (p : T) :
    newDeriv A w k p = ∑ i, planeDerivation A T i p * newDeriv A w k (coord A T i) :=
  derivation_eq_sum A T (newDeriv A w k) p

/-- The Jacobian matrix `(∂ᵢ wⱼ)` times the matrix `(∂'ₖ uᵢ)` is the identity. -/
theorem sum_planeDerivation_mul_newDeriv (j k : Fin 2) :
    ∑ i, planeDerivation A T i (w j) * newDeriv A w k (coord A T i) =
      if j = k then 1 else 0 := by
  rw [← newDeriv_eq_sum, newDeriv_w]

/-- The Jacobian determinant `det (∂'ₖ uᵢ)` of the old coordinates in the new ones. -/
def newJacobian : T :=
  newDeriv A w 0 (coord A T 0) * newDeriv A w 1 (coord A T 1) -
    newDeriv A w 1 (coord A T 0) * newDeriv A w 0 (coord A T 1)

/-- The Jacobian determinant of the old coordinates in the new ones is inverse to `jacobian w`. -/
theorem jacobian_mul_newJacobian : jacobian A T w * newJacobian A w = 1 := by
  have e00 := sum_planeDerivation_mul_newDeriv A w 0 0
  have e01 := sum_planeDerivation_mul_newDeriv A w 0 1
  have e10 := sum_planeDerivation_mul_newDeriv A w 1 0
  have e11 := sum_planeDerivation_mul_newDeriv A w 1 1
  simp only [Fin.sum_univ_two, ↓reduceIte] at e00 e01 e10 e11
  simp only [show ((0 : Fin 2) = 1) = False from by decide,
    show ((1 : Fin 2) = 0) = False from by decide, if_false] at e01 e10
  simp only [jacobian, newJacobian]
  linear_combination
    (planeDerivation A T 0 (w 1) * newDeriv A w 1 (coord A T 0) +
      planeDerivation A T 1 (w 1) * newDeriv A w 1 (coord A T 1)) * e00 + e11 -
    (planeDerivation A T 0 (w 1) * newDeriv A w 0 (coord A T 0) +
      planeDerivation A T 1 (w 1) * newDeriv A w 0 (coord A T 1)) * e01

end Recoord

section Quotient

section General

variable (R : Type u) [CommRing R] (T : Type u) [CommRing T] [Algebra R T] (I : Ideal R)

/-- Base change of a formally étale algebra to a quotient `R/I`: `T/IT = (R/I) ⊗_R T`. -/
theorem formallyEtale_quotient_map [Algebra.FormallyEtale R T] :
    Algebra.FormallyEtale (R ⧸ I) (T ⧸ I.map (algebraMap R T)) :=
  Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T I).symm

theorem isScalarTower_quotient_map (A : Type u) [CommRing A] [Algebra A R] [Algebra A T]
    [IsScalarTower A R T] : IsScalarTower A (R ⧸ I) (T ⧸ I.map (algebraMap R T)) := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply A R (R ⧸ I), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.algebraMap_quotient_map_quotient, IsScalarTower.algebraMap_apply A T (T ⧸ _),
    Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply A R T]

end General

variable (A : Type u) [CommRing A]

/-- The ideal `(X₀, X₁)` of the origin of the plane. -/
def originIdeal : Ideal (MvPolynomial (Fin 2) A) :=
  Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}

theorem algebraMap_originQuotient_bijective :
    Function.Bijective (algebraMap A (MvPolynomial (Fin 2) A ⧸ originIdeal A)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin 2) A), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem] at ha
    have hle : originIdeal A ≤ RingHom.ker (MvPolynomial.constantCoeff (R := A) (σ := Fin 2)) := by
      rw [originIdeal, Ideal.span_le]
      rintro _ (rfl | rfl)
      · exact RingHom.mem_ker.mpr (MvPolynomial.constantCoeff_X A 0)
      · exact RingHom.mem_ker.mpr (MvPolynomial.constantCoeff_X A 1)
    have := hle ha
    rwa [RingHom.mem_ker, MvPolynomial.algebraMap_eq, MvPolynomial.constantCoeff_C] at this
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin 2) A), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq]
    have : originIdeal A = Ideal.span (MvPolynomial.X '' Set.univ) := by
      rw [Set.image_univ, originIdeal]
      congr 1
      ext m
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
    rw [this, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm' : m ≠ 0 := by
      intro h0
      rw [h0, MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [MvPolynomial.coeff_sub, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C, if_pos rfl,
        MvPolynomial.constantCoeff_eq, sub_self]
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm'
    exact ⟨i, Set.mem_univ _, hi⟩

instance : Algebra.FormallyEtale A (MvPolynomial (Fin 2) A ⧸ originIdeal A) := by
  rw [Algebra.FormallyEtale.iff_of_surjective (algebraMap_originQuotient_bijective A).2]
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap_originQuotient_bijective A).1]
  exact Ideal.mul_bot _

variable (T : Type u) [CommRing T] [Algebra A T]
  [Algebra (MvPolynomial (Fin 2) A) T] [IsScalarTower A (MvPolynomial (Fin 2) A) T]

omit [Algebra A T] [IsScalarTower A (MvPolynomial (Fin 2) A) T] in
theorem map_originIdeal :
    (originIdeal A).map (algebraMap (MvPolynomial (Fin 2) A) T) =
      Ideal.span {coord A T 0, coord A T 1} := by
  rw [originIdeal, Ideal.map_span, Set.image_pair]

/-- **The zero locus of étale coordinates is étale over the base**: if `T` is formally étale over
`A[X₀, X₁]`, then `T/(u₀, u₁) = A ⊗_{A[X]} T` is formally étale over `A`. -/
theorem formallyEtale_quotient_coord [Algebra.FormallyEtale (MvPolynomial (Fin 2) A) T] :
    Algebra.FormallyEtale A (T ⧸ Ideal.span {coord A T 0, coord A T 1}) := by
  have := formallyEtale_quotient_map (MvPolynomial (Fin 2) A) T (originIdeal A)
  have := isScalarTower_quotient_map (MvPolynomial (Fin 2) A) T (originIdeal A) A
  have : Algebra.FormallyEtale A (T ⧸ (originIdeal A).map (algebraMap _ T)) :=
    .comp A (MvPolynomial (Fin 2) A ⧸ originIdeal A) _
  exact .of_equiv (Ideal.quotientEquivAlgOfEq A (map_originIdeal A T))

/-- `T/(u₀, u₁)` is étale over `A` when `T` is étale over `A[X₀, X₁]`. -/
theorem etale_quotient_coord [Algebra.Etale (MvPolynomial (Fin 2) A) T] :
    Algebra.Etale A (T ⧸ Ideal.span {coord A T 0, coord A T 1}) := by
  have := formallyEtale_quotient_coord A T
  have : Algebra.FinitePresentation A T :=
    Algebra.FinitePresentation.trans A (MvPolynomial (Fin 2) A) T
  exact ⟨inferInstance, Algebra.FinitePresentation.quotient
    (Submodule.fg_def.mpr ⟨_, Set.toFinite _, rfl⟩)⟩

end Quotient

end DeJongAlterations.StableModification.Curves.SemistableNormal
