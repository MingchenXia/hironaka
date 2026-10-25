/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.Cech
import DeJongAlterations.Geometry.ProperSteinProjectiveCechFiniteGraded
import Mathlib.Algebra.Polynomial.Module.Basic

/-!
# Projective coordinates and the graded module of twisted sections

This file starts the finiteness part of the Claude team's cohomology library (lane COH2,
blueprint `sm-cohomology-finite.tex`, plan `PLAN-SM-GEOM.md` chapter F). The finiteness of the
cohomology of a coherent module `F` on a projective `A`-scheme (Hartshorne III.5.2, EGA III 2.2.1;
used by Temkin, *Stable modification of relative curves*, Lemma 4.4.2 and Proposition 4.4.6) is
reduced to Codex's finiteness of the coordinate Čech cohomology of finite graded modules over
`A[x_i]` (`ProperSteinProjectiveCech.finiteGradedPolynomialCoordinateCech_homology_finite`) by
Serre's construction `Γ_*(F) = ⊕_k Γ(X, F(k))`. Twisting sheaves are never constructed: a
section of `F(k)` is recorded through its dehomogenizations `s/x_i^k ∈ Γ(U_i, F)` on the
coordinate opens.

## The coordinate datum

`ProjectiveCoordinates X A c` (blueprint `def:sm-projective-coordinates`) is a finite family of
affine opens `U_i` covering `X`, with sections `ratio i j ∈ Γ(U_i, 𝒪_X)` (the function
`x_j / x_i`) such that `U_i ∩ U_j = D(ratio i j)` inside `U_i`, `ratio i i = 1`, the cocycle
identity `ratio i j · ratio j k = ratio i k` holds on `U_i ∩ U_j`, and `Γ(U_i, 𝒪_X)` is generated
over `A` by the `ratio i j`, `j ∈ ι`. A closed subscheme of `ℙⁿ_A` carries such a datum
(`FiniteProjective.lean`). All finite intersections of the `U_i` are basic opens of affine opens,
so the datum is a `FiniteAffineCover`.

## The ambient graded module

For a module `F` on `X` let `Ambient D F = ∏_i Γ(U_i, F)[T]` (`PolynomialModule`). The
polynomial ring `S = A[x_i]` acts on the `i`-th factor through `x_j ↦ ratio i j · T`, and the
grading by the `T`-degree (`grading`) makes `Ambient D F` a graded `S`-module
(`SetLike.GradedSMul` for the standard grading `polynomialIntegralGrading`). The submodule
`gstar D F` of compatible families (`(e_i)_k = (ratio i j)^k (e_j)_k` on `U_i ∩ U_j`) is
`Γ_*(F)` in nonnegative degrees: a homogeneous element of degree `k` is a section `s` of `F(k)`,
recorded by `e_i = s / x_i^k`.

## Main declarations

* `ProjectiveCoordinates`, `ProjectiveCoordinates.toFiniteAffineCover`,
  `ProjectiveCoordinates.inf_eq_basicOpen_prod`.
* `ProjectiveCoordinates.Ambient`, `ProjectiveCoordinates.grading`,
  `ProjectiveCoordinates.isInternal_grading`, `ProjectiveCoordinates.gradedSMul`.
* `ProjectiveCoordinates.gstar`: `Γ_*(F)` as an `S`-submodule.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

variable {X : Scheme.{u}} {A : Type u} [CommRing A]

/-- **Projective coordinates** on a scheme `X` over a ring `A` (with structure map
`c : A →+* Γ(X, ⊤)`): a finite family of affine opens `U i` covering `X`, together with the
functions `ratio i j ∈ Γ(U i, 𝒪_X)` (to be thought of as `x_j / x_i`) such that
`U i ∩ U j = D(ratio i j)`, `ratio i i = 1`, `ratio i j * ratio j k = ratio i k` on `U i ∩ U j`, and
`Γ(U i, 𝒪_X)` is generated as an `A`-algebra by the `ratio i j` (blueprint
`def:sm-projective-coordinates`). -/
structure ProjectiveCoordinates (X : Scheme.{u}) (A : Type u) [CommRing A]
    (c : A →+* Γ(X, ⊤)) where
  /-- The index type of the coordinates. -/
  ι : Type u
  [linearOrder : LinearOrder ι]
  [fintype : Fintype ι]
  /-- The coordinate opens `U_i = D₊(x_i)`. -/
  U : ι → X.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The function `x_j / x_i` on `U_i`. -/
  ratio : ∀ i, ι → Γ(X, U i)
  inf_eq_basicOpen : ∀ i j, U i ⊓ U j = X.basicOpen (ratio i j)
  ratio_self : ∀ i, ratio i i = 1
  ratio_mul : ∀ i j k,
    X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (ratio i j) *
        X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (ratio j k) =
      X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (ratio i k)
  surjective : ∀ i,
    Function.Surjective (MvPolynomial.eval₂Hom (sectionsRingHom c (le_top : U i ≤ ⊤)) (ratio i))

attribute [instance] ProjectiveCoordinates.linearOrder ProjectiveCoordinates.fintype

namespace ProjectiveCoordinates

variable {c : A →+* Γ(X, ⊤)} (D : ProjectiveCoordinates X A c)

section Opens

/-- `U j ∩ U_T = D(∏_{l ∈ T} ratio j l)` inside `U j`. -/
theorem inf_inf_eq_basicOpen_prod (j : D.ι) (T : Finset D.ι) :
    D.U j ⊓ T.inf D.U = X.basicOpen (∏ l ∈ T, D.ratio j l) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.inf_empty, Finset.prod_empty, Scheme.basicOpen_one, inf_top_eq]
  | insert l T hl ih =>
    rw [Finset.inf_insert, Finset.prod_insert hl, Scheme.basicOpen_mul, ← ih,
      ← D.inf_eq_basicOpen, inf_inf_distrib_left]

/-- For `j ∈ T`, `U_T = D(∏_{l ∈ T} ratio j l)` inside `U j`. -/
theorem inf_eq_basicOpen_prod {j : D.ι} {T : Finset D.ι} (hj : j ∈ T) :
    T.inf D.U = X.basicOpen (∏ l ∈ T, D.ratio j l) := by
  rw [← D.inf_inf_eq_basicOpen_prod j T, inf_eq_right.mpr (Finset.inf_le hj)]

theorem inf_le_U {j : D.ι} {T : Finset D.ι} (hj : j ∈ T) : T.inf D.U ≤ D.U j :=
  Finset.inf_le hj

theorem isAffineOpen_finsetInf {T : Finset D.ι} (hT : T.Nonempty) : IsAffineOpen (T.inf D.U) := by
  obtain ⟨j, hj⟩ := hT
  rw [D.inf_eq_basicOpen_prod hj]
  exact (D.isAffineOpen j).basicOpen _

/-- The coordinate opens form a finite affine cover. -/
def toFiniteAffineCover : FiniteAffineCover X where
  ι := D.ι
  U := D.U
  iSup_eq_top := D.iSup_eq_top
  isAffineOpen_inf _ hT := D.isAffineOpen_finsetInf hT

theorem inf_comm_eq_basicOpen (i j : D.ι) : D.U i ⊓ D.U j = X.basicOpen (D.ratio j i) := by
  rw [inf_comm, D.inf_eq_basicOpen]

end Opens

section Ratios

/-- Restriction of functions along `V ≤ W`. -/
abbrev resR {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma resR_resR {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (r : Γ(X, V₁)) :
    resR h₂ (resR h₁ r) = resR (h₂.trans h₁) r := by
  change (X.presheaf.map _ ≫ X.presheaf.map _) r = _
  rw [← Functor.map_comp]
  rfl

lemma resR_resR' {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (h₃ : V₃ ≤ V₁)
    (r : Γ(X, V₁)) : resR h₂ (resR h₁ r) = resR h₃ r :=
  resR_resR h₁ h₂ r

/-- The cocycle identity restricted to any open `V ⊆ U i ∩ U j`. -/
lemma ratio_mul_res {V : X.Opens} (i j k : D.ι) (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    resR hi (D.ratio i j) * resR hj (D.ratio j k) = resR hi (D.ratio i k) := by
  have hV : V ≤ D.U i ⊓ D.U j := le_inf hi hj
  have h := congrArg (resR hV) (D.ratio_mul i j k)
  rw [map_mul, resR_resR, resR_resR, resR_resR] at h
  exact h

/-- `ratio i j` and `ratio j i` are inverse on any open inside `U i ∩ U j`. -/
lemma ratio_mul_ratio {V : X.Opens} (i j : D.ι) (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    resR hi (D.ratio i j) * resR hj (D.ratio j i) = 1 := by
  rw [D.ratio_mul_res i j i hi hj, D.ratio_self, map_one]

lemma isUnit_ratio_res {V : X.Opens} (i j : D.ι) (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    IsUnit (resR hi (D.ratio i j)) :=
  IsUnit.of_mul_eq_one _ (D.ratio_mul_ratio i j hi hj)

/-- The structure constants on `U i`. -/
abbrev const (i : D.ι) : A →+* Γ(X, D.U i) := sectionsRingHom c le_top

lemma resR_const {V : X.Opens} (i : D.ι) (h : V ≤ D.U i) (a : A) :
    resR h (D.const i a) = sectionsRingHom c (h.trans le_top) a :=
  resR_resR le_top h (c a)

/-- Dehomogenization at `x_i`: `A[x_j] → Γ(U i, 𝒪_X)`, `x_j ↦ ratio i j`. -/
def dehom (i : D.ι) : MvPolynomial D.ι A →+* Γ(X, D.U i) :=
  MvPolynomial.eval₂Hom (D.const i) (D.ratio i)

@[simp] lemma dehom_C (i : D.ι) (a : A) : D.dehom i (MvPolynomial.C a) = D.const i a :=
  MvPolynomial.eval₂Hom_C _ _ _

@[simp] lemma dehom_X (i j : D.ι) : D.dehom i (MvPolynomial.X j) = D.ratio i j :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma dehom_surjective (i : D.ι) : Function.Surjective (D.dehom i) :=
  D.surjective i

/-- Homogenization towards the `i`-th factor: `A[x_j] → Γ(U i, 𝒪_X)[T]`,
`x_j ↦ ratio i j · T`. -/
def toPolynomial (i : D.ι) : MvPolynomial D.ι A →+* Polynomial Γ(X, D.U i) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (D.const i))
    (fun l => Polynomial.monomial 1 (D.ratio i l))

@[simp] lemma toPolynomial_C (i : D.ι) (a : A) :
    D.toPolynomial i (MvPolynomial.C a) = Polynomial.C (D.const i a) :=
  MvPolynomial.eval₂Hom_C _ _ _

@[simp] lemma toPolynomial_X (i j : D.ι) :
    D.toPolynomial i (MvPolynomial.X j) = Polynomial.monomial 1 (D.ratio i j) :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- Evaluating the homogenization at `T = 1` is the dehomogenization. -/
lemma eval_one_toPolynomial (i : D.ι) (s : MvPolynomial D.ι A) :
    (D.toPolynomial i s).eval 1 = D.dehom i s := by
  have : (Polynomial.evalRingHom (1 : Γ(X, D.U i))).comp (D.toPolynomial i) = D.dehom i := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp [Polynomial.eval_monomial]
  exact congrArg (fun f => f s) this

/-- A product of `T`-monomials of degree one is a `T`-monomial. -/
lemma prod_monomial_one_pow {R : Type*} [CommRing R] {κ : Type*} (s : Finset κ) (r : κ → R)
    (e : κ → ℕ) :
    ∏ l ∈ s, Polynomial.monomial 1 (r l) ^ e l =
      Polynomial.monomial (∑ l ∈ s, e l) (∏ l ∈ s, r l ^ e l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.prod_insert hl, Finset.sum_insert hl, ih,
      Polynomial.monomial_pow, one_mul, Polynomial.monomial_mul_monomial]

/-- The homogenization of a monomial is a monomial in `T` of the total degree. -/
lemma toPolynomial_monomial (i : D.ι) (μ : D.ι →₀ ℕ) (a : A) :
    D.toPolynomial i (MvPolynomial.monomial μ a) =
      Polynomial.monomial (Finsupp.degree μ)
        (D.const i a * μ.prod fun l e => D.ratio i l ^ e) := by
  rw [toPolynomial, MvPolynomial.eval₂Hom_monomial, Finsupp.prod, Finsupp.prod,
    Finsupp.degree_apply, RingHom.coe_comp, Function.comp_apply, prod_monomial_one_pow,
    ← Polynomial.C_mul_monomial]

/-- The homogenization of a polynomial of degree `d` is concentrated in `T`-degree `d`. -/
lemma toPolynomial_coeff_eq_zero_of_mem (i : D.ι) {d : ℤ} {s : MvPolynomial D.ι A}
    (hs : s ∈ MvPolynomial.weightedHomogeneousSubmodule A (fun _ : D.ι => (1 : ℤ)) d)
    {a : ℕ} (ha : (a : ℤ) ≠ d) : (D.toPolynomial i s).coeff a = 0 := by
  classical
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hs
  rw [MvPolynomial.as_sum s, map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  rw [toPolynomial_monomial, Polynomial.coeff_monomial, if_neg]
  intro h
  apply ha
  have hw := hs (MvPolynomial.mem_support_iff.mp hμ)
  rw [← hw, ← h, Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, Nat.cast_sum]
  simp

end Ratios

section Ambient

variable (F : X.Modules)

/-- The ambient module `∏_i Γ(U_i, F)[T]` of the graded module of twisted sections. -/
abbrev Ambient : Type u := ∀ i, PolynomialModule Γ(X, D.U i) Γ(F, D.U i)

instance : AddCommGroup (D.Ambient F) :=
  inferInstanceAs (AddCommGroup (∀ i, PolynomialModule Γ(X, D.U i) Γ(F, D.U i)))

instance : Module (∀ i, Polynomial Γ(X, D.U i)) (D.Ambient F) :=
  inferInstanceAs (Module (∀ i, Polynomial Γ(X, D.U i))
    (∀ i, PolynomialModule Γ(X, D.U i) Γ(F, D.U i)))

/-- The coordinate ring acts on all factors at once. -/
def coordHom : MvPolynomial D.ι A →+* (∀ i, Polynomial Γ(X, D.U i)) :=
  RingHom.pi D.toPolynomial

instance : Module (MvPolynomial D.ι A) (D.Ambient F) :=
  Module.compHom _ D.coordHom

instance : Module A (D.Ambient F) :=
  Module.compHom _ (D.coordHom.comp MvPolynomial.C)

variable {D F}

/-- The `i`-th factor of an element of the ambient module. -/
abbrev Ambient.comp (e : D.Ambient F) (i : D.ι) : PolynomialModule Γ(X, D.U i) Γ(F, D.U i) := e i

@[ext]
lemma Ambient.ext {e e' : D.Ambient F} (h : ∀ i, e i = e' i) : e = e' := funext h

@[simp] lemma Ambient.add_apply (e e' : D.Ambient F) (i : D.ι) : (e + e') i = e i + e' i := rfl
@[simp] lemma Ambient.zero_apply (i : D.ι) : (0 : D.Ambient F) i = 0 := rfl
@[simp] lemma Ambient.neg_apply (e : D.Ambient F) (i : D.ι) : (-e) i = -e i := rfl
@[simp] lemma Ambient.sub_apply (e e' : D.Ambient F) (i : D.ι) : (e - e') i = e i - e' i := rfl

lemma Ambient.sum_apply {κ : Type*} (s : Finset κ) (f : κ → D.Ambient F) (i : D.ι) :
    (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Ambient.add_apply, ih]

@[simp] lemma Ambient.smul_apply (s : MvPolynomial D.ι A) (e : D.Ambient F) (i : D.ι) :
    (s • e) i = D.toPolynomial i s • e i := rfl

@[simp] lemma Ambient.smul_apply' (a : A) (e : D.Ambient F) (i : D.ι) :
    (a • e) i = Polynomial.C (D.const i a) • e i := by
  change D.toPolynomial i (MvPolynomial.C a) • e i = _
  rw [toPolynomial_C]

instance : IsScalarTower A (MvPolynomial D.ι A) (D.Ambient F) where
  smul_assoc a s e := by
    ext i : 1
    rw [Ambient.smul_apply, Ambient.smul_apply', Ambient.smul_apply, Algebra.smul_def a s,
      map_mul, MvPolynomial.algebraMap_eq, toPolynomial_C, mul_smul]

/-- `C r` acts coefficientwise on `PolynomialModule`. -/
lemma PolynomialModule.coeff_C_smul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (p : PolynomialModule R M) (n : ℕ) :
    (Polynomial.C r • p).coeff n = r • p.coeff n := by
  rw [← Polynomial.monomial_zero_left, PolynomialModule.monomial_smul_apply]
  simp

lemma PolynomialModule.coeff_monomial_one_smul_succ {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) (p : PolynomialModule R M) (n : ℕ) :
    (Polynomial.monomial 1 r • p).coeff (n + 1) = r • p.coeff n := by
  rw [PolynomialModule.monomial_smul_apply]
  simp

lemma PolynomialModule.coeff_monomial_one_smul_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) (p : PolynomialModule R M) :
    (Polynomial.monomial 1 r • p).coeff 0 = 0 := by
  rw [PolynomialModule.monomial_smul_apply]
  simp

@[simp] lemma Ambient.coeff_smul' (a : A) (e : D.Ambient F) (i : D.ι) (n : ℕ) :
    ((a • e) i).coeff n = D.const i a • (e i).coeff n := by
  rw [Ambient.smul_apply', PolynomialModule.coeff_C_smul]

lemma Ambient.coeff_X_smul_succ (j : D.ι) (e : D.Ambient F) (i : D.ι) (n : ℕ) :
    (((MvPolynomial.X j : MvPolynomial D.ι A) • e) i).coeff (n + 1) = D.ratio i j • (e i).coeff n := by
  rw [Ambient.smul_apply, toPolynomial_X, PolynomialModule.coeff_monomial_one_smul_succ]

lemma Ambient.coeff_X_smul_zero (j : D.ι) (e : D.Ambient F) (i : D.ι) :
    (((MvPolynomial.X j : MvPolynomial D.ι A) • e) i).coeff 0 = 0 := by
  rw [Ambient.smul_apply, toPolynomial_X, PolynomialModule.coeff_monomial_one_smul_zero]

end Ambient

section Grading

variable (F : X.Modules)

/-- The degree-`k` part of the ambient module: families concentrated in `T`-degree `k`. -/
def grading (k : ℤ) : Submodule A (D.Ambient F) where
  carrier := {e | ∀ i (m : ℕ), (m : ℤ) ≠ k → (e i).coeff m = 0}
  add_mem' {e e'} he he' i m hm := by
    rw [Ambient.add_apply, PolynomialModule.coeff_add, Finsupp.add_apply, he i m hm, he' i m hm,
      add_zero]
  zero_mem' i m _ := rfl
  smul_mem' a e he i m hm := by
    change ((a • e) i).coeff m = 0
    rw [Ambient.coeff_smul', he i m hm, smul_zero]

variable {D F}

lemma mem_grading_iff {k : ℤ} {e : D.Ambient F} :
    e ∈ D.grading F k ↔ ∀ i (m : ℕ), (m : ℤ) ≠ k → (e i).coeff m = 0 := Iff.rfl

/-- A family of elements concentrated in degree `n`. -/
def single (n : ℕ) (s : ∀ i, Γ(F, D.U i)) : D.Ambient F :=
  fun i => PolynomialModule.single Γ(X, D.U i) n (s i)

lemma single_mem_grading (n : ℕ) (s : ∀ i, Γ(F, D.U i)) :
    single n s ∈ D.grading F n := by
  intro i m hm
  change (Finsupp.single n (s i)) m = 0
  rw [Finsupp.single_apply, if_neg]
  intro h
  exact hm (by rw [h])

@[simp] lemma single_coeff_self (n : ℕ) (s : ∀ i, Γ(F, D.U i)) (i : D.ι) :
    ((single n s : D.Ambient F) i).coeff n = s i := by
  change (Finsupp.single n (s i)) n = s i
  simp

/-- The degree-`k` part of an element (zero for `k < 0`). -/
def proj (k : ℤ) (e : D.Ambient F) : D.Ambient F :=
  fun i => PolynomialModule.single Γ(X, D.U i) k.toNat (if 0 ≤ k then (e i).coeff k.toNat else 0)

lemma proj_mem (k : ℤ) (e : D.Ambient F) : proj k e ∈ D.grading F k := by
  intro i m hm
  change (Finsupp.single k.toNat (if 0 ≤ k then (e i).coeff k.toNat else 0)) m = 0
  rw [Finsupp.single_apply]
  split_ifs with h1 h2
  · exact absurd (by rw [← h1]; omega) hm
  · rfl
  · rfl

lemma coeff_proj (k : ℤ) (e : D.Ambient F) (i : D.ι) (m : ℕ) :
    ((proj k e : D.Ambient F) i).coeff m = if (m : ℤ) = k then (e i).coeff m else 0 := by
  change (Finsupp.single k.toNat (if 0 ≤ k then (e i).coeff k.toNat else 0)) m = _
  rw [Finsupp.single_apply]
  by_cases h : (m : ℤ) = k
  · subst h
    simp
  · rw [if_neg h]
    split_ifs with h1 h2
    · exact absurd (by rw [← h1]; omega) h
    · rfl
    · rfl

/-- The coefficient of `coe x` in `T`-degree `m` comes from the degree-`m` component. -/
lemma coeff_coe_directSum (x : DirectSum ℤ fun k => D.grading F k) (i : D.ι) (m : ℕ) :
    ((DirectSum.coeAddMonoidHom (D.grading F) x : D.Ambient F) i).coeff m =
      ((x m : D.Ambient F) i).coeff m := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k y =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : (m : ℤ) = k
    · subst h
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ h, y.property i m h]
      rfl
  | add x y hx hy =>
    rw [map_add, Ambient.add_apply, PolynomialModule.coeff_add, Finsupp.add_apply, hx, hy,
      DirectSum.add_apply, Submodule.coe_add, Ambient.add_apply, PolynomialModule.coeff_add,
      Finsupp.add_apply]

/-- The `T`-degree grading of the ambient module is an internal direct sum. -/
theorem isInternal_grading : DirectSum.IsInternal (D.grading F) := by
  classical
  constructor
  · intro x y hxy
    ext k : 1
    apply Subtype.ext
    ext i : 1
    apply PolynomialModule.ext
    ext m
    by_cases hm : (m : ℤ) = k
    · subst hm
      have := congrArg (fun e : D.Ambient F => (e i).coeff m) hxy
      rw [coeff_coe_directSum, coeff_coe_directSum] at this
      exact this
    · rw [(x k).property i m hm, (y k).property i m hm]
  · intro e
    let s : Finset ℤ := Finset.univ.biUnion fun i => (e i).coeff.support.image (fun m : ℕ => (m : ℤ))
    refine ⟨∑ k ∈ s, DirectSum.of (fun k => D.grading F k) k ⟨proj k e, proj_mem k e⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    ext i : 1
    apply PolynomialModule.ext
    ext m
    rw [Ambient.sum_apply, PolynomialModule.coeff_sum, Finset.sum_apply']
    simp only [coeff_proj]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · symm
      by_contra hne
      apply h
      simp only [s, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
      exact ⟨i, m, Finsupp.mem_support_iff.mpr hne, rfl⟩

instance : DirectSum.Decomposition (D.grading F) := isInternal_grading.chooseDecomposition

/-- The standard grading of `A[x_i]` acts on the `T`-degree grading. -/
instance gradedSMul :
    SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule A (fun _ : D.ι => (1 : ℤ)))
      (D.grading F) where
  smul_mem {d k s e} hs he := by
    intro i m hm
    rw [Ambient.smul_apply, PolynomialModule.smul_apply]
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    by_cases ha : (ab.1 : ℤ) = d
    · rw [he i ab.2 (by intro h; apply hm; change (m : ℤ) = d + k; omega), smul_zero]
    · rw [D.toPolynomial_coeff_eq_zero_of_mem i hs ha, zero_smul]

end Grading

section Gstar

variable (F : X.Modules)

/-- Restriction of sections of `F` along `V ≤ W`. -/
abbrev resM {V W : X.Opens} (h : V ≤ W) (s : Γ(F, W)) : Γ(F, V) :=
  F.presheaf.map (homOfLE h).op s

variable {F}

lemma resM_resM {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (s : Γ(F, V₁)) :
    resM F h₂ (resM F h₁ s) = resM F (h₂.trans h₁) s :=
  presheaf_map_map F h₁ h₂ (h₂.trans h₁) s

lemma resM_smul {V W : X.Opens} (h : V ≤ W) (r : Γ(X, W)) (s : Γ(F, W)) :
    resM F h (r • s) = resR h r • resM F h s :=
  Scheme.Modules.map_smul F (homOfLE h) r s

lemma resM_add {V W : X.Opens} (h : V ≤ W) (s t : Γ(F, W)) :
    resM F h (s + t) = resM F h s + resM F h t :=
  map_add _ s t

lemma resM_zero {V W : X.Opens} (h : V ≤ W) : resM F h (0 : Γ(F, W)) = 0 :=
  map_zero _

lemma resM_sub {V W : X.Opens} (h : V ≤ W) (s t : Γ(F, W)) :
    resM F h (s - t) = resM F h s - resM F h t :=
  map_sub _ s t

lemma resM_sum {V W : X.Opens} (h : V ≤ W) {κ : Type*} (t : Finset κ) (f : κ → Γ(F, W)) :
    resM F h (∑ k ∈ t, f k) = ∑ k ∈ t, resM F h (f k) :=
  map_sum (F.presheaf.map (homOfLE h).op).hom f t

lemma resM_self {V : X.Opens} (h : V ≤ V) (s : Γ(F, V)) : resM F h s = s := by
  change F.presheaf.map (𝟙 _) s = s
  rw [F.presheaf.map_id]
  rfl

/-- Restriction along an equality of opens is injective. -/
lemma resM_injective_of_eq {V W : X.Opens} (h : V = W) :
    Function.Injective (resM F h.le) := by
  intro s t hst
  have := congrArg (resM F h.ge) hst
  rwa [resM_resM, resM_resM, resM_self, resM_self] at this

/-- The compatibility condition defining `Γ_*(F)`: `(e_i)_m = (ratio i j)^m (e_j)_m` on
`U i ∩ U j`. -/
def IsCompatible (e : D.Ambient F) : Prop :=
  ∀ i j (m : ℕ),
    resM F (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) ((e i).coeff m) =
      resR (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.ratio i j) ^ m •
        resM F (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) ((e j).coeff m)

variable {D}

/-- The compatibility condition restricted to any open `V ⊆ U i ∩ U j`. -/
lemma IsCompatible.res {e : D.Ambient F} (he : D.IsCompatible e) {V : X.Opens} (i j : D.ι)
    (hi : V ≤ D.U i) (hj : V ≤ D.U j) (m : ℕ) :
    resM F hi ((e i).coeff m) = resR hi (D.ratio i j) ^ m • resM F hj ((e j).coeff m) := by
  have hV : V ≤ D.U i ⊓ D.U j := le_inf hi hj
  have h := congrArg (resM F hV) (he i j m)
  rwa [resM_resM, resM_smul, resM_resM, map_pow, resR_resR] at h

lemma isCompatible_zero : D.IsCompatible (0 : D.Ambient F) := by
  intro i j m
  change resM F _ (0 : Γ(F, D.U i)) = _ • resM F _ (0 : Γ(F, D.U j))
  rw [resM_zero, resM_zero, smul_zero]

lemma IsCompatible.add {e e' : D.Ambient F} (he : D.IsCompatible e) (he' : D.IsCompatible e') :
    D.IsCompatible (e + e') := by
  intro i j m
  simp only [Ambient.add_apply, PolynomialModule.coeff_add, Finsupp.add_apply, resM_add,
    he i j m, he' i j m, smul_add]

lemma IsCompatible.C_smul {e : D.Ambient F} (he : D.IsCompatible e) (a : A) :
    D.IsCompatible ((MvPolynomial.C a : MvPolynomial D.ι A) • e) := by
  intro i j m
  rw [Ambient.smul_apply, Ambient.smul_apply, toPolynomial_C, toPolynomial_C,
    PolynomialModule.coeff_C_smul, PolynomialModule.coeff_C_smul, resM_smul, resM_smul,
    resR_const, resR_const, he i j m, smul_comm]

lemma IsCompatible.X_smul {e : D.Ambient F} (he : D.IsCompatible e) (n : D.ι) :
    D.IsCompatible ((MvPolynomial.X n : MvPolynomial D.ι A) • e) := by
  intro i j m
  cases m with
  | zero =>
    rw [Ambient.coeff_X_smul_zero, Ambient.coeff_X_smul_zero, resM_zero, resM_zero, smul_zero]
  | succ m =>
    rw [Ambient.coeff_X_smul_succ, Ambient.coeff_X_smul_succ, resM_smul, resM_smul, he i j m,
      smul_smul, smul_smul, ← D.ratio_mul_res i j n inf_le_left inf_le_right]
    congr 1
    ring

lemma IsCompatible.smul {e : D.Ambient F} (he : D.IsCompatible e) (s : MvPolynomial D.ι A) :
    D.IsCompatible (s • e) := by
  induction s using MvPolynomial.induction_on generalizing e with
  | C a => exact he.C_smul a
  | add p q hp hq => rw [add_smul]; exact (hp he).add (hq he)
  | mul_X p n hp => rw [mul_smul]; exact hp (he.X_smul n)

variable (D F)

/-- `Γ_*(F)` in nonnegative degrees: the compatible families, an `A[x_i]`-submodule of the
ambient module (blueprint `def:sm-gamma-star`). -/
def gstar : Submodule (MvPolynomial D.ι A) (D.Ambient F) where
  carrier := {e | D.IsCompatible e}
  add_mem' he he' := IsCompatible.add he he'
  zero_mem' := isCompatible_zero
  smul_mem' s _ he := IsCompatible.smul he s

variable {F}

variable {D}

lemma mem_gstar_iff {e : D.Ambient F} : e ∈ D.gstar F ↔ D.IsCompatible e := Iff.rfl

end Gstar

end ProjectiveCoordinates

end

end DeJongAlterations.StableModification.Cohomology
