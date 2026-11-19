import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-!
# The Cauchy--Binet formula

For a commutative ring `R`, `A : Matrix (Fin k) (Fin n) R` and
`B : Matrix (Fin n) (Fin k) R`,

  `det (A * B) = ∑_{I ⊆ Fin n, |I| = k} det (A_{·,I}) · det (B_{I,·})`,

the sum being over the `k`-element subsets of `Fin n`, each read off in its
increasing enumeration `Finset.orderEmbOfFin`.

Over `ℂ` the case `A = Bᴴ` gives the identity Demailly's proof of the local
finite-volume theorem (CADG III.2.6) needs,

  `det (Bᴴ B) = ∑_{|I| = k} ‖det (B_{I,·})‖²`,

which expresses the Gram determinant of a `k`-frame in `ℂⁿ`
(`Hironaka.FlatDensityGramDeterminant.rectGram_eq`) as the sum of the squared
moduli of the Jacobians of the `k`-dimensional coordinate projections.

Mathlib has `Matrix.det_mul` for square factors; the proof below is the
rectangular version of the same Leibniz-formula argument.  Nothing here mentions
this project: the file is pure matrix algebra.
-/

namespace Hironaka.CauchyBinet

open Equiv Equiv.Perm Finset Function

variable {R : Type*} [CommRing R] {k n : ℕ}

/-- The `k`-element subsets of `Fin n`: the index set of the Cauchy--Binet
expansion of a `k × n` by `n × k` product. -/
abbrev CardSubset (k n : ℕ) : Type := {I : Finset (Fin n) // I.card = k}

/-- The increasing enumeration `Fin k → Fin n` of a `k`-element subset of
`Fin n`.  Selecting the rows `I.emb` of an `n × k` matrix gives the `k × k`
minor of `I`. -/
def CardSubset.emb (I : CardSubset k n) : Fin k → Fin n :=
  I.1.orderEmbOfFin I.2

theorem CardSubset.strictMono_emb (I : CardSubset k n) : StrictMono I.emb :=
  (I.1.orderEmbOfFin I.2).strictMono

theorem CardSubset.injective_emb (I : CardSubset k n) : Function.Injective I.emb :=
  (I.1.orderEmbOfFin I.2).injective

theorem CardSubset.image_emb (I : CardSubset k n) :
    Finset.image I.emb Finset.univ = I.1 :=
  Finset.image_orderEmbOfFin_univ _ _

theorem CardSubset.range_emb (I : CardSubset k n) : Set.range I.emb = (I.1 : Set (Fin n)) :=
  Finset.range_orderEmbOfFin _ _

/-- **Leibniz expansion of a rectangular product.**  Expanding each entry of
`A * B` over the `n` inner indices turns the determinant into a sum over all
maps `p : Fin k → Fin n`, whose `p`-term is the minor of `A` on the columns `p`
times the diagonal product of `B` along `p`. -/
theorem det_mul_eq_sum_fun (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ p : Fin k → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.submatrix_apply, id_eq]
  ring

/-- A repeated column makes the minor vanish: only injective selections
contribute. -/
theorem det_submatrix_eq_zero_of_not_injective (A : Matrix (Fin k) (Fin n) R)
    {p : Fin k → Fin n} (hp : ¬ Function.Injective p) : (A.submatrix id p).det = 0 := by
  rw [Function.Injective] at hp
  push Not at hp
  obtain ⟨i, j, hij, hne⟩ := hp
  exact Matrix.det_zero_of_column_eq hne fun l => by
    simp only [Matrix.submatrix_apply, id_eq, hij]

/-- Every injective `p : Fin k → Fin n` factors as the increasing enumeration of
its image followed by a permutation of `Fin k`. -/
theorem exists_cardSubset_perm {p : Fin k → Fin n} (hp : Function.Injective p) :
    ∃ (I : CardSubset k n) (τ : Equiv.Perm (Fin k)), I.emb ∘ τ = p := by
  have hcard : (Finset.image p Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
  refine ⟨⟨Finset.image p Finset.univ, hcard⟩, ?_⟩
  set I : CardSubset k n := ⟨Finset.image p Finset.univ, hcard⟩ with hI
  have hrange : Set.range I.emb = Set.range p := by
    rw [CardSubset.range_emb]
    simp [hI, Finset.coe_image]
  have hmem : ∀ i : Fin k, p i ∈ Set.range I.emb := fun i => by
    rw [hrange]; exact ⟨i, rfl⟩
  set f : Fin k → Fin k := fun i =>
    (Equiv.ofInjective I.emb I.injective_emb).symm ⟨p i, hmem i⟩ with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have := congrArg (Equiv.ofInjective I.emb I.injective_emb) hab
    simp only [hf, Equiv.apply_symm_apply, Subtype.mk.injEq] at this
    exact hp this
  refine ⟨Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hfinj), ?_⟩
  funext i
  have : I.emb (f i) = p i := by
    have h := Equiv.apply_ofInjective_symm I.injective_emb (⟨p i, hmem i⟩ : Set.range I.emb)
    simpa [hf] using h
  simpa using this

/-- **Cauchy--Binet.**  The determinant of a product of a `k × n` by an `n × k`
matrix is the sum, over the `k`-element subsets `I` of the inner index set, of
the product of the two complementary `k × k` minors. -/
theorem det_mul_rect (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ I : CardSubset k n, (A.submatrix id I.emb).det * (B.submatrix I.emb id).det := by
  classical
  rw [det_mul_eq_sum_fun]
  set F : (Fin k → Fin n) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  have key : ∀ (I : CardSubset k n),
      ∑ τ : Equiv.Perm (Fin k), F (I.emb ∘ τ) =
        (A.submatrix id I.emb).det * (B.submatrix I.emb id).det := by
    intro I
    have hstep : ∀ τ : Equiv.Perm (Fin k),
        F (I.emb ∘ τ) = (A.submatrix id I.emb).det *
          (((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, (B.submatrix I.emb id) (τ i) i) := by
      intro τ
      have hsub : A.submatrix id (I.emb ∘ τ) = (A.submatrix id I.emb).submatrix id τ := rfl
      rw [hF]
      simp only [hsub, Matrix.det_permute', Matrix.submatrix_apply, id_eq, Function.comp_apply]
      ring
    calc ∑ τ : Equiv.Perm (Fin k), F (I.emb ∘ τ)
        = ∑ τ : Equiv.Perm (Fin k), (A.submatrix id I.emb).det *
            (((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, (B.submatrix I.emb id) (τ i) i) :=
          Finset.sum_congr rfl fun τ _ => hstep τ
      _ = (A.submatrix id I.emb).det * (B.submatrix I.emb id).det := by
          rw [← Finset.mul_sum, ← Matrix.det_apply']
  have hinj : Function.Injective
      (fun x : CardSubset k n × Equiv.Perm (Fin k) => x.1.emb ∘ (x.2 : Fin k → Fin k)) := by
    rintro ⟨I, τ⟩ ⟨J, ρ⟩ hxy
    simp only at hxy
    have himg : I.1 = J.1 := by
      have h1 : Finset.image (I.emb ∘ (τ : Fin k → Fin k)) Finset.univ = I.1 := by
        rw [← Finset.image_image, Finset.image_univ_equiv, I.image_emb]
      have h2 : Finset.image (J.emb ∘ (ρ : Fin k → Fin k)) Finset.univ = J.1 := by
        rw [← Finset.image_image, Finset.image_univ_equiv, J.image_emb]
      rw [← h1, ← h2, hxy]
    have hIJ : I = J := Subtype.ext himg
    subst hIJ
    have : (τ : Fin k → Fin k) = (ρ : Fin k → Fin k) := by
      funext i
      exact I.injective_emb (congrFun hxy i)
    exact Prod.ext rfl (Equiv.coe_fn_injective this)
  have hvanish : ∀ p : Fin k → Fin n,
      p ∉ Set.range (fun x : CardSubset k n × Equiv.Perm (Fin k) =>
        x.1.emb ∘ (x.2 : Fin k → Fin k)) → F p = 0 := by
    intro p hp
    have hnotinj : ¬ Function.Injective p := by
      intro hinjp
      obtain ⟨I, τ, hIτ⟩ := exists_cardSubset_perm hinjp
      exact hp ⟨(I, τ), hIτ⟩
    rw [hF]
    simp only
    rw [det_submatrix_eq_zero_of_not_injective A hnotinj, zero_mul]
  have hsum : ∑ x : CardSubset k n × Equiv.Perm (Fin k), F (x.1.emb ∘ (x.2 : Fin k → Fin k)) =
      ∑ p : Fin k → Fin n, F p :=
    Fintype.sum_of_injective _ hinj _ _ hvanish (fun _ => rfl)
  calc ∑ p : Fin k → Fin n, F p
      = ∑ x : CardSubset k n × Equiv.Perm (Fin k), F (x.1.emb ∘ (x.2 : Fin k → Fin k)) :=
        hsum.symm
    _ = ∑ I : CardSubset k n, ∑ τ : Equiv.Perm (Fin k), F (I.emb ∘ (τ : Fin k → Fin k)) :=
        Fintype.sum_prod_type _
    _ = ∑ I : CardSubset k n, (A.submatrix id I.emb).det * (B.submatrix I.emb id).det :=
        Finset.sum_congr rfl fun I _ => key I

section Complex

open scoped ComplexConjugate Matrix

/-- **Cauchy--Binet for a Gram matrix.**  The determinant of `AᴴA`, `A` an
`n × k` complex matrix, is the sum over the `k`-element subsets `I` of the rows
of the squared modulus of the corresponding `k × k` minor.  In particular it is
a nonnegative real number. -/
theorem det_conjTranspose_mul_self (A : Matrix (Fin n) (Fin k) ℂ) :
    (Aᴴ * A).det =
      ∑ I : CardSubset k n, ((Complex.normSq ((A.submatrix I.emb id).det) : ℝ) : ℂ) := by
  rw [det_mul_rect]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hsub : Aᴴ.submatrix id I.emb = (A.submatrix I.emb id)ᴴ := by
    rw [Matrix.conjTranspose_submatrix]
  rw [hsub, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
  rfl

/-- The real form of `det_conjTranspose_mul_self`: the Gram determinant is the
sum of the squared moduli of the `k × k` minors. -/
theorem re_det_conjTranspose_mul_self (A : Matrix (Fin n) (Fin k) ℂ) :
    ((Aᴴ * A).det).re = ∑ I : CardSubset k n, ‖(A.submatrix I.emb id).det‖ ^ 2 := by
  rw [det_conjTranspose_mul_self, Complex.re_sum]
  exact Finset.sum_congr rfl fun I _ => by
    simp [Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

/-- The Gram determinant is real. -/
theorem im_det_conjTranspose_mul_self (A : Matrix (Fin n) (Fin k) ℂ) :
    ((Aᴴ * A).det).im = 0 := by
  rw [det_conjTranspose_mul_self, Complex.im_sum]
  simp

end Complex

end Hironaka.CauchyBinet
