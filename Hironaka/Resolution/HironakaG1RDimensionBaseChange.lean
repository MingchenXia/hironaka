import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Krull dimension and minimal primes under field extension (ALG14 input D2, first part)

* `ringKrullDim_eq_of_isIntegral`: an injective integral ring map preserves the Krull dimension
  (lying over + going up for `≥`, incomparability for `≤`);
* `ringKrullDim_tensorProduct_of_field`: for a finite type algebra `A` over a field `k` and ANY
  field extension `L / k`, `dim (L ⊗[k] A) = dim A` (Noether normalization
  `k[X₁..X_s] ↪ A` integral, base-changed to `L[X₁..X_s] ↪ L ⊗[k] A`);
* `comap_mem_minimalPrimes_of_flat`, `exists_mem_minimalPrimes_comap_eq`: along a flat (resp.
  faithfully flat) ring map, minimal primes contract to minimal primes (going down), and every
  minimal prime of the base is such a contraction.  For `A → L ⊗[k] A`: the irreducible components
  of `Spec (L ⊗[k] A)` lie over irreducible components of `Spec A`, and every component of `Spec A`
  is dominated by a component of `Spec (L ⊗[k] A)`.

Only Mathlib is imported; no named input.  Blueprint: `hironaka-g1-r-dimension-base-change.tex`.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Hironaka.HironakaG1RDimensionBaseChange

/-! ### Integral extensions -/

section Integral

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Incomparability**: an integral extension does not raise the Krull dimension. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  refine iSup_le fun l ↦ ?_
  let l' : LTSeries (PrimeSpectrum R) :=
    { length := l.length
      toFun := fun i ↦ PrimeSpectrum.comap (algebraMap R S) (l i)
      step := fun i ↦ by
        have h : (l (Fin.castSucc i)).asIdeal < (l i.succ).asIdeal := l.step i
        exact Ideal.IsIntegral.comap_lt_comap (R := R) h }
  exact le_iSup (fun p : LTSeries (PrimeSpectrum R) ↦ (p.length : WithBot ℕ∞)) l'

/-- **Lying over and going up**: an injective integral extension does not lower the Krull
dimension. -/
theorem le_ringKrullDim_of_isIntegral [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  refine iSup_le fun l ↦ ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S) l.head.asIdeal ⊥
    (Ideal.comap_bot_le_of_injective _ hinj)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hlen]
  exact le_iSup (fun p : LTSeries (PrimeSpectrum S) ↦ (p.length : WithBot ℕ∞)) L

/-- **An injective integral ring map preserves the Krull dimension.** -/
theorem ringKrullDim_eq_of_isIntegral [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral (le_ringKrullDim_of_isIntegral hinj)

omit [Algebra R S] in
/-- Ring-hom form of `ringKrullDim_eq_of_isIntegral`. -/
theorem ringKrullDim_eq_of_ringHom_isIntegral (f : R →+* S) (hf : f.IsIntegral)
    (hinj : Function.Injective f) : ringKrullDim S = ringKrullDim R := by
  let _ := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  exact ringKrullDim_eq_of_isIntegral hinj

end Integral

/-! ### Krull dimension under field extension -/

section Field

variable (k L A : Type*) [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]

/-- `dim K[X₁, …, X_s] = s` over a field `K`. -/
theorem ringKrullDim_mvPolynomial_fin (K : Type*) [Field K] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) K) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_fin,
    zero_add]

/-- Base change of an integral ring map along `k → L` is integral. -/
theorem isIntegral_tensorProduct_map {P : Type*} [CommRing P] [Algebra k P]
    (g : P →ₐ[k] A) (hg : g.toRingHom.IsIntegral) :
    (Algebra.TensorProduct.map (AlgHom.id k L) g).toRingHom.IsIntegral := by
  let _ := g.toRingHom.toAlgebra
  let _ := (Algebra.TensorProduct.map (AlgHom.id k L) g).toRingHom.toAlgebra
  have hint : ∀ a : A, IsIntegral (L ⊗[k] P) ((1 : L) ⊗ₜ[k] a) := by
    intro a
    have h : (algebraMap (L ⊗[k] P) (L ⊗[k] A)).comp
        (Algebra.TensorProduct.includeRight : P →ₐ[k] L ⊗[k] P).toRingHom =
        (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom.comp
          (algebraMap P A) := by
      ext x
      simp [RingHom.algebraMap_toAlgebra]
    exact IsIntegral.map_of_comp_eq _ _ h (hg a)
  intro x
  change IsIntegral (L ⊗[k] P) x
  induction x with
  | zero => exact isIntegral_zero
  | tmul l a =>
    have : l ⊗ₜ[k] a = algebraMap (L ⊗[k] P) (L ⊗[k] A) (l ⊗ₜ[k] 1) * ((1 : L) ⊗ₜ[k] a) := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [this]
    exact (isIntegral_algebraMap).mul (hint a)
  | add x y hx hy => exact hx.add hy

/-- **The Krull dimension is invariant under field extension**: for a finite type algebra `A`
over a field `k` and any field extension `L / k`, `dim (L ⊗[k] A) = dim A`. -/
theorem ringKrullDim_tensorProduct_of_field [Algebra.FiniteType k A] :
    ringKrullDim (L ⊗[k] A) = ringKrullDim A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  have hA : ringKrullDim A = s := by
    rw [ringKrullDim_eq_of_ringHom_isIntegral g.toRingHom hint hinj, ringKrullDim_mvPolynomial_fin]
  let gL := Algebra.TensorProduct.map (AlgHom.id k L) g
  have hinjL : Function.Injective gL :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) g.toLinearMap hinj
  have hP : ringKrullDim (L ⊗[k] MvPolynomial (Fin s) k) = s := by
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k L).toRingEquiv,
      ringKrullDim_mvPolynomial_fin]
  rw [hA, ringKrullDim_eq_of_ringHom_isIntegral gL.toRingHom
    (isIntegral_tensorProduct_map k L A g hint) hinjL, hP]

end Field

/-! ### Minimal primes along flat maps -/

section MinimalPrimes

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Going down**: along a flat ring map, minimal primes contract to minimal primes. -/
theorem comap_mem_minimalPrimes_of_flat [Module.Flat R S] {Q : Ideal S}
    (hQ : Q ∈ minimalPrimes S) : Q.comap (algebraMap R S) ∈ minimalPrimes R := by
  rw [minimalPrimes_eq_minimals] at hQ ⊢
  have : Q.IsPrime := hQ.1
  refine ⟨Ideal.IsPrime.comap _, fun p hp hle ↦ ?_⟩
  have : p.IsPrime := hp
  have : Q.LiesOver (Q.comap (algebraMap R S)) := ⟨rfl⟩
  obtain ⟨P, hPQ, hP, hPp⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  have hQP : Q ≤ P := hQ.2 hP hPQ
  rw [hPp.over, ← le_antisymm hPQ hQP]

/-- **Every minimal prime of the base is a contraction of a minimal prime** along a faithfully
flat ring map. -/
theorem exists_mem_minimalPrimes_comap_eq [Module.FaithfullyFlat R S] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) :
    ∃ Q ∈ minimalPrimes S, Q.comap (algebraMap R S) = p := by
  have : p.IsPrime := hp.1.1
  obtain ⟨⟨Q', hQ'⟩, hQ'p⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := S) (⟨p, this⟩ : PrimeSpectrum R)
  have hQ'p : Q'.comap (algebraMap R S) = p := congrArg PrimeSpectrum.asIdeal hQ'p
  obtain ⟨Q, hQ, hQQ'⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S) ≤ Q')
  refine ⟨Q, hQ, ?_⟩
  have hmin := comap_mem_minimalPrimes_of_flat (R := R) hQ
  have hle : Q.comap (algebraMap R S) ≤ p := hQ'p ▸ Ideal.comap_mono hQQ'
  exact le_antisymm hle (hp.2 ⟨hmin.1.1, bot_le⟩ hle)

/-- The two statements together: along a faithfully flat ring map, contraction maps the minimal
primes ONTO the minimal primes. -/
theorem image_comap_minimalPrimes_of_faithfullyFlat [Module.FaithfullyFlat R S] :
    Ideal.comap (algebraMap R S) '' minimalPrimes S = minimalPrimes R := by
  ext p
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact comap_mem_minimalPrimes_of_flat hQ
  · intro hp
    obtain ⟨Q, hQ, hQp⟩ := exists_mem_minimalPrimes_comap_eq (S := S) hp
    exact ⟨Q, hQ, hQp⟩

end MinimalPrimes

/-! ### Components under field extension -/

section FieldComponents

variable (k L A : Type*) [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `L ⊗[k] A` is faithfully flat over `A` for a field extension `L / k`. -/
theorem faithfullyFlat_tensorProduct_of_field : Module.FaithfullyFlat A (L ⊗[k] A) := by
  exact Module.FaithfullyFlat.of_linearEquiv A (A ⊗[k] L)
    (inferInstance : Algebra.IsPushout k A L (L ⊗[k] A)).out.equiv.symm

/-- **Components under field extension**: the minimal primes of `L ⊗[k] A` contract exactly onto
the minimal primes of `A` (every irreducible component of `Spec (L ⊗[k] A)` lies over an irreducible
component of `Spec A`, and every component of `Spec A` is dominated by one of `Spec (L ⊗[k] A)`). -/
theorem image_comap_minimalPrimes_tensorProduct_of_field :
    Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) ''
        minimalPrimes (L ⊗[k] A) = minimalPrimes A := by
  have := faithfullyFlat_tensorProduct_of_field k L A
  exact image_comap_minimalPrimes_of_faithfullyFlat

end FieldComponents

end Hironaka.HironakaG1RDimensionBaseChange
