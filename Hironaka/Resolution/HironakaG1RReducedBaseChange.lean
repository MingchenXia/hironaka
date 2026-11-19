import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Unramified.Field

/-!
# Reduced base change over perfect fields (ALG14 input D1)

**Main result** (`isReduced_tensorProduct_of_perfectField`): for a perfect field `k` (e.g. a field of
characteristic zero), a field extension `L / k` and a reduced `k`-algebra `A`, the base change
`L ⊗[k] A` is reduced; more generally the tensor product of two reduced `k`-algebras is reduced
(`isReduced_tensorProduct_of_isReduced`).  Mathlib lists this as a TODO
(`Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`, header).  This is input D1 of lane G1's
ALG14 route (`work/hironaka-resume-20261111/G1/ALG14-R02-FINITE-GENERATION-DESCENT.md`, §3).

Proof (Bourbaki, Algèbre V §15; Stacks 030U/030W):
* `isReduced_tensorProduct_of_forall_field` (fields suffice): `C ⊗ A` is reduced for every reduced
  `A` once `C ⊗ E` is reduced for every finitely generated field extension `E`: reduce to finitely
  generated `A` (`IsReduced.tensorProduct_of_flat_of_forall_fg`), which is noetherian, so it embeds
  into the finite product of the fraction fields of its quotients by its minimal primes; finite
  products commute with `C ⊗ -`, and `C` is flat;
* `isReduced_tensorProduct_of_isLocalization`: localization (here: `k(t) = Frac k[t]`) keeps the
  base change reduced, by clearing one denominator;
* `isReduced_tensorProduct_of_formallyUnramified`: a formally unramified essentially finite type
  algebra (here: a finite separable field extension) has reduced base change to every reduced
  algebra (fields suffice, then `Algebra.FormallyUnramified.isReduced_of_field`);
* `isReduced_tensorProduct_field`: a finitely generated extension `E` of a perfect field is
  separable over a purely transcendental subextension `F = k(s)`
  (`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`), and
  `E ⊗[k] L ≅ E ⊗[F] (F ⊗[k] L)`.

Only Mathlib is imported; no named input.  Blueprint: `hironaka-g1-r-reduced-base-change.tex`.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Hironaka.HironakaG1RReducedBaseChange

universe u v w

/-! ### Localizations -/

/-- **Base change and localization.** If `C` is flat over `k`, `C ⊗[k] P` is reduced and `P'` is a
localization of `P` at nonzerodivisors, then `C ⊗[k] P'` is reduced. -/
theorem isReduced_tensorProduct_of_isLocalization {k C P P' : Type*} [CommRing k] [CommRing C]
    [Algebra k C] [Module.Flat k C] [CommRing P] [Algebra k P] [CommRing P'] [Algebra k P']
    [Algebra P P'] [IsScalarTower k P P'] (M : Submonoid P) [IsLocalization M P']
    (hM : M ≤ nonZeroDivisors P) [IsReduced (C ⊗[k] P)] : IsReduced (C ⊗[k] P') := by
  let f : C ⊗[k] P →ₐ[k] C ⊗[k] P' :=
    Algebra.TensorProduct.map (AlgHom.id k C) (IsScalarTower.toAlgHom k P P')
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom k P P').toLinearMap
      (IsLocalization.injective P' hM)
  have key : ∀ z : C ⊗[k] P', ∃ (x : C ⊗[k] P) (m : M),
      ((1 : C) ⊗ₜ[k] algebraMap P P' m) * z = f x := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 1, by simp⟩
    | tmul c q =>
      obtain ⟨⟨p, m⟩, hpm⟩ := IsLocalization.surj M q
      refine ⟨c ⊗ₜ p, m, ?_⟩
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, f, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      rw [mul_comm]
      exact congrArg (c ⊗ₜ[k] ·) hpm
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨x₁, m₁, h₁⟩ := h₁
      obtain ⟨x₂, m₂, h₂⟩ := h₂
      refine ⟨((1 : C) ⊗ₜ[k] (m₂ : P)) * x₁ + ((1 : C) ⊗ₜ[k] (m₁ : P)) * x₂, m₁ * m₂, ?_⟩
      have e₁ : f ((1 : C) ⊗ₜ[k] (m₂ : P)) = (1 : C) ⊗ₜ[k] algebraMap P P' m₂ := by simp [f]
      have e₂ : f ((1 : C) ⊗ₜ[k] (m₁ : P)) = (1 : C) ⊗ₜ[k] algebraMap P P' m₁ := by simp [f]
      rw [map_add, map_mul, map_mul, e₁, e₂, ← h₁, ← h₂, mul_add]
      simp only [Submonoid.coe_mul, map_mul]
      have hsplit : ∀ a b : P', ((1 : C) ⊗ₜ[k] (a * b)) = ((1 : C) ⊗ₜ[k] a) * ((1 : C) ⊗ₜ[k] b) := by
        intro a b
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hsplit]
      ring
  constructor
  intro z hz
  obtain ⟨x, m, hx⟩ := key z
  have hxn : IsNilpotent (f x) := by
    rw [← hx]
    exact (Commute.all _ _).isNilpotent_mul_left hz
  have hx0 : x = 0 := ((IsNilpotent.map_iff hf).mp hxn).eq_zero
  rw [hx0, map_zero] at hx
  have hu : IsUnit ((1 : C) ⊗ₜ[k] algebraMap P P' m) :=
    (IsLocalization.map_units P' m).map (Algebra.TensorProduct.includeRight (R := k) (A := C))
  exact hu.mul_right_eq_zero.mp hx

/-! ### Fields suffice -/

/-- **Fields suffice.** Over a field `k`, if `C ⊗[k] E` is reduced for every finitely generated
(essentially of finite type) field extension `E` of `k`, then `C ⊗[k] A` is reduced for every
reduced `k`-algebra `A`. -/
theorem isReduced_tensorProduct_of_forall_field {k : Type u} {C : Type w} [Field k] [CommRing C]
    [Algebra k C]
    (h : ∀ (E : Type v) [Field E] [Algebra k E] [Algebra.EssFiniteType k E], IsReduced (C ⊗[k] E))
    (A : Type v) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (C ⊗[k] A) := by
  classical
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Fintype (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).fintype
  have hprime : ∀ p : minimalPrimes B, p.1.IsPrime := fun p => p.2.isPrime
  let E : minimalPrimes B → Type v := fun p => FractionRing (B ⧸ p.1)
  let φ : B →ₐ[k] (∀ p, E p) := AlgHom.pi fun p =>
    (IsScalarTower.toAlgHom k (B ⧸ p.1) (E p)).comp (Ideal.Quotient.mkₐ k p.1)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hmem : b ∈ sInf (minimalPrimes B) := by
      rw [Submodule.mem_sInf]
      intro p hp
      have := hprime ⟨p, hp⟩
      have h1 : algebraMap (B ⧸ p) (FractionRing (B ⧸ p)) (Ideal.Quotient.mk p b) = 0 :=
        congrFun hb ⟨p, hp⟩
      rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact h1
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      exact hmem
    obtain ⟨n, hn⟩ := hrad
    exact IsNilpotent.eq_zero ⟨n, (Submodule.mem_bot B).mp hn⟩
  have : ∀ p, IsReduced (C ⊗[k] E p) := fun p => h (E p)
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k C) φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hφ
  let Φ : C ⊗[k] B →+* ∀ p, C ⊗[k] E p :=
    ((Algebra.TensorProduct.piRight k k C E).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k C) φ)).toRingHom
  have hΦ : Function.Injective Φ := fun a b hab =>
    hinj ((Algebra.TensorProduct.piRight k k C E).injective hab)
  exact isReduced_of_injective Φ hΦ

/-! ### Formally unramified algebras -/

/-- **Formally unramified base change.** If `E` is a formally unramified, essentially finite type
algebra over a field `F` (e.g. a finite separable field extension), then `E ⊗[F] R` is reduced for
every reduced `F`-algebra `R`. -/
theorem isReduced_tensorProduct_of_formallyUnramified (F : Type u) (E : Type w) [Field F]
    [CommRing E] [Algebra F E] [Algebra.FormallyUnramified F E] [Algebra.EssFiniteType F E]
    (R : Type v) [CommRing R] [Algebra F R] [IsReduced R] : IsReduced (E ⊗[F] R) := by
  refine isReduced_tensorProduct_of_forall_field (fun Ω _ _ _ => ?_) R
  have : IsReduced (Ω ⊗[F] E) := Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[F] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm F E Ω) (AlgEquiv.injective _)

/-- **Towers.** If `E` is formally unramified and essentially of finite type over a field `F`
containing `k` and `F ⊗[k] L` is reduced, then `E ⊗[k] L ≅ E ⊗[F] (F ⊗[k] L)` is reduced. -/
theorem isReduced_tensorProduct_of_tower (k : Type u) (F : Type*) (E : Type v) (L : Type w)
    [Field k] [Field F] [CommRing E] [CommRing L] [Algebra k F] [Algebra k E] [Algebra F E]
    [IsScalarTower k F E] [Algebra k L] [Algebra.FormallyUnramified F E] [Algebra.EssFiniteType F E]
    [IsReduced (F ⊗[k] L)] : IsReduced (E ⊗[k] L) := by
  have h1 : IsReduced (E ⊗[F] (F ⊗[k] L)) :=
    isReduced_tensorProduct_of_formallyUnramified F E (F ⊗[k] L)
  exact isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange k F E E L).symm
    (AlgEquiv.injective _)

/-! ### Fields over a perfect field -/

/-- **The field case.** Over a perfect field `k`, `L ⊗[k] E` is reduced for every field extension
`L` and every finitely generated field extension `E`. -/
theorem isReduced_tensorProduct_field (k : Type u) (L : Type w) (E : Type v) [Field k]
    [PerfectField k] [Field L] [Algebra k L] [Field E] [Algebra k E] [Algebra.EssFiniteType k E] :
    IsReduced (L ⊗[k] E) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k E
  set F := IntermediateField.adjoin k (s : Set E)
  -- `F` is the rational function field on `s`
  let e : FractionRing (MvPolynomial s k) ≃ₐ[k] F :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by rw [Subtype.range_coe]))
  have hP : IsReduced (L ⊗[k] MvPolynomial s k) :=
    isReduced_of_injective (MvPolynomial.algebraTensorAlgEquiv k L) (AlgEquiv.injective _)
  have hFrac : IsReduced (L ⊗[k] FractionRing (MvPolynomial s k)) :=
    isReduced_tensorProduct_of_isLocalization (nonZeroDivisors (MvPolynomial s k)) le_rfl
  have hF : IsReduced (F ⊗[k] L) :=
    isReduced_of_injective
      ((Algebra.TensorProduct.comm k F L).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl e.symm))
      (AlgEquiv.injective _)
  -- `E` is separable over `F`
  have : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp k F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  have h2 : IsReduced (E ⊗[k] L) := isReduced_tensorProduct_of_tower k F E L
  exact isReduced_of_injective (Algebra.TensorProduct.comm k L E) (AlgEquiv.injective _)

/-! ### Main results -/

/-- **Reduced base change over a perfect field** (ALG14 input D1; a Mathlib TODO): for a perfect
field `k`, a field extension `L` of `k` and a reduced `k`-algebra `A`, `L ⊗[k] A` is reduced. -/
theorem isReduced_tensorProduct_of_perfectField (k : Type u) (L : Type w) (A : Type v) [Field k]
    [PerfectField k] [Field L] [Algebra k L] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (L ⊗[k] A) :=
  isReduced_tensorProduct_of_forall_field (fun E _ _ _ => isReduced_tensorProduct_field k L E) A

/-- **D1 in characteristic zero**: for a field `k` of characteristic zero, a field extension `L` of
`k` and a reduced `k`-algebra `A`, `L ⊗[k] A` is reduced. -/
theorem isReduced_tensorProduct_of_charZero (k : Type u) (L : Type w) (A : Type v) [Field k]
    [CharZero k] [Field L] [Algebra k L] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (L ⊗[k] A) :=
  isReduced_tensorProduct_of_perfectField k L A

/-- **The tensor product of two reduced algebras over a perfect field is reduced.** -/
theorem isReduced_tensorProduct_of_isReduced (k : Type u) (A : Type w) (B : Type v) [Field k]
    [PerfectField k] [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B]
    [IsReduced B] : IsReduced (A ⊗[k] B) := by
  refine isReduced_tensorProduct_of_forall_field (fun E _ _ _ => ?_) B
  have : IsReduced (E ⊗[k] A) := isReduced_tensorProduct_of_perfectField k E A
  exact isReduced_of_injective (Algebra.TensorProduct.comm k A E) (AlgEquiv.injective _)

/-- Over a perfect field every reduced algebra is geometrically reduced. -/
theorem isGeometricallyReduced_of_perfectField (k : Type u) (A : Type v) [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [IsReduced A] : Algebra.IsGeometricallyReduced k A :=
  (Algebra.isGeometricallyReduced_field_iff k A).mpr
    (isReduced_tensorProduct_of_perfectField k (AlgebraicClosure k) A)

end Hironaka.HironakaG1RReducedBaseChange
