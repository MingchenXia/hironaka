import Hironaka.Resolution.HironakaG1RSmoothLocusBaseChange

/-!
# The smooth locus along an arbitrary flat pushout square

`HironakaG1RSmoothLocusBaseChange` compares smooth loci for the concrete base change `T ⊗[R] A`.
Here the comparison is stated for ANY pushout square of rings `R → T`, `R → A`, `B = T ⊗[R] A`
(`Algebra.IsPushout R T A B`), as it arises from a cartesian square of affine schemes
(`AlgebraicGeometry.isPushout_appTop_of_isPullback`):

* `mem_smoothLocus_congr`: the smooth locus is invariant under isomorphisms of `T`-algebras;
* `mem_smoothLocus_of_isPushout`: for `R → T` flat and `A` essentially of finite type over `R`,
  `q ∈ smoothLocus T B ↔ q ∩ A ∈ smoothLocus R A`, and `smoothLocus_of_isPushout` (set form).

Only Mathlib and `HironakaG1RSmoothLocusBaseChange` are imported; no named input.
Blueprint: `hironaka-g1-r-smooth-locus-base-change.tex` (node `g1r:smooth-locus-pushout`).
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Hironaka.HironakaG1RSmoothLocusPushout

open HironakaG1RSmoothLocusBaseChange

/-- **The smooth locus is invariant under isomorphisms of `T`-algebras.** -/
theorem mem_smoothLocus_congr {T B B' : Type*} [CommRing T] [CommRing B] [CommRing B']
    [Algebra T B] [Algebra T B'] (e : B ≃ₐ[T] B') (q' : PrimeSpectrum B') :
    q' ∈ Algebra.smoothLocus T B' ↔
      q'.comap (e : B →+* B') ∈ Algebra.smoothLocus T B := by
  have H : Submonoid.map e (q'.comap (e : B →+* B')).asIdeal.primeCompl =
      q'.asIdeal.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      change e (e.symm y) ∉ q'.asIdeal
      simpa using hy
  exact (Algebra.FormallySmooth.iff_of_equiv (IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime (q'.comap (e : B →+* B')).asIdeal) (Localization.AtPrime q'.asIdeal)
    e H)).symm

variable {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B] [Algebra R T]
  [Algebra R A] [Algebra R B] [Algebra T B] [Algebra A B] [IsScalarTower R T B]
  [IsScalarTower R A B] [Algebra.IsPushout R T A B]

/-- **The smooth locus along a flat pushout square, pointwise.**  If `B` is the pushout of
`R → T` (flat) and `R → A` (essentially of finite type), then `B` is smooth over `T` at `q` iff `A`
is smooth over `R` at the contraction of `q`. -/
theorem mem_smoothLocus_of_isPushout [Module.Flat R T] [Algebra.EssFiniteType R A]
    (q : PrimeSpectrum B) :
    q ∈ Algebra.smoothLocus T B ↔ q.comap (algebraMap A B) ∈ Algebra.smoothLocus R A := by
  let e := Algebra.IsPushout.equiv R T A B
  have he : (e : T ⊗[R] A →+* B).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom = algebraMap A B := by
    ext a
    simp [e, Algebra.IsPushout.equiv_tmul]
  rw [mem_smoothLocus_congr e, mem_smoothLocus_tensorProduct_iff, ← PrimeSpectrum.comap_comp_apply,
    he]

/-- Set form of `mem_smoothLocus_of_isPushout`. -/
theorem smoothLocus_of_isPushout [Module.Flat R T] [Algebra.EssFiniteType R A] :
    Algebra.smoothLocus T B = PrimeSpectrum.comap (algebraMap A B) ⁻¹' Algebra.smoothLocus R A := by
  ext q
  exact mem_smoothLocus_of_isPushout q

end Hironaka.HironakaG1RSmoothLocusPushout
