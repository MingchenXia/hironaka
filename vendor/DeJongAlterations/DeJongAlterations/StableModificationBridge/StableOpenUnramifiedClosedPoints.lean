import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Jacobson.Artinian

/-! The actual finite unramified affine map is closed from injectivity on original closed points.

The private Nullstellensatz/diagonal-kernel argument is adapted from the native proof in
`EnvelopeProperty/EnvelopeProperty/Global/Radicial.lean`, without an external project import.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenUnramifiedClosedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nilpotent_of_points_zero {k R : Type u} [Field k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] {x : R}
    (h : ∀ χ : R →ₐ[k] k, χ x = 0) : x ∈ nilradical R := by
  have hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hrad : (nilradical R).IsRadical := Ideal.radical_isRadical ⊥
  rw [← IsJacobsonRing.out hJ hrad, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨-, hm⟩
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  have hbij : Function.Bijective (algebraMap k (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij
  have h1 := h (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_eq_zero_iff _ e.symm.injective,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h1
  exact h1

private theorem points_eq_of_maximal_injective {k A B : Type u} [Field k]
    [CommRing A] [CommRing B] [Algebra k B] [Algebra A B]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m')
    {φ₁ φ₂ : B →ₐ[k] k} (h : ∀ a : A, φ₁ (algebraMap A B a) = φ₂ (algebraMap A B a)) :
    φ₁ = φ₂ := by
  have hsurj : ∀ φ : B →ₐ[k] k, Function.Surjective φ := fun φ c =>
    ⟨algebraMap k B c, φ.commutes c⟩
  have hmax₁ : (RingHom.ker φ₁).IsMaximal := RingHom.ker_isMaximal_of_surjective φ₁ (hsurj φ₁)
  have hmax₂ : (RingHom.ker φ₂).IsMaximal := RingHom.ker_isMaximal_of_surjective φ₂ (hsurj φ₂)
  have hcomap :
      (RingHom.ker φ₁).comap (algebraMap A B) = (RingHom.ker φ₂).comap (algebraMap A B) := by
    ext a
    simp only [Ideal.mem_comap, RingHom.mem_ker, h a]
  have hker := hmax _ _ hmax₁ hmax₂ hcomap
  ext b
  have hb : b - algebraMap k B (φ₁ b) ∈ RingHom.ker φ₁ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  rw [hker, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hb
  exact hb.symm

/-- ORIGINAL finite unramified affine geometry and original maximal-ideal injectivity internally
give a native closed immersion; no comparison, stalk-surjectivity or residue certificate is given. -/
theorem closedImmersion_spec_of_maximal_injective {k A B : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra A B] [Algebra k B]
    [IsScalarTower k A B] [Algebra.FiniteType k A] [Module.Finite A B]
    [Algebra.FormallyUnramified A B]
    (hmax : ∀ m m' : Ideal B, m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A B) = m'.comap (algebraMap A B) → m = m') :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.FiniteType k (B ⊗[A] B) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have hnil : RingHom.ker (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B) ≤
      nilradical (B ⊗[A] B) := by
    change KaehlerDifferential.ideal A B ≤ _
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    refine nilpotent_of_points_zero (k := k) fun χ => ?_
    have key : χ.comp (Algebra.TensorProduct.includeLeft (S := k)) =
        χ.comp ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).restrictScalars k) := by
      refine points_eq_of_maximal_injective hmax fun a => ?_
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_one_eq_one_tmul]
    have hb := congrArg (fun φ : B →ₐ[k] k => φ b) key
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply] at hb
    rw [map_sub, hb, sub_self]
  let μ := (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom
  have hμ : Function.Surjective μ := fun b => ⟨1 ⊗ₜ[A] b, by simp [μ]⟩
  let δ := Spec.map (CommRingCat.ofHom μ)
  have hδ : Function.Surjective δ := by
    rw [← Set.range_eq_univ]
    change Set.range (PrimeSpectrum.comap μ) = Set.univ
    rw [range_comap_of_surjective _ _ hμ, PrimeSpectrum.zeroLocus_eq_univ_iff]
    exact hnil
  let : Epi δ.base := (TopCat.epi_iff_surjective δ.base).mpr hδ
  have : IsIso δ := IsOpenImmersion.isIso δ
  have : IsIso (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A B)))) := by
    rw [diagonal_SpecMap A B]
    exact inferInstanceAs (IsIso (δ ≫ (pullbackSpecIso A B B).inv))
  let : Mono (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    (pullback.isIso_diagonal_iff _).mp inferInstance
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap).mpr inferInstance
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end DeJongAlterations.StableModificationBridge.StableOpenUnramifiedClosedPoints
