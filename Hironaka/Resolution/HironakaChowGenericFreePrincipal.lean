import Hironaka.Resolution.HironakaChowPureTransformBaseChange
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Original finite-domain modules internally produce a generic trivialization

No Noetherianity or finite-presentation hypothesis on M is needed. Native
finite-free-source lifting and a native finite-cokernel annihilator produce
one genuine original principal localization equivalence, including rank0.

Blueprint: `hironaka-g10-generic-free-principal.tex`.
-/

set_option autoImplicit false

open Set Module TensorProduct

namespace Hironaka.HironakaChowGenericFreePrincipal

universe uT

noncomputable section

variable {R M : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Original finite generation constructs a genuine free-source injection and
ONE nonzero annihilator of its ENTIRE ORIGINAL native cokernel. Only the
internally chosen finite FREE source uses native finite presentation. -/
theorem exists_injective_free_map_annihilating_coker :
    ∃ (r : ℕ) (h : (Fin r →₀ R) →ₗ[R] M) (d : R),
      d ≠ 0 ∧ Function.Injective h ∧ ∀ c : M ⧸ h.range, d • c = 0 := by
  classical
  let S := nonZeroDivisors R
  let K := FractionRing R
  let MK := LocalizedModule S M
  let l := LocalizedModule.mkLinearMap S M
  let r := Module.finrank K MK
  let b := Module.finBasis K MK
  let J : (Fin r →₀ R) →ₗ[R] (Fin r →₀ K) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap R K)
  let B : (Fin r →₀ K) →ₗ[R] MK := (b.repr.symm.restrictScalars R).toLinearMap
  let : Module.FinitePresentation R (Fin r →₀ R) :=
    Module.finitePresentation_of_projective R (Fin r →₀ R)
  obtain ⟨h, s, hmap, hsurj⟩ :=
    Module.exists_localizedMap_surjective_of_surjective S J l (ϕ := B) b.repr.symm.surjective
  have hJinj : Function.Injective J := by
    intro v w hvw
    ext i
    apply IsFractionRing.injective R K
    exact congrArg (fun a : Fin r →₀ K => a i) hvw
  have hmapinj : Function.Injective (IsLocalizedModule.map S J l h) := by
    rw [hmap]
    intro v w hvw
    apply b.repr.symm.injective
    exact IsLocalizedModule.smul_injective l s hvw
  have hinj : Function.Injective h := by
    intro v w hvw
    apply hJinj
    apply hmapinj
    rw [IsLocalizedModule.map_apply, IsLocalizedModule.map_apply, hvw]
  let Q := M ⧸ h.range
  have hsurjNative : Function.Surjective (LocalizedModule.map S h) :=
    (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective J l).mp hsurj
  let : Subsingleton (LocalizedModule S Q) :=
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker S h).mp hsurjNative
  let lQ := LocalizedModule.mkLinearMap S Q
  have hzero : lQ.comp (LinearMap.id : Q →ₗ[R] Q) = lQ.comp (0 : Q →ₗ[R] Q) := by
    ext c
    exact Subsingleton.elim _ _
  obtain ⟨d, hd⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S lQ (LinearMap.id : Q →ₗ[R] Q) (0 : Q →ₗ[R] Q) hzero
  refine ⟨r, h, d.val, nonZeroDivisors.ne_zero d.property, hinj, ?_⟩
  intro c
  have hh := LinearMap.congr_fun hd c
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply,
    smul_zero, Submonoid.smul_def] using hh

/-- Actual original generic freeness from finite generation over a domain,
including finite torsion modules/rank0. No incoming generic basis or free data. -/
theorem exists_generic_free_principal :
    ∃ (d : R) (r : ℕ)
      (_e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
        (Fin r → Localization.Away d)), d ≠ 0 := by
  obtain ⟨r, h, d, hd, hinj, hkill⟩ := exists_injective_free_map_annihilating_coker (R := R) (M := M)
  let S := Submonoid.powers d
  have hQ : Subsingleton (LocalizedModule S (M ⧸ h.range)) := by
    apply LocalizedModule.subsingleton_iff.mpr
    intro c
    exact ⟨d, Submonoid.mem_powers d, hkill c⟩
  have hsurj : Function.Surjective (LocalizedModule.map S h) :=
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker S h).mpr hQ
  let E := LinearEquiv.ofBijective (LocalizedModule.map S h)
    ⟨LocalizedModule.map_injective S h hinj, hsurj⟩
  let b : Basis (Fin r) R (Fin r →₀ R) := Finsupp.basisSingleOne
  let bS := b.ofIsLocalizedModule (Localization S) S (LocalizedModule.mkLinearMap S (Fin r →₀ R))
  exact ⟨d, r, (bS.map E).equivFun, hd⟩


open HironakaChowDeterminantalImage HironakaChowPureTransformBaseChange

/-- Source finite-domain data INTERNALLY construct d and the generic
trivialization, then retain ONE original matrix/full ideal before EVERY target
ring map. Neither a generic basis nor a target freeness certificate is an input. -/
theorem exists_universal_pure_transform_matrix :
    ∃ (d : R) (r : ℕ)
      (e : LocalizedModule (Submonoid.powers d) M ≃ₗ[Localization.Away d]
        (Fin r → Localization.Away d))
      (N q : ℕ) (g : Fin q → M) (f : M →ₗ[R] (Fin r → R))
      (A : Matrix (Fin r) (Fin q) R)
      (E : (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M))
        ≃ₗ[R] (Matrix.toLin' A).range) (K : ℕ),
      d ≠ 0 ∧ Submodule.span R (range g) = ⊤ ∧
      (∀ m i, algebraMap R (Localization.Away d) (f m i) =
        d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) M m) i) ∧
      (∀ j, A.col j = f (g j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) M) ∧
      (∀ m, (E (Submodule.Quotient.mk m)).val = f m) ∧
      (minorIdeal A r).FG ∧ d ^ K ∈ minorIdeal A r ∧ IsRegular (d ^ K) ∧
      ∀ (T : Type uT) [CommRing T] (φ : R →+* T),
        letI : Algebra R T := φ.toAlgebra
        IsRegular (φ d) →
        ∃ ET : ((T ⊗[R] M) ⧸ LinearMap.ker (LocalizedModule.mkLinearMap
          (Submonoid.powers (φ d)) (T ⊗[R] M))) ≃ₗ[T] (Matrix.toLin' (A.map φ)).range,
          (vectorBaseChange (S := T) f).range = (Matrix.toLin' (A.map φ)).range ∧
          LinearMap.ker (vectorBaseChange (S := T) f) =
            LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers (φ d)) (T ⊗[R] M)) ∧
          (∀ t, (ET (Submodule.Quotient.mk t)).val = vectorBaseChange (S := T) f t) ∧
          minorIdeal (A.map φ) r = Ideal.map φ (minorIdeal A r) ∧
          (φ d) ^ K ∈ Ideal.map φ (minorIdeal A r) ∧ IsRegular ((φ d) ^ K) := by
  obtain ⟨d, r, e, hd⟩ := exists_generic_free_principal (R := R) (M := M)
  obtain ⟨N, q, g, f, A, E, K, hg, hclear, hcols, hrange, hker, hE, hfg, hK, hreg, hAll⟩ :=
    exists_universal_baseChange_pure_transform_matrix d (IsRegular.of_ne_zero' hd) r e
  exact ⟨d, r, e, N, q, g, f, A, E, K, hd, hg, hclear, hcols, hrange, hker,
    hE, hfg, hK, hreg, hAll⟩

open HironakaSmoothCentreRealDomainActualSheafStalk

/-- The literal ORIGINAL smooth structure-sheaf stalk internally supplies
its domain and generic trivialization, without an incoming domain/free certificate. -/
theorem actual_stalk_exists_generic_free_principal
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (x : X) (F : Type*) [AddCommGroup F]
    [Module (actualComplexStructureStalk (n := n) x) F]
    [Module.Finite (actualComplexStructureStalk (n := n) x) F] :
    ∃ (d : actualComplexStructureStalk (n := n) x) (r : ℕ)
      (_e : LocalizedModule (Submonoid.powers d) F ≃ₗ[Localization.Away d]
        (Fin r → Localization.Away d)), d ≠ 0 := by
  let : IsDomain (actualComplexStructureStalk (n := n) x) :=
    MulEquiv.isDomain _ (actualStalkChartEquiv (n := n) x).toMulEquiv
  exact exists_generic_free_principal (R := actualComplexStructureStalk (n := n) x) (M := F)

end

end Hironaka.HironakaChowGenericFreePrincipal
