/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.RegularSmoothConverseKernel
import DeJongAlterations.Algebra.RegularSmoothConversePresentation
import DeJongAlterations.Algebra.RegularSmoothConverseJacobian
import DeJongAlterations.Algebra.RegularSmoothConverseConormal

/-!
# Regular local algebras over perfect fields are formally smooth

The actual polynomial-local presentation and its actual kernel are constructed
internally. No conormal injectivity or smoothness certificate is an input to
the final theorem.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing TensorProduct KaehlerDifferential

namespace DeJongAlterations.Algebra.RegularSmoothConverseFormalSmooth

/-- A regular local quotient of the genuine smooth ambient local algebra is formally smooth. -/
theorem formallySmooth_of_surjective_regular_local
    {K P S : Type*} [Field K] [PerfectField K] [CommRing P] [CommRing S]
    [Algebra K P] [Algebra K S] [IsRegularLocalRing P] [IsRegularLocalRing S]
    [Algebra.EssFiniteType K P] [Algebra.FormallySmooth K P]
    [Module.Free P Ω[P⁄K]] [Module.Finite P Ω[P⁄K]]
    (f : P →ₐ[K] S) (hf : Function.Surjective f) : Algebra.FormallySmooth K S := by
  let : Algebra P S := f.toAlgebra
  let : IsScalarTower K P S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let I : Ideal P := RingHom.ker (algebraMap P S)
  have hI : I ≤ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨n, t, ht, hspan⟩ :=
    RegularSmoothConverseKernel.exists_kernel_span_independent_parameters f.toRingHom hf
  let t' : Fin n → I := fun i ↦ ⟨t i, by
    change (t i : P) ∈ RingHom.ker f.toRingHom
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_range_self i)⟩
  have hspan' : Ideal.span (Set.range fun i ↦ (t' i : P)) = I := hspan
  have ht' : LinearIndependent (ResidueField P)
      (fun i ↦ (maximalIdeal P).toCotangent ⟨(t' i : P), hI (t' i).property⟩) := ht
  have hinj := RegularSmoothConverseConormal.toMaximalCotangent_injective I hI t' hspan' ht'
  have hres : I ≤ RingHom.ker (IsScalarTower.toAlgHom K P (ResidueField P)).toRingHom := by
    change I ≤ RingHom.ker (algebraMap P (ResidueField P))
    rwa [ResidueField.algebraMap_eq, ker_residue]
  let g : S →ₐ[K] ResidueField P := AlgHom.liftOfSurjective f hf
    (IsScalarTower.toAlgHom K P (ResidueField P)) hres
  let : Algebra S (ResidueField P) := g.toAlgebra
  have hg : g.comp f = IsScalarTower.toAlgHom K P (ResidueField P) :=
    AlgHom.liftOfSurjective_comp _ _ _ _
  let : IsScalarTower P S (ResidueField P) :=
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom hg).symm
  have hgsurj : Function.Surjective g :=
    AlgHom.liftOfSurjective_surjective f hf _ hres residue_surjective
  let : IsLocalHom (algebraMap S (ResidueField P)) :=
    IsLocalHom.of_surjective g.toRingHom hgsurj
  have hmax : maximalIdeal S ≤ RingHom.ker (algebraMap S (ResidueField P)) := by
    rw [← maximalIdeal_comap (algebraMap S (ResidueField P)), maximalIdeal_eq_bot]
    rfl
  have hcomp : cotangentComplexBaseChange K S P (ResidueField P) =
      (RegularSmoothConverseResidue.residueCotangentMap (k := K)).comp
        (RegularSmoothConverseConormal.toMaximalCotangent I hI) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      simp only [I, cotangentComplexBaseChange_tmul, LinearMap.comp_apply,
        RegularSmoothConverseConormal.toMaximalCotangent_tmul, map_smul,
        RegularSmoothConverseResidue.residueCotangentMap_toCotangent]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange P
    (ResidueField P) hf (RingHom.ker (algebraMap P S)).fg_of_isNoetherianRing hmax).mpr
  rw [hcomp]
  exact (RegularSmoothConverseResidue.residueCotangentMap_injective K P).comp hinj

universe u

/-- Actual regular local essentially finite-type algebras over a perfect field are formally smooth. -/
theorem formallySmooth_of_isRegularLocalRing (K S : Type u) [Field K] [PerfectField K]
    [CommRing S] [Algebra K S] [IsRegularLocalRing S] [Algebra.EssFiniteType K S] :
    Algebra.FormallySmooth K S := by
  obtain ⟨n, p, f, hf⟩ :=
    RegularSmoothConversePresentation.exists_polynomial_local_surjection K S
  let P := Localization.AtPrime p.asIdeal
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra.EssFiniteType K P := Algebra.EssFiniteType.comp K (MvPolynomial (Fin n) K) P
  let : Algebra.FormallyEtale (MvPolynomial (Fin n) K) P :=
    Algebra.FormallyEtale.of_isLocalization p.asIdeal.primeCompl
  let : Algebra.FormallySmooth K P :=
    Algebra.FormallySmooth.comp K (MvPolynomial (Fin n) K) P
  let : Module.Free P Ω[P⁄K] :=
    Module.Free.of_basis (RegularSmoothConverseJacobian.localizedKaehlerBasis p.asIdeal)
  exact formallySmooth_of_surjective_regular_local f hf

/-- Every finite-type regular algebra over a perfect field is actually smooth. -/
theorem smooth_of_isRegularRing (K S : Type u) [Field K] [PerfectField K]
    [CommRing S] [Algebra K S] [Algebra.FiniteType K S] [IsRegularRing S] :
    Algebra.Smooth K S := by
  let : Algebra.FinitePresentation K S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallySmooth K S := Algebra.smoothLocus_eq_univ_iff.mp (by
    apply Set.eq_univ_of_forall
    intro p
    let : p.asIdeal.IsPrime := p.isPrime
    let : Algebra.EssFiniteType K (Localization.AtPrime p.asIdeal) :=
      Algebra.EssFiniteType.comp K S (Localization.AtPrime p.asIdeal)
    exact formallySmooth_of_isRegularLocalRing K (Localization.AtPrime p.asIdeal))
  exact ⟨‹Algebra.FormallySmooth K S›, inferInstance⟩

end DeJongAlterations.Algebra.RegularSmoothConverseFormalSmooth
