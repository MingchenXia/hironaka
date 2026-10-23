/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureLocalHypersurface
import DeJongAlterations.StableModification.Curves.SemistableNormalAlgebra

/-!
# The local structure of a nodal family at a geometric node

Let `R` be an integrally closed local domain and `B` a flat finitely presented `R`-algebra. If
`z ⊂ K ⊗_R B` is a geometric node lying over the closed point of `R`, then after inverting some
`f` outside the point under `z`, the local ring of `B_f` at the point under every geometric node
of `B_f` over the closed point has `LocalStructure` (`exists_away_localStructure_of_isFormalNode`).
The proof transports `localStructure_hypersurface` along the hypersurface presentation
`(B_f)_{ψ(a)} ≅ P_a/(g)` of lane SS3 (`Curves.SemistableNormal.exists_principal_kernel_crit`),
exactly as `Curves.SemistableNormal.exists_away_isIntegrallyClosed_of_isFormalNode` transports
normality.

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-node-structure`.
-/

noncomputable section

open IsLocalRing TensorProduct

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Curves.SemistableNormal Curves.SemistableOpen

section Transport

variable {R : Type*} [CommRing R] (𝔭 : Ideal R)

/-- `LocalStructure` along an isomorphism of algebras, at corresponding primes. -/
theorem LocalStructure.localization_of_algEquiv {T S : Type*} [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] (e : T ≃ₐ[R] S) (w : Ideal S) [w.IsPrime]
    (h : LocalStructure R (Localization.AtPrime (w.comap e.toRingHom)) 𝔭) :
    LocalStructure R (Localization.AtPrime w) 𝔭 := by
  refine h.of_algEquiv (IsLocalization.algEquivOfAlgEquiv
    (M := (w.comap e.toRingHom).primeCompl) (T := w.primeCompl)
    (Localization.AtPrime (w.comap e.toRingHom)) (Localization.AtPrime w) e ?_)
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨e.symm x, by simpa using hx, by simp⟩

/-- `LocalStructure` of a local ring of a localization `M⁻¹B` gives it for `B`. -/
theorem LocalStructure.of_localization_localization {B : Type*} [CommRing B] [Algebra R B]
    (M : Submonoid B) (w : Ideal (Localization M)) [w.IsPrime]
    (h : LocalStructure R (Localization.AtPrime w) 𝔭) :
    LocalStructure R (Localization.AtPrime (w.comap (algebraMap B (Localization M)))) 𝔭 :=
  h.of_algEquiv ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization M w).symm.restrictScalars R)

/-- Rewriting the prime of a local ring. -/
theorem LocalStructure.of_eq {B : Type*} [CommRing B] [Algebra R B] {p p' : Ideal B} [p.IsPrime]
    [p'.IsPrime] (hpp' : p = p') (h : LocalStructure R (Localization.AtPrime p) 𝔭) :
    LocalStructure R (Localization.AtPrime p') 𝔭 := by
  subst hpp'
  exact h

end Transport

section Node

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
  {B : Type u} [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FinitePresentation R B]

set_option backward.isDefEq.respectTransparency.types false in
/-- **The local structure of a nodal family near a geometric node over the closed point**
(blueprint `lem:sm-bdu-node-structure`). -/
theorem exists_away_localStructure_of_isFormalNode
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
    (z : Ideal (K ⊗[R] B)) [z.IsMaximal] (hz : IsFormalNode K z) :
    ∃ f : B, f ∉ z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ∧
      ∀ (K' : Type u) [Field K'] [IsAlgClosed K'] [Algebra R K']
        (z' : Ideal (K' ⊗[R] Localization.Away f)) [z'.IsMaximal], IsFormalNode K' z' →
        (z'.comap (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom).comap
            (algebraMap R (Localization.Away f)) = maximalIdeal R →
        LocalStructure R (Localization.AtPrime (z'.comap (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom))
          (maximalIdeal R) := by
  obtain ⟨e⟩ := hz
  have : IsNoetherianRing (K ⊗[R] B) := Algebra.FiniteType.isNoetherianRing K _
  have h2 : (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 2 := by
    rw [← AdicCompletion.spanFinrank_maximalIdeal_eq,
      ← Ideal.spanFinrank_map_eq_of_ringEquiv e.toRingEquiv,
      map_ringEquiv_maximalIdeal e.toRingEquiv]
    exact spanFinrank_maximalIdeal_formalUV_le_two K
  obtain ⟨b, -, hunr⟩ := exists_isUnramifiedAt_plane z 2 le_rfl h2
  let : Algebra (MvPolynomial (Fin 2) R) B := (MvPolynomial.aeval (R := R) b).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin 2) R) B := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R B r = MvPolynomial.aeval b (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C]
  have : Algebra.FiniteType (MvPolynomial (Fin 2) R) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (MvPolynomial (Fin 2) R) B
  have := hunr
  obtain ⟨f, hfq, Pe, ψ, hψ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := MvPolynomial (Fin 2) R)
      (z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom)
  refine ⟨f, hfq, fun K' _ _ _ z' _ ⟨e'⟩ hz'R => ?_⟩
  let : Algebra R Pe.Ring := ((algebraMap (MvPolynomial (Fin 2) R) Pe.Ring).comp
    (algebraMap R (MvPolynomial (Fin 2) R))).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pe.Ring :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψR : Pe.Ring →ₐ[R] Localization.Away f := ψ.restrictScalars R
  have : Module.Flat R (Localization.Away f) := Module.Flat.trans R B (Localization.Away f)
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    Algebra.FinitePresentation.trans R B (Localization.Away f)
  obtain ⟨g, hgJ, h, hhQ, hhessQ, hcrit, hJ⟩ := exists_principal_kernel_crit ψR hψ z' e'
  set Q₀ := z'.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).comp ψR).toRingHom with hQ₀
  have : Q₀.IsPrime := Ideal.comap_isPrime _ _
  set a := h * hessian R Pe.Ring g with ha
  have haQ : a ∉ Q₀ := fun hmem => (Ideal.IsPrime.mem_or_mem ‹_› hmem).elim hhQ hhessQ
  -- localize at `a`
  let Pa := Localization.Away a
  have : Algebra.Etale Pe.Ring Pa := Algebra.Etale.of_isLocalizationAway a
  have : Algebra.Etale (MvPolynomial (Fin 2) R) Pa := Algebra.Etale.comp _ Pe.Ring Pa
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pa := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R Pe.Ring Pa,
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) Pe.Ring,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) Pe.Ring Pa]
  have hca : ∀ i, (IsScalarTower.toAlgHom R Pe.Ring Pa) (coord R Pe.Ring i) = coord R Pa i :=
    fun i => (IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) Pe.Ring Pa _).symm
  have hhess : IsUnit (hessian R Pa (algebraMap Pe.Ring Pa g)) := by
    have := hessian_map (IsScalarTower.toAlgHom R Pe.Ring Pa) hca g
    simp only [IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    have hau : IsUnit (algebraMap Pe.Ring Pa a) := IsLocalization.Away.algebraMap_isUnit a
    have hmul : algebraMap Pe.Ring Pa a = algebraMap Pe.Ring Pa h *
        algebraMap Pe.Ring Pa (hessian R Pe.Ring g) := map_mul _ _ _
    rw [hmul] at hau
    exact isUnit_of_mul_isUnit_right hau
  have hdisj : Disjoint (Submonoid.powers a : Set Pe.Ring) Q₀ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr haQ
  set Q₀a := Q₀.map (algebraMap Pe.Ring Pa)
  have : Q₀a.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) Pa Q₀ ‹_› hdisj
  have hQ₀a : Q₀a.comap (algebraMap Pe.Ring Pa) = Q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) Pa ‹_› hdisj
  have hcrita : ∀ i, planeDerivation R Pa i (algebraMap Pe.Ring Pa g) ∈ Q₀a := by
    intro i
    have := planeDerivation_map (IsScalarTower.toAlgHom R Pe.Ring Pa) hca i g
    simp only [IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    exact Ideal.mem_map_of_mem _ (hcrit i)
  have hgQ₀ : g ∈ Q₀ := by
    rw [hQ₀, Ideal.mem_comap]
    change (Algebra.TensorProduct.includeRight : Localization.Away f →ₐ[R] _) (ψR g) ∈ z'
    rw [show ψR g = 0 from RingHom.mem_ker.mp hgJ, map_zero]
    exact z'.zero_mem
  have hgaQ : algebraMap Pe.Ring Pa g ∈ Q₀a := Ideal.mem_map_of_mem _ hgQ₀
  -- the hypersurface `T = Pa/(g) ≅ (B_f)_{ψ a}`
  set ga := algebraMap Pe.Ring Pa g
  set T := Pa ⧸ Ideal.span {ga}
  let Bfs := Localization.Away (ψR a)
  let φa : Pa →ₐ[R] Bfs := Localization.awayMapₐ ψR a
  have hφa : Function.Surjective φa := IsLocalization.Away.mapₐ_surjective_of_surjective a hψ
  have hker : RingHom.ker φa.toRingHom = Ideal.span {ga} :=
    ker_awayMap_eq_span ψR g hgJ h (hessian R Pe.Ring g) hJ
  let eB : T ≃ₐ[R] Bfs :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hφa)
  have heB : ∀ x, eB (Ideal.Quotient.mk _ x) = φa x := fun _ => rfl
  have himg : ∀ p : Pe.Ring, algebraMap (Localization.Away f) Bfs (ψR p) =
      φa (algebraMap Pe.Ring Pa p) := by
    intro p
    change _ = IsLocalization.Away.map Pa Bfs ψR.toRingHom a (algebraMap Pe.Ring Pa p)
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  -- the node of the hypersurface
  set QT : Ideal T := Q₀a.map (Ideal.Quotient.mk _)
  have hkerT : RingHom.ker (Ideal.Quotient.mk (Ideal.span {ga})) ≤ Q₀a := by
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact hgaQ
  have : QT.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerT
  have hQT : ∀ x, Ideal.Quotient.mk (Ideal.span {ga}) x ∈ QT ↔ x ∈ Q₀a := by
    intro x
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerT]
  have hcritT : ∀ i, Ideal.Quotient.mk _ (planeDerivation R Pa i ga) ∈ QT :=
    fun i => (hQT _).mpr (hcrita i)
  -- the node lies over the closed point
  have hQTR : QT.comap (algebraMap R T) = maximalIdeal R := by
    rw [← hz'R]
    ext r
    simp only [Ideal.mem_comap]
    rw [IsScalarTower.algebraMap_apply R Pa T, Ideal.Quotient.algebraMap_eq, hQT,
      IsScalarTower.algebraMap_apply R Pe.Ring Pa, ← Ideal.mem_comap, hQ₀a, hQ₀, Ideal.mem_comap]
    change (Algebra.TensorProduct.includeRight : Localization.Away f →ₐ[R] _)
      (ψR (algebraMap R Pe.Ring r)) ∈ z' ↔
      (Algebra.TensorProduct.includeRight : Localization.Away f →ₐ[R] _)
        (algebraMap R (Localization.Away f) r) ∈ z'
    rw [AlgHom.commutes]
  have hT := localStructure_hypersurface R Pa ga hhess QT hcritT hQTR
  -- transport back to `B_f`
  have h1 : LocalStructure R (Localization.AtPrime (QT.comap eB.symm.toRingHom))
      (maximalIdeal R) := by
    refine LocalStructure.localization_of_algEquiv (maximalIdeal R) eB _ ?_
    refine LocalStructure.of_eq (maximalIdeal R) ?_ hT
    ext x
    simp
  have h2 := LocalStructure.of_localization_localization (maximalIdeal R)
    (Submonoid.powers (ψR a)) _ h1
  refine LocalStructure.of_eq (maximalIdeal R) ?_ h2
  apply Ideal.comap_injective_of_surjective ψR.toRingHom hψ
  ext p
  simp only [Ideal.mem_comap]
  change eB.symm (algebraMap (Localization.Away f) Bfs (ψR p)) ∈ QT ↔ _
  rw [himg, ← heB, AlgEquiv.symm_apply_apply, hQT, ← Ideal.mem_comap, hQ₀a, hQ₀]
  rfl

end Node

end DeJongAlterations.StableModification.BlowDown.ClosureLocal
