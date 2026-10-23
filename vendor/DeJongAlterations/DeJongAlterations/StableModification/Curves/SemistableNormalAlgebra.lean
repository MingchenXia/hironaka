import DeJongAlterations.StableModification.Curves.SemistableNormalNode
import DeJongAlterations.StableModification.Curves.SemistableNormalHypersurface

/-!
# Normality of a nodal family at a node, with smooth generic fibre

Let `R` be an integrally closed domain and `B` a flat finitely presented `R`-algebra which is
formally smooth over `R` at the primes over the generic point of `R`. If `z ⊂ K ⊗_R B` is a
geometric node, then after inverting some `f` outside the point under `z`, the local ring of `B_f`
at the point under every geometric node of `B_f` is an integrally closed domain
(`exists_away_isIntegrallyClosed_of_isFormalNode`). This is the node case of the normality of
semi-stable curves with smooth generic fibre (Temkin, T:2966–2967; blueprint
`sm-semistable-normal.tex`).

The proof transports `isDomain_isIntegrallyClosed_hypersurface` along the hypersurface
presentation `(B_f)_{ψ(a)} ≅ P_a/(g)` of `exists_away_etale_nodeChart`; the transport lemmas for
local rings of localizations are `formallySmooth_localization_localization` and
`isDomain_isIntegrallyClosed_localization_localization`.
-/

noncomputable section

open IsLocalRing TensorProduct MvPowerSeries

namespace DeJongAlterations.StableModification.Curves.SemistableNormal

open SemistableOpen
open Algebra.NodeFormalMorse Algebra.NodeVariableMorse Algebra.NodeGeometricCompletionFormalUV

universe u

section Transport

/-- An integrally closed domain is preserved by ring isomorphisms. -/
theorem isDomain_isIntegrallyClosed_of_ringEquiv {A A' : Type*} [CommRing A] [CommRing A']
    (e : A ≃+* A') (h : IsDomain A ∧ IsIntegrallyClosed A) :
    IsDomain A' ∧ IsIntegrallyClosed A' := by
  obtain ⟨h1, h2⟩ := h
  have : IsDomain A' := e.symm.injective.isDomain e.symm.toRingHom
  exact ⟨this, IsIntegrallyClosed.of_equiv e⟩

/-- Rewriting the prime of a local ring. -/
theorem isDomain_isIntegrallyClosed_of_eq {A : Type*} [CommRing A] {p p' : Ideal A} [p.IsPrime]
    [p'.IsPrime] (hpp' : p = p')
    (h : IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsDomain (Localization.AtPrime p') ∧ IsIntegrallyClosed (Localization.AtPrime p') := by
  subst hpp'
  exact h

/-- The local ring of a localization `M⁻¹B` at a prime `w` is the local ring of `B` at `w ∩ B`. -/
theorem isDomain_isIntegrallyClosed_localization_localization {B : Type*} [CommRing B]
    (M : Submonoid B) (w : Ideal (Localization M)) [w.IsPrime]
    (h : IsDomain (Localization.AtPrime w) ∧ IsIntegrallyClosed (Localization.AtPrime w)) :
    IsDomain (Localization.AtPrime (w.comap (algebraMap B (Localization M)))) ∧
      IsIntegrallyClosed (Localization.AtPrime (w.comap (algebraMap B (Localization M)))) :=
  isDomain_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M w).symm.toRingEquiv h

/-- Formal smoothness of a local ring of a localization `M⁻¹B`, from that of `B`. -/
theorem formallySmooth_localization_localization {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (M : Submonoid B) (w : Ideal (Localization M)) [w.IsPrime]
    [Algebra.FormallySmooth R
      (Localization.AtPrime (w.comap (algebraMap B (Localization M))))] :
    Algebra.FormallySmooth R (Localization.AtPrime w) :=
  Algebra.FormallySmooth.of_equiv
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization M w).restrictScalars R)

/-- Local rings along an algebra isomorphism. -/
theorem formallySmooth_localization_of_algEquiv {R T S : Type u} [CommRing R] [CommRing T]
    [CommRing S] [Algebra R T] [Algebra R S] (e : T ≃ₐ[R] S) (w : Ideal T) [w.IsPrime]
    [Algebra.FormallySmooth R (Localization.AtPrime (w.comap e.symm.toRingHom))] :
    Algebra.FormallySmooth R (Localization.AtPrime w) := by
  refine Algebra.FormallySmooth.of_equiv (IsLocalization.algEquivOfAlgEquiv
    (M := (w.comap e.symm.toRingHom).primeCompl) (T := w.primeCompl)
    (Localization.AtPrime (w.comap e.symm.toRingHom)) (Localization.AtPrime w) e.symm ?_)
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨e x, by simpa using hx, by simp⟩

/-- Normality of local rings along a ring isomorphism. -/
theorem isDomain_isIntegrallyClosed_localization_of_ringEquiv {T S : Type*} [CommRing T]
    [CommRing S] (e : T ≃+* S) (w : Ideal T) [w.IsPrime]
    (h : IsDomain (Localization.AtPrime w) ∧ IsIntegrallyClosed (Localization.AtPrime w)) :
    IsDomain (Localization.AtPrime (w.comap e.symm.toRingHom)) ∧
      IsIntegrallyClosed (Localization.AtPrime (w.comap e.symm.toRingHom)) := by
  refine isDomain_isIntegrallyClosed_of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (M := w.primeCompl) (T := (w.comap e.symm.toRingHom).primeCompl)
    (Localization.AtPrime w) (Localization.AtPrime (w.comap e.symm.toRingHom)) e ?_) h
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

end Transport

section NodeNormal

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {B : Type u} [CommRing B]
  [Algebra R B] [Module.Flat R B] [Algebra.FinitePresentation R B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **A nodal family with smooth generic fibre is normal near a node.** Let `R` be an integrally
closed domain and `B` a flat finitely presented `R`-algebra, formally smooth over `R` at the primes
over the generic point of `R`. If `z ⊂ K ⊗_R B` is a geometric node, there is `f` outside the
point under `z` such that for every geometric node `z'` of `B_f`, the local ring of `B_f` at the
point under `z'` is an integrally closed domain. -/
theorem exists_away_isIntegrallyClosed_of_isFormalNode
    (hgen : ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮.comap (algebraMap R B) = ⊥ →
      Algebra.FormallySmooth R (Localization.AtPrime 𝔮))
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
    (z : Ideal (K ⊗[R] B)) [z.IsMaximal] (hz : IsFormalNode K z) :
    ∃ f : B, f ∉ z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ∧
      ∀ (K' : Type u) [Field K'] [IsAlgClosed K'] [Algebra R K']
        (z' : Ideal (K' ⊗[R] Localization.Away f)) [z'.IsMaximal], IsFormalNode K' z' →
        IsDomain (Localization.AtPrime (z'.comap (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom)) ∧
        IsIntegrallyClosed (Localization.AtPrime (z'.comap (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom)) := by
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
  refine ⟨f, hfq, fun K' _ _ _ z' _ ⟨e'⟩ => ?_⟩
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
  -- generic smoothness of `T`
  have hgenT : ∀ (w : Ideal T) [w.IsPrime], w ≤ QT → w.comap (algebraMap R T) = ⊥ →
      Algebra.FormallySmooth R (Localization.AtPrime w) := by
    intro w _ _ hw
    set w' := w.comap eB.symm.toRingHom
    set w'' := w'.comap (algebraMap (Localization.Away f) Bfs)
    set 𝔮 := w''.comap (algebraMap B (Localization.Away f))
    have h𝔮 : 𝔮.comap (algebraMap R B) = ⊥ := by
      rw [← hw]
      ext r
      simp only [𝔮, w'', w', Ideal.mem_comap]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      change eB.symm (algebraMap R Bfs r) ∈ w ↔ _
      rw [AlgEquiv.commutes]
    have := hgen 𝔮 h𝔮
    have : Algebra.FormallySmooth R (Localization.AtPrime w'') :=
      formallySmooth_localization_localization (Submonoid.powers f) w''
    have : Algebra.FormallySmooth R (Localization.AtPrime w') :=
      formallySmooth_localization_localization (Submonoid.powers (ψR a)) w'
    exact formallySmooth_localization_of_algEquiv eB w
  have hT := isDomain_isIntegrallyClosed_hypersurface R Pa ga hhess QT hcritT hgenT
  -- transport back to `B_f`
  have h1 := isDomain_isIntegrallyClosed_localization_of_ringEquiv eB.toRingEquiv QT hT
  have h2 := isDomain_isIntegrallyClosed_localization_localization (Submonoid.powers (ψR a)) _ h1
  refine isDomain_isIntegrallyClosed_of_eq ?_ h2
  apply Ideal.comap_injective_of_surjective ψR.toRingHom hψ
  ext p
  simp only [Ideal.mem_comap]
  change eB.symm (algebraMap (Localization.Away f) Bfs (ψR p)) ∈ QT ↔ _
  rw [himg, ← heB, AlgEquiv.symm_apply_apply, hQT, ← Ideal.mem_comap, hQ₀a, hQ₀]
  rfl

end NodeNormal

end DeJongAlterations.StableModification.Curves.SemistableNormal
