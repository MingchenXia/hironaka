import DeJongAlterations.StableModification.Omega.EtaleChart
import DeJongAlterations.StableModification.Curves.SemistableNormalScheme
import DeJongAlterations.StableModification.Curves.SemistableNormalNode
import DeJongAlterations.Geometry.NodeCompletedLocalSpecLocalization
import DeJongAlterations.Algebra.CompletionRegularityAscent

/-!
# Smooth points of nodal curves

Two facts about a nodal curve `f : X ⟶ S` (`DeJong.IsNodalCurve`) used in step 4 of
`lem:sm-omega-invertible` (blueprint `sm-omega-invertible.tex`,
`lem:sm-omega-smooth-geometric-point`, `lem:sm-omega-etale-smooth-descent`).

* `exists_away_formallySmooth_of_spanFinrank_le_one` (adapted from lane SS3's
  `exists_away_isIntegrallyClosed_of_spanFinrank_le_one`): a flat finitely presented algebra is
  formally smooth near a geometric point whose local ring has principal maximal ideal, when the
  geometric local rings are one-dimensional (it is étale-locally `R[X₀]`).
* `mem_smoothLocus_of_tensorChart_spec`: hence a point of a nodal curve is smooth as soon as a
  closed point of a geometric fibre over it is (the fibre criterion for nodal curves; Stacks,
  Tag 01V9 in general).
* `not_isDomain_formalUV`, `not_spanFinrank_le_one_of_isFormalNode`: a formal node is not a
  smooth point (a regular local ring has a domain as completion, `K[[u,v]]/(uv)` is not one).
* `smoothDescendsAlongEtale_of_isNodalCurve`: smoothness of a nodal curve descends along étale
  maps (Stacks, Tag 02K5 in general): `SmoothDescendsAlongEtale`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

universe u

namespace DeJongAlterations.StableModification.Omega

open Curves.SemistableOpen Curves.SemistableNormal Curves



section Transport

/-- Formal smoothness of local rings transfers along an algebra isomorphism (to the prime under
the inverse). -/
theorem formallySmooth_localization_comap_of_algEquiv {R T S : Type u} [CommRing R] [CommRing T]
    [CommRing S] [Algebra R T] [Algebra R S] (e : T ≃ₐ[R] S) (w : Ideal T) [w.IsPrime]
    [Algebra.FormallySmooth R (Localization.AtPrime w)] :
    Algebra.FormallySmooth R (Localization.AtPrime (w.comap e.symm.toRingHom)) := by
  refine Algebra.FormallySmooth.of_equiv (IsLocalization.algEquivOfAlgEquiv
    (M := w.primeCompl) (T := (w.comap e.symm.toRingHom).primeCompl)
    (Localization.AtPrime w) (Localization.AtPrime (w.comap e.symm.toRingHom)) e ?_)
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

/-- Formal smoothness of a local ring along an equality of primes. -/
theorem formallySmooth_localization_of_eq {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {p p' : Ideal A} [p.IsPrime] [p'.IsPrime] (h : p = p')
    (hp : Algebra.FormallySmooth R (Localization.AtPrime p)) :
    Algebra.FormallySmooth R (Localization.AtPrime p') := by
  subst h
  exact hp

/-- Formal smoothness of the local ring of `B` under a prime of a localization `M⁻¹B`. -/
theorem formallySmooth_localization_comap_localization {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (M : Submonoid B) (w : Ideal (Localization M)) [w.IsPrime]
    [Algebra.FormallySmooth R (Localization.AtPrime w)] :
    Algebra.FormallySmooth R
      (Localization.AtPrime (w.comap (algebraMap B (Localization M)))) :=
  Algebra.FormallySmooth.of_equiv
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization M w).symm.restrictScalars R)

end Transport

section SmoothPoint

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B]
  [Algebra R B] [Module.Flat R B] [Algebra.FinitePresentation R B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **A flat family is smooth near a smooth geometric point** (adapted from lane SS3's
`exists_away_isIntegrallyClosed_of_spanFinrank_le_one`). Let `B` be a flat finitely presented
`R`-algebra and `z ⊂ K ⊗_R B` a closed point of a geometric fibre whose local ring has principal
maximal ideal. There is `f` outside the point under `z` such that for every closed point `z'` of a
geometric fibre of `B_f` with one-dimensional local ring, `B_f` is formally smooth over `R` at the
point under `z'`: near such a point `B_f` is a localization of a surface étale over
`R[X₀, X₁]/(X₁) ≅ R[X₀]`. -/
theorem exists_away_formallySmooth_of_spanFinrank_le_one
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
    (z : Ideal (K ⊗[R] B)) [z.IsMaximal]
    (hz : (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1) :
    ∃ f : B, f ∉ z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ∧
      ∀ (K' : Type u) [Field K'] [IsAlgClosed K'] [Algebra R K']
        (z' : Ideal (K' ⊗[R] Localization.Away f)) [z'.IsMaximal],
        ringKrullDim (Localization.AtPrime z') = 1 →
        Algebra.FormallySmooth R (Localization.AtPrime (z'.comap
          (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom)) := by
  obtain ⟨b, hb0, hunr⟩ := exists_isUnramifiedAt_plane z 1 (by norm_num) hz
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
  refine ⟨f, hfq, fun K' _ _ _ z' _ hdim => ?_⟩
  let : Algebra R Pe.Ring := ((algebraMap (MvPolynomial (Fin 2) R) Pe.Ring).comp
    (algebraMap R (MvPolynomial (Fin 2) R))).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pe.Ring :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψR : Pe.Ring →ₐ[R] Localization.Away f := ψ.restrictScalars R
  have h1 : ψR (coord R Pe.Ring 1) = 0 := by
    change ψ (algebraMap (MvPolynomial (Fin 2) R) Pe.Ring (MvPolynomial.X 1)) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) B
      (Localization.Away f)]
    change algebraMap B _ (MvPolynomial.aeval b (MvPolynomial.X 1)) = 0
    rw [MvPolynomial.aeval_X, hb0 1 (by simp), map_zero]
  have : Module.Flat R (Localization.Away f) := Module.Flat.trans R B (Localization.Away f)
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    Algebra.FinitePresentation.trans R B (Localization.Away f)
  obtain ⟨h, hhQ, hJ⟩ := exists_annihilator_of_coord_eq_zero ψR hψ z' h1 hdim
  set Q₀ := z'.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).comp ψR).toRingHom with hQ₀
  have : Q₀.IsPrime := Ideal.comap_isPrime _ _
  set a := h * 1 with ha
  have haQ : a ∉ Q₀ := by rw [ha, mul_one]; exact hhQ
  -- localize at `a`
  let Pa := Localization.Away a
  have : Algebra.Etale Pe.Ring Pa := Algebra.Etale.of_isLocalizationAway a
  have : Algebra.Etale (MvPolynomial (Fin 2) R) Pa := Algebra.Etale.comp _ Pe.Ring Pa
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pa := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R Pe.Ring Pa,
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) Pe.Ring,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) Pe.Ring Pa]
  have hdisj : Disjoint (Submonoid.powers a : Set Pe.Ring) Q₀ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr haQ
  set Q₀a := Q₀.map (algebraMap Pe.Ring Pa)
  have : Q₀a.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) Pa Q₀ ‹_› hdisj
  have hQ₀a : Q₀a.comap (algebraMap Pe.Ring Pa) = Q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) Pa ‹_› hdisj
  set ga := algebraMap Pe.Ring Pa (coord R Pe.Ring 1)
  have hgQ₀ : coord R Pe.Ring 1 ∈ Q₀ := by
    rw [hQ₀, Ideal.mem_comap]
    change (Algebra.TensorProduct.includeRight : Localization.Away f →ₐ[R] _)
      (ψR (coord R Pe.Ring 1)) ∈ z'
    rw [h1, map_zero]
    exact z'.zero_mem
  have hgaQ : ga ∈ Q₀a := Ideal.mem_map_of_mem _ hgQ₀
  -- the curve `T = Pa/(u₁) ≅ (B_f)_{ψ a}`, étale over `R[X₀, X₁]/(X₁)`
  set I₁ := Ideal.span {MvPolynomial.X (R := R) (1 : Fin 2)}
  have hI₁ : I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa) = Ideal.span {ga} := by
    rw [Ideal.map_span, Set.image_singleton, IsScalarTower.algebraMap_apply
      (MvPolynomial (Fin 2) R) Pe.Ring Pa]
  set T := Pa ⧸ I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa)
  let Bfs := Localization.Away (ψR a)
  let φa : Pa →ₐ[R] Bfs := Localization.awayMapₐ ψR a
  have hφa : Function.Surjective φa := IsLocalization.Away.mapₐ_surjective_of_surjective a hψ
  have hker : RingHom.ker φa.toRingHom = Ideal.span {ga} :=
    ker_awayMap_eq_span ψR (coord R Pe.Ring 1) h1 h 1 hJ
  let eB : T ≃ₐ[R] Bfs :=
    (Ideal.quotientEquivAlgOfEq R (hI₁.trans hker.symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective hφa)
  have heB : ∀ x, eB (Ideal.Quotient.mk _ x) = φa x := fun _ => rfl
  have himg : ∀ p : Pe.Ring, algebraMap (Localization.Away f) Bfs (ψR p) =
      φa (algebraMap Pe.Ring Pa p) := by
    intro p
    change _ = IsLocalization.Away.map Pa Bfs ψR.toRingHom a (algebraMap Pe.Ring Pa p)
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have : Algebra.FinitePresentation (MvPolynomial (Fin 2) R) T :=
    Algebra.FinitePresentation.quotient (hI₁ ▸ Submodule.fg_span_singleton ga)
  have := formallyEtale_quotient_map (MvPolynomial (Fin 2) R) Pa I₁
  have := isScalarTower_quotient_map (MvPolynomial (Fin 2) R) Pa I₁ (MvPolynomial (Fin 2) R)
  have : Algebra.FinitePresentation (MvPolynomial (Fin 2) R ⧸ I₁) T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation (MvPolynomial (Fin 2) R)
      (MvPolynomial (Fin 2) R ⧸ I₁) T
  have : Algebra.Etale (MvPolynomial (Fin 2) R ⧸ I₁) T := ⟨inferInstance, inferInstance⟩
  -- the point
  set QT : Ideal T := Q₀a.map (Ideal.Quotient.mk _)
  have hkerT : RingHom.ker (Ideal.Quotient.mk (I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa)))
      ≤ Q₀a := by
    rw [Ideal.mk_ker, hI₁, Ideal.span_le, Set.singleton_subset_iff]
    exact hgaQ
  have : QT.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerT
  have hQT : ∀ x, Ideal.Quotient.mk (I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa)) x ∈ QT ↔
      x ∈ Q₀a := by
    intro x
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerT]
  -- `T` is formally smooth over `R`, hence so is its local ring at `QT`
  have : Algebra.FormallySmooth R (MvPolynomial (Fin 2) R ⧸ I₁) :=
    Algebra.FormallySmooth.of_equiv (quotientXOneEquiv R).symm
  have := isScalarTower_quotient_map (MvPolynomial (Fin 2) R) Pa I₁ R
  have : Algebra.FormallySmooth R T :=
    Algebra.FormallySmooth.comp R (MvPolynomial (Fin 2) R ⧸ I₁) T
  have : Algebra.FormallySmooth R (Localization.AtPrime QT) :=
    Algebra.FormallySmooth.comp R T (Localization.AtPrime QT)
  -- transport back to `B_f`
  have : Algebra.FormallySmooth R (Localization.AtPrime (QT.comap eB.symm.toRingHom)) :=
    formallySmooth_localization_comap_of_algEquiv eB QT
  have h2 := formallySmooth_localization_comap_localization (R := R) (Submonoid.powers (ψR a))
    (QT.comap eB.symm.toRingHom)
  refine formallySmooth_localization_of_eq ?_ h2
  apply Ideal.comap_injective_of_surjective ψR.toRingHom hψ
  ext p
  simp only [Ideal.mem_comap]
  change eB.symm (algebraMap (Localization.Away f) Bfs (ψR p)) ∈ QT ↔ _
  rw [himg, ← heB, AlgEquiv.symm_apply_apply, hQT, ← Ideal.mem_comap, hQ₀a, hQ₀]
  rfl

end SmoothPoint

attribute [local instance] Curves.SemistableOpen.locallyOfFinitePresentation_spec

section FibreCriterion

open DeJong (IsNodalCurve IsSmoothAt)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The fibre criterion for nodal curves.** If a closed point `zp` of a geometric fibre
`K ⊗_R Γ(X, W)` of a nodal curve is a smooth point of `Spec (K ⊗_R Γ(X, W)) → Spec K`, then `f` is
smooth at the point of `W` under `zp`. -/
theorem mem_smoothLocus_of_tensorChart_spec {X S : Scheme.{u}} (f : X ⟶ S) [IsNodalCurve f]
    {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W) (hle : W ≤ f ⁻¹ᵁ V) :
    letI := (f.appLE V W hle).hom.toAlgebra
    ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra Γ(S, V) K]
      (zp : PrimeSpectrum (K ⊗[Γ(S, V)] Γ(X, W))),
      IsClosed ({zp} : Set (Spec (.of (K ⊗[Γ(S, V)] Γ(X, W))))) →
      tensorChart f (IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hle).symm
        (a := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec) rfl zp ∈
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫
          hV.fromSpec)).smoothLocus →
      hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (K ⊗[Γ(S, V)] Γ(X, W))) zp) ∈
        f.smoothLocus := by
  intro K _ _ _ zp hzc hs
  let := (f.appLE V W hle).hom.toAlgebra
  have : Module.Flat Γ(S, V) Γ(X, W) :=
    HasRingHomProperty.appLE @Flat f inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have : Algebra.FinitePresentation Γ(S, V) Γ(X, W) :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation f inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have hsq : hW.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hle).symm
  set a : Spec (.of K) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec
  have ha : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec = a := rfl
  set y := tensorChart f hsq ha zp
  have hy : IsClosed ({y} : Set (pullback (C := Scheme.{u}) f a)) :=
    isClosed_image_of_isClosed (tensorChart f hsq ha) (tensorChart_snd f hsq ha) hzc
  have hpure := IsNodalCurve.pureGeometricFibers (g := f) K a
  have hpureT := pure_of_etale (q' := pullback.snd f a) (tensorChart f hsq ha) hpure
  have hdim := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT zp hzc
  have hzs := mem_smoothLocus_of_tensorChart f hsq ha zp hs
  have h1 := (mem_smoothLocus_spec_iff zp hdim).mp hzs
  have : zp.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hzc
  obtain ⟨f₁, hf₁, hnext⟩ := exists_away_formallySmooth_of_spanFinrank_le_one zp.asIdeal h1
  set 𝔭 := PrimeSpectrum.comap (algebraMap Γ(X, W) (K ⊗[Γ(S, V)] Γ(X, W))) zp
  have hsq₁ := localization_chart_sq f hsq f₁
  have hxB₁ : pullback.fst f a y ∈ Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) (Localization.Away f₁))) ≫
        hW.fromSpec) := by
    rw [← jB_comap_eq f hsq ha zp]
    exact mem_range_localization_chart f₁ 𝔭 hf₁
  obtain ⟨z₁, hz₁y, hz₁c⟩ := exists_tensorChart_eq f hsq₁ ha y hy hxB₁
  have : z₁.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₁).mp hz₁c
  have : Module.Flat Γ(S, V) (Localization.Away f₁) := Module.Flat.trans _ Γ(X, W) _
  have : Algebra.FinitePresentation Γ(S, V) (Localization.Away f₁) :=
    Algebra.FinitePresentation.trans _ Γ(X, W) _
  have hpureT₁ := pure_of_etale (q' := pullback.snd f a) (tensorChart f hsq₁ ha) hpure
  have hdim₁ := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT₁ z₁ hz₁c
  let := Scheme.stalkAlgebra
    (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[Γ(S, V)] Localization.Away f₁)))) z₁
  let ε := (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv K
    (K ⊗[Γ(S, V)] Localization.Away f₁) z₁).toRingEquiv
  have hdimL : ringKrullDim (Localization.AtPrime z₁.asIdeal) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv ε]
    exact hdim₁
  have h₁ := hnext K z₁.asIdeal hdimL
  have h₂ := formallySmooth_localization_comap_localization (R := Γ(S, V))
    (Submonoid.powers f₁) (z₁.asIdeal.comap (Algebra.TensorProduct.includeRight :
      Localization.Away f₁ →ₐ[Γ(S, V)] K ⊗[Γ(S, V)] Localization.Away f₁).toRingHom)
  have hxz₁ := jB_comap_eq f hsq₁ ha z₁
  rw [hz₁y, ← jB_comap_eq f hsq ha zp, Scheme.Hom.comp_apply] at hxz₁
  have hz₁𝔭 := hW.fromSpec.isOpenEmbedding.injective hxz₁
  have hx𝔭W : hW.fromSpec 𝔭 ∈ W := by
    have := Set.mem_range_self (f := hW.fromSpec) 𝔭
    rwa [hW.range_fromSpec] at this
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff V hV W hW hle hx𝔭W,
    hW.primeIdealOf_fromSpec 𝔭 hx𝔭W]
  change Algebra.FormallySmooth Γ(S, V) (Localization.AtPrime 𝔭.asIdeal)
  exact formallySmooth_localization_of_eq (congrArg PrimeSpectrum.asIdeal hz₁𝔭) h₂

end FibreCriterion

section EtaleDescent

open DeJong (IsNodalCurve IsSmoothAt)

open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV in
/-- The formal node `K[[u, v]]/(uv)` is not a domain. -/
theorem not_isDomain_formalUV (K : Type u) [Field K] : ¬ IsDomain (FormalUV K) := by
  intro h
  have hne : ∀ i j : Fin 2, i ≠ j → coordinate K i ≠ 0 := by
    intro i j hij h0
    rw [coordinate, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    have hj : (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X i := by
      refine dvd_trans ?_ h0
      rw [uvPolynomial, MvPolynomial.coe_mul, MvPolynomial.coe_X, MvPolynomial.coe_X]
      fin_cases j
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    rw [MvPowerSeries.X_dvd_iff] at hj
    have h1 := hj (Finsupp.single i 1) (by rw [Finsupp.single_apply, if_neg hij])
    rw [MvPowerSeries.coeff_X, if_pos rfl] at h1
    exact one_ne_zero h1
  have huv : coordinate K 0 * coordinate K 1 = 0 := by
    rw [coordinate, coordinate, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.subset_span
    rw [Set.mem_singleton_iff, uvPolynomial, MvPolynomial.coe_mul, MvPolynomial.coe_X,
      MvPolynomial.coe_X]
  rcases mul_eq_zero.mp huv with h0 | h0
  · exact hne 0 1 (by decide) h0
  · exact hne 1 0 (by decide) h0

/-- **A formal node is not a smooth point**: the local ring at a formal node of a curve does not
have principal maximal ideal (otherwise it would be regular, and so would be its completion
`K[[u, v]]/(uv)`, which is not a domain). -/
theorem not_spanFinrank_le_one_of_isFormalNode {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [IsNoetherianRing A] (z : Ideal A) [z.IsPrime] (hz : IsFormalNode K z)
    (hdim : ringKrullDim (Localization.AtPrime z) = 1) :
    ¬ (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1 := by
  intro hspan
  obtain ⟨e⟩ := hz
  have : IsRegularLocalRing (Localization.AtPrime z) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by rw [hdim]; exact_mod_cast hspan)
  have := Algebra.CompletionRegularityAscent.isRegularLocalRing_completion
    (Localization.AtPrime z)
  have : IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime z))
      (Localization.AtPrime z)) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  exact not_isDomain_formalUV K (e.symm.toRingEquiv.injective.isDomain e.symm.toRingHom)

/-- **Smoothness descends along étale maps** (Stacks, Tag 02K5), as a proposition about `f`: if
`ψ : X' ⟶ X` is étale and `ψ ≫ f` is smooth at `y`, then `f` is smooth at `ψ y`. -/
def SmoothDescendsAlongEtale {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (X' : Scheme.{u}) (ψ : X' ⟶ X) [Etale ψ] (y : X'), IsSmoothAt (ψ ≫ f) y → IsSmoothAt f (ψ y)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Smoothness of a nodal curve descends along étale maps.** If `ψ : X' ⟶ X` is étale and
`ψ ≫ f` is smooth at `y`, take a closed point `y'` of a geometric fibre of `ψ ≫ f` over `y` and its
image `y₀` in the geometric fibre of `f` over `ψ y`. If `y₀` were a node, so would be `y'`
(étale maps preserve completions at closed points), but nodes are not smooth; so `y₀` is a smooth
point and `f` is smooth at `ψ y` by the fibre criterion `mem_smoothLocus_of_tensorChart_spec`. -/
theorem smoothDescendsAlongEtale_of_isNodalCurve {X S : Scheme.{u}} (f : X ⟶ S) [IsNodalCurve f] :
    SmoothDescendsAlongEtale f := by
  intro X' ψ _ y hy
  have : IsNodalCurve (ψ ≫ f) := IsNodalCurve.etale_comp ψ f
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f (ψ y)) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := ψ y) (U := f ⁻¹ᵁ V) hxV
  obtain ⟨W', hW', hyW', hW'W⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ψ ⁻¹ᵁ W) hxW
  have hle : W ≤ f ⁻¹ᵁ V := hWV
  have hle' : W' ≤ ψ ⁻¹ᵁ W := hW'W
  have hle'' : W' ≤ (ψ ≫ f) ⁻¹ᵁ V := fun y hy => hle (hle' hy)
  -- the geometric point over `y`
  let : Algebra Γ(S, V) Γ(X', W') := ((ψ ≫ f).appLE V W' hle'').hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, V) Γ(X', W') :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation (ψ ≫ f) inferInstance ⟨V, hV⟩
      ⟨W', hW'⟩ hle''
  have hsq' : hW'.fromSpec ≫ (ψ ≫ f) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X', W'))) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec (ψ ≫ f) hV hW' hle'').symm
  set 𝔮 := hW'.primeIdealOf ⟨y, hyW'⟩
  have hy𝔮 : hW'.fromSpec 𝔮 = y := hW'.fromSpec_primeIdealOf ⟨y, hyW'⟩
  obtain ⟨K, _, _, _, z', hz'max, hz'𝔮⟩ := exists_geometricPoint (R := Γ(S, V)) 𝔮.asIdeal
  set a : Spec (.of K) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec
  have ha : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec = a := rfl
  set z'p : PrimeSpectrum (K ⊗[Γ(S, V)] Γ(X', W')) := ⟨z', hz'max.isPrime⟩
  have hz'c : IsClosed ({z'p} : Set (Spec (.of (K ⊗[Γ(S, V)] Γ(X', W'))))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hz'max
  set y' := tensorChart (ψ ≫ f) hsq' ha z'p
  have hy'y : pullback.fst (ψ ≫ f) a y' = y := by
    rw [← jB_comap_eq (ψ ≫ f) hsq' ha z'p]
    have : PrimeSpectrum.comap (algebraMap Γ(X', W') (K ⊗[Γ(S, V)] Γ(X', W'))) z'p = 𝔮 :=
      PrimeSpectrum.ext hz'𝔮
    rw [this, hy𝔮]
  have hy'c : IsClosed ({y'} : Set (pullback (C := Scheme.{u}) (ψ ≫ f) a)) :=
    isClosed_image_of_isClosed (tensorChart (ψ ≫ f) hsq' ha) (tensorChart_snd (ψ ≫ f) hsq' ha)
      hz'c
  have hy's : y' ∈ (pullback.snd (ψ ≫ f) a).smoothLocus :=
    preimage_smoothLocus_le_smoothLocus_pullback_snd (ψ ≫ f) a
      (show pullback.fst (ψ ≫ f) a y' ∈ (ψ ≫ f).smoothLocus by rw [hy'y]; exact hy)
  -- its image in the geometric fibre of `f`
  set E := pullbackCompMap ψ f a
  set y₀ := E y'
  have hy₀c : IsClosed ({y₀} : Set (pullback (C := Scheme.{u}) f a)) :=
    isClosed_image_of_isClosed E (pullbackCompMap_snd ψ f a) hy'c
  have hy₀x : pullback.fst f a y₀ = ψ y := by
    change (E ≫ pullback.fst f a) y' = ψ y
    rw [pullbackCompMap_fst, Scheme.Hom.comp_apply, hy'y]
  rcases IsNodalCurve.geometricNodes (g := f) K a y₀ hy₀c with hs | hn
  · -- a smooth point downstairs: the fibre criterion
    let : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W hle).hom.toAlgebra
    have hsq : hW.fromSpec ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))) ≫ hV.fromSpec :=
      (IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hle).symm
    have hxB : pullback.fst f a y₀ ∈ Set.range hW.fromSpec := by
      rw [hy₀x, hW.range_fromSpec]
      exact hxW
    obtain ⟨zp, hzpy, hzpc⟩ := exists_tensorChart_eq f hsq ha y₀ hy₀c hxB
    have h := mem_smoothLocus_of_tensorChart_spec f hV hW hle K zp hzpc (hzpy ▸ hs)
    have hpt := jB_comap_eq f hsq ha zp
    rw [hzpy, hy₀x] at hpt
    rw [hpt] at h
    exact h
  · -- a node downstairs gives a node upstairs, which is not smooth
    exfalso
    have : IsIso (E.residueFieldMap y') :=
      isIso_residueFieldMap_of_isClosed (K := K) E (pullbackCompMap_snd ψ f a) hy'c
    have hn' := isGeometricOrdinaryDoublePoint_of_etale E (pullback.snd f a) y' hn
    rw [pullbackCompMap_snd] at hn'
    have hz'n := isGeometricOrdinaryDoublePoint_of_tensorChart (ψ ≫ f) hsq' ha z'p hz'c hn'
    have hz'n' := (isGeometricOrdinaryDoublePoint_spec_iff z'p).mp hz'n
    have hz's := mem_smoothLocus_of_tensorChart (ψ ≫ f) hsq' ha z'p hy's
    have hpure' := IsNodalCurve.pureGeometricFibers (g := ψ ≫ f) K a
    have hpureT' := pure_of_etale (q' := pullback.snd (ψ ≫ f) a) (tensorChart (ψ ≫ f) hsq' ha)
      hpure'
    have hdim' := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT' z'p hz'c
    have h1' := (mem_smoothLocus_spec_iff z'p hdim').mp hz's
    let := Scheme.stalkAlgebra
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[Γ(S, V)] Γ(X', W'))))) z'p
    let ε := (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv K
      (K ⊗[Γ(S, V)] Γ(X', W')) z'p).toRingEquiv
    have hdimL : ringKrullDim (Localization.AtPrime z'p.asIdeal) = 1 := by
      rw [← ringKrullDim_eq_of_ringEquiv ε]
      exact hdim'
    have : IsNoetherianRing (K ⊗[Γ(S, V)] Γ(X', W')) := Algebra.FiniteType.isNoetherianRing K _
    exact not_spanFinrank_le_one_of_isFormalNode z'p.asIdeal hz'n' hdimL h1'

end EtaleDescent

end DeJongAlterations.StableModification.Omega
