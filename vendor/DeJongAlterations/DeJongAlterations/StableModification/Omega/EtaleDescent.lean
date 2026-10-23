import DeJongAlterations.StableModification.Omega.EtaleOmega
import DeJongAlterations.StableModification.Curves.Basic

/-!
# Étale descent of the invertibility of `ω_{X/S}`

Step 3 of `lem:sm-omega-invertible` (blueprint `sm-omega-invertible.tex`,
`lem:sm-omega-etale-descent`; M. Temkin, *Stable modification of relative curves*, §1.2,
T:1700–1712: "`ω_{X/S}` is invertible since this is so étale-locally, where `X` is
`R[u, v]/(uv − h)`"). Let `f : X ⟶ S` be locally of finite presentation, `ψ : X' ⟶ X`,
`W ⊆ X`, `W' ⊆ X'` affine opens with `W' ≤ ψ⁻¹ W` and `Γ(X, W) → Γ(X', W')` étale.

* `bijective_smul_of_baseChange`: faithfully flat descent of a free generator: if
  `A ⊗_R M ≅ N` and the image of `1 ⊗ m` freely generates `N`, then `m` freely generates `M`.
* `faithfullyFlat_of_surjective`, `etale_appLE_basicOpen`: faithful flatness from surjectivity
  on points; étaleness passes to basic opens.
* `exists_generator_of_etale`: if `ψ` is compatible with the smooth loci, surjective onto `W`
  and open on basic opens, and `Ω¹_{X'/S}` has a free generator over `W' ∩ U'` on every basic open,
  then around every `x ∈ W` there is a basic open `D(t)` and a free generator of `Ω¹_{X/S}` over
  `D(t) ∩ U` on every basic open of `D(t)`.
* `isInvertibleAt_dualizingSheaf_of_etale`, `isInvertibleAt_dualizingSheaf_of_etale_of_surjective`:
  consequently, if `ψ ≫ f` is a two-chart affine on `W'` (for instance an étale node chart,
  `EtaleNodeChart.twoChartAffine`), then `ω_{X/S}` is invertible at every point of `W`; for `ψ`
  étale, only the descent of smoothness along `ψ` (the hard half of the étale invariance of the
  smooth locus) and surjectivity onto `W` remain as hypotheses.
* `exists_eq_iSup_basicOpen_of_isCompact`, `exists_basicOpen_inf_eq_iSup`: quasi-compact opens
  of an affine are finite unions of basic opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct

universe u

namespace DeJongAlterations.StableModification.Omega

section Aux

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X)

theorem _root_.AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec {U : X.Opens}
    (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) (h : hU.fromSpec p ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec p, h⟩ = p :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

/-- Étaleness of `ψ^♯` passes to basic opens. -/
theorem etale_appLE_basicOpen {W : X.Opens} (hW : IsAffineOpen W) {W' : X'.Opens}
    (hW' : IsAffineOpen W') (hWW' : W' ≤ ψ ⁻¹ᵁ W) (hét : (ψ.appLE W W' hWW').hom.Etale)
    (g : Γ(X, W)) (h : Γ(X', W')) (hle : X'.basicOpen h ≤ ψ ⁻¹ᵁ X.basicOpen g) :
    (ψ.appLE (X.basicOpen g) (X'.basicOpen h) hle).hom.Etale := by
  let := pullAlgebra ψ hWW'
  have : Algebra.Etale Γ(X, W) Γ(X', W') := hét
  let : Algebra Γ(X, W) Γ(X, X.basicOpen g) := (res (X.basicOpen_le g)).toAlgebra
  let : Algebra Γ(X', W') Γ(X', X'.basicOpen h) := (res (X'.basicOpen_le h)).toAlgebra
  let : Algebra Γ(X, X.basicOpen g) Γ(X', X'.basicOpen h) :=
    (ψ.appLE (X.basicOpen g) (X'.basicOpen h) hle).hom.toAlgebra
  let : Algebra Γ(X, W) Γ(X', X'.basicOpen h) :=
    (ψ.appLE W (X'.basicOpen h) ((X'.basicOpen_le h).trans hWW')).hom.toAlgebra
  have : IsScalarTower Γ(X, W) Γ(X', W') Γ(X', X'.basicOpen h) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      change ψ.appLE W _ _ a = res (X'.basicOpen_le h) (ψ.appLE W W' hWW' a)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  have : IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) Γ(X', X'.basicOpen h) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      change ψ.appLE W _ _ a = ψ.appLE (X.basicOpen g) _ hle (res (X.basicOpen_le g) a)
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE])
  have : IsLocalization (Submonoid.powers h) Γ(X', X'.basicOpen h) := hW'.isLocalization_basicOpen h
  have : IsLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) := hW.isLocalization_basicOpen g
  have : Algebra.Etale Γ(X', W') Γ(X', X'.basicOpen h) := Algebra.Etale.of_isLocalizationAway h
  have : Algebra.Etale Γ(X, W) Γ(X', X'.basicOpen h) :=
    Algebra.Etale.comp Γ(X, W) Γ(X', W') Γ(X', X'.basicOpen h)
  have : Algebra.Etale Γ(X, W) Γ(X, X.basicOpen g) := Algebra.Etale.of_isLocalizationAway g
  have : Algebra.Etale Γ(X, X.basicOpen g) Γ(X', X'.basicOpen h) :=
    Algebra.Etale.of_restrictScalars Γ(X, W) Γ(X, X.basicOpen g) Γ(X', X'.basicOpen h)
  exact this

/-- Faithful flatness from surjectivity on points. -/
theorem faithfullyFlat_of_surjective {W : X.Opens} (hW : IsAffineOpen W) {W' : X'.Opens}
    (hW' : IsAffineOpen W') (hWW' : W' ≤ ψ ⁻¹ᵁ W)
    (hflat : letI := pullAlgebra ψ hWW'; Module.Flat Γ(X, W) Γ(X', W'))
    (hsurj : ∀ y ∈ W, ∃ y' ∈ W', ψ y' = y) :
    letI := pullAlgebra ψ hWW'
    Module.FaithfullyFlat Γ(X, W) Γ(X', W') := by
  let := pullAlgebra ψ hWW'
  refine Module.FaithfullyFlat.of_comap_surjective (fun p => ?_)
  have hp : hW.fromSpec p ∈ (W : Set X) := by
    rw [← hW.range_fromSpec]; exact Set.mem_range_self _
  obtain ⟨y', hy', hψ⟩ := hsurj _ hp
  refine ⟨hW'.primeIdealOf ⟨y', hy'⟩, ?_⟩
  have := IsAffineOpen.comap_primeIdealOf_appLE W hW W' hW' hWW' hy'
  change (hW'.primeIdealOf ⟨y', hy'⟩).comap (ψ.appLE W W' hWW').hom = p
  rw [this]
  convert hW.primeIdealOf_fromSpec p hp using 2
  exact Subtype.ext hψ

end Aux


section Natural

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) {F : X.Modules} {G : X'.Modules}
  (θ : F ⟶ (Scheme.Modules.pushforward ψ).obj G)

theorem secLinear_restrict₂ {W₁ : X.Opens} {W₁' : X'.Opens} (h₁' : W₁' ≤ ψ ⁻¹ᵁ W₁)
    {W₂ : X.Opens} {W₂' : X'.Opens} (h₂' : W₂' ≤ ψ ⁻¹ᵁ W₂) {Y₁ Y₂ : X.Opens} (hY₁ : Y₁ ≤ W₁)
    (hY₂ : Y₂ ≤ W₂) (hY : Y₂ ≤ Y₁) (hW' : W₂' ≤ W₁') (m : Γ(F, Y₁)) :
    SecOver.equiv _ _ (secLinear ψ θ h₂' hY₂
        ((SecOver.equiv F hY₂).symm (F.presheaf.map (homOfLE hY).op m))) =
      G.presheaf.map (homOfLE (inf_le_inf (ψ.preimage_mono hY) hW')).op
        (SecOver.equiv _ _ (secLinear ψ θ h₁' hY₁ ((SecOver.equiv F hY₁).symm m))) := by
  change G.presheaf.map (homOfLE inf_le_left).op
      (secMap₀ ψ θ Y₂ (F.presheaf.map (homOfLE hY).op m)) =
    G.presheaf.map _ (G.presheaf.map (homOfLE inf_le_left).op (secMap₀ ψ θ Y₁ m))
  rw [secMap₀_map, map_map_eq, map_map_eq]

end Natural


section FFDescent

/-- **Faithfully flat descent of a generator.** If `Θ : A ⊗_R M ≅ N` and `Θ (1 ⊗ m)` generates the
`A`-module `N` freely, then `m` generates `M` freely, provided `A` is faithfully flat over `R`. -/
theorem bijective_smul_of_baseChange {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module A N]
    [Module R N] [IsScalarTower R A N] (Θ : A ⊗[R] M →ₗ[A] N) (hΘ : Function.Bijective Θ) (m : M)
    (hn : Function.Bijective (fun a : A => a • Θ (1 ⊗ₜ m))) :
    Function.Bijective (fun r : R => r • m) := by
  let μ : R →ₗ[R] M := LinearMap.toSpanSingleton R M m
  have hcomp : (Θ : A ⊗[R] M → N) ∘ (μ.lTensor A) =
      (fun a : A => a • Θ (1 ⊗ₜ m)) ∘ (TensorProduct.AlgebraTensorModule.rid R A A) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [Function.comp_apply, map_add, add_smul] at ha hb ⊢
      rw [ha, hb]
    | tmul a r =>
      simp only [Function.comp_apply, LinearMap.lTensor_tmul,
        TensorProduct.AlgebraTensorModule.rid_tmul, μ, LinearMap.toSpanSingleton_apply]
      rw [← TensorProduct.smul_tmul, show (r • a) ⊗ₜ[R] m = (r • a) • ((1 : A) ⊗ₜ[R] m) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
  have h1 : Function.Bijective ((Θ : A ⊗[R] M → N) ∘ (μ.lTensor A)) := by
    rw [hcomp]
    exact hn.comp (TensorProduct.AlgebraTensorModule.rid R A A).bijective
  have h2 : Function.Bijective (μ.lTensor A) := (Function.Bijective.of_comp_iff' hΘ _).mp h1
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R A μ).mp h2

end FFDescent


section Descent

variable {X X' S : Scheme.{u}} (f : X ⟶ S) (ψ : X' ⟶ X) [LocallyOfFinitePresentation f]
  [LocallyOfFinitePresentation (ψ ≫ f)] {V : S.Opens} (hV : IsAffineOpen V)
  {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) {W' : X'.Opens} (hW' : IsAffineOpen W')
  (hWW' : W' ≤ ψ ⁻¹ᵁ W)

omit [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (ψ ≫ f)] in
include hV hW hWV hW' in
/-- Flat base change of `Ω¹` over a finite union of basic opens, for an arbitrary open `Y`
equal to it. -/
theorem bijective_baseChangeSec_of_eq_iSup (hét : (ψ.appLE W W' hWW').hom.Etale) {Y : X.Opens}
    (hY : Y ≤ W) {n : ℕ} (b : Fin n → Γ(X, W)) (hYb : Y = ⨆ i, X.basicOpen (b i)) :
    Function.Bijective (baseChangeSec ψ (pullbackDifferentials f ψ) hWW' hY) := by
  subst hYb
  exact bijective_baseChangeSec_iSup_of_etale f ψ hV hW hWV hW' hWW' hét b

include hV hW hWV hW' in
/-- **Descent of a generator of `Ω¹` on the smooth locus along an étale map.** -/
theorem exists_generator_of_etale (hét : (ψ.appLE W W' hWW').hom.Etale)
    (hsm : ψ ⁻¹ᵁ f.smoothLocus ⊓ W' = (ψ ≫ f).smoothLocus ⊓ W')
    (hqc : ∀ g : Γ(X, W), ∃ (n : ℕ) (b : Fin n → Γ(X, W)),
      X.basicOpen g ⊓ f.smoothLocus = ⨆ i, X.basicOpen (b i))
    (τ' : Γ(relativeDifferentials (ψ ≫ f), W' ⊓ (ψ ≫ f).smoothLocus))
    (hτ' : ∀ (D : X'.Opens) (hD : D ≤ W'), (∃ h : Γ(X', W'), D = X'.basicOpen h) →
      Function.Bijective (fun c : Γ(X', D) =>
        res (inf_le_left : D ⊓ (ψ ≫ f).smoothLocus ≤ D) c •
          (relativeDifferentials (ψ ≫ f)).presheaf.map
            (homOfLE (inf_le_inf_right (ψ ≫ f).smoothLocus hD)).op τ'))
    (hsurj : ∀ y ∈ W, ∃ y' ∈ W', ψ y' = y)
    (hopen : ∀ h : Γ(X', W'), IsOpen (ψ '' (X'.basicOpen h : Set X')))
    {x : X} (hx : x ∈ W) :
    ∃ (t : Γ(X, W)) (_ : x ∈ X.basicOpen t)
      (m : Γ(relativeDifferentials f, X.basicOpen t ⊓ f.smoothLocus)),
      ∀ g : Γ(X, X.basicOpen t), Function.Bijective (fun c : Γ(X, X.basicOpen g) =>
        res (inf_le_left : X.basicOpen g ⊓ f.smoothLocus ≤ X.basicOpen g) c •
          (relativeDifferentials f).presheaf.map
            (homOfLE (inf_le_inf_right f.smoothLocus (X.basicOpen_le g))).op m) := by
  let θ := pullbackDifferentials f ψ
  let := pullAlgebra ψ hWW'
  have hY₀ : W ⊓ f.smoothLocus ≤ W := inf_le_left
  -- Step 1: base change on `W ∩ U`
  obtain ⟨n₀, b₀, hb₀⟩ := hqc 1
  have hW1 : W ⊓ f.smoothLocus = ⨆ i, X.basicOpen (b₀ i) := by rw [← hb₀, basicOpen_one_eq]
  have hΘ := bijective_baseChangeSec_of_eq_iSup f ψ hV hW hWV hW' hWW' hét hY₀ b₀ hW1
  -- Step 2: the upstairs generator over `W'`
  have hsm' : ∀ y, y ∈ ψ ⁻¹ᵁ f.smoothLocus ⊓ W' ↔ y ∈ (ψ ≫ f).smoothLocus ⊓ W' := fun y => by
    rw [hsm]
  have heq₀ : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W' = W' ⊓ (ψ ≫ f).smoothLocus := by
    ext y
    have := hsm' y
    simp only [TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage] at this ⊢
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩
      exact ⟨h2, (this.mp ⟨h1, h2⟩).1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨⟨hWW' h2, (this.mpr ⟨h1, h2⟩).1⟩, h2⟩
  set T₀ := SecOver (relativeDifferentials (ψ ≫ f))
    (inf_le_right : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W' ≤ W')
  set τT : T₀ := (SecOver.equiv _ _).symm
    ((relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heq₀.le).op τ')
  let gen₀ : Γ(X', W') →ₗ[Γ(X', W')] T₀ := LinearMap.toSpanSingleton Γ(X', W') T₀ τT
  have hgen₀ : Function.Bijective gen₀ := by
    have h1 := hτ' W' le_rfl ⟨1, (basicOpen_one_eq (W := W')).symm⟩
    have h2 : Function.Bijective ((relativeDifferentials (ψ ≫ f)).presheaf.map
        (homOfLE heq₀.le).op) := (relativeDifferentials (ψ ≫ f)).map_bijective_of_le _ heq₀.ge
    have hfun : (gen₀ : Γ(X', W') → T₀) = (SecOver.equiv _ _).symm ∘
        (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heq₀.le).op ∘
          (fun c : Γ(X', W') => res (inf_le_left : W' ⊓ (ψ ≫ f).smoothLocus ≤ W') c •
            (relativeDifferentials (ψ ≫ f)).presheaf.map
              (homOfLE (inf_le_inf_right (ψ ≫ f).smoothLocus (le_refl W'))).op τ') := by
      funext c
      apply (SecOver.equiv _ _).injective
      simp only [Function.comp_apply, AddEquiv.apply_symm_apply]
      change res (inf_le_right : ψ ⁻¹ᵁ (W ⊓ f.smoothLocus) ⊓ W' ≤ W') c •
          (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heq₀.le).op τ' = _
      rw [Ω_map_res_smul, res_res, map_map_eq]
    rw [hfun]
    exact (SecOver.equiv _ _).symm.bijective.comp (h2.comp h1)
  let coeff := (LinearEquiv.ofBijective gen₀ hgen₀).symm
  -- Step 3: a section whose image generates at `x'`
  obtain ⟨x', hx'W', hx'⟩ := hsurj x hx
  set p := (hW'.primeIdealOf ⟨x', hx'W'⟩).asIdeal
  have hm : ∃ m : SecOver (relativeDifferentials f) hY₀,
      coeff (secLinear ψ θ hWW' hY₀ m) ∉ p := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    let P : Submodule Γ(X', W') T₀ :=
      Submodule.comap coeff.toLinearMap (p.restrictScalars Γ(X', W'))
    have hP : ∀ t, baseChangeSec ψ θ hWW' hY₀ t ∈ P := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact P.zero_mem
      | add a b ha hb => rw [map_add]; exact P.add_mem ha hb
      | tmul a' m =>
        change a' • secLinear ψ θ hWW' hY₀ m ∈ P
        exact P.smul_mem a' (hcon m)
    obtain ⟨t, ht⟩ := hΘ.2 τT
    have h1 := hP t
    rw [ht] at h1
    have : coeff τT = 1 := by
      have hg1 : gen₀ 1 = τT := by simp [gen₀]
      rw [← hg1]
      exact (LinearEquiv.ofBijective gen₀ hgen₀).symm_apply_apply 1
    have h2 : coeff τT ∈ p := h1
    rw [this] at h2
    exact (hW'.primeIdealOf ⟨x', hx'W'⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨m, hmp⟩ := hm
  set c' := coeff (secLinear ψ θ hWW' hY₀ m)
  have hmc : secLinear ψ θ hWW' hY₀ m = c' • τT := by
    have := (LinearEquiv.ofBijective gen₀ hgen₀).apply_symm_apply (secLinear ψ θ hWW' hY₀ m)
    rw [← this]
    rfl
  have hx'c : x' ∈ X'.basicOpen c' := (mem_basicOpen_iff_notMem hW' hx'W' c').mpr hmp
  -- Step 4: a basic open around `x` inside `ψ (D(c'))`
  have hxim : x ∈ ψ '' (X'.basicOpen c' : Set X') := ⟨x', hx'c, hx'⟩
  obtain ⟨t, htle, hxt⟩ := hW.exists_basicOpen_le (V := ⟨_, hopen c'⟩) ⟨x, hxim⟩ hx
  have hU : X.basicOpen t ⊓ f.smoothLocus ≤ W ⊓ f.smoothLocus :=
    inf_le_inf_right _ (X.basicOpen_le t)
  let mt : Γ(relativeDifferentials f, X.basicOpen t ⊓ f.smoothLocus) :=
    (relativeDifferentials f).presheaf.map (homOfLE hU).op (SecOver.equiv _ _ m)
  refine ⟨t, hxt, mt, fun g => ?_⟩
  obtain ⟨g₀, hg₀⟩ := hW.basicOpen_basicOpen_is_basicOpen t g
  -- Step 5: descent over `D(g) = D(g₀)`
  suffices key : ∀ (D : X.Opens) (hDt : D ≤ X.basicOpen t), D = X.basicOpen g₀ →
      Function.Bijective (fun c : Γ(X, D) =>
        res (inf_le_left : D ⊓ f.smoothLocus ≤ D) c •
          (relativeDifferentials f).presheaf.map
            (homOfLE (inf_le_inf_right f.smoothLocus hDt)).op mt) from
    key _ (X.basicOpen_le g) hg₀.symm
  intro D hDt hD
  subst hD
  have hDW : X.basicOpen g₀ ≤ W := X.basicOpen_le g₀
  have hDaff : IsAffineOpen (X.basicOpen g₀) := hW.basicOpen g₀
  have hDV : X.basicOpen g₀ ≤ f ⁻¹ᵁ V := hDW.trans hWV
  let h'' : Γ(X', W') := c' * ψ.appLE W W' hWW' g₀
  have hW''aff : IsAffineOpen (X'.basicOpen h'') := hW'.basicOpen h''
  have hW''eq : X'.basicOpen h'' = X'.basicOpen c' ⊓ (ψ ⁻¹ᵁ X.basicOpen g₀ ⊓ W') := by
    rw [Scheme.basicOpen_mul, basicOpen_appLE_eq]
  have hW''le : X'.basicOpen h'' ≤ ψ ⁻¹ᵁ X.basicOpen g₀ :=
    hW''eq.le.trans (inf_le_right.trans inf_le_left)
  have hW''W' : X'.basicOpen h'' ≤ W' := X'.basicOpen_le h''
  have hW''c : X'.basicOpen h'' ≤ X'.basicOpen c' := hW''eq.le.trans inf_le_left
  have hét'' := etale_appLE_basicOpen ψ hW hW' hWW' hét g₀ h'' hW''le
  have hsurj'' : ∀ y ∈ X.basicOpen g₀, ∃ y' ∈ X'.basicOpen h'', ψ y' = y := by
    intro y hy
    have hy' : y ∈ ψ '' (X'.basicOpen c' : Set X') := htle (hDt hy)
    obtain ⟨y', hy'c, rfl⟩ := hy'
    refine ⟨y', ?_, rfl⟩
    rw [hW''eq]
    exact ⟨hy'c, hy, X'.basicOpen_le c' hy'c⟩
  let := pullAlgebra ψ hW''le
  have hEt : Algebra.Etale Γ(X, X.basicOpen g₀) Γ(X', X'.basicOpen h'') := hét''
  have hFF : Module.FaithfullyFlat Γ(X, X.basicOpen g₀) Γ(X', X'.basicOpen h'') :=
    faithfullyFlat_of_surjective ψ hDaff hW''aff hW''le inferInstance hsurj''
  obtain ⟨n, b, hb⟩ := hqc g₀
  let b' : Fin n → Γ(X, X.basicOpen g₀) := fun i => res hDW (b i)
  have hb' : ∀ i, X.basicOpen (b' i) = X.basicOpen g₀ ⊓ X.basicOpen (b i) := fun i =>
    Scheme.basicOpen_res X (b i) (homOfLE hDW).op
  have hYb : X.basicOpen g₀ ⊓ f.smoothLocus = ⨆ i, X.basicOpen (b' i) := by
    simp only [hb']
    rw [← inf_iSup_eq, ← hb, ← inf_assoc, inf_idem]
  have hΘ'' := bijective_baseChangeSec_of_eq_iSup f ψ hV hDaff hDV hW''aff hW''le hét''
    (inf_le_left : X.basicOpen g₀ ⊓ f.smoothLocus ≤ X.basicOpen g₀) b' hYb
  let mD : SecOver (relativeDifferentials f)
      (inf_le_left : X.basicOpen g₀ ⊓ f.smoothLocus ≤ X.basicOpen g₀) :=
    (SecOver.equiv _ _).symm ((relativeDifferentials f).presheaf.map
      (homOfLE (inf_le_inf_right f.smoothLocus hDt)).op mt)
  have hmD : mD = (SecOver.equiv _ _).symm ((relativeDifferentials f).presheaf.map
      (homOfLE (inf_le_inf_right f.smoothLocus hDW)).op (SecOver.equiv _ _ m)) := by
    simp only [mD, mt, map_map_eq]
  have hle₄ : ψ ⁻¹ᵁ (X.basicOpen g₀ ⊓ f.smoothLocus) ⊓ X'.basicOpen h'' ≤ W' :=
    inf_le_right.trans hW''W'
  have heq'' : ψ ⁻¹ᵁ (X.basicOpen g₀ ⊓ f.smoothLocus) ⊓ X'.basicOpen h'' =
      X'.basicOpen h'' ⊓ (ψ ≫ f).smoothLocus := by
    ext y
    have := hsm' y
    have hy1 : y ∈ X'.basicOpen h'' → y ∈ ψ ⁻¹ᵁ X.basicOpen g₀ := fun h => hW''le h
    have hy2 : y ∈ X'.basicOpen h'' → y ∈ W' := fun h => hW''W' h
    simp only [TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage] at this hy1 hy2 ⊢
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩
      exact ⟨h2, (this.mp ⟨h1, hy2 h2⟩).1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨⟨hy1 h2, (this.mpr ⟨h1, hy2 h2⟩).1⟩, h2⟩
  have hle₃ : ψ ⁻¹ᵁ (X.basicOpen g₀ ⊓ f.smoothLocus) ⊓ X'.basicOpen h'' ≤
      W' ⊓ (ψ ≫ f).smoothLocus :=
    heq''.le.trans (inf_le_inf_right _ hW''W')
  let := pullModule ψ hW''le (G := relativeDifferentials (ψ ≫ f))
    (inf_le_right : ψ ⁻¹ᵁ (X.basicOpen g₀ ⊓ f.smoothLocus) ⊓ X'.basicOpen h'' ≤ X'.basicOpen h'')
  have := pullIsScalarTower ψ hW''le (G := relativeDifferentials (ψ ≫ f))
    (inf_le_right : ψ ⁻¹ᵁ (X.basicOpen g₀ ⊓ f.smoothLocus) ⊓ X'.basicOpen h'' ≤ X'.basicOpen h'')
  have hval : SecOver.equiv _ _ (baseChangeSec ψ θ hW''le
      (inf_le_left : X.basicOpen g₀ ⊓ f.smoothLocus ≤ X.basicOpen g₀) (1 ⊗ₜ mD)) =
      res hle₄ c' • (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE hle₃).op τ' := by
    have h2 := secLinear_restrict₂ ψ θ hWW' hW''le hY₀
      (inf_le_left : X.basicOpen g₀ ⊓ f.smoothLocus ≤ X.basicOpen g₀)
      (inf_le_inf_right f.smoothLocus hDW) hW''W' (SecOver.equiv _ _ m)
    rw [AddEquiv.symm_apply_apply, hmc] at h2
    change SecOver.equiv _ _ (((secLinear ψ θ hW''le _).liftBaseChange _) (1 ⊗ₜ mD)) = _
    rw [LinearMap.liftBaseChange_tmul, one_smul, hmD, h2, SecOver.smul_def,
      AddEquiv.apply_symm_apply, Ω_map_res_smul, map_map_eq, res_res]
  have hu : IsUnit (res hW''W' c') := by
    have := (X'.toRingedSpace.isUnit_res_basicOpen c').map (res hW''c)
    change IsUnit (res hW''c (res (X'.basicOpen_le c') c')) at this
    rwa [res_res] at this
  have hmulu : Function.Bijective (fun a : Γ(X', X'.basicOpen h'') => a * res hW''W' c') := by
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    exact (Units.mulRight v).bijective
  have hτ'' := hτ' (X'.basicOpen h'') hW''W' ⟨h'', rfl⟩
  have h2 : Function.Bijective
      ((relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heq''.le).op) :=
    (relativeDifferentials (ψ ≫ f)).map_bijective_of_le _ heq''.ge
  refine bijective_smul_of_baseChange (baseChangeSec ψ θ hW''le
      (inf_le_left : X.basicOpen g₀ ⊓ f.smoothLocus ≤ X.basicOpen g₀)) hΘ'' mD ?_
  have hfun : (fun a : Γ(X', X'.basicOpen h'') => a • baseChangeSec ψ θ hW''le
      (inf_le_left : X.basicOpen g₀ ⊓ f.smoothLocus ≤ X.basicOpen g₀) (1 ⊗ₜ mD)) =
      (SecOver.equiv _ _).symm ∘
        (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heq''.le).op ∘
        (fun c : Γ(X', X'.basicOpen h'') =>
          res (inf_le_left : X'.basicOpen h'' ⊓ (ψ ≫ f).smoothLocus ≤ X'.basicOpen h'') c •
            (relativeDifferentials (ψ ≫ f)).presheaf.map
              (homOfLE (inf_le_inf_right (ψ ≫ f).smoothLocus hW''W')).op τ') ∘
        (fun a => a * res hW''W' c') := by
    funext a
    apply (SecOver.equiv _ _).injective
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply, SecOver.smul_def, hval]
    rw [Ω_map_res_smul, map_map_eq, map_mul, map_mul, mul_smul]
    simp only [res_res]
  rw [hfun]
  exact (SecOver.equiv _ _).symm.bijective.comp (h2.comp (hτ''.comp hmulu))

include hV hW hWV hW' in
/-- **Invertibility of `ω_{X/S}` from an étale two-chart neighbourhood.** Let `ψ : X' → X` be
étale on the affine `W' → W`, surjective onto `W`, with open images of basic opens, compatible with
the smooth loci, and let `ψ ≫ f` be a two-chart affine on `W'`. If `W ∩ U` is a finite union of
basic opens of `W` (after intersecting with any basic open), then `ω_{X/S}` is invertible on `W`. -/
theorem isInvertibleAt_dualizingSheaf_of_etale (hét : (ψ.appLE W W' hWW').hom.Etale)
    (hsm : ψ ⁻¹ᵁ f.smoothLocus ⊓ W' = (ψ ≫ f).smoothLocus ⊓ W')
    (hqc : ∀ g : Γ(X, W), ∃ (n : ℕ) (b : Fin n → Γ(X, W)),
      X.basicOpen g ⊓ f.smoothLocus = ⨆ i, X.basicOpen (b i))
    {u v : Γ(X', W')} (H : TwoChartAffine (ψ ≫ f) W' u v)
    (hsurj : ∀ y ∈ W, ∃ y' ∈ W', ψ y' = y)
    (hopen : ∀ h : Γ(X', W'), IsOpen (ψ '' (X'.basicOpen h : Set X')))
    {x : X} (hx : x ∈ W) : IsInvertibleAt (dualizingSheaf f) x := by
  let τ' := dualizingSheafSectionsEquiv (ψ ≫ f) W' H.dualizingGenerator
  have hτ' : ∀ (D : X'.Opens) (hD : D ≤ W'), (∃ h : Γ(X', W'), D = X'.basicOpen h) →
      Function.Bijective (fun c : Γ(X', D) =>
        res (inf_le_left : D ⊓ (ψ ≫ f).smoothLocus ≤ D) c •
          (relativeDifferentials (ψ ≫ f)).presheaf.map
            (homOfLE (inf_le_inf_right (ψ ≫ f).smoothLocus hD)).op τ') := by
    rintro D hD ⟨h, rfl⟩
    have h1 := H.bijective_dualizingGenerator h
    let E := dualizingSheafSectionsEquiv (ψ ≫ f) (X'.basicOpen h)
    have hfun : (fun c : Γ(X', X'.basicOpen h) =>
        res (inf_le_left : X'.basicOpen h ⊓ (ψ ≫ f).smoothLocus ≤ X'.basicOpen h) c •
          (relativeDifferentials (ψ ≫ f)).presheaf.map
            (homOfLE (inf_le_inf_right (ψ ≫ f).smoothLocus hD)).op τ') =
        E ∘ (fun c : Γ(X', X'.basicOpen h) =>
          c • (dualizingSheaf (ψ ≫ f)).presheaf.map (homOfLE (X'.basicOpen_le h)).op
            H.dualizingGenerator) := by
      funext c
      simp only [Function.comp_apply, E]
      rw [dualizingSheafSectionsEquiv_smul, dualizingSheafSectionsEquiv_map]
    rw [hfun]
    exact E.bijective.comp h1
  obtain ⟨t, hxt, m, hm⟩ :=
    exists_generator_of_etale f ψ hV hW hWV hW' hWW' hét hsm hqc τ' hτ' hsurj hopen hx
  refine isInvertibleAt_of_generator (dualizingSheaf f) (hW.basicOpen t)
    ((dualizingSheafSectionsEquiv f (X.basicOpen t)).symm m) (fun g => ?_) hxt
  let E := dualizingSheafSectionsEquiv f (X.basicOpen g)
  have hfun : (fun c : Γ(X, X.basicOpen g) => c • (dualizingSheaf f).presheaf.map
      (homOfLE (X.basicOpen_le g)).op ((dualizingSheafSectionsEquiv f (X.basicOpen t)).symm m)) =
      E.symm ∘ (fun c : Γ(X, X.basicOpen g) =>
        res (inf_le_left : X.basicOpen g ⊓ f.smoothLocus ≤ X.basicOpen g) c •
          (relativeDifferentials f).presheaf.map
            (homOfLE (inf_le_inf_right f.smoothLocus (X.basicOpen_le g))).op m) := by
    funext c
    apply E.injective
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply, E]
    rw [dualizingSheafSectionsEquiv_smul, dualizingSheafSectionsEquiv_map,
      AddEquiv.apply_symm_apply]
  rw [hfun]
  exact E.symm.bijective.comp (hm g)

end Descent


section Compact

variable {X : Scheme.{u}}

/-- A quasi-compact open contained in an affine open `W` is a finite union of basic opens of
`W`. -/
theorem exists_eq_iSup_basicOpen_of_isCompact {W : X.Opens} (hW : IsAffineOpen W) {K : X.Opens}
    (hK : IsCompact (K : Set X)) (hKW : K ≤ W) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, W)), K = ⨆ i, X.basicOpen (b i) := by
  let ι := {b : Γ(X, W) // X.basicOpen b ≤ K}
  have hcover : (K : Set X) ⊆ ⋃ i : ι, (X.basicOpen i.1 : Set X) := by
    intro x hx
    obtain ⟨b, hbK, hxb⟩ := hW.exists_basicOpen_le ⟨x, hx⟩ (hKW hx)
    exact Set.mem_iUnion.mpr ⟨⟨b, hbK⟩, hxb⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : ι => (X.basicOpen i.1 : Set X))
    (fun i => (X.basicOpen i.1).isOpen) hcover
  refine ⟨t.card, fun i => (t.equivFin.symm i).1.1, ?_⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨t.equivFin ⟨i, hi⟩, ?_⟩
    simpa using hxi
  · exact iSup_le fun i => (t.equivFin.symm i).1.2

/-- If `W ∩ U` is quasi-compact (`W` affine), then `D(g) ∩ U` is a finite union of basic opens of
`W` for every `g ∈ Γ(X, W)`. -/
theorem exists_basicOpen_inf_eq_iSup {W : X.Opens} (hW : IsAffineOpen W) {U : X.Opens}
    (hK : IsCompact ((W ⊓ U : X.Opens) : Set X)) (g : Γ(X, W)) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, W)), X.basicOpen g ⊓ U = ⨆ i, X.basicOpen (b i) := by
  obtain ⟨n, b, hb⟩ := exists_eq_iSup_basicOpen_of_isCompact hW hK inf_le_left
  refine ⟨n, fun i => g * b i, ?_⟩
  simp only [Scheme.basicOpen_mul]
  rw [← inf_iSup_eq, ← hb, ← inf_assoc, inf_eq_left.mpr (X.basicOpen_le g)]

end Compact

section EtaleScheme

variable {X X' S : Scheme.{u}} (f : X ⟶ S) (ψ : X' ⟶ X) [LocallyOfFinitePresentation f]
  [LocallyOfFinitePresentation (ψ ≫ f)] {V : S.Opens} (hV : IsAffineOpen V)
  {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) {W' : X'.Opens} (hW' : IsAffineOpen W')
  (hWW' : W' ≤ ψ ⁻¹ᵁ W)

include hV hW hWV hW' hWW' in
/-- **Invertibility of `ω_{X/S}` from an étale two-chart neighbourhood** (`ψ` étale). Let
`ψ : X' ⟶ X` be étale, `W' ≤ ψ⁻¹ W` affine with `ψ(W') ⊇ W`, such that `ψ ≫ f` is a two-chart
affine on `W'` and `f` is smooth at the image of every smooth point of `ψ ≫ f` in `W'`. Then
`ω_{X/S}` is invertible at every point of `W`. -/
theorem isInvertibleAt_dualizingSheaf_of_etale_of_surjective [Etale ψ] {u v : Γ(X', W')}
    (H : TwoChartAffine (ψ ≫ f) W' u v)
    (hsm : ∀ y ∈ W', y ∈ (ψ ≫ f).smoothLocus → ψ y ∈ f.smoothLocus)
    (hsurj : ∀ y ∈ W, ∃ y' ∈ W', ψ y' = y) {x : X} (hx : x ∈ W) :
    IsInvertibleAt (dualizingSheaf f) x := by
  have hét : (ψ.appLE W W' hWW').hom.Etale :=
    HasRingHomProperty.appLE @Etale ψ inferInstance ⟨W, hW⟩ ⟨W', hW'⟩ hWW'
  have hsm' : ψ ⁻¹ᵁ f.smoothLocus ⊓ W' = (ψ ≫ f).smoothLocus ⊓ W' := by
    apply le_antisymm
    · rintro y ⟨h1, h2⟩
      exact ⟨Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth ψ y) h1, h2⟩
    · rintro y ⟨h1, h2⟩
      exact ⟨hsm y h2 h1, h2⟩
  have hopen : ∀ h : Γ(X', W'), IsOpen (ψ '' (X'.basicOpen h : Set X')) := fun h =>
    ψ.isOpenMap _ (X'.basicOpen h).isOpen
  have hK : IsCompact ((W ⊓ f.smoothLocus : X.Opens) : Set X) := by
    have : ((W ⊓ f.smoothLocus : X.Opens) : Set X) =
        ψ '' ((X'.basicOpen u ⊔ X'.basicOpen v : X'.Opens) : Set X') := by
      rw [← H.smoothLocus]
      ext y
      constructor
      · rintro ⟨hyW, hyU⟩
        obtain ⟨y', hy', rfl⟩ := hsurj y hyW
        exact ⟨y', ⟨hy', Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth ψ y') hyU⟩, rfl⟩
      · rintro ⟨y', ⟨hy'W, hy'U⟩, rfl⟩
        exact ⟨hWW' hy'W, hsm y' hy'W hy'U⟩
    rw [this]
    exact ((hW'.basicOpen u).isCompact.union (hW'.basicOpen v).isCompact).image ψ.continuous
  exact isInvertibleAt_dualizingSheaf_of_etale f ψ hV hW hWV hW' hWW' hét hsm'
    (exists_basicOpen_inf_eq_iSup hW hK) H hsurj hopen hx

end EtaleScheme

end DeJongAlterations.StableModification.Omega
