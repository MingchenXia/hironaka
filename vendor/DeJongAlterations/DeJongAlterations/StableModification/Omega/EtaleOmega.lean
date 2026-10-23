import DeJongAlterations.StableModification.Omega.EtaleBaseChange

/-!
# Étale base change of `Ω¹_{X/S}`

Step 3 of `lem:sm-omega-invertible` (blueprint `sm-omega-invertible.tex`,
`lem:sm-omega-etale-base-change`). For `ψ : X' ⟶ X` and `f : X ⟶ S`:

* `pullbackDifferentials f ψ : Ω¹_{X/S} ⟶ ψ_* Ω¹_{X'/S}`, `ds ↦ d(ψ^♯ s)` (from the universal
  property of `Ω¹_{X/S}`; `app_mem_baseSubring_comp`: pullbacks of base sections are base
  sections);
* `bijective_baseChangeSec_basicOpen`: if `W ⊆ X`, `W' ⊆ X'` are affine with
  `Γ(X, W) → Γ(X', W')` étale, then for every basic open `D(b) ⊆ W` the map
  `Γ(X', W') ⊗ Γ(Ω¹_{X/S}, D(b)) → Γ(Ω¹_{X'/S}, ψ⁻¹ D(b) ∩ W')` is bijective. On the affine
  opens `D(b)`, `D(b') = ψ⁻¹ D(b) ∩ W'` the two modules are the Kähler differentials
  (`sectionsEquiv`), `Γ(X', D(b')) = Γ(X', W') ⊗ Γ(X, D(b))` (localizations), and
  `Γ(X', D(b')) ⊗ Ω_{Γ(X, D(b))} ≅ Ω_{Γ(X', D(b'))}` because `Γ(X, D(b)) → Γ(X', D(b'))` is
  formally étale (`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`);
* `bijective_baseChangeSec_iSup_of_etale`: hence (flat base change of sections,
  `bijective_baseChangeSec_iSup`) for every finite union of basic opens of `W`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct

universe u

namespace DeJongAlterations.StableModification.Omega

section SecOverNative

variable {X : Scheme.{u}} (F : X.Modules) {W Y : X.Opens} (hY : Y ≤ W)

/-- The native `Γ(X, Y)`-module structure on `SecOver F hY = Γ(F, Y)`. -/
abbrev SecOver.nativeModule : Module Γ(X, Y) (SecOver F hY) :=
  inferInstanceAs (Module Γ(X, Y) Γ(F, Y))

theorem SecOver.nativeIsScalarTower :
    letI := (res hY).toAlgebra
    letI := SecOver.nativeModule F hY
    IsScalarTower Γ(X, W) Γ(X, Y) (SecOver F hY) := by
  let := (res hY).toAlgebra
  let := SecOver.nativeModule F hY
  exact ⟨fun a c m => mul_smul (res hY a) c (show Γ(F, Y) from m)⟩

end SecOverNative

section PullbackDifferentials

variable {X X' S : Scheme.{u}} (f : X ⟶ S) (ψ : X' ⟶ X)

/-- Pullbacks of sections locally coming from the base come locally from the base. -/
theorem app_mem_baseSubring_comp {U : X.Opens} {t : Γ(X, U)} (ht : t ∈ baseSubring f U) :
    ψ.app U t ∈ baseSubring (ψ ≫ f) (ψ ⁻¹ᵁ U) := by
  intro x' hx'
  obtain ⟨σ, hσ⟩ := ht (ψ x') hx'
  refine ⟨σ, ?_⟩
  rw [Scheme.Hom.stalkMap_comp]
  exact (congrArg (ψ.stalkMap x') hσ).trans (Scheme.Hom.germ_stalkMap_apply ψ U x' hx' t)

/-- The pre-derivation `𝒪_X → ψ_* Ω¹_{X'/S}`, `s ↦ d(ψ^♯ s)`. -/
def pullbackPreDerivation :
    PreDerivation ((Scheme.Modules.pushforward ψ).obj (relativeDifferentials (ψ ≫ f))) where
  d U := ((universalDerivation (ψ ≫ f)).sec (ψ ⁻¹ᵁ U)).comp (ψ.app U).hom.toAddMonoidHom
  d_mul U s t := by
    change (universalDerivation (ψ ≫ f)).sec _ (ψ.app U (s * t)) = _
    rw [map_mul, RelDerivation.sec_mul]
    rfl
  d_map {U U'} i s := by
    change (universalDerivation (ψ ≫ f)).sec _ (ψ.app U' (X.presheaf.map i.op s)) =
      (relativeDifferentials (ψ ≫ f)).presheaf.map _
        ((universalDerivation (ψ ≫ f)).sec _ (ψ.app U s))
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply,
      RelDerivation.sec_map]
    rfl

/-- The relative derivation `𝒪_X → ψ_* Ω¹_{X'/S}`, `s ↦ d(ψ^♯ s)`. -/
def pullbackDerivation :
    RelDerivation f ((Scheme.Modules.pushforward ψ).obj (relativeDifferentials (ψ ≫ f))) :=
  (pullbackPreDerivation f ψ).toRelDerivation (fun _ _ ht =>
    (universalDerivation (ψ ≫ f)).sec_base _ (app_mem_baseSubring_comp f ψ ht))

/-- The pullback of differentials `Ω¹_{X/S} ⟶ ψ_* Ω¹_{X'/S}`. -/
def pullbackDifferentials :
    relativeDifferentials f ⟶ (Scheme.Modules.pushforward ψ).obj (relativeDifferentials (ψ ≫ f)) :=
  (homEquiv f _).symm (pullbackDerivation f ψ)

theorem pullbackDifferentials_app_d {U : X.Opens} (s : Γ(X, U)) :
    (pullbackDifferentials f ψ).app U ((universalDerivation f).d s) =
      (universalDerivation (ψ ≫ f)).d (ψ.app U s) := by
  rw [← homEquiv_apply_d, pullbackDifferentials, Equiv.apply_symm_apply]
  rfl

end PullbackDifferentials


section EtaleBasicOpen

variable {X X' S : Scheme.{u}} (f : X ⟶ S) (ψ : X' ⟶ X) {V : S.Opens} (hV : IsAffineOpen V)
  {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) {W' : X'.Opens} (hW' : IsAffineOpen W')
  (hWW' : W' ≤ ψ ⁻¹ᵁ W)

theorem basicOpen_appLE_eq (b : Γ(X, W)) :
    X'.basicOpen (ψ.appLE W W' hWW' b) = ψ ⁻¹ᵁ X.basicOpen b ⊓ W' := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, Scheme.preimage_basicOpen,
    inf_comm]

include hV hW hWV hW' in
/-- **Étale base change of `Ω¹` on basic opens.** If `Γ(X, W) → Γ(X', W')` is étale, the base
change map `Γ(X', W') ⊗ Γ(Ω¹_{X/S}, D(b)) → Γ(Ω¹_{X'/S}, ψ⁻¹ D(b) ∩ W')` is bijective. -/
theorem bijective_baseChangeSec_basicOpen (hét : (ψ.appLE W W' hWW').hom.Etale) (b : Γ(X, W)) :
    Function.Bijective
      (baseChangeSec ψ (pullbackDifferentials f ψ) hWW' (X.basicOpen_le b)) := by
  set D := X.basicOpen b
  set b' := ψ.appLE W W' hWW' b
  set D' := X'.basicOpen b'
  have hDV : D ≤ f ⁻¹ᵁ V := (X.basicOpen_le b).trans hWV
  have hD'V : D' ≤ (ψ ≫ f) ⁻¹ᵁ V := (X'.basicOpen_le _).trans (fun x hx => hWV (hWW' hx))
  have hDD' : D' ≤ ψ ⁻¹ᵁ D := (basicOpen_appLE_eq ψ hWW' b).le.trans inf_le_left
  have hD'W' : D' ≤ W' := X'.basicOpen_le _
  have heqD : D' = ψ ⁻¹ᵁ D ⊓ W' := basicOpen_appLE_eq ψ hWW' b
  -- algebras
  let := pullAlgebra ψ hWW'
  let : Algebra Γ(X, W) Γ(X, D) := (res (X.basicOpen_le b)).toAlgebra
  let : Algebra Γ(X', W') Γ(X', D') := (res hD'W').toAlgebra
  let : Algebra Γ(X, D) Γ(X', D') := (ψ.appLE D D' hDD').hom.toAlgebra
  let : Algebra Γ(X, W) Γ(X', D') := (ψ.appLE W D' (hD'W'.trans hWW')).hom.toAlgebra
  have : IsScalarTower Γ(X, W) Γ(X', W') Γ(X', D') := IsScalarTower.of_algebraMap_eq (fun a => by
    change ψ.appLE W D' _ a = res hD'W' (ψ.appLE W W' hWW' a)
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  have : IsScalarTower Γ(X, W) Γ(X, D) Γ(X', D') := IsScalarTower.of_algebraMap_eq (fun a => by
    change ψ.appLE W D' _ a = ψ.appLE D D' hDD' (res (X.basicOpen_le b) a)
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE])
  have : IsLocalization (Submonoid.powers b) Γ(X, D) := hW.isLocalization_basicOpen b
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(X', W') (Submonoid.powers b)) Γ(X', D') := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hW'.isLocalization_basicOpen b'
  have hpush : Algebra.IsPushout Γ(X, W) Γ(X', W') Γ(X, D) Γ(X', D') :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers b) Γ(X, D) Γ(X', W') Γ(X', D')
  -- Kähler differentials
  let : Algebra Γ(S, V) Γ(X, D) := (f.appLE V D hDV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X', D') := ((ψ ≫ f).appLE V D' hD'V).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, D) Γ(X', D') := IsScalarTower.of_algebraMap_eq (fun r => by
    change (ψ ≫ f).appLE V D' hD'V r = ψ.appLE D D' hDD' (f.appLE V D hDV r)
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE])
  have : Algebra.Etale Γ(X, W) Γ(X', W') := hét
  have : IsLocalization (Submonoid.powers b') Γ(X', D') := hW'.isLocalization_basicOpen b'
  have : Algebra.FormallyEtale Γ(X', W') Γ(X', D') :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers b')
  have : Algebra.FormallyEtale Γ(X, W) Γ(X', D') :=
    Algebra.FormallyEtale.comp Γ(X, W) Γ(X', W') Γ(X', D')
  have : Algebra.FormallyUnramified Γ(X, W) Γ(X, D) :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers b)
  have : Algebra.FormallyEtale Γ(X, D) Γ(X', D') :=
    Algebra.FormallyEtale.of_restrictScalars (R := Γ(X, W))
  -- the module `M = Γ(Ω¹, D)`
  let := SecOver.nativeModule (relativeDifferentials f) (X.basicOpen_le b)
  have := SecOver.nativeIsScalarTower (relativeDifferentials f) (X.basicOpen_le b)
  let e1 := Algebra.IsPushout.cancelBaseChange Γ(X, W) Γ(X', W') Γ(X, D) Γ(X', D')
    (SecOver (relativeDifferentials f) (X.basicOpen_le b))
  let eΩM : SecOver (relativeDifferentials f) (X.basicOpen_le b) ≃ₗ[Γ(X, D)]
      Ω[Γ(X, D)⁄Γ(S, V)] := (sectionsEquiv f (hW.basicOpen b) hV hDV).symm
  let e3 := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Γ(S, V) Γ(X, D) Γ(X', D')
  let e4 : Ω[Γ(X', D')⁄Γ(S, V)] ≃ₗ[Γ(X', D')] Γ(relativeDifferentials (ψ ≫ f), D') :=
    sectionsEquiv (ψ ≫ f) (hW'.basicOpen b') hV hD'V
  let e5 : Γ(relativeDifferentials (ψ ≫ f), D') →+ Γ(relativeDifferentials (ψ ≫ f), ψ ⁻¹ᵁ D ⊓ W') :=
    ((relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heqD.ge).op).hom
  have he5 : Function.Bijective e5 := (relativeDifferentials (ψ ≫ f)).map_bijective_of_le _ heqD.le
  set θ := pullbackDifferentials f ψ
  have hres : ∀ s : Γ(X, D), X'.presheaf.map (homOfLE heqD.ge).op (ψ.appLE D D' hDD' s) =
      X'.presheaf.map (homOfLE (inf_le_left : ψ ⁻¹ᵁ D ⊓ W' ≤ ψ ⁻¹ᵁ D)).op (ψ.app D s) := by
    intro s
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  -- semilinearity of `secLinear` for the native action of `Γ(X, D)`
  have hsl : ∀ (c : Γ(X, D)) (m : SecOver (relativeDifferentials f) (X.basicOpen_le b)),
      secLinear ψ θ hWW' (X.basicOpen_le b) (c • m) =
        (show SecOver (relativeDifferentials (ψ ≫ f)) (inf_le_right : ψ ⁻¹ᵁ D ⊓ W' ≤ W') from
          X'.presheaf.map (homOfLE (inf_le_left : ψ ⁻¹ᵁ D ⊓ W' ≤ ψ ⁻¹ᵁ D)).op (ψ.app D c) •
          (show Γ(relativeDifferentials (ψ ≫ f), ψ ⁻¹ᵁ D ⊓ W') from
            secLinear ψ θ hWW' (X.basicOpen_le b) m)) := by
    intro c m
    change (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE inf_le_left).op
        (secMap₀ ψ θ D (c • (show Γ(relativeDifferentials f, D) from m))) = _
    rw [secMap₀_smul, Ω_map_res_smul]
    rfl
  -- comparison with Kähler differentials
  have hC : ∀ ω : Ω[Γ(X, D)⁄Γ(S, V)],
      e5 (e4 (KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, D) Γ(X', D') ω)) =
        SecOver.equiv _ _ (secLinear ψ θ hWW' (X.basicOpen_le b) (eΩM.symm ω)) := by
    intro ω
    have hω : ω ∈ Submodule.span Γ(X, D) (Set.range (KaehlerDifferential.D Γ(S, V) Γ(X, D))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      rw [KaehlerDifferential.map_D]
      have h4 : e4 (KaehlerDifferential.D Γ(S, V) Γ(X', D') (ψ.appLE D D' hDD' s)) =
          (universalDerivation (ψ ≫ f)).d (ψ.appLE D D' hDD' s) :=
        sectionsEquiv_d (ψ ≫ f) (hW'.basicOpen b') hV hD'V _
      have hΩ : eΩM.symm (KaehlerDifferential.D Γ(S, V) Γ(X, D) s) = (universalDerivation f).d s :=
        sectionsEquiv_d f (hW.basicOpen b) hV hDV s
      change e5 (e4 (KaehlerDifferential.D Γ(S, V) Γ(X', D') (ψ.appLE D D' hDD' s))) = _
      rw [h4, hΩ]
      change (relativeDifferentials (ψ ≫ f)).presheaf.map _ ((universalDerivation (ψ ≫ f)).d _) =
        (relativeDifferentials (ψ ≫ f)).presheaf.map _ (θ.app D ((universalDerivation f).d s))
      rw [pullbackDifferentials_app_d, ← RelDerivation.d_map, ← RelDerivation.d_map, hres]
    | zero =>
      simp only [map_zero]
    | add a c _ _ ha hc =>
      rw [map_add, map_add, map_add, ha, hc, map_add, map_add, map_add]
    | smul c a _ ha =>
      have h1 : e4 (KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, D) Γ(X', D') (c • a)) =
          ψ.appLE D D' hDD' c •
            e4 (KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, D) Γ(X', D') a) := by
        rw [LinearMap.map_smul, ← algebraMap_smul Γ(X', D'), LinearEquiv.map_smul]
        rfl
      rw [h1]
      change (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heqD.ge).op
        (ψ.appLE D D' hDD' c • e4 (KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, D) Γ(X', D') a)) = _
      rw [Ω_map_res_smul, hres, LinearEquiv.map_smul, hsl]
      change _ • e5 (e4 _) = _
      rw [ha]
      rfl
  -- the composite
  let Φ : Γ(X', W') ⊗[Γ(X, W)] SecOver (relativeDifferentials f) (X.basicOpen_le b) →+
      Γ(relativeDifferentials (ψ ≫ f), ψ ⁻¹ᵁ D ⊓ W') :=
    e5.comp ((e4.toAddEquiv.toAddMonoidHom.comp e3.toAddEquiv.toAddMonoidHom).comp
      ((LinearEquiv.lTensor Γ(X', D') eΩM).toAddEquiv.toAddMonoidHom.comp
        e1.symm.toAddEquiv.toAddMonoidHom))
  have hΦ : Function.Bijective Φ :=
    he5.comp ((e4.bijective.comp e3.bijective).comp
      ((LinearEquiv.lTensor Γ(X', D') eΩM).bijective.comp e1.symm.bijective))
  have hΘ : ∀ t, SecOver.equiv _ _ (baseChangeSec ψ θ hWW' (X.basicOpen_le b) t) = Φ t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul a' m =>
      have h1 : e1.symm (a' ⊗ₜ m) = algebraMap Γ(X', W') Γ(X', D') a' ⊗ₜ m :=
        Algebra.IsPushout.cancelBaseChange_symm_tmul _ _ _ _ _ a' m
      change _ = e5 (e4 (e3 ((LinearEquiv.lTensor Γ(X', D') eΩM) (e1.symm (a' ⊗ₜ m)))))
      rw [h1, LinearEquiv.lTensor_tmul, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
        KaehlerDifferential.mapBaseChange_tmul, LinearEquiv.map_smul]
      change _ = (relativeDifferentials (ψ ≫ f)).presheaf.map (homOfLE heqD.ge).op
        (algebraMap Γ(X', W') Γ(X', D') a' • e4 (KaehlerDifferential.map Γ(S, V) Γ(S, V) Γ(X, D)
          Γ(X', D') (eΩM m)))
      rw [Ω_map_res_smul]
      change _ = _ • e5 (e4 _)
      rw [hC, LinearEquiv.symm_apply_apply]
      change res (inf_le_right : ψ ⁻¹ᵁ D ⊓ W' ≤ W') a' •
          SecOver.equiv _ _ (secLinear ψ θ hWW' (X.basicOpen_le b) m) =
        res heqD.ge (res hD'W' a') • SecOver.equiv _ _ (secLinear ψ θ hWW' (X.basicOpen_le b) m)
      rw [res_res]
  have : (fun t => SecOver.equiv _ _ (baseChangeSec ψ θ hWW' (X.basicOpen_le b) t)) = Φ :=
    funext hΘ
  have hcomp : Function.Bijective
      ((SecOver.equiv _ _) ∘ (baseChangeSec ψ θ hWW' (X.basicOpen_le b))) := by
    change Function.Bijective
      (fun t => SecOver.equiv _ _ (baseChangeSec ψ θ hWW' (X.basicOpen_le b) t))
    rw [this]
    exact hΦ
  exact (Function.Bijective.of_comp_iff' (SecOver.equiv _ _).bijective _).mp hcomp

end EtaleBasicOpen


variable {X X' S : Scheme.{u}} (f : X ⟶ S) (ψ : X' ⟶ X) {V : S.Opens} (hV : IsAffineOpen V)
  {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) {W' : X'.Opens} (hW' : IsAffineOpen W')
  (hWW' : W' ≤ ψ ⁻¹ᵁ W)

include hV hW hWV hW' in
/-- **Étale base change of the sections of `Ω¹` over finite unions of basic opens.** -/
theorem bijective_baseChangeSec_iSup_of_etale (hét : (ψ.appLE W W' hWW').hom.Etale) {n : ℕ}
    (b : Fin n → Γ(X, W)) :
    Function.Bijective (baseChangeSec ψ (pullbackDifferentials f ψ) hWW'
      (iSup_le fun i => X.basicOpen_le (b i))) := by
  let := pullAlgebra ψ hWW'
  have : Algebra.Etale Γ(X, W) Γ(X', W') := hét
  exact bijective_baseChangeSec_iSup ψ _ hWW' inferInstance
    (bijective_baseChangeSec_basicOpen f ψ hV hW hWV hW' hWW' hét) b

end DeJongAlterations.StableModification.Omega
