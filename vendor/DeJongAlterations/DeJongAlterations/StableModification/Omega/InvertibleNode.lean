import DeJongAlterations.StableModification.Omega.NodeSingular

/-!
# `ω_{X/S}` is invertible on node charts

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2
(`semi-stable.tex`, T:1691–1712) uses that the relative dualizing sheaf of a nodal curve is
invertible. Here `ω_{X/S} = j_*(Ω¹_{X/S}|_U)` (`dualizingSheaf`, `U` the smooth locus), and this
file proves the first step of `lem:sm-omega-invertible` (blueprint `sm-omega-invertible.tex`): on
a node chart `W` (`NodeChart`: `Γ(X, W) ≅ Γ(S, V)[u,v]/(uv - h)`, `h` a non-zero-divisor),
`ω_{X/S}|_W ≅ 𝒪_W`.

`NodeChart.exists_dualizing_generator` (lane OM1) gives, for each basic open `D(g) ⊆ W`, some
generator of `Γ(D(g), ω)`. Two further facts turn this into an isomorphism of sheaves:

* the generators are compatible: a section `σ` with `u σ = du` on `D(u)` and `v σ = -dv` on
  `D(v)` is unique (`eq_of_mul_eq_two`), so the restriction of the generator `du/u` over `W`
  to `D(g)` is the generator there (`TwoChartData.bijective_of_eqns`,
  `NodeChart.bijective_generator_restrict`);
* a morphism `𝒪 ⟶ M|_{Spec Γ(Y, W)}`, `1 ↦ τ`, which is bijective on the sections over every
  basic open is an isomorphism (`isIso_generatorHom`, via `TopCat.Sheaf.isIso_iff_isIso_basis`);
  hence `isInvertibleAt_of_generator`.

Main results: `isInvertibleAt_of_generator`, `dualizingSheafSectionsEquiv_map`,
`NodeChart.isInvertibleAt_dualizingSheaf`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

section Generator

variable {Y : Scheme.{u}} (M : Y.Modules) {W : Y.Opens} (hW : IsAffineOpen W)

/-- A section over `W`, as a global section of `M|_{Spec Γ(Y, W)}`. -/
noncomputable def topSection (τ : Γ(M, W)) : Γ(M.restrict hW.fromSpec, ⊤) :=
  (M.restrictAppIso hW.fromSpec ⊤).inv (M.presheaf.map (homOfLE (fromSpec_image_top_le hW)).op τ)

/-- The compatible family of restrictions of `topSection`. -/
noncomputable def restrictSections (τ : Γ(M, W)) : (M.restrict hW.fromSpec).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (M.restrict hW.fromSpec).presheaf.map (homOfLE le_top).op (topSection M hW τ))
    (by
      intro U V i
      change (M.restrict hW.fromSpec).presheaf.map i
        ((M.restrict hW.fromSpec).presheaf.map _ _) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

/-- The morphism `𝒪 ⟶ M|_{Spec Γ(Y, W)}`, `1 ↦ τ`. -/
noncomputable def generatorHom (τ : Γ(M, W)) :
    (SheafOfModules.unit (Spec Γ(Y, W)).ringCatSheaf : (Spec Γ(Y, W)).Modules) ⟶
      M.restrict hW.fromSpec :=
  (M.restrict hW.fromSpec).unitHomEquiv.symm (restrictSections M hW τ)

theorem generatorHom_app (τ : Γ(M, W)) (U : (Spec Γ(Y, W)).Opens) (c : Γ(Spec Γ(Y, W), U)) :
    Scheme.Modules.Hom.app (generatorHom M hW τ) U c =
      c • (M.restrict hW.fromSpec).presheaf.map (homOfLE le_top).op (topSection M hW τ) := by
  rfl

end Generator

section Generator2
variable {Y : Scheme.{u}} (M : Y.Modules) {W : Y.Opens} (hW : IsAffineOpen W)

theorem generatorHom_app_eq (τ : Γ(M, W)) (U : (Spec Γ(Y, W)).Opens) (c : Γ(Spec Γ(Y, W), U)) :
    Scheme.Modules.Hom.app (generatorHom M hW τ) U c =
      (hW.fromSpec.appIso U).inv c • M.presheaf.map (homOfLE ((hW.fromSpec.image_mono le_top).trans
        (fromSpec_image_top_le hW))).op τ := by
  rw [generatorHom_app]
  change (M.restrictAppIso hW.fromSpec U).hom (c • _) = _
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  congr 1
  change M.presheaf.map _ (M.presheaf.map _ τ) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem isIso_generatorHom (τ : Γ(M, W))
    (hτ : ∀ g : Γ(Y, W), Function.Bijective (fun c : Γ(Y, Y.basicOpen g) =>
      c • M.presheaf.map (homOfLE (Y.basicOpen_le g)).op τ)) :
    IsIso (generatorHom M hW τ) := by
  let O : (Spec Γ(Y, W)).Modules := SheafOfModules.unit (Spec Γ(Y, W)).ringCatSheaf
  let N : (Spec Γ(Y, W)).Modules := M.restrict hW.fromSpec
  let φ : O ⟶ N := generatorHom M hW τ
  have hbij : ∀ g : Γ(Y, W), Function.Bijective
      (Scheme.Modules.Hom.app φ (PrimeSpectrum.basicOpen g)) := by
    intro g
    have aux : ∀ (V : Y.Opens) (hV : V ≤ W), V = Y.basicOpen g →
        Function.Bijective (fun c : Γ(Y, V) => c • M.presheaf.map (homOfLE hV).op τ) := by
      rintro V hV rfl
      exact hτ g
    have h1 := aux _ ((hW.fromSpec.image_mono le_top).trans (fromSpec_image_top_le hW))
      (hW.fromSpec_image_basicOpen g)
    have h2 : Function.Bijective (hW.fromSpec.appIso (PrimeSpectrum.basicOpen g)).inv :=
      ConcreteCategory.bijective_of_isIso _
    have : (Scheme.Modules.Hom.app φ (PrimeSpectrum.basicOpen g) : _ → _) =
        (fun c => c • M.presheaf.map (homOfLE ((hW.fromSpec.image_mono le_top).trans
          (fromSpec_image_top_le hW))).op τ) ∘
            (hW.fromSpec.appIso (PrimeSpectrum.basicOpen g)).inv := by
      funext c
      exact generatorHom_app_eq M hW τ _ c
    rw [this]
    exact h1.comp h2
  let F : TopCat.Sheaf Ab (Spec Γ(Y, W)) := ⟨O.presheaf, O.isSheaf⟩
  let G : TopCat.Sheaf Ab (Spec Γ(Y, W)) := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ObjectProperty.homMk (Scheme.Modules.Hom.mapPresheaf φ)
  have hψ : IsIso ψ := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := PrimeSpectrum.basicOpen)
      PrimeSpectrum.isBasis_basic_opens (fun g => ?_)
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hbij g
  have h3 : IsIso ψ.hom := ((sheafToPresheaf _ _).mapIso (@asIso _ _ _ _ ψ hψ)).isIso_hom
  have : IsIso ((Scheme.Modules.toPresheaf _).map φ) := h3
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf _)

include hW in
/-- **A generator on all basic opens gives invertibility.** If `τ ∈ Γ(M, W)` (`W` affine) is such
that, for every `g ∈ Γ(Y, W)`, `c ↦ c τ|_{D(g)}` is a bijection `Γ(Y, D(g)) → Γ(M, D(g))`, then
`M` is invertible at every point of `W`. -/
theorem isInvertibleAt_of_generator (τ : Γ(M, W))
    (hτ : ∀ g : Γ(Y, W), Function.Bijective (fun c : Γ(Y, Y.basicOpen g) =>
      c • M.presheaf.map (homOfLE (Y.basicOpen_le g)).op τ)) {y : Y} (hy : y ∈ W) :
    IsInvertibleAt M y := by
  have := isIso_generatorHom M hW τ hτ
  exact ⟨W, hW, hy, ⟨(asIso (generatorHom M hW τ)).symm⟩⟩

end Generator2

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Restrict
variable [LocallyOfFinitePresentation f]

/-- The identification `Γ(ω, W) ≃ Γ(Ω¹, W ∩ U)` is compatible with restriction. -/
theorem dualizingSheafSectionsEquiv_map {W W' : X.Opens} (h : W' ≤ W)
    (s : Γ(dualizingSheaf f, W)) :
    dualizingSheafSectionsEquiv f W' ((dualizingSheaf f).presheaf.map (homOfLE h).op s) =
      (relativeDifferentials f).presheaf.map (homOfLE (inf_le_inf_right _ h)).op
        (dualizingSheafSectionsEquiv f W s) := by
  let s' : Γ(relativeDifferentials f, f.smoothLocus.ι ''ᵁ (f.smoothLocus.ι ⁻¹ᵁ W)) := s
  change (relativeDifferentials f).presheaf.map _ ((relativeDifferentials f).presheaf.map
      (homOfLE (f.smoothLocus.ι.image_mono (f.smoothLocus.ι.preimage_mono h))).op s') =
    (relativeDifferentials f).presheaf.map _ ((relativeDifferentials f).presheaf.map _ s')
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

end Restrict

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A section over `D(u₀) ∪ D(v₀)` is determined by `u₀ σ` on `D(u₀)` and `v₀ σ` on `D(v₀)`. -/
theorem eq_of_mul_eq_two {N : X.Modules} {W₀ : X.Opens} (u₀ v₀ : Γ(X, W₀))
    {σ₁ σ₂ : Γ(N, X.basicOpen u₀ ⊔ X.basicOpen v₀)}
    (hu : res (X.basicOpen_le u₀) u₀ • N.presheaf.map (homOfLE le_sup_left).op σ₁ =
      res (X.basicOpen_le u₀) u₀ • N.presheaf.map (homOfLE le_sup_left).op σ₂)
    (hv : res (X.basicOpen_le v₀) v₀ • N.presheaf.map (homOfLE le_sup_right).op σ₁ =
      res (X.basicOpen_le v₀) v₀ • N.presheaf.map (homOfLE le_sup_right).op σ₂) :
    σ₁ = σ₂ := by
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  have huU : IsUnit (res (X.basicOpen_le u₀) u₀) := X.toRingedSpace.isUnit_res_basicOpen u₀
  have hvV : IsUnit (res (X.basicOpen_le v₀) v₀) := X.toRingedSpace.isUnit_res_basicOpen v₀
  exact F.eq_of_locally_eq₂ (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl _ _
    (huU.smul_left_cancel.mp hu) (hvV.smul_left_cancel.mp hv)

variable (f) in
/-- The hypotheses of the two-chart computation (`TwoChartData` of lane OM1), with the condition
that `u₀ v₀` comes from the base replaced by its consequence `d(u₀ v₀) = 0` on every open of `W₀`
(this also covers étale charts of the node, where `u₀ v₀` comes from an étale `𝒪_S`-algebra). -/
structure TwoChartRel (W₀ : X.Opens) (u₀ v₀ : Γ(X, W₀)) : Prop where
  isAffineOpen : IsAffineOpen W₀
  rel : ∀ (U : X.Opens) (hU : U ≤ W₀), (universalDerivation f).sec U (res hU (u₀ * v₀)) = 0
  equalizer : NodeEqualizerData u₀ v₀
  kaehler_u : Function.Bijective (fun c : Γ(X, X.basicOpen u₀) =>
    c • (universalDerivation f).sec _ (res (X.basicOpen_le u₀) u₀))
  kaehler_v : Function.Bijective (fun c : Γ(X, X.basicOpen v₀) =>
    c • (universalDerivation f).sec _ (res (X.basicOpen_le v₀) v₀))
  kaehler_uv : Function.Bijective (fun c : Γ(X, X.basicOpen (u₀ * v₀)) =>
    c • (universalDerivation f).sec _ (res (X.basicOpen_le (u₀ * v₀)) u₀))

/-- `TwoChartData` (lane OM1) gives `TwoChartRel`. -/
theorem TwoChartData.toTwoChartRel {V : S.Opens} {W₀ : X.Opens} {u₀ v₀ : Γ(X, W₀)}
    (H : TwoChartData f V W₀ u₀ v₀) : TwoChartRel f W₀ u₀ v₀ where
  isAffineOpen := H.isAffineOpen
  rel U hU := by
    obtain ⟨r, hr⟩ := H.base
    rw [hr, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    exact (universalDerivation f).sec_appLE _ r
  equalizer := H.equalizer
  kaehler_u := H.kaehler_u
  kaehler_v := H.kaehler_v
  kaehler_uv := H.kaehler_uv

namespace TwoChartRel

variable {W₀ : X.Opens} {u₀ v₀ : Γ(X, W₀)} (H : TwoChartRel f W₀ u₀ v₀)
include H

/-- **The two-chart computation** (`TwoChartData.exists_bijective` of lane OM1, with the
relation `d(u₀ v₀) = 0`). There is a section `σ` of `Ω¹_{X/S}` over `D(u₀) ∪ D(v₀)` with
`u₀ σ = du₀` on `D(u₀)` and `v₀ σ = -dv₀` on `D(v₀)`, and `c ↦ c σ` is a bijection from
`Γ(X, W₀)` onto the sections of `Ω¹_{X/S}` over `D(u₀) ∪ D(v₀)`. -/
theorem exists_bijective :
    ∃ σ : Γ(relativeDifferentials f, X.basicOpen u₀ ⊔ X.basicOpen v₀),
      res (X.basicOpen_le u₀) u₀ • (relativeDifferentials f).presheaf.map
          (homOfLE le_sup_left).op σ =
        (universalDerivation f).sec _ (res (X.basicOpen_le u₀) u₀) ∧
      res (X.basicOpen_le v₀) v₀ • (relativeDifferentials f).presheaf.map
          (homOfLE le_sup_right).op σ =
        -(universalDerivation f).sec _ (res (X.basicOpen_le v₀) v₀) ∧
      Function.Bijective (fun c : Γ(X, W₀) =>
        res (sup_le (X.basicOpen_le u₀) (X.basicOpen_le v₀)) c • σ) := by
  set Du := X.basicOpen u₀
  set Dv := X.basicOpen v₀
  set hu := X.basicOpen_le u₀
  set hv := X.basicOpen_le v₀
  set uU := res hu u₀
  set vV := res hv v₀
  have huU : IsUnit uU := X.toRingedSpace.isUnit_res_basicOpen u₀
  have hvV : IsUnit vV := X.toRingedSpace.isUnit_res_basicOpen v₀
  -- the relation `u dv + v du = 0` on any open `U ≤ W₀`
  have hrel : ∀ {U : X.Opens} (hU : U ≤ W₀),
      res hU u₀ • (universalDerivation f).sec U (res hU v₀) +
        res hU v₀ • (universalDerivation f).sec U (res hU u₀) = 0 := by
    intro U hU
    rw [← RelDerivation.sec_mul, ← map_mul]
    exact H.rel U hU
  -- the two local generators agree on the overlap
  set σu : Γ(relativeDifferentials f, Du) := huU.unit⁻¹.val • (universalDerivation f).sec Du uU
  set σv : Γ(relativeDifferentials f, Dv) := -(hvV.unit⁻¹.val • (universalDerivation f).sec Dv vV)
  have hglue : (relativeDifferentials f).presheaf.map (homOfLE inf_le_left : Du ⊓ Dv ⟶ Du).op σu =
      (relativeDifferentials f).presheaf.map (homOfLE inf_le_right : Du ⊓ Dv ⟶ Dv).op σv := by
    have hI : Du ⊓ Dv ≤ W₀ := inf_le_left.trans hu
    set a := res (inf_le_left : Du ⊓ Dv ≤ Du) huU.unit⁻¹.val
    set b := res (inf_le_right : Du ⊓ Dv ≤ Dv) hvV.unit⁻¹.val
    have ha : a * res hI u₀ = 1 := by
      rw [← res_res hu inf_le_left, ← map_mul, IsUnit.val_inv_mul, map_one]
    have hb : b * res hI v₀ = 1 := by
      rw [← res_res hv inf_le_right, ← map_mul, IsUnit.val_inv_mul, map_one]
    simp only [σu, σv, map_neg, Ω_map_res_smul, uU, vV, ← sec_res f, res_res]
    have := hrel hI
    rw [eq_neg_iff_add_eq_zero]
    calc a • (universalDerivation f).sec _ (res hI u₀) +
          b • (universalDerivation f).sec _ (res hI v₀)
        = (a * b) • (res hI u₀ • (universalDerivation f).sec _ (res hI v₀) +
            res hI v₀ • (universalDerivation f).sec _ (res hI u₀)) := by
          rw [smul_add, smul_smul, smul_smul]
          rw [show a * b * res hI u₀ = b by rw [mul_right_comm, ha, one_mul],
            show a * b * res hI v₀ = a by rw [mul_assoc, hb, mul_one]]
          abel
      _ = 0 := by rw [this, smul_zero]
  obtain ⟨σ, hσu, hσv⟩ := (relativeDifferentials f).exists_glue₂ σu σv hglue
  refine ⟨σ, ?_, ?_, ?_⟩
  · rw [hσu, smul_smul, IsUnit.mul_val_inv, one_smul]
  · rw [hσv, smul_neg, smul_smul, IsUnit.mul_val_inv, one_smul]
  have hUW : Du ⊔ Dv ≤ W₀ := sup_le hu hv
  have hW₀ := H.isAffineOpen
  -- restricting `c • σ` to the two charts
  have hresU : ∀ c : Γ(X, W₀), (relativeDifferentials f).presheaf.map
      (homOfLE le_sup_left : Du ⟶ Du ⊔ Dv).op (res hUW c • σ) = res hu c • σu := by
    intro c
    rw [Ω_map_res_smul, hσu, res_res]
  have hresV : ∀ c : Γ(X, W₀), (relativeDifferentials f).presheaf.map
      (homOfLE le_sup_right : Dv ⟶ Du ⊔ Dv).op (res hUW c • σ) = res hv c • σv := by
    intro c
    rw [Ω_map_res_smul, hσv, res_res]
  have hinj_u : Function.Injective (res hu) := by
    let := (X.presheaf.map (homOfLE hu).op).hom.toAlgebra
    have := hW₀.isLocalization_basicOpen u₀
    exact IsLocalization.injective (M := Submonoid.powers u₀) Γ(X, Du)
      (Submonoid.powers_le.mpr H.equalizer.u_mem)
  let F : TopCat.Sheaf Ab X := ⟨(relativeDifferentials f).presheaf,
    (relativeDifferentials f).isSheaf⟩
  constructor
  · intro c c' hcc'
    have h1 := congrArg ((relativeDifferentials f).presheaf.map
      (homOfLE le_sup_left : Du ⟶ Du ⊔ Dv).op) hcc'
    simp only [hresU, σu, smul_smul] at h1
    have h2 := H.kaehler_u.1 h1
    apply hinj_u
    have := congrArg (· * uU) h2
    simp only [mul_assoc, IsUnit.val_inv_mul, mul_one] at this
    exact this
  · intro τ
    obtain ⟨a, ha⟩ := H.kaehler_u.2 ((relativeDifferentials f).presheaf.map
      (homOfLE le_sup_left : Du ⟶ Du ⊔ Dv).op τ)
    obtain ⟨b, hb⟩ := H.kaehler_v.2 ((relativeDifferentials f).presheaf.map
      (homOfLE le_sup_right : Dv ⟶ Du ⊔ Dv).op τ)
    simp only at ha hb
    set Duv := X.basicOpen (u₀ * v₀)
    have hDuv : Duv = Du ⊓ Dv := X.basicOpen_mul u₀ v₀
    have huv_u : Duv ≤ Du := hDuv.le.trans inf_le_left
    have huv_v : Duv ≤ Dv := hDuv.le.trans inf_le_right
    have huv : Duv ≤ W₀ := X.basicOpen_le _
    -- compare on `D(u₀v₀)`
    have hτ : (res huv_u a) • (universalDerivation f).sec _ (res huv u₀) =
        (res huv_v b) • (universalDerivation f).sec _ (res huv v₀) := by
      have e1 := congrArg ((relativeDifferentials f).presheaf.map (homOfLE huv_u).op) ha
      have e2 := congrArg ((relativeDifferentials f).presheaf.map (homOfLE huv_v).op) hb
      rw [map_map_eq, Ω_map_res_smul, ← sec_res f, res_res] at e1 e2
      rw [e1, e2]
    have hrel' := hrel huv
    have hkey : (res huv_u a * res huv u₀) • (universalDerivation f).sec _ (res huv u₀) =
        (-(res huv_v b * res huv v₀)) • (universalDerivation f).sec _ (res huv u₀) := by
      rw [mul_comm, ← smul_smul, hτ, smul_smul, mul_comm, ← smul_smul,
        eq_neg_of_add_eq_zero_left hrel', smul_neg, smul_smul, neg_smul, mul_comm]
    have hab := H.kaehler_uv.1 hkey
    -- the equalizer gives `c`
    let := (X.presheaf.map (homOfLE hu).op).hom.toAlgebra
    let := (X.presheaf.map (homOfLE hv).op).hom.toAlgebra
    let := (X.presheaf.map (homOfLE huv).op).hom.toAlgebra
    have := hW₀.isLocalization_basicOpen u₀
    have := hW₀.isLocalization_basicOpen v₀
    have := hW₀.isLocalization_basicOpen (u₀ * v₀)
    obtain ⟨c, hcu, hcv⟩ := H.equalizer.exists_eq (Au := Γ(X, Du)) (Av := Γ(X, Dv))
      (Auv := Γ(X, Duv)) (res huv_u) (res huv_v)
      (RingHom.ext fun x => res_res hu huv_u x) (RingHom.ext fun x => res_res hv huv_v x)
      (a * uU) (-(b * vV)) (by
        rw [map_mul, map_neg, map_mul, res_res, res_res]
        exact hab)
    refine ⟨c, ?_⟩
    simp only
    apply F.eq_of_locally_eq₂ (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl
    · change (relativeDifferentials f).presheaf.map _ (res hUW c • σ) =
        (relativeDifferentials f).presheaf.map _ τ
      rw [hresU, ← ha]
      change res hu c • σu = _
      rw [show res hu c = a * uU from hcu, mul_smul, smul_smul uU, IsUnit.mul_val_inv,
        one_smul]
    · change (relativeDifferentials f).presheaf.map _ (res hUW c • σ) =
        (relativeDifferentials f).presheaf.map _ τ
      rw [hresV, ← hb]
      change res hv c • σv = _
      rw [show res hv c = -(b * vV) from hcv, smul_neg, neg_smul, neg_neg, mul_smul,
        smul_smul vV, IsUnit.mul_val_inv, one_smul]

/-- **Every solution of the chart equations is a generator.** If `σ` satisfies `u₀ σ = du₀` on
`D(u₀)` and `v₀ σ = -dv₀` on `D(v₀)`, then `c ↦ c σ` is a bijection from `Γ(X, W₀)` onto the
sections of `Ω¹_{X/S}` over `D(u₀) ∪ D(v₀)`. -/
theorem bijective_of_eqns {σ : Γ(relativeDifferentials f, X.basicOpen u₀ ⊔ X.basicOpen v₀)}
    (hu : res (X.basicOpen_le u₀) u₀ • (relativeDifferentials f).presheaf.map
        (homOfLE le_sup_left).op σ =
      (universalDerivation f).sec _ (res (X.basicOpen_le u₀) u₀))
    (hv : res (X.basicOpen_le v₀) v₀ • (relativeDifferentials f).presheaf.map
        (homOfLE le_sup_right).op σ =
      -(universalDerivation f).sec _ (res (X.basicOpen_le v₀) v₀)) :
    Function.Bijective (fun c : Γ(X, W₀) =>
      res (sup_le (X.basicOpen_le u₀) (X.basicOpen_le v₀)) c • σ) := by
  obtain ⟨σ', hu', hv', hbij⟩ := H.exists_bijective
  have : σ = σ' := eq_of_mul_eq_two u₀ v₀ (hu.trans hu'.symm) (hv.trans hv'.symm)
  subst this
  exact hbij

end TwoChartRel

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Points of a basic open of an affine open, in terms of prime ideals. -/
theorem mem_basicOpen_iff_notMem {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W) {y : Y}
    (hy : y ∈ W) (g : Γ(Y, W)) :
    y ∈ Y.basicOpen g ↔ g ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have key : hW.fromSpec (hW.primeIdealOf ⟨y, hy⟩) = y := hW.fromSpec_primeIdealOf ⟨y, hy⟩
  conv_lhs => rw [← key]
  change hW.primeIdealOf ⟨y, hy⟩ ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen g ↔ _
  rw [hW.fromSpec_preimage_basicOpen]
  rfl

theorem basicOpen_one_eq {W : X.Opens} : X.basicOpen (1 : Γ(X, W)) = W :=
  X.basicOpen_of_isUnit isUnit_one

variable (f) in
/-- An affine open `W ≤ f⁻¹ V` with two functions `u, v` behaving like the coordinates of a
node chart: `uv` comes from the base, `u, v` satisfy the equalizer condition, `Ω¹_{X/S}` is free
on `du` (resp. `dv`) on every affine localization of `W` in which `u` (resp. `v`) is a unit, and
`D(u) ∪ D(v)` is the smooth locus in `W`. Node charts and étale node charts are examples. -/
structure TwoChartAffine [LocallyOfFinitePresentation f] (W : X.Opens) (u v : Γ(X, W)) :
    Prop where
  isAffineOpen : IsAffineOpen W
  rel : ∀ (U : X.Opens) (hU : U ≤ W), (universalDerivation f).sec U (res hU (u * v)) = 0
  equalizer : NodeEqualizerData u v
  kaehler : ∀ (W' : X.Opens) (_ : IsAffineOpen W') (hle : W' ≤ W) (M : Submonoid Γ(X, W)),
    (letI := (res hle).toAlgebra; IsLocalization M Γ(X, W')) → ∀ t : Γ(X, W), (t = u ∨ t = v) →
      IsUnit (res hle t) → Function.Bijective (fun c : Γ(X, W') =>
        c • (universalDerivation f).sec W' (res hle t))
  smoothLocus : W ⊓ f.smoothLocus = X.basicOpen u ⊔ X.basicOpen v

namespace TwoChartAffine

variable [LocallyOfFinitePresentation f] {W : X.Opens} {u v : Γ(X, W)}
  (H : TwoChartAffine f W u v)

theorem basicOpen_res_le (g t : Γ(X, W)) :
    X.basicOpen (res (X.basicOpen_le g) t) ≤ X.basicOpen (res (X.basicOpen_le 1) t) := by
  rw [Scheme.basicOpen_res, Scheme.basicOpen_res, basicOpen_one_eq (W := W)]
  exact inf_le_inf_right _ (X.basicOpen_le g)

theorem sup_basicOpen_res_le (g : Γ(X, W)) :
    X.basicOpen (res (X.basicOpen_le g) u) ⊔ X.basicOpen (res (X.basicOpen_le g) v) ≤
      X.basicOpen (res (X.basicOpen_le 1) u) ⊔ X.basicOpen (res (X.basicOpen_le 1) v) :=
  sup_le_sup (basicOpen_res_le g u) (basicOpen_res_le g v)

include H in
/-- **Every basic open of a two-chart affine satisfies the two-chart hypotheses.** -/
theorem twoChartData (g : Γ(X, W)) :
    TwoChartRel f (X.basicOpen g) (res (X.basicOpen_le g) u) (res (X.basicOpen_le g) v) := by
  have hW := H.isAffineOpen
  set hg := X.basicOpen_le g
  have hbo : ∀ t : Γ(X, W), X.basicOpen (res hg t) ≤ X.basicOpen t := fun t =>
    (Scheme.basicOpen_res X t (homOfLE hg).op).le.trans inf_le_right
  have hk : ∀ t : Γ(X, W), (t = u ∨ t = v) →
      Function.Bijective (fun c : Γ(X, X.basicOpen (res hg t)) =>
        c • (universalDerivation f).sec _ (res (X.basicOpen_le (res hg t)) (res hg t))) := by
    intro t ht
    have hle := (X.basicOpen_le (res hg t)).trans hg
    have := H.kaehler _ ((hW.basicOpen g).basicOpen (res hg t)) hle
      (Submonoid.powers (g * t)) (NodeChart.isLocalization_basicOpen_res hW g t) t ht
      (isUnit_map_of_le_basicOpen _ (hbo t) hle)
    simpa only [res_res] using this
  refine ⟨hW.basicOpen g, ?_, ?_, hk u (Or.inl rfl), hk v (Or.inr rfl), ?_⟩
  · intro U hU
    rw [← map_mul, res_res]
    exact H.rel U (hU.trans hg)
  · let := (res hg).toAlgebra
    have := hW.isLocalization_basicOpen g
    exact H.equalizer.isLocalization (Submonoid.powers g)
  · have e : res hg u * res hg v = res hg (u * v) := (map_mul _ _ _).symm
    rw [e]
    have hle := (X.basicOpen_le (res hg (u * v))).trans hg
    have hu : X.basicOpen (res hg (u * v)) ≤ X.basicOpen u :=
      (Scheme.basicOpen_res X _ (homOfLE hg).op).le.trans
        (inf_le_right.trans (X.basicOpen_mul u v).le |>.trans inf_le_left)
    have := H.kaehler _ ((hW.basicOpen g).basicOpen (res hg (u * v))) hle
      (Submonoid.powers (g * (u * v))) (NodeChart.isLocalization_basicOpen_res hW g _) u
      (Or.inl rfl) (isUnit_map_of_le_basicOpen _ hu hle)
    simpa only [res_res] using this

/-- The generator `du/u = -dv/v` of `Ω¹_{X/S}` over `D(u) ∪ D(v)`. -/
noncomputable def generator :
    Γ(relativeDifferentials f, X.basicOpen (res (X.basicOpen_le 1) u) ⊔
      X.basicOpen (res (X.basicOpen_le 1) v)) :=
  Classical.choose (H.twoChartData 1).exists_bijective

theorem generator_spec :
    res (X.basicOpen_le (res (X.basicOpen_le 1) u)) (res (X.basicOpen_le 1) u) •
        (relativeDifferentials f).presheaf.map (homOfLE le_sup_left).op H.generator =
      (universalDerivation f).sec _
        (res (X.basicOpen_le (res (X.basicOpen_le 1) u)) (res (X.basicOpen_le 1) u)) ∧
    res (X.basicOpen_le (res (X.basicOpen_le 1) v)) (res (X.basicOpen_le 1) v) •
        (relativeDifferentials f).presheaf.map (homOfLE le_sup_right).op H.generator =
      -(universalDerivation f).sec _
        (res (X.basicOpen_le (res (X.basicOpen_le 1) v)) (res (X.basicOpen_le 1) v)) :=
  ⟨(Classical.choose_spec (H.twoChartData 1).exists_bijective).1,
    (Classical.choose_spec (H.twoChartData 1).exists_bijective).2.1⟩

/-- **Compatibility of the generators.** The restriction of `generator` to the chart of `D(g)`
satisfies the chart equations there, hence (`TwoChartRel.bijective_of_eqns`) generates. -/
theorem bijective_generator_restrict (g : Γ(X, W)) :
    Function.Bijective (fun c : Γ(X, X.basicOpen g) =>
      res (sup_le (X.basicOpen_le (res (X.basicOpen_le g) u))
          (X.basicOpen_le (res (X.basicOpen_le g) v))) c •
        (relativeDifferentials f).presheaf.map (homOfLE (sup_basicOpen_res_le g)).op
          H.generator) := by
  obtain ⟨h1u, h1v⟩ := H.generator_spec
  refine (H.twoChartData g).bijective_of_eqns ?_ ?_
  · have e := congrArg ((relativeDifferentials f).presheaf.map
      (homOfLE (basicOpen_res_le g u)).op) h1u
    rw [Ω_map_res_smul, map_map_eq, ← sec_res] at e
    rw [map_map_eq]
    simp only [res_res] at e ⊢
    exact e
  · have e := congrArg ((relativeDifferentials f).presheaf.map
      (homOfLE (basicOpen_res_le g v)).op) h1v
    rw [Ω_map_res_smul, map_map_eq, map_neg, ← sec_res] at e
    rw [map_map_eq]
    simp only [res_res] at e ⊢
    exact e

include H in
/-- On a basic open `D(g)`, `D(g) ∩ smoothLocus(f) = D(u|_{D(g)}) ∪ D(v|_{D(g)})`. -/
theorem basicOpen_inf_smoothLocus (g : Γ(X, W)) :
    X.basicOpen g ⊓ f.smoothLocus =
      X.basicOpen (res (X.basicOpen_le g) u) ⊔ X.basicOpen (res (X.basicOpen_le g) v) := by
  have hg : X.basicOpen g ≤ W := X.basicOpen_le g
  rw [Scheme.basicOpen_res, Scheme.basicOpen_res, ← inf_sup_left, ← H.smoothLocus,
    ← inf_assoc, inf_eq_left.mpr hg]

include H in
theorem inf_smoothLocus_le_generator :
    W ⊓ f.smoothLocus ≤
      X.basicOpen (res (X.basicOpen_le 1) u) ⊔ X.basicOpen (res (X.basicOpen_le 1) v) := by
  rw [← H.basicOpen_inf_smoothLocus 1, basicOpen_one_eq (W := W)]

/-- The section `du/u = -dv/v` of `ω_{X/S}` over `W`. -/
noncomputable def dualizingGenerator : Γ(dualizingSheaf f, W) :=
  (dualizingSheafSectionsEquiv f W).symm
    ((relativeDifferentials f).presheaf.map (homOfLE H.inf_smoothLocus_le_generator).op
      H.generator)

/-- For every basic open `D(g)` of `W`, the restriction of `dualizingGenerator` freely generates
`Γ(D(g), ω_{X/S})`. -/
theorem bijective_dualizingGenerator (g : Γ(X, W)) :
    Function.Bijective (fun c : Γ(X, X.basicOpen g) =>
      c • (dualizingSheaf f).presheaf.map (homOfLE (X.basicOpen_le g)).op
        H.dualizingGenerator) := by
  have heq := H.basicOpen_inf_smoothLocus g
  let ι : X.basicOpen g ⊓ f.smoothLocus ⟶
      X.basicOpen (res (X.basicOpen_le g) u) ⊔ X.basicOpen (res (X.basicOpen_le g) v) :=
    homOfLE heq.le
  let E := dualizingSheafSectionsEquiv f (X.basicOpen g)
  have hfun : (fun c : Γ(X, X.basicOpen g) =>
      c • (dualizingSheaf f).presheaf.map (homOfLE (X.basicOpen_le g)).op
        H.dualizingGenerator) =
      E.symm ∘ (relativeDifferentials f).presheaf.map ι.op ∘
        (fun c : Γ(X, X.basicOpen g) =>
          res (sup_le (X.basicOpen_le (res (X.basicOpen_le g) u))
              (X.basicOpen_le (res (X.basicOpen_le g) v))) c •
            (relativeDifferentials f).presheaf.map (homOfLE (sup_basicOpen_res_le g)).op
              H.generator) := by
    funext c
    apply E.injective
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply]
    rw [dualizingSheafSectionsEquiv_smul, dualizingSheafSectionsEquiv_map, dualizingGenerator,
      AddEquiv.apply_symm_apply, Ω_map_res_smul, res_res, map_map_eq, map_map_eq]
  rw [hfun]
  exact E.symm.bijective.comp
    (((relativeDifferentials f).map_bijective_of_le ι heq.ge).comp
      (H.bijective_generator_restrict g))

include H in
/-- **`ω_{X/S}` is invertible on a two-chart affine.** -/
theorem isInvertibleAt_dualizingSheaf {x : X} (hx : x ∈ W) :
    IsInvertibleAt (dualizingSheaf f) x :=
  isInvertibleAt_of_generator _ H.isAffineOpen H.dualizingGenerator
    H.bijective_dualizingGenerator hx

end TwoChartAffine

namespace NodeChart

variable [LocallyOfFinitePresentation f] {V : S.Opens} {W : X.Opens} (C : NodeChart f V W)

/-- A node chart is a two-chart affine with the coordinates `u = x₀`, `v = x₁`. -/
theorem twoChartAffine : TwoChartAffine f W (C.coord 0) (C.coord 1) where
  isAffineOpen := C.isAffineOpen_W
  rel U hU := by
    rw [C.coord_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    exact (universalDerivation f).sec_appLE _ C.h
  equalizer := C.nodeEqualizerData
  kaehler := by
    rintro W' hW' hle M hM t (rfl | rfl) ht
    · exact C.kaehler_bijective hW' hle M hM 0 ht
    · exact C.kaehler_bijective hW' hle M hM 1 ht
  smoothLocus := C.inf_smoothLocus

include C in
/-- **`ω_{X/S}` is invertible on a node chart** (step 1 of `lem:sm-omega-invertible`): on a node
chart `W` (`Γ(X, W) ≅ Γ(S, V)[u,v]/(uv - h)`, `h` a non-zero-divisor) the restriction of
`ω_{X/S}` to `Spec Γ(X, W)` is isomorphic to the structure sheaf, with generator
`du/u = -dv/v`. -/
theorem isInvertibleAt_dualizingSheaf {x : X} (hx : x ∈ W) :
    IsInvertibleAt (dualizingSheaf f) x :=
  C.twoChartAffine.isInvertibleAt_dualizingSheaf hx

end NodeChart

end DeJongAlterations.StableModification.Omega
