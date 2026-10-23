/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.EtaleOmega
import DeJongAlterations.StableModification.Omega.InvertibleNode

/-!
# Base change of `Ω¹_{X/S}` along commutative squares

Let
```
  Y --ψ--> X
  |f'      |f
  v        v
  T --h--> S
```
be a commutative square of schemes. This file constructs the base change map of relative
differentials `baseChangeDifferentials : Ω¹_{X/S} ⟶ ψ_* Ω¹_{Y/T}`, `ds ↦ d(ψ^♯ s)`
(`baseChangeDifferentials_app_d`), from the universal property of `Ω¹_{X/S}` (sections locally
pulled back from `S` pull back to sections locally pulled back from `T`, `baseSubring_comp_le`),
and records:

* `baseChangeDifferentials_smul`, `baseChangeDifferentials_map`: it is semilinear along `ψ^♯`
  and compatible with restriction;
* `baseChangeDifferentials_smul_eq_d`: if `t σ = dt` on `U` then `ψ^♯t · θ(σ) = d(ψ^♯t)` on
  `ψ⁻¹U`; in particular (`baseChangeDifferentials_eq_logForm`) the base change of a logarithmic
  form `σ = dt/t` (for instance the generator `du/u = -dv/v` of `ω` on an étale node chart,
  `Omega.TwoChartAffine.generator_spec`) is the logarithmic form `d(ψ^♯t)/ψ^♯t`;
* `sectionsEquiv_baseChange`: on affine opens it is the map of Kähler differentials
  `Ω_{Γ(X,W)/Γ(S,V)} → Ω_{Γ(Y,W')/Γ(T,V')}` (`KaehlerDifferential.map`).

For the geometric fibre `X_K = X ×_S Spec K` (`T = Spec K`), these are the maps through which
`ω_{X/S}` is compared with Rosenlicht's sheaf of the fibre (M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), §1.2, properties (a), (b), `semi-stable.tex`
T:1700–1704): on the smooth locus `Ω¹` commutes with base change, and near a node the generator
`du/u = -dv/v` goes to the Rosenlicht generator (`Omega/RosenlichtFibre.lean`).
Blueprint `sm-omega-base-change.tex`, `def:sm-omega-base-change-map`, `lem:sm-omega-base-change-log`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

variable {X Y S T : Scheme.{u}} (f : X ⟶ S) (f' : Y ⟶ T) (ψ : Y ⟶ X) (h : T ⟶ S)

/-- Sections locally pulled back from `S` along `f' ≫ h` are locally pulled back from `T`. -/
theorem baseSubring_comp_le (U : Y.Opens) : baseSubring (f' ≫ h) U ≤ baseSubring f' U := by
  intro s hs y hy
  obtain ⟨σ, hσ⟩ := hs y hy
  refine ⟨h.stalkMap (f' y) σ, ?_⟩
  rw [← hσ, Scheme.Hom.stalkMap_comp]
  rfl

variable (sq : ψ ≫ f = f' ≫ h)

/-- The pre-derivation `𝒪_X → ψ_* Ω¹_{Y/T}`, `s ↦ d(ψ^♯ s)`. -/
def baseChangePreDerivation :
    PreDerivation ((Scheme.Modules.pushforward ψ).obj (relativeDifferentials f')) where
  d U := ((universalDerivation f').sec (ψ ⁻¹ᵁ U)).comp (ψ.app U).hom.toAddMonoidHom
  d_mul U s t := by
    change (universalDerivation f').sec _ (ψ.app U (s * t)) = _
    rw [map_mul, RelDerivation.sec_mul]
    rfl
  d_map {U U'} i s := by
    change (universalDerivation f').sec _ (ψ.app U' (X.presheaf.map i.op s)) =
      (relativeDifferentials f').presheaf.map _
        ((universalDerivation f').sec _ (ψ.app U s))
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply,
      RelDerivation.sec_map]
    rfl

include sq in
/-- The relative derivation `𝒪_X → ψ_* Ω¹_{Y/T}`, `s ↦ d(ψ^♯ s)`. -/
def baseChangeDerivation :
    RelDerivation f ((Scheme.Modules.pushforward ψ).obj (relativeDifferentials f')) :=
  (baseChangePreDerivation f' ψ).toRelDerivation (fun U t ht => by
    have h1 := app_mem_baseSubring_comp f ψ ht
    rw [sq] at h1
    exact (universalDerivation f').sec_base _ (baseSubring_comp_le f' h _ h1))

/-- **The base change map of differentials** `Ω¹_{X/S} ⟶ ψ_* Ω¹_{Y/T}`, `ds ↦ d(ψ^♯ s)`, for a
commutative square `ψ ≫ f = f' ≫ h`. -/
def baseChangeDifferentials :
    relativeDifferentials f ⟶ (Scheme.Modules.pushforward ψ).obj (relativeDifferentials f') :=
  (homEquiv f _).symm (baseChangeDerivation f f' ψ h sq)

theorem baseChangeDifferentials_app_d {U : X.Opens} (s : Γ(X, U)) :
    (baseChangeDifferentials f f' ψ h sq).app U ((universalDerivation f).d s) =
      (universalDerivation f').d (ψ.app U s) := by
  rw [← homEquiv_apply_d, baseChangeDifferentials, Equiv.apply_symm_apply]
  rfl

/-- The base change map on sections over `U`, as a map into `Γ(Ω¹_{Y/T}, ψ⁻¹ U)`. -/
def baseChangeSecMap (U : X.Opens) :
    Γ(relativeDifferentials f, U) → Γ(relativeDifferentials f', ψ ⁻¹ᵁ U) :=
  fun m => (baseChangeDifferentials f f' ψ h sq).app U m

theorem baseChangeSecMap_d {U : X.Opens} (s : Γ(X, U)) :
    baseChangeSecMap f f' ψ h sq U ((universalDerivation f).d s) =
      (universalDerivation f').d (ψ.app U s) :=
  baseChangeDifferentials_app_d f f' ψ h sq s

theorem baseChangeSecMap_add {U : X.Opens} (m m' : Γ(relativeDifferentials f, U)) :
    baseChangeSecMap f f' ψ h sq U (m + m') =
      baseChangeSecMap f f' ψ h sq U m + baseChangeSecMap f f' ψ h sq U m' :=
  map_add ((baseChangeDifferentials f f' ψ h sq).app U).hom m m'

/-- The base change map is semilinear along `ψ^♯`. -/
theorem baseChangeSecMap_smul {U : X.Opens} (c : Γ(X, U)) (m : Γ(relativeDifferentials f, U)) :
    baseChangeSecMap f f' ψ h sq U (c • m) = ψ.app U c • baseChangeSecMap f f' ψ h sq U m :=
  Scheme.Modules.Hom.app_smul (baseChangeDifferentials f f' ψ h sq) c m

/-- The base change map commutes with restriction. -/
theorem baseChangeSecMap_map {U U' : X.Opens} (hU : U' ≤ U) (m : Γ(relativeDifferentials f, U)) :
    baseChangeSecMap f f' ψ h sq U' ((relativeDifferentials f).presheaf.map (homOfLE hU).op m) =
      (relativeDifferentials f').presheaf.map (homOfLE (ψ.preimage_mono hU)).op
        (baseChangeSecMap f f' ψ h sq U m) :=
  Scheme.Modules.Hom.app_map (baseChangeDifferentials f f' ψ h sq) (homOfLE hU) m

theorem baseChangeSecMap_sec {U : X.Opens} (s : Γ(X, U)) :
    baseChangeSecMap f f' ψ h sq U ((universalDerivation f).sec U s) =
      (universalDerivation f').sec (ψ ⁻¹ᵁ U) (ψ.app U s) :=
  baseChangeDifferentials_app_d f f' ψ h sq s

/-- **The relation `t σ = dt` survives base change**: if `t · σ|_{U'} = dt` on `U' ⊆ U`, then
`ψ^♯ t · θ(σ)|_{ψ⁻¹ U'} = d(ψ^♯ t)`. -/
theorem baseChangeSecMap_smul_eq_d {U U' : X.Opens} (hU : U' ≤ U)
    (σ : Γ(relativeDifferentials f, U)) (t : Γ(X, U'))
    (ht : t • (relativeDifferentials f).presheaf.map (homOfLE hU).op σ =
      (universalDerivation f).sec U' t) :
    ψ.app U' t • (relativeDifferentials f').presheaf.map (homOfLE (ψ.preimage_mono hU)).op
        (baseChangeSecMap f f' ψ h sq U σ) =
      (universalDerivation f').sec (ψ ⁻¹ᵁ U') (ψ.app U' t) := by
  rw [← baseChangeSecMap_map f f' ψ h sq hU, ← baseChangeSecMap_smul, ht, baseChangeSecMap_sec]

/-- **Logarithmic forms base change to logarithmic forms**: if `t · σ|_{U'} = dt` and `ψ^♯ t` is
a unit on `ψ⁻¹ U'` with inverse `t'`, then `θ(σ)|_{ψ⁻¹ U'} = t' · d(ψ^♯ t)`. -/
theorem baseChangeSecMap_eq_logForm {U U' : X.Opens} (hU : U' ≤ U)
    (σ : Γ(relativeDifferentials f, U)) (t : Γ(X, U'))
    (ht : t • (relativeDifferentials f).presheaf.map (homOfLE hU).op σ =
      (universalDerivation f).sec U' t)
    (t' : Γ(Y, ψ ⁻¹ᵁ U')) (htt' : t' * ψ.app U' t = 1) :
    (relativeDifferentials f').presheaf.map (homOfLE (ψ.preimage_mono hU)).op
        (baseChangeSecMap f f' ψ h sq U σ) =
      t' • (universalDerivation f').sec (ψ ⁻¹ᵁ U') (ψ.app U' t) := by
  rw [← baseChangeSecMap_smul_eq_d f f' ψ h sq hU σ t ht, smul_smul, htt', one_smul]

/-- On affine opens: the restriction to `W' ⊆ ψ⁻¹ W` of the base change of `da` is
`d(ψ^♯ a|_{W'})`, i.e. the base change map is the map of Kähler differentials
`Ω_{Γ(X,W)/Γ(S,V)} → Ω_{Γ(Y,W')/Γ(T,V')}` under `sectionsEquiv`. -/
theorem baseChangeSecMap_restrict_sec {W : X.Opens} {W' : Y.Opens} (hW'W : W' ≤ ψ ⁻¹ᵁ W)
    (a : Γ(X, W)) :
    (relativeDifferentials f').presheaf.map (homOfLE hW'W).op
        (baseChangeSecMap f f' ψ h sq W ((universalDerivation f).sec W a)) =
      (universalDerivation f').sec W' (ψ.appLE W W' hW'W a) := by
  rw [baseChangeSecMap_sec, ← RelDerivation.sec_map]
  rfl

/-- The negative form of `baseChangeSecMap_smul_eq_d`: `t · σ|_{U'} = -dt` gives
`ψ^♯ t · θ(σ)|_{ψ⁻¹ U'} = -d(ψ^♯ t)`. -/
theorem baseChangeSecMap_smul_eq_neg_d {U U' : X.Opens} (hU : U' ≤ U)
    (σ : Γ(relativeDifferentials f, U)) (t : Γ(X, U'))
    (ht : t • (relativeDifferentials f).presheaf.map (homOfLE hU).op σ =
      -(universalDerivation f).sec U' t) :
    ψ.app U' t • (relativeDifferentials f').presheaf.map (homOfLE (ψ.preimage_mono hU)).op
        (baseChangeSecMap f f' ψ h sq U σ) =
      -(universalDerivation f').sec (ψ ⁻¹ᵁ U') (ψ.app U' t) := by
  rw [← baseChangeSecMap_map f f' ψ h sq hU, ← baseChangeSecMap_smul, ht, ← baseChangeSecMap_sec]
  change ((baseChangeDifferentials f f' ψ h sq).app U').hom (-_) = -((baseChangeDifferentials f f' ψ h sq).app U').hom _
  rw [map_neg]

section TwoChart

variable [LocallyOfFinitePresentation f] {W : X.Opens} {u v : Γ(X, W)} (H : TwoChartAffine f W u v)

/-- **The base change of the generator `du/u = -dv/v`** of `ω` on a two-chart affine (e.g. an
étale node chart, `EtaleNodeChart.twoChartAffine`): its image `θ(σ)` satisfies
`ψ^♯u · θ(σ) = d(ψ^♯ u)` on `ψ⁻¹ D(u)` and `ψ^♯v · θ(σ) = -d(ψ^♯ v)` on `ψ⁻¹ D(v)`. On the
geometric fibre, where `ψ^♯u · ψ^♯v = 0` near the nodes, this is the Rosenlicht generator
`(du/u, -dv/v)` of `Omega/RosenlichtAlgebra.lean`. -/
theorem baseChange_generator_spec :
    ψ.app _ (res (X.basicOpen_le (res (X.basicOpen_le 1) u)) (res (X.basicOpen_le 1) u)) •
        (relativeDifferentials f').presheaf.map (homOfLE (ψ.preimage_mono le_sup_left)).op
          (baseChangeSecMap f f' ψ h sq _ H.generator) =
      (universalDerivation f').sec _ (ψ.app _
        (res (X.basicOpen_le (res (X.basicOpen_le 1) u)) (res (X.basicOpen_le 1) u))) ∧
    ψ.app _ (res (X.basicOpen_le (res (X.basicOpen_le 1) v)) (res (X.basicOpen_le 1) v)) •
        (relativeDifferentials f').presheaf.map (homOfLE (ψ.preimage_mono le_sup_right)).op
          (baseChangeSecMap f f' ψ h sq _ H.generator) =
      -(universalDerivation f').sec _ (ψ.app _
        (res (X.basicOpen_le (res (X.basicOpen_le 1) v)) (res (X.basicOpen_le 1) v))) :=
  ⟨baseChangeSecMap_smul_eq_d f f' ψ h sq le_sup_left _ _ H.generator_spec.1,
    baseChangeSecMap_smul_eq_neg_d f f' ψ h sq le_sup_right _ _ H.generator_spec.2⟩

end TwoChart

end DeJongAlterations.StableModification.Omega
