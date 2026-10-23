/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.DualitySchemeComparison
import DeJongAlterations.StableModification.CurvesField.DualitySchemeIntegral
import DeJongAlterations.Geometry.NormalCurveModification

/-!
# Chart pairs of a proper curve and Serre duality for its cohomology

A *chart pair* on a scheme `X` (`ChartPair`) consists of nonempty affine opens `U₀`, `U₁`
covering `X` and functions `t ∈ Γ(X, U₀)`, `s ∈ Γ(X, U₁)` with `D(t) = U₀ ∩ U₁ = D(s)` and
`t s = 1` on `U₀ ∩ U₁`: the charts of the map `X → ℙ¹` given by `t` (no such map is
constructed). For an integral `X` over a field `k` it is *separable* (`ChartPair.IsSeparable`) if
`k[T] → K(X)`, `T ↦ t`, is injective (`t` is transcendental) and `K(X)` is separable over `k(T)`.

For `X` integral, proper and normal over an algebraically closed `k`, with torsion free modules of
differentials on affine opens (e.g. `X` smooth), a separable chart pair gives the hypotheses of
the numerical Serre duality of lane OM2 (`DualityCurve`, blueprint `def:sm-two-chart-curve`), with
`A = Γ(X, U₀)` (`T ↦ t`), `B = Γ(X, U₁)` (`T ↦ s`), `W = Γ(X, U₀ ∩ U₁)`, `L = k(T)`,
`K = K(X)`: finiteness of `A` over `k[t]` is `isIntegral_eval₂_of_universallyClosed` (valuative
criterion), the localizations are the basic opens, and normality gives integrally closed
rings. Combined with the comparison of `DualitySchemeComparison` this computes the cohomology of
`𝒪_X` and of `Ω¹_{X/k}` (`ChartPair.duality`):

`h⁰(Ω¹) = h¹(𝒪)`, `h¹(Ω¹) = h⁰(𝒪)` and `h⁰(𝒪) = 1`, all finite.

Reference: M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, Thm 1.1, lines 1717–1741.
Blueprint: `sm-omega-degree-scheme.tex`, `def:sm-chart-pair`, `lem:sm-chart-pair-two-chart`,
`lem:sm-h0-structure-chart`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Polynomial Module
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.StableModification.Omega

namespace DeJongAlterations.StableModification.CurvesField.DualityScheme

noncomputable section

/-! ### Global functions of a two-chart complex -/

section GlobalFunctions

variable {k : Type u} [Field k] {A B W : Type u} [CommRing A] [CommRing B] [CommRing W]
  [IsDomain W] [Algebra k A] [Algebra k B] [Algebra k W] [Algebra A W] [Algebra B W]
  [IsScalarTower k A W] [IsScalarTower k B W]

/-- **Global functions** (blueprint `lem:sm-h0-structure-chart`): if `A → W`, `B → W` are
injective, `W` is a domain, `k` is algebraically closed and `H⁰(A × B → W)` is
finite-dimensional, then it is one-dimensional (the constants). -/
theorem finrank_H0_resO_eq_one [IsAlgClosed k]
    (hA : Function.Injective (algebraMap A W)) (hB : Function.Injective (algebraMap B W))
    [FiniteDimensional k (H0 (Duality.resO k A W) (Duality.resO k B W) LinearMap.id)] :
    finrank k (H0 (Duality.resO k A W) (Duality.resO k B W) LinearMap.id) = 1 := by
  let T : Subalgebra k W := (IsScalarTower.toAlgHom k A W).range ⊓
    (IsScalarTower.toAlgHom k B W).range
  have hT : Subalgebra.toSubmodule T =
      LinearMap.range (Duality.resO k A W) ⊓ LinearMap.range (Duality.resO k B W) := by
    ext x
    simp [T, Duality.resO]
  have e : H0 (Duality.resO k A W) (Duality.resO k B W) LinearMap.id ≃ₗ[k] T :=
    (Duality.H0EquivInf hA hB).trans (LinearEquiv.ofEq _ _ hT.symm)
  have : FiniteDimensional k T := Module.Finite.equiv e
  have : Algebra.IsIntegral k T := Algebra.IsIntegral.of_finite k T
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := T)
  rw [e.finrank_eq, ← (LinearEquiv.ofBijective (Algebra.linearMap k T) hbij).finrank_eq,
    Module.finrank_self]

end GlobalFunctions

/-! ### Germs at the generic point -/

section Germ

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- Restriction is compatible with the maps to the function field. -/
lemma germToFunctionField_restrict {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op a) = X.germToFunctionField U a :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ a

variable {k : Type u} [Field k] (c : k →+* Γ(X, ⊤))

/-- The constants of `k` in the function field do not depend on the chart. -/
lemma germToFunctionField_sectionsRingHom {U : X.Opens} [Nonempty U] [Nonempty (⊤ : X.Opens)]
    (r : k) :
    X.germToFunctionField U (sectionsRingHom c (le_top : U ≤ ⊤) r) =
      X.germToFunctionField ⊤ (c r) :=
  germToFunctionField_restrict (le_top : U ≤ ⊤) (c r)

end Germ

/-! ### The structure map on affine charts -/

section Structure

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- On an affine open `U`, the structure morphism is `Spec` of `k → Γ(X, U)`. -/
lemma fromSpec_comp_eq {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤))) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU (le_preimage_top f U),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp,
    sectionsRingHom_structureCoeff]
  rfl

/-- For `f` locally of finite type, the rings of affine opens are of finite type over `k`. -/
lemma finiteType_sectionsRingHom [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    (sectionsRingHom (structureCoeff f) (le_top : U ≤ ⊤)).FiniteType := by
  rw [sectionsRingHom_structureCoeff]
  refine RingHom.FiniteType.comp ?_ ?_
  · exact HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (le_preimage_top f U)
  · exact RingHom.FiniteType.of_surjective _ specTop_surjective

end Structure

/-! ### Chart pairs -/

/-- A **chart pair** on `X` (blueprint `def:sm-chart-pair`): nonempty affine opens `U₀`, `U₁`
covering `X` and `t ∈ Γ(X, U₀)`, `s ∈ Γ(X, U₁)` with `D(t) = U₀ ∩ U₁ = D(s)` and `t s = 1` on
`U₀ ∩ U₁`. -/
structure ChartPair (X : Scheme.{u}) where
  /-- The chart where `t` is regular. -/
  U₀ : X.Opens
  /-- The chart where `s = t⁻¹` is regular. -/
  U₁ : X.Opens
  isAffineOpen₀ : IsAffineOpen U₀
  isAffineOpen₁ : IsAffineOpen U₁
  nonempty₀ : Nonempty U₀
  nonempty₁ : Nonempty U₁
  sup_eq_top : U₀ ⊔ U₁ = ⊤
  /-- The coordinate on `U₀`. -/
  t : Γ(X, U₀)
  /-- The coordinate on `U₁`. -/
  s : Γ(X, U₁)
  basicOpen_t : X.basicOpen t = U₀ ⊓ U₁
  basicOpen_s : X.basicOpen s = U₀ ⊓ U₁
  mul_eq_one : X.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op t *
    X.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op s = 1

namespace ChartPair

variable {X : Scheme.{u}} (P : ChartPair X)

lemma isAffineOpen_inf : IsAffineOpen (P.U₀ ⊓ P.U₁) :=
  P.basicOpen_t ▸ P.isAffineOpen₀.basicOpen P.t

/-- In an irreducible scheme the two charts meet. -/
lemma nonempty_inf [IrreducibleSpace X] : Nonempty (P.U₀ ⊓ P.U₁ : X.Opens) := by
  have h₀ := P.nonempty₀
  have h₁ := P.nonempty₁
  have hη₀ : genericPoint X ∈ P.U₀ :=
    ((genericPoint_spec X).mem_open_set_iff P.U₀.isOpen).mpr (by simpa using h₀)
  have hη₁ : genericPoint X ∈ P.U₁ :=
    ((genericPoint_spec X).mem_open_set_iff P.U₁.isOpen).mpr (by simpa using h₁)
  exact ⟨⟨genericPoint X, hη₀, hη₁⟩⟩

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- The map `k[T] → K(X)`, `T ↦ t`. -/
def polyToFunctionField [IrreducibleSpace X] : k[X] →+* X.functionField :=
  haveI := P.nonempty₀
  (algebraMap Γ(X, P.U₀) X.functionField).comp
    (Polynomial.eval₂RingHom (sectionsRingHom (structureCoeff f) (le_top : P.U₀ ≤ ⊤)) P.t)

/-- A chart pair on an integral `k`-scheme is **separable** (blueprint `def:sm-chart-pair`) if
`k[T] → K(X)`, `T ↦ t`, is injective (`t` is transcendental over `k`) and `K(X)` is separable
over `k(T)` through it. -/
def IsSeparable [IsIntegral X] : Prop :=
  ∃ h : Function.Injective (P.polyToFunctionField f),
    @Algebra.IsSeparable (RatFunc k) X.functionField _ _ (IsFractionRing.lift h).toAlgebra


section Duality

variable {X : Scheme.{u}} (P : ChartPair X) {k : Type u} [Field k]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- **Serre duality for a proper normal curve with a separable chart pair** (blueprints
`lem:sm-chart-pair-two-chart`, `lem:sm-h0-structure-chart`, `thm:sm-omega-degree-scheme`): for
`X` integral, universally closed and locally of finite type over an algebraically closed `k`,
normal, with torsion free modules of differentials over affine opens, the cohomology of `𝒪_X`
and of `Ω¹_{X/k}` is finite-dimensional, `h⁰(Ω¹) = h¹(𝒪)`, `h¹(Ω¹) = h⁰(𝒪)` and `h⁰(𝒪) = 1`. -/
theorem duality [IsIntegral X] [IsAlgClosed k] [UniversallyClosed f] [LocallyOfFiniteType f]
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (hnormal : IsNormalScheme X)
    (htf : ∀ U : X.Opens, IsAffineOpen U →
      Module.IsTorsionFree Γ(X, U) Γ(relativeDifferentials f, U))
    (hsep : P.IsSeparable f) :
    FiniteDimensional k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0) ∧
    FiniteDimensional k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 1) ∧
    FiniteDimensional k (cohomology (relativeDifferentials f) (structureCoeff f) 0) ∧
    FiniteDimensional k (cohomology (relativeDifferentials f) (structureCoeff f) 1) ∧
    finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 0) =
      finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 1) ∧
    finrank k (cohomology (relativeDifferentials f) (structureCoeff f) 1) =
      finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0) ∧
    finrank k (cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0) = 1 := by
  obtain ⟨hinj, hsepL⟩ := hsep
  have h₀ := P.isAffineOpen₀
  have h₁ := P.isAffineOpen₁
  have h₀₁ := P.isAffineOpen_inf
  have := P.nonempty₀
  have := P.nonempty₁
  have := P.nonempty_inf
  have : Nonempty (⊤ : X.Opens) := by
    obtain ⟨x⟩ := P.nonempty₀
    exact ⟨⟨x.1, trivial⟩⟩
  set c := structureCoeff f with hc
  -- the rings of the charts as `k`-algebras
  let iA : Algebra k Γ(X, P.U₀) := (sectionsRingHom c (le_top : P.U₀ ≤ ⊤)).toAlgebra
  let iB : Algebra k Γ(X, P.U₁) := (sectionsRingHom c (le_top : P.U₁ ≤ ⊤)).toAlgebra
  let iW : Algebra k Γ(X, P.U₀ ⊓ P.U₁) :=
    (sectionsRingHom c (le_top : P.U₀ ⊓ P.U₁ ≤ ⊤)).toAlgebra
  let iAW : Algebra Γ(X, P.U₀) Γ(X, P.U₀ ⊓ P.U₁) :=
    (X.presheaf.map (homOfLE (inf_le_left : P.U₀ ⊓ P.U₁ ≤ P.U₀)).op).hom.toAlgebra
  let iBW : Algebra Γ(X, P.U₁) Γ(X, P.U₀ ⊓ P.U₁) :=
    (X.presheaf.map (homOfLE (inf_le_right : P.U₀ ⊓ P.U₁ ≤ P.U₁)).op).hom.toAlgebra
  have : IsScalarTower k Γ(X, P.U₀) Γ(X, P.U₀ ⊓ P.U₁) := IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.congr_fun (Genus.sectionsRingHom_comp (c := c) (inf_le_left : P.U₀ ⊓ P.U₁ ≤ P.U₀)) r).symm
  have : IsScalarTower k Γ(X, P.U₁) Γ(X, P.U₀ ⊓ P.U₁) := IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.congr_fun (Genus.sectionsRingHom_comp (c := c) (inf_le_right : P.U₀ ⊓ P.U₁ ≤ P.U₁)) r).symm
  -- the `k[T]`-algebra structures `T ↦ t`, `T ↦ s`
  let iXA : Algebra k[X] Γ(X, P.U₀) := (eval₂RingHom (algebraMap k Γ(X, P.U₀)) P.t).toAlgebra
  let iXB : Algebra k[X] Γ(X, P.U₁) := (eval₂RingHom (algebraMap k Γ(X, P.U₁)) P.s).toAlgebra
  have : IsScalarTower k k[X] Γ(X, P.U₀) := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = eval₂ _ _ (C r)
    rw [eval₂_C]
  have : IsScalarTower k k[X] Γ(X, P.U₁) := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = eval₂ _ _ (C r)
    rw [eval₂_C]

  -- finiteness over `k[T]` (valuative criterion)
  have hint₀ : (eval₂RingHom (sectionsRingHom c (le_top : P.U₀ ≤ ⊤)) P.t).IsIntegral :=
    isIntegral_eval₂_of_universallyClosed f h₀ h₁ P.sup_eq_top inf_le_left inf_le_right le_rfl
      P.t P.s P.basicOpen_t P.basicOpen_s P.mul_eq_one _ (fromSpec_comp_eq f h₀)
  have hint₁ : (eval₂RingHom (sectionsRingHom c (le_top : P.U₁ ≤ ⊤)) P.s).IsIntegral :=
    isIntegral_eval₂_of_universallyClosed f h₁ h₀ (by rw [sup_comm]; exact P.sup_eq_top)
      inf_le_right inf_le_left (le_of_eq (inf_comm _ _)) P.s P.t P.basicOpen_s P.basicOpen_t
      (by rw [mul_comm]; exact P.mul_eq_one) _ (fromSpec_comp_eq f h₁)
  have : Algebra.IsIntegral k[X] Γ(X, P.U₀) := ⟨fun a => hint₀ a⟩
  have : Algebra.IsIntegral k[X] Γ(X, P.U₁) := ⟨fun a => hint₁ a⟩
  have : Algebra.FiniteType k Γ(X, P.U₀) := finiteType_sectionsRingHom f h₀
  have : Algebra.FiniteType k Γ(X, P.U₁) := finiteType_sectionsRingHom f h₁
  have : Algebra.FiniteType k[X] Γ(X, P.U₀) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k k[X] _
  have : Algebra.FiniteType k[X] Γ(X, P.U₁) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k k[X] _
  have : Module.Finite k[X] Γ(X, P.U₀) := Algebra.IsIntegral.finite
  have : Module.Finite k[X] Γ(X, P.U₁) := Algebra.IsIntegral.finite
  -- the function field and the constants
  let g₀ : k →+* X.functionField := (X.germToFunctionField ⊤).hom.comp c
  have hg₀ : ∀ (U : X.Opens) [Nonempty U],
      (X.germToFunctionField U).hom.comp (sectionsRingHom c (le_top : U ≤ ⊤)) = g₀ :=
    fun U _ => RingHom.ext fun r => germToFunctionField_sectionsRingHom c r
  have hpoly : ∀ p : k[X], P.polyToFunctionField f p =
      eval₂ g₀ (X.germToFunctionField P.U₀ P.t) p := fun p => by
    change X.germToFunctionField P.U₀ (eval₂ _ _ p) = _
    rw [hom_eval₂, ← hg₀ P.U₀]
  have hst : X.germToFunctionField P.U₁ P.s = (X.germToFunctionField P.U₀ P.t)⁻¹ := by
    have h := congrArg (X.germToFunctionField (P.U₀ ⊓ P.U₁)) P.mul_eq_one
    rw [map_mul, map_one, germToFunctionField_restrict, germToFunctionField_restrict] at h
    exact eq_inv_of_mul_eq_one_right h
  -- torsion freeness over `k[T]`
  have : Module.IsTorsionFree k[X] Γ(X, P.U₀) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro p q hpq
    exact hinj (congrArg (X.germToFunctionField P.U₀) hpq)
  have : Module.IsTorsionFree k[X] Γ(X, P.U₁) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro p hp
    have hx : X.germToFunctionField P.U₀ P.t ≠ 0 := by
      intro h0
      have h := congrArg (X.germToFunctionField (P.U₀ ⊓ P.U₁)) P.mul_eq_one
      rw [map_mul, map_one, germToFunctionField_restrict, h0, zero_mul] at h
      exact zero_ne_one h
    let : Invertible (X.germToFunctionField P.U₀ P.t) := invertibleOfNonzero hx
    have h1 : eval₂ g₀ (X.germToFunctionField P.U₀ P.t)⁻¹ p = 0 := by
      have h := congrArg (X.germToFunctionField P.U₁) hp
      change X.germToFunctionField P.U₁ (eval₂ _ _ p) = _ at h
      rw [hom_eval₂, map_zero, hst] at h
      rw [← hg₀ P.U₁]
      exact h
    have h2 := eval₂_reflect_mul_pow g₀ (X.germToFunctionField P.U₀ P.t) p.natDegree
      (reflect p.natDegree p) (natDegree_reflect_le.trans (max_le le_rfl le_rfl))
    rw [reflect_reflect, invOf_eq_inv, h1, zero_mul, eq_comm, ← hpoly] at h2
    rw [← reflect_eq_zero_iff (N := p.natDegree)]
    exact hinj (h2.trans (map_zero _).symm)
  -- localizations
  have hXt : algebraMap k[X] Γ(X, P.U₀) Polynomial.X = P.t := eval₂_X _ _
  have hXs : algebraMap k[X] Γ(X, P.U₁) Polynomial.X = P.s := eval₂_X _ _
  have : IsLocalization.Away (algebraMap k[X] Γ(X, P.U₀) Polynomial.X) Γ(X, P.U₀ ⊓ P.U₁) := by
    rw [hXt]
    exact h₀.isLocalization_of_eq_basicOpen P.t (homOfLE inf_le_left) P.basicOpen_t.symm
  have : IsLocalization.Away (algebraMap k[X] Γ(X, P.U₁) Polynomial.X) Γ(X, P.U₀ ⊓ P.U₁) := by
    rw [hXs]
    exact h₁.isLocalization_of_eq_basicOpen P.s (homOfLE inf_le_right) P.basicOpen_s.symm
  -- the fraction fields
  have : IsFractionRing Γ(X, P.U₀ ⊓ P.U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (P.U₀ ⊓ P.U₁) h₀₁
  have : IsScalarTower Γ(X, P.U₀) Γ(X, P.U₀ ⊓ P.U₁) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (germToFunctionField_restrict inf_le_left a).symm
  have : IsScalarTower Γ(X, P.U₁) Γ(X, P.U₀ ⊓ P.U₁) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (germToFunctionField_restrict inf_le_right a).symm
  let iLK : Algebra (RatFunc k) X.functionField := (IsFractionRing.lift hinj).toAlgebra
  let iXK : Algebra k[X] X.functionField := (P.polyToFunctionField f).toAlgebra
  have : IsScalarTower k[X] (RatFunc k) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap hinj p).symm
  have : IsScalarTower k[X] Γ(X, P.U₀) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ikK : Algebra k X.functionField := g₀.toAlgebra
  have hk : ∀ (U : X.Opens) [Nonempty U] (r : k),
      g₀ r = X.germToFunctionField U (sectionsRingHom c (le_top : U ≤ ⊤) r) :=
    fun U _ r => (RingHom.congr_fun (hg₀ U) r).symm
  have : IsScalarTower k Γ(X, P.U₀ ⊓ P.U₁) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => hk (P.U₀ ⊓ P.U₁) r
  have : IsScalarTower k Γ(X, P.U₀) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => hk P.U₀ r
  have : IsScalarTower k Γ(X, P.U₁) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => hk P.U₁ r
  have : IsScalarTower k k[X] X.functionField := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = P.polyToFunctionField f (C r)
    rw [hpoly, eval₂_C]
    rfl
  have : IsScalarTower k (RatFunc k) X.functionField := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k) r,
      ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) X.functionField,
      ← IsScalarTower.algebraMap_apply k k[X] X.functionField]
  -- `K(X)` is finite over `k(T)`
  have : IsIntegrallyClosed Γ(X, P.U₀) :=
    Geometry.NormalCurveModification.affineSections_isIntegrallyClosed hnormal P.U₀ h₀
  have : IsIntegrallyClosed Γ(X, P.U₁) :=
    Geometry.NormalCurveModification.affineSections_isIntegrallyClosed hnormal P.U₁ h₁
  have : IsFractionRing Γ(X, P.U₀) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X P.U₀ h₀
  have : Module.IsTorsionFree k[X] X.functionField := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Algebra.IsAlgebraic k[X] X.functionField :=
    (IsFractionRing.isAlgebraic_iff' k[X] Γ(X, P.U₀) X.functionField).mp inferInstance
  have : Algebra.IsAlgebraic (RatFunc k) X.functionField :=
    Algebra.IsAlgebraic.extendScalars (R := k[X]) (IsFractionRing.injective k[X] (RatFunc k))
  have : IsIntegralClosure Γ(X, P.U₀) k[X] X.functionField :=
    IsIntegralClosure.of_isIntegrallyClosed Γ(X, P.U₀) k[X] X.functionField
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, P.U₀) (nonZeroDivisors k[X]))
      X.functionField :=
    IsIntegralClosure.isLocalization k[X] (RatFunc k) X.functionField Γ(X, P.U₀)
  have : FiniteDimensional (RatFunc k) X.functionField :=
    Module.Finite.of_isLocalization k[X] Γ(X, P.U₀) (nonZeroDivisors k[X])
  have : Algebra.IsSeparable (RatFunc k) X.functionField := hsepL
  -- torsion freeness of the differentials
  have : Module.IsTorsionFree Γ(X, P.U₀) Ω[Γ(X, P.U₀)⁄k] := by
    have := htf P.U₀ h₀
    let e := sectionsKaehlerEquivAux f h₀ rfl
    exact e.symm.injective.moduleIsTorsionFree e.symm (fun r m => e.symm.map_smul r m)
  have : Module.IsTorsionFree Γ(X, P.U₁) Ω[Γ(X, P.U₁)⁄k] := by
    have := htf P.U₁ h₁
    let e := sectionsKaehlerEquivAux f h₁ rfl
    exact e.symm.injective.moduleIsTorsionFree e.symm (fun r m => e.symm.map_smul r m)
  -- `t s = 1`
  have hts : algebraMap Γ(X, P.U₀) Γ(X, P.U₀ ⊓ P.U₁) (algebraMap k[X] Γ(X, P.U₀) Polynomial.X) *
      algebraMap Γ(X, P.U₁) Γ(X, P.U₀ ⊓ P.U₁) (algebraMap k[X] Γ(X, P.U₁) Polynomial.X) = 1 := by
    rw [hXt, hXs]
    exact P.mul_eq_one
  -- the comparison isomorphisms
  let eO₀ := cohomologyZeroEquivStructure f P.sup_eq_top h₀ h₁ h₀₁ (U₀ := P.U₀) (U₁ := P.U₁)
    rfl rfl rfl rfl rfl
  let eO₁ := cohomologyOneEquivStructure f P.sup_eq_top h₀ h₁ h₀₁ (U₀ := P.U₀) (U₁ := P.U₁)
    rfl rfl rfl rfl rfl
  let eΩ₀ := cohomologyZeroEquivKaehler f P.sup_eq_top h₀ h₁ h₀₁ (U₀ := P.U₀) (U₁ := P.U₁)
    rfl rfl rfl rfl rfl
  let eΩ₁ := cohomologyOneEquivKaehler f P.sup_eq_top h₀ h₁ h₀₁ (U₀ := P.U₀) (U₁ := P.U₁)
    rfl rfl rfl rfl rfl
  have fO₀ := Duality.finiteDimensional_H0_structure (RatFunc k) X.functionField hts
  have fO₁ := Duality.finiteDimensional_H1_structure (RatFunc k) X.functionField hts
  have fΩ₀ := Duality.finiteDimensional_H0_kaehler (RatFunc k) X.functionField hts
  have fΩ₁ := Duality.finiteDimensional_H1_kaehler (RatFunc k) X.functionField hts
  refine ⟨Module.Finite.equiv eO₀.symm, Module.Finite.equiv eO₁.symm,
    Module.Finite.equiv eΩ₀.symm, Module.Finite.equiv eΩ₁.symm, ?_, ?_, ?_⟩
  · rw [eΩ₀.finrank_eq, eO₁.finrank_eq]
    exact Duality.finrank_H0_kaehler (RatFunc k) X.functionField hts
  · rw [eΩ₁.finrank_eq, eO₀.finrank_eq]
    exact Duality.finrank_H1_kaehler (RatFunc k) X.functionField hts
  · rw [eO₀.finrank_eq]
    exact finrank_H0_resO_eq_one
      (Duality.algebraMap_injective_away (k := k) Γ(X, P.U₀) Γ(X, P.U₀ ⊓ P.U₁))
      (Duality.algebraMap_injective_away (k := k) Γ(X, P.U₁) Γ(X, P.U₀ ⊓ P.U₁))

end Duality

end ChartPair

end

end DeJongAlterations.StableModification.CurvesField.DualityScheme
