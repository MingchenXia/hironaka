/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusFormula
import DeJongAlterations.Geometry.NormalizationFiniteArbitraryField
import DeJongAlterations.StableModification.Cohomology.FiniteProjective
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# The genus formula for the normalization of an integral curve

This file discharges the hypotheses of the δ-formula (`GenusFormula.eulerChar_eq_add_finsum_delta`)
for the normalization `π : C̃ → C` of an integral curve `C` locally of finite type over a field
`k` (Codex's `NormalizationGluing.normalizationStructure C`, glued from the integral closures of
the affine coordinate rings in the function field, finite by
`NormalizationFiniteArbitraryField.normalizationStructure_isFinite`), and proves Temkin's genus
formula (Lemma B.1 of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), `references/temkin10-stable-modification/source/semi-stable.tex`, lines 4413–4433) for
integral projective curves: `p_a(C) = p_a(C̃) + ∑ᶠ x, δ(x)` (`arithmeticGenus_eq_normalization`).
For an irreducible `C` (`|C⁰| = 1`) this is Temkin's `p_a(C) = 1 - |C⁰| + ∑_{x ∈ C} g(x)`, with
`g(η) = p_a(C̃)` the genus of the normalization (`= h¹(𝒪_{C̃})` when `h⁰(𝒪_{C̃}) = 1` and
`H^{≥2} = 0`) and `g(x) = δ(x)` at closed points.

The case of a reducible reduced curve (normalization = disjoint union of the normalizations of
the components, additivity of `χ`) is not treated here (blueprint `lem:sm-genus-formula`).

## Main results

* `finiteDimensional_coker_of_isFractionRing`: for a domain `A` of finite type over `k` of
  dimension `≤ 1` and a finite `A`-subalgebra `B` of `Frac(A)`, `B / A` is finite-dimensional
  over `k` (a common denominator `s ≠ 0` kills `B / A`, and `A / sA` is Artinian of finite type,
  hence finite over `k`).
* `chartSectionsIso`, `chartSectionsIso_coeff`: `Γ(π⁻¹V, 𝒪_{C̃})` is the integral closure of
  `Γ(V, 𝒪_C)` in the function field, compatibly with `π^♯`.
* `normalization_app_injective`, `normalization_isFiniteCoker`: the hypotheses of the δ-formula
  for the normalization of an integral curve.
* `compactSpace_of_isAffineHom`, `isAffineHom_diagonal_of_isAffineHom`: the source of an affine
  morphism inherits quasi-compactness and affineness of the diagonal.
* `arithmeticGenus_eq_normalization`: the genus formula for integral projective curves.

Blueprint: `sm-curves-fields-genus.tex`, `lem:sm-normalization-skyscraper`,
`thm:sm-genus-formula-integral`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open Module

set_option autoImplicit false

universe u v w

section Algebra

variable (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
  {K : Type w} [Field K] [Algebra A K] [IsFractionRing A K]

/-- A finite `A`-subalgebra of the fraction field has a common denominator: some `s ≠ 0` in `A`
multiplies it into `A`. -/
theorem exists_mul_mem_range {B : Type*} [CommRing B] [Algebra A B] [Algebra B K]
    [IsScalarTower A B K] (hinj : Function.Injective (algebraMap B K)) [Module.Finite A B] :
    ∃ s : A, s ≠ 0 ∧ ∀ b : B, s • b ∈ LinearMap.range (Algebra.linearMap A B) := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
  have hden : ∀ b : B, ∃ t : A, t ≠ 0 ∧ t • b ∈ LinearMap.range (Algebra.linearMap A B) := by
    intro b
    obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.surj (nonZeroDivisors A) (algebraMap B K b)
    refine ⟨t, nonZeroDivisors.ne_zero t.2, a, hinj ?_⟩
    simp only [Algebra.linearMap_apply]
    rw [← IsScalarTower.algebraMap_apply, ← ht, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_comm]
  choose t ht0 ht using hden
  refine ⟨∏ b ∈ S, t b, Finset.prod_ne_zero_iff.2 fun b _ => ht0 b, fun b => ?_⟩
  have hb : b ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_coe.1 hx), mul_smul]
    exact Submodule.smul_mem _ _ (ht x)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

/-- A quotient of a one-dimensional domain of finite type over `k` by a nonzero element is
finite-dimensional over `k`. -/
theorem finite_quotient_span_singleton [Algebra.FiniteType k A] [Ring.KrullDimLE 1 A] {s : A}
    (hs : s ≠ 0) : Module.Finite k (A ⧸ Ideal.span {s}) := by
  have hdim0 : Ring.KrullDimLE 0 (A ⧸ Ideal.span {s}) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro J hJ
    have hprime : J.IsPrime := hJ.1.1
    refine hprime.isMaximal_of_ne_bot ?_
    rintro rfl
    exact hs (Ideal.span_singleton_le_iff_mem _ |>.1 hJ.1.2 |> (Submodule.mem_bot A).1)
  have : Algebra.FiniteType k (A ⧸ Ideal.span {s}) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  exact (Module.finite_iff_krullDimLE_zero k (A ⧸ Ideal.span {s})).2 hdim0

/-- **The cokernel of a one-dimensional domain in a finite birational extension is
finite-dimensional** (`π_*𝒪_{C̃}/𝒪_C` is a finite-length skyscraper). For `A` a domain of finite
type over `k` with `dim A ≤ 1` and `B` a finite `A`-algebra embedded in `Frac(A)`, `B / A` is
finite-dimensional over `k`. -/
theorem finiteDimensional_coker_of_isFractionRing [Algebra.FiniteType k A] [Ring.KrullDimLE 1 A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra B K] [IsScalarTower A B K]
    (hinj : Function.Injective (algebraMap B K)) [Module.Finite A B] [Algebra k B]
    [IsScalarTower k A B] : FiniteDimensional k (Coker A B) := by
  classical
  obtain ⟨s, hs0, hs⟩ := exists_mul_mem_range (A := A) (K := K) hinj
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
  have : Module.Finite k (A ⧸ Ideal.span {s}) := finite_quotient_span_singleton k hs0
  -- the generators of `B / A` and the map `(A / sA)^S → B / A`
  let q : S → Coker A B := fun b => Submodule.Quotient.mk (b : B)
  have hker : ∀ b : S, Ideal.span {s} ≤ LinearMap.ker (LinearMap.toSpanSingleton A _ (q b)) := by
    intro b
    rw [Ideal.span_le]
    rintro _ rfl
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hs b
  let Φ : (S → A ⧸ Ideal.span {s}) →ₗ[A] Coker A B :=
    ∑ b : S, ((Ideal.span {s}).liftQ (LinearMap.toSpanSingleton A _ (q b)) (hker b)) ∘ₗ
      LinearMap.proj b
  have hΦ : Function.Surjective Φ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
    have hy : y ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hy
    refine ⟨fun b => Ideal.Quotient.mk _ (c b), ?_⟩
    rw [← hc]
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [show (Submodule.Quotient.mk (∑ a ∈ S, c a • a) : Coker A B) =
      ∑ a ∈ S, Submodule.Quotient.mk (c a • a) from map_sum (Submodule.mkQ _) _ _,
      ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun b _ => ?_
    change (Ideal.span {s}).liftQ _ _ (Submodule.Quotient.mk (c b)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  exact Module.Finite.of_surjective (Φ.restrictScalars k) hΦ

end Algebra

section Scheme

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open DeJongAlterations.Geometry DeJongAlterations.StableModification.Cohomology

/-- An affine morphism to a quasi-compact scheme has quasi-compact source. -/
theorem compactSpace_of_isAffineHom {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π]
    [CompactSpace X] : CompactSpace Y :=
  ⟨by simpa using QuasiCompact.isCompact_preimage (f := π) Set.univ isOpen_univ isCompact_univ⟩

/-- An affine morphism to a scheme with affine diagonal has source with affine diagonal. -/
theorem isAffineHom_diagonal_of_isAffineHom {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π]
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    IsAffineHom (pullback.diagonal (terminal.from Y)) := by
  have hsnd : ∀ {X' Y' Z' : Scheme.{u}} (f : X' ⟶ Z') (g : Y' ⟶ Z') [hf : IsAffineHom f],
      IsAffineHom (pullback.snd f g) := fun f g hf =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback f g) hf
  have h : IsAffineHom (pullback.diagonal (π ≫ terminal.from X)) := by
    rw [pullback.diagonal_comp]
    have : IsAffineHom (pullback.diagonal π) := inferInstance
    have := hsnd (pullback.diagonal (terminal.from X))
      (pullback.map (π ≫ terminal.from X) (π ≫ terminal.from X) (terminal.from X)
        (terminal.from X) π π (𝟙 (⊤_ Scheme)) (by simp) (by simp))
    infer_instance
  have e : π ≫ terminal.from X = terminal.from Y := terminal.hom_ext _ _
  exact e ▸ h

variable {C : Scheme.{u}} [IsIntegral C]

open NormalizationGluing

/-- The sections of the normalization over the preimage of a nonempty affine open `U` are the
integral closure of `Γ(U, 𝒪_C)` in the function field (adapted from Codex's
`ProperSteinGlobalSections.normalizationChartSectionsIso`, written there for
`NormalizationInExtension`). -/
noncomputable def chartSectionsIso (U : NormalizationGluing.NonemptyAffineOpen C) :
    CommRingCat.of (closureRing U) ≅ Γ(normalization C, normalizationStructure C ⁻¹ᵁ U.1.1) :=
  (Scheme.ΓSpecIso (.of (closureRing U))).symm ≪≫
    IsOpenImmersion.ΓIsoTop (chartInclusion C U) ≪≫
      (normalization C).presheaf.mapIso (eqToIso (chartInclusion_opensRange U).symm).op

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma chartSectionsIso_inv (U : NormalizationGluing.NonemptyAffineOpen C) :
    (chartSectionsIso U).inv =
      (chartInclusion C U).appLE (normalizationStructure C ⁻¹ᵁ U.1.1) ⊤
        (by rw [← chartInclusion_opensRange U, Scheme.Hom.preimage_opensRange]) ≫
        (Scheme.ΓSpecIso (.of (closureRing U))).hom := by
  simp [chartSectionsIso, IsOpenImmersion.ΓIsoTop, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Under `chartSectionsIso`, `π^♯ : Γ(U, 𝒪_C) → Γ(π⁻¹U, 𝒪_{C̃})` is the inclusion of `Γ(U, 𝒪_C)`
into its integral closure. -/
theorem chartSectionsIso_coeff (U : NormalizationGluing.NonemptyAffineOpen C) :
    CommRingCat.ofHom (algebraMap Γ(C, U.1.1) (closureRing U)) ≫ (chartSectionsIso U).hom =
      (normalizationStructure C).app U.1.1 := by
  apply (cancel_mono (chartSectionsIso U).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [chartSectionsIso_inv, ← Category.assoc, ← Scheme.Hom.comp_appLE]
  simp only [chartInclusion_structure]
  simp only [affineStructure, Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self,
    Category.assoc, Scheme.Hom.map_appLE]
  change CommRingCat.ofHom (algebraMap Γ(C, U.1.1) (closureRing U)) =
    (Scheme.ΓSpecIso Γ(C, U.1.1)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, U.1.1) (closureRing U)))).appTop ≫
        (Scheme.ΓSpecIso (.of (closureRing U))).hom
  rw [Scheme.ΓSpecIso_naturality]
  change _ = (Scheme.ΓSpecIso Γ(C, U.1.1)).inv ≫ (Scheme.ΓSpecIso Γ(C, U.1.1)).hom ≫ _
  simp

/-- The nonempty affine open determined by an affine open with a point. -/
abbrev toNonemptyAffineOpen (V : C.Opens) (hV : IsAffineOpen V) (hne : Nonempty V) :
    NormalizationGluing.NonemptyAffineOpen C :=
  ⟨⟨V, hV⟩, hne⟩

/-- `π^♯` on a nonempty affine open is the inclusion into the integral closure. -/
lemma normalization_app_eq (V : C.Opens) (hV : IsAffineOpen V) (hne : Nonempty V) :
    ((normalizationStructure C).app V).hom =
      (chartSectionsIso (toNonemptyAffineOpen V hV hne)).hom.hom.comp
        (algebraMap Γ(C, V) (closureRing (toNonemptyAffineOpen V hV hne))) := by
  rw [← chartSectionsIso_coeff (toNonemptyAffineOpen V hV hne)]
  rfl

/-- **`𝒪_C → π_*𝒪_{C̃}` is injective** on affine opens. -/
theorem normalization_app_injective (V : C.Opens) (hV : IsAffineOpen V) :
    Function.Injective ((normalizationStructure C).app V).hom := by
  rcases (V : Set C).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · have : V = ⊥ := TopologicalSpace.Opens.ext h
    subst this
    intro a b _
    exact Subsingleton.elim a b
  · have hne : Nonempty V := ⟨⟨x, hx⟩⟩
    rw [normalization_app_eq V hV hne]
    refine (ConcreteCategory.bijective_of_isIso
      (chartSectionsIso (toNonemptyAffineOpen V hV hne)).hom).1.comp ?_
    intro a b hab
    apply C.germToFunctionField_injective V
    exact congrArg (fun c : closureRing (toNonemptyAffineOpen V hV hne) => (c : C.functionField)) hab

variable {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include p in
/-- The normalization of an integral scheme locally of finite type over a field is affine (it
is finite, `NormalizationFiniteArbitraryField.normalizationStructure_isFinite`). -/
theorem normalization_isAffineHom : IsAffineHom (normalizationStructure C) := by
  have := NormalizationFiniteArbitraryField.normalizationStructure_isFinite p
  infer_instance

omit [IsIntegral C] [LocallyOfFiniteType p] in
/-- The constants on an affine open are Codex's coefficient map
`NormalizationFinite.affineCoefficientMap`. -/
lemma sectionsRingHom_structureCoeff (V : C.Opens) (hV : IsAffineOpen V) :
    sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤) =
      NormalizationFinite.affineCoefficientMap p ⟨V, hV⟩ := rfl

/-- **`π_*𝒪_{C̃} / 𝒪_C` is a finite-dimensional skyscraper**: for an integral curve `C` locally
of finite type over `k` and every affine open `V`, `Γ(π⁻¹V, 𝒪_{C̃}) / Γ(V, 𝒪_C)` is
finite-dimensional over `k`. -/
theorem normalization_isFiniteCoker (hdim : topologicalKrullDim C ≤ 1) (V : C.Opens)
    (hV : IsAffineOpen V) :
    IsFiniteCoker (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))
      ((normalizationStructure C).app V).hom := by
  rcases (V : Set C).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · have : V = ⊥ := TopologicalSpace.Opens.ext h
    subst this
    unfold IsFiniteCoker
    have : Subsingleton Γ(normalization C, normalizationStructure C ⁻¹ᵁ ⊥) := by
      rw [Scheme.Hom.preimage_bot]
      infer_instance
    infer_instance
  · have hne : Nonempty V := ⟨⟨x, hx⟩⟩
    let ψ := sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)
    let φ := ((normalizationStructure C).app V).hom
    -- the integral closure `B` of `A = Γ(V, 𝒪_C)` in `K = k(C)`
    let _ : Algebra k Γ(C, V) := ψ.toAlgebra
    let _ : Algebra k (closureRing (toNonemptyAffineOpen V hV hne)) := ((algebraMap Γ(C, V) (closureRing (toNonemptyAffineOpen V hV hne))).comp ψ).toAlgebra
    have : IsScalarTower k Γ(C, V) (closureRing (toNonemptyAffineOpen V hV hne)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.FiniteType k Γ(C, V) := NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
    have : IsDomain Γ(C, V) := IsIntegral.component_integral V
    have : IsFractionRing Γ(C, V) C.functionField :=
      functionField_isFractionRing_of_isAffineOpen C V hV
    have : Ring.KrullDimLE 1 Γ(C, V) := NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
    have : Module.Finite Γ(C, V) (closureRing (toNonemptyAffineOpen V hV hne)) :=
      NormalizationFiniteArbitraryField.finite_integralClosure_functionField p ⟨V, hV⟩
    have hB : FiniteDimensional k (Coker Γ(C, V) (closureRing (toNonemptyAffineOpen V hV hne))) :=
      finiteDimensional_coker_of_isFractionRing k (K := C.functionField) Subtype.val_injective
    -- transport along `B ≅ Γ(π⁻¹V, 𝒪_{C̃})`
    let _ : Algebra Γ(C, V) Γ(normalization C, normalizationStructure C ⁻¹ᵁ V) := φ.toAlgebra
    let _ : Algebra k Γ(normalization C, normalizationStructure C ⁻¹ᵁ V) := (φ.comp ψ).toAlgebra
    have : IsScalarTower k Γ(C, V) Γ(normalization C, normalizationStructure C ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let e₀ := (chartSectionsIso (toNonemptyAffineOpen V hV hne)).commRingCatIsoToRingEquiv
    have hcomm : ∀ a : Γ(C, V),
        e₀ (algebraMap Γ(C, V) (closureRing (toNonemptyAffineOpen V hV hne)) a) = φ a := fun a =>
      (RingHom.congr_fun (normalization_app_eq V hV hne) a).symm
    let e : closureRing (toNonemptyAffineOpen V hV hne) ≃ₐ[Γ(C, V)] Γ(normalization C, normalizationStructure C ⁻¹ᵁ V) :=
      { e₀ with commutes' := hcomm }
    have hmap : (LinearMap.range (Algebra.linearMap Γ(C, V) (closureRing (toNonemptyAffineOpen V hV hne)))).map
        e.toLinearEquiv.toLinearMap = LinearMap.range (Algebra.linearMap Γ(C, V)
          Γ(normalization C, normalizationStructure C ⁻¹ᵁ V)) := by
      ext b
      simp only [Submodule.mem_map, LinearMap.mem_range, Algebra.linearMap_apply]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, (e.commutes a).symm⟩
      · rintro ⟨a, rfl⟩
        exact ⟨_, ⟨a, rfl⟩, e.commutes a⟩
    let eQ := Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap
    unfold IsFiniteCoker
    exact Module.Finite.equiv (eQ.restrictScalars k)

/-- **Temkin's genus formula for integral curves** (Lemma B.1 for `|C⁰| = 1`): for an integral
curve `C` (dimension `≤ 1`), projective over a field `k`, with normalization `π : C̃ → C`,
`p_a(C) = p_a(C̃) + ∑ᶠ x, δ(x)`, where `δ(x) = dim_k (π_*𝒪_{C̃} / 𝒪_C)_x` vanishes outside a
finite set of points; and the cohomology of `𝒪_{C̃}` is finite-dimensional. -/
theorem arithmeticGenus_eq_normalization [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] (hdim : topologicalKrullDim C ≤ 1)
    (hp : IsProjectiveOver p) :
    haveI := normalization_isAffineHom p
    haveI := compactSpace_of_isAffineHom (normalizationStructure C)
    haveI := isAffineHom_diagonal_of_isAffineHom (normalizationStructure C)
    (Function.support (deltaInvariant (normalizationStructure C) (structureCoeff p))).Finite ∧
      arithmeticGenus C (structureCoeff p) =
        arithmeticGenus (normalization C)
            ((normalizationStructure C).appTop.hom.comp (structureCoeff p)) +
          ((∑ᶠ x, deltaInvariant (normalizationStructure C) (structureCoeff p) x : ℕ) : ℤ) := by
  have := normalization_isAffineHom p
  have := compactSpace_of_isAffineHom (normalizationStructure C)
  have := isAffineHom_diagonal_of_isAffineHom (normalizationStructure C)
  have hX : ∀ i, FiniteDimensional k
      (cohomology (SheafOfModules.unit C.ringCatSheaf) (structureCoeff p) i) := fun i =>
    finite_cohomology_of_isProjectiveOver hp (SheafOfModules.unit C.ringCatSheaf)
      (fun U _ => Module.Finite.self Γ(C, U)) i
  have h := eulerChar_eq_add_finsum_delta (normalizationStructure C) (structureCoeff p)
    normalization_app_injective (fun V hV => normalization_isFiniteCoker p hdim V hV) hX
  refine ⟨h.2.1, ?_⟩
  rw [arithmeticGenus, arithmeticGenus, h.2.2]
  ring

end Scheme

end DeJongAlterations.StableModification.CurvesField.Genus
