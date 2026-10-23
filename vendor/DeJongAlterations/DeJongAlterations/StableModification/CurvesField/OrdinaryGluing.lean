/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OrdinaryGluingLocal
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricCor
import DeJongAlterations.StableModification.BlowDown.StabilityFibre
import DeJongAlterations.Geometry.RegularSmoothConverse

/-!
# Ordinary points in gluing form are smooth points or ordinary double points (scheme level)

Let `X` be a reduced curve over an algebraically closed field `k` (reduced, of dimension `≤ 1`,
locally of finite type, with finitely many generic points), `π : X̃ → X` its normalization and
`z ∈ X` a closed point which is not generic. M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification/source/semi-stable.tex`,
App. B, l. 4381–4397) characterizes the ordinary `n`-fold points, defined by
`𝒪̂_{X,z} ≅ k[[T₁, …, Tₙ]]/(TᵢTⱼ)_{i ≠ j}`, by `g(z) = |z̃| - 1`, equivalently by the gluing form
`𝒪_{X,z} = Gl(𝒪_{X̃,z̃})`. CRV4 proved "completed ⇒ gluing" for `n ≤ 2`
(`Genus.eq_gluing_of_isGeometricOrdinaryDoublePoint`, `Genus.eq_gluing_of_isSmoothAt`). This file
proves the converse for `n ≤ 2`:

* `isGeometricOrdinaryDoublePoint_of_eq_gluing`: if the semilocal ring `B` of `X̃` over `z` (on an
  affine chart) has two maximal ideals and `𝒪_{X,z}` is its gluing ring, then `z` is an ordinary
  double point, `𝒪̂_{X,z} ≅ k[[u, v]]/(uv)` (Codex's `Geometry.IsGeometricOrdinaryDoublePoint`);
* `isSmoothAt_of_eq_gluing`: if `B` is local and `𝒪_{X,z}` is its gluing ring, then `X → Spec k` is
  smooth at `z` (`DeJong.IsSmoothAt`);
* `ordinaryPointCompletion_of_isAlgClosed`: **the δ-form consumed by the stability criterion**,
  T44A2's `BlowDown.OrdinaryPointCompletion k`: a closed, non-generic point `z` with
  `δ(z) + 1 = |z̃|` is smooth if `|z̃| = 1` and an ordinary double point if `|z̃| = 2`.

The local algebra is `CurvesField.OrdinaryGluingLocal`; this file supplies its hypotheses on an
affine chart `V ∋ z` exactly as CRV4's `Genus.chart_core` does (`R = Γ(V, 𝒪_X)`,
`B = Γ(π⁻¹V, 𝒪_{X̃})`,
the integral closure of `R` in the ring `L` of the generic points of `V`, a conductor element
`s ∈ 𝔭_z` invertible in `L`), and the conversions δ-form ⇔ gluing form of
`Genus.finite_local_inputs` and `CurvesField.delta_add_one_eq_card_iff_of_isLocalRing`.

Blueprint: `sm-curves-fields-ordinary-gluing.tex`, `thm:sm-og-scheme`, `cor:sm-og-delta`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryGluing

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module IsLocalRing
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField.Genus
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion
open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
open DeJongAlterations.Algebra.CompletionRegularityBasics

set_option autoImplicit false

universe u

noncomputable section

section Chart

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
  [LocallyOfFiniteType q]

/-- **The local theorems of `OrdinaryGluingLocal` on an affine chart of a reduced curve.** For an
affine open `V ∋ z` of a reduced curve `X` over `k` and a closed point `z ∈ V` which is not
generic, with `R = Γ(V, 𝒪_X)`, `B = Γ(π⁻¹V, 𝒪_{X̃})` and `𝔭` the prime of `z`: if all residue
fields of `B_𝔭` are `k` and `R_𝔭` is the gluing subalgebra of `B_𝔭`, then `R_𝔭` has completion
`k[[u, v]]/(uv)` when `B_𝔭` has two maximal ideals, and `R_𝔭` is a discrete valuation ring when
`B_𝔭` has one. -/
theorem chart_gluing [IsReduced X] (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens)
    (hV : IsAffineOpen V) (z : X) (hz : z ∈ V) (hzc : IsClosed {z})
    (hzg : z ∉ genericPoints X) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
      (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
        normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    (∀ m : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)),
      Function.Surjective (algebraMap k (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl) ⧸ m.asIdeal))) →
    rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
        (Localization (Algebra.algebraMapSubmonoid Γ(normalizationPoints (genericPoints X),
          normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)) =
      gluing k (Localization (Algebra.algebraMapSubmonoid Γ(normalizationPoints (genericPoints X),
          normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)) →
    (Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 2 →
      Nonempty (Completion (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) ≃ₐ[k]
        FormalUV k)) ∧
    (Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 1 →
      ∃ _ : IsDomain (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal),
        IsDiscreteValuationRing (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)) := by
  set S := genericPoints X
  let R := Γ(X, V)
  let B := Γ(normalizationPoints S, normalizationPointsMap S ⁻¹ᵁ V)
  let L := Γ(pointsScheme X S, pointsMap X S ⁻¹ᵁ V)
  let _ : Algebra k R := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  let _ : Algebra R B := ((normalizationPointsMap S).app V).hom.toAlgebra
  let _ : Algebra k B := (((normalizationPointsMap S).app V).hom.comp
    (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra R L := ((pointsMap X S).app V).hom.toAlgebra
  -- `B ≅ integralClosure R L` (as in `Genus.chart_core`)
  obtain ⟨iso, hisodef⟩ : ∃ iso, iso = (pointsMap X S).normalizationObjIso hV := ⟨_, rfl⟩
  have happ := Scheme.Hom.fromNormalization_app (pointsMap X S) hV
  rw [← hisodef] at happ
  have hiso : ∀ a : R, iso.hom.hom (algebraMap R B a) = algebraMap R (integralClosure R L) a := by
    intro a
    have h := congrArg (fun f => (f ≫ iso.hom).hom a) happ
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    exact h
  let ι : B →ₐ[R] L :=
    { toRingHom := (integralClosure R L).val.toRingHom.comp iso.hom.hom
      commutes' := fun a => by
        change ((integralClosure R L).val (iso.hom.hom (algebraMap R B a))) = _
        rw [hiso]
        rfl }
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (ConcreteCategory.bijective_of_isIso iso.hom).1
  have hint : ∀ y : L, IsIntegral R y → y ∈ ι.range := by
    intro y hy
    refine ⟨iso.inv.hom ⟨y, hy⟩, ?_⟩
    change ((iso.inv ≫ iso.hom).hom ⟨y, hy⟩ : L) = y
    rw [Iso.inv_hom_id]
    rfl
  have hRB : Function.Injective (algebraMap R B) :=
    normalizationPoints_app_injective (S := S) rfl V hV
  have : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap (S := S) q
  have hfin : Module.Finite R B := IsFinite.finite_app (normalizationPointsMap S) V hV
  -- the generic points of `V`
  let pr : GenericIn X S V → Ideal R := fun i => (hV.primeIdealOf ⟨i.1.1, i.2⟩).asIdeal
  have : Finite (GenericIn X S V) := Subtype.finite
  let _ : ∀ i : GenericIn X S V, Algebra R (X.residueField i.1.1) := fun i =>
    (residueAt V i.1.1 i.2).toAlgebra
  have hgen := isGenericFamily_residueField hV S rfl
  let Φ : B →ₐ[R] ∀ i : GenericIn X S V, X.residueField i.1.1 :=
    { toRingHom := (pointsEvalRingHom S V).comp ι.toRingHom
      commutes' := fun a => by
        have := congrArg (fun φ => φ a) (pointsEvalRingHom_comp (S := S) V)
        change (pointsEvalRingHom S V) (ι (algebraMap R B a)) = _
        rw [ι.commutes]
        exact this }
  have hΦ : Function.Injective Φ := (pointsEvalRingHom_injective V).comp hι
  have hsep : ∀ i (b : B), ∃ t : R, t ∉ pr i ∧ t • b ∈ LinearMap.range (Algebra.linearMap R B) :=
    fun i b => hgen.exists_smul_mem_range Φ hΦ i b
  have hunit : ∀ r : R, (∀ i, r ∉ pr i) → IsUnit (algebraMap R L r) := by
    intro r hr
    refine isUnit_of_forall_pointsEval_ne_zero V _ fun η hη h0 => hr ⟨η, hη⟩ ?_
    have h1 := congrArg (fun f => f.hom r) (app_pointsEval (S := S) V η hη)
    change pointsEval V η hη (((pointsMap X S).app V).hom r) = residueAt V η.1 hη r at h1
    change pointsEval V η hη (((pointsMap X S).app V).hom r) = 0 at h0
    rw [h1] at h0
    exact (residueAt_eq_zero_iff hV η.1 hη r).1 h0
  -- the prime of `z`
  set P := (hV.primeIdealOf ⟨z, hz⟩).asIdeal
  have hPmax : P.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨z, hz⟩ hzc
  have hP : ∀ i, ¬ P ≤ pr i := by
    intro i hle
    have heq : P = pr i := hPmax.eq_of_le (hgen.isPrime i).ne_top hle
    have : hV.primeIdealOf ⟨z, hz⟩ = hV.primeIdealOf ⟨i.1.1, i.2⟩ := PrimeSpectrum.ext heq
    have hzη : z = i.1.1 := calc
      z = hV.fromSpec (hV.primeIdealOf ⟨z, hz⟩) := (hV.fromSpec_primeIdealOf ⟨z, hz⟩).symm
      _ = hV.fromSpec (hV.primeIdealOf ⟨i.1.1, i.2⟩) := by rw [this]
      _ = i.1.1 := hV.fromSpec_primeIdealOf _
    exact hzg (hzη ▸ i.1.2)
  have : Algebra.FiniteType k R :=
    Geometry.NormalizationFinite.affineSections_finiteType q ⟨V, hV⟩
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : Ring.KrullDimLE 1 R :=
    Geometry.NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
  have : Ring.KrullDimLE 1 (Localization.AtPrime P) := krullDimLE_localization P
  -- the localized data at `𝔭`
  obtain ⟨s, hsP, hs, -⟩ := exists_conductor_mem pr hsep P hP
  have hsm : algebraMap R (Localization.AtPrime P) s ∈ maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P s).2 hsP
  have hAB := algebraMap_localization_injective P hRB
  have hι' := localizedAlgHom_injective ι P hι
  have hsL := isUnit_algebraMap_localization (T := L) P (hunit s hs)
  have hint' := mem_range_localizedAlgHom_of_isIntegral ι P hint
  intro hres hgl
  refine ⟨fun h2 => ?_, fun h1 => ?_⟩
  · exact nonempty_completion_algEquiv_formalUV_of_gluing hAB (localizedAlgHom ι P) hι' hint' hsm
      hsL hres hgl h2
  · exact exists_isDiscreteValuationRing_of_surjective
      (algebraMap_surjective_of_gluing hres hgl h1) hAB (localizedAlgHom ι P) hι' hint' hsm hsL

end Chart

section Points

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [IsReduced X] {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
  [LocallyOfFiniteType q]

/-- **The residue fields of the normalization over a closed point are `k`** (`k = k̄`) when the
local ring is contained in the gluing ring: the residue fields are finite over `k`
(`CurvesField.finiteDimensional_residue`). -/
theorem residue_surjective_of_le_gluing [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B]
    [Fintype (MaximalSpectrum B)] (A : Subalgebra k B) (hA : A ≤ gluing k B)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] (m : MaximalSpectrum B) :
    Function.Surjective (algebraMap k (B ⧸ m.asIdeal)) := by
  have := finiteDimensional_residue A hA m
  let _ : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have : Algebra.IsIntegral k (B ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ m.asIdeal)).2

/-- **An ordinary `2`-fold point in gluing form is an ordinary double point** (Temkin, App. B,
l. 4381–4387; blueprint `lem:sm-ordinary-completion`, "⇐" for `n = 2`; the converse of CRV4's
`Genus.eq_gluing_of_isGeometricOrdinaryDoublePoint`): for a reduced curve `X` over `k = k̄`, a
closed point `z` which is not generic, an affine open `V ∋ z`, and `A` the image of `𝒪_{X,z}` in the
semilocal ring `B = Γ(π⁻¹V, 𝒪_{X̃})_𝔭` of the normalization: if `B` has two maximal ideals and `A`
is the gluing ring of `B`, then `Ô_{X,z} ≅ k[[u, v]]/(uv)`. -/
theorem isGeometricOrdinaryDoublePoint_of_eq_gluing [IsAlgClosed k]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X)
    (V : X.Opens) (hV : IsAffineOpen V) (hzV : z ∈ V) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
      (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
        normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl))) = 2 →
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨z, hzV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) →
      Geometry.IsGeometricOrdinaryDoublePoint q z := by
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  let _ := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
    (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
      normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro h2 hgl
  obtain ⟨_, _, _, _, -, -, -⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints X)) q z hzc V hV hzV
      (normalizationPoints_app_injective rfl V hV)
      (normalizationPoints_isFiniteCoker q rfl hdim V hV)
  obtain ⟨e⟩ := (chart_gluing q hdim V hV z hzV hzc hzg
    (residue_surjective_of_le_gluing _ hgl.le) hgl).1 h2
  let _ := Scheme.completedLocalRingAlgebra q z
  exact ⟨(completedLocalRingAlgEquiv q V hV z hzV).symm.trans e⟩

/-- **An ordinary `1`-fold point in gluing form is a smooth point** (blueprint
`lem:sm-ordinary-completion`, "⇐" for `n = 1`; the converse of CRV4's
`Genus.eq_gluing_of_isSmoothAt`):
under the hypotheses of `isGeometricOrdinaryDoublePoint_of_eq_gluing`, if the semilocal ring `B` of
the normalization over `z` is local and `A` is its gluing ring, then `𝒪_{X,z}` is a discrete
valuation ring, hence regular, and `X → Spec k` is smooth at `z`. -/
theorem isSmoothAt_of_eq_gluing [IsAlgClosed k]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X)
    (V : X.Opens) (hV : IsAffineOpen V) (hzV : z ∈ V) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
      (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
        normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl))) = 1 →
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨z, hzV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) →
      DeJong.IsSmoothAt q z := by
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  let _ := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
    (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
      normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro h1 hgl
  obtain ⟨_, _, _, _, -, -, -⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints X)) q z hzc V hV hzV
      (normalizationPoints_app_injective rfl V hV)
      (normalizationPoints_isFiniteCoker q rfl hdim V hV)
  obtain ⟨_, _⟩ := (chart_gluing q hdim V hV z hzV hzc hzg
    (residue_surjective_of_le_gluing _ hgl.le) hgl).2 h1
  let _ := Scheme.stalkAlgebra q z
  have hreg : IsRegularLocalRing (X.presheaf.stalk z) :=
    IsRegularLocalRing.of_ringEquiv (localizationAlgEquivStalk q V hV z hzV).toRingEquiv
  exact Geometry.RegularSmoothConverse.formallySmooth_stalkMap_of_isRegularLocalRing q z hreg

end Points

/-- **The converse of the ordinary-completion lemma for `n ≤ 2`, in the δ-form consumed by the
stability criterion** (T44A2's `BlowDown.OrdinaryPointCompletion k`; blueprint
`lem:sm-ordinary-completion`, "⇐" for `n = 1, 2`; Temkin, App. B, l. 4381–4397): over an
algebraically closed field `k`, a closed point `x` of a reduced curve `C`, not a generic point,
with `δ(x) + 1 = |x̃|` is a smooth point if `|x̃| = 1` and an ordinary double point
(`𝒪̂_{C,x} ≅ k[[u, v]]/(uv)`) if `|x̃| = 2`. -/
theorem ordinaryPointCompletion_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] :
    BlowDown.OrdinaryPointCompletion k := by
  intro C _ _ _ _ p _ hdim x hxc hxg hδ
  have : IsFinite (normalizationPointsMap (genericPoints C)) :=
    isFinite_normalizationPointsMap (S := genericPoints C) p
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let _ := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
    (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
      normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints C)) p x hxc V hV hxV
      (normalizationPoints_app_injective rfl V hV)
      (normalizationPoints_isFiniteCoker p rfl hdim V hV)
  have hgl := ((delta_add_one_eq_card_iff_of_isLocalRing _ hres).1
    (by rw [← hdelta, hcard]; exact hδ)).2
  have hcard' : Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {x}) =
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) :=
    hcard.symm.trans Nat.card_eq_fintype_card.symm
  refine ⟨fun h1 => isSmoothAt_of_eq_gluing p hdim x hxc hxg V hV hxV (hcard' ▸ h1) hgl,
    fun h2 => isGeometricOrdinaryDoublePoint_of_eq_gluing p hdim x hxc hxg V hV hxV
      (hcard' ▸ h2) hgl⟩

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryGluing
