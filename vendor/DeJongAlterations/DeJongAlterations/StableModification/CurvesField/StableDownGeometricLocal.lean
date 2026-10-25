/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OrdinaryCompletionLocalization
import DeJongAlterations.StableModification.CurvesField.StableDownSchemeCount
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.Geometry.RegularSmooth

/-!
# The δ-invariant of a reduced curve at smooth points and ordinary double points

Let `X` be a reduced scheme of dimension `≤ 1`, locally of finite type over a field `k`, with
finitely many irreducible components, and let `π : X̃ → X` be its normalization (the
normalization of `X` in its generic points, `Genus.normalizationPointsMap`). For a closed point
`z ∈ X` which is not a generic point:

* `deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint`: **if `z` is an ordinary double point
  (`Ô_{X,z} ≅ k[[u, v]]/(uv)`), then `δ(z) = 1` and `z` has two branches** (the semilocal ring of
  `X̃` over `z` has two maximal ideals);
* `deltaInvariant_eq_zero_of_isSmoothAt`: **if `X → Spec k` is smooth at `z`, then `δ(z) = 0` and
  `z` has one branch.**

These are the values `g(z) = 1` at the double points and `g(z) = 0` at the smooth points used in the
proof of Corollary B.2 of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom.
19 (2010) (`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4442–4446: "the
number of double points on `Z` equals …"), and the branch count `|x̃| = 2` of an ordinary double
point (l. 4382–4383). The local algebra is `CurvesField.OrdinaryCompletion`; this file supplies the
geometric hypotheses on an affine chart `V ∋ z` (`R = Γ(V, 𝒪_X)`, `L` the sections of
`∐_{η} Spec κ(η)` over `V`, and `B = Γ(π⁻¹V, 𝒪_{X̃})`, the integral closure of `R` in `L`):
`B` is finite over `R`, `R → B` is injective (`X` reduced), `B` agrees with `R` at the generic
points, an element of `R` vanishing at no generic point is a unit in `L`
(`isUnit_of_forall_pointsEval_ne_zero`), and the completed local ring of `X` at `z` is the
completion of `R_𝔭` (`completedLocalRingAlgEquiv`).

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-stabdown-delta-node`,
`lem:sm-stabdown-delta-smooth`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module IsLocalRing
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion
open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
open DeJongAlterations.Algebra.CompletionRegularityBasics

set_option autoImplicit false

universe u

noncomputable section

section Units

variable {X : Scheme.{u}} {S : Set X}

/-- **A section of `𝒪_{X_S}` with nonzero values at all points of `S ∩ V` is a unit**: each point
of `X_S` over `V` is the point of some `Spec κ(η)`, `η ∈ S ∩ V`, whose stalk is `κ(η)`. -/
theorem isUnit_of_forall_pointsEval_ne_zero (V : X.Opens)
    (s : Γ(pointsScheme X S, pointsMap X S ⁻¹ᵁ V))
    (hs : ∀ (η : S) (hη : η.1 ∈ V), pointsEval V η hη s ≠ 0) : IsUnit s := by
  refine RingedSpace.isUnit_of_isUnit_germ (pointsScheme X S).toSheafedSpace _ s fun x hx => ?_
  obtain ⟨η, y, rfl⟩ : ∃ (η : S) (y : Spec (X.residueField η.1)), pointsι η y = x := by
    obtain ⟨⟨η, y⟩, h⟩ := (sigmaMk fun η : S => Spec (X.residueField η.1)).surjective x
    exact ⟨η, y, (sigmaMk_mk (fun η : S => Spec (X.residueField η.1)) η y).symm.trans h⟩
  have hη : η.1 ∈ V := by
    have := hx
    change pointsMap X S (pointsι η y) ∈ V at this
    rwa [pointsMap_ι_apply] at this
  let e := (asIso ((pointsι η).stalkMap y)).commRingCatIsoToRingEquiv
  change IsUnit ((pointsScheme X S).presheaf.germ _ ((pointsι η) y) hx s)
  rw [← isUnit_map_iff e]
  change IsUnit (((pointsι η).stalkMap y).hom ((pointsScheme X S).presheaf.germ _ _ hx s))
  rw [Scheme.Hom.germ_stalkMap_apply]
  have ht : IsUnit ((pointsι η).appLE _ ⊤ (le_pointsι_preimage V η hη) s) := by
    have h1 : (Scheme.ΓSpecIso (X.residueField η.1)).hom
        ((pointsι η).appLE _ ⊤ (le_pointsι_preimage V η hη) s) ≠ 0 := by
      have := hs η hη
      rwa [pointsEval, CommRingCat.comp_apply] at this
    have h2 := h1.isUnit
    have h3 := h2.map (Scheme.ΓSpecIso (X.residueField η.1)).inv.hom
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at h3
  have h4 := ht.map ((Spec (X.residueField η.1)).presheaf.germ ⊤ y
    (show y ∈ (⊤ : (Spec (X.residueField η.1)).Opens) from trivial)).hom
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply] at h4
  exact h4

end Units

section Chart

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
  [LocallyOfFiniteType q]

/-- **The local theorems on an affine chart of a reduced curve.** For an affine open `V ∋ z` of a
reduced curve `X` over `k` and a closed point `z ∈ V` which is not generic, with `R = Γ(V, 𝒪_X)`,
`B = Γ(π⁻¹V, 𝒪_{X̃})` and `𝔭` the prime of `z`: if `R_𝔭` has completion `k[[u, v]]/(uv)`, then
`δ(R_𝔭 ⊆ B_𝔭) = 1` and `B_𝔭` has two maximal ideals; if `R_𝔭` is an integrally closed domain, then
`δ(R_𝔭 ⊆ B_𝔭) = 0` and `B_𝔭` has one maximal ideal. -/
theorem chart_core [IsReduced X] (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens)
    (hV : IsAffineOpen V) (z : X) (hz : z ∈ V) (hzc : IsClosed {z})
    (hzg : z ∉ genericPoints X) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
      (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
        normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    (∀ _ : Completion (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) ≃ₐ[k] FormalUV k,
      delta k (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
        (Localization (Algebra.algebraMapSubmonoid Γ(normalizationPoints (genericPoints X),
          normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 1 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 2) ∧
    (IsDomain (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) →
      IsIntegrallyClosed (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) →
      delta k (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
        (Localization (Algebra.algebraMapSubmonoid Γ(normalizationPoints (genericPoints X),
          normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 0 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 1) := by
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
  -- `B ≅ integralClosure R L`
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
  exact ⟨fun e => chart_node ι hι hRB hint pr hsep hunit P hP e,
    fun _ _ => chart_smooth ι hι hRB pr hsep hunit P hP⟩

/-- **The local ring of an affine chart at a point is the stalk, as a `k`-algebra**: for an affine
open `V ∋ z`, `Γ(V, 𝒪_X)_𝔭 ≅ 𝒪_{X,z}`, compatibly with the `k`-algebra structures coming from
`q : X → Spec k`. -/
def localizationAlgEquivStalk (V : X.Opens) (hV : IsAffineOpen V) (z : X) (hz : z ∈ V) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := Scheme.stalkAlgebra q z
    Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal ≃ₐ[k] X.presheaf.stalk z := by
  letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  letI := Scheme.stalkAlgebra q z
  let _ : Algebra Γ(X, V) (X.presheaf.stalk z) := (X.presheaf.germ V z hz).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨z, hz⟩
  let e₀ := IsLocalization.algEquiv (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) (X.presheaf.stalk z)
  refine AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun c => ?_
  rw [IsScalarTower.algebraMap_apply k Γ(X, V) (Localization.AtPrime _)]
  change e₀ (algebraMap Γ(X, V) _ _) = _
  rw [AlgEquiv.commutes]
  change X.presheaf.germ V z hz (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (structureCoeff q c)) = X.presheaf.germ ⊤ z trivial (structureCoeff q c)
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **The completed local ring at `z` is the completion of the local ring of a chart.** -/
def completedLocalRingAlgEquiv (V : X.Opens) (hV : IsAffineOpen V) (z : X) (hz : z ∈ V) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := Scheme.completedLocalRingAlgebra q z
    Completion (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) ≃ₐ[k]
      X.completedLocalRing z := by
  letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  letI := Scheme.stalkAlgebra q z
  let e := localizationAlgEquivStalk q V hV z hz
  exact AdicCompletion.congrAlgEquiv _ _ e
    (IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv).symm

/-- **An ordinary double point of a reduced curve has `δ = 1`** (Temkin, App. B, l. 4392–4393).
Let `X` be a reduced scheme of dimension `≤ 1`, locally of finite type over a field `k`, with
finitely many generic points, and `z` a closed point which is not generic, with
`Ô_{X,z} ≅ k[[u, v]]/(uv)`. Then the δ-invariant of the normalization at `z` is `1`, and in every
affine chart `V ∋ z` the semilocal ring of the normalization over `z` has two maximal ideals. -/
theorem deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X)
    (hnode : Geometry.IsGeometricOrdinaryDoublePoint q z) :
    deltaInvariant (normalizationPointsMap (genericPoints X)) (structureCoeff q) z = 1 ∧
      ∀ (V : X.Opens) (hV : IsAffineOpen V) (hz : z ∈ V),
        letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
        Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 2 := by
  have key : ∀ (V : X.Opens) (hV : IsAffineOpen V) (hz : z ∈ V), _ := fun V hV hz => by
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := Scheme.completedLocalRingAlgebra q z
    exact (chart_core q hdim V hV z hz hzc hzg).1
      ((completedLocalRingAlgEquiv q V hV z hz).trans hnode.some)
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  refine ⟨?_, fun V hV hz => (key V hV hz).2⟩
  rw [deltaInvariant_eq_delta (π := normalizationPointsMap (genericPoints X))
    (c := structureCoeff q) V hV z hzV]
  exact (key V hV hzV).1

/-- **A smooth point of a reduced curve has `δ = 0`**: under the hypotheses of
`deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint`, if `X → Spec k` is smooth at `z`, then
the δ-invariant of the normalization at `z` is `0`, and in every affine chart `V ∋ z` the
semilocal ring of the normalization over `z` is local. -/
theorem deltaInvariant_eq_zero_of_isSmoothAt [IsReduced X] [LocallyOfFinitePresentation q]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X)
    (hsm : DeJong.IsSmoothAt q z) :
    deltaInvariant (normalizationPointsMap (genericPoints X)) (structureCoeff q) z = 0 ∧
      ∀ (V : X.Opens) (hV : IsAffineOpen V) (hz : z ∈ V),
        letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
        Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl))) = 1 := by
  have hreg : IsRegularLocalRing (X.presheaf.stalk z) :=
    Geometry.RegularSmooth.isRegularLocalRing_of_mem_smoothLocus q z hsm
  have key : ∀ (V : X.Opens) (hV : IsAffineOpen V) (hz : z ∈ V), _ := fun V hV hz => by
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := Scheme.stalkAlgebra q z
    have : IsRegularLocalRing (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) :=
      IsRegularLocalRing.of_ringEquiv (localizationAlgEquivStalk q V hV z hz).toRingEquiv.symm
    have : Ring.KrullDimLE 1 Γ(X, V) :=
      Geometry.NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
    have : Ring.KrullDimLE 1 (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) :=
      krullDimLE_localization _
    obtain ⟨h1, h2⟩ := isDomain_isIntegrallyClosed_of_isRegularLocalRing
      (A := Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal)
    exact (chart_core q hdim V hV z hz hzc hzg).2 h1 h2
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  refine ⟨?_, fun V hV hz => (key V hV hz).2⟩
  rw [deltaInvariant_eq_delta (π := normalizationPointsMap (genericPoints X))
    (c := structureCoeff q) V hV z hzV]
  exact (key V hV hzV).1

end Chart

end

end DeJongAlterations.StableModification.CurvesField.Genus
