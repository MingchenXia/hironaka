/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusReducedAlgebra
import DeJongAlterations.StableModification.CurvesField.GenusReducedEuler
import Mathlib.AlgebraicGeometry.Normalization

/-!
# The genus formula for reduced curves (Temkin, Lemma B.1)

Let `C` be a reduced scheme. For a set `S` of points of `C` let `X_S = ∐_{η ∈ S} Spec κ(η)` with
its canonical map `f_S : X_S → C` (`pointsMap`), and let `C̃_S = f_S.normalization` be the relative
normalization of `C` in `X_S` (Mathlib's `Scheme.Hom.normalization`, the relative spectrum of the
integral closure of `𝒪_C` in `(f_S)_* 𝒪_{X_S}`), with `π_S = f_S.fromNormalization : C̃_S → C`.
For `S` the set of generic points of the irreducible components of `C` this is the normalization of
`C` (`normalizationReduced C`): over an affine open `V = Spec A` it is the spectrum of the integral
closure of `A` in `∏_{η ∈ V} κ(η)`, the total ring of fractions of `A`.

## Main results

* `pointsSections_injective`: on an affine open `V`, the values at the points of `S ∩ V` determine
  the sections of `𝒪_{X_S}` over `f_S⁻¹(V)`.
* `isGenericFamily_residueField`: the generic points in an affine open `V = Spec A` of a scheme with
  finitely many irreducible components form a generic family of `A` with their residue fields.
* `normalizationReduced_app_injective`, `normalizationReduced_isFiniteCoker`: for a reduced curve
  `C` locally of finite type over a field `k`, `𝒪_C → π_*𝒪_{C̃}` is injective with
  finite-dimensional cokernel on every affine open (the hypotheses of the δ-formula
  `GenusFormula.eulerChar_eq_add_finsum_delta`).
* `arithmeticGenus_eq_normalizationReduced`: **Temkin's genus formula in δ-form** for a reduced
  projective curve, `p_a(C) = p_a(C̃) + ∑ᶠ x, δ(x)`.
* `eulerChar_normalizationReduced_split`: splitting `S = S₁ ⊔ S₂` splits the normalization,
  `χ(C̃_S) = χ(C̃_{S₁}) + χ(C̃_{S₂})` (`normalizationCoprodIso` and
  `GenusReducedEuler.eulerChar_eq_add_of_isCompl`).

Reference: M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, Lemma B.1 (l. 4413–4433).
Blueprint: `sm-curves-fields-genus-reduced.tex`, `lem:sm-genus-formula-reduced`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology

set_option autoImplicit false

universe u

noncomputable section

section Points

variable (C : Scheme.{u}) (S : Set C)

/-- The disjoint union `X_S = ∐_{η ∈ S} Spec κ(η)` of the spectra of the residue fields at the
points of `S`. -/
abbrev pointsScheme : Scheme.{u} := ∐ fun η : S => Spec (C.residueField η.1)

/-- The canonical morphism `f_S : ∐_{η ∈ S} Spec κ(η) → C`. -/
def pointsMap : pointsScheme C S ⟶ C := Sigma.desc fun η : S => C.fromSpecResidueField η.1

@[reassoc (attr := simp)]
lemma ι_pointsMap (η : S) :
    Sigma.ι (fun η : S => Spec (C.residueField η.1)) η ≫ pointsMap C S =
      C.fromSpecResidueField η.1 :=
  Sigma.ι_desc _ _

variable {C S}

lemma pointsMap_ι_apply (η : S) (y : Spec (C.residueField η.1)) :
    pointsMap C S (Sigma.ι (fun η : S => Spec (C.residueField η.1)) η y) = η.1 := by
  rw [← Scheme.Hom.comp_apply, ι_pointsMap, Scheme.fromSpecResidueField_apply]

variable (C S)

instance [Finite S] [IsAffineHom (pullback.diagonal (terminal.from C))] :
    QuasiCompact (pointsMap C S) := by
  have : QuasiSeparated (terminal.from C) := ⟨inferInstance⟩
  have : QuasiCompact (pointsMap C S ≫ terminal.from C) := by
    rw [terminal.comp_from]
    exact (compactSpace_iff_quasiCompact _).1 inferInstance
  exact QuasiCompact.of_comp _ (terminal.from C)

instance [Finite S] : QuasiSeparated (pointsMap C S) := by
  have : QuasiSeparated (pointsMap C S ≫ terminal.from C) := by
    rw [terminal.comp_from]
    exact (quasiSeparatedSpace_iff_quasiSeparated _).1 inferInstance
  exact QuasiSeparated.of_comp _ (terminal.from C)

end Points

section Residue

variable {C : Scheme.{u}}

/-- The value of a section at a point through `Spec κ(x) → C`: `(fromSpecResidueField x)^♯` is the
residue of the germ. -/
lemma fromSpecResidueField_appLE_ΓSpecIso (V : C.Opens) (x : C) (hx : x ∈ V)
    (h : (⊤ : (Spec (C.residueField x)).Opens) ≤ C.fromSpecResidueField x ⁻¹ᵁ V) :
    (C.fromSpecResidueField x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (C.residueField x)).hom =
      C.presheaf.germ V x hx ≫ C.residue x := by
  have h' : (⊤ : (Spec (C.residueField x)).Opens) ≤
      Spec.map (C.residue x) ⁻¹ᵁ C.fromSpecStalk x ⁻¹ᵁ V := h
  have e1 : (C.fromSpecResidueField x).appLE V ⊤ h = (C.fromSpecStalk x).app V ≫
      (Spec.map (C.residue x)).appLE _ ⊤ h' :=
    Scheme.Hom.comp_appLE (Spec.map (C.residue x)) (C.fromSpecStalk x) V ⊤ h
  rw [e1, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE_assoc]
  have : (Spec.map (C.residue x)).appLE ⊤ ⊤ (Scheme.Hom.preimage_top _).ge =
      (Spec.map (C.residue x)).appTop := rfl
  rw [this, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

end Residue

section Eval

variable {C : Scheme.{u}} {S : Set C}

/-- The component `Spec κ(η) → X_S`. -/
abbrev pointsι (η : S) : Spec (C.residueField η.1) ⟶ pointsScheme C S :=
  Sigma.ι (fun η : S => Spec (C.residueField η.1)) η

lemma le_pointsι_preimage (V : C.Opens) (η : S) (hη : η.1 ∈ V) :
    (⊤ : (Spec (C.residueField η.1)).Opens) ≤ pointsι η ⁻¹ᵁ (pointsMap C S ⁻¹ᵁ V) := by
  intro y _
  change pointsMap C S (pointsι η y) ∈ V
  rw [pointsMap_ι_apply]
  exact hη

/-- The value at `η ∈ S ∩ V` of a section of `𝒪_{X_S}` over `f_S⁻¹(V)`. -/
def pointsEval (V : C.Opens) (η : S) (hη : η.1 ∈ V) :
    Γ(pointsScheme C S, pointsMap C S ⁻¹ᵁ V) ⟶ C.residueField η.1 :=
  (pointsι η).appLE _ ⊤ (le_pointsι_preimage V η hη) ≫ (Scheme.ΓSpecIso _).hom

lemma appLE_eq_of_eq {X Y : Scheme.{u}} {g₁ g₂ : X ⟶ Y} (h : g₁ = g₂) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) (e₂ : V ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U V e₁ = g₂.appLE U V e₂ := by
  subst h
  rfl

/-- `f_S^♯` followed by the value at `η` is the residue of the germ at `η`. -/
lemma app_pointsEval (V : C.Opens) (η : S) (hη : η.1 ∈ V) :
    (pointsMap C S).app V ≫ pointsEval V η hη = C.presheaf.germ V η.1 hη ≫ C.residue η.1 := by
  have e₂ : (⊤ : (Spec (C.residueField η.1)).Opens) ≤ C.fromSpecResidueField η.1 ⁻¹ᵁ V :=
    fun y _ => by
      change C.fromSpecResidueField η.1 y ∈ V
      rw [Scheme.fromSpecResidueField_apply]
      exact hη
  have e₁ : (⊤ : (Spec (C.residueField η.1)).Opens) ≤ (pointsι η ≫ pointsMap C S) ⁻¹ᵁ V :=
    fun y _ => by
      change pointsMap C S (pointsι η y) ∈ V
      rw [pointsMap_ι_apply]
      exact hη
  calc (pointsMap C S).app V ≫ pointsEval V η hη
      = ((pointsMap C S).app V ≫ (pointsι η).appLE _ ⊤ (le_pointsι_preimage V η hη)) ≫
          (Scheme.ΓSpecIso _).hom := (Category.assoc _ _ _).symm
    _ = (pointsι η ≫ pointsMap C S).appLE V ⊤ e₁ ≫ (Scheme.ΓSpecIso _).hom := by
        congr 1
    _ = (C.fromSpecResidueField η.1).appLE V ⊤ e₂ ≫ (Scheme.ΓSpecIso _).hom := by
        congr 1
        exact appLE_eq_of_eq (ι_pointsMap C S η) V ⊤ e₁ e₂
    _ = C.presheaf.germ V η.1 hη ≫ C.residue η.1 :=
        fromSpecResidueField_appLE_ΓSpecIso V η.1 hη e₂

/-- **The values at the points of `S ∩ V` determine a section of `𝒪_{X_S}` over `f_S⁻¹(V)`.** -/
theorem pointsEval_injective (V : C.Opens) (s : Γ(pointsScheme C S, pointsMap C S ⁻¹ᵁ V))
    (hs : ∀ (η : S) (hη : η.1 ∈ V), pointsEval V η hη s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext (pointsScheme C S).sheaf _ s 0 fun x hx => ?_
  obtain ⟨η, y, rfl⟩ : ∃ (η : S) (y : Spec (C.residueField η.1)), pointsι η y = x := by
    obtain ⟨⟨η, y⟩, h⟩ := (sigmaMk fun η : S => Spec (C.residueField η.1)).surjective x
    exact ⟨η, y, (sigmaMk_mk (fun η : S => Spec (C.residueField η.1)) η y).symm.trans h⟩
  have hη : η.1 ∈ V := by
    have := hx
    change pointsMap C S (pointsι η y) ∈ V at this
    rwa [pointsMap_ι_apply] at this
  change (pointsScheme C S).presheaf.germ _ ((pointsι η) y) hx s =
    (pointsScheme C S).presheaf.germ _ ((pointsι η) y) hx 0
  rw [map_zero]
  apply (ConcreteCategory.bijective_of_isIso ((pointsι η).stalkMap y)).1
  rw [map_zero, Scheme.Hom.germ_stalkMap_apply]
  have h0 : (pointsι η).appLE _ ⊤ (le_pointsι_preimage V η hη) s = 0 := by
    have := hs η hη
    rw [pointsEval, CommRingCat.comp_apply] at this
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (C.residueField η.1)).hom).1
      (this.trans (map_zero _).symm)
  have h1 := congrArg ((Spec (C.residueField η.1)).presheaf.germ ⊤ y
    (show y ∈ (⊤ : (Spec (C.residueField η.1)).Opens) from trivial)) h0
  rw [map_zero, Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply] at h1
  exact h1

end Eval

section Generic

variable {C : Scheme.{u}}

/-- The residue map `Γ(V, 𝒪_C) → κ(x)` at a point `x ∈ V`. -/
abbrev residueAt (V : C.Opens) (x : C) (hx : x ∈ V) : Γ(C, V) →+* C.residueField x :=
  (C.presheaf.germ V x hx ≫ C.residue x).hom

/-- The residue map at `x` vanishes exactly on the prime of `x`. -/
lemma residueAt_eq_zero_iff {V : C.Opens} (hV : IsAffineOpen V) (x : C) (hx : x ∈ V) (a : Γ(C, V)) :
    residueAt V x hx a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let _ : Algebra Γ(C, V) (C.presheaf.stalk x) := (C.presheaf.germ V x hx).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨x, hx⟩
  change IsLocalRing.residue _ (C.presheaf.germ V x hx a) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (C.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal a

/-- Every element of `κ(x)` is a fraction `a / t` of sections over `V` with `t(x) ≠ 0`. -/
lemma exists_residueAt_mul_eq {V : C.Opens} (hV : IsAffineOpen V) (x : C) (hx : x ∈ V)
    (z : C.residueField x) : ∃ a t : Γ(C, V), t ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      residueAt V x hx t * z = residueAt V x hx a := by
  let _ : Algebra Γ(C, V) (C.presheaf.stalk x) := (C.presheaf.germ V x hx).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨w, rfl⟩ := C.residue_surjective x z
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl w
  refine ⟨a, t, t.2, ?_⟩
  have h := IsLocalization.mk'_spec (C.presheaf.stalk x) a t
  change C.residue x (C.presheaf.germ V x hx t) * C.residue x _ =
    C.residue x (C.presheaf.germ V x hx a)
  rw [← map_mul, mul_comm]
  exact congrArg (C.residue x) h

/-- Two distinct generic points of `C` lying in an affine open `V` have incomparable primes. -/
lemma not_primeIdealOf_le {V : C.Opens} (hV : IsAffineOpen V) {x y : C} (hx : x ∈ V)
    (hy : y ∈ V) (hyg : y ∈ genericPoints C) (hxy : x ≠ y) :
    ¬ (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro hle
  have hsp : hV.primeIdealOf ⟨x, hx⟩ ⤳ hV.primeIdealOf ⟨y, hy⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hle
  have hsp' : x ⤳ y := by
    have := hsp.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at this
  have h1 : closure {y} ⊆ closure {x} := specializes_iff_closure_subset.1 hsp'
  have h2 : closure {x} ⊆ closure {y} :=
    hyg.2 isIrreducible_singleton.closure h1
  exact hxy ((specializes_iff_closure_subset.2 h2).antisymm hsp').eq.symm

/-- The point of an affine open corresponding to a minimal prime is a generic point. -/
lemma fromSpec_mem_genericPoints {V : C.Opens} (hV : IsAffineOpen V) (q : PrimeSpectrum Γ(C, V))
    (hq : q.asIdeal ∈ minimalPrimes Γ(C, V)) : hV.fromSpec q ∈ genericPoints C := by
  set y := hV.fromSpec q
  have hyV : y ∈ V := by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact Set.mem_range_self q
  let T := irreducibleComponent y
  have hT : T ∈ irreducibleComponents C := irreducibleComponent_mem_irreducibleComponents y
  have hTirr : IsIrreducible T := hT.1
  have hTcl : IsClosed T := isClosed_of_mem_irreducibleComponents T hT
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hTirr hTcl
  have hξy : ξ ⤳ y := by
    rw [specializes_iff_mem_closure, hξ.def]
    exact mem_irreducibleComponent
  have hξV : ξ ∈ V := hξy.mem_open V.2 hyV
  set q' := hV.primeIdealOf ⟨ξ, hξV⟩
  have hq'y : hV.fromSpec q' ⤳ hV.fromSpec q := by
    rw [hV.fromSpec_primeIdealOf]
    exact hξy
  have hle : q'.asIdeal ≤ q.asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2
      ((hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff).1 hq'y)
  have heq : q' = q := PrimeSpectrum.ext (le_antisymm hle (hq.2 ⟨q'.isPrime, bot_le⟩ hle))
  have hξ' : ξ = y := calc
    ξ = hV.fromSpec q' := (hV.fromSpec_primeIdealOf ⟨ξ, hξV⟩).symm
    _ = y := by rw [heq]
  change closure {y} ∈ irreducibleComponents C
  rw [← hξ', hξ.def]
  exact hT

variable (C) in
/-- The generic points of `C` in an affine open `V`, as an index type. -/
abbrev GenericIn (S : Set C) (V : C.Opens) : Type u := {η : S // η.1 ∈ V}

/-- **Points of an affine open with their residue fields form a fraction family.** -/
theorem isFractionFamily_residueField {V : C.Opens} (hV : IsAffineOpen V) (S : Set C) :
    letI : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
      (residueAt V i.1.1 i.2).toAlgebra
    IsFractionFamily (fun i : GenericIn C S V => (hV.primeIdealOf ⟨i.1.1, i.2⟩).asIdeal)
      (fun i => C.residueField i.1.1) := by
  let _ : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
    (residueAt V i.1.1 i.2).toAlgebra
  refine ⟨fun i => ?_, fun i z => ?_⟩
  · ext a
    rw [RingHom.mem_ker]
    exact residueAt_eq_zero_iff hV i.1.1 i.2 a
  · exact exists_residueAt_mul_eq hV i.1.1 i.2 z

/-- **The generic points in an affine open form a generic family.** For an affine open
`V = Spec A` of a scheme `C` and a set `S` of points of `C` equal to the set of generic points of
the irreducible components of `C`, the primes `𝔭_η` (`η ∈ S ∩ V`) with the residue fields `κ(η)`
form a generic family of `A`. -/
theorem isGenericFamily_residueField {V : C.Opens} (hV : IsAffineOpen V) (S : Set C)
    (hS : S = genericPoints C) :
    letI : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
      (residueAt V i.1.1 i.2).toAlgebra
    IsGenericFamily (fun i : GenericIn C S V => (hV.primeIdealOf ⟨i.1.1, i.2⟩).asIdeal)
      (fun i => C.residueField i.1.1) := by
  let _ : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
    (residueAt V i.1.1 i.2).toAlgebra
  refine IsGenericFamily.mk (isFractionFamily_residueField hV S) (fun i j hij => ?_)
    (fun q hq => ?_)
  · refine not_primeIdealOf_le hV i.2 j.2 (hS ▸ j.1.2) fun h => hij ?_
    exact Subtype.ext (Subtype.ext h)
  · let q₀ : PrimeSpectrum Γ(C, V) := ⟨q, hq.1.1⟩
    have hgen := fromSpec_mem_genericPoints hV q₀ hq
    have hyV : hV.fromSpec q₀ ∈ V := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact Set.mem_range_self q₀
    refine ⟨⟨⟨hV.fromSpec q₀, hS ▸ hgen⟩, hyV⟩, ?_⟩
    have : hV.primeIdealOf ⟨hV.fromSpec q₀, hyV⟩ = q₀ :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf _)
    exact congrArg PrimeSpectrum.asIdeal this

end Generic

section Normalization

variable {C : Scheme.{u}} (S : Set C)

/-- The values at the points of `S ∩ V` of the sections of `𝒪_{X_S}` over `f_S⁻¹(V)`. -/
def pointsEvalRingHom (V : C.Opens) :
    Γ(pointsScheme C S, pointsMap C S ⁻¹ᵁ V) →+* ∀ i : GenericIn C S V, C.residueField i.1.1 :=
  RingHom.pi fun i => (pointsEval V i.1 i.2).hom

variable {S}

lemma pointsEvalRingHom_comp (V : C.Opens) :
    (pointsEvalRingHom S V).comp ((pointsMap C S).app V).hom =
      RingHom.pi fun i : GenericIn C S V => residueAt V i.1.1 i.2 := by
  ext a i
  change ((pointsMap C S).app V ≫ pointsEval V i.1 i.2) a = _
  rw [app_pointsEval]
  rfl

lemma pointsEvalRingHom_injective (V : C.Opens) : Function.Injective (pointsEvalRingHom S V) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  exact pointsEval_injective V s fun η hη => congrFun hs ⟨η, hη⟩

variable [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite S]

variable (S) in
/-- The relative normalization `C̃_S` of `C` in `∐_{η ∈ S} Spec κ(η)`. -/
abbrev normalizationPoints : Scheme.{u} := (pointsMap C S).normalization

variable (S) in
/-- The normalization morphism `π_S : C̃_S → C`. -/
abbrev normalizationPointsMap : normalizationPoints S ⟶ C := (pointsMap C S).fromNormalization

variable [IsReduced C]

/-- **`𝒪_C → π_*𝒪_{C̃}` is injective** on affine opens, for `S` the set of generic points of a
reduced scheme. -/
theorem normalizationPoints_app_injective (hS : S = genericPoints C) (V : C.Opens)
    (hV : IsAffineOpen V) : Function.Injective ((normalizationPointsMap S).app V).hom := by
  let _ := ((pointsMap C S).app V).hom.toAlgebra
  let _ : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
    (residueAt V i.1.1 i.2).toAlgebra
  have h := isGenericFamily_residueField hV S hS
  have hA := h.injective_algebraMap
  have hL : Function.Injective (algebraMap Γ(C, V) Γ(pointsScheme C S, pointsMap C S ⁻¹ᵁ V)) := by
    refine Function.Injective.of_comp (f := pointsEvalRingHom S V) ?_
    have : (pointsEvalRingHom S V).comp (algebraMap Γ(C, V) _) = algebraMap Γ(C, V)
        (∀ i : GenericIn C S V, C.residueField i.1.1) := by
      rw [RingHom.algebraMap_toAlgebra, pointsEvalRingHom_comp]
      rfl
    rw [← RingHom.coe_comp, this]
    exact hA
  rw [Scheme.Hom.fromNormalization_app _ hV, CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.bijective_of_isIso ((pointsMap C S).normalizationObjIso hV).inv).1.comp
    ?_
  intro a b hab
  exact hL (congrArg Subtype.val hab)

variable {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

omit [IsReduced C] in
include p in
/-- **The normalization in finitely many points is finite**: for `C` locally of finite type over a
field and `S` a finite set of points, `π_S : C̃_S → C` is a finite morphism (the integral closure of
`Γ(V, 𝒪_C)` in `∏_{η ∈ S ∩ V} κ(η)` is a finite module). -/
theorem isFinite_normalizationPointsMap : IsFinite (normalizationPointsMap S) := by
  refine ⟨fun V hV => ?_⟩
  let ψ := Geometry.NormalizationFinite.affineCoefficientMap p ⟨V, hV⟩
  let _ : Algebra k Γ(C, V) := ψ.toAlgebra
  have : Algebra.FiniteType k Γ(C, V) := Geometry.NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
  let _ := ((pointsMap C S).app V).hom.toAlgebra
  let _ : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
    (residueAt V i.1.1 i.2).toAlgebra
  have h := isFractionFamily_residueField hV S
  have : Finite (GenericIn C S V) := Subtype.finite
  let B := integralClosure Γ(C, V) Γ(pointsScheme C S, pointsMap C S ⁻¹ᵁ V)
  let Φ : B →ₐ[Γ(C, V)] ∀ i : GenericIn C S V, C.residueField i.1.1 :=
    { toRingHom := (pointsEvalRingHom S V).comp (B.val : B →+* _)
      commutes' := fun a => by
        have := congrArg (fun φ => φ a) (pointsEvalRingHom_comp (S := S) V)
        exact this }
  have hΦ : Function.Injective Φ :=
    (pointsEvalRingHom_injective V).comp Subtype.val_injective
  have hfin : Module.Finite Γ(C, V) B := h.finite_of_injective k Φ hΦ
  rw [Scheme.Hom.fromNormalization_app _ hV, CommRingCat.hom_comp]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso ((pointsMap C S).normalizationObjIso hV).inv).2) ?_
  exact hfin

omit [IsReduced C] in
/-- **`π_*𝒪_{C̃} / 𝒪_C` is a finite-dimensional skyscraper**: for a reduced scheme `C` of dimension
`≤ 1`, locally of finite type over `k`, and `S` its set of generic points, `Γ(π⁻¹V, 𝒪_{C̃}) / Γ(V, 𝒪_C)`
is finite-dimensional over `k` for every affine open `V`. -/
theorem normalizationPoints_isFiniteCoker (hS : S = genericPoints C)
    (hdim : topologicalKrullDim C ≤ 1) (V : C.Opens) (hV : IsAffineOpen V) :
    IsFiniteCoker (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))
      ((normalizationPointsMap S).app V).hom := by
  classical
  let ψ := sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)
  let _ : Algebra k Γ(C, V) := ψ.toAlgebra
  have : Algebra.FiniteType k Γ(C, V) := Geometry.NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
  have : Ring.KrullDimLE 1 Γ(C, V) :=
    Geometry.NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
  let _ := ((pointsMap C S).app V).hom.toAlgebra
  let _ : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
    (residueAt V i.1.1 i.2).toAlgebra
  have h := isGenericFamily_residueField hV S hS
  have : Finite (GenericIn C S V) := Subtype.finite
  let B := integralClosure Γ(C, V) Γ(pointsScheme C S, pointsMap C S ⁻¹ᵁ V)
  let Φ : B →ₐ[Γ(C, V)] ∀ i : GenericIn C S V, C.residueField i.1.1 :=
    { toRingHom := (pointsEvalRingHom S V).comp (B.val : B →+* _)
      commutes' := fun a => by
        have := congrArg (fun φ => φ a) (pointsEvalRingHom_comp (S := S) V)
        exact this }
  have hΦ : Function.Injective Φ :=
    (pointsEvalRingHom_injective V).comp Subtype.val_injective
  let _ : Algebra k B := ((algebraMap Γ(C, V) B).comp ψ).toAlgebra
  have : IsScalarTower k Γ(C, V) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hB : FiniteDimensional k (Coker Γ(C, V) B) := h.finiteDimensional_coker k Φ hΦ
  -- transport along `B ≅ Γ(π⁻¹V, 𝒪_{C̃})`
  let φ := ((normalizationPointsMap S).app V).hom
  let B' := Γ(normalizationPoints S, normalizationPointsMap S ⁻¹ᵁ V)
  let _ : Algebra Γ(C, V) B' := φ.toAlgebra
  let _ : Algebra k B' := (φ.comp ψ).toAlgebra
  have : IsScalarTower k Γ(C, V) B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e₀ : B ≃+* B' :=
    ((pointsMap C S).normalizationObjIso hV).symm.commRingCatIsoToRingEquiv
  have hcomm : ∀ a : Γ(C, V), e₀ (algebraMap Γ(C, V) B a) = φ a := fun a => by
    have := congrArg (fun f => f.hom a) (Scheme.Hom.fromNormalization_app (pointsMap C S) hV)
    exact this.symm
  let e : B ≃ₐ[Γ(C, V)] B' := { e₀ with commutes' := hcomm }
  have hmap : (LinearMap.range (Algebra.linearMap Γ(C, V) B)).map e.toLinearEquiv.toLinearMap =
      LinearMap.range (Algebra.linearMap Γ(C, V) B') := by
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

end Normalization

section Noetherian

variable {C : Scheme.{u}} {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include p in
/-- A scheme locally of finite type over a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_locallyOfFiniteType : IsLocallyNoetherian C := by
  refine ⟨fun U => ?_⟩
  let _ := (Geometry.NormalizationFinite.affineCoefficientMap p U).toAlgebra
  have := Geometry.NormalizationFinite.affineSections_finiteType p U
  exact Algebra.FiniteType.isNoetherianRing k Γ(C, U.1)

include p in
/-- A quasi-compact scheme locally of finite type over a field has finitely many irreducible
components, hence finitely many generic points. -/
theorem finite_genericPoints [CompactSpace C] : Finite (genericPoints C) := by
  have := isLocallyNoetherian_of_locallyOfFiniteType p
  have : IsNoetherian C := ⟨⟩
  exact (genericPoints.finite finite_irreducibleComponents_of_isNoetherian).to_subtype

end Noetherian

section Instances

/-- The relative normalization of a qcqs morphism to a quasi-compact scheme is quasi-compact. -/
instance compactSpace_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace Y] : CompactSpace f.normalization :=
  compactSpace_of_isAffineHom f.fromNormalization

/-- The relative normalization of a qcqs morphism to a scheme with affine diagonal has affine
diagonal. -/
instance isAffineHom_diagonal_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] [IsAffineHom (pullback.diagonal (terminal.from Y))] :
    IsAffineHom (pullback.diagonal (terminal.from f.normalization)) :=
  isAffineHom_diagonal_of_isAffineHom f.fromNormalization

end Instances

section Formula

variable {C : Scheme.{u}} [CompactSpace C] [IsAffineHom (pullback.diagonal (terminal.from C))]
  [IsReduced C] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

/-- **Temkin's genus formula in δ-form for reduced curves** (Lemma B.1): for a reduced curve `C`
(dimension `≤ 1`), projective over a field `k`, and `S` its set of generic points, the normalization
`π : C̃ = C̃_S → C` satisfies: the cohomology of `𝒪_{C̃}` is finite-dimensional,
`δ(x) = dim_k (π_*𝒪_{C̃}/𝒪_C)_x` vanishes outside a finite set, and
`p_a(C) = p_a(C̃) + ∑ᶠ x, δ(x)`. -/
theorem arithmeticGenus_eq_normalizationPoints (S : Set C) [Finite S] (hS : S = genericPoints C)
    (hdim : topologicalKrullDim C ≤ 1) (hp : IsProjectiveOver p) :
    (∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit
        (normalizationPoints S).ringCatSheaf)
        ((normalizationPointsMap S).appTop.hom.comp (structureCoeff p)) i)) ∧
      (Function.support (deltaInvariant (normalizationPointsMap S) (structureCoeff p))).Finite ∧
      arithmeticGenus C (structureCoeff p) =
        arithmeticGenus (normalizationPoints S)
            ((normalizationPointsMap S).appTop.hom.comp (structureCoeff p)) +
          ((∑ᶠ x, deltaInvariant (normalizationPointsMap S) (structureCoeff p) x : ℕ) : ℤ) := by
  have hX : ∀ i, FiniteDimensional k
      (cohomology (SheafOfModules.unit C.ringCatSheaf) (structureCoeff p) i) := fun i =>
    finite_cohomology_of_isProjectiveOver hp (SheafOfModules.unit C.ringCatSheaf)
      (fun U _ => Module.Finite.self Γ(C, U)) i
  have h := eulerChar_eq_add_finsum_delta (normalizationPointsMap S)
    (structureCoeff p) (normalizationPoints_app_injective hS)
    (fun V hV => normalizationPoints_isFiniteCoker p hS hdim V hV) hX
  refine ⟨h.1, h.2.1, ?_⟩
  rw [arithmeticGenus, arithmeticGenus, h.2.2]
  ring

/-- The genus formula for the normalization of a reduced curve in its generic points. -/
theorem arithmeticGenus_eq_normalizationReduced [Finite (genericPoints C)]
    (hdim : topologicalKrullDim C ≤ 1) (hp : IsProjectiveOver p) :
    arithmeticGenus C (structureCoeff p) =
      arithmeticGenus (normalizationPoints (genericPoints C))
          ((normalizationPointsMap (genericPoints C)).appTop.hom.comp (structureCoeff p)) +
        ((∑ᶠ x, deltaInvariant (normalizationPointsMap (genericPoints C))
          (structureCoeff p) x : ℕ) : ℤ) :=
  (arithmeticGenus_eq_normalizationPoints p (genericPoints C) rfl hdim hp).2.2

end Formula

section Split

variable {k : Type u} [Field k]

variable {k : Type u} [Field k]

/-- **Normalization in a disjoint union is a disjoint union**: if `X = U ⊔ V`
(`IsColimit (BinaryCofan.mk iU iV)`) and `f : X ⟶ Y` restricts to `gU`, `gV` on `U`, `V`, the
relative normalizations of `gU` and `gV` are complementary open subschemes of that of `f`, over `Y`
(Mathlib's `Scheme.Hom.normalizationCoprodIso`). -/
theorem exists_normalization_split {X Y U V : Scheme.{u}} (f : X ⟶ Y) (iU : U ⟶ X)
    (iV : V ⟶ X) (gU : U ⟶ Y) (gV : V ⟶ Y) (hU : iU ≫ f = gU) (hV : iV ≫ f = gV)
    (e : IsColimit (BinaryCofan.mk iU iV)) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact iU]
    [QuasiSeparated iU] [QuasiCompact iV] [QuasiSeparated iV] [QuasiCompact gU]
    [QuasiSeparated gU] [QuasiCompact gV] [QuasiSeparated gV] :
    ∃ (jU : gU.normalization ⟶ f.normalization) (jV : gV.normalization ⟶ f.normalization)
      (_ : IsOpenImmersion jU) (_ : IsOpenImmersion jV),
      jU ≫ f.fromNormalization = gU.fromNormalization ∧
      jV ≫ f.fromNormalization = gV.fromNormalization ∧
      Disjoint jU.opensRange jV.opensRange ∧ jU.opensRange ⊔ jV.opensRange = ⊤ := by
  subst hU hV
  let E := f.normalizationCoprodIso e
  let jU : (iU ≫ f).normalization ⟶ f.normalization := coprod.inl ≫ E.hom
  let jV : (iV ≫ f).normalization ⟶ f.normalization := coprod.inr ≫ E.hom
  have hjU : jU ≫ f.fromNormalization = (iU ≫ f).fromNormalization :=
    Scheme.Hom.inl_normalizationCoprodIso_hom_fromNormalization f e
  have hjV : jV ≫ f.fromNormalization = (iV ≫ f).fromNormalization :=
    Scheme.Hom.inr_normalizationCoprodIso_hom_fromNormalization f e
  have hdisj : Disjoint jU.opensRange jV.opensRange := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have : (coprod.inl : _ ⟶ (iU ≫ f).normalization ⨿ (iV ≫ f).normalization) a =
        (coprod.inr : _ ⟶ (iU ≫ f).normalization ⨿ (iV ≫ f).normalization) b := by
      apply E.hom.homeomorph.injective
      change (coprod.inl ≫ E.hom) a = (coprod.inr ≫ E.hom) b
      exact ha.trans hb.symm
    exact Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr _ _).1 ⟨a, rfl⟩ ⟨b, rfl⟩ this
  have hcov : jU.opensRange ⊔ jV.opensRange = ⊤ := by
    refine top_unique fun x _ => ?_
    have hx : E.inv x ∈ Set.range (coprod.inl : _ ⟶ (iU ≫ f).normalization ⨿
        (iV ≫ f).normalization) ∪ Set.range (coprod.inr : _ ⟶ (iU ≫ f).normalization ⨿
        (iV ≫ f).normalization) := by
      have hu := codisjoint_iff.1 (isCompl_range_inl_inr (iU ≫ f).normalization
        (iV ≫ f).normalization).2
      have : E.inv x ∈ Set.univ := Set.mem_univ _
      rw [← Set.top_eq_univ, ← hu] at this
      exact this
    have hxx : E.hom (E.inv x) = x := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rcases hx with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine Opens.mem_sup.2 (Or.inl ⟨a, ?_⟩)
      change E.hom ((coprod.inl : (iU ≫ f).normalization ⟶ _) a) = x
      rw [ha, hxx]
    · refine Opens.mem_sup.2 (Or.inr ⟨b, ?_⟩)
      change E.hom ((coprod.inr : (iV ≫ f).normalization ⟶ _) b) = x
      rw [hb, hxx]
  exact ⟨jU, jV, inferInstance, inferInstance, hjU, hjV, hdisj, hcov⟩

/-- **Normalization in a disjoint union splits the Euler characteristic.** If `X = U ⊔ V`
(`IsColimit (BinaryCofan.mk iU iV)`) and `f : X ⟶ Y` restricts to `gU`, `gV` on `U`, `V`, then
`χ(Ỹ_f) = χ(Ỹ_{gU}) + χ(Ỹ_{gV})` for the relative normalizations, provided the cohomology of
`𝒪_{Ỹ_f}` is finite-dimensional (then so is that of the two pieces). -/
theorem eulerChar_normalization_split {X Y U V : Scheme.{u}} (f : X ⟶ Y) (iU : U ⟶ X)
    (iV : V ⟶ X) (gU : U ⟶ Y) (gV : V ⟶ Y) (hU : iU ≫ f = gU) (hV : iV ≫ f = gV)
    (e : IsColimit (BinaryCofan.mk iU iV)) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact iU]
    [QuasiSeparated iU] [QuasiCompact iV] [QuasiSeparated iV] [QuasiCompact gU]
    [QuasiSeparated gU] [QuasiCompact gV] [QuasiSeparated gV] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (c : k →+* Γ(Y, ⊤))
    (hfin : ∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit f.normalization.ringCatSheaf)
      (f.fromNormalization.appTop.hom.comp c) i)) :
    (∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit gU.normalization.ringCatSheaf)
      (gU.fromNormalization.appTop.hom.comp c) i)) ∧
    (∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit gV.normalization.ringCatSheaf)
      (gV.fromNormalization.appTop.hom.comp c) i)) ∧
    eulerChar f.normalization (f.fromNormalization.appTop.hom.comp c) =
      eulerChar gU.normalization (gU.fromNormalization.appTop.hom.comp c) +
        eulerChar gV.normalization (gV.fromNormalization.appTop.hom.comp c) := by
  obtain ⟨jU, jV, _, _, hjU, hjV, hdisj, hcov⟩ := exists_normalization_split f iU iV gU gV hU hV e
  obtain ⟨h₁, h₂, h₃⟩ := eulerChar_eq_add_of_isCompl (f.fromNormalization.appTop.hom.comp c)
    jU jV hdisj hcov hfin
  have hcU : jU.appTop.hom.comp (f.fromNormalization.appTop.hom.comp c) =
      gU.fromNormalization.appTop.hom.comp c := by
    rw [← hjU]
    rfl
  have hcV : jV.appTop.hom.comp (f.fromNormalization.appTop.hom.comp c) =
      gV.fromNormalization.appTop.hom.comp c := by
    rw [← hjV]
    rfl
  rw [hcU] at h₁ h₃
  rw [hcV] at h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

end Split

section PointsSplit

/-- The relative normalization of a morphism from the empty scheme is empty. -/
lemma isEmpty_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsEmpty X] : IsEmpty f.normalization := by
  refine ⟨fun z => ?_⟩
  have hd : Dense (Set.range f.toNormalization) := f.toNormalization.denseRange
  have : (Set.range f.toNormalization).Nonempty := hd.nonempty_iff.2 ⟨z⟩
  obtain ⟨_, x, -⟩ := this
  exact IsEmpty.false x

/-- The Euler characteristic of the empty scheme vanishes. -/
lemma eulerChar_of_isEmpty {k : Type u} [Field k] (X : Scheme.{u}) [IsEmpty X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (c : k →+* Γ(X, ⊤)) :
    eulerChar X c = 0 := by
  have hW : ∀ W : X.Opens, W = ⊥ := fun W => Opens.ext (Set.eq_empty_of_isEmpty _)
  have hsub : ∀ i, Subsingleton (cohomology (SheafOfModules.unit X.ringCatSheaf) c i) := by
    intro i
    refine ModuleCat.subsingleton_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ _ ?_)
    change Limits.IsZero (ModuleCat.of k (Geometry.ProperSteinProjectiveCech.subsetCechCardPiece
      (cechDiagram
      (SheafOfModules.unit X.ringCatSheaf) (FiniteAffineCover.choose X).U c) (i + 1)))
    have : ∀ T : Finset (FiniteAffineCover.choose X).ι, Subsingleton
        ((cechDiagram (SheafOfModules.unit X.ringCatSheaf) (FiniteAffineCover.choose X).U c).obj
          T) := fun T => subsingleton_sectionsModuleCat_unit c (hW _) le_top
    exact ModuleCat.isZero_of_subsingleton _
  rw [eulerChar, homologyEulerChar_eq_sum _ 0 fun i _ => hsub i, Finset.sum_range_zero]

variable {C : Scheme.{u}}

/-- The inclusion `X_{S₁} → X_S` for `S₁ ⊆ S`. -/
def pointsIncl {S₁ S : Set C} (h : S₁ ⊆ S) : pointsScheme C S₁ ⟶ pointsScheme C S :=
  Sigma.desc fun η : S₁ => Sigma.ι (fun η : S => Spec (C.residueField η.1)) ⟨η.1, h η.2⟩

@[reassoc (attr := simp)]
lemma ι_pointsIncl {S₁ S : Set C} (h : S₁ ⊆ S) (η : S₁) :
    Sigma.ι (fun η : S₁ => Spec (C.residueField η.1)) η ≫ pointsIncl h =
      Sigma.ι (fun η : S => Spec (C.residueField η.1)) ⟨η.1, h η.2⟩ :=
  Sigma.ι_desc _ _

@[reassoc (attr := simp)]
lemma pointsIncl_pointsMap {S₁ S : Set C} (h : S₁ ⊆ S) :
    pointsIncl h ≫ pointsMap C S = pointsMap C S₁ :=
  Sigma.hom_ext _ _ fun η => by simp

lemma pointsMap_mem {S : Set C} (z : pointsScheme C S) : pointsMap C S z ∈ S := by
  obtain ⟨⟨η, y⟩, rfl⟩ := (sigmaMk fun η : S => Spec (C.residueField η.1)).surjective z
  rw [sigmaMk_mk, pointsMap_ι_apply]
  exact η.2

instance {S₁ S : Set C} (h : S₁ ⊆ S) : IsOpenImmersion (pointsIncl h) := by
  refine isOpenImmersion_sigmaDesc _ _ fun η η' hne => ?_
  have hne' : (⟨η.1, h η.2⟩ : S) ≠ ⟨η'.1, h η'.2⟩ := fun e =>
    hne (Subtype.ext (by simpa using congrArg Subtype.val e))
  have := disjoint_opensRange_sigmaι (fun η : S => Spec (C.residueField η.1)) _ _ hne'
  rw [← Opens.coe_disjoint] at this
  exact this

lemma mem_range_pointsIncl {S₁ S : Set C} (h : S₁ ⊆ S) (z : pointsScheme C S)
    (hz : pointsMap C S z ∈ S₁) : z ∈ Set.range (pointsIncl h) := by
  obtain ⟨⟨η, y⟩, rfl⟩ := (sigmaMk fun η : S => Spec (C.residueField η.1)).surjective z
  rw [sigmaMk_mk, pointsMap_ι_apply] at hz
  refine ⟨Sigma.ι (fun η : S₁ => Spec (C.residueField η.1)) ⟨η.1, hz⟩ y, ?_⟩
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_pointsIncl]

/-- For `S = S₁ ⊔ S₂`, `X_S` is the disjoint union of `X_{S₁}` and `X_{S₂}`. -/
lemma isCompl_opensRange_pointsIncl {S₁ S₂ : Set C} (hd : Disjoint S₁ S₂) :
    IsCompl (pointsIncl (Set.subset_union_left (s := S₁) (t := S₂))).opensRange
      (pointsIncl (Set.subset_union_right (s := S₁) (t := S₂))).opensRange := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h₁ := pointsMap_mem a
    have h₂ := pointsMap_mem b
    rw [← pointsIncl_pointsMap (Set.subset_union_left (s := S₁) (t := S₂)),
      Scheme.Hom.comp_apply] at h₁
    rw [← pointsIncl_pointsMap (Set.subset_union_right (s := S₁) (t := S₂)),
      Scheme.Hom.comp_apply, hb] at h₂
    exact Set.disjoint_left.1 hd h₁ h₂
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    rcases pointsMap_mem z with hz | hz
    · exact Opens.mem_sup.2 (Or.inl (mem_range_pointsIncl _ z hz))
    · exact Opens.mem_sup.2 (Or.inr (mem_range_pointsIncl _ z hz))

variable [CompactSpace C] [IsAffineHom (pullback.diagonal (terminal.from C))] {k : Type u}
  [Field k]

/-- **Splitting the points splits the normalization**: for disjoint finite sets `S₁`, `S₂` of
points of `C` with union `S`, `χ(C̃_S) = χ(C̃_{S₁}) + χ(C̃_{S₂})`, the cohomology of the pieces
being finite-dimensional when that of `C̃_S` is. -/
theorem eulerChar_normalizationPoints_union (S S₁ S₂ : Set C) [Finite S] [Finite S₁] [Finite S₂]
    (hS : S = S₁ ∪ S₂) (hd : Disjoint S₁ S₂) (c : k →+* Γ(C, ⊤))
    (hfin : ∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit
      (normalizationPoints S).ringCatSheaf) ((normalizationPointsMap S).appTop.hom.comp c) i)) :
    (∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit
      (normalizationPoints S₁).ringCatSheaf) ((normalizationPointsMap S₁).appTop.hom.comp c) i)) ∧
    (∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit
      (normalizationPoints S₂).ringCatSheaf) ((normalizationPointsMap S₂).appTop.hom.comp c) i)) ∧
    eulerChar (normalizationPoints S) ((normalizationPointsMap S).appTop.hom.comp c) =
      eulerChar (normalizationPoints S₁) ((normalizationPointsMap S₁).appTop.hom.comp c) +
        eulerChar (normalizationPoints S₂) ((normalizationPointsMap S₂).appTop.hom.comp c) := by
  subst hS
  obtain ⟨e⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (isCompl_opensRange_pointsIncl hd)
  exact eulerChar_normalization_split (pointsMap C (S₁ ∪ S₂)) _ _ (pointsMap C S₁)
    (pointsMap C S₂) (pointsIncl_pointsMap _) (pointsIncl_pointsMap _) e c hfin

/-- **The Euler characteristic of the normalization is the sum over the points**: for a finite
set `T` of points of `C`, `χ(C̃_T) = ∑_{η ∈ T} χ(C̃_η)`, where `C̃_η` is the normalization of `C`
in `Spec κ(η)` (for a generic point `η`: the normalization of the irreducible component with
generic point `η`). -/
theorem eulerChar_normalizationPoints_eq_sum (T : Finset C) (c : k →+* Γ(C, ⊤))
    (hfin : ∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit
      (normalizationPoints (T : Set C)).ringCatSheaf)
      ((normalizationPointsMap (T : Set C)).appTop.hom.comp c) i)) :
    (∀ η ∈ T, ∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit
      (normalizationPoints ({η} : Set C)).ringCatSheaf)
      ((normalizationPointsMap ({η} : Set C)).appTop.hom.comp c) i)) ∧
    eulerChar (normalizationPoints (T : Set C))
        ((normalizationPointsMap (T : Set C)).appTop.hom.comp c) =
      ∑ η ∈ T, eulerChar (normalizationPoints ({η} : Set C))
        ((normalizationPointsMap ({η} : Set C)).appTop.hom.comp c) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨fun η hη => absurd hη (Finset.notMem_empty η), ?_⟩
    rw [Finset.sum_empty]
    have : IsEmpty (pointsScheme C ((∅ : Finset C) : Set C)) := by
      refine ⟨fun z => ?_⟩
      have := pointsMap_mem z
      simp at this
    have : IsEmpty (normalizationPoints ((∅ : Finset C) : Set C)) :=
      isEmpty_normalization _
    exact eulerChar_of_isEmpty (normalizationPoints ((∅ : Finset C) : Set C)) _
  | insert a T ha ih =>
    have hS : ((insert a T : Finset C) : Set C) = {a} ∪ (T : Set C) := by
      rw [Finset.coe_insert, Set.insert_eq]
    have hd : Disjoint ({a} : Set C) (T : Set C) := by
      rw [Set.disjoint_singleton_left]
      exact_mod_cast ha
    obtain ⟨h₁, h₂, h₃⟩ := eulerChar_normalizationPoints_union _ _ _ hS hd c hfin
    obtain ⟨ih₁, ih₂⟩ := ih h₂
    refine ⟨fun η hη => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hη with rfl | hη
      · exact h₁
      · exact ih₁ η hη
    · rw [h₃, ih₂, Finset.sum_insert ha]

end PointsSplit

section Temkin

variable {C : Scheme.{u}} [CompactSpace C] [IsAffineHom (pullback.diagonal (terminal.from C))]
  {k : Type u} [Field k]

/-- The local contribution `dim_k (B / A)_𝔭` vanishes when every element of `B` is a fraction of
elements of `A` with denominator outside `𝔭`. -/
lemma deltaAt_eq_zero_of_forall {A B : Type u} [CommRing A] [CommRing B] (ψ : k →+* A)
    (φ : A →+* B) (q : PrimeSpectrum A)
    (h : ∀ b : B, ∃ t : A, t ∉ q.asIdeal ∧ ∃ a : A, φ t * b = φ a) : deltaAt ψ φ q = 0 := by
  let _ := ψ.toAlgebra
  let _ := φ.toAlgebra
  let _ := (φ.comp ψ).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change localFinrank k (Coker A B) q = 0
  rw [localFinrank_def]
  have : Subsingleton (LocalizedModule q.asIdeal.primeCompl (Coker A B)) := by
    rw [IsLocalizedModule.subsingleton_iff q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (Coker A B))]
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H b =>
    obtain ⟨t, ht, a, hta⟩ := h b
    refine ⟨t, ht, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by rw [Algebra.linearMap_apply, Algebra.smul_def]; exact hta.symm⟩
  exact Module.finrank_zero_of_subsingleton

omit [CompactSpace C] in
/-- **The δ-invariant vanishes at the generic points**: the normalization is an isomorphism at
the generic points of a reduced scheme (`B` and `A` agree there). -/
theorem deltaInvariant_eq_zero_of_mem_genericPoints (S : Set C) [Finite S]
    (hS : S = genericPoints C) (c : k →+* Γ(C, ⊤)) (η : C) (hη : η ∈ genericPoints C) :
    deltaInvariant (normalizationPointsMap S) c η = 0 := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  rw [← chartDelta_eq_deltaInvariant V hV η hηV]
  refine deltaAt_eq_zero_of_forall _ _ _ fun b' => ?_
  let _ := ((pointsMap C S).app V).hom.toAlgebra
  let _ : ∀ i : GenericIn C S V, Algebra Γ(C, V) (C.residueField i.1.1) := fun i =>
    (residueAt V i.1.1 i.2).toAlgebra
  have h := isGenericFamily_residueField hV S hS
  have : Finite (GenericIn C S V) := Subtype.finite
  let B := integralClosure Γ(C, V) Γ(pointsScheme C S, pointsMap C S ⁻¹ᵁ V)
  let Φ : B →ₐ[Γ(C, V)] ∀ i : GenericIn C S V, C.residueField i.1.1 :=
    { toRingHom := (pointsEvalRingHom S V).comp (B.val : B →+* _)
      commutes' := fun a => by
        have := congrArg (fun φ => φ a) (pointsEvalRingHom_comp (S := S) V)
        exact this }
  have hΦ : Function.Injective Φ :=
    (pointsEvalRingHom_injective V).comp Subtype.val_injective
  let i₀ : GenericIn C S V := ⟨⟨η, hS ▸ hη⟩, hηV⟩
  let e := ((pointsMap C S).normalizationObjIso hV).commRingCatIsoToRingEquiv
  obtain ⟨t, ht, a, ha⟩ := h.exists_smul_mem_range Φ hΦ i₀ (e b')
  refine ⟨t, ht, a, ?_⟩
  have hφ : ∀ x : Γ(C, V), ((normalizationPointsMap S).app V).hom x =
      e.symm (algebraMap Γ(C, V) B x) := fun x =>
    congrArg (fun f => f.hom x) (Scheme.Hom.fromNormalization_app (pointsMap C S) hV)
  rw [hφ, hφ]
  simp only [Algebra.linearMap_apply] at ha
  rw [ha, Algebra.smul_def, map_mul, e.symm_apply_apply]

variable [IsReduced C] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

/-- The genus `g(η) = p_a(C̃_η) = 1 - χ(𝒪_{C̃_η})` of the normalization of the irreducible component
with generic point `η` (Temkin's `g(η)`, the geometric genus `h¹(𝒪_{C̃_η})` when `h⁰ = 1` and
`H^{≥ 2} = 0`). -/
def componentGenus (c : k →+* Γ(C, ⊤)) (η : C) : ℤ :=
  arithmeticGenus (normalizationPoints ({η} : Set C))
    ((normalizationPointsMap ({η} : Set C)).appTop.hom.comp c)

/-- **Temkin's genus formula, Lemma B.1** (`lastlem`, l. 4413–4433): for a reduced curve `C`
(dimension `≤ 1`), projective over a field `k`, with finite set of generic points `C⁰ = G` and
normalization `π : C̃ → C`,
`p_a(C) = 1 - |C⁰| + ∑_{η ∈ C⁰} g(η) + ∑ᶠ_{x ∈ C} δ(x)`,
where `g(η) = p_a(C̃_η)` is the genus of the normalization of the component of `η`
(`componentGenus`), `δ(x) = dim_k (π_*𝒪_{C̃}/𝒪_C)_x = dim_k 𝒪_{C̃,x̃}/𝒪_{C,x}` is Temkin's `g(x)` at
the other points, and `δ` vanishes at the generic points
(`deltaInvariant_eq_zero_of_mem_genericPoints`) and outside a finite set. -/
theorem arithmeticGenus_eq_one_sub_card_add (G : Finset C) (hG : (G : Set C) = genericPoints C)
    (hdim : topologicalKrullDim C ≤ 1) (hp : IsProjectiveOver p) :
    (Function.support (deltaInvariant (normalizationPointsMap (G : Set C))
        (structureCoeff p))).Finite ∧
      arithmeticGenus C (structureCoeff p) =
        1 - G.card + ∑ η ∈ G, componentGenus (structureCoeff p) η +
          ((∑ᶠ x, deltaInvariant (normalizationPointsMap (G : Set C))
            (structureCoeff p) x : ℕ) : ℤ) := by
  obtain ⟨hfin, hsupp, hpa⟩ := arithmeticGenus_eq_normalizationPoints p (G : Set C) hG hdim hp
  obtain ⟨-, hχ⟩ := eulerChar_normalizationPoints_eq_sum G (structureCoeff p) hfin
  refine ⟨hsupp, ?_⟩
  rw [hpa, arithmeticGenus, hχ]
  simp only [componentGenus, arithmeticGenus, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  ring

end Temkin

end

end DeJongAlterations.StableModification.CurvesField.Genus
