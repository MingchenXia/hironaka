/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricCor

/-!
# The outer normalization is the normalization of `C` (Temkin, Cor. B.2)

Let `f : C' → C` be a proper morphism which is an isomorphism over `U = C ∖ {x}`, `x` not a
generic point of `C`, and let `b : N → C` be the normalization of `C'` in its generic points `η`
with `f η ≠ x`, composed with `f`. If `b` is integral (e.g. finite,
`isFinite_outerNormalization`), then `N` is the normalization `C̃` of `C` (in its generic
points), over `C` (`outerNormalizationIso`). Hence `δ_b = δ_C` and `b⁻¹(x)` is the set `x̃` of
branches of `C` at `x` (`deltaInvariant_outerMap_eq`, `natCard_outerMap_fiber_eq`), and
Corollary B.2 holds with Temkin's `g(x) = dim_k 𝒪_{C̃,x̃}/𝒪_{C,x}` and the semilocal ring
`𝒪_{C̃,x̃}` of the normalization of `C` itself (`stabdown_scheme_normalization`, in Temkin's
form `stabdown_scheme_normalization_iff`: `x` is an ordinary `n`-fold point iff `Z` is a `ℙ¹`-tree
with `|∂Z| = n`; and `stabdown_scheme_normalization_of_isP1Tree` for a disconnected fibre).

The proof is formal: relative normalization only depends on the source up to isomorphism over the
target (`normalizationIsoOfIso`), normalizing in two steps `X → C' → C` with `C̃'_X → C`
integral gives the normalization of the composite (`normalizationCompIso`, by the universal
property `Scheme.Hom.normalizationDesc`), and `∐_{η} Spec κ(η) ≅ ∐_{ξ} Spec κ(ξ)` over `C`
through `f` (`outerPointsIso`).

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, App. B, l. 4376–4378 (the
normalization `π : C̃ → C`, `x̃ = π⁻¹(x)`, `g(x)`), l. 4435–4467 (Corollary B.2)).

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-stabdown-outer-normalization`,
`cor:sm-stabdown-scheme-proof`, `cor:sm-stabdown-scheme-tree`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Module IsLocalRing
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

set_option autoImplicit false

universe u

noncomputable section

section Universal

lemma normalizationIsoOfIso_aux {X X' Y : Scheme.{u}} (g : X ⟶ Y) (g' : X' ⟶ Y) [QuasiCompact g']
    [QuasiSeparated g'] (φ : X ≅ X') (h : φ.hom ≫ g' = g) :
    g = (φ.hom ≫ g'.toNormalization) ≫ g'.fromNormalization := by
  rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h]

/-- **Relative normalization only depends on the source up to isomorphism**: for qcqs
`g : X → Y`, `g' : X' → Y` and `φ : X ≅ X'` with `φ ≫ g' = g`, the normalizations of `g` and
`g'` are isomorphic over `Y`. -/
def normalizationIsoOfIso {X X' Y : Scheme.{u}} (g : X ⟶ Y) (g' : X' ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] (φ : X ≅ X') (h : φ.hom ≫ g' = g) :
    g.normalization ≅ g'.normalization where
  hom := g.normalizationDesc (φ.hom ≫ g'.toNormalization) g'.fromNormalization
    (normalizationIsoOfIso_aux g g' φ h)
  inv := g'.normalizationDesc (φ.inv ≫ g.toNormalization) g.fromNormalization
    (normalizationIsoOfIso_aux g' g φ.symm (by rw [Iso.symm_hom, ← h, Iso.inv_hom_id_assoc]))
  hom_inv_id := by
    refine Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization ?_ ?_ ?_
    · rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, Category.assoc,
        Scheme.Hom.toNormalization_normalizationDesc, Iso.hom_inv_id_assoc, Category.comp_id]
    · rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, Scheme.Hom.normalizationDesc_comp]
    · rw [Category.id_comp]
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext g' _ _ g'.fromNormalization ?_ ?_ ?_
    · rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, Category.assoc,
        Scheme.Hom.toNormalization_normalizationDesc, Iso.inv_hom_id_assoc, Category.comp_id]
    · rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, Scheme.Hom.normalizationDesc_comp]
    · rw [Category.id_comp]

lemma normalizationIsoOfIso_hom_fromNormalization {X X' Y : Scheme.{u}} (g : X ⟶ Y)
    (g' : X' ⟶ Y) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (φ : X ≅ X') (h : φ.hom ≫ g' = g) :
    (normalizationIsoOfIso g g' φ h).hom ≫ g'.fromNormalization = g.fromNormalization :=
  Scheme.Hom.normalizationDesc_comp _ _ _ (normalizationIsoOfIso_aux g g' φ h)

/-- **Normalizing in two steps**: for qcqs `h : X → C'` and `f : C' → C` such that
`C̃'_X → C' → C` is integral, the normalization of `C` in `X` (along `h ≫ f`) is the
normalization `C̃'_X` of `C'` in `X`, over `C`. -/
def normalizationCompIso {X C' C : Scheme.{u}} (h : X ⟶ C') (f : C' ⟶ C) [QuasiCompact h]
    [QuasiSeparated h] [QuasiCompact (h ≫ f)] [QuasiSeparated (h ≫ f)]
    [IsIntegralHom (h.fromNormalization ≫ f)] : (h ≫ f).normalization ≅ h.normalization :=
  let D₁ : (h ≫ f).normalization ⟶ h.normalization :=
    (h ≫ f).normalizationDesc h.toNormalization (h.fromNormalization ≫ f)
      (Scheme.Hom.toNormalization_fromNormalization_assoc h f).symm
  have hD₁ : (h ≫ f).toNormalization ≫ D₁ = h.toNormalization :=
    Scheme.Hom.toNormalization_normalizationDesc _ _ _ _
  have hD₁' : D₁ ≫ h.fromNormalization ≫ f = (h ≫ f).fromNormalization :=
    Scheme.Hom.normalizationDesc_comp _ _ _ _
  let D₂ : h.normalization ⟶ (h ≫ f).normalization :=
    h.normalizationDesc (h ≫ f).toNormalization (D₁ ≫ h.fromNormalization)
      (by rw [← Category.assoc, hD₁, Scheme.Hom.toNormalization_fromNormalization])
  have hD₂ : h.toNormalization ≫ D₂ = (h ≫ f).toNormalization :=
    Scheme.Hom.toNormalization_normalizationDesc _ _ _ _
  have hD₂' : D₂ ≫ D₁ ≫ h.fromNormalization = h.fromNormalization :=
    Scheme.Hom.normalizationDesc_comp _ _ _ _
  { hom := D₁
    inv := D₂
    hom_inv_id := by
      refine Scheme.Hom.normalization.hom_ext (h ≫ f) _ _ (h ≫ f).fromNormalization ?_ ?_ ?_
      · rw [← Category.assoc, hD₁, hD₂, Category.comp_id]
      · calc (D₁ ≫ D₂) ≫ (h ≫ f).fromNormalization =
            D₁ ≫ (D₂ ≫ D₁ ≫ h.fromNormalization) ≫ f := by
              rw [← hD₁']
              simp only [Category.assoc]
          _ = (h ≫ f).fromNormalization := by rw [hD₂']; exact hD₁'
      · rw [Category.id_comp]
    inv_hom_id := by
      refine Scheme.Hom.normalization.hom_ext h _ _ h.fromNormalization ?_ ?_ ?_
      · rw [← Category.assoc, hD₂, hD₁, Category.comp_id]
      · rw [Category.assoc, hD₂']
      · rw [Category.id_comp] }

lemma normalizationCompIso_hom_fromNormalization {X C' C : Scheme.{u}} (h : X ⟶ C') (f : C' ⟶ C)
    [QuasiCompact h] [QuasiSeparated h] [QuasiCompact (h ≫ f)] [QuasiSeparated (h ≫ f)]
    [IsIntegralHom (h.fromNormalization ≫ f)] :
    (normalizationCompIso h f).hom ≫ h.fromNormalization ≫ f = (h ≫ f).fromNormalization :=
  Scheme.Hom.normalizationDesc_comp _ _ _ (Scheme.Hom.toNormalization_fromNormalization_assoc h f).symm

end Universal

section Outer

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (x : C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ≠ x)
  [IsIso (f ∣_ U)]

omit [IsIso (f ∣_ U)] in
include hU in
lemma mem_U_of_mem_outerPoints {η : C'} (hη : η ∈ outerPoints f x) : f η ∈ U :=
  (hU _).2 hη.2

include hU in
/-- **The outer generic points of `C'` are the generic points of `C`**, through `f`. -/
lemma bijective_outerPoints (hxg : x ∉ genericPoints C) :
    Function.Bijective (fun η : outerPoints f x => (⟨f η.1,
      (mem_genericPoints_iff_of_isIso_morphismRestrict f U
        (mem_U_of_mem_outerPoints f x U hU η.2)).1 η.2.1⟩ : genericPoints C)) := by
  refine ⟨fun η η' h => Subtype.ext (injOn_of_isIso_morphismRestrict f U
    (mem_U_of_mem_outerPoints f x U hU η.2) (mem_U_of_mem_outerPoints f x U hU η'.2)
    (congrArg Subtype.val h)), fun ξ => ?_⟩
  have hξx : ξ.1 ≠ x := fun h => hxg (h ▸ ξ.2)
  obtain ⟨η, hη⟩ := exists_eq_of_isIso_morphismRestrict f U ((hU _).2 hξx)
  have hηU : f η ∈ U := hη ▸ (hU _).2 hξx
  have hηg : η ∈ genericPoints C' :=
    (mem_genericPoints_iff_of_isIso_morphismRestrict f U hηU).2 (hη ▸ ξ.2)
  exact ⟨⟨η, hηg, hη ▸ hξx⟩, Subtype.ext hη⟩

/-- The bijection `η ↦ f η` from the outer generic points of `C'` to the generic points of `C`. -/
abbrev outerPointsEquiv (hxg : x ∉ genericPoints C) : outerPoints f x ≃ genericPoints C where
  toFun η := ⟨f η.1, (mem_genericPoints_iff_of_isIso_morphismRestrict f U
    (mem_U_of_mem_outerPoints f x U hU η.2)).1 η.2.1⟩
  invFun := (Equiv.ofBijective _ (bijective_outerPoints f x U hU hxg)).symm
  left_inv := (Equiv.ofBijective _ (bijective_outerPoints f x U hU hxg)).symm_apply_apply
  right_inv := (Equiv.ofBijective _ (bijective_outerPoints f x U hU hxg)).apply_symm_apply

/-- **The points schemes agree**: `∐_{η} Spec κ(η) ≅ ∐_{ξ} Spec κ(ξ)`, through the residue
field isomorphisms `κ(f η) ≅ κ(η)` (`f` is an isomorphism near `η`). -/
def outerPointsIso (hxg : x ∉ genericPoints C) :
    pointsScheme C' (outerPoints f x) ≅ pointsScheme C (genericPoints C) :=
  Sigma.whiskerEquiv (outerPointsEquiv f x U hU hxg) fun η =>
    haveI := isIso_residueFieldMap_of_isIso_morphismRestrict f U η.1
      (mem_U_of_mem_outerPoints f x U hU η.2)
    (asIso (Spec.map (f.residueFieldMap η.1))).symm

lemma outerPointsIso_hom_pointsMap (hxg : x ∉ genericPoints C) :
    (outerPointsIso f x U hU hxg).hom ≫ pointsMap C (genericPoints C) =
      pointsMap C' (outerPoints f x) ≫ f := by
  refine Sigma.hom_ext _ _ fun η => ?_
  have h1 : Sigma.ι (fun η : outerPoints f x => Spec (C'.residueField η.1)) η ≫
      (outerPointsIso f x U hU hxg).hom = Spec.map (f.residueFieldMap η.1) ≫
        Sigma.ι (fun ξ : genericPoints C => Spec (C.residueField ξ.1))
          (outerPointsEquiv f x U hU hxg η) :=
    Sigma.ι_comp_map' _ _ η
  have h2 : Sigma.ι (fun ξ : genericPoints C => Spec (C.residueField ξ.1))
      (outerPointsEquiv f x U hU hxg η) ≫ pointsMap C (genericPoints C) =
        C.fromSpecResidueField (f η.1) :=
    ι_pointsMap _ _ _
  rw [← Category.assoc, h1, Category.assoc, h2, ι_pointsMap_assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

variable [IsAffineHom (pullback.diagonal (terminal.from C'))] [Finite (genericPoints C')]
  [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)]

/-- **The outer normalization is the normalization of `C`**: if `b : N → C` is integral (e.g.
finite), then `N ≅ C̃` over `C`. -/
def outerNormalizationIso [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom (outerMap f x)]
    (hxg : x ∉ genericPoints C) :
    normalizationPoints (outerPoints f x) ≅ normalizationPoints (genericPoints C) :=
  (normalizationCompIso (pointsMap C' (outerPoints f x)) f).symm ≪≫
    normalizationIsoOfIso _ _ (outerPointsIso f x U hU hxg) (outerPointsIso_hom_pointsMap f x U hU hxg)

lemma outerNormalizationIso_hom_comp [QuasiCompact f] [QuasiSeparated f]
    [IsIntegralHom (outerMap f x)] (hxg : x ∉ genericPoints C) :
    (outerNormalizationIso f x U hU hxg).hom ≫ normalizationPointsMap (genericPoints C) =
      outerMap f x := by
  rw [outerNormalizationIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    normalizationIsoOfIso_hom_fromNormalization, ← normalizationCompIso_hom_fromNormalization,
    Iso.inv_hom_id_assoc]

include hU in
/-- **`δ_b = δ_C`**: the δ-invariant of `b : N → C` at any point is that of the normalization of
`C`. -/
theorem deltaInvariant_outerMap_eq {k : Type u} [Field k] [QuasiCompact f] [QuasiSeparated f]
    [IsFinite (outerMap f x)] (hxg : x ∉ genericPoints C) (c : k →+* Γ(C, ⊤)) (y : C) :
    deltaInvariant (outerMap f x) c y =
      deltaInvariant (normalizationPointsMap (genericPoints C)) c y := by
  have : IsAffineHom (normalizationPointsMap (genericPoints C)) := inferInstance
  refine deltaInvariant_eq_of_isOpenImmersion (normalizationPointsMap (genericPoints C))
    (outerNormalizationIso f x U hU hxg).hom (outerMap f x)
    (outerNormalizationIso_hom_comp f x U hU hxg) c y ⊤ trivial ?_
  intro w _
  obtain ⟨w', rfl⟩ := ((ConcreteCategory.bijective_of_isIso
    (outerNormalizationIso f x U hU hxg).hom.base).2 w)
  exact ⟨w', rfl⟩

include hU in
/-- **`b⁻¹(x)` is the set of branches `x̃ = π⁻¹(x)` of `C` at `x`.** -/
theorem natCard_outerMap_fiber_eq [QuasiCompact f] [QuasiSeparated f]
    [IsIntegralHom (outerMap f x)] (hxg : x ∉ genericPoints C) (y : C) :
    Nat.card ↥(outerMap f x ⁻¹' {y}) =
      Nat.card ↥(normalizationPointsMap (genericPoints C) ⁻¹' {y}) := by
  let e := outerNormalizationIso f x U hU hxg
  have hb := ConcreteCategory.bijective_of_isIso e.hom.base
  have hcomp : ∀ w, normalizationPointsMap (genericPoints C) (e.hom w) = outerMap f x w := by
    intro w
    rw [← Scheme.Hom.comp_apply, outerNormalizationIso_hom_comp]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨e.hom w.1, by
    change normalizationPointsMap (genericPoints C) (e.hom w.1) = y
    rw [hcomp]
    exact w.2⟩) ⟨fun w w' h => Subtype.ext (hb.1 (congrArg Subtype.val h)), fun w => ?_⟩)
  obtain ⟨w', hw'⟩ := hb.2 w.1
  refine ⟨⟨w', ?_⟩, Subtype.ext hw'⟩
  change outerMap f x w' = y
  rw [← hcomp, show e.hom w' = w.1 from hw']
  exact w.2

end Outer

section Corollary

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (x : C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ≠ x)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

open scoped Classical in
include hU in
/-- **Temkin, Corollary B.2, scheme level, with the normalization of `C`** (`stabdowncor`,
`semi-stable.tex` l. 4435–4467). In the situation of `stabdown_scheme` (`k = k̄`, `f : C' → C`
proper between reduced projective curves, an isomorphism off the closed point `x`,
`p_a(C') = p_a(C)`, `Z = f⁻¹(x)` a connected curve along which `C'` is semi-stable, nonnegative
genera of the components of `Z`), let `π : C̃ → C` be the normalization of `C`, `V ∋ x` an affine
open, `A` the image of `𝒪_{C,x} = Γ(V, 𝒪_C)_𝔭` in the semilocal ring `B = Γ(π⁻¹V, 𝒪_{C̃})_𝔭 =
𝒪_{C̃,x̃}`, and `Γ = nodalGraph` the incidence graph of `C'` along `Z`. Then
* Temkin's `g(x) = δ_C(x)` is `#∂Z + #inner(Z) + ∑_{v ∈ Z⁰} g(v) - |Z⁰|`,
* `|x̃| = |∂Z|`, and
* `x` is an ordinary (`|∂Z|`-fold) point, in gluing form, iff `Z` is a `ℙ¹`-tree. -/
theorem stabdown_scheme_normalization [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) (hZ : _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
        normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    (deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x : ℤ) =
        contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) G ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) ↔
        (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree G) := by
  obtain ⟨hδ, hbr⟩ := deltaInvariant_eq_contractedDelta_nodalGraph f x U hU p p' hfp hxg hx hdim
    hdim' hp hp' hpa G hG hcurve hnodal hg
  have : IsFinite (outerMap f x) := isFinite_outerNormalization f x U hU p' hdim' hx
  have hδC := deltaInvariant_outerMap_eq f x U hU hxg (structureCoeff p) x
  have hbrC := natCard_outerMap_fiber_eq f x U hU hxg x
  have hconn := isConnected_nodalGraph_fiber f x p' hx hdim' G hG hZ hcurve hnodal
  have : IsFinite (normalizationPointsMap (genericPoints C)) :=
    isFinite_normalizationPointsMap (S := genericPoints C) p
  let _ := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
    (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
      normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints C)) p x hx V hV hxV
      (normalizationPoints_app_injective rfl V hV) (normalizationPoints_isFiniteCoker p rfl hdim V hV)
  have hδC' : (deltaInvariant (normalizationPointsMap (genericPoints C)) (structureCoeff p) x : ℤ) =
      contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) G := by
    rw [← hδC]
    exact hδ
  have hbr' := hcard.trans (hbrC.symm.trans hbr)
  refine ⟨hδC', ?_, stabdown_gluing_iff_of_isAlgClosed _ hres hconn (hdelta ▸ hδC') hbr'⟩
  rw [Nat.card_eq_fintype_card]
  exact hbr'

open scoped Classical in
include hU in
/-- **The usable variant of Corollary B.2 for a disconnected fibre, with the normalization of
`C`** (ERRATA DJA-O7): in the situation of `stabdown_scheme_normalization` without assuming `Z`
connected, if the components `G` of `Z` are partitioned into families whose components pairwise
do not meet and every family is a `ℙ¹`-tree, then there is at most one family (`Z` is connected),
`|x̃| = |∂Z|` and `x` is an ordinary point in gluing form. -/
theorem stabdown_scheme_normalization_of_isP1Tree [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x)
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (𝒴 : Finset (Finset C')) (hsub : ∀ Y ∈ 𝒴, Y ⊆ G)
    (hcov : ∀ v ∈ G, ∃ Y ∈ 𝒴, v ∈ Y)
    (hsep : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → ∀ v ∈ Y, ∀ v' ∈ Y',
      Disjoint (closure ({v} : Set C')) (closure {v'}))
    (htree : ∀ Y ∈ 𝒴, (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree Y)
    (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
        normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    𝒴.card ≤ 1 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) := by
  obtain ⟨hδ, hbr⟩ := deltaInvariant_eq_contractedDelta_nodalGraph f x U hU p p' hfp hxg hx hdim
    hdim' hp hp' hpa G hG hcurve hnodal hg
  obtain ⟨hsum, hbsum⟩ := partition_nodalGraph f x p' hdim' G hG hcurve 𝒴 hsub hcov hsep
  have : IsFinite (outerMap f x) := isFinite_outerNormalization f x U hU p' hdim' hx
  have hδC := deltaInvariant_outerMap_eq f x U hU hxg (structureCoeff p) x
  have hbrC := natCard_outerMap_fiber_eq f x U hU hxg x
  have : IsFinite (normalizationPointsMap (genericPoints C)) :=
    isFinite_normalizationPointsMap (S := genericPoints C) p
  let _ := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
    (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
      normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints C)) p x hx V hV hxV
      (normalizationPoints_app_injective rfl V hV) (normalizationPoints_isFiniteCoker p rfl hdim V hV)
  have hδ' : (delta k (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
      (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) : ℤ) =
      ∑ Y ∈ 𝒴, contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) Y + ((0 : ℕ) : ℤ) := by
    rw [← hdelta, ← hδC, hδ, hsum]
    simp
  have hbr' := hcard.trans (hbrC.symm.trans hbr)
  have hbr'' : (Fintype.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
      Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) : ℤ) =
      ∑ Y ∈ 𝒴, (((nodalGraph p' hdim' (f ⁻¹' {x})).boundary Y).card : ℤ) +
        2 * ((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) := by
    rw [hbr', ← hbsum]
    push_cast
    ring
  obtain ⟨hle, hord⟩ := stabdown_connected_of_isP1Tree _ hres 𝒴 0 0 hδ' hbr'' htree
  refine ⟨by simpa using hle, ?_, ((delta_add_one_eq_card_iff_of_isLocalRing _ hres).1 hord).2⟩
  rw [Nat.card_eq_fintype_card]
  exact hbr'

open scoped Classical in
include hU in
/-- **Temkin, Corollary B.2, in Temkin's form** (`stabdowncor`, l. 4435–4441): under the hypotheses
of `stabdown_scheme_normalization`, `x` is an ordinary `n`-fold point (in gluing form: `x̃` has `n`
points and `𝒪_{C,x}` is the gluing ring of `𝒪_{C̃,x̃}`) if and only if `Z` is a `ℙ¹`-tree with
`|∂Z| = n`. -/
theorem stabdown_scheme_normalization_iff [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [Finite (genericPoints C)] [IsReduced C]
    [CompactSpace C'] [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) (hZ : _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V)
    (n : ℕ) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints C)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints C)).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (genericPoints C),
        normalizationPointsMap (genericPoints C) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    (Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints C), normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) = n ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints C),
              normalizationPointsMap (genericPoints C) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) ↔
      ((nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree G ∧
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card = n) := by
  obtain ⟨-, hcard, hiff⟩ := stabdown_scheme_normalization f x U hU p p' hfp hxg hx hdim hdim'
    hp hp' hpa G hG hZ hcurve hnodal hg V hV hxV
  rw [hcard, hiff, and_comm]

end Corollary

end

end DeJongAlterations.StableModification.CurvesField.Genus
