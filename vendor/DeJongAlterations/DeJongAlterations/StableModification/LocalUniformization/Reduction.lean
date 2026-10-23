import DeJongAlterations.StableModification.ValCurves.ModificationsFiniteness
import DeJongAlterations.StableModification.Curves.StandardModels

/-!
# Reduction of cofinality to a single valuation (Temkin, proof of Proposition 4.3.1)

Let `S` be a scheme whose local rings are valuation rings, `φ : C → S` a quasi-compact separated
relative curve with `C` integral, and `𝔊 = RZ_L(C)`, `L = K(C)`. M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), Proposition 4.3.1 (`cofinprop`, `semi-stable.tex`
lines 2956–2966) states that for `C` strictly semi-stable with smooth generic fibre, strictly
semi-stable blow-ups of `C` are cofinal among all modifications. Its proof begins:

> it is enough to prove the following claim: for any element `𝔵 ∈ 𝔊⁰₀` there exists a strictly
> semi-stable blow up `h : C' → C` such that `𝔵 ∈ Γ₀(C')`. Indeed, [...] given any finite subset
> `F ⊂ 𝔊⁰₀` we can apply the claim iteratively [...]. Then Proposition 4.3.1 would follow from
> Proposition 4.2.3 and normality of semi-stable `S`-curves with smooth generic fiber.

This file formalizes that reduction (`lem:sm-cofinal-reduction` of the blueprint chapter
`sm-local-uniformization-model.tex`).

## Main definitions

* `unionGammaSet φ`: the union of the sets `Γ(C')` over all modifications `C' → C`. Temkin remarks
  (T:2881–2883, "although we will not use that") that this union is `𝔊⁰`; we only use that the
  points of `Γ₀(C')` lie in it.
* `CentreClaim φ`: Temkin's claim, in the relative form needed for the iteration: for every
  strictly semi-stable modification `f₁ : C₁ → C` and every `V ∈ ⋃ Γ(C')` whose centre `x₁` on `C₁`
  is a closed point of `C₁`, there is a strictly semi-stable modification `C₂ → C` dominating `C₁`
  with `V ∈ Γ(C₂)`.

## Main results

* `mem_fibreGenericSet_or_isClosed`: if `V ∈ 𝔊` has closed centre on `C`, its centre on a
  modification `C₁` is either in `(C₁/S)⁰` or a closed point of `C₁` (Temkin, T:2970–2971: "if at
  some stage `x` is not a closed point of its fiber then it is already a generic point of its
  `S`-fiber").
* `gammaSet_subset_of_dominates`, `gammaZeroSet_subset_of_dominates`: `Γ` and `Γ₀` grow along
  domination.
* `exists_subset_gammaZeroSet`: **the iteration** — under `CentreClaim φ`, for every finite set
  `F` of points of `⋃ Γ(C')` with closed centre on `C` there is a strictly semi-stable modification
  `C₁ → C` with `F ⊆ Γ₀(C₁)`.
* `exists_dominates_of_finite_gammaZeroSet`, `exists_dominates_of_isNormalScheme`: **cofinality**
  — every modification `C' → C` with finite `Γ₀(C')` (for instance a normal one over a base of
  finite height, `ValCurves.finite_gammaZeroSet`) is dominated by a strictly semi-stable
  modification, provided strictly semi-stable modifications of `C` are normal.

## Adaptations

* Normality of strictly semi-stable curves with smooth generic fibre (Temkin's Proposition 3.5.2,
  the blueprint's `thm:sm-semistable-normal`, lane SS2) enters as the explicit hypothesis
  `hnormal` (a hypothesis of the theorem, neither a definition nor an axiom).
* Temkin iterates blow-ups, which compose (Conrad 1.2); here the claim directly provides a strictly
  semi-stable modification of `C` dominating the intermediate one (in applications the composite
  `C₂ → C₁ → C`, a modification by `IsModification.comp`); whether it is a blow-up is not needed
  downstream.
* Temkin applies the claim to `𝔵 ∈ 𝔊⁰₀` with respect to the intermediate curve `C₁`; since the
  centre on `C₁` of a point of `𝔊⁰₀` need not be closed in `C₁` but is then in `(C₁/S)⁰`
  (`mem_fibreGenericSet_or_isClosed`), the claim is only needed for closed centres.
* Cofinality is stated for modifications `C'` with `Γ₀(C')` finite. Temkin asserts it for all
  modifications; finiteness of `Γ₀(C')` for non-normal `C'` (T:2915 states it for normal `C'`)
  is not needed in the Claude route (consumers dominate normal modifications).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open ValCurves Curves

variable {S C : Scheme.{u}} (φ : C ⟶ S) [IsIntegral C]

/-- The union of Temkin's sets `Γ(C')` (T:2873) over all modifications `C' → C`: the points of
`𝔊 = RZ_{K(C)}(C)` centred, on some modification `C'`, at a point of `(C'/S)⁰`. By Temkin's remark
(T:2881–2883) this is the set `𝔊⁰`. -/
def unionGammaSet : Set (RiemannZariskiSpace C.functionField) :=
  {V | ∃ (C' : Scheme.{u}) (_ : IsIntegral C') (f' : C' ⟶ C) (_ : IsModification f'),
    V ∈ gammaSet (f' ≫ φ) (genericLift f')}

theorem mem_unionGammaSet_of_mem_gammaZeroSet {C' : Scheme.{u}} [IsIntegral C'] (f' : C' ⟶ C)
    [IsModification f'] {V : RiemannZariskiSpace C.functionField}
    (hV : V ∈ gammaZeroSet (f' ≫ φ) (genericLift f') (genericPt C)) : V ∈ unionGammaSet φ :=
  ⟨C', inferInstance, f', inferInstance, hV.1⟩

/-- **Temkin's claim** in the proof of Proposition 4.3.1 (T:2961–2963), in the relative form used by
the iteration: for every strictly semi-stable modification `f₁ : C₁ → C` and every point
`V ∈ ⋃ Γ(C')` centred at a closed point `x₁` of `C₁`, there is a strictly semi-stable
modification `f₂ : C₂ → C` dominating `f₁` such that `V ∈ Γ(C₂)`. -/
def CentreClaim : Prop :=
  ∀ ⦃C₁ : Scheme.{u}⦄ [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁],
    IsStrictlySemistable (f₁ ≫ φ) ⊤ →
    ∀ (V : RiemannZariskiSpace C.functionField) (x₁ : C₁), V ∈ unionGammaSet φ →
      IsClosed ({x₁} : Set C₁) → IsCentre (genericLift f₁) V x₁ →
      ∃ (C₂ : Scheme.{u}) (_ : IsIntegral C₂) (f₂ : C₂ ⟶ C) (_ : IsModification f₂),
        (∃ g : C₂ ⟶ C₁, g ≫ f₁ = f₂) ∧ IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧
          V ∈ gammaSet (f₂ ≫ φ) (genericLift f₂)

variable {φ} [∀ s : S, PreValuationRing (S.presheaf.stalk s)]

/-- A singleton closed in a closed subspace is closed. -/
theorem isClosed_singleton_of_isClosed_subtype {X : Type*} [TopologicalSpace X] {T : Set X}
    (hT : IsClosed T) {x : X} (hx : x ∈ T) (h : IsClosed ({⟨x, hx⟩} : Set T)) :
    IsClosed ({x} : Set X) := by
  have := hT.isClosedEmbedding_subtypeVal.isClosedMap _ h
  rwa [Set.image_singleton] at this

/-- **Centres on a modification** (Temkin, T:2970–2971): let `f₁ : C₁ → C` be a modification and
`x₁ ∈ C₁` a point over a closed point of `C`. Then `x₁ ∈ (C₁/S)⁰` or `x₁` is a closed point of
`C₁`: if `κ(x₁)` has transcendence degree zero over the base, it is algebraic over `κ(f₁ x₁)`, so
`x₁` is closed in the fibre of `f₁` over the closed point `f₁ x₁`. -/
theorem mem_fibreGenericSet_or_isClosed (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    {C₁ : Scheme.{u}} [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁] {x₁ : C₁}
    (hx : IsClosed ({f₁ x₁} : Set C)) :
    x₁ ∈ fibreGenericSet (f₁ ≫ φ) ∨ IsClosed ({x₁} : Set C₁) := by
  by_cases h : x₁ ∈ fibreGenericSet (f₁ ≫ φ)
  · exact Or.inl h
  right
  have h0 : fiberTrdeg (f₁ ≫ φ) x₁ = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f₁ x₁) h
  rw [fiberTrdeg_comp] at h0
  have halg : IsAlgebraicAt f₁ x₁ :=
    (isAlgebraicAt_iff_fiberTrdeg_eq_zero f₁ x₁).mpr (add_eq_zero.mp h0).2
  have hT : IsClosed (f₁ ⁻¹' {f₁ x₁}) := hx.preimage f₁.continuous
  exact isClosed_singleton_of_isClosed_subtype hT rfl
    (isClosed_singleton_preimage_of_isAlgebraicAt f₁ rfl halg)

/-- `(C₁/S)⁰` lifts along domination: if `g ≫ f₁ = f₂` and `g y₂ ∈ (C₁/S)⁰`, then
`y₂ ∈ (C₂/S)⁰`. -/
theorem mem_fibreGenericSet_of_dominates (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    {C₁ C₂ : Scheme.{u}} [IsIntegral C₁] [IsIntegral C₂] (f₁ : C₁ ⟶ C) (f₂ : C₂ ⟶ C)
    [IsModification f₂] (g : C₂ ⟶ C₁) (hg : g ≫ f₁ = f₂) {y₂ : C₂}
    (hy : g y₂ ∈ fibreGenericSet (f₁ ≫ φ)) : y₂ ∈ fibreGenericSet (f₂ ≫ φ) := by
  have hle := fiberTrdeg_le_one φ hdim f₂ y₂
  have heq : f₂ ≫ φ = g ≫ f₁ ≫ φ := by rw [← hg, Category.assoc]
  rw [heq, fiberTrdeg_comp, hy] at hle
  rw [mem_fibreGenericSet_iff, heq, fiberTrdeg_comp, hy,
    Cardinal.eq_zero_of_one_add_le_one hle, add_zero]

/-- **`Γ` and `Γ₀` grow along domination**: if `C₂` dominates `C₁` (`g ≫ f₁ = f₂`), then
`Γ(C₁) ⊆ Γ(C₂)` and `Γ₀(C₁) ⊆ Γ₀(C₂)`. The centre of `V ∈ Γ(C₁)` on `C₂` lies over its centre on
`C₁` (valuative criterion for the proper `g`), hence in `(C₂/S)⁰`. -/
theorem gammaSet_subset_of_dominates (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    {C₁ C₂ : Scheme.{u}} [IsIntegral C₁] [IsIntegral C₂] (f₁ : C₁ ⟶ C) (f₂ : C₂ ⟶ C)
    [IsModification f₁] [IsModification f₂] (g : C₂ ⟶ C₁) (hg : g ≫ f₁ = f₂) :
    gammaSet (f₁ ≫ φ) (genericLift f₁) ⊆ gammaSet (f₂ ≫ φ) (genericLift f₂) := by
  rintro V ⟨y₁, hy₁, hV⟩
  have : IsProper (g ≫ f₁) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g f₁
  obtain ⟨y₂, hV₂, hy₂⟩ := hV.exists_of_universallyClosed g (genericLift_comp_of_comp f₁ f₂ g hg)
  exact ⟨y₂, mem_fibreGenericSet_of_dominates hdim f₁ f₂ g hg (hy₂ ▸ hy₁), hV₂⟩

/-- `Γ₀(C₁) ⊆ Γ₀(C₂)` when `C₂` dominates `C₁`: the centre on `C` is unchanged. -/
theorem gammaZeroSet_subset_of_dominates (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    {C₁ C₂ : Scheme.{u}} [IsIntegral C₁] [IsIntegral C₂] (f₁ : C₁ ⟶ C) (f₂ : C₂ ⟶ C)
    [IsModification f₁] [IsModification f₂] (g : C₂ ⟶ C₁) (hg : g ≫ f₁ = f₂) :
    gammaZeroSet (f₁ ≫ φ) (genericLift f₁) (genericPt C) ⊆
      gammaZeroSet (f₂ ≫ φ) (genericLift f₂) (genericPt C) :=
  fun _ hV ↦ ⟨gammaSet_subset_of_dominates hdim f₁ f₂ g hg hV.1, hV.2⟩

/-- **The iteration** (Temkin, T:2963–2966): under `CentreClaim φ`, for a strictly semi-stable `C`
and every finite set `F` of points of `⋃ Γ(C')` with closed centres on `C`, there is a strictly
semi-stable modification `f₁ : C₁ → C` with `F ⊆ Γ₀(C₁)`. -/
theorem exists_subset_gammaZeroSet (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (hC : IsStrictlySemistable φ ⊤) (hclaim : CentreClaim φ)
    {F : Set (RiemannZariskiSpace C.functionField)} (hF : F.Finite)
    (hFsub : ∀ V ∈ F, V ∈ unionGammaSet φ ∧
      ∃ x : C, IsClosed ({x} : Set C) ∧ IsCentre (genericPt C) V x) :
    ∃ (C₁ : Scheme.{u}) (_ : IsIntegral C₁) (f₁ : C₁ ⟶ C) (_ : IsModification f₁),
      IsStrictlySemistable (f₁ ≫ φ) ⊤ ∧ F ⊆ gammaZeroSet (f₁ ≫ φ) (genericLift f₁) (genericPt C) := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    exact ⟨C, inferInstance, 𝟙 C, inferInstance, by rwa [Category.id_comp],
      Set.empty_subset _⟩
  | @insert V F _ _ ih =>
    obtain ⟨C₁, _, f₁, _, hss₁, hF₁⟩ :=
      ih fun W hW ↦ hFsub W (Set.mem_insert_of_mem V hW)
    obtain ⟨hVG, x, hxcl, hVx⟩ := hFsub V (Set.mem_insert V F)
    obtain ⟨x₁, hV₁, hx₁⟩ := hVx.exists_of_universallyClosed f₁ (genericLift_comp f₁)
    rcases mem_fibreGenericSet_or_isClosed hdim f₁ (x₁ := x₁) (hx₁ ▸ hxcl) with hgen | hcl
    · refine ⟨C₁, inferInstance, f₁, inferInstance, hss₁, Set.insert_subset ?_ hF₁⟩
      exact ⟨⟨x₁, hgen, hV₁⟩, x, hxcl, hVx⟩
    · obtain ⟨C₂, _, f₂, _, ⟨g, hg⟩, hss₂, hV₂⟩ := hclaim f₁ hss₁ V x₁ hVG hcl hV₁
      refine ⟨C₂, inferInstance, f₂, inferInstance, hss₂, Set.insert_subset ⟨hV₂, x, hxcl, hVx⟩
        (hF₁.trans (gammaZeroSet_subset_of_dominates hdim f₁ f₂ g hg))⟩

/-- **Cofinality of strictly semi-stable modifications** (Temkin, Proposition 4.3.1, reduction to
the claim, T:2961–2966). Let `C` be strictly semi-stable over `S`, quasi-compact and separated,
assume that strictly semi-stable modifications of `C` are normal (`hnormal`; Temkin's
Proposition 3.5.2) and Temkin's claim `CentreClaim φ`. Then every modification `f' : C' → C` with
`Γ₀(C')` finite is dominated by a strictly semi-stable modification of `C`. -/
theorem exists_dominates_of_finite_gammaZeroSet [CompactSpace C] [C.IsSeparated]
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (hC : IsStrictlySemistable φ ⊤)
    (hnormal : ∀ ⦃C₁ : Scheme.{u}⦄ [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁],
      IsStrictlySemistable (f₁ ≫ φ) ⊤ → IsNormalScheme C₁)
    (hclaim : CentreClaim φ) {C' : Scheme.{u}} [IsIntegral C'] (f' : C' ⟶ C) [IsModification f']
    (hfin : (gammaZeroSet (f' ≫ φ) (genericLift f') (genericPt C)).Finite) :
    ∃ (C'' : Scheme.{u}) (_ : IsIntegral C'') (f'' : C'' ⟶ C) (_ : IsModification f''),
      IsStrictlySemistable (f'' ≫ φ) ⊤ ∧ ∃ g : C'' ⟶ C', g ≫ f' = f'' := by
  obtain ⟨C₁, _, f₁, _, hss₁, hsub⟩ := exists_subset_gammaZeroSet hdim hC hclaim hfin
    fun V hV ↦ ⟨mem_unionGammaSet_of_mem_gammaZeroSet φ f' hV, hV.2⟩
  exact ⟨C₁, inferInstance, f₁, inferInstance, hss₁,
    dominates_of_gammaZeroSet_subset φ f' f₁ (hnormal f₁ hss₁) hdim hsub⟩

/-- **Cofinality for normal modifications**: over a base with finitely many points (a valuation
ring of finite height) and for `φ` of finite type, every normal modification of a strictly
semi-stable `C` is dominated by a strictly semi-stable one (`Γ₀(C')` is finite by
`ValCurves.finite_gammaZeroSet`). -/
theorem exists_dominates_of_isNormalScheme [Finite S] [QuasiCompact φ] [LocallyOfFiniteType φ]
    [CompactSpace C] [C.IsSeparated]
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (hC : IsStrictlySemistable φ ⊤)
    (hnormal : ∀ ⦃C₁ : Scheme.{u}⦄ [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁],
      IsStrictlySemistable (f₁ ≫ φ) ⊤ → IsNormalScheme C₁)
    (hclaim : CentreClaim φ) {C' : Scheme.{u}} [IsIntegral C'] (f' : C' ⟶ C) [IsModification f']
    (hC' : IsNormalScheme C') :
    ∃ (C'' : Scheme.{u}) (_ : IsIntegral C'') (f'' : C'' ⟶ C) (_ : IsModification f''),
      IsStrictlySemistable (f'' ≫ φ) ⊤ ∧ ∃ g : C'' ⟶ C', g ≫ f' = f'' :=
  exists_dominates_of_finite_gammaZeroSet hdim hC hnormal hclaim f'
    (finite_gammaZeroSet φ f' hC' hdim)

end DeJongAlterations.StableModification.LocalUniformization
