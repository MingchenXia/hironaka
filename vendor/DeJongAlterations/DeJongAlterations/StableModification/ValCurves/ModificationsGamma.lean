import DeJongAlterations.StableModification.ValCurves.Modifications
import DeJongAlterations.StableModification.RiemannZariski.Refinement
import DeJongAlterations.Geometry.ModificationCenter
import DeJongAlterations.StableModification.ValuationRing.Composite

/-!
# The sets `Γ(C')` and `Γ₀(C')` in the Riemann–Zariski space (Temkin §4.2)

Let `L` be a field and `η : Spec L → X` a morphism. Following RZ0
(`StableModification.RiemannZariski.Scheme`), a point of `RZ_L(X)` is a valuation ring `V` of `L`
such that `η` extends to `Spec V → X`; the *centre* of `V` is the image of the closed point
(`IsCentre η V x`). For the generic point `η_C : Spec K(C) → C` of an integral scheme and a
modification `f : C' → C` there is a unique lift `genericLift f : Spec K(C) → C'` of `η_C`
(`genericLift_comp`, `genericLift_unique`), so `RZ_L(C') = RZ_L(C) =: 𝔊` (`L = K(C)`) and every
point of `𝔊` has a centre on every modification of `C` (`IsCentre.exists_of_universallyClosed`).

Following M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
§4.2 (`semi-stable.tex` lines 2873–2886, 2904–2928), for `C → S` with `S` having valuation-ring
local rings:

* `gammaSet g η = Γ(X)`: the valuation rings centred (via `η`) on `(X/S)⁰`; for a modification
  `f : C' → C` this is `Γ(C') = gammaSet (f ≫ φ) (genericLift f)` (T:2873).
* `gammaZeroSet g η η_C = Γ₀(X)`: the points of `Γ(X)` whose centre on `C` is a closed point of
  `C` (T:2879–2880).
* `generalizations T = gen(T)`: the generalizations in the Riemann–Zariski space of points of
  `T` (T:2911).

## Main results

* `IsCentre.exists_le_of_specializes`: if `V` is centred at `x` and `x ⤳ y`, some `W ⊆ V` is
  centred at `y` (composite valuation `W = V ∘ B`, `B` a valuation ring of `κ(V)` dominating the
  image of `𝒪_{X,y}`; Temkin's Lemma 2.1.4 `composlem`).
* `IsCentre.exists_of_le`: a generalization of a point centred at `y` is centred at a
  generalization of `y`.
* `IsCentre.unique`, `IsCentre.exists_of_universallyClosed`, `exists_isCentre`.
* `gammaSet_eq_union` (**Temkin, Lemma 4.2.2, third assertion**): for every modification
  `f : C' → C` of a quasi-compact relative curve,
  `Γ(C') = gen(Γ₀(C')) ∪ Γ(C)`. The proof does not use normality of `C'`; in the source the
  inclusion `⊆` is deduced via the bijection `Γ(C') ≅ (C'/S)⁰`, which needs `C'` normal, and
  Proposition 4.2.3 applies the lemma to a possibly non-normal `C'` (see the blueprint chapter).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology IsLocalRing

universe u

namespace DeJongAlterations.StableModification.ValCurves

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg
  stableUnderGeneralization_fiberTrdeg_eq_one)
open Geometry.ModificationCenter (isomorphismOpen center)
open RiemannZariskiSpace (toSpecValuationSubring specClosedPoint ofScheme)

section Centre

variable {L : Type u} [Field L] {X X' : Scheme.{u}}

/-- `V ∈ RZ_L(X)` is centred at `x` (with respect to `η : Spec L → X`): some extension
`Spec V → X` of `η` maps the closed point to `x`. -/
def IsCentre (η : Spec (.of L) ⟶ X) (V : RiemannZariskiSpace L) (x : X) : Prop :=
  ∃ ψ : Spec (.of V.valuationSubring) ⟶ X, toSpecValuationSubring V ≫ ψ = η ∧
    ψ (specClosedPoint V) = x

variable {η : Spec (.of L) ⟶ X}

theorem IsCentre.mem_ofScheme {V : RiemannZariskiSpace L} {x : X} (h : IsCentre η V x) :
    V ∈ ofScheme η := by
  obtain ⟨ψ, hψ, -⟩ := h
  exact ⟨ψ, hψ⟩

theorem exists_isCentre_of_mem_ofScheme {V : RiemannZariskiSpace L} (h : V ∈ ofScheme η) :
    ∃ x, IsCentre η V x := by
  obtain ⟨ψ, hψ⟩ := h
  exact ⟨_, ψ, hψ, rfl⟩

/-- Centres are compatible with morphisms. -/
theorem IsCentre.comp {V : RiemannZariskiSpace L} {x : X} (h : IsCentre η V x) {Y : Scheme.{u}}
    (g : X ⟶ Y) : IsCentre (η ≫ g) V (g x) := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  exact ⟨ψ ≫ g, by rw [← Category.assoc, hψ], rfl⟩

/-- On a separated scheme a point of the Riemann–Zariski space has at most one centre
(valuative criterion of separatedness). -/
theorem IsCentre.unique [X.IsSeparated] {V : RiemannZariskiSpace L} {x y : X}
    (hx : IsCentre η V x) (hy : IsCentre η V y) : x = y := by
  obtain ⟨ψ₁, h₁, rfl⟩ := hx
  obtain ⟨ψ₂, h₂, rfl⟩ := hy
  rw [RiemannZariskiSpace.extension_unique h₁ h₂]

/-- **Centres lift along universally closed morphisms** (valuative criterion): if
`η' ≫ f = η` and `V` is centred at `x`, then `V` is centred (via `η'`) at a point over `x`. -/
theorem IsCentre.exists_of_universallyClosed {η' : Spec (.of L) ⟶ X'} (f : X' ⟶ X)
    [UniversallyClosed f] (hη : η' ≫ f = η) {V : RiemannZariskiSpace L} {x : X}
    (h : IsCentre η V x) : ∃ x', IsCentre η' V x' ∧ f x' = x := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have hex : ValuativeCriterion.Existence f := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact this.1
  let sq : ValuativeCommSq f :=
    { R := V.valuationSubring, K := L, i₁ := η', i₂ := ψ, commSq := ⟨by rw [hη, hψ]⟩ }
  obtain ⟨l⟩ := (hex sq).exists_lift
  refine ⟨l.l (specClosedPoint V), ⟨l.l, l.fac_left, rfl⟩, ?_⟩
  rw [← Scheme.Hom.comp_apply, l.fac_right]

/-- **Generalizations** (Temkin, proof of Lemma 4.2.2, T:2916–2917): if `V ⊆ V'` and `V` is
centred at `y`, then `V'` is centred at a generalization of `y`. -/
theorem IsCentre.exists_of_le {V V' : RiemannZariskiSpace L} (hle : V.valuationSubring ≤
    V'.valuationSubring) {y : X} (h : IsCentre η V y) : ∃ y', IsCentre η V' y' ∧ y' ⤳ y := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  let ι : CommRingCat.of V.valuationSubring ⟶ CommRingCat.of V'.valuationSubring :=
    CommRingCat.ofHom (Subring.inclusion hle)
  refine ⟨_, ⟨Spec.map ι ≫ ψ, ?_, rfl⟩, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← hψ]
    rfl
  · rw [Scheme.Hom.comp_apply]
    exact (IsLocalRing.specializes_closedPoint _).map ψ.continuous

/-- **Composite valuations centred at a specialization** (Temkin, Lemma 2.1.4 `composlem`): if
`V` is centred at `x` and `x ⤳ y`, there is `W ⊆ V` centred at `y`, namely the composite of `V`
with a valuation ring of `κ(V)` dominating the image of `𝒪_{X,y}`. -/
theorem IsCentre.exists_le_of_specializes {V : RiemannZariskiSpace L} {x y : X}
    (h : IsCentre η V x) (hxy : x ⤳ y) :
    ∃ W : RiemannZariskiSpace L, W.valuationSubring ≤ V.valuationSubring ∧ IsCentre η W y := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  let A := V.valuationSubring
  let φ₀ := Scheme.stalkClosedPointTo ψ
  let sp : X.presheaf.stalk y ⟶ X.presheaf.stalk (ψ (closedPoint A)) :=
    X.presheaf.stalkSpecializes hxy
  let g₀ : X.presheaf.stalk y →+* A := (sp ≫ φ₀).hom
  let gk : X.presheaf.stalk y →+* ResidueField A := (residue A).comp g₀
  obtain ⟨B, hB, hBc⟩ := ValuationRing.exists_valuationSubring_dominating gk
  let W := Valuation.compose A B
  have hW : ∀ r, ((g₀ r : A) : L) ∈ W := fun r ↦ Valuation.mem_compose_of_mem (hB r)
  let g₁ : X.presheaf.stalk y →+* W := (A.subtype.comp g₀).codRestrict W.toSubring hW
  have hloc : IsLocalHom g₁ := by
    refine ⟨fun r hr ↦ ?_⟩
    by_contra hnu
    have h1 : gk r ∈ B.nonunits := (hBc r).mpr ((mem_maximalIdeal r).mpr hnu)
    rw [ValuationSubring.mem_nonunits_iff] at h1
    have h2 : W.valuation ((g₀ r : A) : L) < 1 :=
      (Valuation.valuation_compose_lt_one_iff A B _).mpr h1
    have h3 : W.valuation (g₁ r : L) = 1 := (W.valuation_eq_one_iff (g₁ r)).mp hr
    exact absurd h3 (ne_of_lt h2)
  let ψ' : Spec (.of W) ⟶ X := Spec.map (CommRingCat.ofHom g₁) ≫ X.fromSpecStalk y
  refine ⟨⟨W⟩, Valuation.compose_le A B, ψ', ?_, ?_⟩
  · have hc : CommRingCat.ofHom g₁ ≫ CommRingCat.ofHom (algebraMap W L) =
        sp ≫ φ₀ ≫ CommRingCat.ofHom (algebraMap A L) := by
      ext r
      rfl
    have h2 : Spec.map sp ≫ X.fromSpecStalk y = X.fromSpecStalk (ψ (closedPoint A)) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hxy
    calc toSpecValuationSubring ⟨W⟩ ≫ ψ'
        = Spec.map (CommRingCat.ofHom g₁ ≫ CommRingCat.ofHom (algebraMap W L)) ≫
            X.fromSpecStalk y := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ Spec.map φ₀ ≫
            (Spec.map sp ≫ X.fromSpecStalk y) := by
          rw [hc, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
      _ = toSpecValuationSubring V ≫ ψ := by
          rw [h2]
          congr 1
          exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ψ
      _ = η := hψ
  · change X.fromSpecStalk y (Spec.map (CommRingCat.ofHom g₁) (closedPoint W)) = y
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- The trivial valuation ring `L` is centred at the image of `η`. -/
theorem isCentre_top (z : Spec (.of L)) :
    IsCentre η (⟨⊤⟩ : RiemannZariskiSpace L) (η z) := by
  let e : CommRingCat.of (⊤ : ValuationSubring L) ⟶ CommRingCat.of L :=
    CommRingCat.ofHom (algebraMap (⊤ : ValuationSubring L) L)
  let e' : CommRingCat.of L ⟶ CommRingCat.of (⊤ : ValuationSubring L) :=
    CommRingCat.ofHom ((RingHom.id L).codRestrict (⊤ : ValuationSubring L).toSubring
      fun _ ↦ trivial)
  have hee' : e' ≫ e = 𝟙 _ := by
    ext a
    rfl
  refine ⟨Spec.map e' ≫ η, ?_, ?_⟩
  · change Spec.map e ≫ Spec.map e' ≫ η = η
    rw [← Category.assoc, ← Spec.map_comp, hee', Spec.map_id, Category.id_comp]
  · rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _

/-- **Every point specializing from the image of `η` is a centre.** -/
theorem exists_isCentre_of_specializes {z : Spec (.of L)} {x : X} (hx : η z ⤳ x) :
    ∃ V : RiemannZariskiSpace L, IsCentre η V x := by
  obtain ⟨W, -, hW⟩ := (isCentre_top (η := η) z).exists_le_of_specializes hx
  exact ⟨W, hW⟩

end Centre

section Generic

variable {C C' : Scheme.{u}} [IsIntegral C]

/-- The generic point `Spec K(C) → C` of an integral scheme (equal to RZ1's
`RiemannZariskiSpace.functionFieldPoint C K(C)`, `functionFieldPoint_eq_genericPt`). -/
def genericPt (C : Scheme.{u}) [IsIntegral C] : Spec (.of C.functionField) ⟶ C :=
  C.fromSpecStalk (genericPoint C)

theorem genericPt_apply (z : Spec (.of C.functionField)) : genericPt C z = genericPoint C := by
  have : Subsingleton (Spec (.of C.functionField)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum C.functionField))
  rw [Subsingleton.elim z (closedPoint C.functionField)]
  exact Scheme.fromSpecStalk_closedPoint

theorem functionFieldPoint_eq_genericPt :
    RiemannZariskiSpace.functionFieldPoint C C.functionField = genericPt C := by
  rw [RiemannZariskiSpace.functionFieldPoint, genericPt]
  have : CommRingCat.ofHom (algebraMap C.functionField C.functionField) = 𝟙 _ := rfl
  rw [this, Spec.map_id, Category.id_comp]

/-- Every point of an integral scheme is the centre of a point of `RZ_{K(C)}(C)`. -/
theorem exists_isCentre_genericPt (x : C) :
    ∃ V : RiemannZariskiSpace C.functionField, IsCentre (genericPt C) V x := by
  obtain ⟨z⟩ : Nonempty (Spec (.of C.functionField)) := inferInstance
  refine exists_isCentre_of_specializes (z := z) ?_
  rw [genericPt_apply]
  exact (genericPoint_spec C).specializes (Set.mem_univ x)

theorem range_genericPt_subset {U : C.Opens} (hU : (U : Set C).Nonempty) :
    Set.range (genericPt C) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  rw [genericPt_apply]
  exact ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

variable (f : C' ⟶ C) [hf : IsModification f]

theorem genericPt_range_subset_isomorphismOpen :
    Set.range (genericPt C) ⊆ Set.range (isomorphismOpen f).ι := by
  rw [Scheme.Opens.range_ι]
  obtain ⟨w⟩ := Geometry.ModificationCenter.nonempty_isomorphismOpen f
  exact range_genericPt_subset ⟨w.1, w.2⟩

/-- The lift of the generic point of `C` to a modification `f : C' → C`: the generic point of
`C` lies in the open over which `f` is an isomorphism. -/
def genericLift : Spec (.of C.functionField) ⟶ C' :=
  IsOpenImmersion.lift (isomorphismOpen f).ι (genericPt C)
      (genericPt_range_subset_isomorphismOpen f) ≫
    inv (f ∣_ isomorphismOpen f) ≫ (f ⁻¹ᵁ isomorphismOpen f).ι

@[reassoc (attr := simp)]
theorem genericLift_comp : genericLift f ≫ f = genericPt C := by
  rw [genericLift, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    IsOpenImmersion.lift_fac]

/-- The lift of the generic point is unique. -/
theorem genericLift_unique {η' : Spec (.of C.functionField) ⟶ C'} (h : η' ≫ f = genericPt C) :
    η' = genericLift f := by
  let W := isomorphismOpen f
  have hr : Set.range η' ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change f (η' z) ∈ W
    rw [← Scheme.Hom.comp_apply, h]
    obtain ⟨w, hw⟩ := genericPt_range_subset_isomorphismOpen f ⟨z, rfl⟩
    rw [← hw]
    exact w.2
  let e' := IsOpenImmersion.lift (f ⁻¹ᵁ W).ι η' hr
  have he' : e' ≫ (f ⁻¹ᵁ W).ι = η' := IsOpenImmersion.lift_fac _ _ _
  have h2 : e' ≫ f ∣_ W = IsOpenImmersion.lift W.ι (genericPt C)
      (genericPt_range_subset_isomorphismOpen f) := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% he', h,
      IsOpenImmersion.lift_fac]
  rw [← he', genericLift, ← h2, Category.assoc, IsIso.hom_inv_id_assoc]

/-- The lift of the generic point hits the generic point of `C'`. -/
theorem genericLift_apply [IsIntegral C'] (z : Spec (.of C.functionField)) :
    genericLift f z = genericPoint C' := by
  have h1 : f (genericLift f z) = genericPoint C := by
    rw [← Scheme.Hom.comp_apply, genericLift_comp, genericPt_apply]
  have h2 : f (genericPoint C') = genericPoint C :=
    Geometry.NormalCurveModification.genericPoint_map f hf.birational
  have hW : genericPoint C ∈ isomorphismOpen f := by
    obtain ⟨w, hw⟩ := genericPt_range_subset_isomorphismOpen f ⟨z, rfl⟩
    rw [genericPt_apply] at hw
    rw [← hw]
    exact w.2
  -- `f` is injective over the isomorphism open
  let W := isomorphismOpen f
  have hinj : Function.Injective (f ∣_ W) := by
    have := (f ∣_ W).homeomorph.injective
    convert this using 1
    funext a
    exact (Scheme.Hom.homeomorph_apply _ a).symm
  let a : (f ⁻¹ᵁ W).toScheme := ⟨genericLift f z, by change f _ ∈ W; rw [h1]; exact hW⟩
  let b : (f ⁻¹ᵁ W).toScheme := ⟨genericPoint C', by change f _ ∈ W; rw [h2]; exact hW⟩
  have : (f ∣_ W) a = (f ∣_ W) b := by
    apply Subtype.ext
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    exact h1.trans h2.symm
  exact congrArg Subtype.val (hinj this)

/-- For the identity, the lift is the generic point itself. -/
theorem genericLift_id : genericLift (𝟙 C) = genericPt C :=
  (genericLift_unique (𝟙 C) (Category.comp_id _)).symm

/-- Lifts of the generic point are compatible with domination of modifications. -/
theorem genericLift_comp_of_comp {C'' : Scheme.{u}} (f' : C'' ⟶ C) [IsModification f']
    (h : C'' ⟶ C') (hh : h ≫ f = f') : genericLift f' ≫ h = genericLift f :=
  genericLift_unique f (by rw [Category.assoc, hh, genericLift_comp])

/-- Every point of a modification is the centre of a point of `𝔊 = RZ_{K(C)}(C)` (via the lift of
the generic point). -/
theorem exists_isCentre_genericLift [IsIntegral C'] (x' : C') :
    ∃ V : RiemannZariskiSpace C.functionField, IsCentre (genericLift f) V x' := by
  obtain ⟨z⟩ : Nonempty (Spec (.of C.functionField)) := inferInstance
  refine exists_isCentre_of_specializes (z := z) ?_
  rw [genericLift_apply]
  exact (genericPoint_spec C').specializes (Set.mem_univ x')

/-- Temkin's `𝔊 = RZ_L(C)` with `L = K(C)` (T:2867): the valuation rings of the function field
centred on `C`. -/
abbrev rzSpace (C : Scheme.{u}) [IsIntegral C] : Set (RiemannZariskiSpace C.functionField) :=
  ofScheme (genericPt C)

/-- `RZ_L(C') = RZ_L(C)` for a modification `C' → C` (valuative criterion of properness). -/
theorem ofScheme_genericLift : ofScheme (genericLift f) = rzSpace C :=
  RiemannZariskiSpace.ofScheme_eq_of_universallyClosed f (genericLift_comp f)

/-- `Γ(C') ⊆ 𝔊`. -/
theorem IsCentre.mem_rzSpace {V : RiemannZariskiSpace C.functionField} {x' : C'}
    (h : IsCentre (genericLift f) V x') : V ∈ rzSpace C :=
  ofScheme_genericLift f ▸ h.mem_ofScheme

end Generic

section Gamma

variable {S C C' X : Scheme.{u}} {L : Type u} [Field L]

/-- Temkin's `Γ(X)` (T:2873): the points of the Riemann–Zariski space centred, via
`η : Spec L → X`, at a point of `(X/S)⁰`. -/
def gammaSet (g : X ⟶ S) (η : Spec (.of L) ⟶ X) : Set (RiemannZariskiSpace L) :=
  {V | ∃ x ∈ fibreGenericSet g, IsCentre η V x}

/-- Temkin's `Γ₀(X)` (T:2879–2880): the points of `Γ(X)` whose centre on `C` (via `η_C`) is a closed
point of `C`. -/
def gammaZeroSet (g : X ⟶ S) (η : Spec (.of L) ⟶ X) (ηC : Spec (.of L) ⟶ C) :
    Set (RiemannZariskiSpace L) :=
  {V | V ∈ gammaSet g η ∧ ∃ x : C, IsClosed ({x} : Set C) ∧ IsCentre ηC V x}

/-- The set of generalizations of points of `T` in the Riemann–Zariski space (Temkin's `gen`,
T:2911): `V` generalizes `W` iff `W ⊆ V`. -/
def generalizations (T : Set (RiemannZariskiSpace L)) : Set (RiemannZariskiSpace L) :=
  {V | ∃ W ∈ T, V ⤳ W}

/-- `Γ(C') ⊆ 𝔊` for a modification `f : C' → C`. -/
theorem gammaSet_subset_rzSpace {C C' : Scheme.{u}} [IsIntegral C] (f : C' ⟶ C)
    [IsModification f] (g : C' ⟶ S) : gammaSet g (genericLift f) ⊆ rzSpace C :=
  fun _ ⟨_, _, h⟩ ↦ h.mem_rzSpace f

theorem gammaZeroSet_subset (g : X ⟶ S) (η : Spec (.of L) ⟶ X) (ηC : Spec (.of L) ⟶ C) :
    gammaZeroSet g η ηC ⊆ gammaSet g η := fun _ h ↦ h.1

theorem subset_generalizations (T : Set (RiemannZariskiSpace L)) : T ⊆ generalizations T :=
  fun V hV ↦ ⟨V, hV, specializes_rfl⟩

variable [∀ s : S, PreValuationRing (S.presheaf.stalk s)]

/-- `Γ(X)` is closed under generalization (T:2908), since `(X/S)⁰` is
(`ValuationRing.stableUnderGeneralization_fiberTrdeg_eq_one`). -/
theorem generalizations_gammaSet_subset (g : X ⟶ S) (η : Spec (.of L) ⟶ X)
    (hdim : ∀ x, fiberTrdeg g x ≤ 1) : generalizations (gammaSet g η) ⊆ gammaSet g η := by
  rintro V ⟨W, ⟨y, hy, hW⟩, hVW⟩
  obtain ⟨y', hV, hy'⟩ := hW.exists_of_le (RiemannZariskiSpace.specializes_iff.mp hVW)
  exact ⟨y', stableUnderGeneralization_fiberTrdeg_eq_one g hdim hy' hy, hV⟩

variable (φ : C ⟶ S) [IsIntegral C] [IsIntegral C'] (f : C' ⟶ C) [IsModification f]

/-- `Γ(C) ⊆ Γ(C')` for every modification (T:2916). -/
theorem gammaSet_subset_gammaSet (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) :
    gammaSet φ (genericPt C) ⊆ gammaSet (f ≫ φ) (genericLift f) := by
  rintro V ⟨x, hx, hV⟩
  obtain ⟨x', hV', rfl⟩ := hV.exists_of_universallyClosed f (genericLift_comp f)
  exact ⟨x', mem_fibreGenericSet_comp φ hdim f hx, hV'⟩

/-- **Temkin, Lemma 4.2.2, third assertion** (`gamlem`): for a modification `f : C' → C` of a
quasi-compact relative curve, `Γ(C') = gen(Γ₀(C')) ∪ Γ(C)`. -/
theorem gammaSet_eq_union [CompactSpace C] (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) :
    gammaSet (f ≫ φ) (genericLift f) =
      generalizations (gammaZeroSet (f ≫ φ) (genericLift f) (genericPt C)) ∪
        gammaSet φ (genericPt C) := by
  refine Set.Subset.antisymm ?_ (Set.union_subset ?_ (gammaSet_subset_gammaSet φ f hdim))
  · rintro V ⟨x', hx', hV⟩
    by_cases hfx : f x' ∈ fibreGenericSet φ
    · exact Or.inr ⟨f x', hfx, by simpa using hV.comp f⟩
    · left
      obtain ⟨y', hxy, hy', hcl⟩ :=
        exists_specializes_mem_fibreGenericSet_isClosed φ hdim f hx' hfx
      obtain ⟨W, hWV, hW⟩ := hV.exists_le_of_specializes hxy
      refine ⟨W, ⟨⟨y', hy', hW⟩, f y', hcl, by simpa using hW.comp f⟩,
        RiemannZariskiSpace.specializes_iff.mpr hWV⟩
  · exact ((generalizations_gammaSet_subset (f ≫ φ) (genericLift f)
      (fiberTrdeg_le_one φ hdim f)).trans' (fun V ⟨W, hW, hVW⟩ ↦ ⟨W, hW.1, hVW⟩))

end Gamma

end DeJongAlterations.StableModification.ValCurves
