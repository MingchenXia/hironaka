import DeJongAlterations.StableModification.ValCurves.ModificationsDomination

/-!
# Points of `(C'/S)⁰` and the Riemann–Zariski space (Temkin, Lemma 4.2.2, first assertion)

Let `S` be a scheme whose local rings are valuation rings and `C → S` a separated relative curve
with `C` integral. M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), `semi-stable.tex` lines 2904–2905 and Lemma 4.2.2 (`gamlem`, lines 2909–2913): if `C` is
normal, every point `x ∈ (C/S)⁰` has a unique preimage in `𝔊 = RZ_L(C)`, so that for a normal
modification `C'` the centre map is a bijection `Γ(C') ≅ (C'/S)⁰`.

* `mem_isomorphismOpen_of_isGenericIso`: Lemma 4.2.1 (i) for a proper morphism `p : X → C` of
  integral schemes which is an isomorphism at the generic point (not necessarily presented as
  a modification).
* `IsCentre.eq_of_mem_fibreGenericSet`: **uniqueness of centres over `(C/S)⁰`**. If two valuation
  rings `V₁, V₂` of `L` are centred at `x ∈ (C/S)⁰` and `u ∈ V₁ ∖ V₂`, the graph closure of `u`
  (RZ1's `RiemannZariskiSpace.graphProj`, the schematic closure of `(η, (1 : u))` in `C ×_ℤ ℙ¹_ℤ`)
  is proper and generically an isomorphism over the normal `C`, so `x` has a single preimage in it
  (Lemma 4.2.1); but the centre of `V₁` lies in the chart with section ring `𝒪(V)[u]` while the
  centre of `V₂` does not. This replaces Temkin's appeal to Lemma 4.2.1 for all modifications at
  once (`𝒪_{𝔊,𝔵} = colim 𝒪_{C',x'}`) by a single modification.
* `existsUnique_isCentre_genericLift`, `exists_gammaEquiv` (**Lemma 4.2.2, first assertion**):
  for a normal modification `f : C' → C`, each point of `(C'/S)⁰` is the centre of exactly one
  point of `𝔊`, and the centre map is a bijection `Γ(C') ≃ (C'/S)⁰`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology IsLocalRing

universe u

namespace DeJongAlterations.StableModification.ValCurves

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open Geometry.ModificationCenter (isomorphismOpen center)
open RiemannZariskiSpace (toSpecValuationSubring specClosedPoint ofScheme ofOpen)

section General

variable {X Y : Scheme.{u}}

/-- Points over the isomorphism open of `p` are determined by their image. -/
theorem eq_of_mem_isomorphismOpen (p : X ⟶ Y) {a b : X} (ha : p a ∈ isomorphismOpen p)
    (hab : p a = p b) : a = b := by
  let W := isomorphismOpen p
  have hinj : Function.Injective (p ∣_ W) := by
    have := (p ∣_ W).homeomorph.injective
    convert this using 1
    funext c
    exact (Scheme.Hom.homeomorph_apply _ c).symm
  let a' : (p ⁻¹ᵁ W).toScheme := ⟨a, ha⟩
  let b' : (p ⁻¹ᵁ W).toScheme := ⟨b, by change p b ∈ W; rw [← hab]; exact ha⟩
  have : (p ∣_ W) a' = (p ∣_ W) b' := by
    apply Subtype.ext
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    exact hab
  exact congrArg Subtype.val (hinj this)

/-- **Residue fields at generic points along points with values in a field.** If `ηX ≫ p = ηY`
for points `Spec L → X, Y`, `ηX` hits the generic point of `X` and the residue field map of
`ηY` is surjective, then so is the residue field map of `p` at the generic point. -/
theorem residueFieldMap_genericPoint_surjective [IsIntegral X] {L : Type u} [Field L]
    (p : X ⟶ Y) {ηX : Spec (.of L) ⟶ X} {ηY : Spec (.of L) ⟶ Y} (h : ηX ≫ p = ηY)
    (z : Spec (.of L)) (hz : ηX z = genericPoint X)
    (hsurj : Function.Surjective (ηY.residueFieldMap z)) :
    Function.Surjective (p.residueFieldMap (genericPoint X)) := by
  have h3 : Function.Surjective ((ηX ≫ p).residueFieldMap z) := by
    rw [Scheme.Hom.residueFieldMap_congr h z]
    exact surjective_isIso_comp _ hsurj
  rw [Scheme.residueFieldMap_comp] at h3
  have hinj : Function.Injective (ηX.residueFieldMap z) := (ηX.residueFieldMap z).hom.injective
  rw [← hz]
  intro b
  obtain ⟨c, hc⟩ := h3 (ηX.residueFieldMap z b)
  exact ⟨c, hinj hc⟩

/-- The residue field map of the generic point `Spec K(C) → C` is surjective. -/
theorem genericPt_residueFieldMap_surjective [IsIntegral Y] (z : Spec (.of Y.functionField)) :
    Function.Surjective ((genericPt Y).residueFieldMap z) :=
  residueFieldMap_surjective_of_stalkMap_surjective
    (show Function.Surjective ((Y.fromSpecStalk (genericPoint Y)).stalkMap z) from
      Scheme.Hom.stalkMap_surjective _ _)

/-- The residue field map of the lift of the generic point to a modification is surjective. -/
theorem genericLift_residueFieldMap_surjective [IsIntegral Y] (f : X ⟶ Y) [IsModification f]
    (z : Spec (.of Y.functionField)) :
    Function.Surjective ((genericLift f).residueFieldMap z) := by
  have h1 : Function.Surjective ((genericLift f ≫ f).residueFieldMap z) := by
    rw [Scheme.Hom.residueFieldMap_congr (genericLift_comp f) z]
    exact surjective_isIso_comp _ (genericPt_residueFieldMap_surjective z)
  rw [Scheme.residueFieldMap_comp] at h1
  exact Function.Surjective.of_comp h1

/-- The lift of the generic point to a modification is dominant. -/
theorem isDominant_genericLift [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y) [IsModification f] :
    IsDominant (genericLift f) := by
  refine ⟨?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (.of Y.functionField)) := inferInstance
  rw [DenseRange, dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun y ↦ ?_
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (genericLift f) :=
    Set.singleton_subset_iff.mpr ⟨z, genericLift_apply f z⟩
  refine closure_mono hsub ?_
  rw [(genericPoint_spec X).def]
  trivial

end General

section Lemma421

variable {S C X : Scheme.{u}} [∀ s : S, PreValuationRing (S.presheaf.stalk s)] (φ : C ⟶ S)
  [IsIntegral C] [IsIntegral X]

/-- The relative curve bound for a scheme mapping to `C` by a morphism which is an isomorphism at
the generic point. -/
theorem fiberTrdeg_le_one_of_isGenericIso (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (p : X ⟶ C) (hgen : p (genericPoint X) = genericPoint C)
    [IsIso (p.stalkMap (genericPoint X))] (x : X) : fiberTrdeg (p ≫ φ) x ≤ 1 := by
  refine (fiberTrdeg_le_genericPoint (p ≫ φ) x).trans ?_
  rw [fiberTrdeg_comp, (isAlgebraicAt_iff_fiberTrdeg_eq_zero p _).mp
    isAlgebraicAt_of_isIso_stalkMap, add_zero, hgen]
  exact hdim

/-- **Temkin, Lemma 4.2.1 (i), for generic isomorphisms.** Let `C` be normal and `p : X → C` a
proper morphism of integral schemes mapping the generic point to the generic point and inducing
an isomorphism of function fields. Every `x ∈ (C/S)⁰` lies in the open over which `p` is an
isomorphism. -/
theorem mem_isomorphismOpen_of_isGenericIso (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (p : X ⟶ C) [IsProper p]
    (hgen : p (genericPoint X) = genericPoint C) [hiso : IsIso (p.stalkMap (genericPoint X))]
    {x : C} (hx : x ∈ fibreGenericSet φ) : x ∈ isomorphismOpen p := by
  have halg : ∀ x', p x' = x → IsAlgebraicAt p x' := by
    intro x' hx'
    rw [isAlgebraicAt_iff_fiberTrdeg_eq_zero]
    have h := fiberTrdeg_le_one_of_isGenericIso φ hdim p hgen x'
    rw [fiberTrdeg_comp, hx', hx] at h
    exact Cardinal.eq_zero_of_one_add_le_one h
  obtain ⟨V, hxV, hfin, -⟩ := exists_isFinite_morphismRestrict_of_isAlgebraicAt p x halg
  have hξV : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hpre : genericPoint X ∈ p ⁻¹ᵁ V := by
    change p _ ∈ V
    rw [hgen]
    exact hξV
  have : Nonempty (p ⁻¹ᵁ V) := ⟨⟨_, hpre⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral (p ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (p ⁻¹ᵁ V).ι
  have hn : IsNormalScheme V.toScheme :=
    Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion V.ι hnormal
  let ξX : (p ⁻¹ᵁ V).toScheme := ⟨genericPoint X, hpre⟩
  let ξC : V.toScheme := ⟨genericPoint C, hξV⟩
  have hgX : genericPoint (p ⁻¹ᵁ V).toScheme = ξX :=
    Subtype.ext (genericPoint_eq_of_isOpenImmersion (p ⁻¹ᵁ V).ι)
  have hgV : genericPoint V.toScheme = ξC :=
    Subtype.ext (genericPoint_eq_of_isOpenImmersion V.ι)
  have hgen' : (p ∣_ V) (genericPoint (p ⁻¹ᵁ V).toScheme) = genericPoint V.toScheme := by
    rw [hgX, hgV]
    apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact hgen
  have : IsIso ((p ∣_ V).stalkMap (genericPoint (p ⁻¹ᵁ V).toScheme)) := by
    rw [hgX]
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (morphismRestrictStalkMap p V ξX)).mpr hiso
  have : IsIso (p ∣_ V) := isIso_of_isFinite_of_isIso_stalkMap (p ∣_ V) hgen' hn
  exact Geometry.ModificationCenter.le_isomorphismOpen_of_isIso p V hxV

end Lemma421

section Unique

variable {S C : Scheme.{u}} [∀ s : S, PreValuationRing (S.presheaf.stalk s)] (φ : C ⟶ S)
  [IsIntegral C] [C.IsSeparated] {L : Type u} [Field L]

/-- A point of the Riemann–Zariski space centred at `y` is the point `ofScheme.center` of RZ0. -/
theorem IsCentre.center_eq {X : Scheme.{u}} [X.IsSeparated] {η : Spec (.of L) ⟶ X}
    {V : RiemannZariskiSpace L} {y : X} (h : IsCentre η V y) :
    RiemannZariskiSpace.ofScheme.center η ⟨V, h.mem_ofScheme⟩ = y := by
  have hV := h.mem_ofScheme
  exact IsCentre.unique ⟨hV.choose, hV.choose_spec, rfl⟩ h

/-- **Key step for the uniqueness of centres.** Let `C` be normal and separated, `η : Spec L → C`
dominant with surjective residue field map, and `V₁, V₂` centred at `x ∈ (C/S)⁰`. Then
`V₁ ⊆ V₂`. -/
theorem IsCentre.le_of_mem_fibreGenericSet (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {η : Spec (.of L) ⟶ C} [IsDominant η]
    (hsurj : ∀ z, Function.Surjective (η.residueFieldMap z)) {x : C}
    (hx : x ∈ fibreGenericSet φ) {V₁ V₂ : RiemannZariskiSpace L} (h₁ : IsCentre η V₁ x)
    (h₂ : IsCentre η V₂ x) : V₁.valuationSubring ≤ V₂.valuationSubring := by
  intro w hw₁
  by_contra hw₂
  -- the graph closure of `w`
  let f : Geometry.ProjectiveIdeal.ChartIndex (0 : Fin (1 + 1)) → L := fun _ ↦ w
  let gp := RiemannZariskiSpace.graphPoint η 1 f
  let ηu := gp.toImage
  let p := RiemannZariskiSpace.graphProj η 1 f
  have hp : ηu ≫ p = η := by
    simp only [ηu, p, RiemannZariskiSpace.graphProj, Scheme.Hom.toImage_imageι_assoc, gp,
      RiemannZariskiSpace.graphPoint_fst]
  have : gp.image.IsSeparated := isSeparated_of_isSeparated p
  -- `p` is an isomorphism at the generic point
  obtain ⟨z⟩ : Nonempty (Spec (.of L)) := inferInstance
  have hzX : ηu z = genericPoint gp.image := by
    have := genericPoint_map_of_isDominant ηu
    rwa [Subsingleton.elim (genericPoint (Spec (.of L))) z] at this
  have hzC : η z = genericPoint C := by
    have := genericPoint_map_of_isDominant η
    rwa [Subsingleton.elim (genericPoint (Spec (.of L))) z] at this
  have hgen : p (genericPoint gp.image) = genericPoint C := by
    rw [← hzX, ← Scheme.Hom.comp_apply, hp, hzC]
  have : IsIso (p.stalkMap (genericPoint gp.image)) :=
    isIso_stalkMap_genericPoint p hgen
      (residueFieldMap_genericPoint_surjective p hp z hzX (hsurj z))
  have hxW := mem_isomorphismOpen_of_isGenericIso φ hnormal hdim p hgen hx
  -- the centres of `V₁` and `V₂` on the graph closure coincide
  obtain ⟨y₁, hy₁, hpy₁⟩ := h₁.exists_of_universallyClosed p hp
  obtain ⟨y₂, hy₂, hpy₂⟩ := h₂.exists_of_universallyClosed p hp
  have hy : y₁ = y₂ := eq_of_mem_isomorphismOpen p (hpy₁ ▸ hxW) (hpy₁.trans hpy₂.symm)
  -- an affine chart over an affine neighbourhood of `x`
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hηV : η ⁻¹ᵁ V = ⊤ := RiemannZariskiSpace.preimage_eq_top_of_isDominant ⟨x, hxV⟩
  obtain ⟨W, hW, hηW, -, -, hrange⟩ := RiemannZariskiSpace.graph_hasCharts η 1 f V hV hηV
  have hwmem : w ∈ (RiemannZariskiSpace.sectionsToField ηu W hηW).range := by
    rw [hrange]
    exact (le_sup_right : Subring.closure (Set.range f) ≤ _)
      (Subring.subset_closure ⟨⟨1, by decide⟩, rfl⟩)
  -- the centre of `V₁` lies in the chart
  obtain ⟨ψ₁, hψ₁, hψ₁x⟩ := h₁
  have hV₁ : V₁ ∈ ofOpen η V :=
    RiemannZariskiSpace.mem_ofOpen_of_extension ψ₁ hψ₁ (hψ₁x ▸ hxV)
  have hV₁s : ∀ a, RiemannZariskiSpace.sectionsToField η V hηV a ∈ V₁.valuationSubring :=
    RiemannZariskiSpace.mem_ofRingHom.mp ((RiemannZariskiSpace.mem_ofOpen_iff hηV).mp hV₁)
  have hle : (RiemannZariskiSpace.sectionsToField ηu W hηW).range ≤
      V₁.valuationSubring.toSubring := by
    rw [hrange]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact hV₁s a
    · rw [Subring.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hw₁
  have hV₁W : V₁ ∈ ofOpen ηu W :=
    ⟨hηW, RiemannZariskiSpace.mem_ofRingHom.mpr fun a ↦ hle ⟨a, rfl⟩⟩
  have hy₁W : y₁ ∈ W := by
    rw [← hy₁.center_eq]
    exact (RiemannZariskiSpace.ofScheme.center_mem_iff hW _).mpr hV₁W
  -- the centre of `V₂` does not
  have hy₂W : y₂ ∉ W := by
    intro hmem
    rw [← hy₂.center_eq] at hmem
    obtain ⟨hU', hV₂⟩ := (RiemannZariskiSpace.ofScheme.center_mem_iff hW _).mp hmem
    obtain ⟨a, ha⟩ := hwmem
    exact hw₂ (ha ▸ RiemannZariskiSpace.mem_ofRingHom.mp hV₂ a)
  exact hy₂W (hy ▸ hy₁W)

/-- **Uniqueness of centres over `(C/S)⁰`** (Temkin, T:2904–2905): for `C` normal and separated and
`η : Spec L → C` dominant with surjective residue field map, a point `x ∈ (C/S)⁰` is the centre
of at most one point of `RZ_L(C)`. -/
theorem IsCentre.eq_of_mem_fibreGenericSet (hnormal : IsNormalScheme C)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {η : Spec (.of L) ⟶ C} [IsDominant η]
    (hsurj : ∀ z, Function.Surjective (η.residueFieldMap z)) {x : C}
    (hx : x ∈ fibreGenericSet φ) {V₁ V₂ : RiemannZariskiSpace L} (h₁ : IsCentre η V₁ x)
    (h₂ : IsCentre η V₂ x) : V₁ = V₂ :=
  RiemannZariskiSpace.ext (le_antisymm
    (h₁.le_of_mem_fibreGenericSet φ hnormal hdim hsurj hx h₂)
    (h₂.le_of_mem_fibreGenericSet φ hnormal hdim hsurj hx h₁))

variable {C' : Scheme.{u}} [IsIntegral C'] (f : C' ⟶ C) [IsModification f]

/-- **Temkin, T:2904–2905**: for a normal modification `f : C' → C`, every point of `(C'/S)⁰` is the
centre of exactly one point of `𝔊 = RZ_{K(C)}(C)`. -/
theorem existsUnique_isCentre_genericLift (hnormal : IsNormalScheme C')
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {x' : C'} (hx : x' ∈ fibreGenericSet (f ≫ φ)) :
    ∃! V : RiemannZariskiSpace C.functionField, IsCentre (genericLift f) V x' := by
  have : C'.IsSeparated := isSeparated_of_isSeparated f
  have := isDominant_genericLift f
  have hdim' : fiberTrdeg (f ≫ φ) (genericPoint C') ≤ 1 := fiberTrdeg_le_one φ hdim f _
  obtain ⟨V, hV⟩ := exists_isCentre_genericLift f x'
  exact ⟨V, hV, fun W hW ↦ hW.eq_of_mem_fibreGenericSet (f ≫ φ) hnormal hdim'
    (genericLift_residueFieldMap_surjective f) hx hV⟩

/-- **Temkin, Lemma 4.2.2, first assertion** (`gamlem`): for a normal modification `f : C' → C`
the centre map is a bijection `Γ(C') ≃ (C'/S)⁰`. -/
theorem exists_gammaEquiv (hnormal : IsNormalScheme C')
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) :
    ∃ e : gammaSet (f ≫ φ) (genericLift f) ≃ fibreGenericSet (f ≫ φ),
      ∀ V, IsCentre (genericLift f) V.1 (e V).1 := by
  have : C'.IsSeparated := isSeparated_of_isSeparated f
  choose c hc hcV using fun V : gammaSet (f ≫ φ) (genericLift f) ↦ V.2
  refine ⟨{ toFun := fun V ↦ ⟨c V, hc V⟩
            invFun := fun x ↦
              ⟨(existsUnique_isCentre_genericLift φ f hnormal hdim x.2).exists.choose,
              x.1, x.2, (existsUnique_isCentre_genericLift φ f hnormal hdim x.2).exists.choose_spec⟩
            left_inv := fun V ↦ ?_
            right_inv := fun x ↦ ?_ }, fun V ↦ hcV V⟩
  · apply Subtype.ext
    exact (existsUnique_isCentre_genericLift φ f hnormal hdim (hc V)).unique
      (existsUnique_isCentre_genericLift φ f hnormal hdim (hc V)).exists.choose_spec (hcV V)
  · apply Subtype.ext
    exact IsCentre.unique (hcV _)
      (existsUnique_isCentre_genericLift φ f hnormal hdim x.2).exists.choose_spec

end Unique

section Dominates

variable {C C₁ C₂ : Scheme.{u}} [IsIntegral C] [IsIntegral C₁] [IsIntegral C₂]

/-- A modification `f₁ : C₁ → C` *dominates* a modification `f₂ : C₂ → C` if `f₁` factors through
`f₂` (Temkin, T:2928). -/
def Dominates (f₁ : C₁ ⟶ C) (f₂ : C₂ ⟶ C) : Prop := ∃ g : C₁ ⟶ C₂, g ≫ f₂ = f₁

omit [IsIntegral C₂] in
/-- **The domination morphism is unique** (T:2929): two factorizations of `f₁` through the
separated `f₂` agree, since they agree on the dense point `genericLift f₁`. -/
theorem Dominates.unique (f₁ : C₁ ⟶ C) (f₂ : C₂ ⟶ C) [IsModification f₁] [IsModification f₂]
    {g g' : C₁ ⟶ C₂} (hg : g ≫ f₂ = f₁) (hg' : g' ≫ f₂ = f₁) : g = g' := by
  have := isDominant_genericLift f₁
  refine ext_of_isDominant_of_isSeparated f₂ (hg.trans hg'.symm) (genericLift f₁) ?_
  rw [genericLift_comp_of_comp f₂ f₁ g hg, genericLift_comp_of_comp f₂ f₁ g' hg']

/-- **Temkin, Proposition 4.2.3** (`schmodprop`), in terms of `Dominates`. -/
theorem dominates_of_gammaZeroSet_subset {S : Scheme.{u}}
    [∀ s : S, PreValuationRing (S.presheaf.stalk s)] (φ : C ⟶ S) [CompactSpace C]
    [C.IsSeparated] (f' : C₁ ⟶ C) (f'' : C₂ ⟶ C) [IsModification f'] [IsModification f'']
    (hnormal : IsNormalScheme C₂) (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (h : gammaZeroSet (f' ≫ φ) (genericLift f') (genericPt C) ⊆
      gammaZeroSet (f'' ≫ φ) (genericLift f'') (genericPt C)) :
    Dominates f'' f' :=
  exists_comp_eq_of_gammaZeroSet_subset φ f' f'' hnormal hdim h

end Dominates

end DeJongAlterations.StableModification.ValCurves
