/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownSchemeTop
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Contracting a subcurve to a point: the δ-count (Temkin, Corollary B.2)

Let `f : C' → C` be a proper morphism of reduced projective curves over a field `k`, `x ∈ C` a
closed point which is not a generic point, `Z = f⁻¹(x)`, and assume that `f` is an isomorphism over
`C ∖ {x}` and `p_a(C') = p_a(C)`. Temkin's proof of Corollary B.2 (M. Temkin, *Stable modification
of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4442–4444) starts with the
identity

  `g(x) = ∑_{z ∈ Z} g_{C'}(z) - |Z⁰|`,

obtained by comparing the genus formulas (Lemma B.1) for `C'` and `C`. This file provides the
ingredients for that identity at the scheme level: the outer normalization `b : N → C` is finite
(`isFinite_outerNormalization`) and satisfies the hypotheses of the δ-formula
(`outerMap_app_injective`, `outerMap_isFiniteCoker`). The identity itself, with `p_a = 1 - χ(𝒪)`,
`g(z) = δ(z)` at the closed points of `Z` and `g(v) = p_a(C̃'_v)` at the generic points `v ∈ Z⁰`,
is `StableDownSchemeCount.deltaInvariant_contraction`.

## The argument

Let `S''` be the generic points of `C'` outside `Z` and `N = C̃'_{S''}` the normalization of `C'` in
them, with `π'' : N → C'`. Then `b = π'' ≫ f : N → C` is finite: it is proper, and quasi-finite
because its fibre over `x` is the preimage of the finite set `Z ∩ closure(S'')`
(Zariski's main theorem in the form `IsFinite.of_isProper_of_locallyQuasiFinite`). The
residue fields at the points of `S''` form a generic family of every affine open of `C` (through
`f`), so `b` satisfies the hypotheses of the δ-formula and `N` *is* a normalization of `C`:
`p_a(C) = 1 - χ(N) + ∑ᶠ δ_b`. On the other hand `C̃' = N ⊔ C̃'_{Z⁰}`, so
`p_a(C') = 1 - χ(N) - ∑_{v ∈ Z⁰} χ(C̃'_v) + ∑ᶠ δ_{C'}`, and `δ_{C'}(y') = δ_b(f y')` for `y' ∉ Z`
because `f` and `N ⊆ C̃'` are isomorphisms there.

Blueprint: `sm-curves-fields-genus-reduced.tex`, `lem:sm-stabdown-count-scheme`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology

set_option autoImplicit false

universe u

noncomputable section

section Range

/-- The image of the normalization in a set `S` of points lies in the closure of `S`. -/
theorem range_normalizationPointsMap_subset {C : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from C))] (S : Set C) [Finite S] :
    Set.range (normalizationPointsMap S) ⊆ closure S := by
  have hd : closure (Set.range (pointsMap C S).toNormalization) = Set.univ :=
    (pointsMap C S).toNormalization.denseRange.closure_range
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ closure (Set.range (pointsMap C S).toNormalization) := hd ▸ Set.mem_univ z
  have := image_closure_subset_closure_image (normalizationPointsMap S).continuous
    (Set.mem_image_of_mem _ hz)
  refine closure_mono ?_ this
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  change ((pointsMap C S).toNormalization ≫ (pointsMap C S).fromNormalization) w ∈ S
  rw [Scheme.Hom.toNormalization_fromNormalization]
  exact pointsMap_mem w

/-- **`X → X̃_f` is injective on sections**: for a qcqs `g : X ⟶ Y` and any open `W ⊆ Y`,
`Γ(Ỹ_g, π⁻¹W) → Γ(X, g⁻¹W)` is injective (on affine `W` it is the inclusion of the integral
closure; in general by the sheaf property). -/
theorem toNormalization_app_injective {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g]
    [QuasiSeparated g] (W : Y.Opens) :
    Function.Injective (g.toNormalization.app (g.fromNormalization ⁻¹ᵁ W)).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext g.normalization.sheaf _ s 0 fun n hn => ?_
  change g.normalization.presheaf.germ _ n hn s = g.normalization.presheaf.germ _ n hn 0
  rw [map_zero]
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hnW₀, hW₀W⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hn W.2
  have hle : g.fromNormalization ⁻¹ᵁ W₀ ≤ g.fromNormalization ⁻¹ᵁ W :=
    g.fromNormalization.preimage_mono hW₀W
  let s₀ := g.normalization.presheaf.map (homOfLE hle).op s
  have hgerm : g.normalization.presheaf.germ _ n hn s =
      g.normalization.presheaf.germ (g.fromNormalization ⁻¹ᵁ W₀) n hnW₀ s₀ :=
    (TopCat.Presheaf.germ_res_apply _ (homOfLE hle) n hnW₀ s).symm
  rw [hgerm]
  suffices hs₀ : s₀ = 0 by rw [hs₀, map_zero]
  have hnat : g.toNormalization.app (g.fromNormalization ⁻¹ᵁ W₀) s₀ =
      X.presheaf.map (homOfLE (g.toNormalization.preimage_mono hle)).op
        (g.toNormalization.app (g.fromNormalization ⁻¹ᵁ W) s) := by
    have := congrArg (fun φ => φ.hom s)
      (g.toNormalization.naturality (homOfLE hle).op)
    exact this
  rw [hs, map_zero] at hnat
  have hinj : Function.Injective (g.toNormalization.app (g.fromNormalization ⁻¹ᵁ W₀)).hom := by
    rw [Scheme.Hom.toNormalization_app_preimage g ⟨W₀, hW₀⟩]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    refine (ConcreteCategory.bijective_of_isIso (X.presheaf.map _)).1.comp
      (Function.Injective.comp ?_ (ConcreteCategory.bijective_of_isIso
        (g.normalizationObjIso hW₀).hom).1)
    exact Subtype.val_injective
  exact hinj (hnat.trans (map_zero _).symm)

section EvalOn

variable {C : Scheme.{u}} {S : Set C}

/-- The value at `η ∈ S` of a section of `𝒪_{X_S}` over an open `W'` containing the point of
`Spec κ(η)`. -/
def pointsEvalOn (W' : (pointsScheme C S).Opens) (η : S)
    (h : (⊤ : (Spec (C.residueField η.1)).Opens) ≤ pointsι η ⁻¹ᵁ W') :
    Γ(pointsScheme C S, W') ⟶ C.residueField η.1 :=
  (pointsι η).appLE W' ⊤ h ≫ (Scheme.ΓSpecIso _).hom

lemma subsingleton_spec_residueField (η : C) : Subsingleton (Spec (C.residueField η)) :=
  have : Unique (PrimeSpectrum (C.residueField η)) := inferInstance
  this.instSubsingleton

/-- **The values at the points of `S` determine a section over any open `W' ⊆ f_S⁻¹(W)`.** -/
theorem pointsEvalOn_injective (W : C.Opens) (W' : (pointsScheme C S).Opens)
    (hW' : W' ≤ pointsMap C S ⁻¹ᵁ W) (s : Γ(pointsScheme C S, W'))
    (hs : ∀ (η : S) (_ : η.1 ∈ W) (h : (⊤ : (Spec (C.residueField η.1)).Opens) ≤
      pointsι η ⁻¹ᵁ W'), pointsEvalOn W' η h s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext (pointsScheme C S).sheaf _ s 0 fun x hx => ?_
  obtain ⟨η, y, rfl⟩ : ∃ (η : S) (y : Spec (C.residueField η.1)), pointsι η y = x := by
    obtain ⟨⟨η, y⟩, h⟩ := (sigmaMk fun η : S => Spec (C.residueField η.1)).surjective x
    exact ⟨η, y, (sigmaMk_mk (fun η : S => Spec (C.residueField η.1)) η y).symm.trans h⟩
  have hη : η.1 ∈ W := by
    have := hW' hx
    change pointsMap C S (pointsι η y) ∈ W at this
    rwa [pointsMap_ι_apply] at this
  have h : (⊤ : (Spec (C.residueField η.1)).Opens) ≤ pointsι η ⁻¹ᵁ W' := by
    intro y' _
    have := subsingleton_spec_residueField η.1
    rw [Subsingleton.elim y' y]
    exact hx
  change (pointsScheme C S).presheaf.germ _ ((pointsι η) y) hx s =
    (pointsScheme C S).presheaf.germ _ ((pointsι η) y) hx 0
  rw [map_zero]
  apply (ConcreteCategory.bijective_of_isIso ((pointsι η).stalkMap y)).1
  rw [map_zero, Scheme.Hom.germ_stalkMap_apply]
  have h0 : (pointsι η).appLE _ ⊤ h s = 0 := by
    have := hs η hη h
    rw [pointsEvalOn, CommRingCat.comp_apply] at this
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (C.residueField η.1)).hom).1
      (this.trans (map_zero _).symm)
  have h1 := congrArg ((Spec (C.residueField η.1)).presheaf.germ ⊤ y
    (show y ∈ (⊤ : (Spec (C.residueField η.1)).Opens) from trivial)) h0
  rw [map_zero, Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply] at h1
  exact h1

/-- For a morphism `g : pointsScheme C S ⟶ T` and `h : T ⟶ C` with `g ≫ h = f_S`, the value at `η`
of the pullback along `g` of a section of `𝒪_T` over `h⁻¹(W)` is the residue at `η` of its image
in `C`... in the form needed: `(g ≫ h)^♯` followed by the value at `η` is the residue map. -/
lemma app_pointsEvalOn {T : Scheme.{u}} (g : pointsScheme C S ⟶ T) (hT : T ⟶ C)
    (hg : g ≫ hT = pointsMap C S) (W : C.Opens) (η : S) (hη : η.1 ∈ W)
    (h : (⊤ : (Spec (C.residueField η.1)).Opens) ≤ pointsι η ⁻¹ᵁ (g ⁻¹ᵁ (hT ⁻¹ᵁ W))) :
    hT.app W ≫ g.app (hT ⁻¹ᵁ W) ≫ pointsEvalOn (g ⁻¹ᵁ (hT ⁻¹ᵁ W)) η h =
      C.presheaf.germ W η.1 hη ≫ C.residue η.1 := by
  have e₂ : (⊤ : (Spec (C.residueField η.1)).Opens) ≤ C.fromSpecResidueField η.1 ⁻¹ᵁ W :=
    fun y _ => by
      change C.fromSpecResidueField η.1 y ∈ W
      rw [Scheme.fromSpecResidueField_apply]
      exact hη
  have hcomp : pointsι η ≫ g ≫ hT = C.fromSpecResidueField η.1 := by
    rw [hg, ι_pointsMap]
  calc hT.app W ≫ g.app (hT ⁻¹ᵁ W) ≫ pointsEvalOn (g ⁻¹ᵁ (hT ⁻¹ᵁ W)) η h
      = ((hT.app W ≫ g.app (hT ⁻¹ᵁ W)) ≫ (pointsι η).appLE _ ⊤ h) ≫
          (Scheme.ΓSpecIso _).hom := by
        rw [pointsEvalOn]
        simp only [Category.assoc]
    _ = (pointsι η ≫ g ≫ hT).appLE W ⊤ h ≫ (Scheme.ΓSpecIso _).hom := by
        congr 1
    _ = (C.fromSpecResidueField η.1).appLE W ⊤ e₂ ≫ (Scheme.ΓSpecIso _).hom := by
        congr 1
        exact appLE_eq_of_eq hcomp W ⊤ h e₂
    _ = C.presheaf.germ W η.1 hη ≫ C.residue η.1 :=
        fromSpecResidueField_appLE_ΓSpecIso W η.1 hη e₂

end EvalOn

end Range

section Contraction

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (x : C)

/-- The generic points of `C'` outside `f⁻¹(x)`. -/
def outerPoints : Set C' := {η | η ∈ genericPoints C' ∧ f η ≠ x}

/-- The generic points of `C'` in `f⁻¹(x)` (Temkin's `Z⁰`). -/
def innerPoints : Set C' := {η | η ∈ genericPoints C' ∧ f η = x}

instance [Finite (genericPoints C')] : Finite (outerPoints f x) :=
  Set.Finite.subset (Set.toFinite (genericPoints C')) fun _ h => h.1

instance [Finite (genericPoints C')] : Finite (innerPoints f x) :=
  Set.Finite.subset (Set.toFinite (genericPoints C')) fun _ h => h.1

lemma outerPoints_union_innerPoints : outerPoints f x ∪ innerPoints f x = genericPoints C' := by
  ext η
  simp only [outerPoints, innerPoints, Set.mem_union, Set.mem_ofPred_eq]
  tauto

lemma disjoint_outerPoints_innerPoints : Disjoint (outerPoints f x) (innerPoints f x) :=
  Set.disjoint_left.2 fun _ h h' => h.2 h'.2

/-- **The outer components meet the fibre in finitely many points.** -/
theorem finite_closure_outerPoints_inter [NoetherianSpace C'] [Finite (genericPoints C')]
    (hdim : topologicalKrullDim C' ≤ 1) (hx : IsClosed {x}) :
    (closure (outerPoints f x) ∩ f ⁻¹' {x}).Finite := by
  refine finite_of_isClosed_of_disjoint_genericPoints hdim
    (isClosed_closure.inter (hx.preimage f.continuous)) fun η hη hgen => ?_
  obtain ⟨hcl, hfib⟩ := hη
  rw [← Set.biUnion_of_singleton (outerPoints f x),
    (Set.toFinite (outerPoints f x)).closure_biUnion] at hcl
  obtain ⟨η'', hη'', hηcl⟩ := Set.mem_iUnion₂.1 hcl
  have hsp : η'' ⤳ η := specializes_iff_mem_closure.2 hηcl
  have heq := (mem_genericPoints_iff η).1 hgen η'' hsp
  exact hη''.2 (heq ▸ hfib)

variable (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ≠ x) [IsIso (f ∣_ U)]
  [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p']

omit [IsAffineHom (pullback.diagonal (terminal.from C'))] in
include hU in
/-- Over `y ≠ x` the fibre of `f` has at most one point. -/
lemma subsingleton_preimage_of_ne {y : C} (hy : y ≠ x) : (f ⁻¹' {y}).Subsingleton := by
  intro z₁ h₁ z₂ h₂
  have hy' : y ∈ U := (hU y).2 hy
  exact injOn_of_isIso_morphismRestrict f U (h₁ ▸ hy') (h₂ ▸ hy') (h₁.trans h₂.symm)

include hU p' in
/-- **The normalization of `C'` in its outer generic points is finite over `C`**: `b = π'' ≫ f`
is proper with finite fibres, hence finite (Zariski's main theorem). -/
theorem isFinite_outerNormalization [CompactSpace C'] [Finite (genericPoints C')] [IsProper f]
    (hdim : topologicalKrullDim C' ≤ 1) (hx : IsClosed {x}) :
    IsFinite (normalizationPointsMap (outerPoints f x) ≫ f) := by
  have := isFinite_normalizationPointsMap (S := outerPoints f x) p'
  have := isLocallyNoetherian_of_locallyOfFiniteType p'
  have : IsNoetherian C' := ⟨⟩
  have hfib : ∀ z : C', ((normalizationPointsMap (outerPoints f x)) ⁻¹' {z}).Finite :=
    fun z => (normalizationPointsMap (outerPoints f x)).finite_preimage_singleton z
  have : LocallyQuasiFinite (normalizationPointsMap (outerPoints f x) ≫ f) := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    by_cases hy : y = x
    · subst hy
      refine ((finite_closure_outerPoints_inter f y hdim hx).preimage' fun z _ => hfib z).subset ?_
      intro w hw
      exact ⟨range_normalizationPointsMap_subset _ ⟨w, rfl⟩, hw⟩
    · exact ((subsingleton_preimage_of_ne f x U hU hy).finite).preimage' fun z _ => hfib z
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- The value at a point `η` of `C'` of the pullback of a section of `𝒪_C`. -/
abbrev pullbackResidue (V : C.Opens) (η : C') (hη : η ∈ f ⁻¹ᵁ V) :
    Γ(C, V) →+* C'.residueField η :=
  (f.app V ≫ C'.evaluation (f ⁻¹ᵁ V) η hη).hom

omit [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] in
lemma pullbackResidue_eq (V : C.Opens) (η : C') (hη : η ∈ f ⁻¹ᵁ V) (a : Γ(C, V)) :
    pullbackResidue f V η hη a = f.residueFieldMap η (residueAt V (f η) hη a) :=
  (Scheme.evaluation_naturality_apply f η hη a).symm

omit [IsAffineHom (pullback.diagonal (terminal.from C'))] in
include hU in
/-- **The outer generic points form a generic family of every affine open of `C`**, through `f`:
for an affine open `V = Spec A` of `C`, the residue fields `κ(η)` at the generic points `η` of `C'`
outside `Z` with `f η ∈ V`, with `A → κ(η)`, `a ↦ (f^♯ a)(η)`, form a generic family of `A`
(provided `x` is not a generic point of `C`). -/
theorem isGenericFamily_outer {V : C.Opens} (hV : IsAffineOpen V)
    (hxg : x ∉ genericPoints C) :
    letI : ∀ i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
    IsGenericFamily (fun i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V) =>
        (hV.primeIdealOf ⟨f i.1.1, i.2⟩).asIdeal) (fun i => C'.residueField i.1.1) := by
  let _ : ∀ i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
  have hmemU : ∀ i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V), f i.1.1 ∈ U := fun i =>
    (hU _).2 i.1.2.2
  refine IsGenericFamily.mk ⟨fun i => ?_, fun i z => ?_⟩ (fun i j hij => ?_) (fun q hq => ?_)
  · ext a
    rw [RingHom.mem_ker, ← residueAt_eq_zero_iff hV (f i.1.1) i.2 a]
    change pullbackResidue f V i.1.1 i.2 a = 0 ↔ _
    rw [pullbackResidue_eq]
    exact map_eq_zero_iff _ (f.residueFieldMap i.1.1).hom.injective
  · have := isIso_residueFieldMap_of_isIso_morphismRestrict f U i.1.1 (hmemU i)
    obtain ⟨z₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.residueFieldMap i.1.1)).2 z
    obtain ⟨a, t, ht, hta⟩ := exists_residueAt_mul_eq hV (f i.1.1) i.2 z₀
    refine ⟨a, t, ht, ?_⟩
    change pullbackResidue f V i.1.1 i.2 t * _ = pullbackResidue f V i.1.1 i.2 a
    rw [pullbackResidue_eq, pullbackResidue_eq, ← map_mul, hta]
  · have hne : f i.1.1 ≠ f j.1.1 := fun h => hij (Subtype.ext (Subtype.ext
      (injOn_of_isIso_morphismRestrict f U (hmemU i) (hmemU j) h)))
    exact not_primeIdealOf_le hV i.2 j.2
      ((mem_genericPoints_iff_of_isIso_morphismRestrict f U (hmemU j)).1 j.1.2.1) hne
  · let q₀ : PrimeSpectrum Γ(C, V) := ⟨q, hq.1.1⟩
    have hgen := fromSpec_mem_genericPoints hV q₀ hq
    have hyV : hV.fromSpec q₀ ∈ V := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact Set.mem_range_self q₀
    have hyx : hV.fromSpec q₀ ≠ x := fun h => hxg (h ▸ hgen)
    obtain ⟨η, hη⟩ := exists_eq_of_isIso_morphismRestrict f U ((hU _).2 hyx)
    have hηU : f η ∈ U := hη ▸ (hU _).2 hyx
    have hηgen : η ∈ genericPoints C' :=
      (mem_genericPoints_iff_of_isIso_morphismRestrict f U hηU).2 (hη ▸ hgen)
    refine ⟨⟨⟨η, hηgen, hη ▸ hyx⟩, show f η ∈ V from hη ▸ hyV⟩, ?_⟩
    have : hV.primeIdealOf ⟨f η, hη ▸ hyV⟩ = q₀ := by
      apply hV.fromSpec.isOpenEmbedding.injective
      rw [hV.fromSpec_primeIdealOf]
      exact hη
    exact congrArg PrimeSpectrum.asIdeal this

variable [Finite (genericPoints C')]

/-- The morphism `b = π'' ≫ f : N = C̃'_{S''} → C`, `S''` the generic points of `C'` outside
`f⁻¹(x)`. -/
abbrev outerMap : normalizationPoints (outerPoints f x) ⟶ C :=
  normalizationPointsMap (outerPoints f x) ≫ f

omit [IsIso (f ∣_ U)] in
lemma le_pointsι_preimage_outer (V : C.Opens) (i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V)) :
    (⊤ : (Spec (C'.residueField i.1.1)).Opens) ≤ pointsι i.1 ⁻¹ᵁ
      ((pointsMap C' (outerPoints f x)).toNormalization ⁻¹ᵁ
        (normalizationPointsMap (outerPoints f x) ⁻¹ᵁ (f ⁻¹ᵁ V))) := by
  intro y _
  change ((pointsMap C' (outerPoints f x)).toNormalization ≫
    (pointsMap C' (outerPoints f x)).fromNormalization) (pointsι i.1 y) ∈ f ⁻¹ᵁ V
  rw [Scheme.Hom.toNormalization_fromNormalization, pointsMap_ι_apply]
  exact i.2

/-- The values at the outer generic points of the sections of `𝒪_N` over `b⁻¹(V)`. -/
def outerEval (V : C.Opens) :
    Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) →+*
      ∀ i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V), C'.residueField i.1.1 :=
  RingHom.pi fun i => (pointsEvalOn ((pointsMap C' (outerPoints f x)).toNormalization ⁻¹ᵁ
      (normalizationPointsMap (outerPoints f x) ⁻¹ᵁ (f ⁻¹ᵁ V))) i.1
      (le_pointsι_preimage_outer f x V i)).hom.comp
    ((pointsMap C' (outerPoints f x)).toNormalization.app
      (normalizationPointsMap (outerPoints f x) ⁻¹ᵁ (f ⁻¹ᵁ V))).hom

omit [IsIso (f ∣_ U)] in
lemma outerEval_comp (V : C.Opens) :
    (outerEval f x V).comp ((outerMap f x).app V).hom =
      RingHom.pi fun i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V) =>
        pullbackResidue f V i.1.1 i.2 := by
  ext a i
  have h := app_pointsEvalOn (pointsMap C' (outerPoints f x)).toNormalization
    (normalizationPointsMap (outerPoints f x))
    (Scheme.Hom.toNormalization_fromNormalization _) (f ⁻¹ᵁ V) i.1 i.2
    (le_pointsι_preimage_outer f x V i)
  have h' := congrArg (fun φ => φ.hom (f.app V a)) h
  simp only at h'
  change (pointsEvalOn _ i.1 _).hom (((pointsMap C' (outerPoints f x)).toNormalization.app _).hom
    (((normalizationPointsMap (outerPoints f x)).app (f ⁻¹ᵁ V)).hom ((f.app V).hom a))) = _
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply] at h'
  exact h'

omit [IsIso (f ∣_ U)] in
lemma outerEval_injective (V : C.Opens) : Function.Injective (outerEval f x V) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h0 : ((pointsMap C' (outerPoints f x)).toNormalization.app
      (normalizationPointsMap (outerPoints f x) ⁻¹ᵁ (f ⁻¹ᵁ V))).hom s = 0 := by
    refine pointsEvalOn_injective (f ⁻¹ᵁ V) _ ?_ _ fun η hη h => ?_
    · intro w hw
      change ((pointsMap C' (outerPoints f x)).toNormalization ≫
        (pointsMap C' (outerPoints f x)).fromNormalization) w ∈ f ⁻¹ᵁ V at hw
      rwa [Scheme.Hom.toNormalization_fromNormalization] at hw
    · exact congrFun hs ⟨η, hη⟩
  exact toNormalization_app_injective (pointsMap C' (outerPoints f x)) (f ⁻¹ᵁ V)
    (h0.trans (map_zero _).symm)

include hU in
/-- **`𝒪_C → b_*𝒪_N` is injective** on affine opens, for `C` reduced. -/
theorem outerMap_app_injective [IsReduced C] (hxg : x ∉ genericPoints C) (V : C.Opens)
    (hV : IsAffineOpen V) : Function.Injective ((outerMap f x).app V).hom := by
  let _ : ∀ i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
  have h := isGenericFamily_outer f x U hU hV hxg
  refine Function.Injective.of_comp (f := outerEval f x V) ?_
  rw [← RingHom.coe_comp, outerEval_comp]
  exact h.injective_algebraMap

include hU p' in
/-- **`b_*𝒪_N / 𝒪_C` is a finite-dimensional skyscraper** on affine opens. -/
theorem outerMap_isFiniteCoker [CompactSpace C'] [IsProper f]
    (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p] (hxg : x ∉ genericPoints C)
    (hdim : topologicalKrullDim C ≤ 1) (hdim' : topologicalKrullDim C' ≤ 1) (hx : IsClosed {x})
    (V : C.Opens) (hV : IsAffineOpen V) :
    IsFiniteCoker (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))
      ((outerMap f x).app V).hom := by
  have := isFinite_outerNormalization f x U hU p' hdim' hx
  let ψ := sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)
  let _ : Algebra k Γ(C, V) := ψ.toAlgebra
  have : Algebra.FiniteType k Γ(C, V) :=
    Geometry.NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
  have : Ring.KrullDimLE 1 Γ(C, V) :=
    Geometry.NormalizationFinite.affineSections_krullDimLE_one ⟨V, hV⟩ hdim
  let _ : ∀ i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V),
      Algebra Γ(C, V) (C'.residueField i.1.1) := fun i => (pullbackResidue f V i.1.1 i.2).toAlgebra
  have h := isGenericFamily_outer f x U hU hV hxg
  have : Finite (GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V)) := Subtype.finite
  let φ := ((outerMap f x).app V).hom
  let B := Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
  let _ : Algebra Γ(C, V) B := φ.toAlgebra
  let _ : Algebra k B := (φ.comp ψ).toAlgebra
  have : IsScalarTower k Γ(C, V) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral Γ(C, V) B :=
    algebraMap_isIntegral_iff.1 ((outerMap f x).isIntegral_app V hV)
  let Φ : B →ₐ[Γ(C, V)] ∀ i : GenericIn C' (outerPoints f x) (f ⁻¹ᵁ V), C'.residueField i.1.1 :=
    { toRingHom := outerEval f x V
      commutes' := fun a => by
        have := congrArg (fun ρ => ρ a) (outerEval_comp f x V)
        exact this }
  unfold IsFiniteCoker
  exact h.finiteDimensional_coker k Φ (outerEval_injective f x V)

end Contraction

end

end DeJongAlterations.StableModification.CurvesField.Genus
