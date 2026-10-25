/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusFormula
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Cohomology of a disjoint union

Let `Z` be a quasi-compact scheme with affine diagonal which is the disjoint union of two open
subschemes `U` and `V` (open immersions `iU : U ⟶ Z`, `iV : V ⟶ Z` with disjoint ranges covering
`Z`). Then `H^p(Z, 𝒪_Z) ≅ H^p(U, 𝒪_U) × H^p(V, 𝒪_V)` (`cohomologyUnitEquivProd`), and hence the
Euler characteristic is additive: `χ(Z, 𝒪_Z) = χ(U, 𝒪_U) + χ(V, 𝒪_V)`
(`eulerChar_eq_add_of_isCompl`), the cohomology of `𝒪_U` and `𝒪_V` being finite-dimensional when
that of `𝒪_Z` is.

This is the additivity of `χ` over the components of the normalization used in Temkin's proof of
Lemma B.1 (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4425–4433: "`H⁰(𝒪_{C̃})` is
the direct sum of `|C⁰|` copies of `k`") and in Corollary B.2 (l. 4442–4444, the normalization of
`C'` is that of `C` together with the normalizations of the components of `Z`).

## The argument

Choose finite affine covers `(Uᵢ)` of `U` and `(V_k)` of `V`; their images form a finite affine
cover `W` of `Z` indexed by `ι ⊕ₗ κ`, and every intersection of opens of both kinds is empty. The two
restrictions `Č(W) ⟶ Č(W|_ι)` and `Č(W) ⟶ Č(W|_κ)` together form an isomorphism of complexes
`Č(W) ≅ Č(W|_ι) ⊞ Č(W|_κ)` (`isIso_cechSplit`): an alternating cochain is determined by its values on
subsets of one kind, the values on mixed subsets lying in `Γ(∅) = 0`. Finally `Č(𝒪_Z, W|_ι)` is the
Čech complex of `𝒪_U` for `(Uᵢ)`, since `iU^♯ : Γ(Z, iU(Uᵢ)) → Γ(U, Uᵢ)` is bijective
(`isIso_subsetCechComplexMap`, `cechComplexPushforwardIso`).

Blueprint: `sm-curves-fields-genus-reduced.tex`, `lem:sm-euler-disjoint-union`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.Geometry.ProperSteinProjectiveCech

set_option autoImplicit false

universe u

noncomputable section

section SubsetCech

variable {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι]
  {D₁ D₂ : Finset ι ⥤ ModuleCat.{u} R}

omit [LinearOrder ι] in
/-- A map of subset diagrams which is bijective on nonempty subsets is bijective on the Čech
pieces of positive cardinality. -/
lemma subsetCechCardMap_bijective (α : D₁ ⟶ D₂)
    (hα : ∀ T : Finset ι, T.Nonempty → Function.Bijective (α.app T)) (n : ℕ) (hn : 0 < n) :
    Function.Bijective (subsetCechCardMap α n) := by
  classical
  have hne : ∀ T : Finset ι, T.card = n → T.Nonempty := fun T hT =>
    Finset.card_pos.1 (hT ▸ hn)
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · apply Subtype.ext
    funext T
    by_cases hT : T.card = n
    · exact (hα T (hne T hT)).1 (congrFun (congrArg Subtype.val hxy) T)
    · rw [x.property T hT, y.property T hT]
  · refine ⟨⟨fun T => if hT : T.card = n then
        Classical.choose ((hα T (hne T hT)).2 (y.val T)) else 0, fun T hT => by
          simp only [dif_neg hT]⟩, ?_⟩
    apply Subtype.ext
    funext T
    change α.app T (if hT : T.card = n then _ else 0) = y.val T
    by_cases hT : T.card = n
    · rw [dif_pos hT]
      exact Classical.choose_spec ((hα T (hne T hT)).2 (y.val T))
    · rw [dif_neg hT, map_zero, y.property T hT]

/-- A map of subset diagrams which is bijective on nonempty subsets induces an isomorphism of
Čech complexes. -/
theorem isIso_subsetCechComplexMap (α : D₁ ⟶ D₂)
    (hα : ∀ T : Finset ι, T.Nonempty → Function.Bijective (α.app T)) :
    IsIso (subsetCechComplexMap α) := by
  have : ∀ p, IsIso ((subsetCechComplexMap α).f p) := fun p =>
    (LinearEquiv.ofBijective (subsetCechCardMap α (p + 1))
      (subsetCechCardMap_bijective α hα (p + 1) p.succ_pos)).toModuleIso.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

end SubsetCech

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

section Split

variable (c : R →+* Γ(X, ⊤)) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (V : κ → X.Opens)

/-- The sections of a module over an empty open are trivial. -/
lemma subsingleton_sectionsModuleCat_unit {W : X.Opens} (hW : W = ⊥) (h : W ≤ ⊤) :
    Subsingleton (sectionsModuleCat (SheafOfModules.unit X.ringCatSheaf) c W h) := by
  subst hW
  change Subsingleton Γ(X, ⊥)
  infer_instance

omit [LinearOrder ι] [LinearOrder κ] in
lemma sumLex_cases' (s : ι ⊕ₗ κ) : (∃ i, toLex (Sum.inl i) = s) ∨ ∃ k, toLex (Sum.inr k) = s := by
  obtain ⟨s, rfl⟩ := toLex.surjective s
  rcases s with i | k
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨k, rfl⟩

lemma sumLex_cases (s : ι ⊕ₗ κ) : (∃ i, inlLex i = s) ∨ ∃ k, inrLex k = s :=
  sumLex_cases' s

lemma inlLex_ne_inrLex (i : ι) (k : κ) : (inlLex i : ι ⊕ₗ κ) ≠ inrLex k := fun h =>
  Sum.inl_ne_inr (congrArg ofLex h)

/-- Every finite subset of `ι ⊕ₗ κ` lies in one of the two summands, or meets both. -/
lemma finset_sumLex_cases (S : Finset (ι ⊕ₗ κ)) :
    (S.preimage inlLex inlLex.injective.injOn).map inlLex.toEmbedding = S ∨
      (S.preimage inrLex inrLex.injective.injOn).map inrLex.toEmbedding = S ∨
      ((∃ i, inlLex i ∈ S) ∧ ∃ k, inrLex k ∈ S) := by
  classical
  by_cases hl : ∀ s ∈ S, ∃ i, inlLex i = s
  · left
    ext s
    simp only [Finset.mem_map, Finset.mem_preimage, RelEmbedding.coe_toEmbedding]
    exact ⟨fun ⟨i, hi, his⟩ => his ▸ hi, fun hs => by
      obtain ⟨i, rfl⟩ := hl s hs
      exact ⟨i, hs, rfl⟩⟩
  by_cases hr : ∀ s ∈ S, ∃ k, inrLex k = s
  · right; left
    ext s
    simp only [Finset.mem_map, Finset.mem_preimage, RelEmbedding.coe_toEmbedding]
    exact ⟨fun ⟨i, hi, his⟩ => his ▸ hi, fun hs => by
      obtain ⟨i, rfl⟩ := hr s hs
      exact ⟨i, hs, rfl⟩⟩
  right; right
  push Not at hl hr
  obtain ⟨s, hs, hsl⟩ := hl
  obtain ⟨t, ht, htr⟩ := hr
  have hs' : ∃ k, inrLex k = s := (sumLex_cases s).resolve_left fun ⟨i, hi⟩ => hsl i hi
  have ht' : ∃ i, inlLex i = t := (sumLex_cases t).resolve_right fun ⟨k, hk⟩ => htr k hk
  obtain ⟨k, rfl⟩ := hs'
  obtain ⟨i, rfl⟩ := ht'
  exact ⟨⟨i, ht⟩, ⟨k, hs⟩⟩

variable {U V}

/-- If the opens of the two families are pairwise disjoint, the intersection over a subset meeting
both summands is empty. -/
lemma inf_sumLexFamily_eq_bot (hUV : ∀ i k, U i ⊓ V k = ⊥) (S : Finset (ι ⊕ₗ κ))
    (hS : (∃ i, inlLex i ∈ S) ∧ ∃ k, inrLex k ∈ S) : S.inf (sumLexFamily U V) = ⊥ := by
  obtain ⟨⟨i, hi⟩, ⟨k, hk⟩⟩ := hS
  refine le_bot_iff.1 ((le_inf (Finset.inf_le hi) (Finset.inf_le hk)).trans ?_)
  exact (hUV i k).le

/-- The pair of restrictions `Č(W) → Č(W|_ι) × Č(W|_κ)` is bijective in every degree. -/
lemma cechSplit_bijective (hUV : ∀ i k, U i ⊓ V k = ⊥) (p : ℕ) :
    Function.Bijective (LinearMap.prod ((cechRestrict (SheafOfModules.unit X.ringCatSheaf)
      (sumLexFamily U V) inlLex c).f p).hom ((cechRestrict (SheafOfModules.unit X.ringCatSheaf)
      (sumLexFamily U V) inrLex c).f p).hom) := by
  classical
  set F := SheafOfModules.unit X.ringCatSheaf
  set W := sumLexFamily U V
  refine ⟨fun x y hxy => ?_, fun ab => ?_⟩
  · have hl := congrArg Prod.fst hxy
    have hr := congrArg Prod.snd hxy
    apply Subtype.ext
    funext S
    rcases finset_sumLex_cases S with hS | hS | hS
    · have h0 := congrArg (fun z => z.val (S.preimage inlLex inlLex.injective.injOn)) hl
      have hinj := (sectionsRestrict_bijective_of_eq F c
        (le_top : ((S.preimage inlLex inlLex.injective.injOn).map inlLex.toEmbedding).inf W ≤ ⊤)
        (le_top : (S.preimage inlLex inlLex.injective.injOn).inf (W ∘ inlLex) ≤ ⊤)
        (inf_map_orderEmbedding W inlLex _).symm).1 h0
      rw [hS] at hinj
      exact hinj
    · have h0 := congrArg (fun z => z.val (S.preimage inrLex inrLex.injective.injOn)) hr
      have hinj := (sectionsRestrict_bijective_of_eq F c
        (le_top : ((S.preimage inrLex inrLex.injective.injOn).map inrLex.toEmbedding).inf W ≤ ⊤)
        (le_top : (S.preimage inrLex inrLex.injective.injOn).inf (W ∘ inrLex) ≤ ⊤)
        (inf_map_orderEmbedding W inrLex _).symm).1 h0
      rw [hS] at hinj
      exact hinj
    · have := subsingleton_sectionsModuleCat_unit c (inf_sumLexFamily_eq_bot hUV S hS)
        (le_top : S.inf W ≤ ⊤)
      exact Subsingleton.elim _ _
  · obtain ⟨xa, hxa⟩ := cechRestrict_f_surjective F W inlLex c p ab.1
    obtain ⟨xb, hxb⟩ := cechRestrict_f_surjective F W inrLex c p ab.2
    let isLeft : Finset (ι ⊕ₗ κ) → Prop := fun S =>
      (S.preimage inlLex inlLex.injective.injOn).map inlLex.toEmbedding = S
    let x : subsetCechCube (cechDiagram F W c) := fun S =>
      if isLeft S then xa.val S else xb.val S
    have hx : x ∈ subsetCechCardPiece (cechDiagram F W c) (p + 1) := by
      intro S hS
      simp only [x]
      split_ifs
      · exact xa.property S hS
      · exact xb.property S hS
    refine ⟨⟨x, hx⟩, Prod.ext ?_ ?_⟩
    · rw [← hxa]
      apply Subtype.ext
      funext T
      have hpre : (T.map (inlLex (ι := ι) (κ := κ)).toEmbedding).preimage inlLex
          inlLex.injective.injOn = T := by
        ext i
        simp
      have hl : isLeft (T.map (inlLex (ι := ι) (κ := κ)).toEmbedding) := by
        change Finset.map _ _ = _
        rw [hpre]
      have : x (T.map (inlLex (ι := ι) (κ := κ)).toEmbedding) =
          xa.val (T.map (inlLex (ι := ι) (κ := κ)).toEmbedding) := by
        change (if isLeft _ then _ else _) = _
        rw [if_pos hl]
      exact congrArg _ this
    · rw [← hxb]
      apply Subtype.ext
      funext T
      by_cases hT : T.card = p + 1
      · have hl : ¬ isLeft (T.map (inrLex (ι := ι) (κ := κ)).toEmbedding) := by
          intro h
          obtain ⟨k, hk⟩ := Finset.card_pos.1 (show 0 < T.card by omega)
          have hmem : inrLex k ∈ T.map (inrLex (ι := ι) (κ := κ)).toEmbedding :=
            Finset.mem_map_of_mem _ hk
          rw [← h] at hmem
          obtain ⟨i, -, hi⟩ := Finset.mem_map.1 hmem
          exact inlLex_ne_inrLex i k hi
        have : x (T.map (inrLex (ι := ι) (κ := κ)).toEmbedding) =
            xb.val (T.map (inrLex (ι := ι) (κ := κ)).toEmbedding) := by
          change (if isLeft _ then _ else _) = _
          rw [if_neg hl]
        exact congrArg _ this
      · have h1 : (T.map (inrLex (ι := ι) (κ := κ)).toEmbedding).card ≠ p + 1 := by
          rwa [Finset.card_map]
        have : x (T.map (inrLex (ι := ι) (κ := κ)).toEmbedding) =
            xb.val (T.map (inrLex (ι := ι) (κ := κ)).toEmbedding) := by
          rw [hx _ h1, xb.property _ h1]
        exact congrArg _ this

/-- The splitting map `Č(W) ⟶ Č(W|_ι) ⊞ Č(W|_κ)`. -/
def cechSplit :
    cechComplex (SheafOfModules.unit X.ringCatSheaf) (sumLexFamily U V) c ⟶
      cechComplex (SheafOfModules.unit X.ringCatSheaf) U c ⊞
        cechComplex (SheafOfModules.unit X.ringCatSheaf) V c :=
  biprod.lift (cechRestrict (SheafOfModules.unit X.ringCatSheaf) (sumLexFamily U V) inlLex c)
    (cechRestrict (SheafOfModules.unit X.ringCatSheaf) (sumLexFamily U V) inrLex c)

/-- **The Čech complex of a disjoint union splits.** -/
theorem isIso_cechSplit (hUV : ∀ i k, U i ⊓ V k = ⊥) : IsIso (cechSplit c (U := U) (V := V)) := by
  suffices ∀ p, IsIso ((cechSplit c (U := U) (V := V)).f p) from
    HomologicalComplex.Hom.isIso_of_components _
  intro p
  set K := cechComplex (SheafOfModules.unit X.ringCatSheaf) U c
  set L := cechComplex (SheafOfModules.unit X.ringCatSheaf) V c
  let e := LinearEquiv.ofBijective _ (cechSplit_bijective c hUV p)
  have key : (cechSplit c).f p ≫ (HomologicalComplex.biprodXIso K L p).hom ≫
      (ModuleCat.biprodIsoProd (K.X p) (L.X p)).hom = e.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · have h1 : (ModuleCat.biprodIsoProd (K.X p) (L.X p)).hom ≫
          ModuleCat.ofHom (LinearMap.fst R (K.X p) (L.X p)) = biprod.fst := by
        rw [← Iso.eq_inv_comp, ModuleCat.biprodIsoProd_inv_comp_fst]
      have h2 := congrArg (fun φ => φ.hom x) (show (cechSplit c).f p ≫
          (HomologicalComplex.biprodXIso K L p).hom ≫
          (ModuleCat.biprodIsoProd (K.X p) (L.X p)).hom ≫
            ModuleCat.ofHom (LinearMap.fst R (K.X p) (L.X p)) =
          (cechRestrict (SheafOfModules.unit X.ringCatSheaf) (sumLexFamily U V) inlLex c).f p by
        rw [h1, HomologicalComplex.biprodXIso_hom_fst, ← HomologicalComplex.comp_f]
        exact congrArg (fun φ => HomologicalComplex.Hom.f φ p) (biprod.lift_fst _ _))
      exact h2
    · have h1 : (ModuleCat.biprodIsoProd (K.X p) (L.X p)).hom ≫
          ModuleCat.ofHom (LinearMap.snd R (K.X p) (L.X p)) = biprod.snd := by
        rw [← Iso.eq_inv_comp, ModuleCat.biprodIsoProd_inv_comp_snd]
      have h2 := congrArg (fun φ => φ.hom x) (show (cechSplit c).f p ≫
          (HomologicalComplex.biprodXIso K L p).hom ≫
          (ModuleCat.biprodIsoProd (K.X p) (L.X p)).hom ≫
            ModuleCat.ofHom (LinearMap.snd R (K.X p) (L.X p)) =
          (cechRestrict (SheafOfModules.unit X.ringCatSheaf) (sumLexFamily U V) inrLex c).f p by
        rw [h1, HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
        exact congrArg (fun φ => HomologicalComplex.Hom.f φ p) (biprod.lift_snd _ _))
      exact h2
  have : IsIso ((cechSplit c).f p ≫ (HomologicalComplex.biprodXIso K L p).hom ≫
      (ModuleCat.biprodIsoProd (K.X p) (L.X p)).hom) := by
    rw [key]
    exact e.toModuleIso.isIso_hom
  exact IsIso.of_isIso_comp_right ((cechSplit c).f p)
    ((HomologicalComplex.biprodXIso K L p).hom ≫ (ModuleCat.biprodIsoProd (K.X p) (L.X p)).hom)

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
/-- **Čech cohomology of a disjoint union**: `Ȟ^p(W) ≃ Ȟ^p(W|_ι) × Ȟ^p(W|_κ)`. -/
def cechCohomologySplitEquiv (hUV : ∀ i k, U i ⊓ V k = ⊥) (p : ℕ) :
    cechCohomology (SheafOfModules.unit X.ringCatSheaf) (sumLexFamily U V) c p ≃ₗ[R]
      cechCohomology (SheafOfModules.unit X.ringCatSheaf) U c p ×
        cechCohomology (SheafOfModules.unit X.ringCatSheaf) V c p :=
  have := isIso_cechSplit c hUV
  ((HomologicalComplex.homologyFunctor _ _ p).mapIso (asIso (cechSplit c (U := U) (V := V))) ≪≫
    (HomologicalComplex.homologyFunctor _ _ p).mapBiprod _ _ ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv

end Split

section DisjointUnion

variable {k : Type u} [Field k] {Z Y : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (c : k →+* Γ(Z, ⊤)) {ι : Type u} [LinearOrder ι]

/-- On the images of opens under an open immersion `j : Y ⟶ Z`, the comparison
`𝒪_Z → j_*𝒪_Y` is bijective on all nonempty intersections. -/
lemma cechStructureMap_image_bijective (W : ι → Y.Opens) (T : Finset ι) (hT : T.Nonempty) :
    Function.Bijective ((cechStructureMap j c (fun i => j ''ᵁ W i)).app T) := by
  obtain ⟨i, hi⟩ := hT
  have hle : T.inf (fun i => j ''ᵁ W i) ≤ j.opensRange :=
    (Finset.inf_le hi).trans (j.image_le_opensRange _)
  have := j.isIso_app _ hle
  exact ConcreteCategory.bijective_of_isIso (j.app (T.inf fun i => j ''ᵁ W i))

/-- `Č(𝒪_Z, j(W)) ≅ Č(𝒪_Y, j⁻¹(j(W)))` for an open immersion `j : Y ⟶ Z`. -/
def cechComplexImageIso (W : ι → Y.Opens) :
    cechComplex (SheafOfModules.unit Z.ringCatSheaf) (fun i => j ''ᵁ W i) c ≅
      cechComplex (SheafOfModules.unit Y.ringCatSheaf) (fun i => j ⁻¹ᵁ (j ''ᵁ W i))
        (j.appTop.hom.comp c) :=
  @asIso _ _ _ _ (cechComplexMap (fun i => j ''ᵁ W i) c (structureMap j))
    (isIso_subsetCechComplexMap (cechStructureMap j c (fun i => j ''ᵁ W i))
      (cechStructureMap_image_bijective j c W)) ≪≫
    cechComplexPushforwardIso j (SheafOfModules.unit Y.ringCatSheaf) c (fun i => j ''ᵁ W i)

/-- A finite affine cover transported along `j⁻¹ ∘ j`. -/
def preimageImageCover (𝒰 : FiniteAffineCover Y) : FiniteAffineCover Y where
  ι := 𝒰.ι
  U i := j ⁻¹ᵁ (j ''ᵁ 𝒰.U i)
  iSup_eq_top := by simpa using 𝒰.iSup_eq_top
  isAffineOpen_inf T hT := by simpa using 𝒰.isAffineOpen_inf T hT

/-- `H^p(Y, 𝒪_Y)` is computed by the images in `Z` of a finite affine cover of `Y`. -/
def cohomologyImageIso [CompactSpace Y]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))] (𝒰 : FiniteAffineCover Y)
    (p : ℕ) :
    cechCohomology (SheafOfModules.unit Z.ringCatSheaf) (fun i => j ''ᵁ 𝒰.U i) c p ≅
      cohomology (SheafOfModules.unit Y.ringCatSheaf) (j.appTop.hom.comp c) p :=
  (HomologicalComplex.homologyFunctor _ _ p).mapIso (cechComplexImageIso j c 𝒰.U) ≪≫
    (cohomologyIsoCech (SheafOfModules.unit Y.ringCatSheaf) (j.appTop.hom.comp c)
      (preimageImageCover j 𝒰) p).symm

variable {U V : Scheme.{u}} (iU : U ⟶ Z) (iV : V ⟶ Z) [IsOpenImmersion iU] [IsOpenImmersion iV]

/-- The finite affine cover of `Z = U ⊔ V` by the images of finite affine covers of `U` and
`V`. -/
def FiniteAffineCover.ofDisjointUnion [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Z))]
    (hcov : iU.opensRange ⊔ iV.opensRange = ⊤) (𝒰 : FiniteAffineCover U)
    (𝒱 : FiniteAffineCover V) : FiniteAffineCover Z where
  ι := 𝒰.ι ⊕ₗ 𝒱.ι
  U := sumLexFamily (fun i => iU ''ᵁ 𝒰.U i) (fun k => iV ''ᵁ 𝒱.U k)
  iSup_eq_top := by
    refine top_unique fun x _ => ?_
    have hx : x ∈ iU.opensRange ⊔ iV.opensRange := hcov ▸ trivial
    rcases (Opens.mem_sup.1 hx) with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have hy : y ∈ ⨆ i, 𝒰.U i := 𝒰.iSup_eq_top ▸ trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
      exact Opens.mem_iSup.2 ⟨inlLex i, (iU.apply_mem_image_iff).2 hi⟩
    · have hy : y ∈ ⨆ i, 𝒱.U i := 𝒱.iSup_eq_top ▸ trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
      exact Opens.mem_iSup.2 ⟨inrLex i, (iV.apply_mem_image_iff).2 hi⟩
  isAffineOpen_inf := isAffineOpen_inf_sumLexFamily
    (fun i => (𝒰.isAffineOpen i).image_of_isOpenImmersion iU)
    (fun k => (𝒱.isAffineOpen k).image_of_isOpenImmersion iV)

variable [CompactSpace Z] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Z))]
  [CompactSpace U] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from U))]
  [CompactSpace V] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from V))]

/-- **Cohomology of a disjoint union**: if `Z` is the disjoint union of the open subschemes
`U` and `V`, then `H^p(Z, 𝒪_Z) ≃ H^p(U, 𝒪_U) × H^p(V, 𝒪_V)`. -/
theorem nonempty_cohomologyUnitEquivProd (hdisj : Disjoint iU.opensRange iV.opensRange)
    (hcov : iU.opensRange ⊔ iV.opensRange = ⊤) (p : ℕ) :
    Nonempty (cohomology (SheafOfModules.unit Z.ringCatSheaf) c p ≃ₗ[k]
      cohomology (SheafOfModules.unit U.ringCatSheaf) (iU.appTop.hom.comp c) p ×
        cohomology (SheafOfModules.unit V.ringCatSheaf) (iV.appTop.hom.comp c) p) := by
  let 𝒰 := FiniteAffineCover.choose U
  let 𝒱 := FiniteAffineCover.choose V
  let 𝒲 := FiniteAffineCover.ofDisjointUnion iU iV hcov 𝒰 𝒱
  have hUV : ∀ i k, iU ''ᵁ 𝒰.U i ⊓ iV ''ᵁ 𝒱.U k = ⊥ := fun i k =>
    le_bot_iff.1 ((inf_le_inf (iU.image_le_opensRange _) (iV.image_le_opensRange _)).trans
      hdisj.le_bot)
  exact ⟨(cohomologyIsoCech (SheafOfModules.unit Z.ringCatSheaf) c 𝒲 p).toLinearEquiv.trans
    ((cechCohomologySplitEquiv c hUV p).trans (LinearEquiv.prodCongr
      (cohomologyImageIso iU c 𝒰 p).toLinearEquiv (cohomologyImageIso iV c 𝒱 p).toLinearEquiv))⟩

/-- **The Euler characteristic is additive over disjoint unions**: if `Z = U ⊔ V` (open
subschemes with disjoint ranges covering `Z`) and `H^*(Z, 𝒪_Z)` is finite-dimensional, then so are
`H^*(U, 𝒪_U)` and `H^*(V, 𝒪_V)`, and `χ(Z, 𝒪_Z) = χ(U, 𝒪_U) + χ(V, 𝒪_V)`. -/
theorem eulerChar_eq_add_of_isCompl (hdisj : Disjoint iU.opensRange iV.opensRange)
    (hcov : iU.opensRange ⊔ iV.opensRange = ⊤)
    (hfin : ∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit Z.ringCatSheaf) c i)) :
    (∀ i, FiniteDimensional k
        (cohomology (SheafOfModules.unit U.ringCatSheaf) (iU.appTop.hom.comp c) i)) ∧
      (∀ i, FiniteDimensional k
        (cohomology (SheafOfModules.unit V.ringCatSheaf) (iV.appTop.hom.comp c) i)) ∧
      eulerChar Z c = eulerChar U (iU.appTop.hom.comp c) + eulerChar V (iV.appTop.hom.comp c) := by
  classical
  have e := fun i => (nonempty_cohomologyUnitEquivProd c iU iV hdisj hcov i).some
  have hU : ∀ i, FiniteDimensional k
      (cohomology (SheafOfModules.unit U.ringCatSheaf) (iU.appTop.hom.comp c) i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.fst k _ _).comp (e i).toLinearMap)
      ((LinearMap.fst_surjective (R := k)).comp (e i).surjective)
  have hV : ∀ i, FiniteDimensional k
      (cohomology (SheafOfModules.unit V.ringCatSheaf) (iV.appTop.hom.comp c) i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.snd k _ _).comp (e i).toLinearMap)
      ((LinearMap.snd_surjective (R := k)).comp (e i).surjective)
  refine ⟨hU, hV, ?_⟩
  let 𝒰 := FiniteAffineCover.choose U
  let 𝒱 := FiniteAffineCover.choose V
  let 𝒲 := FiniteAffineCover.ofDisjointUnion iU iV hcov 𝒰 𝒱
  have := Fintype.ofFinite 𝒰.ι
  have := Fintype.ofFinite 𝒱.ι
  have := Fintype.ofFinite 𝒲.ι
  have hcard : Fintype.card 𝒲.ι = Fintype.card 𝒰.ι + Fintype.card 𝒱.ι := by
    simp only [← Nat.card_eq_fintype_card]
    change Nat.card (Lex (𝒰.ι ⊕ 𝒱.ι)) = _
    rw [Nat.card_congr toLex.symm, Nat.card_sum]
  set N := Fintype.card 𝒲.ι
  have hN : Fintype.card 𝒰.ι ≤ N ∧ Fintype.card 𝒱.ι ≤ N := by omega
  have hZ0 : ∀ i, N ≤ i →
      Subsingleton (cohomology (SheafOfModules.unit Z.ringCatSheaf) c i) := fun i hi =>
    ModuleCat.subsingleton_of_isZero
      (isZero_cohomology_of_card_le (SheafOfModules.unit Z.ringCatSheaf) c 𝒲 i hi)
  have hU0 : ∀ i, N ≤ i → Subsingleton (cohomology (SheafOfModules.unit U.ringCatSheaf)
      (iU.appTop.hom.comp c) i) := fun i hi =>
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_of_card_le
      (SheafOfModules.unit U.ringCatSheaf) _ 𝒰 i (hN.1.trans hi))
  have hV0 : ∀ i, N ≤ i → Subsingleton (cohomology (SheafOfModules.unit V.ringCatSheaf)
      (iV.appTop.hom.comp c) i) := fun i hi =>
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_of_card_le
      (SheafOfModules.unit V.ringCatSheaf) _ 𝒱 i (hN.2.trans hi))
  rw [eulerChar, eulerChar, eulerChar, homologyEulerChar_eq_sum _ N hZ0,
    homologyEulerChar_eq_sum _ N hU0, homologyEulerChar_eq_sum _ N hV0, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := (e i).finrank_eq
  rw [Module.finrank_prod] at h
  change (-1 : ℤ) ^ i * (finrank k (cohomology (SheafOfModules.unit Z.ringCatSheaf) c i) : ℤ) =
    (-1 : ℤ) ^ i * finrank k (cohomology (SheafOfModules.unit U.ringCatSheaf)
      (iU.appTop.hom.comp c) i) + (-1 : ℤ) ^ i * finrank k
        (cohomology (SheafOfModules.unit V.ringCatSheaf) (iV.appTop.hom.comp c) i)
  rw [h]
  push_cast
  ring

end DisjointUnion

end

end DeJongAlterations.StableModification.CurvesField.Genus
