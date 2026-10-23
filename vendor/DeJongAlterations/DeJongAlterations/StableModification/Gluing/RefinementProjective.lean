/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.RiemannZariski.Refinement
import DeJongAlterations.StableModification.DeJong.BaseStepProjective
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
import DeJongAlterations.Geometry.ChowLemmaProduct
import DeJongAlterations.StableModification.Projectivity.Reduction

/-!
# Refinements of Riemann–Zariski covers are projective

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Lemma 3.2.3
(`ratfunlem`, `semi-stable.tex` lines 2356–2363) and Proposition 3.2.6 (`oetamodprop`,
T:2394–2409): the refinement `p : S' → S` of finitely many affine `L`-quasi-modifications is built
(lane RZ1, `RiemannZariskiSpace.exists_refinement`) from the schematic image of `η` in `S`,
graph closures in `S ×_ℤ ℙⁿ_ℤ` and schematic images in fibre products. The integrated statement
records only that `p` is proper. This file proves that `p` is **projective** over `S`
(`PLAN-T5.md` node A2, ERRATA DJA-O22; blueprint `sm-gluing-semistable.tex`,
`prop:sm-refinement-projective`), relative to any `pS : S → Spec k`:

* `IsRelativelyProjective.pullback_fst`, `IsRelativelyProjective.comp` (Segre embedding over
  `k`, Codex's `Geometry.ChowLemmaProduct.isProjectiveOver_product`; for any base `pS`, unlike
  lane OM3A's `Projectivity.isRelativelyProjective_comp`, which assumes `pS` projective):
  bookkeeping for `DeJong.IsRelativelyProjective`, with lane OM3A's
  `Projectivity.isRelativelyProjective_closedImmersion_comp`;
* `isRelativelyProjective_of_closedImmersion_terminal`: a closed subscheme of `S ×_ℤ ℙⁿ_ℤ` is
  projective relative to every `pS` (`S ×_ℤ ℙⁿ_ℤ ≅ S ×_k ℙⁿ_k`, Codex's
  `Geometry.ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap`);
* `isRelativelyProjective_graphProj`, `isRelativelyProjective_dominate`: graph closures and
  dominating refinements are projective;
* `exists_refinement_projective`: `RiemannZariskiSpace.exists_refinement` with the additional
  conclusion `IsRelativelyProjective pS p` (the induction of RZ1's
  `exists_refinement_finset` rerun with a projectivity invariant, reusing its step lemmas).

Over a projective base (`IsProjectiveOver pS`) the refinement is projective over `k`
(`DeJong.IsRelativelyProjective.isProjectiveOver`), which is PLAN-OM3's obligation E1 for the
refinements of the global argument (PLAN-T5 §2.1 step 3) and the projectivity of the curve
refinement `C' → C` of §2.2 step 2.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace DeJongAlterations.StableModification.Gluing

open DeJong RiemannZariskiSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RelProj

variable {k : Type u} [CommRing k] {X X' S S₁ S₂ : Scheme.{u}}

/-- Base change of a relatively projective morphism along the first factor. -/
theorem IsRelativelyProjective.pullback_fst {pS : S ⟶ Spec (.of k)} {p₂ : S₂ ⟶ S}
    (h : IsRelativelyProjective pS p₂) (p₁ : S₁ ⟶ S) :
    IsRelativelyProjective (p₁ ≫ pS) (pullback.fst p₁ p₂) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  exact Projectivity.isRelativelyProjective_closedImmersion_comp (h.pullback_snd p₁) _

/-- **Composition of relatively projective morphisms** (Segre embedding over `k`). -/
theorem IsRelativelyProjective.comp {pS : S ⟶ Spec (.of k)} {p : S₁ ⟶ S} {q : S₂ ⟶ S₁}
    (hp : IsRelativelyProjective pS p) (hq : IsRelativelyProjective (p ≫ pS) q) :
    IsRelativelyProjective pS (q ≫ p) := by
  obtain ⟨n, i, hi, hip⟩ := hp
  obtain ⟨m, j, hj, hjq⟩ := hq
  have := hi
  have := hj
  obtain ⟨N, σ, hσ, hσP⟩ := Geometry.ChowLemmaProduct.isProjectiveOver_product
    (projectiveSpaceStructure k n) (projectiveSpaceStructure k m)
    (isProjectiveOver_projectiveSpaceStructure k n) (isProjectiveOver_projectiveSpaceStructure k m)
  have := hσ
  have e₁ : p ≫ pS = i ≫ pullback.snd pS (projectiveSpaceStructure k n) ≫
      projectiveSpaceStructure k n := by
    rw [← pullback.condition, ← Category.assoc, hip]
  let Φ₁ : pullback (p ≫ pS) (projectiveSpaceStructure k m) ⟶
      pullback (pullback.snd pS (projectiveSpaceStructure k n) ≫ projectiveSpaceStructure k n)
        (projectiveSpaceStructure k m) :=
    pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) ((Category.comp_id _).trans e₁)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hΦ₁ : IsClosedImmersion Φ₁ :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) hi (inferInstanceAs
      (IsClosedImmersion (𝟙 _))) e₁ (Category.id_comp _).symm
  let Φ₂ := (pullbackAssoc pS (projectiveSpaceStructure k n) (projectiveSpaceStructure k n)
    (projectiveSpaceStructure k m)).hom
  let Φ₃ : pullback pS (pullback.fst (projectiveSpaceStructure k n)
      (projectiveSpaceStructure k m) ≫ projectiveSpaceStructure k n) ⟶
        pullback pS (projectiveSpaceStructure k N) :=
    pullback.map _ _ _ _ (𝟙 _) σ (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans hσP.symm)
  have hΦ₃ : IsClosedImmersion Φ₃ :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) (inferInstanceAs
      (IsClosedImmersion (𝟙 _))) hσ (Category.id_comp _).symm hσP.symm
  refine ⟨N, j ≫ Φ₁ ≫ Φ₂ ≫ Φ₃, inferInstance, ?_⟩
  have h3 : Φ₃ ≫ pullback.fst pS (projectiveSpaceStructure k N) = pullback.fst _ _ := by
    simp only [Φ₃, pullback.lift_fst, Category.comp_id]
  have h2 : Φ₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
    pullbackAssoc_hom_fst _ _ _ _
  have h1 : Φ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ i := pullback.lift_fst _ _ _
  simp only [Category.assoc]
  rw [h3, h2, reassoc_of% h1, hip, ← Category.assoc, hjq]

end RelProj

section Terminal

variable {k : Type u} [CommRing k] {S X : Scheme.{u}}

/-- **From `ℙⁿ_ℤ` to `ℙⁿ_k`.** A closed subscheme of `S ×_ℤ ℙⁿ_ℤ` is projective over `S` relative
to any `pS : S → Spec k` (`S ×_ℤ ℙⁿ_ℤ ≅ S ×_k ℙⁿ_k`, by `ℙⁿ_k ≅ ℙⁿ_ℤ ×_ℤ Spec k`). -/
theorem isRelativelyProjective_of_closedImmersion_terminal (pS : S ⟶ Spec (.of k)) {n : ℕ}
    (i : X ⟶ pullback (specULiftZIsTerminal.from S) (projectiveSpaceStructure (ULift.{u} ℤ) n))
    [IsClosedImmersion i] : IsRelativelyProjective pS (i ≫ pullback.fst _ _) := by
  let f : ULift.{u} ℤ →+* k := (Int.castRingHom k).comp ULift.ringEquiv.toRingHom
  have hT := Geometry.ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap f n
  have hterm : pS ≫ Spec.map (CommRingCat.ofHom f) = specULiftZIsTerminal.from S :=
    specULiftZIsTerminal.hom_ext _ _
  let Ψ : pullback (specULiftZIsTerminal.from S) (projectiveSpaceStructure (ULift.{u} ℤ) n) ⟶
      projectiveSpace k n :=
    hT.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pS)
      (by rw [Category.assoc, hterm, pullback.condition])
  have hsq : IsPullback Ψ (pullback.fst _ _) (projectiveSpaceStructure k n) pS := by
    refine IsPullback.of_right (h₁₂ := _) (h₂₂ := Spec.map (CommRingCat.ofHom f)) (v₁₃ := projectiveSpaceStructure (ULift.{u} ℤ) n)
      ?_ (hT.lift_snd _ _ _) hT
    rw [hT.lift_fst, hterm]
    exact (IsPullback.of_hasPullback _ _).flip
  exact ⟨n, i ≫ hsq.flip.isoPullback.hom, inferInstance,
    by rw [Category.assoc, hsq.flip.isoPullback_hom_fst]⟩

end Terminal

section Refinement

variable {L : Type u} [Field L] {k : Type u} [CommRing k] {S : Scheme.{u}}
  (pS : S ⟶ Spec (.of k))

/-- The graph closure of finitely many elements of `L` is projective over `S` (it is a closed
subscheme of `S ×_ℤ ℙⁿ_ℤ`). -/
theorem isRelativelyProjective_graphProj (η : Spec (.of L) ⟶ S) (n : ℕ)
    (f : Geometry.ProjectiveIdeal.ChartIndex (0 : Fin (n + 1)) → L) :
    IsRelativelyProjective pS (graphProj η n f) :=
  isRelativelyProjective_of_closedImmersion_terminal pS (graphPoint η n f).imageι

/-- The refinement dominating two projective refinements is projective. -/
theorem isRelativelyProjective_dominate {S₁ S₂ : Scheme.{u}} {p₁ : S₁ ⟶ S} {p₂ : S₂ ⟶ S}
    {η₁ : Spec (.of L) ⟶ S₁} {η₂ : Spec (.of L) ⟶ S₂} (hη : η₁ ≫ p₁ = η₂ ≫ p₂)
    (hp₁ : IsRelativelyProjective pS p₁) (hp₂ : IsRelativelyProjective pS p₂) :
    IsRelativelyProjective pS ((dominatePoint hη).imageι ≫ pullback.fst p₁ p₂ ≫ p₁) :=
  Projectivity.isRelativelyProjective_closedImmersion_comp
    (IsRelativelyProjective.comp hp₁ (IsRelativelyProjective.pullback_fst hp₂ p₁)) _

variable [S.IsSeparated] (η : Spec (.of L) ⟶ S) {ι : Type*} (T : ι → Scheme.{u})
  [∀ i, IsAffine (T i)] (g : ∀ i, T i ⟶ S) [∀ i, LocallyOfFiniteType (g i)]
  (ηT : ∀ i, Spec (.of L) ⟶ T i)

/-- **Projective refinement, finite-set form**: `RiemannZariskiSpace.exists_refinement_finset`
with the refinement projective over `S` relative to `pS`. -/
theorem exists_refinement_finset_projective (hηT : ∀ i, ηT i ≫ g i = η) (V : ι → S.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hgV : ∀ i, g i ⁻¹ᵁ V i = ⊤) (s : Finset ι) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (F : Set L),
      IsRefinement η p η' ∧ F.Finite ∧ HasCharts η p η' F ∧
      (∀ i ∈ s, Realizes p η' (g i) (ηT i)) ∧ IsRelativelyProjective pS p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := image_isRefinement_hasCharts η
    exact ⟨_, _, _, ∅, h1, Set.finite_empty, h2, by simp,
      isRelativelyProjective_of_isClosedImmersion pS _⟩
  | insert i s hi ih =>
    obtain ⟨S', p, η', F, hR, hF, hC, hReal, hP⟩ := ih
    obtain ⟨n, f, hfr⟩ := exists_graph_realizes η (g i) (ηT i) (hηT i) (hV i) (hgV i)
    have hη : η' ≫ p = (graphPoint η n f).toImage ≫ graphProj η n f := by
      rw [hR.comp_eq, (graph_isRefinement η n f).comp_eq]
    refine ⟨_, _, _, F ∪ Set.range f,
      dominate_isRefinement hR (graph_isRefinement η n f) hη, hF.union (Set.finite_range f),
      dominate_hasCharts hη hC (graph_hasCharts η n f), ?_,
      isRelativelyProjective_dominate pS hη hP (isRelativelyProjective_graphProj pS η n f)⟩
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact dominate_realizes_right hη hR.isProper hfr
    · exact dominate_realizes_left hη (graph_isRefinement η n f).isProper (hReal j hj)

/-- **Projective refinement of Riemann–Zariski covers** (Temkin, Proposition 3.2.6 `oetamodprop`,
with the covering addendum; node A2 of `PLAN-T5.md`, blueprint `prop:sm-refinement-projective`):
the conclusion of `RiemannZariskiSpace.exists_refinement`, together with the projectivity of the
refinement `p : S' → S` relative to any `pS : S → Spec k` (the refinement is a closed subscheme of
`S ×_ℤ ℙᴺ_ℤ`). -/
theorem exists_refinement_projective [Finite ι] (hηT : ∀ i, ηT i ≫ g i = η) (V : ι → S.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hgV : ∀ i, g i ⁻¹ᵁ V i = ⊤) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (F : Set L)
      (W : ι → S'.Opens) (h : ∀ i, (W i).toScheme ⟶ T i),
      IsRefinement η p η' ∧ F.Finite ∧ HasCharts η p η' F ∧
      (∀ i, IsProper (h i) ∧ h i ≫ g i = (W i).ι ≫ p ∧
        ∃ e : Spec (.of L) ⟶ (W i).toScheme, e ≫ (W i).ι = η' ∧ e ≫ h i = ηT i ∧
          IsDominant e) ∧
      (∀ i, ∀ V' ∈ ofScheme (ηT i), ∃ ψ : Spec (.of V'.valuationSubring) ⟶ S',
        toSpecValuationSubring V' ≫ ψ = η' ∧ ψ (specClosedPoint V') ∈ W i) ∧
      (ofScheme η ⊆ ⋃ i, ofScheme (ηT i) → ⨆ i, W i = ⊤) ∧
      IsRelativelyProjective pS p := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨S', p, η', F, hR, hF, hC, hReal, hP⟩ :=
    exists_refinement_finset_projective pS η T g ηT hηT V hV hgV Finset.univ
  choose W h hh hcomm he hRZ using fun i => hReal i (Finset.mem_univ i)
  have := hR.isDominant
  refine ⟨S', p, η', F, W, h, hR, hF, hC, fun i => ⟨hh i, hcomm i, ?_⟩, hRZ, ?_, hP⟩
  · obtain ⟨e, he1, he2⟩ := he i
    have : IsDominant (e ≫ (W i).ι) := by rw [he1]; infer_instance
    exact ⟨e, he1, he2, isDominant_of_comp_isOpenImmersion e (W i).ι⟩
  · intro hcov
    have := hR.isProper
    have := isSeparated_of_isProper p
    rw [eq_top_iff]
    intro x _
    obtain ⟨V', ψ, hψ, rfl⟩ := hR.exists_extension x
    have hV' : V' ∈ ofScheme η := ⟨ψ ≫ p, by rw [← Category.assoc, hψ, hR.comp_eq]⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hV')
    obtain ⟨ψ', hψ', hψ'W⟩ := hRZ i V' hi
    rw [extension_unique hψ hψ']
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hψ'W⟩

end Refinement

end DeJongAlterations.StableModification.Gluing
