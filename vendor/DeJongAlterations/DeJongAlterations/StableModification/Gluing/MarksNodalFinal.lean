/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lanes T45B, T45E, T45D, T45G)
-/
import DeJongAlterations.StableModification.Gluing.MarksNodal
import DeJongAlterations.StableModification.Gluing.MarksSeparation

/-!
# A nodal modification with separated marks over a valuation ring, unconditionally

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Proposition 4.5.1 (`sepclosprop`, T:3243–3266) with Lemma 4.3.2 (`divlem`, T:3019–3046), in the
form of `PLAN-T5.md` §2.2 steps 1–8 with marks (node V2).

Lane T45E's `Gluing.StableVal.exists_marked_nodal_modification` (`Gluing/MarksNodal.lean`) takes
projective separation of marks, `StableVal.ProjectiveSeparation R`, as a hypothesis: it is used
for the local models with separated marks at the closed bad points of the normalized refinement
`N` (lane T45B's `StableVal.exists_local_marked_model`). Lane T45D proved these local models
without any hypothesis, in the form of a piece of the projective refinement
(`StableVal.exists_local_marked_model_of_piece`, `Gluing/MarksSeparation.lean`): the strictly
semi-stable model `Bᵢ → ν⁻¹(Wᵢ)` of lane T45C is projective over the ring `Eᵢ` of the affine piece
`Spec Eᵢ → C` through `Wᵢ → Spec Eᵢ`, so the marks can be separated on `Bᵢ` (projectivity being
preserved by the separating blow-ups) before restricting to the neighbourhood `O_x` of the bad
point `x`.

This file restates `exists_marked_nodal_modification` with that local model, hence **without the
hypothesis `ProjectiveSeparation R`** (and for `K` algebraically closed, which is what the
separation over `R` needs: `K` separably closed). The proof is lane T45E's, the only change being
the local models.

## Main results

* `exists_marked_nodal_modification`: the nodal modification with separated marks over a valuation
  ring of finite height and equal characteristic of an algebraically closed field, with no named
  hypothesis.

Blueprint: `sm-gluing-existence-final.tex`, `thm:sm-gluing-existence-final-marked-nodal`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.MarksNodalFinal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open Geometry.ModificationCenter (isomorphismOpen center)
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open Curves (IsStrictlySemistable)
open ValCurves (genericPt)
open StableVal

set_option backward.isDefEq.respectTransparency false

section Assembly

variable {K : Type u} [Field K] {R : ValuationSubring K}

local notation "s₀" => IsLocalRing.closedPoint R

/-- **A nodal modification with separated marks, unconditionally** (Temkin, proof of
Proposition 4.5.1, T:3243–3266, with Lemma 4.3.2 `divlem`; `PLAN-T5.md` §2.2 steps 1–8 with marks,
node V2): lane T45E's `StableVal.exists_marked_nodal_modification` without the hypothesis
`ProjectiveSeparation R`. Let `K` be algebraically closed, `R ⊆ K` a valuation ring of finite
height and equal characteristic, and `φ : C → Spec R` a proper flat relative curve, integral,
separated and quasi-compact, with `trdeg K(C)/K = 1`, normal at the points over the generic point,
and let `σ k` be finitely many sections of `φ` with pairwise distinct generic points. Then there
are a modification `b : N → C` (the normalized projective refinement, flat and of finite
presentation over `R`, and projective over `R` if `C` is) and a modification `β : X → N` such that
`X` is a nodal curve over `R`, locally projective over `N`, and the lifts `σX k` of the sections
are pairwise disjoint and pass through smooth points of `X → Spec R`.

The local models with separated marks at the closed bad points are lane T45D's
`StableVal.exists_local_marked_model_of_piece`, applied to the pieces of the projective refinement
and their projective strictly semi-stable models (lane T45C). -/
theorem exists_marked_nodal_modification [IsAlgClosed K] [Finite (PrimeSpectrum R)]
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField R) p)
    {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated] [CompactSpace C] (φ : C ⟶ Spec (.of R))
    [IsProper φ] [Flat φ] (htr : fiberTrdeg φ (genericPoint C) = 1)
    (hnorm : ∀ x : C, φ x = genericPoint (Spec (.of R)) →
      IsIntegrallyClosed (C.presheaf.stalk x))
    {n : ℕ} (σ : Fin n → (Spec (.of R) ⟶ C)) (hσ : ∀ k, σ k ≫ φ = 𝟙 _)
    (hinj : Function.Injective fun k ↦ σ k (genericPoint (Spec (.of R)))) :
    ∃ (N : Scheme.{u}) (_ : IsIntegral N) (b : N ⟶ C) (X : Scheme.{u}) (β : X ⟶ N)
      (σX : Fin n → (Spec (.of R) ⟶ X)),
      IsModification b ∧ IsModification β ∧ Flat (b ≫ φ) ∧
      LocallyOfFinitePresentation (b ≫ φ) ∧ (IsProjectiveOver φ → IsProjectiveOver (b ≫ φ)) ∧
      IsNodalCurve (β ≫ b ≫ φ) ∧ Projectivity.LocallyRelativelyProjective (b ≫ φ) β ∧
      (∀ k, σX k ≫ β ≫ b = σ k) ∧
      (∀ k l, k ≠ l → Disjoint (Set.range (σX k)) (Set.range (σX l))) ∧
      (∀ k t, IsSmoothAt (β ≫ b ≫ φ) (σX k t)) := by
  classical
  -- the projective refinement and its projective strictly semi-stable models (T45A, T45C)
  obtain ⟨C', p, hp, hpproj, ι, hι, E, _, _, g, W, h, hW, hpieces⟩ :=
    exists_projective_refinement hchar φ htr
  have := hp
  have := hp.sourceIntegral
  have hA4 := CofinalProjective.projectiveCofinality R
  have hmodels : ∀ i, ∃ (B : Scheme.{u}) (_ : IsIntegral B) (f : B ⟶ Spec (.of (E i)))
      (_ : IsModification f), IsStrictlySemistable (f ≫ g i ≫ φ) ⊤ ∧
        DeJong.IsRelativelyProjective (g i ≫ φ) f ∧ ∃ q : B ⟶ (W i).toScheme, q ≫ h i = f := by
    intro i
    obtain ⟨hss, htri, -, hhm, -⟩ := hpieces i
    exact hA4 (E i) (g i ≫ φ) hss htri (h i) hhm
  choose B hBi f hfm hfss hfproj q hq using hmodels
  have hhm : ∀ i, IsModification (h i) := fun i ↦ (hpieces i).2.2.2.1
  have hhg : ∀ i, h i ≫ g i = (W i).ι ≫ p := fun i ↦ (hpieces i).2.2.1
  have hqm : ∀ i, IsModification (q i) := by
    intro i
    have := hhm i
    have := hfm i
    have : IsModification (q i ≫ h i) := by rw [hq i]; infer_instance
    exact isModification_of_comp (q i) (h i)
  have hcomp : ∀ i, q i ≫ (W i).ι ≫ p ≫ φ = f i ≫ g i ≫ φ := fun i ↦ by
    rw [← Category.assoc (W i).ι, ← hhg i, Category.assoc, ← Category.assoc (q i), hq i]
  have hqnod : ∀ i, IsNodalCurve (q i ≫ (W i).ι ≫ p ≫ φ) := fun i ↦ by
    rw [hcomp i]
    exact (hfss i).isNodalCurve
  have hqflat : ∀ i, Flat (q i ≫ (W i).ι ≫ p ≫ φ) := fun i ↦ (hqnod i).toFlat
  have hqproj : ∀ i, DeJong.IsRelativelyProjective ((W i).ι ≫ p ≫ φ) (q i) := by
    intro i
    have := hhm i
    have h1 := BlowDown.NoClosedExc.isRelativelyProjective_of_comp (g i ≫ φ) (q i) (h i)
      (by rw [hq i]; exact hfproj i)
    rwa [← Category.assoc, hhg i, Category.assoc] at h1
  have hqnorm : ∀ i, IsNormalScheme (B i) := fun i ↦
    LocalUniformization.isNormalScheme_of_isStrictlySemistable (isNormalScheme_spec R) (hfss i)
  -- `C'` over `R`
  have : IsProper p := hp.toIsProper
  have hgen : (p ≫ φ) (genericPoint C') = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, Geometry.NormalCurveModification.genericPoint_map p hp.birational]
    exact apply_genericPoint_eq_bot_of_flat φ
  have : Flat (p ≫ φ) := flat_of_apply_genericPoint_eq_bot (p ≫ φ) hgen
  have : LocallyOfFinitePresentation (p ≫ φ) := locallyOfFinitePresentation_of_flat (p ≫ φ)
  have hdim : fiberTrdeg (p ≫ φ) (genericPoint C') ≤ 1 := by
    rw [ValCurves.fiberTrdeg_comp_genericPoint φ p, htr]
  have hsep : ∀ P : PrimeSpectrum R, IsSepClosed (FractionRing (R ⧸ P.asIdeal)) :=
    fun P ↦ Cohomology.Connected.isSepClosed_fractionRing_quotient K P
  -- the normalization `N` of `C'` and the local models `τᵢ : Bᵢ → ν⁻¹(Wᵢ)`
  have hfin : IsFinite (genericPt C').fromNormalization :=
    isFinite_fromNormalization_genericPt q (p ≫ φ) hW hqnorm hqflat hqproj
  set ν := (genericPt C').fromNormalization with hνdef
  have hν : IsModification ν := isModification_fromNormalization_genericPt
  have hN : IsNormalScheme (genericPt C').normalization := isNormalScheme_normalization_genericPt
  have := hν.sourceIntegral
  set pN := ν ≫ p ≫ φ with hpNdef
  have hdimN : fiberTrdeg pN (genericPoint (genericPt C').normalization) ≤ 1 := by
    rw [hpNdef, ValCurves.fiberTrdeg_comp_genericPoint (p ≫ φ) ν]
    exact hdim
  have hflatN : Flat pN := flat_fromNormalization_genericPt q (p ≫ φ) hW hqnorm hqflat hqproj
  have hlfpN : LocallyOfFinitePresentation pN :=
    locallyOfFinitePresentation_fromNormalization_genericPt q (p ≫ φ) hW hqnorm hqflat hqproj
  have : IsProper pN := by rw [hpNdef]; infer_instance
  choose ji hji using fun i ↦ isoOver_restrict_normalization_genericPt q i (hqnorm i)
  let τ : ∀ i, B i ⟶ (ν ⁻¹ᵁ W i).toScheme := fun i ↦ (q i).toNormalization ≫ (ji i).inv
  have hτ : ∀ i, τ i ≫ (ν ∣_ W i) = q i := fun i ↦ by
    change ((q i).toNormalization ≫ (ji i).inv) ≫ ν ∣_ W i = q i
    rw [← hji i, Category.assoc, Iso.inv_hom_id_assoc, Scheme.Hom.toNormalization_fromNormalization]
  have hτm : ∀ i, IsModification (τ i) := by
    intro i
    have hmod : IsModification (q i) := inferInstance
    have := hmod.targetIntegral
    have : Nonempty (W i) := (inferInstance : Nonempty (W i).toScheme)
    have := Geometry.CurveCompactification.isModification_morphismRestrict ν (W i)
    have : IsModification (τ i ≫ ν ∣_ W i) := by rw [hτ i]; infer_instance
    exact isModification_of_comp (τ i) (ν ∣_ W i)
  have hτO : ∀ i, τ i ≫ (ν ⁻¹ᵁ W i).ι ≫ ν = q i ≫ (W i).ι := fun i ↦ by
    rw [← morphismRestrict_ι, ← Category.assoc, hτ i]
  have hτss : ∀ i, IsStrictlySemistable (τ i ≫ (ν ⁻¹ᵁ W i).ι ≫ pN) ⊤ := fun i ↦ by
    have e : τ i ≫ (ν ⁻¹ᵁ W i).ι ≫ pN = f i ≫ g i ≫ φ := by
      rw [hpNdef, ← Category.assoc ((ν ⁻¹ᵁ W i).ι), ← Category.assoc (τ i), hτO i,
        Category.assoc, hcomp i]
    rw [e]
    exact hfss i
  -- the sections of `N`
  have hbmod : IsModification (ν ≫ p) := IsModification.comp ν p
  choose σN hσN using fun k ↦ exists_lift_section φ hnorm htr.le (ν ≫ p) (σ k) (hσ k)
  have hσNsec : ∀ k, σN k ≫ pN = 𝟙 _ := fun k ↦ by
    rw [hpNdef, ← Category.assoc ν, ← Category.assoc, hσN, hσ]
  have hinjN : Function.Injective fun k ↦ σN k (genericPoint (Spec (.of R))) := by
    intro k l hkl
    apply hinj
    change σ k _ = σ l _
    rw [← hσN k, ← hσN l, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg (ν ≫ p) hkl
  -- the good locus and the closed bad points
  have hτn : ∀ i, IsNodalCurve (τ i ≫ (ν ⁻¹ᵁ W i).ι ≫ pN) := fun i ↦ (hτss i).isNodalCurve
  have hcovN : ⨆ i, ν ⁻¹ᵁ W i = ⊤ := iSup_preimage_eq_top ν hW
  have hpiece : ∀ y : (genericPt C').normalization, ∃ i, y ∈ ν ⁻¹ᵁ W i := fun y ↦
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hcovN]; trivial)
  choose ix hix using hpiece
  have hnodal_of : ∀ y : (genericPt C').normalization, y ∉ localCenter (ν ⁻¹ᵁ W (ix y)) (τ (ix y)) →
      y ∈ Curves.SemistableOpen.nodalLocus pN := fun y hy ↦ by
    have hiso := mem_isomorphismOpen_of_not_mem_localCenter (ν ⁻¹ᵁ W (ix y)) (τ (ix y))
      (z := ⟨y, hix y⟩) hy
    exact image_isomorphismOpen_le_nodalLocus pN (ν ⁻¹ᵁ W (ix y)) (τ (ix y)) (hτn _)
      ⟨⟨y, hix y⟩, hiso, rfl⟩
  set G := goodOpen pN σN hσNsec with hGdef
  have hbad_sub : ((G : Set (genericPt C').normalization)ᶜ) ⊆
      (⋃ i, localCenter (ν ⁻¹ᵁ W i) (τ i)) ∪ ⋃ k, Set.range (σN k) := by
    intro y hy
    by_cases hyn : y ∈ Curves.SemistableOpen.nodalLocus pN
    · have hb : y ∈ markBad pN σN := by
        by_contra hb
        exact hy ⟨hyn, hb⟩
      obtain ⟨k, hk, -⟩ := Set.mem_iUnion.mp hb
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, hk⟩)
    · left
      refine Set.mem_iUnion.mpr ⟨ix y, ?_⟩
      by_contra hc
      exact hyn (hnodal_of y hc)
  have hbadfin : ((G : Set (genericPt C').normalization)ᶜ).Finite := by
    refine Set.Finite.subset (Set.Finite.union ?_ ?_) hbad_sub
    · exact Set.finite_iUnion fun i ↦ by
        have := hτm i
        exact finite_localCenter pN (τ i) hN hdimN
    · have : Finite (Spec (.of R)) := inferInstanceAs (Finite (PrimeSpectrum R))
      exact Set.finite_iUnion fun k ↦ Set.finite_range (σN k)
  let Sc : Set (genericPt C').normalization := {x | x ∉ G ∧ IsClosed ({x} : Set _)}
  have hScfin : Sc.Finite := hbadfin.subset fun x hx ↦ hx.1
  have : Finite Sc := hScfin.to_subtype
  -- the local models at the closed bad points
  let Ox : Sc → (genericPt C').normalization.Opens := fun x ↦
    ν ⁻¹ᵁ W (ix x.1) ⊓ throughOpen pN σN hσNsec x.1
  have hxOx : ∀ x : Sc, x.1 ∈ Ox x := fun x ↦
    ⟨hix x.1, mem_throughOpen_self pN σN hσNsec x.2.2⟩
  have hlocal : ∀ x : Sc, ∃ (Bx : Scheme.{u}) (τx : Bx ⟶ Ox x),
      IsModification τx ∧ DeJong.IsRelativelyProjective ((Ox x).ι ≫ pN) τx ∧
      IsNodalCurve (τx ≫ (Ox x).ι ≫ pN) ∧ (Ox x).ι ''ᵁ isomorphismOpen τx ≤ G ∧
      ∃ σx : (k : Fin n) → σN k s₀ = x.1 → (Spec (.of R) ⟶ Bx),
        (∀ k hk, σx k hk ≫ τx ≫ (Ox x).ι = σN k) ∧
        (∀ k hk t, IsSmoothAt (τx ≫ (Ox x).ι ≫ pN) (σx k hk t)) ∧
        (∀ k hk l hl, k ≠ l → Disjoint (Set.range (σx k hk)) (Set.range (σx l hl))) := by
    intro x
    have := hτm (ix x.1)
    have := hhm (ix x.1)
    have : IsNodalCurve (g (ix x.1) ≫ φ) := (hpieces (ix x.1)).1.isNodalCurve
    exact exists_local_marked_model_of_piece hN pN hdimN σN hσNsec hinjN ν (p ≫ φ) rfl
      (W (ix x.1)) (h (ix x.1)) (g (ix x.1) ≫ φ) (by rw [← Category.assoc, hhg, Category.assoc])
      (τ (ix x.1)) (hτss _) (f (ix x.1)) (hfproj (ix x.1)) (by rw [← Category.assoc, hτ, hq])
      (hix x.1) x.2.2
  choose Bx τx hτxm hτxp hτxn hτxG σx hσx hσxsm hσxdisj using hlocal
  -- the good locus is nonempty
  have hξG : genericPoint (genericPt C').normalization ∈ G := by
    refine ⟨hnodal_of _ (by
      have := hτm (ix (genericPoint (genericPt C').normalization))
      exact genericPoint_not_mem_localCenter _ _), ?_⟩
    show genericPoint (genericPt C').normalization ∉ markBad pN σN
    rw [not_mem_markBad_iff]
    intro k t hkt
    exfalso
    have h0 := fiberTrdeg_section_apply pN (σN k) (hσNsec k) t
    have h1 : fiberTrdeg pN (genericPoint (genericPt C').normalization) = 1 := by
      rw [hpNdef, ValCurves.fiberTrdeg_comp_genericPoint (p ≫ φ) ν,
        ValCurves.fiberTrdeg_comp_genericPoint φ p, htr]
    rw [hkt, h1] at h0
    exact one_ne_zero h0
  have : Nonempty G := ⟨⟨_, hξG⟩⟩
  -- the cover by `G` and the local models
  have hcov : G ⊔ ⨆ x, Ox x = ⊤ := by
    have : CompactSpace (genericPt C').normalization := BlowDown.compactSpace_of_quasiCompact pN
    refine eq_top_iff.mpr fun y _ ↦ ?_
    by_cases hy : y ∈ G
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hy)
    · obtain ⟨x, hxy, hxc⟩ :=
        (isClosed_closure (s := ({y} : Set (genericPt C').normalization))).exists_closed_singleton
          ⟨y, subset_closure rfl⟩
      have hyx : y ⤳ x := specializes_iff_mem_closure.mpr hxy
      have hxG : x ∉ G := fun hx ↦ hy (hyx.mem_open G.isOpen hx)
      exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr (TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨x, hxG, hxc⟩, hyx.mem_open (Ox ⟨x, hxG, hxc⟩).isOpen (hxOx ⟨x, hxG, hxc⟩)⟩))
  have hGn : IsNodalCurve (G.ι ≫ pN) :=
    Curves.SemistableOpen.isNodalCurve_of_le_nodalLocus _ inf_le_left
  have := hτxm
  obtain ⟨X, β, hβ, hXn, hXp, κ, hκ, U, j, hcovU, hU⟩ :=
    exists_modification_of_localModifications_id hsep hN pN hdimN Ox τx G hcov hτxG hGn hτxn
      hτxp
  -- the sections of `X`
  have hnormN : ∀ y : (genericPt C').normalization, pN y = genericPoint (Spec (.of R)) →
      IsIntegrallyClosed ((genericPt C').normalization.presheaf.stalk y) := fun y _ ↦ (hN y).2
  choose σX hσX using fun k ↦ exists_lift_section pN hnormN hdimN β (σN k) (hσNsec k)
  -- the marks of `X`, pointwise
  have hgenx : ∀ x : Sc, ∀ w₁ w₂ : Bx x, τx x w₁ = τx x w₂ →
      pN ((Ox x).ι (τx x w₁)) = genericPoint (Spec (.of R)) → w₁ = w₂ := by
    intro x w₁ w₂ hw hη
    have := hτxm x
    have : Nonempty (Ox x) := ⟨⟨x.1, hxOx x⟩⟩
    have : IsIntegral (Ox x).toScheme := isIntegral_of_isOpenImmersion (Ox x).ι
    have hiso := isIso_restrict_genericOpen ((Ox x).ι ≫ pN)
      (fun y _ ↦ isIntegrallyClosed_stalk_opens hN _ y)
      (by rw [fiberTrdeg_genericPoint_opens]; exact hdimN) (τx x)
    refine eq_of_isIso_restrict (τx x) (((Ox x).ι ≫ pN) ⁻¹ᵁ BlowDown.genericOpen R) hw ?_
    change ((Ox x).ι ≫ pN) (τx x w₁) ∈ (BlowDown.genericOpen R : Set _)
    rw [BlowDown.coe_genericOpen]
    exact hη
  have hsepx : ∀ x : Sc, IsSeparated (τx x ≫ (Ox x).ι ≫ pN) := fun x ↦ by
    have := hτxm x
    infer_instance
  have hpt : ∀ k t, IsSmoothAt (β ≫ pN) (σX k t) ∧ ∀ l, l ≠ k → σX l t ≠ σX k t := by
    intro k t
    have hyc : σN k t ∈ ⨆ m, U m := by rw [hcovU]; trivial
    obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hyc
    obtain ⟨hnone, hsome⟩ := hU m
    cases hj : j m with
    | none =>
      obtain ⟨hUG, hiso⟩ := hnone hj
      exact marks_of_iso_piece pN β σN σX hσX (U m) (fun y hy ↦ (hUG hy).2) k t hm
    | some x =>
      obtain ⟨hUO, i, hi⟩ := hsome x hj
      exact marks_of_local_piece pN β (Ox x) (U m) (τx x) i hi _
        (fun t' ↦ (genericPoint_spec (Spec (.of R))).specializes (Set.mem_univ t')) (hgenx x)
        σN hσNsec σX hσX (fun l ↦ σN l s₀ = x.1)
        (fun l t' hl ↦ (mem_throughOpen_iff pN σN hσNsec x.1 _).mp (hUO hl).2 l ⟨t', rfl⟩)
        (σx x) (hσx x) (hσxsm x) (hσxdisj x) k t hm
  refine ⟨(genericPt C').normalization, inferInstance, ν ≫ p, X, β, σX, hbmod, hβ, ?_, ?_, ?_, ?_,
    ?_, fun k ↦ ?_, fun k l hkl ↦ ?_, fun k t ↦ ?_⟩
  · rw [Category.assoc]; exact hflatN
  · rw [Category.assoc]; exact hlfpN
  · intro hφ
    rw [Category.assoc]
    exact isProjectiveOver_fromNormalization_genericPt (p ≫ φ)
      (DeJong.IsRelativelyProjective.isProjectiveOver hφ hpproj)
  · rw [Category.assoc]; exact hXn
  · rw [Category.assoc]; exact hXp
  · rw [← Category.assoc, hσX, hσN]
  · rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    have htt : t' = t := by
      have h1 := congrArg (β ≫ pN) ht'
      rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Category.assoc, hσX, hσNsec,
        ← Category.assoc, hσX, hσNsec] at h1
    subst htt
    exact (hpt k t').2 l (Ne.symm hkl) ht'
  · rw [Category.assoc]
    exact (hpt k t).1

end Assembly

end DeJongAlterations.StableModification.Gluing.MarksNodalFinal
