/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lanes T45B, T45E)
-/
import DeJongAlterations.StableModification.Gluing.MarksModel

/-!
# A nodal modification with separated marks over a valuation ring

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (`sepclosprop`, T:3243–3266), in the form of `PLAN-T5.md` §2.2 steps 1–8 **with
marks** (node V2; the pair version of lane T45A's `Gluing.exists_nodal_modification`). Let `K` be
algebraically closed, `R ⊆ K` a valuation ring of finite height and equal characteristic, and
`φ : C → Spec R` a proper flat integral relative curve, normal along its generic fibre, with
finitely many sections `σ k` with pairwise distinct generic points. Then there are the normalized
projective refinement `b : N → C` (lane T45A) and a modification `β : X → N` such that `X` is a
nodal curve over `R`, locally projective over `N`, and the lifts `σX k` of the sections to `X` are
pairwise disjoint and pass through smooth points of `X → Spec R`
(`exists_marked_nodal_modification`).

The construction (lane T45B's draft, completed by lane T45E): the sections lift to `N`
(`exists_lift_section`); the good locus `G` of `(N, ⋃ₖ σN k)` (`goodOpen`) is covered by the
identity, and each closed point `x ∉ G` by a local model with separated marks
(`exists_local_marked_model`, built from lane T45A/T45C's projective strictly semi-stable models
of the pieces of the refinement and the hypothesis `ProjectiveSeparation R`); the local models are
inserted by the identity (`exists_modification_of_localModifications_id`). The marks of `X` are
analysed pointwise: over the part where `β` is an isomorphism onto an open of `G` they are those
of `N` (`marks_of_iso_piece`), over a local model they correspond to the separated lifted
sections (`marks_of_local_piece`, via `IsoOver.apply_section_eq`).

`marks_of_local_piece` is stated over an arbitrary domain `R` (not a `ValuationSubring K`): in the
`ValuationSubring` context the elaboration of its call to `IsoOver.apply_section_eq` times out.

## Main results

* `marks_of_local_piece`: the marks over a local model piece;
* `exists_marked_nodal_modification`: the nodal modification with separated marks.

Blueprint: `sm-gluing-existence.tex`, `lem:sm-gluing-existence-marked-nodal`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.StableVal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open Geometry.ModificationCenter (isomorphismOpen center)
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open Curves (IsStrictlySemistable)
open ValCurves (genericPt)

set_option backward.isDefEq.respectTransparency false

section LocalPiece

variable {R : Type u} [CommRing R] [IsDomain R] {N X B : Scheme.{u}}
  (pN : N ⟶ Spec (.of R)) (β : X ⟶ N) (O U : N.Opens) (τ : B ⟶ O)
  [IsSeparated (τ ≫ O.ι ≫ pN)]
  (i : (β ⁻¹ᵁ U).toScheme ≅ (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).toScheme)
  (hi : i.hom ≫ (τ ⁻¹ᵁ (O.ι ⁻¹ᵁ U)).ι ≫ τ ≫ O.ι = (β ⁻¹ᵁ U).ι ≫ β)
  (η : Spec (.of R)) (hη : ∀ t, η ⤳ t)
  (hgen : ∀ w₁ w₂ : B, τ w₁ = τ w₂ → pN (O.ι (τ w₁)) = η → w₁ = w₂)
  {n : ℕ} (σN : Fin n → (Spec (.of R) ⟶ N)) (hσN : ∀ k, σN k ≫ pN = 𝟙 _)
  (σX : Fin n → (Spec (.of R) ⟶ X)) (hσX : ∀ k, σX k ≫ β = σN k)

include hi hη hgen hσN hσX in
/-- **The marks over a local model piece** (lane T45B; Temkin, proof of Proposition 4.5.1,
T:3246–3252): if `X` is isomorphic over `U ⊆ N` to an open of a local model `τ : B → O`, injective
over the generic point `η`, whose lifted sections `sB k` (defined for the sections `k` with
`P k`, which contain those meeting `U`) are smooth and pairwise disjoint, then the lifted sections
`σX k` of `X` are smooth and pairwise distinct at the points over `U`. -/
theorem marks_of_local_piece (P : Fin n → Prop) (hP : ∀ k t, σN k t ∈ U → P k)
    (sB : (k : Fin n) → P k → (Spec (.of R) ⟶ B))
    (hsB : ∀ k hk, sB k hk ≫ τ ≫ O.ι = σN k)
    (hsm : ∀ k hk t, IsSmoothAt (τ ≫ O.ι ≫ pN) (sB k hk t))
    (hdisj : ∀ k hk l hl, k ≠ l → Disjoint (Set.range (sB k hk)) (Set.range (sB l hl)))
    (k : Fin n) (t : Spec (.of R)) (hm : σN k t ∈ U) :
    IsSmoothAt (β ≫ pN) (σX k t) ∧ ∀ l, l ≠ k → σX l t ≠ σX k t := by
  have hβσ : ∀ l, β (σX l t) = σN l t := fun l ↦ by rw [← Scheme.Hom.comp_apply, hσX]
  have hk := hP k t hm
  have hsec := IsoOver.apply_section_eq pN β O U τ i hi η hgen (σN k) (hσN k) (σX k) (hσX k)
    (sB k hk) (hsB k hk) t (hη t) hm
  refine ⟨?_, fun l hl he ↦ ?_⟩
  · have hz : σX k t ∈ β ⁻¹ᵁ U := by
      rw [Scheme.Hom.mem_preimage, hβσ]
      exact hm
    exact IsoOver.isSmoothAt_of_isSmoothAt pN β O U τ i hi ⟨σX k t, hz⟩
      (by rw [hsec]; exact hsm k hk t)
  · have hlm : σN l t ∈ U := by rw [← hβσ, he, hβσ]; exact hm
    have hl' := hP l t hlm
    have hsec' := IsoOver.apply_section_eq pN β O U τ i hi η hgen (σN l) (hσN l) (σX l) (hσX l)
      (sB l hl') (hsB l hl') t (hη t) hlm
    have heq : sB l hl' t = sB k hk t := by
      rw [← hsec, ← hsec']
      congr 2
      exact Subtype.ext he
    exact Set.disjoint_left.mp (hdisj k hk l hl' (Ne.symm hl)) ⟨t, heq.symm⟩ ⟨t, rfl⟩

end LocalPiece

section Assembly

variable {K : Type u} [Field K] {R : ValuationSubring K}

local notation "s₀" => IsLocalRing.closedPoint R

/-- **A nodal modification with separated marks** (Temkin, proof of Proposition 4.5.1,
T:3243–3266, with Lemma 4.3.3 `divlem`; `PLAN-T5.md` §2.2 steps 1–8 with marks, node V2). Let `K`
be algebraically closed, `R ⊆ K` a valuation ring of finite height and equal characteristic, and
`φ : C → Spec R` a proper flat relative curve, integral, separated and quasi-compact, with
`trdeg K(C)/K = 1`, normal at the points over the generic point, and let `σ k` be finitely many
sections of `φ` with pairwise distinct generic points. Then there are a modification
`b : N → C` (the normalized projective refinement, flat and of finite presentation over `R`, and
projective over `R` if `C` is) and a modification `β : X → N` such that `X` is a nodal curve over
`R`, locally projective over `N` (the input of the valuation-level projectivity theorem,
`PLAN-T5.md` node V1), and the lifts `σX k` of the sections are pairwise disjoint and pass
through smooth points of `X → Spec R`.

Input not proved here: `ProjectiveSeparation R` (projective separation of marks on the strictly
semi-stable local models; lane BND's `Blowups.exists_separation_marks` with the projectivity of
the output). -/
theorem exists_marked_nodal_modification [IsAlgClosed K] [Finite (PrimeSpectrum R)]
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField R) p)
    (hsepM : ProjectiveSeparation R)
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
  have hτp : ∀ i, DeJong.IsRelativelyProjective ((ν ⁻¹ᵁ W i).ι ≫ pN) (τ i) := by
    intro i
    have h1 := BlowDown.NoClosedExc.isRelativelyProjective_toNormalization ((W i).ι ≫ p ≫ φ)
      (q i) (hqproj i)
    have h2 : (q i).fromNormalization ≫ (W i).ι ≫ p ≫ φ =
        (ji i).symm.hom ≫ (ν ⁻¹ᵁ W i).ι ≫ ν ≫ p ≫ φ := by
      rw [Iso.symm_hom, ← morphismRestrict_ι_assoc, ← hji i, Category.assoc,
        Iso.inv_hom_id_assoc]
    rw [h2] at h1
    exact isRelativelyProjective_comp_iso _ (ji i).symm h1
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
    exact exists_local_marked_model hN pN hdimN σN hσNsec hinjN hsepM (ν ⁻¹ᵁ W (ix x.1))
      (τ (ix x.1)) (hτss _) (hτp _) (hix x.1) x.2.2
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

end DeJongAlterations.StableModification.Gluing.StableVal
