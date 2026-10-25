/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45D)
-/
import DeJongAlterations.StableModification.Gluing.SeparationProjective
import DeJongAlterations.StableModification.Gluing.MarksLocal

/-!
# Projective separation of marks over a valuation ring, and the local marked models

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Lemma 4.3.2
(`divlem`, T:3019–3046) with the projectivity of the output, and its use in the proof of
Proposition 4.5.1 (`sepclosprop`, T:3246–3252). This file connects the projective separation
`SeparationProjective.exists_separation_marks_projective` with lane T45B's interface
`Gluing.StableVal.ProjectiveSeparation` (`Gluing/MarksLocal.lean`).

`ProjectiveSeparation R` asks for `β : B' → B` **projective relative to `B → Spec R`** for an
*arbitrary* separated strictly semi-stable `B`, that is, a closed immersion
`B' → ℙⁿ_B` over `B`. What the separation induction provides (as lane T45C's cofinality) is that
`β` is a composite of blow-ups of ideal sheaves of finite type with finite cosupport in affine
opens, and that it **preserves projectivity** (`CofinalProjective.PreservesProjective`): `B'` is
projective over every ring over which `B` is projective and of finite presentation. For a general
(not quasi-projective) `B` the blow-up of a point need not admit a closed immersion into `ℙⁿ_B`
(it requires a line bundle on `B` whose twist of the ideal sheaf is globally generated), so we do
not prove `ProjectiveSeparation R` for arbitrary `B`; we prove

* `ProjectiveSeparationPreserving R` (`projectiveSeparationPreserving`): the statement of
  `ProjectiveSeparation R` with `IsRelativelyProjective g β` replaced by `PreservesProjective β`;
* `projectiveSeparation_of_isProjectiveOver`: the conclusion of `ProjectiveSeparation R` exactly,
  for `B` projective over `R`;
* `exists_local_marked_model_of_isProjectiveOver`: lane T45B's `exists_local_marked_model`
  **without the hypothesis `ProjectiveSeparation R`**, for a strictly semi-stable model
  `τ : B → O` such that `B` is projective over a ring `E` through a separated `O → Spec E` (the
  situation of its consumer: lane T45C's models `B` are projective over the rings `E` of the affine
  pieces of the refinement, and `ν⁻¹(W) → W → Spec E` is separated). Instead of separating the
  marks on `τ⁻¹(O ∩ throughOpen x)` (not projective over an affine scheme), we separate them on
  `B` and restrict afterwards.

All three hold over a valuation ring `R` of a separably closed field `K` (henselian with separably
closed residue field, `Valuation.instHenselianLocalRingValuationSubring`,
`Valuation.instIsSepClosedResidueField`); the first two need no finiteness of the height, the local
models use it (as lane T45B's) to lift the sections to the model (`exists_lift_section`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.StableVal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open Geometry.ModificationCenter (isomorphismOpen center)
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open Curves (IsStrictlySemistable)
open CofinalProjective (PreservesProjective)

set_option backward.isDefEq.respectTransparency false

section Statement

variable {K : Type u} [Field K] (R : ValuationSubring K)

/-- **Projective separation of marks, projectivity-preserving form** (`PLAN-T5.md` §2.2 step 4,
node A4; Temkin, Lemma 4.3.2, T:3019–3044, with projectivity tracked). The statement of
`ProjectiveSeparation R` with the relative projectivity of `β` replaced by: `β` preserves
projectivity (`B'` is projective over every ring over which `B` is projective and of finite
presentation). -/
def ProjectiveSeparationPreserving : Prop :=
  ∀ (B : Scheme.{u}) (g : B ⟶ Spec (.of R)) [IsSeparated g] [IsIntegral B],
    IsStrictlySemistable g ⊤ → ∀ (n : ℕ) (σ : Fin n → (Spec (.of R) ⟶ B)),
      (∀ k, σ k ≫ g = 𝟙 _) → Function.Injective σ →
      ∃ (B' : Scheme.{u}) (β : B' ⟶ B) (σ' : Fin n → (Spec (.of R) ⟶ B')),
        IsModification β ∧ PreservesProjective β ∧ (∀ k, σ' k ≫ β = σ k) ∧
        (∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l))) ∧
        IsSemistablePair (β ≫ g) (⨅ k, (σ' k).ker)

variable [IsSepClosed K]

/-- **`ProjectiveSeparationPreserving R` holds** for every valuation ring `R` of a separably closed
field (`SeparationProjective.exists_separation_marks_projective`). -/
theorem projectiveSeparationPreserving : ProjectiveSeparationPreserving R := by
  intro B g _ _ hss n σ hσ hinj
  obtain ⟨B', β, σ', hβ, hβp, -, hσ', hdisj, -, -, hpair⟩ :=
    SeparationProjective.exists_separation_marks_projective g hss σ hσ hinj
  exact ⟨B', β, σ', hβ, hβp, hσ', hdisj, hpair⟩

/-- **The conclusion of `ProjectiveSeparation R` for `B` projective over `R`**: for an integral
strictly semi-stable `B` projective over a valuation ring `R` of a separably closed field and
pairwise distinct sections, there is a modification `β : B' → B`, projective relative to
`B → Spec R`, with disjoint lifted sections and `(B', ⋃ₖ σ'ₖ)` a semi-stable pair. -/
theorem projectiveSeparation_of_isProjectiveOver (B : Scheme.{u}) (g : B ⟶ Spec (.of R))
    [IsSeparated g] [IsIntegral B] (hgp : IsProjectiveOver g) (hss : IsStrictlySemistable g ⊤)
    (n : ℕ) (σ : Fin n → (Spec (.of R) ⟶ B)) (hσ : ∀ k, σ k ≫ g = 𝟙 _)
    (hinj : Function.Injective σ) :
    ∃ (B' : Scheme.{u}) (β : B' ⟶ B) (σ' : Fin n → (Spec (.of R) ⟶ B')),
      IsModification β ∧ DeJong.IsRelativelyProjective g β ∧ (∀ k, σ' k ≫ β = σ k) ∧
      (∀ k l, k ≠ l → Disjoint (Set.range (σ' k)) (Set.range (σ' l))) ∧
      IsSemistablePair (β ≫ g) (⨅ k, (σ' k).ker) := by
  obtain ⟨B', β, σ', hβ, hβp, hσ', hdisj, hpair⟩ :=
    projectiveSeparationPreserving R B g hss n σ hσ hinj
  have : IsNodalCurve g := hss.isNodalCurve
  exact ⟨B', β, σ', hβ, SeparationProjective.PreservesProjective.isRelativelyProjective hβp g hgp,
    hσ', hdisj, hpair⟩

end Statement

section Projective

/-- **Projectivity relative to an affine base is projectivity over its ring**: a morphism
`f : X → Spec E` projective relative to some `ψ : Spec E → Spec R` is projective over `E` (the
converse of lane T45C's `CofinalProjective.isRelativelyProjective_of_isProjectiveOver_spec`). -/
theorem isProjectiveOver_of_isRelativelyProjective_spec {R E : Type u} [CommRing R] [CommRing E]
    (ψ : Spec (.of E) ⟶ Spec (.of R)) {X : Scheme.{u}} (f : X ⟶ Spec (.of E))
    (h : DeJong.IsRelativelyProjective ψ f) : IsProjectiveOver f := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R →+* E, ψ = Spec.map (CommRingCat.ofHom ρ) :=
    ⟨(Spec.preimage ψ).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have h' : DeJong.IsRelativelyProjective
      (𝟙 (Spec (.of E)) ≫ Spec.map (CommRingCat.ofHom ρ)) f := by
    rwa [Category.id_comp]
  exact (DeJong.isRelativelyProjective_id_iff f).mp
    ((Projectivity.isRelativelyProjective_comp_specMap_iff ρ (𝟙 _) f).mp h')

end Projective

section LocalModel

variable {K : Type u} [Field K] [IsSepClosed K] {R : ValuationSubring K}
  [Finite (PrimeSpectrum R)] {N : Scheme.{u}} [IsIntegral N] (hN : IsNormalScheme N)
  (pN : N ⟶ Spec (.of R)) [IsProper pN]
  [Flat pN] [LocallyOfFinitePresentation pN] (hdim : fiberTrdeg pN (genericPoint N) ≤ 1)
  {n : ℕ} (σN : Fin n → (Spec (.of R) ⟶ N)) (hσN : ∀ k, σN k ≫ pN = 𝟙 _)
  (hinj : Function.Injective fun k ↦ σN k (genericPoint (Spec (.of R))))

local notation "s₀" => IsLocalRing.closedPoint R

include hN hdim hinj in
/-- **A local semi-stable model with separated marks, unconditionally** (Temkin, proof of
Proposition 4.5.1, T:3246–3252, with Lemma 4.3.2; `PLAN-T5.md` §2.2 steps 6–8 with marks): lane
T45B's `exists_local_marked_model` without the hypothesis `ProjectiveSeparation R`, for `K`
separably closed and a strictly semi-stable model `τ : B → O` of an open `O ⊆ N` such that `B` is
projective over a ring `E` through a separated `pE : O → Spec E` over `Spec R` (`B` projective over
`E` replaces "`τ` projective relative to `O → Spec R`"). Over `O_x = O ∩ throughOpen x` there is a
modification `τ_x : B_x → O_x`, projective over `O_x`, nodal over `R`, whose isomorphism locus lies
in the good locus, with lifts of the sections through `x` which are pairwise disjoint and pass
through smooth points of `B_x`. The marks are separated on `B` itself
(`SeparationProjective.exists_separation_marks_projective`, so the result is projective over
`E`), and the model is the restriction over `O_x`. -/
theorem exists_local_marked_model_of_isProjectiveOver (O : N.Opens) {B : Scheme.{u}}
    (τ : B ⟶ O) [IsModification τ] (hss : IsStrictlySemistable (τ ≫ O.ι ≫ pN) ⊤)
    {E : Type u} [CommRing E] (pE : O.toScheme ⟶ Spec (.of E)) [IsSeparated pE]
    (q : Spec (.of E) ⟶ Spec (.of R)) [LocallyOfFiniteType q] (hq : pE ≫ q = O.ι ≫ pN)
    (hBE : IsProjectiveOver (τ ≫ pE)) {x : N} (hxO : x ∈ O) (hx : IsClosed ({x} : Set N)) :
    ∃ (Bx : Scheme.{u}) (τx : Bx ⟶ (O ⊓ throughOpen pN σN hσN x : N.Opens)),
      IsModification τx ∧
      DeJong.IsRelativelyProjective ((O ⊓ throughOpen pN σN hσN x).ι ≫ pN) τx ∧
      IsNodalCurve (τx ≫ (O ⊓ throughOpen pN σN hσN x).ι ≫ pN) ∧
      (O ⊓ throughOpen pN σN hσN x).ι ''ᵁ isomorphismOpen τx ≤ goodOpen pN σN hσN ∧
      ∃ σx : (k : Fin n) → σN k s₀ = x → (Spec (.of R) ⟶ Bx),
        (∀ k hk, σx k hk ≫ τx ≫ (O ⊓ throughOpen pN σN hσN x).ι = σN k) ∧
        (∀ k hk t, IsSmoothAt (τx ≫ (O ⊓ throughOpen pN σN hσN x).ι ≫ pN) (σx k hk t)) ∧
        (∀ k hk l hl, k ≠ l → Disjoint (Set.range (σx k hk)) (Set.range (σx l hl))) := by
  classical
  set Ox := O ⊓ throughOpen pN σN hσN x with hOx
  have hxOx : x ∈ Ox := ⟨hxO, mem_throughOpen_self pN σN hσN hx⟩
  have : Nonempty Ox := ⟨⟨x, hxOx⟩⟩
  have : IsIntegral Ox.toScheme := isIntegral_of_isOpenImmersion Ox.ι
  have : Nonempty O := ⟨⟨x, hxO⟩⟩
  have : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have hτm : IsModification τ := inferInstance
  have : IsIntegral B := hτm.sourceIntegral
  -- the sections through `x`, in `O`, and their lifts to `B`
  let Kx := {k : Fin n // σN k s₀ = x}
  let e : Fin (Fintype.card Kx) ≃ Kx := (Fintype.equivFin Kx).symm
  have hsub : ∀ k : Kx, Set.range (σN k.1) ⊆ Set.range Ox.ι := fun k ↦ by
    rw [Scheme.Opens.range_ι]
    intro y hy
    exact ⟨Blowups.range_subset_of_closedPoint_mem (σN k.1) O (by rw [k.2]; exact hxO) hy,
      range_subset_throughOpen pN σN hσN k.2 hy⟩
  have hsubO : ∀ k : Kx, Set.range (σN k.1) ⊆ Set.range O.ι := fun k ↦ by
    rw [Scheme.Opens.range_ι]
    exact Blowups.range_subset_of_closedPoint_mem (σN k.1) O (by rw [k.2]; exact hxO)
  let sO : Kx → (Spec (.of R) ⟶ O) := fun k ↦ IsOpenImmersion.lift O.ι (σN k.1) (hsubO k)
  have hsO : ∀ k, sO k ≫ O.ι = σN k.1 := fun k ↦ IsOpenImmersion.lift_fac _ _ _
  have hnormO : ∀ y : O, (O.ι ≫ pN) y = genericPoint (Spec (.of R)) →
      IsIntegrallyClosed (O.toScheme.presheaf.stalk y) := fun y _ ↦
    isIntegrallyClosed_stalk_opens hN O y
  have hdimO : fiberTrdeg (O.ι ≫ pN) (genericPoint O.toScheme) ≤ 1 := by
    rw [fiberTrdeg_genericPoint_opens]
    exact hdim
  have hlift : ∀ k : Kx, ∃ s : Spec (.of R) ⟶ B, s ≫ τ = sO k := fun k ↦
    exists_lift_section (O.ι ≫ pN) hnormO hdimO τ (sO k) (by rw [← Category.assoc, hsO, hσN])
  choose σB hσB using hlift
  have hσBN : ∀ k, σB k ≫ τ ≫ O.ι = σN k.1 := fun k ↦ by
    rw [← Category.assoc, hσB, hsO]
  set g₀ := τ ≫ O.ι ≫ pN with hg₀def
  have hσBsec : ∀ i, σB (e i) ≫ g₀ = 𝟙 _ := fun i ↦ by
    rw [hg₀def, ← Category.assoc τ, ← Category.assoc, hσBN, hσN]
  have hσBinj : Function.Injective fun i ↦ σB (e i) := by
    intro i j hij
    have h1 : σN (e i).1 = σN (e j).1 := by
      rw [← hσBN, ← hσBN]
      exact congrArg (· ≫ τ ≫ O.ι) hij
    have h2 := hinj (congrArg (fun f : Spec (.of R) ⟶ N ↦ f (genericPoint (Spec (.of R)))) h1)
    exact e.injective (Subtype.ext h2)
  have : IsSeparated g₀ := by rw [hg₀def]; infer_instance
  -- the separation of the marks on `B`, with projectivity
  obtain ⟨B', β, σ', hβ, hβp, -, hσ', hdisj, -, -, hpair⟩ :=
    SeparationProjective.exists_separation_marks_projective g₀ hss (fun i ↦ σB (e i)) hσBsec
      hσBinj
  -- the composite `ρ = β ≫ τ` is projective over `O`
  set ρ := β ≫ τ with hρ
  have hρm : IsModification ρ := IsModification.comp _ _
  have hlfp : LocallyOfFinitePresentation (τ ≫ pE) := by
    have : IsNodalCurve g₀ := hss.isNodalCurve
    have : LocallyOfFinitePresentation ((τ ≫ pE) ≫ q) := by
      rw [Category.assoc, hq]
      exact (inferInstance : LocallyOfFinitePresentation g₀)
    exact SeparationProjective.locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
      (τ ≫ pE) q
  have hρE : IsProjectiveOver (ρ ≫ pE) := by
    rw [hρ, Category.assoc]
    exact hβp (τ ≫ pE) hBE hlfp
  have hρp : DeJong.IsRelativelyProjective (O.ι ≫ pN) ρ := by
    have h1 := Projectivity.isRelativelyProjective_of_isProjectiveOver pE ρ hρE
    obtain ⟨φq, hφq⟩ : ∃ φq : R →+* E, q = Spec.map (CommRingCat.ofHom φq) :=
      ⟨(Spec.preimage q).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    rw [← hq, hφq]
    exact (Projectivity.isRelativelyProjective_comp_specMap_iff φq pE ρ).mpr h1
  -- the restriction over `Ox`
  let V : O.toScheme.Opens := O.ι ⁻¹ᵁ Ox
  let eV : V.toScheme ≅ Ox.toScheme :=
    IsOpenImmersion.isoOfRangeEq ((O.ι ⁻¹ᵁ Ox).ι ≫ O.ι) Ox.ι (range_ι_preimage_ι inf_le_left)
  have heV : eV.hom ≫ Ox.ι = V.ι ≫ O.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have : Nonempty V := ⟨⟨⟨x, hxO⟩, hxOx⟩⟩
  have hρV := Geometry.CurveCompactification.isModification_morphismRestrict ρ V
  have := isModification_of_isIso eV.hom
  let τx : (ρ ⁻¹ᵁ V).toScheme ⟶ Ox := (ρ ∣_ V) ≫ eV.hom
  have hτx : IsModification τx := IsModification.comp _ _
  have hτxι : τx ≫ Ox.ι = (ρ ⁻¹ᵁ V).ι ≫ ρ ≫ O.ι := by
    simp only [τx, Category.assoc, heV]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hτxg : τx ≫ Ox.ι ≫ pN = (ρ ⁻¹ᵁ V).ι ≫ β ≫ g₀ := by
    rw [← Category.assoc, hτxι, hρ, hg₀def]
    simp only [Category.assoc]
  have hnod : IsNodalCurve (τx ≫ Ox.ι ≫ pN) := by
    rw [hτxg]
    have : IsNodalCurve (β ≫ g₀) := hpair.nodal
    exact Curves.IsNodalCurve.etale_comp _ _
  -- the lifted sections in `ρ⁻¹(V)`
  have hσ'N : ∀ i, σ' i ≫ ρ ≫ O.ι = σN (e i).1 := fun i ↦ by
    rw [hρ, Category.assoc, ← Category.assoc (σ' i), hσ', hσBN]
  have hσ'sec : ∀ i, σ' i ≫ β ≫ g₀ = 𝟙 _ := fun i ↦ by
    rw [← Category.assoc, hσ', hσBsec]
  have hrange : ∀ i, Set.range (σ' i) ⊆ Set.range (ρ ⁻¹ᵁ V).ι := by
    rintro i _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h1 : O.ι (ρ (σ' i t)) = σN (e i).1 t := by
      rw [← hσ'N i]
      rfl
    have h2 : σN (e i).1 t ∈ Ox := by
      have := hsub (e i) ⟨t, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    change O.ι (ρ (σ' i t)) ∈ Ox
    rw [h1]
    exact h2
  let σx' : Fin (Fintype.card Kx) → (Spec (.of R) ⟶ (ρ ⁻¹ᵁ V).toScheme) := fun i ↦
    IsOpenImmersion.lift (ρ ⁻¹ᵁ V).ι (σ' i) (hrange i)
  have hσx' : ∀ i, σx' i ≫ (ρ ⁻¹ᵁ V).ι = σ' i := fun i ↦ IsOpenImmersion.lift_fac _ _ _
  have hσ'N' : ∀ i, σx' i ≫ τx ≫ Ox.ι = σN (e i).1 := fun i ↦ by
    rw [hτxι, ← Category.assoc, hσx', hσ'N]
  have hsm : ∀ i t, IsSmoothAt (τx ≫ Ox.ι ≫ pN) (σx' i t) := by
    intro i t
    have hmem : σ' i t ∈ ((⨅ k, (σ' k).ker).support : Set B') := by
      rw [support_iInf_ker' σ' hσ'sec]
      exact Set.mem_iUnion.mpr ⟨i, t, rfl⟩
    have h := hpair.smoothAlong _ hmem
    rw [hτxg]
    refine Curves.isSmoothAt_comp (Curves.isSmoothAt_of_smooth _ _) ?_
    rw [← Scheme.Hom.comp_apply, hσx']
    exact h
  have hdisjx : ∀ i j, i ≠ j → Disjoint (Set.range (σx' i)) (Set.range (σx' j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    have h1 : (ρ ⁻¹ᵁ V).ι (σx' i t) ∈ Set.range (σ' i) :=
      ⟨t, by rw [← hσx' i, Scheme.Hom.comp_apply]⟩
    have h2 : (ρ ⁻¹ᵁ V).ι (σx' i t) ∈ Set.range (σ' j) :=
      ⟨t', by rw [← hσx' j, Scheme.Hom.comp_apply, ht']⟩
    exact Set.disjoint_left.mp (hdisj i j hij) h1 h2
  refine ⟨(ρ ⁻¹ᵁ V).toScheme, τx, hτx, ?_, hnod, ?_, fun k hk ↦ σx' (e.symm ⟨k, hk⟩),
    fun k hk ↦ ?_, fun k hk t ↦ hsm _ t, fun k hk l hl hkl ↦ hdisjx _ _ fun h ↦ hkl ?_⟩
  · -- projectivity
    have h1 := Projectivity.isRelativelyProjective_restrict hρp V
    have h2 : V.ι ≫ O.ι ≫ pN = eV.hom ≫ Ox.ι ≫ pN := by
      rw [← Category.assoc eV.hom, heV, Category.assoc]
    rw [h2] at h1
    exact isRelativelyProjective_comp_iso (Ox.ι ≫ pN) eV h1
  · -- the isomorphism locus is good
    rintro _ ⟨y', hy', rfl⟩
    rw [mem_goodOpen_iff]
    refine ⟨image_isomorphismOpen_le_nodalLocus pN Ox τx hnod ⟨y', hy', rfl⟩, ?_⟩
    rw [not_mem_markBad_iff]
    have hiso : IsIso (τx ∣_ isomorphismOpen τx) :=
      (Geometry.ModificationCenter.le_isomorphismOpen_iff _ _).mp le_rfl
    -- points of `B_x` over `y'` coincide
    have huniq : ∀ w₁ w₂ : (ρ ⁻¹ᵁ V).toScheme, τx w₁ = y' → τx w₂ = y' → w₁ = w₂ := by
      intro w₁ w₂ h₁ h₂
      have hm₁ : w₁ ∈ τx ⁻¹ᵁ isomorphismOpen τx := by
        rw [Scheme.Hom.mem_preimage, h₁]
        exact hy'
      have hm₂ : w₂ ∈ τx ⁻¹ᵁ isomorphismOpen τx := by
        rw [Scheme.Hom.mem_preimage, h₂]
        exact hy'
      have hinj' := (τx ∣_ isomorphismOpen τx).isOpenEmbedding.injective
      have : (τx ∣_ isomorphismOpen τx) ⟨w₁, hm₁⟩ = (τx ∣_ isomorphismOpen τx) ⟨w₂, hm₂⟩ := by
        apply Subtype.ext
        change (τx ∣_ _ ≫ (isomorphismOpen τx).ι) ⟨w₁, hm₁⟩ =
          (τx ∣_ _ ≫ (isomorphismOpen τx).ι) ⟨w₂, hm₂⟩
        rw [morphismRestrict_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact h₁.trans h₂.symm
      exact congrArg Subtype.val (hinj' this)
    have hpt : ∀ i t, σN (e i).1 t = Ox.ι y' → τx (σx' i t) = y' := by
      intro i t ht
      apply Ox.ι.isOpenEmbedding.injective
      rw [← ht, ← hσ'N' i]
      rfl
    intro k t hkt
    have hk : σN k s₀ = x := (mem_throughOpen_iff pN σN hσN x _).mp y'.2.2 k ⟨t, hkt⟩
    have hkt' : σN (e (e.symm ⟨k, hk⟩)).1 t = Ox.ι y' := by
      rw [Equiv.apply_symm_apply]
      exact hkt
    have hw := hpt _ t hkt'
    refine ⟨?_, fun l hl hyl ↦ ?_⟩
    · have h := isSmoothAt_of_isIso_restrict τx (Ox.ι ≫ pN) _
        (by rw [hw]; exact hy') (hsm (e.symm ⟨k, hk⟩) t)
      rw [hw] at h
      exact Curves.isSmoothAt_of_isOpenImmersion_comp Ox.ι h
    · obtain ⟨t', ht'⟩ := hyl
      have htt : t' = t := by
        have h1 := congrArg pN (ht'.trans hkt.symm)
        rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσN, hσN] at h1
      subst htt
      have hl' : σN l s₀ = x := (mem_throughOpen_iff pN σN hσN x _).mp y'.2.2 l ⟨t', ht'⟩
      have hlt' : σN (e (e.symm ⟨l, hl'⟩)).1 t' = Ox.ι y' := by
        rw [Equiv.apply_symm_apply]
        exact ht'
      have hw' := hpt _ t' hlt'
      have heq := huniq _ _ hw hw'
      have hne : e.symm ⟨k, hk⟩ ≠ e.symm ⟨l, hl'⟩ := fun h ↦ hl (by
        have := congrArg Subtype.val (e.symm.injective h)
        exact this.symm)
      exact Set.disjoint_left.mp (hdisjx _ _ hne) ⟨t', rfl⟩ ⟨t', heq.symm⟩
  · -- the lifts
    have h := hσ'N' (e.symm ⟨k, hk⟩)
    rw [Equiv.apply_symm_apply] at h
    exact h
  · have := congrArg Subtype.val (e.symm.injective h)
    exact this

include hN hdim hinj in
/-- **The local marked model over a piece of a refinement** (the form consumed by the gluing of
Temkin's Proposition 4.5.1, lane T45B's `exists_marked_nodal_modification`):
`exists_local_marked_model_of_isProjectiveOver` for `O = ν⁻¹(W)`, where `ν : N → C'` is separated,
`pN = ν ≫ pC`, `W ⊆ C'` is an open with a separated `h : W → Spec E` over `Spec R` through
`ψ : Spec E → Spec R` locally of finite type, and the model `τ : B → ν⁻¹(W)` is such that
`f = τ ≫ ν|_W ≫ h : B → Spec E` is projective relative to `ψ` (lane T45C's
`CofinalProjective.projectiveCofinality`). -/
theorem exists_local_marked_model_of_piece {C' : Scheme.{u}} (ν : N ⟶ C') [IsSeparated ν]
    (pC : C' ⟶ Spec (.of R)) (hpN : pN = ν ≫ pC) (W : C'.Opens) {E : Type u} [CommRing E]
    (h : W.toScheme ⟶ Spec (.of E)) [IsSeparated h] (ψ : Spec (.of E) ⟶ Spec (.of R))
    [LocallyOfFiniteType ψ] (hψ : h ≫ ψ = W.ι ≫ pC) {B : Scheme.{u}}
    (τ : B ⟶ (ν ⁻¹ᵁ W).toScheme) [IsModification τ]
    (hss : IsStrictlySemistable (τ ≫ (ν ⁻¹ᵁ W).ι ≫ pN) ⊤) (f : B ⟶ Spec (.of E))
    (hf : DeJong.IsRelativelyProjective ψ f) (hτf : τ ≫ (ν ∣_ W) ≫ h = f) {x : N}
    (hxO : x ∈ ν ⁻¹ᵁ W) (hx : IsClosed ({x} : Set N)) :
    ∃ (Bx : Scheme.{u}) (τx : Bx ⟶ (ν ⁻¹ᵁ W ⊓ throughOpen pN σN hσN x : N.Opens)),
      IsModification τx ∧
      DeJong.IsRelativelyProjective ((ν ⁻¹ᵁ W ⊓ throughOpen pN σN hσN x).ι ≫ pN) τx ∧
      IsNodalCurve (τx ≫ (ν ⁻¹ᵁ W ⊓ throughOpen pN σN hσN x).ι ≫ pN) ∧
      (ν ⁻¹ᵁ W ⊓ throughOpen pN σN hσN x).ι ''ᵁ isomorphismOpen τx ≤ goodOpen pN σN hσN ∧
      ∃ σx : (k : Fin n) → σN k s₀ = x → (Spec (.of R) ⟶ Bx),
        (∀ k hk, σx k hk ≫ τx ≫ (ν ⁻¹ᵁ W ⊓ throughOpen pN σN hσN x).ι = σN k) ∧
        (∀ k hk t, IsSmoothAt (τx ≫ (ν ⁻¹ᵁ W ⊓ throughOpen pN σN hσN x).ι ≫ pN) (σx k hk t)) ∧
        (∀ k hk l hl, k ≠ l → Disjoint (Set.range (σx k hk)) (Set.range (σx l hl))) := by
  have hq : ((ν ∣_ W) ≫ h) ≫ ψ = (ν ⁻¹ᵁ W).ι ≫ pN := by
    rw [Category.assoc, hψ, ← Category.assoc, morphismRestrict_ι, Category.assoc, hpN]
  have hBE : IsProjectiveOver (τ ≫ (ν ∣_ W) ≫ h) := by
    rw [hτf]
    exact isProjectiveOver_of_isRelativelyProjective_spec ψ f hf
  exact exists_local_marked_model_of_isProjectiveOver hN pN hdim σN hσN hinj (ν ⁻¹ᵁ W) τ hss
    ((ν ∣_ W) ≫ h) ψ hq hBE hxO hx

end LocalModel

end DeJongAlterations.StableModification.Gluing.StableVal
