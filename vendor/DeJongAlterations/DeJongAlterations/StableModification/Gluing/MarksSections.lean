/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45B)
-/
import DeJongAlterations.StableModification.Blowups.SeparationMarks
import DeJongAlterations.StableModification.BlowDown.ClosureComponent
import DeJongAlterations.StableModification.Global.SetupMarks
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Marks as sections over a valuation ring

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.3.3 (`divlem`, T:3025–3033): over a valuation ring `V` whose fraction field is separably
closed, the marks `D_η` of the generic fibre are finitely many rational points, and on a proper
`V`-curve their closures are sections `σₖ : Spec V → X`. This file provides the bookkeeping for
marks given by sections (`PLAN-T5.md` §2.2, node V2, the "pair version" of nodes A6–A8):

* `existsUnique_lift`: the valuative criterion of properness, for a proper `f : Y → X` and a
  section `σ` of `X` together with a lift of its generic point (`ClosureComponent.residuePt ⊥`,
  the generic point of `Spec V` with values in `κ(⊥) = Frac V`);
* `exists_lift_of_isIso`, `lift_unique_of_isIso`: a section of `X` lifts uniquely along a proper
  `f : Y → X` which is an isomorphism over an open containing the generic point of the section;
* `support_iInf_ker'`, `comap_iInf_ker_eq_ker`: the marks `⋂ₖ ker σₖ` of finitely many sections
  with pairwise disjoint images are their union, and near one section they are its ideal;
* `etale_iInf_ker`, `isSemistablePair_iInf_ker`: **pairwise disjoint sections through smooth
  points of a nodal curve are semi-stable marks** (their union is étale over the base, being
  locally isomorphic to the base).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.StableVal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open BlowDown.ClosureComponent (residuePt residuePt_apply)

set_option backward.isDefEq.respectTransparency false

section Lift

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- The generic point of `Spec V` with values in the residue field `κ(⊥) = Frac V`. -/
abbrev genericPt₀ : Spec (.of (⊥ : Ideal V).ResidueField) ⟶ Spec (.of V) :=
  Spec.map (CommRingCat.ofHom (algebraMap V (⊥ : Ideal V).ResidueField))

omit [ValuationRing V] in
theorem genericPt₀_apply (z : Spec (.of (⊥ : Ideal V).ResidueField)) :
    genericPt₀ z = genericPoint (Spec (.of V)) := by
  rw [genericPoint_eq_bot_of_affine]
  exact residuePt_apply (⊥ : PrimeSpectrum V) z

/-- **The valuative criterion of properness for sections.** For a proper `f : Y → X`, a morphism
`σ : Spec V → X` and a lift `P : Spec κ(⊥) → Y` of its generic point, there is a unique lift
`σ' : Spec V → Y` of `σ` through `f` restricting to `P`. -/
theorem existsUnique_lift {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (σ : Spec (.of V) ⟶ X) (P : Spec (.of (⊥ : Ideal V).ResidueField) ⟶ Y)
    (hP : P ≫ f = genericPt₀ ≫ σ) :
    ∃! σ' : Spec (.of V) ⟶ Y, σ' ≫ f = σ ∧ genericPt₀ ≫ σ' = P := by
  have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) f := by
    rw [← IsProper.eq_valuativeCriterion]
    exact (inferInstance : IsProper f)
  have hv : ValuativeCriterion f := h.1.1.1
  let S : ValuativeCommSq f :=
    { R := V
      K := (⊥ : Ideal V).ResidueField
      i₁ := P
      i₂ := σ
      commSq := ⟨hP⟩ }
  obtain ⟨hu⟩ := hv S
  refine ⟨hu.default.l, ⟨hu.default.fac_right, hu.default.fac_left⟩, fun σ' hσ' => ?_⟩
  have := hu.uniq { l := σ', fac_left := hσ'.2, fac_right := hσ'.1 }
  exact congrArg CommSq.LiftStruct.l this

omit [ValuationRing V] in
/-- If the generic point of a section `σ` lies in an open `U`, then `σ` maps the point of
`Spec κ(⊥)` into `U`. -/
theorem range_genericPt₀_comp_subset {X : Scheme.{u}} (σ : Spec (.of V) ⟶ X) (U : X.Opens)
    (hσ : σ (genericPoint (Spec (.of V))) ∈ U) :
    Set.range (genericPt₀ ≫ σ) ⊆ Set.range U.ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, genericPt₀_apply]
  exact hσ

/-- **Lifting sections along a morphism which is an isomorphism near their generic point.** -/
theorem exists_lift_of_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (U : X.Opens)
    [IsIso (f ∣_ U)] (σ : Spec (.of V) ⟶ X) (hσ : σ (genericPoint (Spec (.of V))) ∈ U) :
    ∃ σ' : Spec (.of V) ⟶ Y, σ' ≫ f = σ := by
  let l : Spec (.of (⊥ : Ideal V).ResidueField) ⟶ U :=
    IsOpenImmersion.lift U.ι (genericPt₀ ≫ σ) (range_genericPt₀_comp_subset σ U hσ)
  have hl : l ≫ U.ι = genericPt₀ ≫ σ := IsOpenImmersion.lift_fac _ _ _
  let P := l ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hP : P ≫ f = genericPt₀ ≫ σ := by
    simp only [P, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hl]
  obtain ⟨σ', ⟨h1, -⟩, -⟩ := existsUnique_lift f σ P hP
  exact ⟨σ', h1⟩

/-- **Lifts of sections are unique** along a separated morphism which is an isomorphism over an
open containing the generic point of the section. -/
theorem lift_unique_of_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsSeparated f] (U : X.Opens)
    [IsIso (f ∣_ U)] (σ₁ σ₂ : Spec (.of V) ⟶ Y) (h : σ₁ ≫ f = σ₂ ≫ f)
    (hσ : (σ₁ ≫ f) (genericPoint (Spec (.of V))) ∈ U) : σ₁ = σ₂ := by
  have hσ₂ : (σ₂ ≫ f) (genericPoint (Spec (.of V))) ∈ U := h ▸ hσ
  have hr : ∀ σ' : Spec (.of V) ⟶ Y, (σ' ≫ f) (genericPoint (Spec (.of V))) ∈ U →
      Set.range (genericPt₀ ≫ σ') ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro σ' hσ' _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f ((genericPt₀ ≫ σ') z) ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.comp_apply, genericPt₀_apply]
    exact hσ'
  let l₁ := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (genericPt₀ ≫ σ₁) (hr σ₁ hσ)
  let l₂ := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (genericPt₀ ≫ σ₂) (hr σ₂ hσ₂)
  have hl₁ : l₁ ≫ (f ⁻¹ᵁ U).ι = genericPt₀ ≫ σ₁ := IsOpenImmersion.lift_fac _ _ _
  have hl₂ : l₂ ≫ (f ⁻¹ᵁ U).ι = genericPt₀ ≫ σ₂ := IsOpenImmersion.lift_fac _ _ _
  have hl : l₁ = l₂ := by
    rw [← cancel_mono (f ∣_ U), ← cancel_mono U.ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, hl₁, ← Category.assoc, hl₂, Category.assoc,
      Category.assoc, h]
  have hgen : genericPt₀ ≫ σ₁ = genericPt₀ ≫ σ₂ := by rw [← hl₁, ← hl₂, hl]
  have hv : ValuativeCriterion.Uniqueness f := IsSeparated.valuativeCriterion f
  let S : ValuativeCommSq f :=
    { R := V
      K := (⊥ : Ideal V).ResidueField
      i₁ := genericPt₀ ≫ σ₁
      i₂ := σ₁ ≫ f
      commSq := ⟨by rw [Category.assoc]⟩ }
  have := hv S
  have e := Subsingleton.elim (α := S.commSq.LiftStruct)
    { l := σ₁, fac_left := rfl, fac_right := rfl }
    { l := σ₂, fac_left := hgen.symm, fac_right := h.symm }
  exact congrArg CommSq.LiftStruct.l e

end Lift

section Marks

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {g : X ⟶ Spec (.of A)} [IsSeparated g]
  {ι : Type*} [Finite ι] (σ : ι → (Spec (.of A) ⟶ X)) (hσ : ∀ k, σ k ≫ g = 𝟙 _)

omit [Finite ι] in
include hσ in
/-- The image of a section of a separated morphism is closed. -/
theorem isClosed_range (k : ι) : IsClosed (Set.range (σ k)) :=
  Blowups.isClosed_range_section (σ k) (hσ k)

include hσ in
/-- **The marks of finitely many sections are their union**: the support of `⋂ₖ ker σₖ` is
`⋃ₖ σₖ(Spec A)` (`Blowups.support_iInf_ker` for an arbitrary finite index type). -/
theorem support_iInf_ker' :
    ((⨅ k, (σ k).ker).support : Set X) = ⋃ k, Set.range (σ k) := by
  have hcl : ∀ l, IsClosedImmersion (σ l) := fun l ↦
    DeJong.isClosedImmersion_of_comp_eq_id g _ (hσ l)
  have hZ : IsClosed (⋃ k, Set.range (σ k)) :=
    isClosed_iUnion_of_finite fun k ↦ isClosed_range σ hσ k
  apply le_antisymm
  · intro x hx
    by_contra hxZ
    let W : X.Opens := ⟨_, hZ.isOpen_compl⟩
    have hD : (⨅ k, (σ k).ker).comap W.ι = ⊤ := by
      rw [Blowups.comap_iInf_of_isOpenImmersion]
      refine eq_top_iff.mpr (le_iInf fun k ↦ ?_)
      rw [Blowups.ker_comap_eq_top_of_disjoint (σ k) W.ι fun y hy ↦
        y.2 (Set.mem_iUnion.mpr ⟨k, hy⟩)]
    have : (⟨x, hxZ⟩ : W.toScheme) ∈ (((⨅ k, (σ k).ker).comap W.ι).support : Set W.toScheme) := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hx
    rw [hD, Scheme.IdealSheafData.support_top] at this
    exact this
  · refine Set.iUnion_subset fun k ↦ ?_
    have h1 : ((σ k).ker.support : Set X) ⊆ ((⨅ k, (σ k).ker).support : Set X) :=
      Scheme.IdealSheafData.support_antitone (iInf_le _ k)
    rw [Scheme.Hom.support_ker, (σ k).isClosedEmbedding.isClosed_range.closure_eq] at h1
    exact h1

include hσ in
/-- The union of the images of all sections but `σ k` is closed. -/
theorem isClosed_iUnion_ne (k : ι) : IsClosed (⋃ l ∈ {l | l ≠ k}, Set.range (σ l)) :=
  Set.Finite.isClosed_biUnion (Set.toFinite _) fun l _ ↦ isClosed_range σ hσ l

/-- The open complement of the images of all sections but `σ k`. -/
def awayOpen (k : ι) : X.Opens :=
  ⟨(⋃ l ∈ {l | l ≠ k}, Set.range (σ l))ᶜ, (isClosed_iUnion_ne σ hσ k).isOpen_compl⟩

theorem mem_awayOpen_iff (k : ι) (x : X) :
    x ∈ awayOpen σ hσ k ↔ ∀ l, l ≠ k → x ∉ Set.range (σ l) := by
  change x ∈ (⋃ l ∈ {l | l ≠ k}, Set.range (σ l))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, exists_prop]
  constructor
  · intro h l hl hx
    exact h l ⟨hl, hx⟩
  · rintro h l ⟨hl, hx⟩
    exact h l hl hx

variable (hdisj : ∀ k l, k ≠ l → Disjoint (Set.range (σ k)) (Set.range (σ l)))

include hdisj in
theorem range_subset_awayOpen (k : ι) : Set.range (σ k) ⊆ awayOpen σ hσ k := by
  intro x hx
  rw [SetLike.mem_coe, mem_awayOpen_iff]
  intro l hl hxl
  exact Set.disjoint_left.mp (hdisj k l hl.symm) hx hxl

/-- The section `σ k` as a section of the open `awayOpen σ hσ k`. -/
def awaySection (k : ι) : Spec (.of A) ⟶ awayOpen σ hσ k :=
  IsOpenImmersion.lift (awayOpen σ hσ k).ι (σ k) (by
    rw [Scheme.Opens.range_ι]
    exact range_subset_awayOpen σ hσ hdisj k)

@[reassoc (attr := simp)]
theorem awaySection_ι (k : ι) : awaySection σ hσ hdisj k ≫ (awayOpen σ hσ k).ι = σ k :=
  IsOpenImmersion.lift_fac _ _ _

include hdisj in
/-- **Near one section the marks are its ideal.** -/
theorem comap_iInf_ker_eq_ker (k : ι) :
    (⨅ l, (σ l).ker).comap (awayOpen σ hσ k).ι = (awaySection σ hσ hdisj k).ker := by
  have hcl : ∀ l, IsClosedImmersion (σ l) := fun l ↦
    DeJong.isClosedImmersion_of_comp_eq_id g _ (hσ l)
  rw [Blowups.comap_iInf_of_isOpenImmersion]
  apply le_antisymm
  · rw [← Blowups.ker_comap_of_comp (σ k) (awayOpen σ hσ k).ι (awaySection σ hσ hdisj k)
      (awaySection_ι σ hσ hdisj k)]
    exact iInf_le _ k
  · refine le_iInf fun l ↦ ?_
    by_cases hl : l = k
    · subst hl
      rw [Blowups.ker_comap_of_comp (σ l) (awayOpen σ hσ l).ι (awaySection σ hσ hdisj l)
        (awaySection_ι σ hσ hdisj l)]
    · rw [Blowups.ker_comap_eq_top_of_disjoint (σ l) (awayOpen σ hσ k).ι fun y hy ↦
        (mem_awayOpen_iff σ hσ k y.1).mp y.2 l hl hy]
      exact le_top

include hσ hdisj in
/-- **Pairwise disjoint sections are étale marks**: the union of the images of finitely many
pairwise disjoint sections of a separated `g : X → Spec A`, with its reduced structure
`⋂ₖ ker σₖ`, is étale over `Spec A` (it is locally isomorphic to `Spec A`). -/
theorem etale_iInf_ker : Etale ((⨅ k, (σ k).ker).subschemeι ≫ g) := by
  set D := ⨅ k, (σ k).ker
  refine Curves.etale_of_cover _ fun d ↦ ?_
  have hd : D.subschemeι d ∈ (D.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨d, rfl⟩
  rw [support_iInf_ker' σ hσ] at hd
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hd
  set U := awayOpen σ hσ k
  have hdU : D.subschemeι d ∈ U := range_subset_awayOpen σ hσ hdisj k hk
  refine ⟨_, (D.comapIso U.ι).hom ≫ pullback.snd U.ι D.subschemeι, inferInstance, ?_, ?_⟩
  · have hd' : d ∈ Set.range (pullback.snd U.ι D.subschemeι) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      change D.subschemeι d ∈ Set.range U.ι
      rw [Scheme.Opens.range_ι]
      exact hdU
    obtain ⟨w, rfl⟩ := hd'
    exact ⟨(D.comapIso U.ι).inv w, by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩
  · have e1 : ((D.comapIso U.ι).hom ≫ pullback.snd U.ι D.subschemeι) ≫ D.subschemeι ≫ g =
        (D.comap U.ι).subschemeι ≫ U.ι ≫ g := by
      rw [Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
        Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    rw [e1, comap_iInf_ker_eq_ker σ hσ hdisj k]
    set s := awaySection σ hσ hdisj k
    have hcl : IsClosedImmersion (σ k) := DeJong.isClosedImmersion_of_comp_eq_id g _ (hσ k)
    have : IsClosedImmersion s := by
      have : IsClosedImmersion (s ≫ U.ι) := by rw [awaySection_ι]; infer_instance
      exact IsClosedImmersion.of_comp s U.ι
    have e2 : s.ker.subschemeι ≫ U.ι ≫ g = inv s.toImage := by
      refine IsIso.eq_inv_of_hom_inv_id ?_
      rw [← Category.assoc, ← Category.assoc]
      change (s.toImage ≫ s.imageι) ≫ U.ι ≫ g = _
      rw [Scheme.Hom.toImage_imageι, ← Category.assoc, awaySection_ι, hσ k]
    rw [e2]
    infer_instance

include hσ hdisj in
/-- **Pairwise disjoint sections through smooth points of a nodal curve form semi-stable
marks.** -/
theorem isSemistablePair_iInf_ker [IsNodalCurve g]
    (hsm : ∀ k t, IsSmoothAt g (σ k t)) : IsSemistablePair g (⨅ k, (σ k).ker) where
  nodal := inferInstance
  etale := etale_iInf_ker σ hσ hdisj
  smoothAlong x hx := by
    rw [support_iInf_ker' σ hσ] at hx
    obtain ⟨k, t, rfl⟩ := Set.mem_iUnion.mp hx
    exact hsm k t

end Marks

end DeJongAlterations.StableModification.Gluing.StableVal
