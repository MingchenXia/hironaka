/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.StableComb
import DeJongAlterations.StableModification.BlowDown.DominationStable
import DeJongAlterations.StableModification.BlowDown.ContractingMap
import DeJongAlterations.StableModification.CurvesField.AmpleSection
import DeJongAlterations.StableModification.Omega.BaseChangeFibre

/-!
# A hyperplane section of the closed fibre (Temkin, Prop. 4.4.6, T:3203–3209)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6: "choose smooth points `pᵢ ∈ Zᵢ` of the other components `Zᵢ` of `C'_s`" (T:3205).
We choose them on a hyperplane: for `q : Y → Spec V` projective and nodal over a local ring with
algebraically closed residue field and a component `Z` of the closed fibre `X = Y_{s₀}`,
`exists_hyperplane_data` gives affine opens `A₀ = Y ∩ D₊(ℓ)`, `B₀ = Y ∩ D₊(ℓ')` of `Y` and the
finite set `P = (X ∖ A₀) ∖ Z` such that

* `X ∖ A₀` is a finite set of closed smooth points of `X`, inside `B₀` (the hyperplane `ℓ`
  avoids the generic points and the finitely many double points of `X`, and `ℓ'` avoids
  `X ∖ A₀`);
* the points of `P` are closed points of `Y` in the smooth locus of `q`, off `Z`, and every other
  component of `X` contains a point of `P` (`exists_not_mem_of_mem_genericPoints`: a component of
  `X`, a proper integral curve over `κ`, is not contained in the affine open `A₀`);
* the points of `X ∖ A₀` outside `P` lie on `Z` and on no other component.

This is the input of the divisor `T = ⋃ P̄ᵢ` (`SectionsDivisor.exists_localEquations`) and of the
two-chart cover `Y = (A₀ ∖ T) ∪ D(σ)` of the cohomological argument (`ContractingExists.lean`).
Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-hyperplane`.
-/

namespace DeJongAlterations.StableModification.BlowDown.SectionsHyperplane

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Topology IsLocalRing
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

variable {V : Type u} [CommRing V] [IsLocalRing V] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of V)) [DeJong.IsNodalCurve q] [IsProper q]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]

local notation "s₀" => IsLocalRing.closedPoint V

/-- **A component of the closed fibre is not contained in an affine open of `Y`**: its reduced
closure is integral and proper over `κ(s₀)`, so its global functions form a field and a morphism
from it to an affine scheme is constant; a component is not a point. -/
theorem exists_not_mem_of_mem_genericPoints (hq : IsProjectiveOver q) {w : q.fiber s₀}
    (hw : w ∈ genericPoints (q.fiber s₀)) {A₀ : Y.Opens} (hA₀ : IsAffineOpen A₀) :
    ∃ x ∈ closure ({w} : Set (q.fiber s₀)), q.fiberι s₀ x ∉ A₀ := by
  by_contra h
  push Not at h
  have hpX := isProjectiveOver_fiberToSpecResidueField q s₀ hq
  have : IsProper (q.fiberToSpecResidueField s₀) := hpX.isProper
  have hpure := Domination.pure_fiber_of_isNodalCurve q s₀
  have hfield : IsField Γ(ClosureComponent.closureScheme w, ⊤) :=
    isField_of_universallyClosed _ (ClosureComponent.closureι w ≫ q.fiberToSpecResidueField s₀)
  set j := ClosureComponent.closureι w ≫ q.fiberι s₀
  have hrange : Set.range j ⊆ A₀ := by
    rintro _ ⟨t, rfl⟩
    apply h
    rw [← ClosureComponent.range_closureι w]
    exact ⟨t, rfl⟩
  obtain ⟨k, hk⟩ := ContractingMap.exists_toSpecΓ_comp j hA₀ hrange
  have hinj : Function.Injective j := by
    intro t₁ t₂ ht
    have h1 : ClosureComponent.closureι w t₁ = ClosureComponent.closureι w t₂ :=
      (q.fiberι s₀).isEmbedding.injective (by simpa [j] using ht)
    exact (ClosureComponent.closureι w).isEmbedding.injective h1
  have hsub : ∀ t₁ t₂ : ClosureComponent.closureScheme w, t₁ = t₂ := by
    intro t₁ t₂
    apply hinj
    rw [← hk, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      ContractingMap.toSpecΓ_apply_eq hfield t₁ t₂]
  -- `closure {w} = {w}`, so `w` is closed
  have hcl : IsClosed ({w} : Set (q.fiber s₀)) := by
    have e : closure ({w} : Set (q.fiber s₀)) = {w} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨subset_closure rfl, fun x hx => ?_⟩
      rw [← ClosureComponent.range_closureι w] at hx
      obtain ⟨t, rfl⟩ := hx
      rw [hsub t (ClosureComponent.closurePt w)]
      exact ClosureComponent.closureι_closurePt w
    rw [← e]
    exact isClosed_closure
  exact not_mem_genericPoints_of_isClosed hpure hcl hw

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **A hyperplane section of the closed fibre** (T:3205): affine opens `A₀`, `B₀` of `Y` and a
finite set `P` of closed smooth points of the closed fibre with the properties listed in the
module docstring. -/
theorem exists_hyperplane_data [Infinite (IsLocalRing.ResidueField V)] (hq : IsProjectiveOver q)
    (Z : q.fiber s₀) (hZ : Z ∈ genericPoints (q.fiber s₀)) :
    ∃ (A₀ B₀ : Y.Opens) (P : Finset Y),
      IsAffineOpen A₀ ∧ IsAffineOpen B₀ ∧
      (∀ p ∈ P, p ∈ q.smoothLocus ∧ IsClosed ({p} : Set Y) ∧ q p = s₀) ∧
      (∀ p ∈ P, p ∉ closure ({q.fiberι s₀ Z} : Set Y)) ∧
      (∀ w ∈ genericPoints (q.fiber s₀), w ≠ Z → ∃ p ∈ P, p ∈ closure ({q.fiberι s₀ w} : Set Y)) ∧
      (∀ w ∈ genericPoints (q.fiber s₀), q.fiberι s₀ w ∈ A₀) ∧
      (∀ x : q.fiber s₀, q.fiberι s₀ x ∉ A₀ →
        q.fiberι s₀ x ∈ B₀ ∧ IsClosed ({q.fiberι s₀ x} : Set Y)) ∧
      {x : q.fiber s₀ | q.fiberι s₀ x ∉ A₀}.Finite ∧
      (∀ p ∈ P, p ∉ A₀) ∧
      (∀ x : q.fiber s₀, q.fiberι s₀ x ∉ A₀ → q.fiberι s₀ x ∉ P →
        x ∈ closure ({Z} : Set (q.fiber s₀)) ∧
          ∀ w ∈ genericPoints (q.fiber s₀), w ≠ Z → x ∉ closure ({w} : Set (q.fiber s₀))) := by
  classical
  -- facts on the closed fibre `X`
  have hdim : topologicalKrullDim (q.fiber s₀) ≤ 1 := topologicalKrullDim_fiber_le_one_of_nodal q s₀
  have hpure := Domination.pure_fiber_of_isNodalCurve q s₀
  have hnodal := Domination.nodes_fiber_of_isNodalCurve q s₀
  have hpX := isProjectiveOver_fiberToSpecResidueField q s₀ hq
  have : NoetherianSpace (q.fiber s₀) := noetherianSpace_fiber q s₀
  have hcemb := isClosedEmbedding_fiberι_closedPoint q
  have : LocallyOfFinitePresentation (q.fiberToSpecResidueField s₀) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  have : IsAlgClosed (IsLocalRing.ResidueField ((Spec (CommRingCat.of V)).presheaf.stalk s₀)) :=
    (inferInstance : IsAlgClosed ((Spec (CommRingCat.of V)).residueField s₀))
  have hq₀ := hq
  -- the generic points and the non-smooth points are finitely many
  set G : Set (q.fiber s₀) := genericPoints (q.fiber s₀)
  have hG : G.Finite := Set.toFinite _
  set Sg : Set (q.fiber s₀) :=
    ((q.fiberToSpecResidueField s₀).smoothLocus : Set (q.fiber s₀))ᶜ
  have hgsm : ∀ v ∈ G, v ∈ (q.fiberToSpecResidueField s₀).smoothLocus := fun v hv =>
    NoClosedExc.isSmoothAt_of_mem_genericPoints (q.fiberToSpecResidueField s₀) hdim hpX hpure
      hnodal hv
  have hSgcl : ∀ x ∈ Sg, IsClosed ({x} : Set (q.fiber s₀)) := fun x hx =>
    Genus.isClosed_singleton_of_not_mem_genericPoints hdim fun hg => hx (hgsm x hg)
  have hSg : Sg.Finite := Ample.finite_of_forall_isClosed_singleton
    (q.fiberToSpecResidueField s₀).smoothLocus.isOpen.isClosed_compl hSgcl
  -- the projective embedding
  obtain ⟨N', i, hi, -⟩ := hq
  have : IsClosedImmersion i := hi
  have hiA : IsAffineHom i := inferInstance
  -- the hyperplane `ℓ` avoids the generic points and the non-smooth points
  obtain ⟨ℓ, hℓ, hℓS⟩ := exists_linearForm_mem_basicOpen (hG.union hSg).toFinset
    (fun x => (i (q.fiberι s₀ x) : Proj (projectiveSpaceGrading V N')))
  set A₀ : Y.Opens := i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading V N') ℓ
  have hA₀ : IsAffineOpen A₀ :=
    @IsAffineOpen.preimage _ _ _ (Proj.isAffineOpen_basicOpen _ ℓ hℓ one_pos) i hiA
  have hGA : ∀ v ∈ G, q.fiberι s₀ v ∈ A₀ := fun v hv =>
    hℓS v ((hG.union hSg).mem_toFinset.mpr (Or.inl hv))
  have hSgA : ∀ v ∈ Sg, q.fiberι s₀ v ∈ A₀ := fun v hv =>
    hℓS v ((hG.union hSg).mem_toFinset.mpr (Or.inr hv))
  -- `H = X ∖ A₀`: finitely many closed smooth points
  set H : Set (q.fiber s₀) := {x | q.fiberι s₀ x ∉ A₀}
  have hHcl : IsClosed H := A₀.isOpen.isClosed_compl.preimage (q.fiberι s₀).continuous
  have hHpt : ∀ x ∈ H, IsClosed ({x} : Set (q.fiber s₀)) := fun x hx =>
    Genus.isClosed_singleton_of_not_mem_genericPoints hdim fun hg => hx (hGA x hg)
  have hHfin : H.Finite := Ample.finite_of_forall_isClosed_singleton hHcl hHpt
  have hHsm : ∀ x ∈ H, x ∈ (q.fiberToSpecResidueField s₀).smoothLocus := fun x hx => by
    by_contra h
    exact hx (hSgA x h)
  -- the hyperplane `ℓ'` avoids `H`
  obtain ⟨ℓ', hℓ', hℓ'S⟩ := exists_linearForm_mem_basicOpen hHfin.toFinset
    (fun x => (i (q.fiberι s₀ x) : Proj (projectiveSpaceGrading V N')))
  set B₀ : Y.Opens := i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading V N') ℓ'
  have hB₀ : IsAffineOpen B₀ :=
    @IsAffineOpen.preimage _ _ _ (Proj.isAffineOpen_basicOpen _ ℓ' hℓ' one_pos) i hiA
  -- `P = H ∖ Z`
  set P₀ : Set (q.fiber s₀) := H \ closure {Z}
  have hP₀ : P₀.Finite := hHfin.subset Set.sdiff_subset
  set P : Finset Y := (hP₀.image (q.fiberι s₀)).toFinset
  have hmemP : ∀ y, y ∈ P ↔ ∃ x ∈ P₀, q.fiberι s₀ x = y := fun y => by
    rw [Set.Finite.mem_toFinset]
    rfl
  -- a smooth point lies on one component only
  have huniq : ∀ x ∈ H, ∀ w₁ ∈ G, ∀ w₂ ∈ G, x ∈ closure {w₁} → x ∈ closure {w₂} → w₁ = w₂ :=
    fun x hx w₁ hw₁ w₂ hw₂ h₁ h₂ =>
      Domination.eq_of_mem_closure_of_isSmoothAt (q.fiberToSpecResidueField s₀) hdim (hHsm x hx)
        hw₁ hw₂ h₁ h₂
  refine ⟨A₀, B₀, P, hA₀, hB₀, ?_, ?_, ?_, hGA, ?_, hHfin, ?_, ?_⟩
  · -- the points of `P`
    intro p hp
    obtain ⟨x, hx, rfl⟩ := (hmemP p).mp hp
    refine ⟨?_, by rw [← Set.image_singleton]; exact hcemb.isClosedMap _ (hHpt x hx.1),
      apply_fiberι q s₀ x⟩
    have e := Omega.preimage_smoothLocus_eq_of_isNodalCurve (f := q)
      ((Spec (CommRingCat.of V)).residueField s₀)
      ((Spec (CommRingCat.of V)).fromSpecResidueField s₀)
    have hx' : x ∈ (pullback.snd q ((Spec (CommRingCat.of V)).fromSpecResidueField s₀)).smoothLocus :=
      hHsm x hx.1
    rw [← e] at hx'
    exact hx'
  · -- `P` avoids `Z`
    intro p hp hpZ
    obtain ⟨x, hx, rfl⟩ := (hmemP p).mp hp
    rw [closure_fiberι_singleton] at hpZ
    obtain ⟨z, hz, hzx⟩ := hpZ
    rw [(q.fiberι s₀).isEmbedding.injective hzx] at hz
    exact hx.2 hz
  · -- every other component meets `P`
    intro w hw hwZ
    obtain ⟨x, hxw, hxA⟩ := exists_not_mem_of_mem_genericPoints q hq₀ hw hA₀
    refine ⟨q.fiberι s₀ x, (hmemP _).mpr ⟨x, ⟨hxA, fun hxZ => hwZ ?_⟩, rfl⟩, ?_⟩
    · exact huniq x hxA w hw Z hZ hxw hxZ
    · rw [closure_fiberι_singleton]
      exact ⟨x, hxw, rfl⟩
  · -- `H ⊆ B₀`, closed points
    intro x hx
    exact ⟨hℓ'S x (hHfin.mem_toFinset.mpr hx),
      by rw [← Set.image_singleton]; exact hcemb.isClosedMap _ (hHpt x hx)⟩
  · -- `P ⊆ H`
    intro p hp
    obtain ⟨x, hx, rfl⟩ := (hmemP p).mp hp
    exact hx.1
  · -- the points of `H` outside `P`
    intro x hx hxP
    have hxZ : x ∈ closure {Z} := by
      by_contra h
      exact hxP ((hmemP _).mpr ⟨x, ⟨hx, h⟩, rfl⟩)
    exact ⟨hxZ, fun w hw hwZ hxw => hwZ (huniq x hx w hw Z hZ hxw hxZ)⟩

end

end DeJongAlterations.StableModification.BlowDown.SectionsHyperplane
