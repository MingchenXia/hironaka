/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.SectionsHyperplane
import DeJongAlterations.StableModification.BlowDown.SectionsDivisor
import DeJongAlterations.StableModification.BlowDown.VanishingCore
import DeJongAlterations.StableModification.BlowDown.VanishingGenus
import DeJongAlterations.StableModification.BlowDown.VanishingTwist
import DeJongAlterations.StableModification.BlowDown.Genus
import DeJongAlterations.StableModification.Cohomology.Valuation
import DeJongAlterations.StableModification.Gluing.SetupAssembly

/-!
# Temkin's contracting morphism (Prop. 4.4.6, T:3203–3226)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6 (T:3203–3226): for a semi-stable stage `β : Y → C` over a henselian valuation ring
`V` with algebraically closed residue field and an exceptional component `Z` of the closed fibre
`X = Y_{s₀}`, there is `h̄ = (h, β) : Y → ℙ¹_C` contracting exactly `Z` among the components of
`X`. This file proves `BlowDown.ContractingMorphismExists` (`contractingMorphismExists`) for `C`
projective over `V`, given lane T44E's `NoClosedExc.NodalComponentGenus` (a component of a nodal
curve without double point of its own has `p_a = g`), and the resulting form of Temkin's
Prop. 4.4.6 without the contracting-morphism hypothesis
(`exists_isStableModification_of_isSemistableStage'`).

## The construction

1. **Genus `0`**: the exceptional data of `Z` (`BlowDown.IsClosedExceptional`: `g(Z) = 0`, `{Z}` a
   tree, so no double point of `Z` lies on `Z` alone) and `NodalComponentGenus` give
   `p_a(Z) = 0` (`arithmeticGenus_closure_eq_zero`).
2. **Points `pᵢ`** (T:3205): a hyperplane section `X ∖ A₀` of `X` avoiding the generic points and
   the double points; `P = (X ∖ A₀) ∖ Z` (`SectionsHyperplane.exists_hyperplane_data`). Every other
   component meets `P`.
3. **The divisor `T = ⋃ P̄ᵢ`** (T:3207–3210, `SectionsDivisor.exists_localEquations`) with
   canonical section `s` of `𝓛 = 𝒪(T)`; `T ∩ X = P`.
4. **The cover** `Y = U ∪ V` with `U = A₀ ∩ D(s)` affine and `V = D(σ)` for a section `σ` of `𝓛`
   over `B₀` without zero on the finite set `X ∖ A₀` (OM3B's `Ample.exists_section_nonvanishing`);
   `𝓛^k = 𝒪(kT)` is the divisor twist by `f = s/σ`.
5. **Vanishing** (T:3210–3219): on `X`, `H¹(X ∖ T, 𝒪) = 0` on the cover
   (`VanishingCore.exists_sub_eq_res` with `h¹(Z, 𝒪_Z) = 0`, `VanishingGenus.exists_sub_eq_closure`:
   the points of `D(f) ∖ U` lie on `Z` only); hence `H¹(Y, 𝒪(mT)) = 0` for `m ≫ 0`
   (`VanishingTwist.exists_forall_subsingleton_H1_of_fibre`; `H¹(Y, 𝒪)` is finitely presented over
   `V`, `Cohomology.finitePresentation_cohomology_of_isProjectiveOver_valuation`).
6. **The second section** `t` of `𝓛^{m+1}` without common zero with `s^{m+1}`
   (`VanishingTwist.exists_section_of_subsingleton_H1`, T:3220–3222), and
   `h̄ = ([s^{m+1} : t], β) : Y → ℙ¹_C` (`ContractingMap.exists_contracting_of_sections`): `Z` misses
   `T` and the other components meet `T`.

Blueprint `sm-blow-down-contracting.tex`, `thm:sm-bdc-contracting`.
-/

namespace DeJongAlterations.StableModification.BlowDown.ContractingExists

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Topology Opposite IsLocalRing
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.Genus
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.CurvesField.Ample.LineBundleData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Genus

variable {V : Type u} [CommRing V] [IsLocalRing V] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of V)) [DeJong.IsNodalCurve q] [IsProper q]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]

local notation "s₀" => IsLocalRing.closedPoint V

open scoped Classical in
/-- **An exceptional component of the closed fibre has arithmetic genus `0`** (T:3213, given
`NodalComponentGenus`): its genus `g(Z)` is `0` and, `{Z}` being a tree of the incidence graph,
every double point of `X` on `Z` lies on another component, so `p_a(Z) = g(Z)`. -/
theorem arithmeticGenus_closure_eq_zero (hbridge : NoClosedExc.NodalComponentGenus.{u})
    (hq : IsProjectiveOver q) (Z : q.fiber s₀) (hZ : Z ∈ genericPoints (q.fiber s₀))
    (hg0 : 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        (q.fiberToSpecResidueField s₀)) Z)
    (hcomb : ∀ [Fintype (nodesIn (q.fiberToSpecResidueField s₀) (closure {Z}))],
      (nodalGraph (q.fiberToSpecResidueField s₀)
          (topologicalKrullDim_fiber_le_one_of_nodal q s₀) (closure {Z})).IsP1Tree {Z}) :
    arithmeticGenus (ClosureComponent.closureScheme Z)
      (structureCoeff (ClosureComponent.closureι Z ≫ q.fiberToSpecResidueField s₀)) = 0 := by
  have hdim := topologicalKrullDim_fiber_le_one_of_nodal q s₀
  have hpX := isProjectiveOver_fiberToSpecResidueField q s₀ hq
  have hpure := Domination.pure_fiber_of_isNodalCurve q s₀
  have hnodal := Domination.nodes_fiber_of_isNodalCurve q s₀
  have : NoetherianSpace (q.fiber s₀) := noetherianSpace_fiber q s₀
  have : Fintype (nodesIn (q.fiberToSpecResidueField s₀) (closure {Z})) :=
    (Genus.finite_nodesIn (q.fiberToSpecResidueField s₀) hdim hpX (closure {Z})).fintype
  obtain ⟨⟨-, hcard⟩, hgen⟩ := hcomb
  -- `g(Z) = 0`
  have hg : componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        (q.fiberToSpecResidueField s₀)) Z = 0 := by
    have h := hgen Z (Finset.mem_singleton_self Z)
    rw [nodalGraph_genus] at h
    have := Int.toNat_eq_zero.mp h
    omega
  -- no double point of `Z` alone
  have hinner : (nodalGraph (q.fiberToSpecResidueField s₀) hdim (closure {Z})).inner {Z} = ∅ := by
    rw [Finset.card_singleton] at hcard
    exact Finset.card_eq_zero.mp (by omega)
  have hbd : ∀ y ∈ closure {Z}, IsClosed ({y} : Set (q.fiber s₀)) →
      Geometry.IsGeometricOrdinaryDoublePoint (q.fiberToSpecResidueField s₀) y →
      ∃ w ∈ genericPoints (q.fiber s₀), w ≠ Z ∧ y ∈ closure {w} := by
    intro y hyZ hyc hyo
    have hyn : y ∈ nodesIn (q.fiberToSpecResidueField s₀) (closure {Z}) :=
      ⟨hyZ, hyc, not_mem_genericPoints_of_isClosed hpure hyc, hyo⟩
    have he : (⟨y, hyn⟩ : nodesIn (q.fiberToSpecResidueField s₀) (closure {Z})) ∉
        (nodalGraph (q.fiberToSpecResidueField s₀) hdim (closure {Z})).inner {Z} := by
      rw [hinner]
      exact Finset.notMem_empty _
    rw [mem_inner] at he
    push Not at he
    obtain ⟨w, hw, hwZ⟩ := he
    rw [mem_nodalGraph_ends] at hw
    exact ⟨w, hw.1, fun h => hwZ (Finset.mem_singleton.mpr h), hw.2⟩
  rw [hbridge _ _ _ hdim hpX hnodal Z hZ hbd, hg]

end Genus

section Sections

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [HenselianLocalRing V]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]
  {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of V)) [IsIntegral Y] [DeJong.IsNodalCurve q]
  [IsProper q]

local notation "s₀" => IsLocalRing.closedPoint V
local notation "ιq" => q.fiberι s₀

/-- **Two generating sections contracting exactly `Z`** (T:3203–3222): for a projective nodal
integral `V`-curve `Y` and a component `Z` of arithmetic genus `0` of the closed fibre, some power
`𝓛^m` of a line bundle has two sections without common zero, the first one without zero on `Z`
and at the generic points of the closed fibre, but with a zero on every other component. -/
theorem exists_sections (hp : IsProjectiveOver q) (Z : q.fiber s₀)
    (hZgen : Z ∈ genericPoints (q.fiber s₀))
    (hgenus : arithmeticGenus (ClosureComponent.closureScheme Z)
      (structureCoeff (ClosureComponent.closureι Z ≫ q.fiberToSpecResidueField s₀)) = 0) :
    ∃ (L : LineBundleData Y) (m : ℤ) (sv : Fin 2 → L.Sections m ⊤),
      LineBundleData.Generates sv ∧
      closure {ιq Z} ⊆ ((sv 0).nonvanishingLocus : Set Y) ∧
      (∀ w ∈ genericPoints (q.fiber s₀), ιq w ∈ (sv 0).nonvanishingLocus) ∧
      (∀ w ∈ genericPoints (q.fiber s₀), w ≠ Z →
        ∃ y ∈ closure {ιq w}, y ∉ (sv 0).nonvanishingLocus) := by
  classical
  have : CompactSpace Y := Ample.compactSpace_of_quasiCompact q
  have : IsAffineHom (pullback.diagonal (terminal.from Y)) :=
    Ample.isAffineHom_diagonal_of_isSeparated q
  have : IsAlgClosed (IsLocalRing.ResidueField V) :=
    IsAlgClosed.of_ringEquiv _ _ (residueFieldClosedPointEquiv (V := V)).symm
  have : Infinite (IsLocalRing.ResidueField V) := inferInstance
  have : IsAlgClosed (IsLocalRing.ResidueField ((Spec (CommRingCat.of V)).presheaf.stalk s₀)) :=
    (inferInstance : IsAlgClosed ((Spec (CommRingCat.of V)).residueField s₀))
  have hpX := isProjectiveOver_fiberToSpecResidueField q s₀ hp
  have : NoetherianSpace (q.fiber s₀) := noetherianSpace_fiber q s₀
  -- the hyperplane data
  obtain ⟨A₀, B₀, P, hA₀, hB₀, hPprop, hPZ, hPmeet, hGA, hHB, hHfin, hPA, hHP⟩ :=
    SectionsHyperplane.exists_hyperplane_data q hp Z hZgen
  -- the divisor `T`
  have hpure : Curves.SemistableOpen.PureOneDimensionalFibres q :=
    DeJong.IsNodalCurve.pureGeometricFibers
  obtain ⟨Dl, hD1, hD2⟩ := SectionsDivisor.exists_localEquations q hpure P
    (fun p hp => (hPprop p hp).1) (fun p hp => (hPprop p hp).2.1) (fun p hp => (hPprop p hp).2.2)
    (ιq Z) (apply_fiberι q s₀ Z) (fun h => hPZ _ h (subset_closure rfl))
  let L := Dl.toLineBundleData
  let s : L.Sections 1 ⊤ := Dl.canonicalSection
  -- the cover
  have hUdef : (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus = A₀ ⊓ s.nonvanishingLocus :=
    LineBundleData.Sections.nonvanishingLocus_restrict _ _
  have hUaff : IsAffineOpen (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus :=
    Ample.isAffineOpen_nonvanishingLocus_of_isAffineOpen hA₀ _
  have hUs : (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ≤ s.nonvanishingLocus :=
    hUdef ▸ inf_le_right
  have hSfin : (ιq '' {x | ιq x ∉ A₀}).Finite := hHfin.image _
  have hSB₀ : ιq '' {x | ιq x ∉ A₀} ⊆ B₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hHB x hx).1
  have hScl : ∀ z ∈ ιq '' {x | ιq x ∉ A₀}, IsClosed ({z} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hHB x hx).2
  obtain ⟨σ₁, hσ₁⟩ := Ample.exists_section_nonvanishing L 1 hB₀ hSfin hSB₀ hScl
  have hVaff : IsAffineOpen σ₁.nonvanishingLocus :=
    Ample.isAffineOpen_nonvanishingLocus_of_isAffineOpen hB₀ σ₁
  let σ : L.Sections 1 σ₁.nonvanishingLocus :=
    σ₁.restrict (LineBundleData.Sections.nonvanishingLocus_le σ₁)
  have hσ : σ.nonvanishingLocus = σ₁.nonvanishingLocus := by
    rw [LineBundleData.Sections.nonvanishingLocus_restrict]
    exact inf_idem _
  -- points of the closed fibre
  have hfib : ∀ y : Y, q y = s₀ → ∃ x, ιq x = y := fun y hy => by
    have : y ∈ Set.range ιq := by rw [Scheme.Hom.range_fiberι]; exact hy
    exact this
  have hPS : ∀ p ∈ P, p ∈ ιq '' {x | ιq x ∉ A₀} := fun p hp => by
    obtain ⟨x, rfl⟩ := hfib p (hPprop p hp).2.2
    exact ⟨x, hPA _ hp, rfl⟩
  have hcov : (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊔ σ₁.nonvanishingLocus = ⊤ := by
    apply top_unique
    intro y _
    by_cases hyU : y ∈ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus
    · exact Opens.mem_sup.mpr (Or.inl hyU)
    refine Opens.mem_sup.mpr (Or.inr ?_)
    by_cases hyA : y ∈ A₀
    · have hys : y ∉ s.nonvanishingLocus := fun h => hyU (by rw [hUdef]; exact ⟨hyA, h⟩)
      obtain ⟨p, hpP, hyp⟩ := hD2 y hys
      exact hyp.mem_open σ₁.nonvanishingLocus.isOpen (hσ₁ p (hPS p hpP))
    · obtain ⟨z, hyz, hz⟩ := SectionsDivisor.exists_specializes_closedPoint q y
      have hzA : z ∉ A₀ := fun h => hyA (hyz.mem_open A₀.isOpen h)
      obtain ⟨x, rfl⟩ := hfib z hz
      exact hyz.mem_open σ₁.nonvanishingLocus.isOpen (hσ₁ _ ⟨x, hzA, rfl⟩)
  have hf := isUnit_ratio s hσ hUs
  have hUV : IsAffineOpen ((s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊓
      σ₁.nonvanishingLocus) := hUaff.inf hVaff
  -- `H¹(Y, 𝒪)` is finitely generated
  have hfp := finitePresentation_cohomology_of_isProjectiveOver_valuation hp (unitModule Y)
    (fun W _ => Module.Finite.self Γ(Y, W)) (fun W _ => flat_sectionsModuleCat_unit q W) 1
  have : Module.Finite V (H1
      (resUV (unitModule Y) (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus
        σ₁.nonvanishingLocus (structureCoeff q))
      (resVU (unitModule Y) (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus
        σ₁.nonvanishingLocus (structureCoeff q))
      (twistFamily (unitModule Y) (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus
        σ₁.nonvanishingLocus (structureCoeff q) hf 0)) :=
    Module.Finite.equiv (cohomologyOneEquivTwistZero (unitModule Y) _ _ (structureCoeff q) hf
      hcov hUaff hVaff hUV)
  -- `H¹(X ∖ T, 𝒪) = 0` on the closed fibre
  have hcore : ∀ w : Γ(q.fiber s₀, ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊓
        ιq ⁻¹ᵁ σ₁.nonvanishingLocus),
      ∃ (a : Γ(q.fiber s₀, ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus))
        (b : Γ(q.fiber s₀, (q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ))))
        (h : ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊓
          ιq ⁻¹ᵁ σ₁.nonvanishingLocus ≤
            (q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ))),
        w = (q.fiber s₀).presheaf.map (homOfLE h).op b -
          (q.fiber s₀).presheaf.map (homOfLE (inf_le_left :
            ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊓
              ιq ⁻¹ᵁ σ₁.nonvanishingLocus ≤
                ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus)).op a := by
    intro w
    have hfX := VanishingTwist.isUnit_app ιq hf
    have hAB' : ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊓
        ιq ⁻¹ᵁ σ₁.nonvanishingLocus ≤
          (q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ)) := by
      intro x hx
      have h := (q.fiber s₀).basicOpen_of_isUnit hfX
      rw [Scheme.basicOpen_res] at h
      have : x ∈ ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊓
          ιq ⁻¹ᵁ σ₁.nonvanishingLocus ⊓
            (q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ)) := by
        rw [h]; exact hx
      exact this.2
    -- the open `N` of points of `Z` on no other component
    have hOcl : IsClosed (⋃ w' ∈ {w' | w' ∈ genericPoints (q.fiber s₀) ∧ w' ≠ Z},
        closure ({w'} : Set (q.fiber s₀))) :=
      ((Set.toFinite (genericPoints (q.fiber s₀))).subset fun _ h => h.1).isClosed_biUnion
        fun _ _ => isClosed_closure
    let Nc : (q.fiber s₀).Opens := ⟨_, hOcl.isOpen_compl⟩
    have hB'B : (q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ)) ≤
        ιq ⁻¹ᵁ σ₁.nonvanishingLocus := (q.fiber s₀).basicOpen_le _
    have hcov' : (q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ)) ≤
        (ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊓ ιq ⁻¹ᵁ σ₁.nonvanishingLocus) ⊔
          ((q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ)) ⊓ Nc) := by
      intro x hx
      by_cases hxU : x ∈ ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus
      · exact Opens.mem_sup.mpr (Or.inl ⟨hxU, hB'B hx⟩)
      refine Opens.mem_sup.mpr (Or.inr ⟨hx, ?_⟩)
      have hx' : ιq x ∈ Y.basicOpen (ratio s hσ) := by
        have e := Scheme.preimage_basicOpen ιq (ratio s hσ)
        have : x ∈ ιq ⁻¹ᵁ Y.basicOpen (ratio s hσ) := by rw [e]; exact hx
        exact this
      rw [basicOpen_ratio] at hx'
      have hxA : ιq x ∉ A₀ := fun h => hxU (by
        change ιq x ∈ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus
        rw [hUdef]
        exact ⟨h, hx'.2⟩)
      have hxP : ιq x ∉ P := (hD1 (ιq x) (apply_fiberι q s₀ x)).mp hx'.2
      obtain ⟨-, hother⟩ := hHP x hxA hxP
      intro hxO
      simp only [Set.mem_iUnion] at hxO
      obtain ⟨w', ⟨hw', hw'Z⟩, hxw'⟩ := hxO
      exact hother w' hw' hw'Z hxw'
    have hNξ : (((q.fiber s₀).basicOpen ((ιq).app σ₁.nonvanishingLocus (ratio s hσ)) ⊓ Nc :
        (q.fiber s₀).Opens) : Set (q.fiber s₀)) ⊆ closure {Z} := by
      rintro x ⟨-, hxN⟩
      obtain ⟨v, hv, hxv⟩ := Domination.exists_mem_genericPoints_mem_closure x
      by_cases hvZ : v = Z
      · rw [← hvZ]; exact hxv
      · exact absurd (Set.mem_biUnion (x := v)
          (show v ∈ {w' | w' ∈ genericPoints (q.fiber s₀) ∧ w' ≠ Z} from ⟨hv, hvZ⟩) hxv) hxN
    have hAX : IsAffineOpen (ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus) :=
      hUaff.preimage ιq
    have hBX : IsAffineOpen (ιq ⁻¹ᵁ σ₁.nonvanishingLocus) := hVaff.preimage ιq
    have hcovX : ιq ⁻¹ᵁ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊔
        ιq ⁻¹ᵁ σ₁.nonvanishingLocus = ⊤ := by
      apply top_unique
      intro x _
      have hx : ιq x ∈ (s.restrict (le_top : A₀ ≤ ⊤)).nonvanishingLocus ⊔ σ₁.nonvanishingLocus := by
        rw [hcov]; trivial
      rcases Opens.mem_sup.mp hx with hx | hx
      · exact Opens.mem_sup.mpr (Or.inl hx)
      · exact Opens.mem_sup.mpr (Or.inr hx)
    have : IsAffineHom (pullback.diagonal (terminal.from (ClosureComponent.closureScheme Z))) :=
      Ample.isAffineHom_diagonal_of_isSeparated
        (ClosureComponent.closureι Z ≫ q.fiberToSpecResidueField s₀)
    have hZ' := VanishingGenus.exists_sub_eq_closure (q.fiberToSpecResidueField s₀) hpX Z hcovX
      hAX hBX hgenus
    obtain ⟨a, b, hab⟩ := VanishingCore.exists_sub_eq_res Z hAX hBX hB'B hAB' inf_le_left hcov'
      hNξ hZ' w
    exact ⟨a, b, hAB', hab⟩
  -- `H¹(Y, 𝒪(mT)) = 0` for `m ≫ 0`
  obtain ⟨m₀, hm₀⟩ := VanishingTwist.exists_forall_subsingleton_H1_of_fibre q hUaff hVaff hUV hf
    hcore
  have := hm₀ m₀ le_rfl
  -- the second section
  obtain ⟨t, ht⟩ := VanishingTwist.exists_section_of_subsingleton_H1 (structureCoeff q) s hσ hUs
    hcov m₀
  have hnv : (s.npow (m₀ + 1)).nonvanishingLocus = s.nonvanishingLocus :=
    LineBundleData.Sections.nonvanishingLocus_npow s (Nat.succ_pos m₀)
  let sv : Fin 2 → L.Sections (1 * ((m₀ + 1 : ℕ) : ℤ)) ⊤ := ![s.npow (m₀ + 1), t]
  have hsv0 : sv 0 = s.npow (m₀ + 1) := rfl
  have hfibnv : ∀ y : Y, q y = s₀ → y ∉ P → y ∈ (sv 0).nonvanishingLocus := fun y hy hyP => by
    rw [hsv0, hnv]
    exact (hD1 y hy).mpr hyP
  refine ⟨L, _, sv, fun y => ?_, ?_, ?_, ?_⟩
  · have hy : y ∈ s.nonvanishingLocus ⊔ t.nonvanishingLocus := by rw [ht]; trivial
    rcases Opens.mem_sup.mp hy with hy | hy
    · exact ⟨0, by rw [hsv0, hnv]; exact hy⟩
    · exact ⟨1, hy⟩
  · intro y hy
    have hyP : y ∉ P := fun h => hPZ y h hy
    rw [closure_fiberι_singleton] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact hfibnv _ (apply_fiberι q s₀ x) hyP
  · intro w hw
    exact hfibnv _ (apply_fiberι q s₀ w) (fun h => hPA _ h (hGA w hw))
  · intro w hw hwZ
    obtain ⟨p, hpP, hpw⟩ := hPmeet w hw hwZ
    refine ⟨p, hpw, ?_⟩
    rw [hsv0, hnv]
    exact fun h => ((hD1 p (hPprop p hpP).2.2).mp h) hpP

end Sections

section Main

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [HenselianLocalRing V]
  {C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]

/-- **Temkin's contracting morphism** (Prop. 4.4.6, T:3203–3226; blueprint
`thm:sm-bdc-contracting`): over a henselian valuation ring with algebraically closed residue field,
for `C` projective and locally of finite presentation over `V`, every semi-stable stage with an
exceptional component `Z` of its closed fibre admits `h̄ : Y → ℙ¹_C` over `C` contracting exactly
`Z`, given `NodalComponentGenus` (lane T44E). -/
theorem contractingMorphismExists (hC : IsProjectiveOver φ) [LocallyOfFinitePresentation φ]
    (hbridge : NoClosedExc.NodalComponentGenus.{u}) : ContractingMorphismExists φ D := by
  intro Y β hY hn hpr Z hZ
  have : IsIntegral Y := hY.isIntegral
  have hp : IsProjectiveOver (β ≫ φ) := hY.isProjectiveOver
  have : DeJong.IsNodalCurve (β ≫ φ) := hn
  have : IsProper (β ≫ φ) := hpr
  have : CompactSpace Y := Ample.compactSpace_of_quasiCompact (β ≫ φ)
  obtain ⟨hZgen, hβZ, hg0, hcomb⟩ := hZ
  have hgenus := arithmeticGenus_closure_eq_zero (β ≫ φ) hbridge hp Z hZgen hg0
    (fun {inst} => (@hcomb inst).1)
  obtain ⟨L, m, sv, hgen, hZcl, hgen', hmeet⟩ := exists_sections (β ≫ φ) hp Z hZgen hgenus
  exact ContractingMap.exists_contracting_of_sections φ β hC hgen hp Z hβZ hZcl hgen' hmeet

end Main

section Stable

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)
  [IsIntegral C] [IsProper φ] [Flat φ] [HenselianLocalRing V]

/-- **Temkin's Proposition 4.4.6 without the contracting-morphism hypothesis** (T:3188–3229;
PLAN-T5's `BlowDownStable`, blueprint `thm:sm-bdc-blowdown-stable`): the conclusion of
`BlowDown.exists_isStableModification_of_isSemistableStage` for `C` projective over `V`, with
`ContractingMorphismExists` discharged by `contractingMorphismExists`. The remaining named
hypotheses are lane T44A3's `ClosureComponentLocal`, `NumericalDescent` and lane T44E's
`NodalComponentGenus` (all three proved by lane T44E, not yet integrated). -/
theorem exists_isStableModification_of_isSemistableStage
    (hloc : ExcSpecialize.ClosureComponentLocal.{u}) (hdesc : NoClosedExc.NumericalDescent.{u})
    (hbridge : NoClosedExc.NodalComponentGenus.{u}) (hC : IsProjectiveOver φ)
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), b ≫ β'' = β ∧
      IsSemistableStage φ D β'' ∧
      Curves.IsStableModification β'' φ D
        (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NoClosedExc.NumericallyStableFibre β'' φ
          (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) a := by
  have := halg (IsLocalRing.closedPoint V)
  have : IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)) :=
    IsAlgClosed.of_ringEquiv _ _
      (Scheme.Spec.residueFieldIso (CommRingCat.of V) _).commRingCatIsoToRingEquiv.symm
  have : LocallyOfFinitePresentation φ := Gluing.locallyOfFinitePresentation_of_flat φ
  exact BlowDown.exists_isStableModification_of_isSemistableStage φ D hloc hdesc hsep halg hdimC
    (contractingMorphismExists φ D hC hbridge) Y β hY

end Stable

end

end DeJongAlterations.StableModification.BlowDown.ContractingExists
