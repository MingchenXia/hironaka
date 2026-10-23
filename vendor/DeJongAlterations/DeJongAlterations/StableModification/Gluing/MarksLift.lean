/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45B)
-/
import DeJongAlterations.StableModification.Gluing.MarksGeneric
import DeJongAlterations.StableModification.Gluing.SetupAssembly
import DeJongAlterations.StableModification.BlowDown.StabilityTop
import DeJongAlterations.StableModification.ValCurves.ModificationsFiniteness

/-!
# Lifting the marks along modifications

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010): every
modification of a relative curve `C → S = Spec V` whose generic fibre is normal is an isomorphism
over the generic fibre (a normal curve over a field has no nontrivial modification), so the
sections of `C → S` through the marks lift uniquely to every modification (`PLAN-T5.md` §2.2,
node V2; used for the transported marks `D'`, Temkin Remark 4.1, T:2810).

* `topologicalKrullDim_fiber_le_one_of_fiberTrdeg`: the fibres of an integral relative curve
  (`trdeg κ(ξ)/κ(φ ξ) ≤ 1`) over a valuation ring have dimension at most one (the strict dimension
  inequality along specializations in a fibre, `ValCurves.one_add_fiberTrdeg_le_of_specializes`);
* `isIso_restrict_genericOpen`: a modification of `C` is an isomorphism over the generic fibre
  if `C` is normal along it (Codex's `Geometry.NormalCurveModification.isIso_of_isModification`;
  this is the argument of lane T45A's `Gluing.isEtaModification_of_isNodalCurve`, with the
  dimension bound from the transcendence degree instead of a nodal source);
* `exists_lift_section`, `lift_section_unique`: sections lift uniquely along modifications;
* `fiberTrdeg_section_apply`: the points of a section are algebraic over the base.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.StableVal

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false

section Dimension

variable {S C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ S)
  [∀ s : S, PreValuationRing (S.presheaf.stalk s)]

/-- **The fibres of a relative curve have dimension at most one.** If the generic point of the
integral `C` has transcendence degree at most one over its image in `S` (the local rings of `S`
being valuation rings), every fibre of `φ` has Krull dimension at most one: a chain `b ⤳ x ⤳ a`
of proper specializations in a fibre would give `2 ≤ trdeg κ(b) ≤ 1`. -/
theorem topologicalKrullDim_fiber_le_one_of_fiberTrdeg
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (s : S) :
    topologicalKrullDim (φ.fiber s) ≤ 1 := by
  rw [BlowDown.topologicalKrullDim_le_one_iff_specializes]
  intro x
  by_contra hx
  push Not at hx
  obtain ⟨⟨a, hxa, hax⟩, ⟨b, hbx, hxb⟩⟩ := hx
  have hemb : Topology.IsEmbedding (φ.fiberι s) := (φ.fiberι s).isEmbedding
  have hne₁ : φ.fiberι s b ≠ φ.fiberι s x := fun h ↦ hxb (by rw [hemb.injective h])
  have hne₂ : φ.fiberι s x ≠ φ.fiberι s a := fun h ↦ hax (by rw [hemb.injective h])
  have hfib : ∀ y : φ.fiber s, φ (φ.fiberι s y) = s := fun y ↦ by
    have : φ.fiberι s y ∈ Set.range (φ.fiberι s) := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have h₁ := ValCurves.one_add_fiberTrdeg_le_of_specializes φ
    (hbx.map (φ.fiberι s).continuous) hne₁ (by rw [hfib, hfib])
  have h₂ := ValCurves.one_add_fiberTrdeg_le_of_specializes φ
    (hxa.map (φ.fiberι s).continuous) hne₂ (by rw [hfib, hfib])
  have h₃ := (ValCurves.fiberTrdeg_le_genericPoint φ (φ.fiberι s b)).trans hdim
  have : (1 : Cardinal) + (1 + fiberTrdeg φ (φ.fiberι s a)) ≤ 1 :=
    ((add_le_add (le_refl 1) h₂).trans h₁).trans h₃
  have h2 : (2 : Cardinal) ≤ 1 := by
    calc (2 : Cardinal) = 1 + 1 := one_add_one_eq_two.symm
      _ ≤ 1 + (1 + fiberTrdeg φ (φ.fiberι s a)) := add_le_add (le_refl 1) le_self_add
      _ ≤ 1 := this
  exact absurd h2 (by norm_num)

end Dimension

section Generic

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of V)) [Flat φ] [LocallyOfFiniteType φ]

/-- **Modifications are isomorphisms over a normal generic fibre** (Temkin T:2243; cf. lane
T45A's `Gluing.isEtaModification_of_isNodalCurve`). If `C` is normal at the points over the
generic point of `Spec V` and of relative dimension at most one, every modification `β : X → C`
is an isomorphism over the generic fibre `C_η = φ⁻¹(η)`. -/
theorem isIso_restrict_genericOpen
    (hnorm : ∀ x : C, φ x = genericPoint (Spec (.of V)) →
      IsIntegrallyClosed (C.presheaf.stalk x))
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {X : Scheme.{u}} (β : X ⟶ C)
    [IsModification β] : IsIso (β ∣_ (φ ⁻¹ᵁ BlowDown.genericOpen V)) := by
  have hβ : IsModification β := inferInstance
  have := hβ.sourceIntegral
  set U := φ ⁻¹ᵁ BlowDown.genericOpen V
  have hgen : φ (genericPoint C) = genericPoint (Spec (.of V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact apply_genericPoint_eq_bot_of_flat φ
  have hξU : genericPoint C ∈ U := hgen
  have : Nonempty U := ⟨⟨_, hξU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  -- `C_η` is normal
  have hUn : IsNormalScheme U.toScheme := by
    intro y
    have hy : φ (U.ι y) = genericPoint (Spec (.of V)) := y.2
    have : IsIntegrallyClosed (C.presheaf.stalk (U.ι y)) := hnorm _ hy
    let e := asIso (U.ι.stalkMap y)
    exact ⟨e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain,
      IsIntegrallyClosed.of_equiv e.commRingCatIsoToRingEquiv⟩
  -- `C_η` is locally Noetherian
  have := isLocallyNoetherian_genericOpen (V := V)
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (φ ∣_ _)
  -- `C_η` has dimension at most one
  have hdimF := topologicalKrullDim_fiber_le_one_of_fiberTrdeg φ hdim
    (genericPoint (Spec (.of V)))
  have hset : (U : Set C) = φ ⁻¹' {genericPoint (Spec (.of V))} := by
    change φ ⁻¹' (BlowDown.genericOpen V : Set (Spec (.of V))) = _
    rw [BlowDown.coe_genericOpen]
  let h₁ : U.toScheme ≃ₜ φ.fiber (genericPoint (Spec (.of V))) :=
    (Homeomorph.setCongr hset).trans (φ.fiberHomeo _).symm
  have hdimU : topologicalKrullDim U.toScheme ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq h₁ h₁.isHomeomorph]
    exact hdimF
  have := Geometry.CurveCompactification.isModification_morphismRestrict β U
  exact Geometry.NormalCurveModification.isIso_of_isModification _ hUn hdimU

omit [IsIntegral C] [Flat φ] [LocallyOfFiniteType φ] in
/-- A section of `φ` has its generic point over the generic open. -/
theorem apply_genericPoint_mem_genericOpen (σ : Spec (.of V) ⟶ C) (hσ : σ ≫ φ = 𝟙 _) :
    σ (genericPoint (Spec (.of V))) ∈ φ ⁻¹ᵁ BlowDown.genericOpen V := by
  change φ (σ _) ∈ (BlowDown.genericOpen V : Set _)
  rw [← Scheme.Hom.comp_apply, hσ, BlowDown.coe_genericOpen]
  rfl

/-- **Sections lift to modifications** of a relative curve with normal generic fibre. -/
theorem exists_lift_section
    (hnorm : ∀ x : C, φ x = genericPoint (Spec (.of V)) →
      IsIntegrallyClosed (C.presheaf.stalk x))
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {X : Scheme.{u}} (β : X ⟶ C)
    [IsModification β] (σ : Spec (.of V) ⟶ C) (hσ : σ ≫ φ = 𝟙 _) :
    ∃ σ' : Spec (.of V) ⟶ X, σ' ≫ β = σ := by
  have := isIso_restrict_genericOpen φ hnorm hdim β
  exact exists_lift_of_isIso β _ σ (apply_genericPoint_mem_genericOpen φ σ hσ)

/-- **Lifts of sections to modifications are unique.** -/
theorem lift_section_unique
    (hnorm : ∀ x : C, φ x = genericPoint (Spec (.of V)) →
      IsIntegrallyClosed (C.presheaf.stalk x))
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {X : Scheme.{u}} (β : X ⟶ C)
    [IsModification β] (σ₁ σ₂ : Spec (.of V) ⟶ X) (h : σ₁ ≫ β = σ₂ ≫ β)
    (hσ : (σ₁ ≫ β) ≫ φ = 𝟙 _) : σ₁ = σ₂ := by
  have := isIso_restrict_genericOpen φ hnorm hdim β
  exact lift_unique_of_isIso β _ σ₁ σ₂ h (apply_genericPoint_mem_genericOpen φ _ hσ)

end Generic

section Algebraic

variable {S X : Scheme.{u}} (φ : X ⟶ S)

/-- **The points of a section are algebraic over the base**: `κ(σ t) ≅ κ(t)`. -/
theorem isAlgebraicAt_section_apply (σ : S ⟶ X) (hσ : σ ≫ φ = 𝟙 _) (t : S) :
    ValCurves.IsAlgebraicAt φ (σ t) := by
  have e := Scheme.residueFieldMap_comp σ φ t
  have : IsOpenImmersion (σ ≫ φ) := by rw [hσ]; infer_instance
  -- `a ≫ b` is an isomorphism, with `a = φ.residueFieldMap (σ t)`, `b = σ.residueFieldMap t`
  set a := φ.residueFieldMap (σ t)
  set b := σ.residueFieldMap t
  have hab : Function.Bijective (a ≫ b).hom := by
    rw [← e]
    exact ConcreteCategory.bijective_of_isIso _
  have hb : Function.Injective b.hom := b.hom.injective
  have hbs : Function.Surjective b.hom := by
    intro y
    obtain ⟨z, hz⟩ := hab.2 y
    exact ⟨a.hom z, hz⟩
  have has : Function.Surjective a.hom := by
    intro y
    obtain ⟨z, hz⟩ := hab.2 (b.hom y)
    exact ⟨z, hb hz⟩
  intro y
  obtain ⟨z, rfl⟩ := has y
  exact RingHom.isIntegralElem_map a.hom

/-- The points of a section have transcendence degree zero. -/
theorem fiberTrdeg_section_apply (σ : S ⟶ X) (hσ : σ ≫ φ = 𝟙 _) (t : S) :
    fiberTrdeg φ (σ t) = 0 :=
  (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero φ _).mp (isAlgebraicAt_section_apply φ σ hσ t)

end Algebraic

end DeJongAlterations.StableModification.Gluing.StableVal
