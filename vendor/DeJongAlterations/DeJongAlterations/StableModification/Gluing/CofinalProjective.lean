/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45C)
-/
import DeJongAlterations.StableModification.Gluing.CofinalProjectiveStage
import DeJongAlterations.StableModification.Gluing.SetupAssembly

/-!
# Projective cofinality of strictly semi-stable modifications (`PLAN-T5.md` node A4)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition
4.3.1 (`cofinprop`, T:2956–3017): strictly semi-stable modifications of a strictly semi-stable
curve over a valuation ring are cofinal among all modifications. Lane T43A proved it
(`LocalUniformization.exists_dominates_isStrictlySemistable_of_finite`, with lane T45A's finiteness
of `Γ₀` for all modifications, `Gluing.exists_dominates_isStrictlySemistable_of_isModification`)
without control of projectivity. This file reruns the induction of the proof with the invariant
"**the modification is projective** over a fixed `pE : C → Spec E`": each step is one of the two
stages of `Gluing.CofinalProjectiveStage`, which preserve projectivity (SERRE-I). For an affine
strictly semi-stable curve `C = Spec E → Spec R` this proves lane T45A's hypothesis
`Gluing.ProjectiveCofinality R` (`projectiveCofinality`).

## Main results

* `ProjCentreClaim`, `centreClaim_projective`: Temkin's claim (T:2961–2963) with projectivity;
* `exists_subset_gammaZeroSet_projective`, `exists_dominates_of_finite_gammaZeroSet_projective`:
  the iteration and the cofinality with projectivity;
* `exists_dominates_isStrictlySemistable_projective`: **projective cofinality** for an affine
  strictly semi-stable curve over a valuation ring of finite height with separably closed fraction
  field: every modification is dominated by a strictly semi-stable modification projective over
  the curve;
* `projectiveCofinality`: **`Gluing.ProjectiveCofinality R`**.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.Gluing.CofinalProjective

open ValCurves RiemannZariskiSpace Curves Blowups LocalUniformization Algebra.NodeBlowupChart
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section FinitePresentation

/-- **Finite presentation descends along a morphism of finite type between affine schemes**: if
`f ≫ g` is locally of finite presentation and `g : Spec A → Spec B` is locally of finite type, then
`f` is locally of finite presentation (EGA IV 1.4.3 (v), on affine charts
`RingHom.FinitePresentation.of_comp_finiteType`). -/
theorem locallyOfFinitePresentation_of_comp {X : Scheme.{u}} {A B : Type u} [CommRing A]
    [CommRing B] (f : X ⟶ Spec (.of A)) (g : Spec (.of A) ⟶ Spec (.of B))
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  have h₁ := HasRingHomProperty.appLE @LocallyOfFinitePresentation (f ≫ g) inferInstance
    ⟨⊤, isAffineOpen_top _⟩ V (by simp)
  have h₂ := HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance
    ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  have hcomp : g.appLE ⊤ U.1 (by simp) ≫ f.appLE U.1 V.1 e = (f ≫ g).appLE ⊤ V.1 (by simp) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← hcomp, CommRingCat.hom_comp] at h₁
  exact RingHom.FinitePresentation.of_comp_finiteType _ h₁ h₂

/-- A strictly semi-stable `f ≫ pE ≫ q` (`q` of finite type between affine schemes) makes `f ≫ pE`
of finite presentation. -/
theorem locallyOfFinitePresentation_of_isStrictlySemistable {C : Scheme.{u}} {E B : Type u}
    [CommRing E] [CommRing B] (φ : C ⟶ Spec (.of B)) (pE : C ⟶ Spec (.of E))
    (q : Spec (.of E) ⟶ Spec (.of B)) [LocallyOfFiniteType q] (hcq : pE ≫ q = φ) {Y : Scheme.{u}}
    (f : Y ⟶ C) (hf : IsStrictlySemistable (f ≫ φ) ⊤) :
    LocallyOfFinitePresentation (f ≫ pE) := by
  have : DeJong.IsNodalCurve (f ≫ φ) := hf.isNodalCurve
  have : LocallyOfFinitePresentation ((f ≫ pE) ≫ q) := by
    rw [Category.assoc, hcq]
    infer_instance
  exact locallyOfFinitePresentation_of_comp (f ≫ pE) q

end FinitePresentation

section Claim

/-- **Temkin's claim with projectivity** (T:2961–2963): for every strictly semi-stable modification
`f₁ : C₁ → C` with `C₁` projective over `Spec E` (through `pE : C → Spec E`) and every point
`V ∈ ⋃ Γ(C')` centred at a closed point `x₁` of `C₁`, there is a strictly semi-stable modification
`C₂ → C` dominating `C₁`, projective over `Spec E`, with `V ∈ Γ(C₂)`. -/
def ProjCentreClaim {S C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ S) {E : Type u} [CommRing E]
    (pE : C ⟶ Spec (.of E)) : Prop :=
  ∀ ⦃C₁ : Scheme.{u}⦄ [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁],
    IsStrictlySemistable (f₁ ≫ φ) ⊤ → IsProjectiveOver (f₁ ≫ pE) →
    ∀ (V : RiemannZariskiSpace C.functionField) (x₁ : C₁), V ∈ unionGammaSet φ →
      IsClosed ({x₁} : Set C₁) → IsCentre (genericLift f₁) V x₁ →
      ∃ (C₂ : Scheme.{u}) (_ : IsIntegral C₂) (f₂ : C₂ ⟶ C) (_ : IsModification f₂),
        (∃ g : C₂ ⟶ C₁, g ≫ f₁ = f₂) ∧ IsStrictlySemistable (f₂ ≫ φ) ⊤ ∧
          IsProjectiveOver (f₂ ≫ pE) ∧ V ∈ gammaSet (f₂ ≫ φ) (genericLift f₂)

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]

/-- **Temkin's claim in the proof of Proposition 4.3.1, with projectivity** (`lem:sm-cofinal-claim`
of lane T43A, `LocalUniformization.centreClaim`, rerun with the projective stages). -/
theorem centreClaim_projective {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated]
    (φ : C ⟶ Spec (.of O)) (hC : IsStrictlySemistable φ ⊤)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {E : Type u} [CommRing E] (pE : C ⟶ Spec (.of E))
    (q : Spec (.of E) ⟶ Spec (.of O)) [LocallyOfFiniteType q] (hcq : pE ≫ q = φ) :
    ProjCentreClaim φ pE := by
  intro C₁ _ f₁ _ hss₁ hpr₁ V x₁ hVG hcl hVx
  have hlfp : ∀ {Y : Scheme.{u}} (f : Y ⟶ C), IsStrictlySemistable (f ≫ φ) ⊤ →
      LocallyOfFinitePresentation (f ≫ pE) := fun f hf ↦
    locallyOfFinitePresentation_of_isStrictlySemistable φ pE q hcq f hf
  have : DeJong.IsNodalCurve φ := hC.isNodalCurve
  let := functionFieldAlgebra φ
  have hK := genericPt_comp φ
  have htr : Algebra.trdeg K C.functionField ≤ 1 := (trdeg_functionField_eq φ).le.trans hdim
  -- the valuation and the base `B = 𝒪_𝔵 ∩ K`
  set vL := V.valuationSubring.valuation
  have hVeq : rzOf vL = V := rzOf_eq V
  rw [← hVeq] at hVx hVG ⊢
  have hq₁ : genericLift f₁ ≫ f₁ ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  have hOB := le_of_isCentre vL (f₁ ≫ φ) hq₁ hVx
  have hidx := asIdeal_eq_idealOfLE vL (f₁ ≫ φ) hq₁ hVx
  have hx' : x₁ ∈ baseOpen O _ hOB (f₁ ≫ φ) := (mem_baseOpen_iff O _ hOB (f₁ ≫ φ)).mpr hidx.le
  have hxc : baseRestrict O _ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩ = closedPoint _ :=
    (baseRestrict_apply_eq_closedPoint_iff O _ hOB (f₁ ≫ φ) _).mpr (PrimeSpectrum.ext hidx)
  -- a transcendental residue, from `𝔵 ∈ Γ(C')`
  obtain ⟨C', _, f', _, y', hy'fib, hVy'⟩ := hVG
  have hq' : genericLift f' ≫ f' ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  obtain ⟨t, ht⟩ := exists_transcendental_residue vL (le_of_isCentre vL (f' ≫ φ) hq' hVy')
    (f' ≫ φ) hq' hVy' (asIdeal_eq_idealOfLE vL (f' ≫ φ) hq' hVy')
    (by rw [hy'fib]; exact one_ne_zero)
  -- if the centre is generic in its fibre there is nothing to do
  have hdone : ∀ {C₂ : Scheme.{u}} [IsIntegral C₂] (f₂ : C₂ ⟶ C) [IsModification f₂]
      (g : C₂ ⟶ C₁), g ≫ f₁ = f₂ → IsStrictlySemistable (f₂ ≫ φ) ⊤ →
      IsProjectiveOver (f₂ ≫ pE) → ∀ y₂,
      IsCentre (genericLift f₂) (rzOf vL) y₂ → fiberTrdeg (f₂ ≫ φ) y₂ = 1 →
      ∃ (C₃ : Scheme.{u}) (_ : IsIntegral C₃) (f₃ : C₃ ⟶ C) (_ : IsModification f₃),
        (∃ g : C₃ ⟶ C₁, g ≫ f₁ = f₃) ∧ IsStrictlySemistable (f₃ ≫ φ) ⊤ ∧
          IsProjectiveOver (f₃ ≫ pE) ∧ rzOf vL ∈ gammaSet (f₃ ≫ φ) (genericLift f₃) :=
    fun f₂ _ g hg hss₂ hpr₂ y₂ hV₂ hy₂ ↦
      ⟨_, inferInstance, f₂, inferInstance, ⟨g, hg⟩, hss₂, hpr₂, y₂, hy₂, hV₂⟩
  by_cases hgen : fiberTrdeg (f₁ ≫ φ) x₁ = 1
  · exact hdone f₁ (𝟙 _) (Category.id_comp _) hss₁ hpr₁ x₁ hVx hgen
  have h0 : fiberTrdeg (f₁ ≫ φ) x₁ = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f₁ x₁) hgen
  -- the smooth stage, for a smooth chart at a closed point of a strictly semi-stable modification
  have hsmooth : ∀ {C₂ : Scheme.{u}} [IsIntegral C₂] (f₂ : C₂ ⟶ C) [IsModification f₂]
      (g : C₂ ⟶ C₁), g ≫ f₁ = f₂ → IsStrictlySemistable (f₂ ≫ φ) ⊤ →
      IsProjectiveOver (f₂ ≫ pE) → ∀ {y₂ : C₂},
      IsClosed ({y₂} : Set C₂) → IsCentre (genericLift f₂) (rzOf vL) y₂ →
      fiberTrdeg (f₂ ≫ φ) y₂ = 0 → ∀ (hy : y₂ ∈ baseOpen O _ hOB (f₂ ≫ φ)),
      baseRestrict O _ hOB (f₂ ≫ φ) ⟨y₂, hy⟩ = closedPoint _ →
      HasSmoothChart (baseRestrict O _ hOB (f₂ ≫ φ)) ⟨y₂, hy⟩ →
      ∃ (C₃ : Scheme.{u}) (_ : IsIntegral C₃) (f₃ : C₃ ⟶ C) (_ : IsModification f₃),
        (∃ g : C₃ ⟶ C₁, g ≫ f₁ = f₃) ∧ IsStrictlySemistable (f₃ ≫ φ) ⊤ ∧
          IsProjectiveOver (f₃ ≫ pE) ∧ rzOf vL ∈ gammaSet (f₃ ≫ φ) (genericLift f₃) := by
    intro C₂ _ f₂ _ g hg hss₂ hpr₂ y₂ hcl₂ hV₂ h0₂ hy hyc hch
    obtain ⟨C₃, _, f₃, _, ⟨g', hg', hgp⟩, hss₃, hV₃⟩ :=
      exists_smoothStep_projective φ hK hdim vL htr ht hOB f₂ hss₂ hcl₂ hV₂ h0₂ hy hyc hch
    have hpr₃ : IsProjectiveOver (f₃ ≫ pE) := by
      rw [← hg', Category.assoc]
      exact hgp _ hpr₂ (hlfp f₂ hss₂)
    exact ⟨C₃, inferInstance, f₃, inferInstance, ⟨g' ≫ g, by rw [Category.assoc, hg, hg']⟩,
      hss₃, hpr₃, hV₃⟩
  -- a chart at `x₁` over `B`
  have hss₁' := isStrictlySemistable_baseRestrict O _ hOB (f₁ ≫ φ) hss₁
  obtain ⟨U, hxU, hcase⟩ := exists_chart hss₁' ⟨x₁, hx'⟩ hxc
  rcases hcase with ⟨e, he, hecomp⟩ | ⟨c, e, he, hecomp⟩
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hpr₁ hcl hVx h0 hx' hxc
      (hasSmoothChart_of_etale _ U e hecomp _ hxU)
  have hcoord : ∀ i : Fin 2, coordinate c i ∉ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal →
      HasSmoothChart (baseRestrict O _ hOB (f₁ ≫ φ)) ⟨x₁, hx'⟩ := fun i hi ↦
    hasSmoothChart_of_node (baseRestrict O _ hOB (f₁ ≫ φ)) U.ι c e hecomp ⟨⟨x₁, hx'⟩, hxU⟩ i hi
  by_cases hu : coordinate c 0 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal
  swap
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hpr₁ hcl hVx h0 hx' hxc (hcoord 0 hu)
  by_cases hv : coordinate c 1 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal
  swap
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hpr₁ hcl hVx h0 hx' hxc (hcoord 1 hv)
  -- the origin of a node chart: the node stage, then the smooth stage
  have : Nonempty (baseOpen O _ hOB (f₁ ≫ φ)).toScheme := ⟨⟨x₁, hx'⟩⟩
  have : IsIntegral (baseOpen O _ hOB (f₁ ≫ φ)).toScheme :=
    isIntegral_of_isOpenImmersion (baseOpen O _ hOB (f₁ ≫ φ)).ι
  have : Nonempty U.toScheme := ⟨⟨⟨x₁, hx'⟩, hxU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsDomain (U.toScheme.presheaf.stalk ⟨⟨x₁, hx'⟩, hxU⟩) :=
    AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral (X := U.toScheme)
  have hc : c ≠ 0 := node_param_ne_zero c e ⟨⟨x₁, hx'⟩, hxU⟩ hu hv
  obtain ⟨C₂, _, f₂, _, g, _, hg, hgp, hss₂, y₂, hV₂, hgy₂, hy₂, hch⟩ :=
    exists_nodeStep_projective φ hK vL htr ht hOB f₁ hss₁ hcl hVx hx' hxc U hxU hc e hecomp hu hv
  have hpr₂ : IsProjectiveOver (f₂ ≫ pE) := by
    rw [← hg, Category.assoc]
    exact hgp _ hpr₁ (hlfp f₁ hss₁)
  have : IsSeparated (f₂ ≫ φ) := inferInstance
  by_cases hgen₂ : fiberTrdeg (f₂ ≫ φ) y₂ = 1
  · exact hdone f₂ g hg hss₂ hpr₂ y₂ hV₂ hgen₂
  have hdim₁ : fiberTrdeg (f₁ ≫ φ) (genericPoint C₁) ≤ 1 := fiberTrdeg_le_one φ hdim f₁ _
  have hcl₂ : IsClosed ({y₂} : Set C₂) := by
    rcases mem_fibreGenericSet_or_isClosed (φ := f₁ ≫ φ) hdim₁ g (x₁ := y₂)
        (by rw [hgy₂]; exact hcl) with h | h
    · exfalso
      apply hgen₂
      have h' : fiberTrdeg (g ≫ f₁ ≫ φ) y₂ = 1 := h
      rwa [← Category.assoc, hg] at h'
    · exact h
  have h0₂ : fiberTrdeg (f₂ ≫ φ) y₂ = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f₂ y₂) hgen₂
  have hyc : baseRestrict O _ hOB (f₂ ≫ φ) ⟨y₂, hy₂⟩ = closedPoint _ := by
    rw [baseRestrict_apply_eq_closedPoint_iff]
    change (f₂ ≫ φ) y₂ = _
    rw [← hg, Category.assoc, Scheme.Hom.comp_apply, hgy₂]
    exact (baseRestrict_apply_eq_closedPoint_iff O _ hOB (f₁ ≫ φ) _).mp hxc
  exact hsmooth f₂ g hg hss₂ hpr₂ hcl₂ hV₂ h0₂ hy₂ hyc hch


end Claim

section Iteration

variable {S C : Scheme.{u}} {φ : C ⟶ S} [IsIntegral C]
  [∀ s : S, PreValuationRing (S.presheaf.stalk s)]
  {E : Type u} [CommRing E] (pE : C ⟶ Spec (.of E))

/-- **The iteration with projectivity** (Temkin, T:2963–2966;
`LocalUniformization.exists_subset_gammaZeroSet` with the invariant "projective over `Spec E`"). -/
theorem exists_subset_gammaZeroSet_projective (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (hC : IsStrictlySemistable φ ⊤) (hpE : IsProjectiveOver (𝟙 C ≫ pE))
    (hclaim : ProjCentreClaim φ pE)
    {F : Set (RiemannZariskiSpace C.functionField)} (hF : F.Finite)
    (hFsub : ∀ V ∈ F, V ∈ unionGammaSet φ ∧
      ∃ x : C, IsClosed ({x} : Set C) ∧ IsCentre (genericPt C) V x) :
    ∃ (C₁ : Scheme.{u}) (_ : IsIntegral C₁) (f₁ : C₁ ⟶ C) (_ : IsModification f₁),
      IsStrictlySemistable (f₁ ≫ φ) ⊤ ∧ IsProjectiveOver (f₁ ≫ pE) ∧
        F ⊆ gammaZeroSet (f₁ ≫ φ) (genericLift f₁) (genericPt C) := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    exact ⟨C, inferInstance, 𝟙 C, inferInstance, by rwa [Category.id_comp], hpE,
      Set.empty_subset _⟩
  | @insert V F _ _ ih =>
    obtain ⟨C₁, _, f₁, _, hss₁, hpr₁, hF₁⟩ :=
      ih fun W hW ↦ hFsub W (Set.mem_insert_of_mem V hW)
    obtain ⟨hVG, x, hxcl, hVx⟩ := hFsub V (Set.mem_insert V F)
    obtain ⟨x₁, hV₁, hx₁⟩ := hVx.exists_of_universallyClosed f₁ (genericLift_comp f₁)
    rcases mem_fibreGenericSet_or_isClosed hdim f₁ (x₁ := x₁) (hx₁ ▸ hxcl) with hgen | hcl
    · refine ⟨C₁, inferInstance, f₁, inferInstance, hss₁, hpr₁, Set.insert_subset ?_ hF₁⟩
      exact ⟨⟨x₁, hgen, hV₁⟩, x, hxcl, hVx⟩
    · obtain ⟨C₂, _, f₂, _, ⟨g, hg⟩, hss₂, hpr₂, hV₂⟩ := hclaim f₁ hss₁ hpr₁ V x₁ hVG hcl hV₁
      refine ⟨C₂, inferInstance, f₂, inferInstance, hss₂, hpr₂,
        Set.insert_subset ⟨hV₂, x, hxcl, hVx⟩
          (hF₁.trans (gammaZeroSet_subset_of_dominates hdim f₁ f₂ g hg))⟩

/-- **Cofinality with projectivity** (Temkin, Proposition 4.3.1, T:2961–2966): every modification
`C' → C` with `Γ₀(C')` finite is dominated by a strictly semi-stable modification of `C` which is
projective over `Spec E`. -/
theorem exists_dominates_of_finite_gammaZeroSet_projective [CompactSpace C] [C.IsSeparated]
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (hC : IsStrictlySemistable φ ⊤)
    (hnormal : ∀ ⦃C₁ : Scheme.{u}⦄ [IsIntegral C₁] (f₁ : C₁ ⟶ C) [IsModification f₁],
      IsStrictlySemistable (f₁ ≫ φ) ⊤ → IsNormalScheme C₁)
    (hpE : IsProjectiveOver (𝟙 C ≫ pE)) (hclaim : ProjCentreClaim φ pE) {C' : Scheme.{u}}
    [IsIntegral C'] (f' : C' ⟶ C) [IsModification f']
    (hfin : (gammaZeroSet (f' ≫ φ) (genericLift f') (genericPt C)).Finite) :
    ∃ (C'' : Scheme.{u}) (_ : IsIntegral C'') (f'' : C'' ⟶ C) (_ : IsModification f''),
      IsStrictlySemistable (f'' ≫ φ) ⊤ ∧ IsProjectiveOver (f'' ≫ pE) ∧
        ∃ g : C'' ⟶ C', g ≫ f' = f'' := by
  obtain ⟨C₁, _, f₁, _, hss₁, hpr₁, hsub⟩ := exists_subset_gammaZeroSet_projective pE hdim hC hpE
    hclaim hfin fun V hV ↦ ⟨mem_unionGammaSet_of_mem_gammaZeroSet φ f' hV, hV.2⟩
  exact ⟨C₁, inferInstance, f₁, inferInstance, hss₁, hpr₁,
    dominates_of_gammaZeroSet_subset φ f' f₁ (hnormal f₁ hss₁) hdim hsub⟩

end Iteration

section Affine

/-- A scheme projective over `Spec E` is projective relative to every `Spec E → Spec R`. -/
theorem isRelativelyProjective_of_isProjectiveOver_spec {R E : Type u} [CommRing R] [CommRing E]
    (ψ : Spec (.of E) ⟶ Spec (.of R)) {X : Scheme.{u}} (f : X ⟶ Spec (.of E))
    (hf : IsProjectiveOver f) : DeJong.IsRelativelyProjective ψ f := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R →+* E, ψ = Spec.map (CommRingCat.ofHom ρ) :=
    ⟨(Spec.preimage ψ).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  obtain ⟨n, j, hj, hjf⟩ := hf
  have := hj
  let e := Geometry.ProjectiveSpaceBaseChange.projectiveSpaceBaseChangeIso ρ n
  refine ⟨n, j ≫ e.hom ≫ (pullbackSymmetry _ _).hom, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst,
    Geometry.ProjectiveSpaceBaseChange.projectiveSpaceBaseChangeIso_hom_snd, hjf]

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]

/-- **Projective cofinality** (`PLAN-T5.md` node A4; Temkin, Proposition 4.3.1 with the
projectivity of the output): let `O` be a valuation ring of finite height with separably closed
fraction field and `ψ : Spec E → Spec O` an affine integral strictly semi-stable relative curve.
Every modification `h : W → Spec E` is dominated by a strictly semi-stable modification
`f : B → Spec E` which is **projective over `E`**. -/
theorem exists_dominates_isStrictlySemistable_projective {E : Type u} [CommRing E] [IsDomain E]
    (ψ : Spec (.of E) ⟶ Spec (.of O)) (hC : IsStrictlySemistable ψ ⊤)
    (hdim : fiberTrdeg ψ (genericPoint (Spec (.of E))) ≤ 1) {W : Scheme.{u}}
    (h : W ⟶ Spec (.of E)) [IsModification h] :
    ∃ (B : Scheme.{u}) (_ : IsIntegral B) (f : B ⟶ Spec (.of E)) (_ : IsModification f),
      IsStrictlySemistable (f ≫ ψ) ⊤ ∧ IsProjectiveOver f ∧ ∃ q : B ⟶ W, q ≫ h = f := by
  have hW : IsModification h := inferInstance
  have := hW.sourceIntegral
  have : DeJong.IsNodalCurve ψ := hC.isNodalCurve
  have : CompactSpace (Spec (.of E)) := inferInstanceAs (CompactSpace (PrimeSpectrum E))
  have : QuasiCompact ψ := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹_›
  have hpE : IsProjectiveOver (𝟙 (Spec (.of E)) ≫ 𝟙 (Spec (.of E))) := by
    rw [Category.comp_id]
    exact (DeJong.isRelativelyProjective_id_iff _).mp
      (DeJong.isRelativelyProjective_of_isClosedImmersion _ _)
  have hclaim := centreClaim_projective ψ hC hdim (𝟙 _) ψ (Category.id_comp ψ)
  obtain ⟨B, _, f, _, hss, hpr, q, hq⟩ :=
    exists_dominates_of_finite_gammaZeroSet_projective (𝟙 _) hdim hC
      (fun _ _ _ _ hss ↦ isNormalScheme_of_isStrictlySemistable_spec hss) hpE hclaim h
      (finite_gammaZeroSet_of_flat ψ hdim h)
  rw [Category.comp_id] at hpr
  exact ⟨B, inferInstance, f, inferInstance, hss, hpr, q, hq⟩

/-- **Lane T45A's hypothesis `ProjectiveCofinality R` holds** (`PLAN-T5.md` node A4) for every
valuation ring `R` of finite height with separably closed fraction field. -/
theorem projectiveCofinality (R : ValuationSubring K) [Finite (PrimeSpectrum R)] :
    ProjectiveCofinality R := by
  intro E _ _ ψ hss htr W h hh
  obtain ⟨B, hB, f, hf, hssf, hpr, q, hq⟩ :=
    exists_dominates_isStrictlySemistable_projective ψ hss htr.le h
  exact ⟨B, hB, f, hf, hssf, isRelativelyProjective_of_isProjectiveOver_spec ψ f hpr, q, hq⟩

end Affine

end DeJongAlterations.StableModification.Gluing.CofinalProjective
