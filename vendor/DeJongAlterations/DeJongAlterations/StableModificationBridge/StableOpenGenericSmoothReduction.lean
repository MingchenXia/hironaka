/-
Copyright (c) 2026 Mingchen Xia and DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableOpenGenericSmoothConsumer
import DeJongAlterations.StableModificationBridge.StableOpenGenericSmoothBaseChange

/-! Actual normalization-component and native field-open descent for the PRECISE
smooth-generic stability gate used by the main theorem. Blueprint:
`stable-open-generic-smooth-reduction.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace DeJongAlterations.StableModification.Global
universe u
open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap)
open Geometry.NormalizationGluing (normalization normalizationStructure normalization_isNormalScheme)
open BlowDown.ClosureComponent (closureScheme closureι range_closureι)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ONLY remaining normal-rational producer, for a native SMOOTH generic fibre.
This is an honest mathematical prerequisite, never an asserted axiom or output certificate. -/
def StableOpenNbhdRationalGenericSmooth (K : Type u) [Field K] [IsAlgClosed K] : Prop :=
  ∀ (V : Scheme.{u}) (pV : V ⟶ Spec (.of K)) (hV : IsVariety pV),
    letI : IsVariety pV := hV
    IsNormalScheme V →
    ∀ (C : Scheme.{u}) (q : C ⟶ V), IsRelativelyProjective pV q →
    ∀ (X : Scheme.{u}) (β : X ⟶ C), IsRelativelyProjective (q ≫ pV) β →
    ∀ (D' : X.IdealSheafData), IsSemistablePair (β ≫ q) D' →
      Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint V)) →
    ∀ (a : Spec (.of K) ⟶ V), a ≫ pV = 𝟙 _ →
      NumericallyStableFibre β q D' a → NoContractedClopen β q a →
      ∃ O : V.Opens, a (IsLocalRing.closedPoint K) ∈ O ∧
        ∀ z' ∈ O, IsNumericallyStableAt β q D' z'

section Rational
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Actual canonical normalization, original rational lifts and WHOLE fibre squares
preserve the genuinely supplied smooth original component generic fibre. -/
theorem exists_open_normalization_genericSmooth (hR : StableOpenNbhdRationalGenericSmooth K) {Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of K)) [IsSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    {C : Scheme.{u}} (q : C ⟶ Y) (hq : IsRelativelyProjective pY q)
    {X : Scheme.{u}} (β : X ⟶ C) (hβ : IsRelativelyProjective (q ≫ pY) β)
    (D' : X.IdealSheafData) (hss : IsSemistablePair (β ≫ q) D')
    (σ : Spec (.of K) ⟶ Y) (hσ : σ ≫ pY = 𝟙 _)
    (hst : NumericallyStableFibre β q D' σ) (hnc : NoContractedClopen β q σ) (v : Y)
    (hsmv : Smooth ((β ≫ q).fiberToSpecResidueField v)) :
    ∃ O : (normalization (closureScheme v)).Opens,
      (∀ w, (normalizationStructure (closureScheme v) ≫ closureι v) w =
        σ (IsLocalRing.closedPoint K) → w ∈ O) ∧
      ∀ w ∈ O, IsNumericallyStableAt β q D'
        ((normalizationStructure (closureScheme v) ≫ closureι v) w) := by
  set N := normalization (closureScheme v)
  set ν : N ⟶ Y := normalizationStructure (closureScheme v) ≫ closureι v with hν
  set y₀ := σ (IsLocalRing.closedPoint K)
  have : IsProper q := hq.isProper
  have : IsProper β := hβ.isProper
  have : IsFinite ν := isFinite_normalization_closure pY v
  have hvar : IsVariety (ν ≫ pY) := isVariety_normalization_closure pY v
  have hnorm : IsNormalScheme N := normalization_isNormalScheme _
  -- the family over `N`
  have hqN : IsRelativelyProjective (ν ≫ pY) (pullback.snd q ν) := hq.pullback_snd ν
  have hβN : IsRelativelyProjective (pullback.snd q ν ≫ ν ≫ pY) (pullbackCompMap β q ν) :=
    isRelativelyProjective_pullbackCompMap hβ ν
  have hssN : IsSemistablePair (pullbackCompMap β q ν ≫ pullback.snd q ν)
      (D'.comap (pullback.fst (β ≫ q) ν)) := by
    rw [Curves.pullbackCompMap_snd]
    exact Curves.IsSemistablePair.pullback hss ν
  have hνgen : ν (genericPoint N) = v :=
    StableModificationBridge.StableOpenGenericSmoothBaseChange.normalization_genericPoint_image v
  have hsmN : Smooth ((pullbackCompMap β q ν ≫ pullback.snd q ν).fiberToSpecResidueField
      (genericPoint N)) := by
    rw [Curves.pullbackCompMap_snd]
    have hsm := hsmv
    rw [← hνgen] at hsm
    exact MorphismProperty.of_isPullback (P := @Smooth)
      (isPullback_fiber_pullback_snd (β ≫ q) ν (genericPoint N)) hsm
  -- the largest open of `N` over which `(q, β, D')` is numerically stable
  let P : N → Prop := fun w ↦ IsNumericallyStableAt β q D' (ν w)
  let O : N.Opens := ⟨{w | ∃ O' : N.Opens, w ∈ O' ∧ ∀ w' ∈ O', P w'},
    isOpen_iff_forall_mem_open.mpr fun w ⟨O', hw, hO'⟩ ↦
      ⟨O', fun w'' hw'' ↦ ⟨O', hw'', hO'⟩, O'.isOpen, hw⟩⟩
  refine ⟨O, fun w hw ↦ ?_, fun w ⟨O', hw, hO'⟩ ↦ hO' w hw⟩
  -- `w` is a closed point
  have : JacobsonSpace N := LocallyOfFiniteType.jacobsonSpace (ν ≫ pY)
  have hy₀ : IsClosed ({y₀} : Set Y) := ((pointEquivClosedPoint pY) ⟨σ, hσ⟩).2
  have hwc : IsClosed ({w} : Set N) := by
    have hfin := ν.finite_preimage_singleton y₀
    have hsub : closure {w} ⊆ ν ⁻¹' {y₀} := by
      intro w' hw'
      have h1 : ν w ⤳ ν w' := (specializes_iff_mem_closure.mpr hw').map ν.continuous
      rw [hw] at h1
      have h2 := specializes_iff_mem_closure.mp h1
      rw [hy₀.closure_eq] at h2
      exact h2
    exact isClosed_singleton_of_finite isClosed_closure (hfin.subset hsub) (subset_closure rfl)
  -- the `K`-point at `w`, lying over `σ`
  let σw := pointOfClosedPoint (ν ≫ pY) w hwc
  have hσw : σw ≫ ν ≫ pY = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hσwpt : σw (IsLocalRing.closedPoint K) = w := pointOfClosedPoint_apply _ _ _ _
  have hσwν : σw ≫ ν = σ := by
    refine ext_of_apply_closedPoint_eq pY (by rw [Category.assoc]; exact hσw) hσ ?_
    change ν (σw (IsLocalRing.closedPoint K)) = _
    rw [hσwpt]
    exact hw
  have hstN : NumericallyStableFibre (pullbackCompMap β q ν) (pullback.snd q ν)
      (D'.comap (pullback.fst (β ≫ q) ν)) σw := by
    rw [numericallyStableFibre_pullback_iff, hσwν]
    exact hst
  have hncN : NoContractedClopen (pullbackCompMap β q ν) (pullback.snd q ν) σw := by
    rw [noContractedClopen_pullback_iff, hσwν]
    exact hnc
  -- the ω step at `σw`
  obtain ⟨Ow, hwOw, hOw⟩ := hR N (ν ≫ pY) hvar hnorm _ (pullback.snd q ν) hqN _
    (pullbackCompMap β q ν) hβN _ hssN hsmN σw hσw hstN hncN
  refine ⟨Ow, ?_, fun w' hw' ↦ isNumericallyStableAt_of_pullback ν (hOw w' hw')⟩
  rwa [hσwpt] at hwOw

/-- The actual finite family of SAME canonical component normalizations produces
an original open stability neighborhood, retaining reducible/nonreduced bases. -/
theorem exists_open_of_stableOpenNbhdRational_genericSmooth
    (hR : StableOpenNbhdRationalGenericSmooth K) {Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of K)) [IsSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    {C : Scheme.{u}} (q : C ⟶ Y) (hq : IsRelativelyProjective pY q)
    {X : Scheme.{u}} (β : X ⟶ C) (hβ : IsRelativelyProjective (q ≫ pY) β)
    (D' : X.IdealSheafData) (hss : IsSemistablePair (β ≫ q) D')
    (hsm : ∀ v ∈ genericPoints Y, Smooth ((β ≫ q).fiberToSpecResidueField v))
    (σ : Spec (.of K) ⟶ Y) (hσ : σ ≫ pY = 𝟙 _)
    (hst : NumericallyStableFibre β q D' σ) (hnc : NoContractedClopen β q σ) :
    ∃ O : Y.Opens, σ (IsLocalRing.closedPoint K) ∈ O ∧
      ∀ y ∈ O, IsNumericallyStableAt β q D' y := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : CompactSpace Y := BlowDown.compactSpace_of_quasiCompact pY
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  have : Finite (genericPoints Y) := CurvesField.Genus.finite_genericPoints pY
  choose Ov hOv₁ hOv₂ using fun v : genericPoints Y =>
    exists_open_normalization_genericSmooth hR pY q hq β hβ D' hss σ hσ hst hnc v.1 (hsm v.1 v.2)
  let y₀ := σ (IsLocalRing.closedPoint K)
  let F : genericPoints Y → Set Y := fun v =>
    (normalizationStructure (closureScheme v.1) ≫ closureι v.1) '' ((Ov v : Set _)ᶜ)
  have hFcl : ∀ v, IsClosed (F v) := fun v => by
    have : IsFinite (normalizationStructure (closureScheme v.1) ≫ closureι v.1) :=
      isFinite_normalization_closure pY v.1
    exact Scheme.Hom.isClosedMap _ _ (Ov v).isOpen.isClosed_compl
  have hy₀F : ∀ v, y₀ ∉ F v := by
    rintro v ⟨w, hw, hwy⟩
    exact hw (hOv₁ v w hwy)
  have hBad : IsClosed (⋃ v, F v) := isClosed_iUnion_of_finite hFcl
  refine ⟨⟨(⋃ v, F v)ᶜ, hBad.isOpen_compl⟩, ?_, fun y hy => ?_⟩
  · change y₀ ∉ ⋃ v, F v
    intro h
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
    exact hy₀F v hv
  · have hy' : y ∉ ⋃ v, F v := hy
    obtain ⟨T, hT, hyT⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
    obtain ⟨v, hv⟩ := QuasiSober.sober hT.1 (isClosed_of_mem_irreducibleComponents T hT)
    have hvT : closure {v} = T := hv
    have hvG : v ∈ genericPoints Y := by
      change closure {v} ∈ irreducibleComponents Y
      rw [hvT]
      exact hT
    have hyv : y ∈ Set.range (normalizationStructure (closureScheme v) ≫ closureι v) := by
      rw [range_normalization_closure pY v, hvT]
      exact hyT rfl
    obtain ⟨w, rfl⟩ := hyv
    by_cases hw : w ∈ Ov ⟨v, hvG⟩
    · exact hOv₂ ⟨v, hvG⟩ w hw
    · exfalso
      apply hy'
      exact Set.mem_iUnion.mpr ⟨⟨v, hvG⟩, w, hw, rfl⟩

end Rational

/-- Original field base change is flat/universally open. Every original component
smoothness premise on the reducible scalar base is DERIVED, and the actual stable
open descends along the SAME original projection. -/
theorem stableOpenNbhdConnGenericSmooth_of_rational (k : Type u) [Field k]
    (hR : ∀ (K : Type u) [Field K] [IsAlgClosed K], StableOpenNbhdRationalGenericSmooth K) :
    StableOpenNbhdConnGenericSmooth k := by
  intro U pU hU
  let : IsVariety pU := hU
  intro C q hq X β hβ D' hss hsm z K _ _ a ha hst hnc
  have : IsProper q := hq.isProper
  have : IsProper β := hβ.isProper
  let κ : CommRingCat.of k ⟶ CommRingCat.of K := Spec.preimage (a ≫ pU)
  have hκ : Spec.map κ = a ≫ pU := Spec.map_preimage _
  let p : pullback pU (Spec.map κ) ⟶ U := pullback.fst pU (Spec.map κ)
  let pK : pullback pU (Spec.map κ) ⟶ Spec (.of K) := pullback.snd pU (Spec.map κ)
  let σ : Spec (.of K) ⟶ pullback pU (Spec.map κ) :=
    pullback.lift a (𝟙 _) (by rw [Category.id_comp, hκ])
  have hσp : σ ≫ p = a := pullback.lift_fst _ _ _
  have hσK : σ ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  have hcond : p ≫ pU = pK ≫ Spec.map (CommRingCat.ofHom κ.hom) := by
    rw [CommRingCat.ofHom_hom]
    exact pullback.condition
  -- the family over `U_K`
  have hqK : IsRelativelyProjective pK (pullback.snd q p) := by
    have h1 := hq.pullback_snd p
    rw [hcond] at h1
    exact (Projectivity.isRelativelyProjective_comp_specMap_iff κ.hom pK _).mp h1
  have hβK : IsRelativelyProjective (pullback.snd q p ≫ pK) (pullbackCompMap β q p) := by
    have h1 := isRelativelyProjective_pullbackCompMap hβ p
    rw [hcond, ← Category.assoc] at h1
    exact (Projectivity.isRelativelyProjective_comp_specMap_iff κ.hom _ _).mp h1
  have hssK : IsSemistablePair (pullbackCompMap β q p ≫ pullback.snd q p)
      (D'.comap (pullback.fst (β ≫ q) p)) := by
    rw [Curves.pullbackCompMap_snd]
    exact Curves.IsSemistablePair.pullback hss p
  have : Flat p := inferInstance
  have hsmK : ∀ v ∈ genericPoints (pullback (C := Scheme.{u}) pU (Spec.map κ)),
      Smooth ((pullbackCompMap β q p ≫ pullback.snd q p).fiberToSpecResidueField v) := by
    intro v hv
    rw [Curves.pullbackCompMap_snd]
    exact StableModificationBridge.StableOpenGenericSmoothBaseChange.smooth_component_generic_fibre_of_flat_pullback
      (β ≫ q) p hsm hv
  have hstK : NumericallyStableFibre (pullbackCompMap β q p) (pullback.snd q p)
      (D'.comap (pullback.fst (β ≫ q) p)) σ := by
    rw [numericallyStableFibre_pullback_iff, hσp]
    exact hst
  have hncK : NoContractedClopen (pullbackCompMap β q p) (pullback.snd q p) σ := by
    rw [noContractedClopen_pullback_iff, hσp]
    exact hnc
  obtain ⟨OK, hσOK, hOK⟩ := exists_open_of_stableOpenNbhdRational_genericSmooth (hR K) pK (pullback.snd q p)
    hqK (pullbackCompMap β q p) hβK _ hssK hsmK σ hσK hstK hncK
  -- the image of `OK` in `U`
  have : UniversallyOpen p := inferInstance
  refine ⟨⟨p '' (OK : Set _), p.isOpenMap _ OK.isOpen⟩,
    ⟨σ (IsLocalRing.closedPoint K), hσOK, ?_⟩, ?_⟩
  · have h := ha (IsLocalRing.closedPoint K)
    rw [← hσp] at h
    exact h
  · rintro _ ⟨u, hu, rfl⟩
    exact isNumericallyStableAt_of_pullback p (hOK u hu)


end DeJongAlterations.StableModification.Global
