/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ContractionStep
import DeJongAlterations.StableModification.Blowups.TransportSection
import DeJongAlterations.StableModification.Omega.BaseChangeFibre

/-!
# The marks of an exceptional blow-down (Temkin, Lemma 4.4.5, marks part)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Lemma 4.4.5
(T:3178–3186): an exceptional blow-down `(C', D') → (C'', D'')` of a semi-stable multipointed
curve is semi-stable. `ContractionStep.lean` proves that `C''` is a nodal curve; this file treats
the marks (blueprint `lem:sm-bdg-marks`, `sm-blow-down-global.tex`). Write `b : Y → Y''` for the
blow-down over `C`, `D_Y`, `D''` for the transported marks of `Y` and `Y''`, `x = b(Z)`.

* `genericMarksClosure_eq_ker_comp`: `D''` is the scheme-theoretic image of `D_Y` under `b`
  (both are schematic closures of the generic marks, and `b` is an isomorphism on generic fibres).
* `isClosedImmersion_subschemeι_comp`: `D_Y → Y''` is a closed immersion. Off the modification
  locus `b` is an isomorphism; near `x` either no mark of `Y` lies on `Z = b⁻¹(x)`, or exactly one
  `d` does, and then the component of the finite étale `D_Y` through `d` is the image of a section
  of `D_Y → Spec V` (henselian `V` with separably closed residue field: lane BND's
  `Blowups.exists_section_of_etale`), clopen in `D_Y` (`DeJong.isClopen_range_of_comp_eq_id`), whose
  composite with `b` is a section of `Y'' → Spec V`, hence a closed immersion.
* `isSemistablePair_blowDown`: `(Y'', D'')` is a semi-stable pair: `D'' ≅ D_Y` is étale over `V`,
  and `D''` lies in the smooth locus of `Y''` (off the modification locus by transport, at `x` by
  the smoothness of `x` in the closed fibre and lane OM1D's
  `Omega.preimage_smoothLocus_eq_of_isNodalCurve`, and at the generizations of `x` by openness of
  the smooth locus).
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Geometry.ModificationCenter (isomorphismOpen center)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section GenericMarks

variable {S C Y Y'' : Scheme.{u}} (φ : C ⟶ S) (D : C.IdealSheafData) (b : Y ⟶ Y'')
  (β'' : Y'' ⟶ C) (s : S)

/-- The fibre map of a composite is the composite of the fibre maps. -/
theorem fiberMap_comp :
    Curves.fiberMap (b ≫ β'') φ s = Curves.fiberMap b (β'' ≫ φ) s ≫ Curves.fiberMap β'' φ s := by
  apply pullback.hom_ext
  · change Curves.fiberMap (b ≫ β'') φ s ≫ φ.fiberι s =
      (Curves.fiberMap b (β'' ≫ φ) s ≫ Curves.fiberMap β'' φ s) ≫ φ.fiberι s
    rw [Curves.fiberMap_fiberι, Category.assoc (Curves.fiberMap b (β'' ≫ φ) s),
      Curves.fiberMap_fiberι, Curves.fiberMap_fiberι_assoc]
    rfl
  · change Curves.fiberMap (b ≫ β'') φ s ≫ φ.fiberToSpecResidueField s =
      (Curves.fiberMap b (β'' ≫ φ) s ≫ Curves.fiberMap β'' φ s) ≫ φ.fiberToSpecResidueField s
    rw [Curves.fiberMap_fiberToSpecResidueField,
      Category.assoc (Curves.fiberMap b (β'' ≫ φ) s), Curves.fiberMap_fiberToSpecResidueField,
      Curves.fiberMap_fiberToSpecResidueField]
    rfl

/-- **The transported marks of the blow-down are the image of those of `Y`**: if `b` is an
isomorphism on the fibres over `s`, then `genericMarksClosure β'' φ D s` is the kernel (the
scheme-theoretic image) of `D_Y → Y → Y''`, `D_Y = genericMarksClosure (b ≫ β'') φ D s`. -/
theorem genericMarksClosure_eq_ker_comp [IsIso (Curves.fiberMap b (β'' ≫ φ) s)] :
    Curves.genericMarksClosure β'' φ D s =
      ((Curves.genericMarksClosure (b ≫ β'') φ D s).subschemeι ≫ b).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
  unfold Curves.genericMarksClosure
  rw [Scheme.IdealSheafData.map_ker, fiberMap_comp, Scheme.IdealSheafData.comap_comp]
  set A := (DeJong.fiberMarks φ D s).comap (Curves.fiberMap β'' φ s)
  set G := Curves.fiberMap b (β'' ≫ φ) s
  have e : (A.comap G).subschemeι ≫ ((b ≫ β'') ≫ φ).fiberι s ≫ b =
      ((A.comapIso G).hom ≫ pullback.snd G A.subschemeι) ≫ A.subschemeι ≫ (β'' ≫ φ).fiberι s := by
    have h1 : ((b ≫ β'') ≫ φ).fiberι s ≫ b = G ≫ (β'' ≫ φ).fiberι s :=
      (Curves.fiberMap_fiberι b (β'' ≫ φ) s).symm
    rw [h1, ← Scheme.IdealSheafData.comapIso_hom_fst A G, Category.assoc, Category.assoc,
      pullback.condition_assoc]
  rw [(Category.assoc _ _ _).trans e,
    Scheme.Hom.ker_comp_of_isIso ((A.comapIso G).hom ≫ pullback.snd G A.subschemeι)]

end GenericMarks

section ClosedImmersion

variable {V : Type u} [CommRing V] [HenselianLocalRing V] [IsSepClosed (IsLocalRing.ResidueField V)]
  {Y Y'' : Scheme.{u}} (p : Y'' ⟶ Spec (CommRingCat.of V)) (b : Y ⟶ Y'') (DY : Y.IdealSheafData)
  [IsProper b] [IsSeparated p] [Etale (DY.subschemeι ≫ b ≫ p)]

/-- **The marks of `Y` map isomorphically onto those of the blow-down** (blueprint
`lem:sm-bdg-marks`): `D_Y → Y → Y''` is a closed immersion, if `b` is an isomorphism off its
modification locus, every point of the modification locus specializes to a point `x` of the closed
fibre, and at most one point of `D_Y` lies over `x`. Off the modification locus this is the
restriction of `D_Y`; near `x`, the component of `D_Y` through the mark over `x` is the image of a
section of the étale `D_Y → Spec V` (henselian `V`), clopen in `D_Y`. -/
theorem isClosedImmersion_subschemeι_comp (x : Y'') (hx : p x = IsLocalRing.closedPoint V)
    (hcen : ∀ y ∈ center b, y ⤳ x) (hmarks : (b ⁻¹' {x} ∩ (DY.support : Set Y)).Subsingleton) :
    IsClosedImmersion (DY.subschemeι ≫ b) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro y
  by_cases hy : y ∈ isomorphismOpen b
  · refine ⟨isomorphismOpen b, hy, ?_⟩
    rw [morphismRestrict_comp]
    have : IsIso (b ∣_ isomorphismOpen b) :=
      Geometry.ModificationCenter.isIso_restrict_isomorphismOpen b
    infer_instance
  have hyx : y ⤳ x := hcen y hy
  -- an open neighbourhood of `x` over which the map is a closed immersion
  suffices h : ∃ U : Y''.Opens, x ∈ U ∧ IsClosedImmersion ((DY.subschemeι ≫ b) ∣_ U) by
    obtain ⟨U, hxU, hU⟩ := h
    exact ⟨U, hyx.mem_open U.isOpen hxU, hU⟩
  by_cases hM : ∃ d, d ∈ b ⁻¹' {x} ∩ (DY.support : Set Y)
  · obtain ⟨d, hdx, hdD⟩ := hM
    rw [← Scheme.IdealSheafData.range_subschemeι] at hdD
    obtain ⟨d', rfl⟩ := hdD
    have hd' : (DY.subschemeι ≫ b ≫ p) d' = IsLocalRing.closedPoint V := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      rw [show b (DY.subschemeι d') = x from hdx]
      exact hx
    have : IsSeparated (DY.subschemeι ≫ b ≫ p) := inferInstance
    obtain ⟨σ, hσ, hσd⟩ := Blowups.exists_section_of_etale (DY.subschemeι ≫ b ≫ p) d' hd'
    have hclopen : IsClopen (Set.range σ) :=
      DeJong.isClopen_range_of_comp_eq_id (DY.subschemeι ≫ b ≫ p) σ hσ
    have hopen : IsOpenImmersion σ :=
      DeJong.isOpenImmersion_of_comp_eq_id (DY.subschemeι ≫ b ≫ p) σ hσ
    -- the other components of `D_Y`
    set F : Set Y := DY.subschemeι '' (Set.range σ)ᶜ with hF
    have hFc : IsClosed F :=
      DY.subschemeι.isClosedEmbedding.isClosedMap _ hclopen.isOpen.isClosed_compl
    have hbF : IsClosed (b '' F) := b.isClosedMap _ hFc
    let U : Y''.Opens := ⟨(b '' F)ᶜ, hbF.isOpen_compl⟩
    have hxU : x ∈ U := by
      rintro ⟨z, ⟨e, he, rfl⟩, hzx⟩
      have h1 : DY.subschemeι e = DY.subschemeι d' := by
        refine hmarks ⟨hzx, ?_⟩ ⟨hdx, ?_⟩
        · rw [← Scheme.IdealSheafData.range_subschemeι]
          exact ⟨e, rfl⟩
        · rw [← Scheme.IdealSheafData.range_subschemeι]
          exact ⟨d', rfl⟩
      have h2 : e = d' := DY.subschemeι.isClosedEmbedding.injective h1
      exact he ⟨IsLocalRing.closedPoint V, by rw [hσd, h2]⟩
    refine ⟨U, hxU, ?_⟩
    -- over `U`, the map is the section `τ = σ ≫ D_Y → Y''` of `Y'' → Spec V`
    set τ := σ ≫ DY.subschemeι ≫ b with hτ
    have hτp : τ ≫ p = 𝟙 _ := by
      rw [hτ, Category.assoc, Category.assoc]
      exact hσ
    have : IsClosedImmersion τ := DeJong.isClosedImmersion_of_comp_eq_id p τ hτp
    set O := (DY.subschemeι ≫ b) ⁻¹ᵁ U with hO
    have hsurj : Function.Surjective (σ ∣_ O) := by
      rintro ⟨e, he⟩
      have heσ : e ∈ Set.range σ := by
        by_contra hne
        exact he ⟨DY.subschemeι e, ⟨e, hne, rfl⟩, rfl⟩
      obtain ⟨t, rfl⟩ := heσ
      refine ⟨⟨t, he⟩, ?_⟩
      apply Subtype.ext
      exact morphismRestrict_base_coe σ O ⟨t, he⟩
    have hiso : IsIso (σ ∣_ O) := by
      rw [isIso_iff_isOpenImmersion_and_epi_base]
      exact ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr hsurj⟩
    have hcomp : σ ∣_ O ≫ (DY.subschemeι ≫ b) ∣_ U = τ ∣_ U :=
      (morphismRestrict_comp σ (DY.subschemeι ≫ b) U).symm
    have : (DY.subschemeι ≫ b) ∣_ U = inv (σ ∣_ O) ≫ τ ∣_ U := by
      rw [← hcomp, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  · push Not at hM
    have hbD : IsClosed (b '' (DY.support : Set Y)) := b.isClosedMap _ DY.support.isClosed
    let U : Y''.Opens := ⟨(b '' (DY.support : Set Y))ᶜ, hbD.isOpen_compl⟩
    have hxU : x ∈ U := by
      rintro ⟨d, hd, hdx⟩
      exact hM d ⟨hdx, hd⟩
    refine ⟨U, hxU, ?_⟩
    have : IsEmpty ((DY.subschemeι ≫ b) ⁻¹ᵁ U) := by
      refine ⟨fun ⟨e, he⟩ => he ⟨DY.subschemeι e, ?_, rfl⟩⟩
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨e, rfl⟩
    infer_instance

end ClosedImmersion

section Pair

variable {V : Type u} [CommRing V] [HenselianLocalRing V] [IsSepClosed (IsLocalRing.ResidueField V)]
  {Y Y'' : Scheme.{u}} (p : Y'' ⟶ Spec (CommRingCat.of V)) (b : Y ⟶ Y'') (DY : Y.IdealSheafData)
  [IsProper b] [IsSeparated p] [LocallyOfFinitePresentation p]

/-- Smoothness transfers along `b` off its modification locus. -/
theorem isSmoothAt_of_mem_isomorphismOpen {z : Y} (hz : b z ∈ isomorphismOpen b)
    (h : DeJong.IsSmoothAt (b ≫ p) z) : DeJong.IsSmoothAt p (b z) := by
  have : IsIso (b ∣_ isomorphismOpen b) := Geometry.ModificationCenter.isIso_restrict_isomorphismOpen b
  have : IsIso (b.stalkMap z) :=
    CurvesField.Genus.isIso_stalkMap_of_isIso_morphismRestrict b (isomorphismOpen b) z hz
  have e := Scheme.Hom.stalkMap_comp b p z
  unfold DeJong.IsSmoothAt at *
  rw [e] at h
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso (p.stalkMap (b z))
    (b.stalkMap z)).mp h

/-- **Temkin's Lemma 4.4.5, marks part** (blueprint `lem:sm-bdg-marks`): let `b : Y → Y''` be
proper over `p : Y'' → Spec V` (`V` henselian with separably closed residue field), `Y''` a nodal
curve, `(Y, D_Y)` a semi-stable pair over `V`, and `D''` the scheme-theoretic image of `D_Y`.
Assume that every point of the modification locus of `b` specializes to a point `x` of the
closed fibre, that at most one point of `D_Y` lies over `x`, and that `x` is a smooth point of
`Y''` if one does. Then `(Y'', D'')` is a semi-stable pair. -/
theorem isSemistablePair_blowDown (hp : DeJong.IsNodalCurve p)
    (hY : DeJong.IsSemistablePair (b ≫ p) DY) {D'' : Y''.IdealSheafData}
    (hD : D'' = (DY.subschemeι ≫ b).ker) (x : Y'') (hx : p x = IsLocalRing.closedPoint V)
    (hcen : ∀ y ∈ center b, y ⤳ x) (hmarks : (b ⁻¹' {x} ∩ (DY.support : Set Y)).Subsingleton)
    (hsmooth : (∃ d, d ∈ b ⁻¹' {x} ∩ (DY.support : Set Y)) → DeJong.IsSmoothAt p x) :
    DeJong.IsSemistablePair p D'' := by
  have := hY.etale
  have hci := isClosedImmersion_subschemeι_comp p b DY x hx hcen hmarks
  subst hD
  have hsupp : ((DY.subschemeι ≫ b).ker.support : Set Y'') = Set.range (DY.subschemeι ≫ b) := by
    rw [Scheme.Hom.support_ker, (DY.subschemeι ≫ b).isClosedEmbedding.isClosed_range.closure_eq]
  refine ⟨hp, ?_, ?_⟩
  · have e : (DY.subschemeι ≫ b).ker.subschemeι =
        inv (DY.subschemeι ≫ b).toImage ≫ DY.subschemeι ≫ b := by
      rw [IsIso.eq_inv_comp]
      exact Scheme.Hom.toImage_imageι _
    rw [e]
    simp only [Category.assoc]
    infer_instance
  · intro y hy
    rw [hsupp] at hy
    obtain ⟨e, rfl⟩ := hy
    by_cases hW : (DY.subschemeι ≫ b) e ∈ isomorphismOpen b
    · have hs := hY.smoothAlong (DY.subschemeι e) (by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨e, rfl⟩)
      exact isSmoothAt_of_mem_isomorphismOpen p b hW hs
    · have hyx := hcen _ hW
      have hxD : x ∈ Set.range (DY.subschemeι ≫ b) :=
        hyx.mem_closed (DY.subschemeι ≫ b).isClosedEmbedding.isClosed_range ⟨e, rfl⟩
      obtain ⟨e', he'⟩ := hxD
      have hsx := hsmooth ⟨DY.subschemeι e', he', by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨e', rfl⟩⟩
      rw [DeJong.isSmoothAt_iff_mem_smoothLocus] at hsx ⊢
      exact hyx.mem_open p.smoothLocus.isOpen hsx

end Pair

section Contracted

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  [Infinite (IsLocalRing.ResidueField V)] {X Y : Scheme.{u}}

local notation "s₀" => IsLocalRing.closedPoint V

open CurvesField CurvesField.Genus Cohomology in
/-- **The fibre of `b` over the contracted point is `Z`**, as a subset of `X` (from the stability
criterion, `contractedPoint_criterion`), for a structure map `q = b ≫ p`. -/
theorem preimage_contractedPoint_eq_closure
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (p : Y ⟶ Spec (CommRingCat.of V)) (b : X ⟶ Y) (q : X ⟶ Spec (CommRingCat.of V))
    (hq : b ≫ p = q) [IsIntegral Y] [IsIntegral X] [IsModification b] [IsProper p]
    [LocallyOfFinitePresentation p] [Flat p] [DeJong.IsNodalCurve q] [IsProper q]
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]
    (hp : IsProjectiveOver p) (hbp : DeJong.IsRelativelyProjective p b)
    (hnormal : IsNormalScheme Y) (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1)
    (hη : Curves.IsEtaModification b p) {Z : q.fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactlyAt q b Z)
    (hgZ : 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        (q.fiberToSpecResidueField s₀)) Z) :
    b ⁻¹' {b (q.fiberι s₀ Z)} = closure {q.fiberι s₀ Z} := by
  subst hq
  obtain ⟨hset, -⟩ := contractedPoint_criterion p b hsep hp hbp hnormal hcurve hη hZ
    ((contractsExactly_iff_contractsExactlyAt p b Z).2 hc) hgZ 0
  rw [closure_fiberι_singleton, ← hset]
  ext y
  constructor
  · intro hy
    have hys : (b ≫ p) y = IsLocalRing.closedPoint V := by
      rw [Scheme.Hom.comp_apply, show b y = b ((b ≫ p).fiberι s₀ Z) from hy,
        ← Scheme.Hom.comp_apply]
      exact apply_fiberι (b ≫ p) s₀ Z
    have : y ∈ Set.range ((b ≫ p).fiberι s₀) := by
      rw [Scheme.Hom.range_fiberι]
      exact hys
    obtain ⟨t, rfl⟩ := this
    refine ⟨t, ?_, rfl⟩
    apply (p.fiberι s₀).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Curves.fiberMap_fiberι]
    exact hy
  · rintro ⟨t, ht, rfl⟩
    change b ((b ≫ p).fiberι s₀ t) = b ((b ≫ p).fiberι s₀ Z)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Curves.fiberMap_fiberι,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg _ ht

/-- **The modification locus specializes to the contracted point**: every point of the
modification locus of `b` is a generization of `x = b(Z)` (its closure contains a closed point,
which lies over `s₀` and in the modification locus, hence is `x`). -/
theorem specializes_contractedPoint_of_mem_center (p : Y ⟶ Spec (CommRingCat.of V)) (b : X ⟶ Y)
    (q : X ⟶ Spec (CommRingCat.of V)) (hq : b ≫ p = q) [IsIntegral Y] [IsIntegral X]
    [IsModification b] [IsProper p] [LocallyOfFinitePresentation p] [Flat p]
    [DeJong.IsNodalCurve q]
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]
    (hnormal : IsNormalScheme Y) (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1)
    {Z : q.fiber s₀} (hZ : Z ∈ genericPoints _) (hc : ContractsExactlyAt q b Z) (y : Y)
    (hy : y ∈ center b) : y ⤳ b (q.fiberι s₀ Z) := by
  subst hq
  have : CompactSpace Y := compactSpace_of_quasiCompact p
  obtain ⟨y₀, hy₀, hy₀c⟩ := (isClosed_closure (s := ({y} : Set Y))).exists_closed_singleton
    (Set.singleton_nonempty y).closure
  have hyy₀ : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
  have hy₀C : y₀ ∈ center b := hyy₀.mem_closed (center b).isClosed hy
  have hps : y₀ ∈ Set.range (p.fiberι s₀) := by
    rw [Scheme.Hom.range_fiberι]
    exact apply_eq_closedPoint_of_isClosed p hy₀c
  obtain ⟨t, rfl⟩ := hps
  have ht := (center_inter_closedFibre p b hnormal hcurve hZ
    ((contractsExactly_iff_contractsExactlyAt p b Z).2 hc) t).1 hy₀C
  rw [ht, ← Scheme.Hom.comp_apply, Curves.fiberMap_fiberι] at hyy₀
  exact hyy₀

end Contracted

end

end DeJongAlterations.StableModification.BlowDown
