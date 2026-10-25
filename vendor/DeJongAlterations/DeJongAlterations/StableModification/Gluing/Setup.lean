/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.Gluing.GammaFinite
import DeJongAlterations.StableModification.Gluing.RefinementProjective
import DeJongAlterations.StableModification.Gluing.RefinementProjectiveBirational

/-!
# The projective refinement of a curve over a valuation ring (Temkin §4.5, first steps)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (`sepclosprop`, `semi-stable.tex` lines 3243–3252): for a curve `C` over a
valuation ring `R` of finite height with algebraically closed fraction field, local uniformization
(Proposition 4.3.3) gives strictly semi-stable affine quasi-modifications `Tᵢ → C` covering
`RZ_L(C)`, `L = K(C)`; Proposition 3.2.6 refines them into a modification `C' → C` covered by
opens `C'ᵢ` with proper `C'ᵢ → Tᵢ`; cofinality (Proposition 4.3.1) dominates each `C'ᵢ` by a
strictly semi-stable modification of `Tᵢ`. This file assembles these steps (`PLAN-T5.md` §2.2
steps 1–3 and the non-projective part of step 4; nodes A1–A3; blueprint `sm-gluing-semistable.tex`,
`thm:sm-gluing-refinement`), with the additions needed by the route of PLAN-T5:

* `exists_transcendental_isSeparable_of_perfectField`: a separating transcendence element of
  `K(C)/K` for perfect `K` (the hypothesis `hsep` of local uniformization; node A1);
* `exists_affine_piece`, `exists_finite_isStrictlySemistable_affine_cover`: local uniformization
  with each piece mapping into an affine open of `C` (the hypothesis of the refinement theorem);
* `SpecMap_apply_eq_genericPoint`, `exists_mul_eq_of_piece`, `fiberTrdeg_piece`: a piece
  `Spec E → C` has function field `L` and relative dimension one;
* `apply_eq_genericPoint_of_isDominant`, `isModification_of_piece`: the pieces `C'ᵢ → Tᵢ` of the
  refinement are modifications (`Gluing.birationalOver_of_locallyOfFiniteType`);
* `exists_projective_refinement`: the assembly — `p : C' → C` is a modification, projective over
  `C` (`Gluing.exists_refinement_projective`, node A2), the pieces are modifications with finite
  `Γ₀` (`Gluing.finite_gammaZeroSet_of_flat`, node A3, the T62 fix) and are dominated by strictly
  semi-stable modifications of the `Tᵢ`.

The projectivity of the strictly semi-stable dominating modifications (PLAN-T5 node A4, needed for
Stein finiteness in the normalization step A5) is **not** proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open scoped IntermediateField

universe u

namespace DeJongAlterations.StableModification.Gluing

open ValCurves RiemannZariskiSpace LocalUniformization LocalUniformization.Curve Curves
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Separable

/-- **A separating transcendence element** over a perfect field: a finitely generated field
extension of transcendence degree one of a perfect field is separable over `K(x)` for some
transcendental `x` (Mathlib's separable generation, `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`). -/
theorem exists_transcendental_isSeparable_of_perfectField {K L : Type*} [Field K] [Field L]
    [Algebra K L] [PerfectField K] (hfg : (⊤ : IntermediateField K L).FG)
    (htr : Algebra.trdeg K L = 1) :
    ∃ x : L, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ L := by
  have := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have hcard : s.card = 1 := by
    have h1 := hs.cardinalMk_eq_trdeg
    rw [htr, Cardinal.mk_coe_finset] at h1
    exact_mod_cast h1
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨x, ?_, ?_⟩
  · exact hs.1.transcendental ⟨x, Finset.mem_singleton_self x⟩
  · rwa [Finset.coe_singleton] at hsep

end Separable

section Cover

variable {K : Type u} [Field K] {R : ValuationSubring K} {C : Scheme.{u}} [IsIntegral C]
  (φ : C ⟶ Spec (.of R))

/-- **Shrinking a local uniformization piece into an affine open.** Let `g : Spec E → C` be an
`L`-quasi-modification (`L = K(C)`, `E ⊆ L`) with `Spec E` strictly semi-stable over `R`, and
`V ∈ RZ_L(Spec E)`. Some basic open `Spec E[1/e]` containing the centre of `V` maps into an affine
open of `C`; it is again such a piece and `V ∈ RZ_L(Spec E[1/e])`. -/
theorem exists_affine_piece {E : Type u} [CommRing E] (ιE : E →+* C.functionField)
    (g : Spec (.of E) ⟶ C) (hinj : Function.Injective ιE)
    (hg : Spec.map (CommRingCat.ofHom ιE) ≫ g = genericPt C) [LocallyOfFiniteType g]
    (hss : IsStrictlySemistable (g ≫ φ) ⊤) {V : RiemannZariskiSpace C.functionField}
    (hV : V ∈ ofScheme (Spec.map (CommRingCat.ofHom ιE))) :
    ∃ (E' : Type u) (_ : CommRing E') (ιE' : E' →+* C.functionField) (g' : Spec (.of E') ⟶ C)
      (VC : C.Opens),
      Function.Injective ιE' ∧ Spec.map (CommRingCat.ofHom ιE') ≫ g' = genericPt C ∧
      LocallyOfFiniteType g' ∧ IsStrictlySemistable (g' ≫ φ) ⊤ ∧ IsAffineOpen VC ∧
      g' ⁻¹ᵁ VC = ⊤ ∧ V ∈ ofScheme (Spec.map (CommRingCat.ofHom ιE')) := by
  obtain ⟨x, hx⟩ := exists_isCentre_of_mem_ofScheme hV
  obtain ⟨_, ⟨VC, hVC, rfl⟩, hgx, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
  obtain ⟨_, ⟨e, rfl⟩, hxe, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show x ∈ (g ⁻¹ᵁ VC : Set (Spec (.of E))) from hgx) (g ⁻¹ᵁ VC).isOpen
  have he : ιE e ≠ 0 := by
    intro h0
    rw [show e = 0 from hinj (by rw [h0, map_zero])] at hxe
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hxe (zero_mem _)
  let E' := Localization.Away e
  let ιE' : E' →+* C.functionField := IsLocalization.Away.lift e (isUnit_iff_ne_zero.mpr he)
  have hιE' : ιE'.comp (algebraMap E E') = ιE := IsLocalization.lift_comp _
  let j := Spec.map (CommRingCat.ofHom (algebraMap E E'))
  have hj : Spec.map (CommRingCat.ofHom ιE') ≫ j = Spec.map (CommRingCat.ofHom ιE) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hιE']
  have hrange : (j.opensRange : Set (Spec (.of E))) =
      ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum E)) : Set (PrimeSpectrum E)) :=
    congrArg SetLike.coe (Scheme.Hom.opensRange_localizationAway (R := .of E) e)
  have hinj' : Function.Injective ιE' := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e) y
    have h1 := congrArg ιE' (IsLocalization.mk'_spec E' a m)
    rw [map_mul, hy, zero_mul, ← RingHom.comp_apply, hιE'] at h1
    change IsLocalization.mk' E' a m = 0
    rw [show a = 0 from hinj (by rw [← h1, map_zero]), IsLocalization.mk'_zero]
  refine ⟨E', inferInstance, ιE', j ≫ g, VC, hinj', by rw [reassoc_of% hj, hg], inferInstance,
    ?_, hVC, ?_, ?_⟩
  · have := hss.etale_comp j
    rwa [Scheme.IdealSheafData.comap_top, ← Category.assoc] at this
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    have hy : j y ∈ (j.opensRange : Set (Spec (.of E))) := ⟨y, rfl⟩
    rw [hrange] at hy
    exact hle hy
  · have hxr : x ∈ (j.opensRange : Set (Spec (.of E))) := by rw [hrange]; exact hxe
    obtain ⟨x', rfl⟩ := hxr
    exact (IsCentre.of_isOpenImmersion j hj hx).mem_ofScheme

/-- **Temkin, Proposition 4.3.3, with affine targets** (`locunifprop`; the form consumed by the
refinement, PLAN-T5 §2.2 step 1). For `K` algebraically closed and `C` integral, separated,
quasi-compact, flat and locally of finite type over a valuation ring `R` of finite height and
equal characteristic, with a separating transcendence element of `K(C)/K`, there are finitely
many `L`-quasi-modifications `gᵢ : Spec Eᵢ → C` (`L = K(C)`, `Eᵢ ⊆ L`), each mapping into an
affine open `Vᵢ ⊆ C` and strictly semi-stable over `R`, whose Riemann–Zariski spaces cover
`RZ_L(C)`. -/
theorem exists_finite_isStrictlySemistable_affine_cover [IsAlgClosed K]
    [Finite (PrimeSpectrum R)] (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p)
    [C.IsSeparated] [CompactSpace C] [Flat φ] [LocallyOfFiniteType φ]
    (hsep : letI := functionFieldAlgebra φ
      ∃ x : C.functionField, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ C.functionField) :
    ∃ (ι : Type u) (_ : Finite ι) (E : ι → Type u) (_ : ∀ i, CommRing (E i))
      (ιE : ∀ i, E i →+* C.functionField) (g : ∀ i, Spec (.of (E i)) ⟶ C) (VC : ι → C.Opens),
      (∀ i, Function.Injective (ιE i) ∧ Spec.map (CommRingCat.ofHom (ιE i)) ≫ g i = genericPt C ∧
        LocallyOfFiniteType (g i) ∧ IsStrictlySemistable (g i ≫ φ) ⊤ ∧ IsAffineOpen (VC i) ∧
        g i ⁻¹ᵁ VC i = ⊤) ∧
      rzSpace C = ⋃ i, ofScheme (Spec.map (CommRingCat.ofHom (ιE i))) := by
  let := functionFieldAlgebra φ
  have hrat := allPlacesRational_of_isAlgClosed (fg_functionField φ) hsep
  choose E _ ιE g hg using fun V : rzSpace C ↦
    exists_isStrictlySemistable_of_mem_rzSpace hchar φ hsep hrat V.1 V.2
  choose E' _ ιE' g' VC hg' using fun V : rzSpace C ↦ by
    have := (hg V).2.2.1
    exact exists_affine_piece φ (ιE V) (g V) (hg V).1 (hg V).2.1 (hg V).2.2.2.2.2.1
      (hg V).2.2.2.2.2.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : rzSpace C ↦
      (Subtype.val : rzSpace C → _) ⁻¹' ofScheme (Spec.map (CommRingCat.ofHom (ιE' V))))
    (fun V ↦ by
      have := (hg' V).2.2.1
      exact isOpen_ofScheme_of_locallyOfFiniteType (g' V) (hg' V).2.1)
    (fun V _ ↦ Set.mem_iUnion.mpr ⟨V, (hg' V).2.2.2.2.2.2⟩)
  refine ⟨t, inferInstance, fun i ↦ E' i.1, fun i ↦ inferInstance, fun i ↦ ιE' i.1,
    fun i ↦ g' i.1, fun i ↦ VC i.1, fun i ↦ ⟨(hg' i.1).1, (hg' i.1).2.1, (hg' i.1).2.2.1,
      (hg' i.1).2.2.2.1, (hg' i.1).2.2.2.2.1, (hg' i.1).2.2.2.2.2.1⟩,
    Set.Subset.antisymm (fun V hV ↦ ?_)
      (Set.iUnion_subset fun i ↦ ofScheme_subset_of_comp (g' i.1) (hg' i.1).2.1)⟩
  obtain ⟨i, hi, hVi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ⟨V, hV⟩))
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hVi⟩

end Cover

section Piece

variable {K : Type u} [Field K] {R : ValuationSubring K} {C : Scheme.{u}} [IsIntegral C]
  {E : Type u} [CommRing E] (ιE : E →+* C.functionField) (g : Spec (.of E) ⟶ C)

/-- The point `Spec L → Spec E` of an injective map `E → L` hits the generic point. -/
theorem SpecMap_apply_eq_genericPoint [IsDomain E] (hinj : Function.Injective ιE)
    (z : Spec (.of C.functionField)) :
    Spec.map (CommRingCat.ofHom ιE) z = genericPoint (Spec (.of E)) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  ext n
  have h := mem_asIdeal_iff_eq_zero (𝟙 (Spec (.of E))) ιE (Category.comp_id _) z n
  rw [PrimeSpectrum.asIdeal_bot, Ideal.mem_bot]
  exact h.trans ⟨fun h ↦ hinj (by rw [h, map_zero]), fun h ↦ by rw [h, map_zero]⟩

/-- **The function field of a piece is `L`**: if `g : Spec E → C` (`E ⊆ L = K(C)`) maps into an
affine open `V ⊆ C`, every element of `L` is a fraction of elements of `E`. -/
theorem exists_mul_eq_of_piece (hg : Spec.map (CommRingCat.ofHom ιE) ≫ g = genericPt C)
    {VC : C.Opens} (hVC : IsAffineOpen VC) (hgV : g ⁻¹ᵁ VC = ⊤) (x : C.functionField) :
    ∃ a b : E, ιE b ≠ 0 ∧ x * ιE b = ιE a := by
  obtain ⟨z⟩ : Nonempty (Spec (.of C.functionField)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  have hξ : genericPoint C ∈ VC := by
    rw [← genericPt_apply z, ← hg, Scheme.Hom.comp_apply]
    have : Spec.map (CommRingCat.ofHom ιE) z ∈ g ⁻¹ᵁ VC := by rw [hgV]; trivial
    exact this
  have : Nonempty VC := ⟨⟨_, hξ⟩⟩
  have : IsFractionRing Γ(C, VC) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C VC hVC
  have hηV : genericPt C ⁻¹ᵁ VC = ⊤ := by
    rw [← functionFieldPoint_eq_genericPt]
    exact functionFieldPoint_preimage hVC hξ
  have hcomp := sectionsToField_comp_appLE g hg (U := VC) (U' := ⊤) hgV.ge rfl hηV
  rw [Curve.sectionsToField_SpecMap_top] at hcomp
  have hsV : sectionsToField (genericPt C) VC hηV = algebraMap Γ(C, VC) C.functionField := by
    rw [sectionsToField_congr functionFieldPoint_eq_genericPt.symm hηV
      (functionFieldPoint_preimage hVC hξ), sectionsToField_functionFieldPoint hVC hξ]
    rfl
  let ψ : Γ(C, VC) →+* E := (g.appLE VC ⊤ hgV.ge ≫ (Scheme.ΓSpecIso (.of E)).hom).hom
  have hψ : ∀ v, ιE (ψ v) = algebraMap Γ(C, VC) C.functionField v := by
    intro v
    rw [← hsV, ← hcomp]
    rfl
  obtain ⟨a₀, b₀, hb₀, rfl⟩ := IsFractionRing.div_surjective (A := Γ(C, VC)) x
  have hb : algebraMap Γ(C, VC) C.functionField b₀ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb₀
  refine ⟨ψ a₀, ψ b₀, by rw [hψ]; exact hb, ?_⟩
  rw [hψ, hψ, div_mul_cancel₀ _ hb]

/-- **The relative dimension of a piece**: if `Spec E → C` is an `L`-quasi-modification
(`E ⊆ L = K(C)`), the generic point of `Spec E` has the fibre dimension of the generic point of
`C` (the residue field map at the generic point is surjective). -/
theorem fiberTrdeg_piece [IsDomain E] (φ : C ⟶ Spec (.of R)) (hinj : Function.Injective ιE)
    (hg : Spec.map (CommRingCat.ofHom ιE) ≫ g = genericPt C) :
    fiberTrdeg (g ≫ φ) (genericPoint (Spec (.of E))) = fiberTrdeg φ (genericPoint C) := by
  obtain ⟨z⟩ : Nonempty (Spec (.of C.functionField)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  set a := Spec.map (CommRingCat.ofHom ιE)
  have haz : a z = genericPoint (Spec (.of E)) := SpecMap_apply_eq_genericPoint ιE hinj z
  have hgz : g (a z) = genericPoint C := by
    rw [← Scheme.Hom.comp_apply, hg, genericPt_apply]
  have : SurjectiveOnStalks (a ≫ g) := by rw [hg]; unfold genericPt; infer_instance
  have hsurj : Function.Surjective ((a ≫ g).residueFieldMap z) := by
    intro y
    obtain ⟨t, rfl⟩ := Scheme.residue_surjective _ z y
    obtain ⟨t', rfl⟩ := (a ≫ g).stalkMap_surjective z t
    refine ⟨Scheme.residue _ _ t', ?_⟩
    have h1 := Scheme.residue_residueFieldMap (a ≫ g) z
    rw [← CommRingCat.comp_apply, h1, CommRingCat.comp_apply]
  have hsurj' : Function.Surjective (g.residueFieldMap (a z)) := by
    intro y
    obtain ⟨w, hw⟩ := hsurj (a.residueFieldMap z y)
    refine ⟨w, (a.residueFieldMap z).hom.injective ?_⟩
    rw [← hw, Scheme.residueFieldMap_comp]
    rfl
  have halg : IsAlgebraicAt g (a z) := RingHom.isIntegral_of_surjective _ hsurj'
  rw [← haz, fiberTrdeg_comp, (isAlgebraicAt_iff_fiberTrdeg_eq_zero g _).mp halg, add_zero, hgz]

/-- A dominant point `Spec L → X` hits the generic point. -/
theorem apply_eq_genericPoint_of_isDominant {L : Type u} [Field L] {X : Scheme.{u}}
    [IsIntegral X] (e : Spec (.of L) ⟶ X) [IsDominant e] (z : Spec (.of L)) :
    e z = genericPoint X := by
  have hr : Set.range e = {e z} := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subsingleton.elim (h := inferInstanceAs (Subsingleton (PrimeSpectrum L))) w z]
      rfl
    · rintro rfl
      exact ⟨z, rfl⟩
  have hgen : IsGenericPoint (e z) (Set.univ : Set X) := by
    rw [isGenericPoint_def, ← hr]
    exact e.denseRange.closure_range
  exact hgen.eq (genericPoint_spec X)

/-- **The pieces of a refinement are modifications** of the affine quasi-modifications
`Spec E → C` (`E ⊆ L = K(C)` mapping into an affine open of `C`): a proper `h : W → Spec E` with
a dominant point `e : Spec L → W` over `Spec L → Spec E`, `W` an open of an integral scheme. -/
theorem isModification_of_piece [IsDomain E] {X : Scheme.{u}} [IsIntegral X] (W : X.Opens)
    (h : W.toScheme ⟶ Spec (.of E)) [IsProper h] (e : Spec (.of C.functionField) ⟶ W.toScheme)
    [IsDominant e] (he : e ≫ h = Spec.map (CommRingCat.ofHom ιE)) (hinj : Function.Injective ιE)
    (hg : Spec.map (CommRingCat.ofHom ιE) ≫ g = genericPt C) {VC : C.Opens}
    (hVC : IsAffineOpen VC) (hgV : g ⁻¹ᵁ VC = ⊤) : IsModification h := by
  obtain ⟨z⟩ : Nonempty (Spec (.of C.functionField)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  have : Nonempty W.toScheme := ⟨e z⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hη : ∀ z, e z = genericPoint W.toScheme := apply_eq_genericPoint_of_isDominant e
  have hηq : ∀ z, (e ≫ h) z = genericPoint (Spec (.of E)) := fun z ↦ by
    rw [he]
    exact SpecMap_apply_eq_genericPoint ιE hinj z
  have hηU : (e ≫ h) ⁻¹ᵁ ⊤ = ⊤ := rfl
  have hs : sectionsToField (e ≫ h) ⊤ hηU =
      ((Scheme.ΓSpecIso (.of E)).hom ≫ CommRingCat.ofHom ιE).hom := by
    rw [sectionsToField_congr he hηU rfl, Curve.sectionsToField_SpecMap_top]
  refine
    { toIsProper := inferInstance
      sourceIntegral := inferInstance
      targetIntegral := inferInstance
      birational := birationalOver_of_locallyOfFiniteType e hη h hηq (isAffineOpen_top _) hηU
        fun x ↦ ?_ }
  obtain ⟨a, b, hb, hab⟩ := exists_mul_eq_of_piece ιE g hg hVC hgV x
  refine ⟨(Scheme.ΓSpecIso (.of E)).inv a, (Scheme.ΓSpecIso (.of E)).inv b, ?_, ?_⟩ <;>
    simp only [hs, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  · rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  · rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
      ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end Piece

section Assembly

variable {K : Type u} [Field K] {R : ValuationSubring K}

/-- **The projective refinement of a curve over a valuation ring** (`PLAN-T5.md` §2.2 steps 1–4
without the projectivity of step 4; nodes A1–A3; Temkin, proof of Proposition 4.5.1, T:3243–3252).
Let `K` be algebraically closed, `R ⊆ K` a valuation ring of finite height and equal
characteristic, and `φ : C → Spec R` an integral, separated, quasi-compact, flat relative curve
locally of finite type (`trdeg K(C)/K = 1`). There are a modification `p : C' → C`, projective over
`C`, and a finite open cover `{Wᵢ}` of `C'` with modifications `hᵢ : Wᵢ → Tᵢ = Spec Eᵢ` over `C`,
where `gᵢ : Tᵢ → C` are affine `L`-quasi-modifications with `Tᵢ` strictly semi-stable over `R`
(local uniformization). Moreover `Γ₀(Wᵢ)` (relative to `Tᵢ`) is finite, and `Wᵢ` is dominated by
a strictly semi-stable modification of `Tᵢ` (Temkin's cofinality, Proposition 4.3.1, available for
all modifications by `exists_dominates_isStrictlySemistable_of_isModification`). -/
theorem exists_projective_refinement [IsAlgClosed K] [Finite (PrimeSpectrum R)]
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p) {C : Scheme.{u}} [IsIntegral C]
    [C.IsSeparated] [CompactSpace C] (φ : C ⟶ Spec (.of R)) [Flat φ] [LocallyOfFiniteType φ]
    (htr : fiberTrdeg φ (genericPoint C) = 1) :
    ∃ (C' : Scheme.{u}) (p : C' ⟶ C), IsModification p ∧ DeJong.IsRelativelyProjective φ p ∧
      ∃ (ι : Type u) (_ : Finite ι) (E : ι → Type u) (_ : ∀ i, CommRing (E i))
        (_ : ∀ i, IsDomain (E i)) (g : ∀ i, Spec (.of (E i)) ⟶ C) (W : ι → C'.Opens)
        (h : ∀ i, (W i).toScheme ⟶ Spec (.of (E i))),
        ⨆ i, W i = ⊤ ∧ ∀ i, IsStrictlySemistable (g i ≫ φ) ⊤ ∧
          fiberTrdeg (g i ≫ φ) (genericPoint (Spec (.of (E i)))) = 1 ∧
          h i ≫ g i = (W i).ι ≫ p ∧
          ∃ (_ : IsModification (h i)),
            (gammaZeroSet (h i ≫ g i ≫ φ) (genericLift (h i))
              (genericPt (Spec (.of (E i))))).Finite ∧
            ∃ (C'' : Scheme.{u}) (_ : IsIntegral C'') (f'' : C'' ⟶ Spec (.of (E i)))
              (_ : IsModification f''), IsStrictlySemistable (f'' ≫ g i ≫ φ) ⊤ ∧
                ∃ q : C'' ⟶ (W i).toScheme, q ≫ h i = f'' := by
  let := functionFieldAlgebra φ
  have hfg := fg_functionField φ
  have htrK : Algebra.trdeg K C.functionField = 1 := (trdeg_functionField_eq φ).trans htr
  have hsep := exists_transcendental_isSeparable_of_perfectField hfg htrK
  obtain ⟨ι, _, E, _, ιE, g, VC, hg, hcov⟩ :=
    exists_finite_isStrictlySemistable_affine_cover φ hchar hsep
  have : ∀ i, LocallyOfFiniteType (g i) := fun i ↦ (hg i).2.2.1
  have : ∀ i, IsDomain (E i) := fun i ↦ (hg i).1.isDomain
  have hηT : ∀ i, Spec.map (CommRingCat.ofHom (ιE i)) ≫ g i =
      functionFieldPoint C C.functionField := fun i ↦ by
    rw [functionFieldPoint_eq_genericPt]
    exact (hg i).2.1
  obtain ⟨C', p, η', F, W, h, hR, hF, hC, hpc, -, hcov', hP⟩ :=
    exists_refinement_projective φ (functionFieldPoint C C.functionField)
      (fun i ↦ Spec (.of (E i))) g (fun i ↦ Spec.map (CommRingCat.ofHom (ιE i))) hηT VC
      (fun i ↦ (hg i).2.2.2.2.1) (fun i ↦ (hg i).2.2.2.2.2)
  have := hR.isIntegral
  refine ⟨C', p, isModification_of_hasCharts hR hF hC, hP, ι, inferInstance, E, inferInstance,
    inferInstance, g, W, h, hcov' ?_, fun i ↦ ?_⟩
  · rw [functionFieldPoint_eq_genericPt]
    exact hcov.le
  · obtain ⟨hhp, hcomm, e, he1, he2, hedom⟩ := hpc i
    have hss := (hg i).2.2.2.1
    have hdim := (fiberTrdeg_piece (ιE i) (g i) φ (hg i).1 (hg i).2.1).trans htr
    have hmod : IsModification (h i) :=
      isModification_of_piece (ιE i) (g i) (W i) (h i) e he2 (hg i).1 (hg i).2.1
        (hg i).2.2.2.2.1 (hg i).2.2.2.2.2
    have := hmod.sourceIntegral
    have : DeJong.IsNodalCurve (g i ≫ φ) := hss.isNodalCurve
    have : QuasiCompact (g i ≫ φ) :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
    exact ⟨hss, hdim, hcomm, hmod, finite_gammaZeroSet_of_flat (g i ≫ φ) hdim.le (h i),
      exists_dominates_isStrictlySemistable_of_isModification (g i ≫ φ) hss hdim.le (h i)⟩

end Assembly

end DeJongAlterations.StableModification.Gluing
