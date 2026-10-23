/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45D)
-/
import DeJongAlterations.StableModification.Gluing.CofinalProjectiveStage
import DeJongAlterations.StableModification.Blowups.SeparationMarks

/-!
# Projective transport of chart blow-ups over a henselian base

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Lemma 4.3.2 (`divlem`, T:3019–3046), whose blow-ups are spread from an étale chart and extended
"trivially" exactly as in the proof of Proposition 4.3.1 (T:2970–2983). Lane BND formalized the
separation of marks (`Blowups.exists_separation_marks`) with the transport
`Blowups.exists_transport`, which does not control projectivity. This file reproves the transport, over a henselian local
ring `A` with separably closed residue field, with the two changes of lane T45C
(`Gluing.CofinalProjective.exists_blowup_globalTransport_projective`):

* the neighbourhood `V₀` of the point `x` over which the chart blow-up `Bl_I M → M` is pulled back
  is **affine**: the modification locus is the image of a section of `φ⁻¹V(I) → Spec A/𝔞` through
  `x` (`exists_open_isClosed_locus_specializes`), so all its points specialize to `x` and it lies
  in every open neighbourhood of `x`;
* the centre `V(I)` of the chart blow-up is the modification locus itself.

Then the extension of the pulled-back blow-up by the identity is a native blow-up of an ideal
sheaf of finite type (lane T45C's `BlowupProjective.isProjectiveOver_extensionHom`), so it
**preserves projectivity** (`CofinalProjective.PreservesProjective`).

## Main results

* `locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType`: EGA IV 1.4.3 (v);
* `PreservesProjective.comp`: projectivity-preserving modifications compose;
* `exists_open_isClosed_locus_specializes`: BND's `Blowups.exists_open_isClosed_locus`, with the
  specialization of the locus to `x`;
* `exists_transport_projective`: BND's `Blowups.exists_transport` for an affine chart blow-up whose
  centre is the modification locus, with the preservation of projectivity;
* `exists_smoothBlowup_transport_projective` (`Bl_{(π, T - a)}`) and
  `exists_locusBlowup_transport_projective` (`Bl_{(u, v, π)}` of `A[u,v]/(uv - π²b)`, lane T45C's
  `Gluing.LocusBlowup`);
* `piLift`, `piLift_comp`: lifts of sections into the `π`-chart of `Bl_{(u, v, π)}`.

Blueprint: `sm-gluing-separation-projective.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.Gluing.SeparationProjective

open Curves Blowups Algebra.NodeBlowupChart
open CofinalProjective (PreservesProjective)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section FinitePresentation

/-- **Finite presentation descends along a morphism locally of finite type** (EGA IV 1.4.3 (v)):
if `f ≫ g` is locally of finite presentation and `g` is locally of finite type, then `f` is
locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [hfg : LocallyOfFinitePresentation (f ≫ g)]
    [hg : LocallyOfFiniteType g] : LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z with H
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have h1 : LocallyOfFinitePresentation ((f ∣_ (g ⁻¹ᵁ U.1)) ≫ (g ∣_ U.1)) := by
      rw [← morphismRestrict_comp]
      exact IsZariskiLocalAtTarget.restrict hfg U.1
    have h2 : LocallyOfFiniteType (g ∣_ U.1) := IsZariskiLocalAtTarget.restrict hg U.1
    have : IsAffine U.1.toScheme := U.2
    exact H (f ∣_ (g ⁻¹ᵁ U.1)) (g ∣_ U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y with H
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have h1 : LocallyOfFinitePresentation ((f ∣_ U.1) ≫ U.1.ι ≫ g) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      exact MorphismProperty.comp_mem _ _ _
        (locallyOfFinitePresentation_of_isOpenImmersion (f ⁻¹ᵁ U.1).ι) hfg
    have h2 : LocallyOfFiniteType (U.1.ι ≫ g) :=
      MorphismProperty.comp_mem _ _ _ (locallyOfFiniteType_of_isOpenImmersion U.1.ι) hg
    have : IsAffine U.1.toScheme := U.2
    exact H (f ∣_ U.1) (U.1.ι ≫ g) inferInstance
  wlog hX : IsAffine X generalizing X with H
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have h1 : LocallyOfFinitePresentation ((U.1.ι ≫ f) ≫ g) := by
      rw [Category.assoc]
      exact MorphismProperty.comp_mem _ _ _
        (locallyOfFinitePresentation_of_isOpenImmersion U.1.ι) hfg
    have : IsAffine U.1.toScheme := U.2
    exact H (U.1.ι ≫ f) inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at hfg ⊢
  have hg' := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hfg
  exact RingHom.FinitePresentation.of_comp_finiteType _ hfg hg'

/-- **Projectivity-preserving morphisms compose**, provided the second is locally of finite
presentation. -/
theorem PreservesProjective.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : PreservesProjective f) (hg : PreservesProjective g) [LocallyOfFinitePresentation g] :
    PreservesProjective (f ≫ g) := fun p hp hlfp ↦ by
  rw [Category.assoc]
  exact hf (g ≫ p) (hg p hp hlfp) inferInstance

/-- The identity preserves projectivity. -/
theorem preservesProjective_id (X : Scheme.{u}) : PreservesProjective (𝟙 X) := fun p hp _ ↦ by
  rwa [Category.id_comp]

/-- A projectivity-preserving morphism to a projective scheme over `A` of finite presentation is
projective relative to every separated base. -/
theorem PreservesProjective.isRelativelyProjective {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : PreservesProjective f) (g : Y ⟶ Spec (.of A)) [IsSeparated g]
    (hg : IsProjectiveOver g) [LocallyOfFinitePresentation g] :
    DeJong.IsRelativelyProjective g f :=
  Projectivity.isRelativelyProjective_of_isProjectiveOver g f (hf g hg inferInstance)

end FinitePresentation

section Locus

/-- **BND's shrinking step, with specialization** (`Blowups.exists_open_isClosed_locus`, the fix
of `ERRATA.md` DJA-T33). In the situation of `Blowups.exists_open_isClosed_locus` (a henselian
local ring `A` with separably closed residue field, `g : C ⟶ Spec A` separated, `φ : U ⟶ M` étale
over `A`, `i : Spec Ā ⟶ M` a closed immersion over the closed subscheme `Spec Ā ⊆ Spec A`, `x ∈ U`
on the closed fibre with `φ x ∈ i(Spec Ā)`), the open `U₀` can be chosen so that, moreover,
**every point of the closed locus `U₀ ∩ φ⁻¹(i(Spec Ā))` specializes to `x`**: the locus is the
image of a section of `φ⁻¹(i(Spec Ā)) ⟶ Spec Ā` through `x`, and every point of the local scheme
`Spec Ā` specializes to its closed point. -/
theorem exists_open_isClosed_locus_specializes {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g]
    (U : C.Opens) {M : Scheme.{u}} (q : M ⟶ Spec (.of A)) (φ : U.toScheme ⟶ M) [Etale φ]
    (hφ : φ ≫ q = U.ι ≫ g) {Ā : Type u} [CommRing Ā] [Algebra A Ā]
    (hĀ : Function.Surjective (algebraMap A Ā)) (i : Spec (.of Ā) ⟶ M) [IsClosedImmersion i]
    (hi : i ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A Ā)))
    (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A) (hxi : φ ⟨x, hxU⟩ ∈ Set.range i) :
    ∃ U₀ : C.Opens, U₀ ≤ U ∧ x ∈ U₀ ∧
      IsClosed ((U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i)) ∧
      (∀ y ∈ (U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i), g y = closedPoint A → y = x) ∧
      ∀ y ∈ (U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i), y ⤳ x := by
  classical
  let pZ : pullback i φ ⟶ Spec (.of Ā) := pullback.fst i φ
  let jZ : pullback i φ ⟶ U.toScheme := pullback.snd i φ
  obtain ⟨a, ha⟩ := hxi
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := φ) a
    (⟨x, hxU⟩ : U) ha
  have : Nontrivial Ā := PrimeSpectrum.nontrivial a
  have : IsLocalHom (algebraMap A Ā) := hĀ.isLocalHom _
  have : HenselianLocalRing Ā := henselianLocalRing_of_surjective _ hĀ
  have : IsSepClosed (ResidueField Ā) := isSepClosed_residueField_of_surjective _ hĀ
  -- the point `z` lies over the closed point of `Spec Ā`
  have hz : pZ z = closedPoint Ā := by
    apply PrimeSpectrum.comap_injective_of_surjective (algebraMap A Ā) hĀ
    have h1 : (Spec.map (CommRingCat.ofHom (algebraMap A Ā))) (pZ z) = closedPoint A := by
      rw [← hi, Scheme.Hom.comp_apply]
      change q (i (pullback.fst i φ z)) = _
      rw [hz1, ha, ← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]
      exact hx
    refine h1.trans (PrimeSpectrum.ext ?_)
    exact (IsLocalRing.maximalIdeal_comap (algebraMap A Ā)).symm
  -- separatedness of `pZ`
  have : IsSeparated (pZ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ā))) := by
    have h : pZ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ā)) = jZ ≫ U.ι ≫ g := by
      rw [← hi, ← Category.assoc, pullback.condition, Category.assoc, hφ]
    rw [h]
    infer_instance
  have : IsSeparated pZ := IsSeparated.of_comp pZ (Spec.map (CommRingCat.ofHom (algebraMap A Ā)))
  obtain ⟨s, hs, hsz⟩ := exists_section_of_etale pZ z hz
  have hclopen : IsClopen (Set.range s) := DeJong.isClopen_range_of_comp_eq_id pZ s hs
  have hinj : Function.Injective jZ := jZ.isClosedEmbedding.injective
  -- the bad part of the locus
  let Bad : Set U.toScheme := jZ '' (Set.range s)ᶜ
  have hBad : IsClosed Bad := jZ.isClosedEmbedding.isClosedMap _ hclopen.isOpen.isClosed_compl
  let U₀' : U.toScheme.Opens := ⟨Badᶜ, hBad.isOpen_compl⟩
  have hnotBad : ∀ b, jZ (s b) ∉ Bad := by
    rintro b ⟨z', hz', hzz'⟩
    exact hz' ⟨b, (hinj hzz').symm⟩
  have heq : ((U.ι ''ᵁ U₀' : C.Opens) : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i) =
      Set.range (s ≫ jZ ≫ U.ι) := by
    ext y
    constructor
    · rintro ⟨⟨y', hy', rfl⟩, ⟨y'', ⟨a', ha'⟩, hy''⟩⟩
      have : y'' = y' := U.ι.isOpenEmbedding.injective hy''
      subst this
      obtain ⟨z', hz'1, hz'2⟩ := Scheme.Pullback.exists_preimage_pullback a' y'' ha'
      by_cases hz' : z' ∈ Set.range s
      · obtain ⟨b, rfl⟩ := hz'
        exact ⟨b, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact congrArg _ hz'2⟩
      · exact absurd ⟨z', hz', hz'2⟩ hy'
    · rintro ⟨b, rfl⟩
      refine ⟨⟨jZ (s b), hnotBad b, rfl⟩, jZ (s b), ⟨pZ (s b), ?_⟩, rfl⟩
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hcomp : (s ≫ jZ ≫ U.ι) ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A Ā)) := by
    rw [Category.assoc, Category.assoc, ← hφ, ← Category.assoc jZ, ← pullback.condition,
      Category.assoc, hi, ← Category.assoc, hs, Category.id_comp]
  have hclosed : (s ≫ jZ ≫ U.ι) (closedPoint Ā) = x := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hsz, hz2]
    rfl
  refine ⟨U.ι ''ᵁ U₀', ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    rw [← hz2, ← hsz]
    exact hnotBad _
  · rw [heq]
    have : IsProper ((s ≫ jZ ≫ U.ι) ≫ g) := by
      rw [hcomp]
      have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap A Ā))) :=
        IsClosedImmersion.spec_of_surjective _ hĀ
      infer_instance
    exact isClosed_range_of_isProper_comp (s ≫ jZ ≫ U.ι) g
  · rw [heq]
    rintro _ ⟨b, rfl⟩ hb
    have hb' : b = closedPoint Ā := by
      apply PrimeSpectrum.comap_injective_of_surjective (algebraMap A Ā) hĀ
      have h1 : (Spec.map (CommRingCat.ofHom (algebraMap A Ā))) b = closedPoint A := by
        rw [← hcomp, Scheme.Hom.comp_apply]
        exact hb
      refine h1.trans (PrimeSpectrum.ext ?_)
      exact (IsLocalRing.maximalIdeal_comap (algebraMap A Ā)).symm
    rw [hb']
    exact hclosed
  · rw [heq]
    rintro _ ⟨b, rfl⟩
    rw [← hclosed]
    exact (Blowups.specializes_closedPoint b).map (s ≫ jZ ≫ U.ι).continuous

end Locus

section Transport

variable {A : Type u} [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]

/-- **Projective transport of an affine chart blow-up** (`thm:sm-sep-proj-transport`; BND's
`Blowups.exists_transport` with the projectivity of lane T45C). Let `A` be a henselian local ring
with separably closed residue field, `g : C ⟶ Spec A` separated, `φ : U ⟶ Spec AM` an étale
`A`-morphism from an open of `C`, `I ⊆ AM` a finitely generated ideal with `A → AM/I` surjective
and `Bl_I(Spec AM)` strictly semi-stable over `A`. For every point `x ∈ U` of the closed fibre with
`φ x ∈ V(I)` there are an affine open `x ∈ U₀ ⊆ U`, an open `W ∌ x` whose complement lies in
`φ⁻¹V(I)` and contains no other point of the closed fibre, and `β : C' ⟶ C` which is the base change
of `Bl_I(Spec AM)` over `U₀` and an isomorphism over `W`, as in `Blowups.exists_transport`; if
moreover `C` is integral, **`β` preserves projectivity**: it is the blow-up of an ideal sheaf of
finite type (lane T45C's `BlowupProjective.isProjectiveOver_extensionHom`). -/
theorem exists_transport_projective {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g]
    (U : C.Opens) {AM : Type u} [CommRing AM] [IsDomain AM] [Algebra A AM] (IM : Ideal AM)
    (hIM : IM.FG) (qM : Spec (.of AM) ⟶ Spec (.of A))
    (hqM : qM = Spec.map (CommRingCat.ofHom (algebraMap A AM)))
    (hĀ : Function.Surjective (algebraMap A (AM ⧸ IM)))
    (hM' : IsStrictlySemistable (affineBlowupStructure IM ≫ qM) ⊤)
    (φ : U.toScheme ⟶ Spec (.of AM)) [Etale φ] (hφ : φ ≫ qM = U.ι ≫ g)
    (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A)
    (hxi : φ ⟨x, hxU⟩ ∈ Set.range (BlowupProjective.quotientMap IM)) :
    ∃ (U₀ : C.Opens) (hU₀ : U₀ ≤ U) (W : C.Opens) (C' : Scheme.{u}) (β : C' ⟶ C)
      (j : pullback (affineBlowupStructure IM) (C.homOfLE hU₀ ≫ φ) ⟶ C')
      (k : W.toScheme ⟶ C'),
      x ∈ U₀ ∧ x ∉ W ∧
      (W : Set C)ᶜ ⊆ U.ι '' (φ ⁻¹' Set.range (BlowupProjective.quotientMap IM)) ∧
      (∀ y ∉ W, g y = closedPoint A → y = x) ∧ IsOpenImmersion j ∧ IsOpenImmersion k ∧
      j ≫ β = pullback.snd (affineBlowupStructure IM) (C.homOfLE hU₀ ≫ φ) ≫ U₀.ι ∧
      k ≫ β = W.ι ∧ (∀ y : C', y ∈ Set.range j ∨ y ∈ Set.range k) ∧ IsProper β ∧
      IsIso (β ∣_ W) ∧ (IsStrictlySemistable g ⊤ → IsStrictlySemistable (β ≫ g) ⊤) ∧
      (IsIntegral C → IsModification (affineBlowupStructure IM) →
        (∀ m : affineBlowup IM, ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B)
          (_ : IsIntegrallyClosed B) (j : Spec (.of B) ⟶ affineBlowup IM)
          (_ : IsOpenImmersion j), m ∈ Set.range j) →
        (∃ y : C, g y ∉ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (AM ⧸ IM))))) →
        IsModification β) ∧
      (IsIntegral C → PreservesProjective β) := by
  have : IsClosedImmersion (BlowupProjective.quotientMap IM) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hi : (BlowupProjective.quotientMap IM) ≫ qM =
      Spec.map (CommRingCat.ofHom (algebraMap A (AM ⧸ IM))) := by
    rw [hqM]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨U₁, hU₁, hxU₁, hcl, huniq, hspec⟩ := exists_open_isClosed_locus_specializes g U qM φ hφ
    hĀ (BlowupProjective.quotientMap IM) hi x hxU hx hxi
  set Z : Set C := (U₁ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range (BlowupProjective.quotientMap IM))
    with hZ
  -- an affine neighbourhood of `x` in `U₁`; it contains the locus
  obtain ⟨V₀, hV₀, hxV₀, hV₀U₁⟩ := LocalUniformization.exists_affine_le U₁ hxU₁
  have hZV₀ : Z ⊆ V₀ := fun y hy ↦ (hspec y hy).mem_open V₀.isOpen hxV₀
  have hV₀U : V₀ ≤ U := fun y hy ↦ hU₁ (hV₀U₁ hy)
  have hxZ : x ∈ Z := ⟨hxU₁, ⟨x, hxU⟩, hxi, rfl⟩
  let W : C.Opens := ⟨Zᶜ, hcl.isOpen_compl⟩
  let φ₀ : V₀.toScheme ⟶ Spec (.of AM) := C.homOfLE hV₀U ≫ φ
  have hφ₀ : φ₀ ≫ qM = V₀.ι ≫ g := by
    rw [Category.assoc, hφ, ← Category.assoc, Scheme.homOfLE_ι]
  -- the locus seen from `V₀`
  have hloc : V₀.ι '' (φ₀ ⁻¹' Set.range (BlowupProjective.quotientMap IM)) = Z := by
    rw [CofinalProjective.image_preimage_homOfLE hV₀U φ]
    ext y
    constructor
    · rintro ⟨hyV, hy⟩
      exact ⟨hV₀U₁ hyV, hy⟩
    · intro hy
      exact ⟨hZV₀ hy, hy.2⟩
  have hzero : PrimeSpectrum.zeroLocus (IM : Set AM) =
      Set.range (BlowupProjective.quotientMap IM) :=
    (BlowupProjective.range_quotientMap IM).symm
  have hcov : V₀ ⊔ W = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    by_cases hy : y ∈ Z
    · exact Or.inl (hZV₀ hy)
    · exact Or.inr hy
  have hWO : V₀.ι ⁻¹ᵁ W ≤ φ₀ ⁻¹ᵁ affineBlowupCenterComplement IM := by
    intro v hv hvZ
    apply hv
    rw [← hloc]
    refine ⟨v, ?_, rfl⟩
    rw [← hzero]
    exact hvZ
  have : IsIso (affineBlowupStructure IM ∣_ affineBlowupCenterComplement IM) :=
    affineBlowupStructure_centerComplement_isIso IM
  have : IsIso (pullback.snd (affineBlowupStructure IM) φ₀ ∣_ (V₀.ι ⁻¹ᵁ W)) :=
    isIso_pullback_snd_restrict_of_le (affineBlowupStructure IM) φ₀ _ hWO
  have : IsProper (affineBlowupStructure IM) := affineBlowupStructure_isProper _ hIM
  have hT : IsClosed (V₀.ι '' (φ₀ ⁻¹' PrimeSpectrum.zeroLocus (IM : Set AM))) := by
    rw [hzero, hloc]
    exact hcl
  refine ⟨V₀, hV₀U, W, extension W (pullback.snd (affineBlowupStructure IM) φ₀),
    extensionHom W (pullback.snd (affineBlowupStructure IM) φ₀), extensionι₁ W _, extensionι₂ W _,
    hxV₀, fun h ↦ h hxZ, fun y hy ↦ ?_, fun y hy ↦ huniq y (not_not.mp hy), inferInstance,
    inferInstance, extensionι₁_extensionHom W _, extensionι₂_extensionHom W _,
    transport_cover φ₀ (affineBlowupStructure IM) W,
    isProper_transport φ₀ (affineBlowupStructure IM) W hcov, inferInstance,
    fun hC ↦ isStrictlySemistable_transport_top φ₀ (affineBlowupStructure IM) W g qM hφ₀ hM' hC,
    ?_, ?_⟩
  · exact (not_not.mp hy).2
  · intro hCint hβ₀ hcovM hy
    have : IsReduced (pullback (affineBlowupStructure IM) φ₀) :=
      isReduced_of_etale_of_cover (pullback.fst (affineBlowupStructure IM) φ₀) hcovM
    obtain ⟨y, hy⟩ := hy
    have hyW : y ∈ W := by
      intro hyZ
      obtain ⟨y', ⟨a, ha⟩, rfl⟩ := hyZ.2
      apply hy
      refine ⟨a, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hi, Scheme.Hom.comp_apply, ha, ← Scheme.Hom.comp_apply, hφ,
        Scheme.Hom.comp_apply]
    exact isModification_transport φ₀ (affineBlowupStructure IM) W hcov ⟨x, hxV₀⟩ ⟨y, hyW⟩
  · intro hCint E _ p hp hlfp
    have := hlfp
    exact BlowupProjective.isProjectiveOver_extensionHom IM hV₀ φ₀ W hIM hcov hWO hT p hp

end Transport

section ChartTransport

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [HenselianLocalRing A]
  [IsSepClosed (ResidueField A)]

attribute [local instance] LocusBlowup.fact_mul_ne_zero

/-- **Projective transport of the smooth chart blow-up** `Bl_{(π, T - a)}` (BND's
`Blowups.exists_smoothBlowup_transport` with the preservation of projectivity; Temkin, proof of
Lemma 4.3.2, separation step, T:3027–3030). -/
theorem exists_smoothBlowup_transport_projective (π a : A) [Fact (π ≠ 0)]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g] (hC : IsStrictlySemistable g ⊤)
    (U : C.Opens) (φ : U.toScheme ⟶ Spec (.of A[X])) [Etale φ]
    (hφ : φ ≫ smoothModel A = U.ι ≫ g) (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A)
    (hxi : φ ⟨x, hxU⟩ ∈ Set.range (smoothLocus π a)) :
    ∃ (U₀ : C.Opens) (hU₀ : U₀ ≤ U) (W : C.Opens) (C' : Scheme.{u}) (β : C' ⟶ C)
      (j : pullback (affineBlowupStructure (smoothCenter π a)) (C.homOfLE hU₀ ≫ φ) ⟶ C')
      (k : W.toScheme ⟶ C'),
      x ∈ U₀ ∧ x ∉ W ∧ (W : Set C)ᶜ ⊆ U.ι '' (φ ⁻¹' Set.range (smoothLocus π a)) ∧
      (∀ y ∉ W, g y = closedPoint A → y = x) ∧ IsOpenImmersion j ∧ IsOpenImmersion k ∧
      j ≫ β = pullback.snd (affineBlowupStructure (smoothCenter π a)) (C.homOfLE hU₀ ≫ φ) ≫
        U₀.ι ∧ k ≫ β = W.ι ∧
      (∀ y : C', y ∈ Set.range j ∨ y ∈ Set.range k) ∧ IsProper β ∧ IsIso (β ∣_ W) ∧
      IsStrictlySemistable (β ≫ g) ⊤ ∧ (IsIntegral C → IsModification β) ∧
      (IsIntegral C → PreservesProjective β) := by
  obtain ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
      hss, hmod, hproj⟩ :=
    exists_transport_projective g U (smoothCenter π a) (smoothCenter_fg π a) (smoothModel A) rfl
      (algebraMap_smoothLocus_surjective π a) (smoothBlowup_isStrictlySemistable π a) φ hφ x hxU
      hx hxi
  refine ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
    hss hC, fun hCint ↦ hmod hCint (smoothBlowup_isModification π a) (smoothBlowup_cover π a) ?_,
    hproj⟩
  have : DeJong.IsNodalCurve g := hC.isNodalCurve
  have : Nonempty C := ⟨x⟩
  refine exists_not_mem_range_of_flat g (Fact.out : π ≠ 0) ?_
  rw [IsScalarTower.algebraMap_apply A A[X], Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact C_mem_smoothCenter π a

/-- **Projective transport of the node-locus blow-up** `Bl_{(u, v, π)}` of `A[u,v]/(uv - π²b)`
(lane T45C's `Gluing.LocusBlowup`; the projective replacement of BND's
`Blowups.exists_nodeBlowup_transport`, whose centre `V(u, π)` is a curve). -/
theorem exists_locusBlowup_transport_projective (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g] (hC : IsStrictlySemistable g ⊤)
    (U : C.Opens) (φ : U.toScheme ⟶ Spec (.of (Node A (π * (π * b))))) [Etale φ]
    (hφ : φ ≫ nodeModel (π * (π * b)) = U.ι ≫ g) (x : C) (hxU : x ∈ U)
    (hx : g x = closedPoint A) (hxi : φ ⟨x, hxU⟩ ∈ Set.range (nodeLocus π (π * b))) :
    ∃ (U₀ : C.Opens) (hU₀ : U₀ ≤ U) (W : C.Opens) (C' : Scheme.{u}) (β : C' ⟶ C)
      (j : pullback (affineBlowupStructure (LocusBlowup.locusIdeal π b)) (C.homOfLE hU₀ ≫ φ) ⟶ C')
      (k : W.toScheme ⟶ C'),
      x ∈ U₀ ∧ x ∉ W ∧ (W : Set C)ᶜ ⊆ U.ι '' (φ ⁻¹' Set.range (nodeLocus π (π * b))) ∧
      (∀ y ∉ W, g y = closedPoint A → y = x) ∧ IsOpenImmersion j ∧ IsOpenImmersion k ∧
      j ≫ β = pullback.snd (affineBlowupStructure (LocusBlowup.locusIdeal π b))
        (C.homOfLE hU₀ ≫ φ) ≫ U₀.ι ∧ k ≫ β = W.ι ∧
      (∀ y : C', y ∈ Set.range j ∨ y ∈ Set.range k) ∧ IsProper β ∧ IsIso (β ∣_ W) ∧
      IsStrictlySemistable (β ≫ g) ⊤ ∧ (IsIntegral C → IsModification β) ∧
      (IsIntegral C → PreservesProjective β) := by
  obtain ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
      hss, hmod, hproj⟩ :=
    exists_transport_projective g U (LocusBlowup.locusIdeal π b) (LocusBlowup.locusIdeal_fg π b)
      (nodeModel (π * (π * b))) rfl (algebraMap_nodeLocus_surjective π (π * b))
      (LocusBlowup.locusBlowup_isStrictlySemistable π b) φ hφ x hxU hx hxi
  refine ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
    hss hC, fun hCint ↦ hmod hCint (LocusBlowup.locusBlowup_isModification π b)
      (LocusBlowup.locusBlowup_cover π b) ?_, hproj⟩
  have : DeJong.IsNodalCurve g := hC.isNodalCurve
  have : Nonempty C := ⟨x⟩
  refine exists_not_mem_range_of_flat g (Fact.out : π ≠ 0) ?_
  rw [IsScalarTower.algebraMap_apply A (Node A (π * (π * b))), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact LocusBlowup.algebraMap_mem_locusIdeal π b

end ChartTransport

section PiLift

variable {A : Type u} [CommRing A] [IsDomain A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]

attribute [local instance] LocusBlowup.fact_mul_ne_zero

/-- The lift `(u/π, v/π) ↦ (c, d)` of a section into the `π`-chart
`A[u/π, v/π]/((u/π)(v/π) - b)` of `Bl_{(u, v, π)}(A[u,v]/(uv - π²b))`. -/
def piLift (c d : A) (h : c * d = b) :
    Spec (.of A) ⟶ affineBlowup (LocusBlowup.locusIdeal π b) :=
  Spec.map (CommRingCat.ofHom (nodePoint b c d h).toRingHom) ≫ LocusBlowup.piChartInclusion π b

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem piLift_mul_eq {c d : A} (h : c * d = b) : π * c * (π * d) = π * (π * b) := by
  rw [← h]; ring

/-- The original coordinates on the `π`-chart: `u = π (u/π)`, `v = π (v/π)`. -/
theorem piChart_originalMap_coordinate (i : Fin 2) :
    LocusBlowup.chartOriginalMap (LocusBlowup.locusIdeal π b) (algebraMap A _ π)
      (LocusBlowup.piEvaluation π b) (LocusBlowup.piEvaluation_injective π b)
      (LocusBlowup.piEvaluation_range π b) (coordinate (π * (π * b)) i) =
      algebraMap A (Node A b) π * coordinate b i := by
  apply LocusBlowup.piEvaluation_injective π b
  rw [LocusBlowup.ev_chartOriginalMap, map_mul, AlgHom.commutes]
  have hπ := LocusBlowup.fπ_ne_zero π b
  fin_cases i
  · change _ = algebraMap A _ π * LocusBlowup.piEvaluation π b (coordinate b 0)
    rw [LocusBlowup.piEvaluation_coordinate0]
    change LocusBlowup.fu π b = LocusBlowup.fπ π b * (LocusBlowup.fu π b / LocusBlowup.fπ π b)
    field_simp
  · change _ = algebraMap A _ π * LocusBlowup.piEvaluation π b (coordinate b 1)
    rw [LocusBlowup.piEvaluation_coordinate1]
    change LocusBlowup.fv π b = LocusBlowup.fπ π b * (LocusBlowup.fv π b / LocusBlowup.fπ π b)
    field_simp

/-- **The lift of the section `(u, v) ↦ (πc, πd)`** to the `π`-chart. -/
theorem piLift_comp (c d : A) (h : c * d = b) :
    piLift π b c d h ≫ affineBlowupStructure (LocusBlowup.locusIdeal π b) =
      Spec.map (CommRingCat.ofHom (nodePoint (π * (π * b)) (π * c) (π * d)
        (piLift_mul_eq π b h)).toRingHom) := by
  rw [piLift, Category.assoc, LocusBlowup.piChartInclusion, LocusBlowup.chartInclusion_structure,
    ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext ?_
  have : (nodePoint b c d h).comp (LocusBlowup.chartOriginalMap (LocusBlowup.locusIdeal π b)
      (algebraMap A _ π) (LocusBlowup.piEvaluation π b) (LocusBlowup.piEvaluation_injective π b)
      (LocusBlowup.piEvaluation_range π b)) =
      nodePoint (π * (π * b)) (π * c) (π * d) (piLift_mul_eq π b h) := by
    apply node_algHom_ext
    · rw [AlgHom.comp_apply, piChart_originalMap_coordinate, map_mul, AlgHom.commutes]
      simp
    · rw [AlgHom.comp_apply, piChart_originalMap_coordinate, map_mul, AlgHom.commutes]
      simp
  exact congrArg AlgHom.toRingHom this

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The closed point of the node point `(u, v) ↦ (c, d)` lies in `D(u)` if `c` is a unit. -/
theorem specMap_nodePoint_closedPoint_mem_coordinateOpen₀ [IsLocalRing A] (a c d : A)
    (h : c * d = a) (hc : IsUnit c) :
    Spec.map (CommRingCat.ofHom (nodePoint a c d h).toRingHom) (closedPoint A) ∈
      Geometry.NodeFamilySmooth.coordinateOpen a 0 := by
  change coordinate a 0 ∉ (Spec.map (CommRingCat.ofHom (nodePoint a c d h).toRingHom)
    (closedPoint A)).asIdeal
  rw [specMap_nodePoint_closedPoint_asIdeal, Ideal.mem_comap]
  change nodePoint a c d h (coordinate a 0) ∉ maximalIdeal A
  rw [nodePoint_coordinate0]
  exact (mem_maximalIdeal _).not.mpr (not_not.mpr hc)

end PiLift

end DeJongAlterations.StableModification.Gluing.SeparationProjective
