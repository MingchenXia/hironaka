/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.Connected
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalCore
import DeJongAlterations.StableModification.BlowDown.NormalizationCurve
import DeJongAlterations.StableModification.DeJong.BaseStepProjective
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import DeJongAlterations.Geometry.ProjectiveIdentity

/-!
# Zariski connectedness for the closure of a closed subset of a fibre

Let `V` be a valuation ring with finitely many primes such that `Frac (V ⧸ 𝔭)` is separably
closed for every prime `𝔭`, and `p : X → Spec V` projective. Let `F` be a preconnected subset of
the fibre `p⁻¹(𝔭)` which is closed in that fibre. Then **the closure of `F` meets every fibre
`p⁻¹(𝔮)` in a preconnected set** (`isPreconnected_closure_inter_preimage`, blueprint
`prop:sm-connbirh-closure`, chapter `sm-cohomology-connected-birational-height.tex`).

This is the "`S`-fibre" input of Zariski's connectedness theorem for a birational morphism
`π : B → Y` onto a normal curve over a valuation ring of height `≥ 2` (M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, proof of Lemma 4.4.2, T:3133;
ERRATA T54, DJA-O13): applied to `F = π⁻¹(y)` for a point `y` of the modification locus, it
controls how the closure of `π⁻¹(y)` meets the fibres over the specializations of `y`
(blueprint remark `rem:sm-connbir-generizations`).

## The argument

Give `closure F` its reduced induced structure `X_F` (`Geometry.ReducedClosedSubscheme`). All its
points lie over `V(𝔭)`, so its structure map factors through `Spec (V ⧸ 𝔭)`
(`exists_comp_eq_of_forall_le`, as `X_F` is reduced), and `X_F` is projective over the valuation
ring `V ⧸ 𝔭` (`isProjectiveOver_of_comp_surjective`). Its generic fibre is `F`, which is dense, so
the functions of `X_F` have no `V ⧸ 𝔭`-torsion and `X_F` is flat over `V ⧸ 𝔭`
(`flat_of_dense_preimage_bot`). Lane COH3C's Zariski connectedness theorem over a valuation ring
(`Cohomology.Connected.isPreconnected_fiber_of_isProjectiveOver`) applies.

## Main results

* `isProjectiveOver_of_comp_surjective`, `toSpecΓ_comp_Spec_map_structureCoeff`,
  `exists_comp_eq_of_forall_le`, `flat_of_dense_preimage_bot`, `isSepClosed_quotient`:
  auxiliary statements.
* `isPreconnected_closure_inter_preimage` (blueprint `prop:sm-connbirh-closure`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Projective

/-- **Projectivity over a quotient.** If `φ : A → B` is surjective and `g : X → Spec B` becomes
projective over `A` after composing with the closed immersion `Spec B → Spec A`, then `g` is
projective: a closed immersion `X ↪ ℙⁿ_A` over `Spec B` lifts to `X ↪ ℙⁿ_B = ℙⁿ_A ×_A B`. -/
theorem isProjectiveOver_of_comp_surjective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of B))
    (h : IsProjectiveOver (g ≫ Spec.map (CommRingCat.ofHom φ))) : IsProjectiveOver g := by
  obtain ⟨n, i, hi, hcomp⟩ := h
  have H := Geometry.ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap φ n
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  have : IsClosedImmersion (Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap φ n) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip this
  let j : X ⟶ projectiveSpace B n := H.lift i g hcomp
  have hj₁ : j ≫ Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap φ n = i :=
    H.lift_fst _ _ _
  have hj₂ : j ≫ projectiveSpaceStructure B n = g := H.lift_snd _ _ _
  have : IsClosedImmersion
      (j ≫ Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap φ n) := by
    rw [hj₁]
    exact hi
  exact ⟨n, j, IsClosedImmersion.of_comp_isClosedImmersion j
    (Geometry.BlowupProjectiveEmbedding.projectiveCoefficientMap φ n), hj₂⟩

end Projective

section Factor

variable {R : Type u} [CommRing R]

/-- A morphism `h : T → Spec R` is `T → Spec Γ(T, 𝒪_T) → Spec R`, the second map induced by the
structure coefficients `R → Γ(T, 𝒪_T)` of `h`. -/
theorem toSpecΓ_comp_Spec_map_structureCoeff {T : Scheme.{u}}
    (h : T ⟶ Spec (CommRingCat.of R)) :
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (structureCoeff h)) = h := by
  have e : CommRingCat.ofHom (structureCoeff h) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop := rfl
  rw [e, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **Factoring through a closed subscheme of the base.** A morphism `h : T → Spec R` from a reduced
quasi-compact scheme whose image lies in `V(I)` factors through `Spec (R ⧸ I)`: the constants of
`I` vanish at every point of `T`, hence are nilpotent, hence zero, in `Γ(T, 𝒪_T)`. -/
theorem exists_comp_eq_of_forall_le {T : Scheme.{u}} [IsReduced T] [CompactSpace T]
    (h : T ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (hI : ∀ t : T, I ≤ (h t).asIdeal) :
    ∃ g : T ⟶ Spec (CommRingCat.of (R ⧸ I)),
      g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = h := by
  have hker : ∀ a ∈ I, structureCoeff h a = 0 := fun a ha =>
    (ConnectedBirational.isNilpotent_structureCoeff_of_forall_mem h
      (fun t => hI t ha)).eq_zero
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I (structureCoeff h) hker)),
    ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  exact toSpecΓ_comp_Spec_map_structureCoeff h

end Factor

section Flat

variable {W : Type u} [CommRing W]

/-- The non-vanishing locus of a constant `c` of `Spec W` on `T`. -/
theorem mem_basicOpen_structureCoeff_iff {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of W))
    (c : W) (t : T) : t ∈ T.basicOpen (structureCoeff g c) ↔ c ∉ (g t).asIdeal := by
  have hpre : T.basicOpen (structureCoeff g c) =
      g ⁻¹ᵁ (Spec (CommRingCat.of W)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of W)).inv c) := by
    rw [Scheme.preimage_basicOpen]
    rfl
  rw [hpre, Scheme.Hom.mem_preimage, basicOpen_eq_of_affine]
  rfl

/-- **Flatness of a reduced scheme with dense generic fibre over a valuation ring.** If `T` is
reduced and the points of `T` over the generic point of `Spec W` are dense, then `g` is flat: a
function `s` with `c s = 0`, `c ≠ 0`, vanishes on the dense open where `c` is invertible, so its
non-vanishing locus is empty and `s = 0`. -/
theorem flat_of_dense_preimage_bot [IsDomain W] [ValuationRing W] {T : Scheme.{u}} [IsReduced T]
    (g : T ⟶ Spec (CommRingCat.of W)) (hd : Dense (g ⁻¹' {(⊥ : PrimeSpectrum W)})) :
    Flat g := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have e : U ≤ g ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hU⟩, hxU, e, ?_⟩
  show (g.appLE ⊤ U e).hom.Flat
  rw [BlowDown.appLE_eq_sectionsRingHom]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)) ?_
  let := (sectionsRingHom (structureCoeff g) (le_top : U ≤ ⊤)).toAlgebra
  change Module.Flat W Γ(T, U)
  rw [ValuationRing.flat_iff_forall_smul_eq_zero]
  intro c hc s hs
  rw [Algebra.smul_def] at hs
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, w ∈ T.basicOpen s := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.mpr fun w hw => h w hw)
  obtain ⟨w', hw'g, hw'O⟩ := hd.exists_mem_open (T.basicOpen s).isOpen ⟨w, hw⟩
  have hw'U : w' ∈ U := T.basicOpen_le s hw'O
  have hc' : w' ∈ T.basicOpen (algebraMap W Γ(T, U) c) := by
    change w' ∈ T.basicOpen ((T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (structureCoeff g c))
    rw [Scheme.basicOpen_res]
    refine ⟨hw'U, (mem_basicOpen_structureCoeff_iff g c w').mpr ?_⟩
    have : g w' = (⊥ : PrimeSpectrum W) := hw'g
    rw [this]
    exact hc
  have hmem : w' ∈ T.basicOpen (algebraMap W Γ(T, U) c * s) := by
    rw [Scheme.basicOpen_mul]
    exact ⟨hc', hw'O⟩
  rw [hs, Scheme.basicOpen_zero] at hmem
  exact hmem

end Flat

section SepClosed

variable {V : Type u} [CommRing V]

/-- The separable closedness hypothesis passes to quotients: `Frac ((V ⧸ 𝔭) ⧸ P)` is
`Frac (V ⧸ Q)` for the preimage `Q` of `P`. -/
theorem isSepClosed_quotient
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal))) (I : Ideal V) (P : PrimeSpectrum (V ⧸ I)) :
    IsSepClosed (FractionRing ((V ⧸ I) ⧸ P.asIdeal)) := by
  let Q := PrimeSpectrum.comap (Ideal.Quotient.mk I) P
  let ψ : V →+* (V ⧸ I) ⧸ P.asIdeal := (Ideal.Quotient.mk P.asIdeal).comp (Ideal.Quotient.mk I)
  have hψ : Function.Surjective ψ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ψ = Q.asIdeal := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  let e : V ⧸ Q.asIdeal ≃+* (V ⧸ I) ⧸ P.asIdeal :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
  have := hsep Q
  exact Connected.isSepClosed_of_ringEquiv
    (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing (V ⧸ Q.asIdeal))
      (L := FractionRing ((V ⧸ I) ⧸ P.asIdeal)) e)

end SepClosed

section Closure

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Zariski connectedness for the closure of a closed subset of a fibre** (blueprint
`prop:sm-connbirh-closure`). Let `V` be a valuation ring with finitely many primes such that
`Frac (V ⧸ 𝔭)` is separably closed for every prime `𝔭`, and `p : X → Spec V` projective. Let `F`
be a preconnected subset of the fibre `p⁻¹(𝔭)` which is closed in it
(`closure F ∩ p⁻¹(𝔭) ⊆ F`). Then `closure F ∩ p⁻¹(𝔮)` is preconnected for every prime `𝔮`. -/
theorem isPreconnected_closure_inter_preimage [Finite (PrimeSpectrum V)]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (hp : IsProjectiveOver p)
    (𝔭 : PrimeSpectrum V) {F : Set X} (hFp : F ⊆ p ⁻¹' {𝔭})
    (hFc : closure F ∩ p ⁻¹' {𝔭} ⊆ F) (hF : _root_.IsPreconnected F) (q : PrimeSpectrum V) :
    _root_.IsPreconnected (closure F ∩ p ⁻¹' {q}) := by
  classical
  -- the reduced closure `X_F` of `F`
  let Z : Closeds X := ⟨closure F, isClosed_closure⟩
  let D := Scheme.IdealSheafData.vanishingIdeal Z
  let ι : D.subscheme ⟶ X := D.subschemeι
  have : IsReduced D.subscheme :=
    Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme Z
  have hrange : Set.range ι = closure F := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
    rfl
  have hmemι : ∀ t, ι t ∈ closure F := fun t => hrange ▸ Set.mem_range_self t
  let f₀ : D.subscheme ⟶ Spec (CommRingCat.of V) := ι ≫ p
  have hf₀ : IsProjectiveOver f₀ := DeJong.IsProjectiveOver.comp_isClosedImmersion hp ι
  have : IsProper f₀ := hf₀.isProper
  have : CompactSpace D.subscheme :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := f₀) Set.univ isOpen_univ isCompact_univ⟩
  -- all points of `X_F` lie over `V(𝔭)`
  have hle : ∀ t, 𝔭.asIdeal ≤ (f₀ t).asIdeal := by
    intro t
    have hsub : p '' closure F ⊆ closure {𝔭} :=
      (image_closure_subset_closure_image p.continuous).trans
        (closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hFp hx))
    have h : 𝔭 ⤳ f₀ t := specializes_iff_mem_closure.mpr (hsub ⟨ι t, hmemι t, rfl⟩)
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr h
  -- the valuation ring `W = V ⧸ 𝔭`
  let W := V ⧸ 𝔭.asIdeal
  have : ValuationRing W :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk 𝔭.asIdeal) Ideal.Quotient.mk_surjective
  have : Finite (PrimeSpectrum W) := Finite.of_injective _
    (PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk 𝔭.asIdeal)
      Ideal.Quotient.mk_surjective)
  have hsepW : ∀ P : PrimeSpectrum W, IsSepClosed (FractionRing (W ⧸ P.asIdeal)) :=
    isSepClosed_quotient hsep 𝔭.asIdeal
  obtain ⟨g, hg⟩ := exists_comp_eq_of_forall_le f₀ 𝔭.asIdeal hle
  let m : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔭.asIdeal))
  have hminj : Function.Injective m :=
    PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  have hmbot : m (⊥ : PrimeSpectrum W) = 𝔭 := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk 𝔭.asIdeal) ⊥ = 𝔭.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hgm : ∀ t, m (g t) = f₀ t := fun t => by rw [← hg]; rfl
  have hgproj : IsProjectiveOver g :=
    isProjectiveOver_of_comp_surjective _ Ideal.Quotient.mk_surjective g (by rw [hg]; exact hf₀)
  -- the generic fibre of `X_F` is `F`
  have hgen_eq : g ⁻¹' {(⊥ : PrimeSpectrum W)} = ι ⁻¹' F := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro ht
      have h𝔭 : p (ι t) = 𝔭 := by
        rw [← hmbot, ← ht, hgm]
        rfl
      exact hFc ⟨hmemι t, h𝔭⟩
    · intro ht
      apply hminj
      rw [hmbot, hgm]
      exact hFp ht
  have hdense : Dense (g ⁻¹' {(⊥ : PrimeSpectrum W)}) := by
    rw [hgen_eq, dense_iff_inter_open]
    rintro O hO ⟨t, htO⟩
    obtain ⟨O', hO', rfl⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.mp hO
    obtain ⟨x, hxO', hxF⟩ := mem_closure_iff.mp (hmemι t) O' hO' htO
    obtain ⟨t', rfl⟩ : x ∈ Set.range ι := hrange ▸ subset_closure hxF
    exact ⟨t', hxO', hxF⟩
  have : Flat g := flat_of_dense_preimage_bot g hdense
  have hgen : _root_.IsPreconnected (g ⁻¹' {(⊥ : PrimeSpectrum W)}) := by
    rw [hgen_eq, ← ι.isClosedEmbedding.isInducing.isPreconnected_image,
      Set.image_preimage_eq_of_subset (hrange ▸ subset_closure)]
    exact hF
  have key := Connected.isPreconnected_fiber_of_isProjectiveOver hsepW g hgproj hgen
  -- the fibre over `q`
  have himg : closure F ∩ p ⁻¹' {q} = ι '' (f₀ ⁻¹' {q}) := by
    ext x
    constructor
    · rintro ⟨hx, hxq⟩
      obtain ⟨t, rfl⟩ : x ∈ Set.range ι := hrange ▸ hx
      exact ⟨t, hxq, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨hmemι t, ht⟩
  rw [himg]
  by_cases hq : ∃ Q, m Q = q
  · obtain ⟨Q, rfl⟩ := hq
    have hpre : f₀ ⁻¹' {m Q} = g ⁻¹' {Q} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hgm, hminj.eq_iff]
    rw [hpre]
    exact (key Q).image _ ι.continuous.continuousOn
  · have hpre : f₀ ⁻¹' {q} = ∅ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro ht
      exact hq ⟨g t, by rw [hgm, ht]⟩
    rw [hpre, Set.image_empty]
    exact isPreconnected_empty

end Closure

end

end DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight
