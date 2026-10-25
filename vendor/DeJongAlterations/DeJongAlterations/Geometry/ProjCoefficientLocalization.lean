/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.ProjStructureMap
import DeJongAlterations.Geometry.AffineBlowupIsomorphism
import DeJongAlterations.Algebra.HomogeneousCoefficientLocalization
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.Localization.Ideal

/-!
# Coefficient localization of the native projective spectrum

An actual graded map which is ordinary localization at a degree-zero element induces
the canonical open immersion on native projective spectra, with its actual structure maps.
-/

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization

set_option autoImplicit false

namespace DeJongAlterations.Geometry.ProjCoefficientLocalization

noncomputable section

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  [Algebra A B] (f : 𝒜 →+*ᵍ ℬ) (s : 𝒜 0)
  [IsLocalization.Away (s : A) B] (hcompat : f.toRingHom = algebraMap A B)

include s hcompat

/-- Ordinary coefficient localization itself supplies the irrelevant-ideal containment needed
by the native `Proj.map`, with no additional geometric hypothesis. -/
theorem irrelevant_le_map : irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn b hb
  obtain ⟨k, a, ha, h⟩ :=
    DeJongAlterations.Algebra.HomogeneousCoefficientLocalization.exists_homogeneous_numerator
      f s hcompat hb
  let J := ((irrelevant 𝒜).map f).toIdeal
  have hmul : b * f (s : A) ^ k ∈ J := by
    rw [h]
    exact Ideal.mem_map_of_mem f.toRingHom
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)
  have hsunit : IsUnit (f (s : A)) := by
    change IsUnit (f.toRingHom (s : A))
    rw [hcompat]
    exact IsLocalization.Away.algebraMap_isUnit (S := B) (s : A)
  obtain ⟨u, hu⟩ := hsunit.pow k
  change b ∈ J
  have hmem : b * (u : B) ∈ J := by rw [hu]; exact hmul
  simpa [mul_assoc] using J.mul_mem_right ((u⁻¹ : Bˣ) : B) hmem

/-- Contraction along the actual coefficient localization is injective on projective points. -/
theorem map_injective (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map f) :
    Function.Injective (Proj.map f hf) := by
  intro p q hpq
  have h : p.asHomogeneousIdeal.toIdeal = q.asHomogeneousIdeal.toIdeal := by
    apply (IsLocalization.orderEmbedding (Submonoid.powers (s : A)) B).injective
    change Ideal.comap (algebraMap A B) p.asHomogeneousIdeal.toIdeal =
      Ideal.comap (algebraMap A B) q.asHomogeneousIdeal.toIdeal
    rw [← hcompat]
    exact congrArg (fun x : Proj 𝒜 => x.asHomogeneousIdeal.toIdeal) hpq
  apply ProjectiveSpectrum.ext
  exact HomogeneousIdeal.ext h

/-- The native projective map has exactly the principal image cut out by the degree-zero
localization element. This statement is about the actual native points, before any chart gluing. -/
theorem map_range (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map f) :
    Set.range (Proj.map f hf) = (Proj.basicOpen 𝒜 (s : A) : Set (Proj 𝒜)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change f (s : A) ∉ y.asHomogeneousIdeal.toIdeal
    have hsunit : IsUnit (f (s : A)) := by
      rw [show f (s : A) = algebraMap A B (s : A) from
        DFunLike.congr_fun hcompat (s : A)]
      exact IsLocalization.Away.algebraMap_isUnit (S := B) (s : A)
    exact fun hs => y.isPrime.ne_top
      (y.asHomogeneousIdeal.toIdeal.eq_top_of_isUnit_mem hs hsunit)
  · intro hx
    let p : PrimeSpectrum A := ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
      rw [PrimeSpectrum.localization_away_comap_range B (s : A)]
      exact hx
    obtain ⟨q, hq⟩ := hp
    have hq' : q.asIdeal.comap f.toRingHom = x.asHomogeneousIdeal.toIdeal := by
      rw [hcompat]
      exact congrArg PrimeSpectrum.asIdeal hq
    have hqmap : (x.asHomogeneousIdeal.map f).toIdeal = q.asIdeal := by
      change Ideal.map f.toRingHom x.asHomogeneousIdeal.toIdeal = q.asIdeal
      rw [← hq', hcompat]
      exact IsLocalization.map_under (Submonoid.powers (s : A)) B q.asIdeal
    let y : Proj ℬ :=
      { asHomogeneousIdeal := x.asHomogeneousIdeal.map f
        isPrime := by rw [hqmap]; exact q.isPrime
        not_irrelevant_le := by
          intro h
          apply x.not_irrelevant_le
          rw [HomogeneousIdeal.irrelevant_le]
          intro n hn a ha
          change a ∈ x.asHomogeneousIdeal.toIdeal
          rw [← hq']
          change f a ∈ q.asIdeal
          rw [← hqmap]
          exact h (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hn (f.2 ha)) }
    refine ⟨y, ?_⟩
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    change Ideal.comap f.toRingHom (x.asHomogeneousIdeal.map f).toIdeal =
      x.asHomogeneousIdeal.toIdeal
    rw [hqmap]
    exact hq'

omit hcompat [Algebra A B] [IsLocalization.Away (s : A) B] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem isOpenImmersion_map_restrict_aux
    (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map f) {d : ℕ} (hd : 0 < d)
    (a : A) (ha : a ∈ 𝒜 d)
    (hlocal : letI := (Away.map f a).toAlgebra
      IsLocalization.Away (fromZeroRingHom 𝒜 (Submonoid.powers a) s)
        (Away ℬ (f a))) :
    IsOpenImmersion ((Proj.map f hf) ∣_ Proj.basicOpen 𝒜 a) := by
  let := (Away.map f a).toAlgebra
  have : IsLocalization.Away (fromZeroRingHom 𝒜 (Submonoid.powers a) s)
      (Away ℬ (f a)) := hlocal
  let eA := Proj.basicOpenIsoSpec 𝒜 a ha hd
  let eB := Proj.basicOpenIsoSpec ℬ (f a) (f.2 ha) hd
  let g := Spec.map (CommRingCat.ofHom (Away.map f a))
  have : IsOpenImmersion g :=
    IsOpenImmersion.of_isLocalization (fromZeroRingHom 𝒜 (Submonoid.powers a) s)
  have heq : (Proj.map f hf) ∣_ Proj.basicOpen 𝒜 a = eB.hom ≫ g ≫ eA.inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 a).ι).mp
    rw [morphismRestrict_ι]
    have h := Proj.awayι_comp_map f hf hd a ha
    change eB.inv ≫ (Proj.basicOpen ℬ (f a)).ι ≫ Proj.map f hf =
      g ≫ eA.inv ≫ (Proj.basicOpen 𝒜 a).ι at h
    have h' := congrArg (fun z => eB.hom ≫ z) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Proj.map_preimage_basicOpen] using h'
  rw [heq]
  infer_instance

/-- The actual graded localization map restricts to an open immersion on every native
positive homogeneous affine chart. The chart localization is derived from the ring hypothesis. -/
theorem isOpenImmersion_map_restrict (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map f)
    {d : ℕ} (hd : 0 < d) (a : A) (ha : a ∈ 𝒜 d) :
    IsOpenImmersion ((Proj.map f hf) ∣_ Proj.basicOpen 𝒜 a) :=
  isOpenImmersion_map_restrict_aux f s hf hd a ha
    (DeJongAlterations.Algebra.HomogeneousCoefficientLocalization.chart_isLocalization
      f s hcompat ha)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Native `Proj.map` for an actual degree-zero coefficient localization is an open immersion. -/
theorem isOpenImmersion_map (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map f) :
    IsOpenImmersion (Proj.map f hf) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsOpenImmersion)
    (fun a : Σ i : PNat, 𝒜 i => Proj.basicOpen 𝒜 a.2)
  · apply Proj.iSup_basicOpen_eq_top
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro i hi a ha
    exact Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨a, ha⟩⟩, rfl⟩
  · intro a
    exact isOpenImmersion_map_restrict f s hcompat hf a.1.2 a.2 a.2.2

/-- The open image of the native localization morphism is its actual degree-zero basic open. -/
theorem map_opensRange (hf : irrelevant ℬ ≤ (irrelevant 𝒜).map f) :
    letI := isOpenImmersion_map f s hcompat hf
    (Proj.map f hf).opensRange = Proj.basicOpen 𝒜 (s : A) := by
  let := isOpenImmersion_map f s hcompat hf
  apply SetLike.coe_injective
  exact map_range f s hcompat hf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical native coefficient-localization isomorphism, constructed from the actual
ordinary localization hypothesis and preserving the original projective open inclusion. -/
def localizationIso :
    Proj ℬ ≅ (Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen s).toScheme := by
  let hf := irrelevant_le_map f s hcompat
  let := isOpenImmersion_map f s hcompat hf
  apply IsOpenImmersion.isoOfRangeEq (Proj.map f hf)
    (Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen s).ι
  rw [Scheme.Opens.range_ι, DeJongAlterations.proj_toSpecZero_preimage_basicOpen]
  exact map_range f s hcompat hf

/-- The canonical isomorphism factors the literal native `Proj.map`, without a supplied
scheme comparison or a separately assumed irrelevant-ideal containment. -/
@[reassoc (attr := simp)]
theorem localizationIso_hom_ι :
    (localizationIso f s hcompat).hom ≫
      (Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen s).ι =
        Proj.map f (irrelevant_le_map f s hcompat) := by
  simp [localizationIso]

/-- The canonical isomorphism preserves both actual degree-zero structure maps. -/
@[reassoc]
theorem localizationIso_hom_structure :
    (localizationIso f s hcompat).hom ≫
      (Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen s).ι ≫ Proj.toSpecZero 𝒜 =
        Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (ProjStructureMap.degreeZeroMap f)) := by
  rw [← Category.assoc, localizationIso_hom_ι, ProjStructureMap.map_toSpecZero]

end

end DeJongAlterations.Geometry.ProjCoefficientLocalization
