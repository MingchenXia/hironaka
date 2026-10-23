/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.AffineBlowupDominant
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.Tactic.FieldSimp

/-!
# The native affine blowup away from its centre

For a domain and a nonzero ideal element `g`, the native blowup structure morphism over `D(g)`
is an isomorphism. The proof uses the actual homogeneous chart and the localized coefficient map.
-/

open AlgebraicGeometry CategoryTheory Polynomial

set_option autoImplicit false

namespace DeJongAlterations

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R] (I : Ideal R) (g : R)

set_option backward.isDefEq.respectTransparency false in
/-- Every element of the actual fraction chart has a denominator which is a power of `g`. -/
theorem affineBlowupFractionChart_clear_denominator (hg0 : g ≠ 0)
    (s : affineBlowupFractionChart I g) :
    ∃ (a : R) (n : ℕ), algebraMap R (affineBlowupFractionChart I g) a =
      algebraMap R (affineBlowupFractionChart I g) g ^ n * s := by
  have hpowers : Submonoid.powers g ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hg0)
  have hle : affineBlowupFractionChart I g ≤
      Localization.subalgebra.ofField (FractionRing R) (Submonoid.powers g) hpowers := by
    apply Algebra.adjoin_le
    rintro _ ⟨a, rfl⟩
    exact ⟨(a : R), g, ⟨1, by simp⟩, by dsimp; rw [div_eq_mul_inv]⟩
  obtain ⟨a, b, ⟨n, rfl⟩, hs⟩ := hle s.2
  refine ⟨a, n, Subtype.ext ?_⟩
  change algebraMap R (FractionRing R) a =
    algebraMap R (FractionRing R) g ^ n * (s : FractionRing R)
  have hgn : algebraMap R (FractionRing R) g ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hg0)
  rw [hs, map_pow, mul_left_comm, mul_inv_cancel₀ hgn, mul_one]

/-- The literal localization of the coefficient map on the fraction chart is bijective. -/
theorem affineBlowupFractionChart_awayMap_bijective (hg0 : g ≠ 0) :
    Function.Bijective
      (Localization.awayMap (algebraMap R (affineBlowupFractionChart I g)) g) := by
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    refine ⟨0, ?_⟩
    have ha0 : a = 0 := affineBlowupFractionChart_algebraMap_injective I g
      (by simpa only [map_zero] using ha)
    simp [ha0]
  · apply Localization.awayMap_surjective_iff.mpr
    exact affineBlowupFractionChart_clear_denominator I g hg0

/-- The actual coefficient localization identifies `R_g` with the localized fraction chart. -/
def affineBlowupFractionChartLocalizedEquiv (hg0 : g ≠ 0) :
    Localization.Away g ≃ₐ[R]
      Localization.Away (algebraMap R (affineBlowupFractionChart I g) g) :=
  AlgEquiv.ofBijective
    (Localization.awayMapₐ (Algebra.ofId R (affineBlowupFractionChart I g)) g)
    (affineBlowupFractionChart_awayMap_bijective I g hg0)

omit [IsDomain R] in
set_option backward.isDefEq.respectTransparency false in
/-- Clearing the same power in an actual homogeneous Rees monomial. -/
theorem rees_homogeneous_clear_denominator (hg : g ∈ I) {n : ℕ} (p : reesAlgebra I)
    (hp : p ∈ reesGrading I n) :
    algebraMap R (reesAlgebra I) g ^ n * p =
      algebraMap R (reesAlgebra I) ((p : R[X]).coeff n) * reesDegreeOne I g hg ^ n := by
  apply Subtype.ext
  change C g ^ n * (p : R[X]) = C ((p : R[X]).coeff n) * monomial 1 g ^ n
  conv_lhs => rw [(mem_reesGrading_iff I n p).mp hp]
  rw [← C_pow, monomial_pow, one_mul, C_mul_monomial, C_mul_monomial, mul_comm]

omit [IsDomain R] in
/-- A relevant homogeneous prime avoiding the coefficient `g` also avoids the element `g*T`.
This uses the actual Rees relation in every positive homogeneous degree. -/
theorem affineBlowup_constant_basicOpen_le_chart (hg : g ∈ I) :
    Proj.basicOpen (reesGrading I) (algebraMap R (reesAlgebra I) g) ≤
      affineBlowupChartOpen I g hg := by
  intro x hx
  let P := x.asHomogeneousIdeal.toIdeal
  change algebraMap R (reesAlgebra I) g ∉ P at hx
  change reesDegreeOne I g hg ∉ P
  intro hGT
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn p hp
  change p ∈ P
  have hmul : algebraMap R (reesAlgebra I) g ^ n * p ∈ P := by
    rw [rees_homogeneous_clear_denominator I g hg p hp]
    exact P.mul_mem_left _ (P.pow_mem_of_mem hGT n hn)
  exact (x.isPrime.mem_or_mem hmul).resolve_left fun h => hx (x.isPrime.mem_of_pow_mem n h)

section GeneralProj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Membership in the prime represented by a native Proj chart is tested by its homogeneous
numerator in the original homogeneous prime. -/
theorem proj_basicOpenToSpec_mem {s : A} (x : Proj.basicOpen 𝒜 s)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers s)) :
    HomogeneousLocalization.mk z ∈ (Proj.basicOpenToSpec 𝒜 s x).asIdeal ↔
      (z.num : A) ∈ x.val.asHomogeneousIdeal := by
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x z

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback of a principal open of the actual degree-zero ring under the native structure map. -/
theorem proj_toSpecZero_preimage_basicOpen (r : 𝒜 0) :
    Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen r = Proj.basicOpen 𝒜 (r : A) := by
  ext x
  change ¬ r ∈ (Proj.toSpecZero 𝒜 x).asIdeal ↔ ¬ (r : A) ∈ x.asHomogeneousIdeal
  apply not_congr
  let e := (Scheme.topIso (Proj 𝒜)).inv ≫
    (Scheme.isoOfEq (Proj 𝒜) (Proj.basicOpen_one 𝒜)).inv
  let y : Proj.basicOpen 𝒜 (1 : A) := e x
  have hy : y.val = x := by
    have he : e ≫ (Proj.basicOpen 𝒜 1).ι = 𝟙 (Proj 𝒜) := by
      dsimp only [e]
      simp only [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
    exact congrArg (fun k : Proj 𝒜 ⟶ Proj 𝒜 => k x) he
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (1 : A)) r ∈
    (Proj.basicOpenToSpec 𝒜 1 y).asIdeal ↔ (r : A) ∈ x.asHomogeneousIdeal
  have hz : HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (1 : A)) r =
      HomogeneousLocalization.mk (⟨0, r, 1, by simp⟩ :
        HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers (1 : A))) := by
    apply HomogeneousLocalization.val_injective
    rfl
  rw [hz]
  simpa only [hy] using
    proj_basicOpenToSpec_mem 𝒜 y ⟨0, r, 1, by simp⟩

end GeneralProj

omit [IsDomain R] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- A base coefficient principal open pulls back to the basic open of its constant Rees element. -/
theorem affineBlowupStructure_preimage_basicOpen :
    affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen g =
      Proj.basicOpen (reesGrading I) (algebraMap R (reesAlgebra I) g) := by
  unfold affineBlowupStructure
  rw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen, proj_toSpecZero_preimage_basicOpen]
  rfl

omit [IsDomain R] in
/-- The entire inverse image of `D(g)` is contained in the actual `g*T` chart. -/
theorem affineBlowupStructure_preimage_le_chart (hg : g ∈ I) :
    affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤ affineBlowupChartOpen I g hg := by
  rw [affineBlowupStructure_preimage_basicOpen]
  exact affineBlowup_constant_basicOpen_le_chart I g hg

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual affine chart structure morphism becomes an isomorphism over `D(g)`. -/
theorem affineBlowupFractionChart_restrict_isIso (hg0 : g ≠ 0) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowupFractionChart I g)))) ∣_
      PrimeSpectrum.basicOpen g) := by
  let S := affineBlowupFractionChart I g
  let F := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let eR := basicOpenIsoSpecAway (R := CommRingCat.of R) g
  let eS := basicOpenIsoSpecAway (R := CommRingCat.of S) (algebraMap R S g)
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen g
  let V : (Spec (CommRingCat.of S)).Opens := PrimeSpectrum.basicOpen (algebraMap R S g)
  let q := Spec.map (CommRingCat.ofHom (R := Localization.Away g)
    (S := Localization.Away (algebraMap R S g)) (Localization.awayMap (algebraMap R S) g))
  have : IsIso q := by
    change IsIso (Spec.map (affineBlowupFractionChartLocalizedEquiv I g hg0).toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  have hR : eR.inv ≫ U.ι =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) := by
    rw [Iso.inv_comp_eq]
    exact (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) g).symm
  have hS : eS.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S g)))) =
      V.ι :=
    basicOpenIsoSpecAway_hom_SpecMap _
  have hcomm :
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S g)))) ≫ F =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) := by
    dsimp only [q, F]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a : 2
    simp [Localization.awayMap, IsLocalization.Away.map]
  have heq : F ∣_ U = eS.hom ≫ q ≫ eR.inv := by
    apply (cancel_mono U.ι).mp
    rw [morphismRestrict_ι]
    have h' := congrArg (fun k => eS.hom ≫ k) hcomm
    rw [← Category.assoc, hS] at h'
    simp only [Category.assoc, hR]
    change V.ι ≫ F = eS.hom ≫ q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
    exact h'
  change IsIso (F ∣_ U)
  rw [heq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The genuine fraction-chart inclusion has precisely the expected native Proj basic-open image. -/
theorem affineBlowupChartInclusion_opensRange (hg : g ∈ I) (hg0 : g ≠ 0) :
    (affineBlowupChartInclusion I g hg hg0).opensRange = affineBlowupChartOpen I g hg := by
  dsimp only [affineBlowupChartInclusion, affineBlowupChartOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting an open immersion over an open contained in its image gives an actual isomorphism. -/
theorem isIso_morphismRestrict_of_le_opensRange {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (V : Y.Opens) (hV : V ≤ i.opensRange) : IsIso (i ∣_ V) := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective]
  intro y
  obtain ⟨x, hx⟩ := hV y.2
  have hxy : x ∈ i ⁻¹ᵁ V := by
    change i x ∈ V
    rw [hx]
    exact y.2
  refine ⟨⟨x, hxy⟩, Subtype.ext ?_⟩
  rw [morphismRestrict_base_coe]
  exact hx

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual native blowup structure map is an isomorphism over every principal open
defined by a nonzero element of its ideal. No finite-generation or comparison certificate is used. -/
theorem affineBlowupStructure_restrict_isIso (hg : g ∈ I) (hg0 : g ≠ 0) :
    IsIso (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen g) := by
  let i := affineBlowupChartInclusion I g hg hg0
  let π := affineBlowupStructure I
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen g
  have hV : π ⁻¹ᵁ U ≤ i.opensRange := by
    rw [affineBlowupChartInclusion_opensRange]
    exact affineBlowupStructure_preimage_le_chart I g hg
  have : IsIso (i ∣_ π ⁻¹ᵁ U) := isIso_morphismRestrict_of_le_opensRange i _ hV
  have : IsIso ((i ≫ π) ∣_ U) := by
    dsimp only [i, π, U]
    rw [affineBlowupChartInclusion_structure]
    exact affineBlowupFractionChart_restrict_isIso I g hg0
  have : IsIso ((i ∣_ π ⁻¹ᵁ U) ≫ π ∣_ U) := by
    rw [← morphismRestrict_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (f := i ∣_ π ⁻¹ᵁ U) (π ∣_ U)

end

end DeJongAlterations
