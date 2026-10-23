/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.ProjectiveIdealGradedQuotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/- Reused from EnvelopeProperty/Projective/HomogeneousQuotient.lean; SHA256 c1b323062e54bbb0982c7e80c91969ea481fe4636ec1e3621ee8741bfeb4a628. -/


/-!
# Actual projective closed immersions of genuine homogeneous quotients

The actual homogeneous ideal quotient grading gives Mathlib’s real Proj.map.
Same-degree numerator lifts make every homogeneous away map surjective;
actual open-immersion pullback squares and target-locality prove that this
whole projective scheme morphism is a closed immersion. Its genuine kernel
ideal sheaf has the true chart localization annihilator criterion in the
original ideal, retaining nilpotents and powers. No radical replacement,
field, domain, Noetherianity or finite-generation assumption is made.
No coherent analytic sheaf identification is claimed.
-/

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : HomogeneousIdeal 𝒜)

/-- Same-degree quotient lifts make the actual homogeneous away-ring map surjective. -/
theorem awayMap_surjective {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map (gradedMk 𝒜 J.toIdeal) s) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := z.mk_surjective _ ((gradedMk 𝒜 J.toIdeal).map_mem hs)
  obtain ⟨b, hb⟩ := componentMap_surjective 𝒜 J.toIdeal (n • d) ⟨a, ha⟩
  refine ⟨Away.mk 𝒜 hs n b b.2, ?_⟩
  have he : (gradedMk 𝒜 J.toIdeal) b = a := congrArg Subtype.val hb
  simp only [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, he]
  rfl

/-- The actual scheme morphism from the genuinely graded original ideal quotient. -/
def quotientSchemeMap : Proj (grading 𝒜 J.toIdeal) ⟶ Proj 𝒜 :=
  Proj.map (gradedMk 𝒜 J.toIdeal) (irrelevant_le_map 𝒜 J)

/-- The whole quotient chart square is a genuine scheme pullback. -/
theorem isPullback_awayMap {d : ℕ} {s : A} (hd : 0 < d) (hs : s ∈ 𝒜 d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map (gradedMk 𝒜 J.toIdeal) s)))
      (Proj.awayι (grading 𝒜 J.toIdeal) ((gradedMk 𝒜 J.toIdeal) s)
        ((gradedMk 𝒜 J.toIdeal).map_mem hs) hd)
      (Proj.awayι 𝒜 s hs hd) (quotientSchemeMap 𝒜 J) := by
  apply IsOpenImmersion.isPullback
  · exact (Proj.awayι_comp_map (gradedMk 𝒜 J.toIdeal) (irrelevant_le_map 𝒜 J) hd s hs)
  · simp only [Proj.opensRange_awayι, quotientSchemeMap, Proj.map_preimage_basicOpen]

set_option backward.isDefEq.respectTransparency false in
/-- The actual projective scheme map of the original homogeneous quotient is a closed immersion. -/
instance instIsClosedImmersion_quotientSchemeMap : IsClosedImmersion (quotientSchemeMap 𝒜 J) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (Proj.affineOpenCover 𝒜).openCover]
  intro s
  change IsClosedImmersion (Limits.pullback.snd (quotientSchemeMap 𝒜 J)
    (Proj.awayι 𝒜 (s.2 : A) s.2.2 s.1.2))
  let sq := isPullback_awayMap 𝒜 J s.1.2 s.2.2
  erw [← sq.flip.isoPullback_inv_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  exact IsClosedImmersion.spec_of_surjective _ (awayMap_surjective 𝒜 J s.2.2)

end DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient

namespace DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : HomogeneousIdeal 𝒜)

/-- The true kernel ideal sheaf of the original projective homogeneous quotient closed immersion. -/
def quotientIdealSheaf : (Proj 𝒜).IdealSheafData := (quotientSchemeMap 𝒜 J).ker

/-- Its actual support is exactly the genuine projective quotient scheme image. -/
theorem quotientIdealSheaf_support :
    (quotientIdealSheaf 𝒜 J).support = Set.range (quotientSchemeMap 𝒜 J) := by
  rw [quotientIdealSheaf, Scheme.Hom.support_ker,
    (quotientSchemeMap 𝒜 J).isClosedEmbedding.isClosed_range.closure_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Every original away-ring element belongs to the actual sheaf ideal precisely when its actual quotient image is zero. -/
theorem mem_quotientIdealSheaf_awayToSection_iff {d : ℕ} {s : A}
    (hd : 0 < d) (hs : s ∈ 𝒜 d) (a : Away 𝒜 s) :
    (Proj.awayToSection 𝒜 s).hom a ∈
      (quotientIdealSheaf 𝒜 J).ideal ⟨Proj.basicOpen 𝒜 s, Proj.isAffineOpen_basicOpen 𝒜 s hs hd⟩ ↔
        Away.map (gradedMk 𝒜 J.toIdeal) s a = 0 := by
  rw [quotientIdealSheaf, Scheme.Hom.ker_apply, RingHom.mem_ker]
  have e := Proj.awayToSection_comp_appLE (gradedMk 𝒜 J.toIdeal) (irrelevant_le_map 𝒜 J) hs
  have he := congrArg (fun f => f.hom a) e
  change (quotientSchemeMap 𝒜 J).app (Proj.basicOpen 𝒜 s) ((Proj.awayToSection 𝒜 s).hom a) = 0 ↔ _
  change (quotientSchemeMap 𝒜 J).app (Proj.basicOpen 𝒜 s) ((Proj.awayToSection 𝒜 s).hom a) =
    (Proj.awayToSection (grading 𝒜 J.toIdeal) ((gradedMk 𝒜 J.toIdeal) s)).hom
      (Away.map (gradedMk 𝒜 J.toIdeal) s a) at he
  rw [he]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (grading 𝒜 J.toIdeal) ((gradedMk 𝒜 J.toIdeal) s)
      ((gradedMk 𝒜 J.toIdeal).map_mem hs) hd).hom).1

/-- The actual homogeneous quotient away-ring kernel retains the original ideal via genuine localization annihilators. -/
theorem awayMap_mk_eq_zero_iff {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    Away.map (gradedMk 𝒜 J.toIdeal) s (Away.mk 𝒜 hs n a ha) = 0 ↔
      ∃ m : ℕ, s ^ m * a ∈ J.toIdeal := by
  rw [Away.map_mk, ← (HomogeneousLocalization.val_injective _).eq_iff,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨b, ⟨m, rfl⟩⟩, hb⟩
    refine ⟨m, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simpa only [map_mul, map_pow, gradedMk_apply] using hb
  · rintro ⟨m, hm⟩
    refine ⟨⟨((gradedMk 𝒜 J.toIdeal) s) ^ m, ⟨m, rfl⟩⟩, ?_⟩
    simpa only [map_mul, map_pow, gradedMk_apply] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

end DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient

namespace DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : HomogeneousIdeal 𝒜)

/-- The actual quotient sheaf ideal on a homogeneous affine chart pulls back to the entire away-ring kernel. -/
theorem quotientIdealSheaf_awayToSection_comap {d : ℕ} {s : A}
    (hd : 0 < d) (hs : s ∈ 𝒜 d) :
    ((quotientIdealSheaf 𝒜 J).ideal
      ⟨Proj.basicOpen 𝒜 s, Proj.isAffineOpen_basicOpen 𝒜 s hs hd⟩).comap
        (Proj.awayToSection 𝒜 s).hom = RingHom.ker (Away.map (gradedMk 𝒜 J.toIdeal) s) := by
  ext a
  exact mem_quotientIdealSheaf_awayToSection_iff 𝒜 J hd hs a

/-- A genuine relevant homogeneous prime containing the original ideal gives an actual quotient projective point. -/
def quotientPoint (p : ProjectiveSpectrum 𝒜) (hJ : J ≤ p.asHomogeneousIdeal) :
    ProjectiveSpectrum (grading 𝒜 J.toIdeal) where
  asHomogeneousIdeal := p.asHomogeneousIdeal.map (gradedMk 𝒜 J.toIdeal)
  isPrime := by
    exact Ideal.isPrime_map_quotientMk_of_isPrime hJ
  not_irrelevant_le h := by
    apply p.not_irrelevant_le
    have he : (p.asHomogeneousIdeal.map (gradedMk 𝒜 J.toIdeal)).comap (gradedMk 𝒜 J.toIdeal) =
        p.asHomogeneousIdeal := HomogeneousIdeal.ext (Ideal.comap_map_mk hJ)
    rw [← he]
    apply HomogeneousIdeal.le_comap_of_map_le
    rw [map_irrelevant]
    exact h

/-- The actual quotient prime maps back to the entire original projective prime. -/
theorem quotientSchemeMap_quotientPoint (p : ProjectiveSpectrum 𝒜) (hJ : J ≤ p.asHomogeneousIdeal) :
    quotientSchemeMap 𝒜 J (quotientPoint 𝒜 J p hJ) = p := by
  apply ProjectiveSpectrum.ext
  exact HomogeneousIdeal.ext (Ideal.comap_map_mk hJ)

/-- The true scheme image of the projective homogeneous quotient is exactly the original homogeneous vanishing locus. -/
theorem range_quotientSchemeMap :
    Set.range (quotientSchemeMap 𝒜 J) = ProjectiveSpectrum.zeroLocus 𝒜 (J.toIdeal : Set A) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    intro a ha
    change Ideal.Quotient.mk J.toIdeal a ∈ q.asHomogeneousIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact q.asHomogeneousIdeal.zero_mem
  · intro hp
    exact ⟨quotientPoint 𝒜 J p hp, quotientSchemeMap_quotientPoint 𝒜 J p hp⟩

end DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient

namespace DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (J : HomogeneousIdeal 𝒜)

/-- The actual original-ideal projective zero locus is the genuine quotient kernel sheaf support. -/
theorem quotientIdealSheaf_support_eq_zeroLocus :
    ((quotientIdealSheaf 𝒜 J).support : Set (Proj 𝒜)) =
      ProjectiveSpectrum.zeroLocus 𝒜 (J.toIdeal : Set A) := by
  rw [quotientIdealSheaf_support, range_quotientSchemeMap]

/-- On every genuine homogeneous affine chart, the sheaf ideal uses the original localization annihilator criterion. -/
theorem mem_quotientIdealSheaf_awayToSection_mk_iff {d : ℕ} {s : A}
    (hd : 0 < d) (hs : s ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    (Proj.awayToSection 𝒜 s).hom (Away.mk 𝒜 hs n a ha) ∈
      (quotientIdealSheaf 𝒜 J).ideal ⟨Proj.basicOpen 𝒜 s, Proj.isAffineOpen_basicOpen 𝒜 s hs hd⟩ ↔
        ∃ m : ℕ, s ^ m * a ∈ J.toIdeal :=
  (mem_quotientIdealSheaf_awayToSection_iff 𝒜 J hd hs _).trans
    (awayMap_mk_eq_zero_iff 𝒜 J hs n a ha)

end DeJongAlterations.Geometry.ProjectiveIdeal.GradedQuotient
