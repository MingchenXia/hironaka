/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.LineBundleEffectivePositiveDegree
import DeJongAlterations.StableModification.Projectivity.LineBundleOpsHyperplane

/-! # Actual finite hyperplane pullbacks and the same original Euler degree -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.CurveLineBundle

universe u

open StableModification StableModification.Projectivity StableModification.Cohomology
open CurvesField CurvesField.Positive
open Projectivity.LineBundleData

set_option backward.isDefEq.respectTransparency false

/-- A proper curve with an actual nonclosed point cannot be an affine scheme:
proper plus affine is finite, and the unchanged field fibre is discrete. -/
theorem not_isAffine_of_nonclosed_point {K : Type u} [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (x : X) (hx : ¬ IsClosed ({x} : Set X)) : ¬ IsAffine X := by
  intro hX
  let : IsAffine X := hX
  let : IsFinite p := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  let t : Spec (.of K) := IsLocalRing.closedPoint K
  have he : p ⁻¹' {t} = (Set.univ : Set X) := by
    ext z
    exact iff_true_intro (Subsingleton.elim _ _)
  have hd := p.isDiscrete_preimage_singleton t
  rw [he] at hd
  have : DiscreteTopology X := isDiscrete_univ_iff.mp hd
  exact hx (isClosed_discrete _)

/-- The SAME actual finite map and original coordinate section internally produce
strict positivity of the pulled-back ORIGINAL hyperplane Euler degree. -/
theorem degree_hyperplane_pullback_pos {K : Type u} [Field K] [Infinite K]
    {X Y : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hη : ¬ IsClosed ({genericPoint X} : Set X))
    {A : Type u} [CommRing A] {c : A →+* Γ(Y, ⊤)}
    (D : ProjectiveCoordinates Y A c) (h : X ⟶ Y) [IsFinite h] :
    0 < Positive.degree ((hyperplane D).pullback h) (structureCoeff p) := by
  let : IsProper p := hp.isProper
  obtain ⟨i, hi⟩ := (hyperplane D).exists_mem_U (h (genericPoint X))
  let s : ((hyperplane D).pullback h).Sections 1 ⊤ := (coordSection D i).pullback h
  have hs : s.nonvanishingLocus = h ⁻¹ᵁ D.U i := by
    rw [Sections.nonvanishingLocus_pullback, nonvanishingLocus_coordSection]
  have hsa : IsAffineOpen s.nonvanishingLocus := hs.symm ▸ (D.isAffineOpen i).preimage h
  have hz : ∃ z : X, z ∉ s.nonvanishingLocus := by
    by_contra hzero
    push Not at hzero
    have htop : s.nonvanishingLocus = ⊤ := top_unique (fun z _ => hzero z)
    have haff : IsAffineOpen (⊤ : X.Opens) := htop ▸ hsa
    let : IsAffine (⊤ : X.Opens).toScheme := haff
    have : IsAffine X := IsAffine.of_isIso X.topIso.inv
    exact not_isAffine_of_nonclosed_point p (genericPoint X) hη this
  apply degree_pos_of_effective_section hp hdim _ s _ hz
  rw [hs]
  exact hi

/-- A whole original module comparison with a finite hyperplane pullback turns
strict positivity of that SAME power into strict positivity of the original L. -/
theorem degree_pos_of_finite_hyperplane_power_iso {K : Type u} [Field K] [Infinite K]
    {X Y : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hη : ¬ IsClosed ({genericPoint X} : Set X))
    (L : LineBundleData X) (m : ℕ) (hm : 0 < m)
    {A : Type u} [CommRing A] {c : A →+* Γ(Y, ⊤)}
    (D : ProjectiveCoordinates Y A c) (h : X ⟶ Y) [IsFinite h]
    (e : L.twist (unitModule X) m ≅ ((hyperplane D).pullback h).twist (unitModule X) 1) :
    0 < Positive.degree L (structureCoeff p) := by
  have hd := degree_hyperplane_pullback_pos hp hdim hη D h
  have he := eulerCharOf_eq_of_iso e (structureCoeff p)
  have hRR := eulerCharOf_twist_eq hp hdim L m
  have hmul : 0 < (m : ℤ) * Positive.degree L (structureCoeff p) := by
    unfold Positive.degree at hd
    rw [← he, hRR] at hd
    omega
  exact (mul_pos_iff_of_pos_left (Int.natCast_pos.mpr hm)).mp hmul

end DeJongAlterations.Geometry.CurveLineBundle
