/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.FiniteHyperplanePositiveDegree

/-! # Actual affine hyperplane pullbacks with the original coefficient field -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.CurveLineBundle

universe u

open StableModification StableModification.Projectivity StableModification.Cohomology
open CurvesField CurvesField.Positive Projectivity.LineBundleData

set_option backward.isDefEq.respectTransparency false

/-- Actual affineness alone suffices for hyperplane positivity over the SAME
original K, independently of the coefficient ring of the actual target coordinates. -/
theorem degree_hyperplane_pullback_pos_of_isAffineHom {K : Type u} [Field K] [Infinite K]
    {X Y : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hη : ¬ IsClosed ({genericPoint X} : Set X))
    {A : Type u} [CommRing A] {c : A →+* Γ(Y, ⊤)}
    (D : ProjectiveCoordinates Y A c) (h : X ⟶ Y) [IsAffineHom h] :
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

/-- The original positive power is compared directly to the original target's
hyperplane, retaining all ORIGINAL K coefficient actions and whole module maps. -/
theorem degree_pos_of_affine_hyperplane_power_iso {K : Type u} [Field K] [Infinite K]
    {X Y : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hη : ¬ IsClosed ({genericPoint X} : Set X))
    (L : LineBundleData X) (m : ℕ) (hm : 0 < m)
    {A : Type u} [CommRing A] {c : A →+* Γ(Y, ⊤)}
    (D : ProjectiveCoordinates Y A c) (h : X ⟶ Y) [IsAffineHom h]
    (e : L.twist (unitModule X) m ≅ ((hyperplane D).pullback h).twist (unitModule X) 1) :
    0 < Positive.degree L (structureCoeff p) := by
  have hd := degree_hyperplane_pullback_pos_of_isAffineHom hp hdim hη D h
  have he := eulerCharOf_eq_of_iso e (structureCoeff p)
  have hRR := eulerCharOf_twist_eq hp hdim L m
  have hmul : 0 < (m : ℤ) * Positive.degree L (structureCoeff p) := by
    unfold Positive.degree at hd
    rw [← he, hRR] at hd
    omega
  exact (mul_pos_iff_of_pos_left (Int.natCast_pos.mpr hm)).mp hmul

end DeJongAlterations.Geometry.CurveLineBundle
