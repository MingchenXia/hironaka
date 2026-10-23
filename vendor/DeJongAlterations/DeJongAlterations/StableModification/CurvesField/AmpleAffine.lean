/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3B)
-/
import DeJongAlterations.StableModification.CurvesField.AmpleSerre
import DeJongAlterations.StableModification.Projectivity.SectionsMapGenerated
import DeJongAlterations.StableModification.Projectivity.Reduction
import DeJongAlterations.StableModification.Cohomology.CurveHypersurface

/-!
# Affine non-vanishing loci from a finite map to the projective line

Let `X` be proper over a field `K`, of dimension at most one (no chains `x ⤳ y ⤳ z` of three
distinct points), and let `s₀`, `s₁` be global sections of `𝓛^N` without common zero. Suppose that
`s₀` does not vanish at the non-closed points of `X` (the generic points of the one-dimensional
irreducible components) and that every non-closed point specializes to a zero of `s₀` (every
one-dimensional component contains a zero of `s₀`). Then the morphism `h = (s₀ : s₁) : X → ℙ¹_K`
(OM3A's `LineBundleData.toProjectiveSpace`) has finite fibres, hence is finite (Zariski's main
theorem, `Projectivity.isFinite_of_finite_preimage_singleton`), and the non-vanishing loci
`D(s₀) = h⁻¹ D₊(x₀)`, `D(s₁) = h⁻¹ D₊(x₁)` are affine (`isAffineOpen_nonvanishingLocus`).
Blueprint `sm-curves-fields-ample.tex`, `lem:sm-ample-finite-map`.

## The fibres of `h`

The non-closed points of `X` are finitely many (`finite_setOf_not_isClosed`: they are generic
points of irreducible components, by the dimension hypothesis), and a closed set all of whose
points are closed is finite (`finite_of_forall_isClosed_singleton`). Closed points map to closed
points (`X` and `ℙ¹_K` are Jacobson spaces, Mathlib's
`Scheme.Hom.closePoints_subset_preimage_closedPoints`),
so the fibre over a non-closed point consists of non-closed points. The fibre over a closed point
`q` is closed; if it contained a non-closed point `η`, it would contain a zero `z` of `s₀`
specializing `η`, while `h(η) ∈ D₊(x₀)` (as `s₀(η) ≠ 0`) and `h(z) ∉ D₊(x₀)`.

This uses only the topology of `X`: no reducedness, so the result applies to non-reduced fibres.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Ample

noncomputable section

variable {X : Scheme.{u}}

/-! ### Topology of curves -/

/-- In a quasi-sober `T₀` space of Krull dimension at most one there are no chains `x ⤳ y ⤳ z` of
three distinct points. -/
theorem eq_or_eq_of_topologicalKrullDim_le_one {T : Type*} [TopologicalSpace T] [QuasiSober T]
    [T0Space T] (hdim : topologicalKrullDim T ≤ 1) (x y z : T) (hxy : x ⤳ y) (hyz : y ⤳ z) :
    x = y ∨ y = z := by
  let _ := specializationOrder T
  by_contra h
  push Not at h
  have h2 := Cohomology.two_le_krullDim_of_specializes hyz hxy (Ne.symm h.2) (Ne.symm h.1)
  rw [← Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints] at h2
  exact absurd (h2.trans hdim) (by decide)

variable {T : Type*} [TopologicalSpace T] [QuasiSober T] [NoetherianSpace T]

/-- In a Noetherian quasi-sober space, a closed set all of whose points are closed is finite. -/
theorem finite_of_forall_isClosed_singleton {A : Set T} (hA : IsClosed A)
    (h : ∀ x ∈ A, IsClosed ({x} : Set T)) : A.Finite := by
  obtain ⟨G, hG, hGA, hspec⟩ := Cohomology.exists_finite_specializes hA
  refine hG.subset fun a ha => ?_
  obtain ⟨g, hg, hga⟩ := hspec a ha
  have : a = g := by
    have hmem := specializes_iff_mem_closure.mp hga
    rw [(h g (hGA hg)).closure_eq] at hmem
    exact hmem
  exact this ▸ hg

/-- In a Noetherian quasi-sober space without chains of three distinct points, the non-closed
points are finitely many. -/
theorem finite_setOf_not_isClosed (hdim : ∀ x y z : T, x ⤳ y → y ⤳ z → x = y ∨ y = z) :
    {x : T | ¬ IsClosed ({x} : Set T)}.Finite := by
  obtain ⟨G, hG, -, hspec⟩ := Cohomology.exists_finite_specializes (isClosed_univ (X := T))
  refine hG.subset fun x hx => ?_
  obtain ⟨η, hη, hηx⟩ := hspec x (Set.mem_univ x)
  by_cases hxη : η = x
  · exact hxη ▸ hη
  · exfalso
    -- `x` is not closed, so it has a proper specialization
    have : closure ({x} : Set T) ≠ {x} := fun h => hx (by rw [← h]; exact isClosed_closure)
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure ({x} : Set T), y ≠ x := by
      by_contra hc
      push Not at hc
      exact this (Set.eq_singleton_iff_unique_mem.mpr ⟨subset_closure rfl, hc⟩)
    rcases hdim η x y hηx (specializes_iff_mem_closure.mpr hy) with h | h
    · exact hxη h
    · exact hyx h.symm

/-! ### The finite map to `ℙ¹` -/

open LineBundleData in
/-- **The non-vanishing loci of two generating sections are affine** (blueprint
`lem:sm-ample-finite-map`): let `X` be proper over a field, without chains of three distinct points,
and `s₀`, `s₁` global sections of `𝓛^N` without common zero such that `s₀` does not vanish at the
non-closed points and every non-closed point specializes to a zero of `s₀`. Then `D(s₀)` and
`D(s₁)` are affine: the morphism `(s₀ : s₁) : X → ℙ¹_K` is finite. -/
theorem isAffineOpen_nonvanishingLocus {K : Type u} [Field K] (p : X ⟶ Spec (.of K))
    [IsProper p] (hdim : ∀ x y z : X, x ⤳ y → y ⤳ z → x = y ∨ y = z)
    {L : LineBundleData X} {N : ℤ} (s₀ s₁ : L.Sections N ⊤)
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (hgen : ∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s₀.nonvanishingLocus)
    (hzero : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s₀.nonvanishingLocus) :
    IsAffineOpen s₀.nonvanishingLocus ∧ IsAffineOpen s₁.nonvanishingLocus := by
  -- `X` is a Noetherian space
  have : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := ⟨⟩
  -- the map `h = (s₀ : s₁)`
  let s : Fin 2 → L.Sections N ⊤ := ![s₀, s₁]
  have hs : Generates s := by
    intro x
    have hx : x ∈ s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus := by rw [hcov]; trivial
    rcases (TopologicalSpace.Opens.mem_sup.mp hx) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  let h := LineBundleData.toProjectiveSpace p hs
  have hstr : h ≫ projectiveSpaceStructure K 1 = p :=
    LineBundleData.toProjectiveSpace_structure p hs
  have : IsProper (h ≫ projectiveSpaceStructure K 1) := by rw [hstr]; infer_instance
  have : IsProper h := IsProper.of_comp h (projectiveSpaceStructure K 1)
  have : LocallyOfFiniteType (h ≫ projectiveSpaceStructure K 1) := by rw [hstr]; infer_instance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h (projectiveSpaceStructure K 1)
  have : JacobsonSpace (projectiveSpace K 1) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceStructure K 1)
  have h0 : h ⁻¹ᵁ Geometry.ProjectiveIdeal.nativeCoordinateOpen 0 = s₀.nonvanishingLocus :=
    LineBundleData.toProjectiveSpace_preimage_coordinate p hs 0
  have h1 : h ⁻¹ᵁ Geometry.ProjectiveIdeal.nativeCoordinateOpen 1 = s₁.nonvanishingLocus :=
    LineBundleData.toProjectiveSpace_preimage_coordinate p hs 1
  -- the fibres of `h` are finite
  have hfin : ∀ q, (h ⁻¹' {q}).Finite := by
    intro q
    by_cases hq : IsClosed ({q} : Set (projectiveSpace K 1))
    · apply finite_of_forall_isClosed_singleton (hq.preimage h.continuous)
      intro η hη
      by_contra hηc
      obtain ⟨z, hηz, hz⟩ := hzero η hηc
      have hqz : h z = q := (hηz.map h.continuous).mem_closed hq hη
      have hη0 : η ∈ h ⁻¹ᵁ Geometry.ProjectiveIdeal.nativeCoordinateOpen 0 := by
        rw [h0]
        exact hgen η hηc
      have hz0 : z ∉ h ⁻¹ᵁ Geometry.ProjectiveIdeal.nativeCoordinateOpen 0 := by
        rw [h0]
        exact hz
      apply hz0
      change h z ∈ Geometry.ProjectiveIdeal.nativeCoordinateOpen 0
      rw [hqz, ← (show h η = q from hη)]
      exact hη0
    · apply (finite_setOf_not_isClosed hdim).subset
      intro x hx hxc
      have := Scheme.Hom.closePoints_subset_preimage_closedPoints h (mem_closedPoints_iff.mpr hxc)
      rw [Set.mem_preimage, mem_closedPoints_iff, show h x = q from hx] at this
      exact hq this
  have hA : IsAffineHom h := (isFinite_of_finite_preimage_singleton h hfin).toIsAffineHom
  refine ⟨?_, ?_⟩
  · rw [← h0]
    exact @IsAffineOpen.preimage _ _ _ (Geometry.ProjectiveIdeal.nativeCoordinateOpen_isAffine 0)
      h hA
  · rw [← h1]
    exact @IsAffineOpen.preimage _ _ _ (Geometry.ProjectiveIdeal.nativeCoordinateOpen_isAffine 1)
      h hA

end

end DeJongAlterations.StableModification.CurvesField.Ample
