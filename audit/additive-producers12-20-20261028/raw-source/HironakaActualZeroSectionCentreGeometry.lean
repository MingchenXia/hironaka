import TranscendentalNakamaye.Pending.HironakaActualZeroSectionBlowupLift

/-!
# Actual product flattenings and genuine image-centre geometry

An original local flattening is extended by its actual first-coordinate
projection and the unchanged normal coordinates. This internally proves
closedness, pointwise regularity and empty interior of the literal whole
zero-section image. No origin ideal or caller image-centre certificate.
Blueprint: hironaka-actual-zero-section-constructed-blowup-extension.tex.
Source-only; no kernel acceptance is claimed.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace TranscendentalNakamaye.Pending.HironakaActualZeroSectionCentreGeometry

noncomputable section

open FirstPass FirstPass.BlowupSequences HironakaRelativeNormalIdeal
  HironakaActualZeroSectionBlowupLift HironakaActualZeroSectionCentreSheaf

private def productMap (d t : ℕ) (f : ComplexModel d → ComplexModel d)
    (z : ComplexModel (d+t)) : ComplexModel (d+t) :=
  tangentInclusion d t (f (tangentProjection d t z)) +
    (z - tangentInclusion d t (tangentProjection d t z))

private theorem productMap_projection (d t : ℕ) (f : ComplexModel d → ComplexModel d)
    (z : ComplexModel (d+t)) :
    tangentProjection d t (productMap d t f z) = f (tangentProjection d t z) := by
  simp only [productMap, map_add, map_sub, tangentProjection_tangentInclusion,
    sub_self, add_zero]

private theorem productMap_tangent (d t : ℕ) (f : ComplexModel d → ComplexModel d)
    (z : ComplexModel (d+t)) (j : Fin d) :
    productMap d t f z (j.castAdd t) = f (tangentProjection d t z) j := by
  simp [productMap, PiLp.add_apply, PiLp.sub_apply]

private theorem productMap_normal (d t : ℕ) (f : ComplexModel d → ComplexModel d)
    (z : ComplexModel (d+t)) (j : Fin t) :
    productMap d t f z (j.natAdd d) = z (j.natAdd d) := by
  simp [productMap, PiLp.add_apply, PiLp.sub_apply]

private theorem productMap_inverse (d t : ℕ)
    (f g : ComplexModel d → ComplexModel d) (z : ComplexModel (d+t))
    (hgf : g (f (tangentProjection d t z)) = tangentProjection d t z) :
    productMap d t g (productMap d t f z) = z := by
  change tangentInclusion d t (g (tangentProjection d t (productMap d t f z))) +
    (productMap d t f z -
      tangentInclusion d t (tangentProjection d t (productMap d t f z))) = z
  rw [productMap_projection, hgf]
  dsimp [productMap]
  abel

private theorem differentiableOn_productMap (d t : ℕ)
    {f : ComplexModel d → ComplexModel d} {U : Set (ComplexModel d)}
    (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (productMap d t f) ((tangentProjection d t) ⁻¹' U) := by
  have hcomp : DifferentiableOn ℂ (f ∘ tangentProjection d t)
      ((tangentProjection d t) ⁻¹' U) :=
    hf.comp (tangentProjection d t).differentiable.differentiableOn (fun _ hz => hz)
  exact ((tangentInclusion d t).differentiable.comp_differentiableOn hcomp).add
    (differentiable_id.sub ((tangentInclusion d t).differentiable.comp
      (tangentProjection d t).differentiable)).differentiableOn

/-- A real product extension, with actual inverse and actual open domains.
The normal coordinates are the original normal coordinates, unchanged. -/
def actual_zeroSection_localEquiv (d t : ℕ) (x : ComplexModel d)
    (Φ : LocalHolomorphicEquivAt (n := d) x) :
    LocalHolomorphicEquivAt (n := d+t) (tangentInclusion d t x) where
  source := (tangentProjection d t) ⁻¹' Φ.source
  target := (tangentProjection d t) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage (tangentProjection d t).continuous
  isOpen_target := Φ.isOpen_target.preimage (tangentProjection d t).continuous
  center_mem_source := by
    change tangentProjection d t (tangentInclusion d t x) ∈ Φ.source
    rw [tangentProjection_tangentInclusion]
    exact Φ.center_mem_source
  toFun := productMap d t Φ.toFun
  invFun := productMap d t Φ.invFun
  toFun_holomorphic := differentiableOn_productMap d t Φ.toFun_holomorphic
  invFun_holomorphic := differentiableOn_productMap d t Φ.invFun_holomorphic
  mapsTo_toFun := fun z hz => by
    change tangentProjection d t (productMap d t Φ.toFun z) ∈ Φ.target
    rw [productMap_projection]
    exact Φ.mapsTo_toFun hz
  mapsTo_invFun := fun z hz => by
    change tangentProjection d t (productMap d t Φ.invFun z) ∈ Φ.source
    rw [productMap_projection]
    exact Φ.mapsTo_invFun hz
  left_inv := fun z hz => productMap_inverse d t Φ.toFun Φ.invFun z (Φ.left_inv _ hz)
  right_inv := fun z hz => productMap_inverse d t Φ.invFun Φ.toFun z (Φ.right_inv _ hz)

/-- Whole plane comparison for the actual extended coordinate change.
The order of the literal original coordinates is preserved, including k=0. -/
theorem actual_zeroSection_localEquiv_plane_iff (d t k : ℕ) (hk : k ≤ d)
    (x : ComplexModel d) (Φ : LocalHolomorphicEquivAt (n := d) x)
    (z : ComplexModel (d+t)) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z ∈ complexCoordinatePlane (d+t) k ↔
      z ∈ complexCoordinatePlane (d+t) d ∧
        Φ.toFun (tangentProjection d t z) ∈ complexCoordinatePlane d k := by
  change productMap d t Φ.toFun z ∈ complexCoordinatePlane (d+t) k ↔ _
  constructor
  · intro h
    constructor
    · intro j hj
      let l : Fin t := ⟨j.val-d, by omega⟩
      have he : j = l.natAdd d := Fin.ext (by dsimp [l]; omega)
      rw [he]
      have hh := h (l.natAdd d) (by simp only [Fin.val_natAdd]; omega)
      rwa [productMap_normal] at hh
    · intro j hj
      have hh := h (j.castAdd t) (by simpa only [Fin.val_castAdd] using hj)
      rwa [productMap_tangent] at hh
  · rintro ⟨hN, hΦ⟩ j hj
    by_cases hji : j.val < d
    · let l : Fin d := ⟨j.val, hji⟩
      have he : j = l.castAdd t := Fin.ext rfl
      rw [he, productMap_tangent]
      exact hΦ l hj
    · let l : Fin t := ⟨j.val-d, by omega⟩
      have he : j = l.natAdd d := Fin.ext (by dsimp [l]; omega)
      rw [he, productMap_normal]
      exact hN _ (by simp only [Fin.val_natAdd]; omega)

/-- The literal image, not only its origin ideal, is a closed-plane intersection. -/
theorem actual_zeroSection_image_eq (d t : ℕ) (C : Set (ComplexModel d)) :
    (tangentInclusion d t) '' C =
      (tangentProjection d t) ⁻¹' C ∩ complexCoordinatePlane (d+t) d := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa only [mem_preimage, tangentProjection_tangentInclusion] using hx,
      tangentInclusion_mem_plane d t x⟩
  · rintro ⟨hx, hz⟩
    exact ⟨tangentProjection d t z, hx, tangentInclusion_projection_eq_of_mem_plane d t hz⟩

private theorem model_regular_iff (n k : ℕ) (C : Set (ComplexModel n))
    (x : ComplexModel n) :
    RegularAtDim (n := n) C x k ↔
      k ≤ n ∧ x ∈ C ∧ ∃ Φ : LocalHolomorphicEquivAt (n := n) x,
        Φ.toFun x = 0 ∧ ∀ {y}, y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun y ∈ complexCoordinatePlane n k) := by
  simp [RegularAtDim, complexChartAt, chartAt_self_eq]
  intro _ _
  rfl

/-- EVERY original regular point has a genuine product flattening upstairs.
Neither the centre nor its pointwise dimension is restricted to the origin. -/
theorem actual_zeroSection_image_regular {d t k : ℕ} {C : Set (ComplexModel d)}
    {x : ComplexModel d} (hx : RegularAtDim (n := d) C x k) :
    RegularAtDim (n := d+t) ((tangentInclusion d t) '' C) (tangentInclusion d t x) k := by
  obtain ⟨hk, hxC, Φ, hΦzero, hΦflat⟩ := (model_regular_iff d k C x).mp hx
  apply (model_regular_iff (d+t) k ((tangentInclusion d t) '' C)
    (tangentInclusion d t x)).mpr
  refine ⟨by omega, ⟨x, hxC, rfl⟩, actual_zeroSection_localEquiv d t x Φ, ?_, ?_⟩
  · change productMap d t Φ.toFun (tangentInclusion d t x) = 0
    simp only [productMap, tangentProjection_tangentInclusion, hΦzero,
      map_zero, sub_self, add_zero]
  · intro y hy
    rw [actual_zeroSection_localEquiv_plane_iff d t k hk x Φ y,
      actual_zeroSection_image_eq]
    change (tangentProjection d t y ∈ C ∧ y ∈ complexCoordinatePlane (d+t) d) ↔ _
    rw [hΦflat hy]
    exact and_comm

/-- Closedness and the actual source flattenings internally give the ENTIRE
image as an actual closed submanifold, with no image-centre premise. -/
theorem actual_zeroSection_image_closedSubmanifold {d t : ℕ} {C : Set (ComplexModel d)}
    (hC : IsClosedSubmanifold d C) :
    IsClosedSubmanifold (d+t) ((tangentInclusion d t) '' C) := by
  constructor
  · rw [actual_zeroSection_image_eq]
    exact (hC.1.preimage (tangentProjection d t).continuous).inter
      (actual_zeroSection_plane_closed d t)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hC.2 x hx
    exact ⟨k, actual_zeroSection_image_regular hk⟩

/-- A continuous actual retraction proves empty interior for ANY centre.
This uses no normal coordinate, and so includes t=0 and d=0. -/
theorem actual_zeroSection_image_interior_eq_empty (d t : ℕ) (C : Set (ComplexModel d))
    (hC : interior C = ∅) :
    interior ((tangentInclusion d t) '' C) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨x, _hx, hix⟩ := interior_subset hz
  let U := (tangentInclusion d t) ⁻¹' interior ((tangentInclusion d t) '' C)
  have hU : IsOpen U := isOpen_interior.preimage (tangentInclusion d t).continuous
  have hxU : x ∈ U := by
    change tangentInclusion d t x ∈ interior ((tangentInclusion d t) '' C)
    rwa [hix]
  have hUC : U ⊆ C := by
    intro y hy
    have hyim : tangentInclusion d t y ∈ (tangentInclusion d t) '' C := interior_subset hy
    have hyC : y ∈ (tangentInclusion d t) ⁻¹' ((tangentInclusion d t) '' C) := hyim
    rwa [actual_zeroSection_centre_preimage d t C] at hyC
  have hxint : x ∈ interior C := interior_maximal hUC hU hxU
  simp only [hC, mem_empty_iff_false] at hxint

end
end TranscendentalNakamaye.Pending.HironakaActualZeroSectionCentreGeometry
