import TranscendentalNakamaye.Pending.HironakaActualZeroSectionCentreGeometry
import TranscendentalNakamaye.Pending.NormalCrossings

/-! Actual whole-labelled product boundary extension. The generic embedded
native-chart transport is a separate remaining consumer. -/

set_option autoImplicit false
open Set
open scoped Topology Manifold

namespace TranscendentalNakamaye.Pending.HironakaDisjointActualBoundaryLift

noncomputable section

open FirstPass NormalCrossings HironakaRelativeNormalIdeal
  HironakaActualZeroSectionCentreGeometry

private def liftMask (d t : ℕ) (S : Finset (Fin d)) : Finset (Fin (d+t)) :=
  S.map ⟨fun j => j.castAdd t, Fin.castAdd_injective d t⟩

private def normalMask (d t : ℕ) : Finset (Fin (d+t)) :=
  Finset.univ.filter fun j => d ≤ j.val

private theorem product_tangent {d t : ℕ} (x : ComplexModel d)
    (Φ : LocalHolomorphicEquivAt (n := d) x) (z : ComplexModel (d+t)) (j : Fin d) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z (j.castAdd t) =
      Φ.toFun (tangentProjection d t z) j := by
  change (tangentInclusion d t (Φ.toFun (tangentProjection d t z)) +
    (z - tangentInclusion d t (tangentProjection d t z))) (j.castAdd t) = _
  simp

private theorem product_normal {d t : ℕ} (x : ComplexModel d)
    (Φ : LocalHolomorphicEquivAt (n := d) x) (z : ComplexModel (d+t)) (j : Fin t) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z (j.natAdd d) = z (j.natAdd d) := by
  change (tangentInclusion d t (Φ.toFun (tangentProjection d t z)) +
    (z - tangentInclusion d t (tangentProjection d t z))) (j.natAdd d) = _
  simp

private theorem mem_liftMask {d t : ℕ} (S : Finset (Fin d))
    (x : ComplexModel d) (Φ : LocalHolomorphicEquivAt (n := d) x)
    (z : ComplexModel (d+t)) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z ∈ coordSubspace (liftMask d t S) ↔
      Φ.toFun (tangentProjection d t z) ∈ coordSubspace S := by
  simp only [coordSubspace, Set.mem_ofPred_eq, liftMask, Finset.mem_map]
  constructor
  · intro h j hj
    simpa only [product_tangent] using h (j.castAdd t) ⟨j, hj, rfl⟩
  · rintro h _ ⟨j, hj, rfl⟩
    change (actual_zeroSection_localEquiv d t x Φ).toFun z (j.castAdd t) = 0
    rw [product_tangent]
    exact h j hj

private theorem mem_centreMask {d t : ℕ} (S : Finset (Fin d))
    (x : ComplexModel d) (Φ : LocalHolomorphicEquivAt (n := d) x)
    (z : ComplexModel (d+t)) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z ∈
        coordSubspace (liftMask d t S ∪ normalMask d t) ↔
      Φ.toFun (tangentProjection d t z) ∈ coordSubspace S ∧
        z ∈ complexCoordinatePlane (d+t) d := by
  have hu : ∀ w : ComplexModel (d+t),
      w ∈ coordSubspace (liftMask d t S ∪ normalMask d t) ↔
      w ∈ coordSubspace (liftMask d t S) ∧ w ∈ coordSubspace (normalMask d t) := by
    intro w
    simp only [coordSubspace, Set.mem_ofPred_eq, Finset.mem_union]
    constructor
    · intro h
      exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
    · rintro ⟨h₁, h₂⟩ j (hj | hj)
      · exact h₁ j hj
      · exact h₂ j hj
  rw [hu, mem_liftMask]
  apply and_congr_right
  intro _
  change (∀ j ∈ normalMask d t, _) ↔ ∀ j : Fin (d+t), d ≤ j.val → z j = 0
  constructor
  · intro h j hj
    let l : Fin t := ⟨j.val-d, by omega⟩
    have he : j = l.natAdd d := Fin.ext (by dsimp [l]; omega)
    have hh := h j (by simp [normalMask, hj])
    rw [he, product_normal] at hh
    simpa only [he] using hh
  · intro h j hj
    have hd : d ≤ j.val := (Finset.mem_filter.mp hj).2
    let l : Fin t := ⟨j.val-d, by omega⟩
    have he : j = l.natAdd d := Fin.ext (by dsimp [l]; omega)
    rw [he, product_normal]
    exact h _ (by simp)

/-- Extend one actual intrinsic NC chart to all original boundary positions. -/
theorem hasNormalCrossings_zeroSection {d t : ℕ} {D : Set (ComplexModel d)}
    {B : List (Set (ComplexModel d))} (h : HasNormalCrossings d D B) :
    HasNormalCrossings (d+t) ((tangentInclusion d t) '' D)
      (B.map fun H => (tangentProjection d t) ⁻¹' H) := by
  simp only [HasNormalCrossings, IsCoordinateFamilyAt, complexChartAt, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source,
    OpenPartialHomeomorph.refl_target, id_eq, Set.mem_univ, true_implies] at h ⊢
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨S₀, S, ⟨Φ, hsrc, h0, hflat⟩, hcard⟩ := h x hx
  change LocalHolomorphicEquivAt (n := d) x at Φ
  have hflat' : ∀ o : Option (Fin B.length),
      x ∈ o.elim D (fun i => B.get i) → ∀ z ∈ Φ.source,
        (z ∈ o.elim D (fun i => B.get i) ↔ Φ.toFun z ∈
          coordSubspace (o.elim S₀ S)) := by
    intro o ho z hz
    exact hflat o ho hz
  let S' : Fin (B.map fun H => (tangentProjection d t) ⁻¹' H).length →
      Finset (Fin (d+t)) := fun i => liftMask d t (S ⟨i.val, by simpa using i.isLt⟩)
  refine ⟨liftMask d t S₀ ∪ normalMask d t, S', ?_, ?_⟩
  · refine ⟨actual_zeroSection_localEquiv d t x Φ, ?_, ?_, ?_⟩
    · exact Set.subset_univ _
    · change (actual_zeroSection_localEquiv d t x Φ).toFun (tangentInclusion d t x) = 0
      change tangentInclusion d t (Φ.toFun (tangentProjection d t (tangentInclusion d t x))) +
        (tangentInclusion d t x - tangentInclusion d t
          (tangentProjection d t (tangentInclusion d t x))) = 0
      have hz : Φ.toFun x = 0 := h0
      simp only [tangentProjection_tangentInclusion, hz, map_zero, sub_self, add_zero]
    · rintro (_ | i) hi z hzΦ
      · change (z ∈ (tangentInclusion d t) '' D ↔
          (actual_zeroSection_localEquiv d t x Φ).toFun z ∈
          coordSubspace (liftMask d t S₀ ∪ normalMask d t))
        erw [mem_centreMask, actual_zeroSection_image_eq]
        have hp : tangentProjection d t z ∈ Φ.source := hzΦ
        exact and_congr_left fun _ => hflat' none hx _ hp
      · let j : Fin B.length := ⟨i.val, by simpa using i.isLt⟩
        have hget : (B.map fun H => (tangentProjection d t) ⁻¹' H).get i =
            (tangentProjection d t) ⁻¹' B.get j := by simp [j]
        change (z ∈ (B.map fun H => (tangentProjection d t) ⁻¹' H).get i ↔ _)
        rw [hget]
        change (tangentProjection d t z ∈ B.get j ↔
          (actual_zeroSection_localEquiv d t x Φ).toFun z ∈ coordSubspace (liftMask d t (S j)))
        erw [mem_liftMask]
        apply hflat' (some j)
        · simpa [hget, tangentProjection_tangentInclusion] using hi
        · exact hzΦ
  · intro i hi
    let j : Fin B.length := ⟨i.val, by simpa using i.isLt⟩
    have hj : x ∈ B.get j := by simpa [j, tangentProjection_tangentInclusion] using hi
    simpa [S', liftMask, j] using hcard j hj

end
end TranscendentalNakamaye.Pending.HironakaDisjointActualBoundaryLift
