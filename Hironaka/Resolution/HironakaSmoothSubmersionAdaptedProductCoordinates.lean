/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionAdaptedProductCoordinates
open BlowupFlatCoordinates HironakaSmoothSubmersionNormalCrossings
noncomputable section

def rotateBlocks (n r : ℕ) : Fin (n+r) ≃ Fin (n+r) :=
  ((finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin r))).trans finSumFinEquiv).trans
    (finCongr (Nat.add_comm r n))

theorem rotateBlocks_target (n r : ℕ) (j : Fin n) :
    (rotateBlocks n r (Fin.castAdd r j)).val = r+j.val := by
  simp [rotateBlocks,Nat.add_comm]

theorem rotateBlocks_fibre (n r : ℕ) (i : Fin r) :
    (rotateBlocks n r (Fin.natAdd n i)).val = i.val := by
  simp [rotateBlocks]


def rotateLinear (n r : ℕ) : ComplexModel (n+r) ≃L[ℂ] ComplexModel (n+r) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (rotateBlocks n r)).toContinuousLinearEquiv

theorem rotateLinear_apply (n r : ℕ) (w : ComplexModel (n+r)) (i : Fin (n+r)) :
    rotateLinear n r w (rotateBlocks n r i) = w i := by
  simp [rotateLinear,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

theorem rotateLinear_plane (n r k : ℕ) (w : ComplexModel (n+r)) :
    rotateLinear n r w ∈ complexCoordinatePlane (n+r) (r+k) ↔
      ∀ j : Fin n, k ≤ j.val → w (Fin.castAdd r j) = 0 := by
  constructor
  · intro h j hj
    rw [← rotateLinear_apply n r w (Fin.castAdd r j)]
    exact h _ (by rw [rotateBlocks_target]; omega)
  · intro h i hi
    obtain ⟨a,rfl⟩ := (rotateBlocks n r).surjective i
    rw [rotateLinear_apply]
    obtain ⟨j|j,hj⟩ := finSumFinEquiv.surjective a
    · rw [← hj] at hi ⊢
      simp only [finSumFinEquiv_apply_left] at hi ⊢
      rw [rotateBlocks_target] at hi
      exact h j (by omega)
    · have hv : (rotateBlocks n r a).val = j.val := by
        rw [← hj,finSumFinEquiv_apply_right,rotateBlocks_fibre]
      rw [hv] at hi
      omega

def postcomposeLinear {d : ℕ} {p : ComplexModel d}
    (Ξ : LocalHolomorphicEquivAt (n := d) p) (L : ComplexModel d ≃L[ℂ] ComplexModel d) :
    LocalHolomorphicEquivAt (n := d) p where
  source := Ξ.source
  target := L.symm ⁻¹' Ξ.target
  isOpen_source := Ξ.isOpen_source
  isOpen_target := Ξ.isOpen_target.preimage L.symm.continuous
  center_mem_source := Ξ.center_mem_source
  toFun := fun z => L (Ξ.toFun z)
  invFun := fun z => Ξ.invFun (L.symm z)
  toFun_holomorphic := L.differentiable.differentiableOn.comp Ξ.toFun_holomorphic
    (fun _ _ => mem_univ _)
  invFun_holomorphic := Ξ.invFun_holomorphic.comp L.symm.differentiable.differentiableOn
    (fun _ hz => hz)
  mapsTo_toFun := fun z hz => by
    change L.symm (L (Ξ.toFun z)) ∈ Ξ.target
    rw [L.symm_apply_apply]; exact Ξ.mapsTo_toFun hz
  mapsTo_invFun := fun z hz => Ξ.mapsTo_invFun hz
  left_inv := fun z hz => by
    rw [L.symm_apply_apply]; exact Ξ.left_inv z hz
  right_inv := fun z hz => by
    rw [Ξ.right_inv _ hz]; exact L.apply_symm_apply z

def fibreFirstSplit (n r : ℕ) : ComplexModel (n+r) ≃L[ℂ] (ComplexModel r × ComplexModel n) :=
  ((rotateLinear n r).symm.trans (HironakaSmoothSubmersionMonomialChartPullback.splitCoordinates n r)).trans
    (ContinuousLinearEquiv.prodComm ℂ (ComplexModel n) (ComplexModel r))

def adaptedTargetProjection (n r : ℕ) (w : ComplexModel (n+r)) : ComplexModel n :=
  (fibreFirstSplit n r w).2

theorem adaptedTargetProjection_apply (n r : ℕ) (w : ComplexModel (n+r)) (j : Fin n) :
    adaptedTargetProjection n r w j = w (rotateBlocks n r (Fin.castAdd r j)) := by
  change HironakaSmoothSubmersionMonomialChartPullback.fibreProjection n r ((rotateLinear n r).symm w) j = _
  rw [HironakaSmoothSubmersionMonomialChartPullback.fibreProjection_apply]
  have he := rotateLinear_apply n r ((rotateLinear n r).symm w) (Fin.castAdd r j)
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  exact he.symm

theorem adaptedTargetProjection_plane (n r k : ℕ) (w : ComplexModel (n+r)) :
    adaptedTargetProjection n r w ∈ complexCoordinatePlane n k ↔
      w ∈ complexCoordinatePlane (n+r) (r+k) := by
  have he := rotateLinear_plane n r k ((rotateLinear n r).symm w)
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  rw [he]
  constructor
  · intro h j hj
    exact h j hj
  · intro h j hj
    exact h j hj

theorem exists_product_open_inside (n r : ℕ) (T : TopologicalSpace.Opens (ComplexModel (n+r)))
    (S₀ : TopologicalSpace.Opens (ComplexModel n)) (hT : (0 : ComplexModel (n+r)) ∈ T)
    (hS : (0 : ComplexModel n) ∈ S₀) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n)),
      (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧ (S : Set (ComplexModel n)) ⊆ S₀ ∧
      (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n))) ⊆ T := by
  have ho := T.isOpen.preimage (fibreFirstSplit n r).symm.continuous
  have hz : (0 : ComplexModel r × ComplexModel n) ∈ (fibreFirstSplit n r).symm ⁻¹' T := by
    simpa using hT
  have hn := ho.mem_nhds hz
  rw [nhds_prod_eq] at hn
  obtain ⟨A,hA,B,hB,hAB⟩ := Filter.mem_prod_iff.mp hn
  obtain ⟨R,hRA,hRo,hR0⟩ := mem_nhds_iff.mp hA
  obtain ⟨S,hSB,hSo,hS0⟩ := mem_nhds_iff.mp hB
  refine ⟨⟨R,hRo⟩,⟨S ∩ S₀,hSo.inter S₀.isOpen⟩,hR0,⟨hS0,hS⟩,inter_subset_right,?_⟩
  intro w hw
  have he := hAB ⟨hRA hw.1,hSB hw.2.1⟩
  change (fibreFirstSplit n r).symm (fibreFirstSplit n r w) ∈ T at he
  rwa [ContinuousLinearEquiv.symm_apply_apply] at he

def restrictTarget {d : ℕ} {p : ComplexModel d} (Ξ : LocalHolomorphicEquivAt (n := d) p)
    (U : TopologicalSpace.Opens (ComplexModel d)) (hU : (U : Set (ComplexModel d)) ⊆ Ξ.target)
    (hp : Ξ.toFun p ∈ U) : LocalHolomorphicEquivAt (n := d) p where
  source := Ξ.source ∩ Ξ.toFun ⁻¹' U
  target := U
  isOpen_source := Ξ.toOpenPartialHomeomorph.isOpen_inter_preimage U.isOpen
  isOpen_target := U.isOpen
  center_mem_source := ⟨Ξ.center_mem_source,hp⟩
  toFun := Ξ.toFun
  invFun := Ξ.invFun
  toFun_holomorphic := Ξ.toFun_holomorphic.mono inter_subset_left
  invFun_holomorphic := Ξ.invFun_holomorphic.mono hU
  mapsTo_toFun := fun _ hz => hz.2
  mapsTo_invFun := fun w hw => ⟨Ξ.mapsTo_invFun (hU hw),by
    change Ξ.toFun (Ξ.invFun w) ∈ U
    rwa [Ξ.right_inv w (hU hw)]⟩
  left_inv := fun z hz => Ξ.left_inv z hz.1
  right_inv := fun w hw => Ξ.right_inv w (hU hw)

section OriginalCharts
variable {n r : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]

def adaptedCoordinates {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) :
    LocalHolomorphicEquivAt (n := n+r) (chartAt (ComplexModel (n+r)) y y) :=
  postcomposeLinear (liftedCoordinatesAdd hf Φ h0) (rotateLinear n r)

theorem adaptedCoordinates_dictionary {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) :
    (adaptedCoordinates hf Φ h0).source ⊆ (chartAt (ComplexModel (n+r)) y).target ∧
    (adaptedCoordinates hf Φ h0).toFun (chartAt (ComplexModel (n+r)) y y) = 0 ∧
    ∀ z ∈ flatDomain (adaptedCoordinates hf Φ h0),
      f z ∈ flatDomain Φ ∧ ∀ j : Fin n,
      flatCoord (adaptedCoordinates hf Φ h0) (rotateBlocks n r (Fin.castAdd r j)) z =
        flatCoord Φ j (f z) := by
  obtain ⟨hsrc,hzero,hd⟩ := liftedCoordinatesAdd_dictionary hf Φ h0
  refine ⟨hsrc,?_,?_⟩
  · change rotateLinear n r ((liftedCoordinatesAdd hf Φ h0).toFun _) = 0
    rw [hzero,map_zero]
  · intro z hz
    refine ⟨(hd z hz).1,?_⟩
    intro j
    change rotateLinear n r ((liftedCoordinatesAdd hf Φ h0).toFun _) _ = _
    rw [rotateLinear_apply]
    exact (hd z hz).2 j

theorem adaptedCoordinates_whole_centre {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (C : Set X) (k : ℕ)
    (hflat : ∀ z ∈ flatDomain Φ, z ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f y) z) ∈ complexCoordinatePlane n k) :
    ∀ z ∈ flatDomain (adaptedCoordinates hf Φ h0), z ∈ f ⁻¹' C ↔
      (adaptedCoordinates hf Φ h0).toFun (chartAt (ComplexModel (n+r)) y z) ∈
        complexCoordinatePlane (n+r) (r+k) := by
  intro z hz
  have hd := (adaptedCoordinates_dictionary hf Φ h0).2.2 z hz
  change f z ∈ C ↔ _
  rw [hflat (f z) hd.1]
  change _ ↔ rotateLinear n r ((liftedCoordinatesAdd hf Φ h0).toFun _) ∈ _
  rw [rotateLinear_plane]
  constructor
  · intro h j hj
    change flatCoord (liftedCoordinatesAdd hf Φ h0) (Fin.castAdd r j) z = 0
    rw [(liftedCoordinatesAdd_dictionary hf Φ h0).2.2 z hz |>.2 j]
    exact h j hj
  · intro h j hj
    change flatCoord Φ j (f z) = 0
    rw [← (liftedCoordinatesAdd_dictionary hf Φ h0).2.2 z hz |>.2 j]
    exact h j hj


theorem exists_adapted_product_coordinates {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
      (Ψ : LocalHolomorphicEquivAt (n := n+r) (chartAt (ComplexModel (n+r)) y y)),
      (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧ (S : Set (ComplexModel n)) ⊆ Φ.target ∧
      Ψ.source ⊆ (chartAt (ComplexModel (n+r)) y).target ∧
      Ψ.toFun (chartAt (ComplexModel (n+r)) y y) = 0 ∧
      Ψ.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n))) ∧
      Ψ.toFun = (adaptedCoordinates hf Φ h0).toFun ∧
      ∀ z ∈ flatDomain Ψ,
        f z ∈ flatDomain Φ ∧
        adaptedTargetProjection n r (Ψ.toFun (chartAt (ComplexModel (n+r)) y z)) =
          Φ.toFun (chartAt (ComplexModel n) (f y) (f z)) := by
  let Ξ := adaptedCoordinates hf Φ h0
  obtain ⟨hsrc,hzero,hd⟩ := adaptedCoordinates_dictionary hf Φ h0
  have hΞ0 : (0 : ComplexModel (n+r)) ∈ Ξ.target := by
    rw [← hzero]
    exact Ξ.mapsTo_toFun Ξ.center_mem_source
  have hΦ0 : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  obtain ⟨R,S,hR0,hS0,hSΦ,hprod⟩ := exists_product_open_inside n r ⟨Ξ.target,Ξ.isOpen_target⟩
    ⟨Φ.target,Φ.isOpen_target⟩ hΞ0 hΦ0
  let U : TopologicalSpace.Opens (ComplexModel (n+r)) :=
    ⟨(fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n))),
      (R.isOpen.prod S.isOpen).preimage (fibreFirstSplit n r).continuous⟩
  have hc : Ξ.toFun (chartAt (ComplexModel (n+r)) y y) ∈ U := by
    rw [hzero]
    change fibreFirstSplit n r 0 ∈ (R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n))
    rw [map_zero]
    exact ⟨hR0,hS0⟩
  let Ψ := restrictTarget Ξ U hprod hc
  refine ⟨R,S,Ψ,hR0,hS0,hSΦ,fun q hq => hsrc hq.1,hzero,rfl,rfl,?_⟩
  intro z hz
  have hzΞ : z ∈ flatDomain Ξ := ⟨hz.1,hz.2.1⟩
  refine ⟨(hd z hzΞ).1,?_⟩
  ext j
  rw [adaptedTargetProjection_apply]
  exact (hd z hzΞ).2 j


theorem exists_adapted_product_centre_coordinates {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (C : Set X) (k : ℕ)
    (hflat : ∀ z ∈ flatDomain Φ, z ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f y) z) ∈ complexCoordinatePlane n k) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
      (Ψ : LocalHolomorphicEquivAt (n := n+r) (chartAt (ComplexModel (n+r)) y y)),
      (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧ (S : Set (ComplexModel n)) ⊆ Φ.target ∧
      Ψ.source ⊆ (chartAt (ComplexModel (n+r)) y).target ∧
      Ψ.toFun (chartAt (ComplexModel (n+r)) y y) = 0 ∧
      Ψ.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n))) ∧
      (∀ z ∈ flatDomain Ψ,
        f z ∈ flatDomain Φ ∧
        adaptedTargetProjection n r (Ψ.toFun (chartAt (ComplexModel (n+r)) y z)) =
          Φ.toFun (chartAt (ComplexModel n) (f y) (f z)) ∧
        (z ∈ f ⁻¹' C ↔ Ψ.toFun (chartAt (ComplexModel (n+r)) y z) ∈
          complexCoordinatePlane (n+r) (r+k))) ∧
      ∀ w ∈ Ψ.target,
        f ((chartAt (ComplexModel (n+r)) y).symm (Ψ.invFun w)) =
          (chartAt (ComplexModel n) (f y)).symm (Φ.invFun (adaptedTargetProjection n r w)) := by
  obtain ⟨R,S,Ψ,hR0,hS0,hSΦ,hsrc,hzero,htarget,-,hd⟩ := exists_adapted_product_coordinates hf Φ h0
  refine ⟨R,S,Ψ,hR0,hS0,hSΦ,hsrc,hzero,htarget,?_,?_⟩
  · intro z hz
    refine ⟨(hd z hz).1,(hd z hz).2,?_⟩
    change f z ∈ C ↔ _
    rw [hflat (f z) (hd z hz).1,← (hd z hz).2,adaptedTargetProjection_plane]
  · intro w hw
    let z := (chartAt (ComplexModel (n+r)) y).symm (Ψ.invFun w)
    obtain ⟨hz,hzcoord⟩ := flatInverse_mem Ψ hw hsrc
    change Ψ.toFun (chartAt (ComplexModel (n+r)) y z) = w at hzcoord
    have hforward := hd z hz
    have hcoord : adaptedTargetProjection n r w = Φ.toFun (chartAt (ComplexModel n) (f y) (f z)) := by
      simpa only [hzcoord] using hforward.2
    rw [hcoord,Φ.left_inv _ hforward.1.2]
    exact ((chartAt (ComplexModel n) (f y)).left_inv hforward.1.1).symm

end OriginalCharts
end
end Hironaka.HironakaSmoothSubmersionAdaptedProductCoordinates
