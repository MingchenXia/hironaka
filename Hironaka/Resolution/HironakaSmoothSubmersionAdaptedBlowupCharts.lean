/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionAdaptedProductCoordinates
import Hironaka.Blowup.BlowupSpaceManifold
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionAdaptedBlowupCharts
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupConstruction
  HironakaSmoothSubmersionAdaptedProductCoordinates
noncomputable section

def adaptedFibreProjection (n r : ℕ) (w : ComplexModel (n+r)) : ComplexModel r :=
  (fibreFirstSplit n r w).1

theorem adaptedFibreProjection_apply (n r : ℕ) (w : ComplexModel (n+r)) (i : Fin r) :
    adaptedFibreProjection n r w i = w (rotateBlocks n r (Fin.natAdd n i)) := by
  change HironakaSmoothSubmersionMonomialChartPullback.blockProjection n r ((rotateLinear n r).symm w) i = _
  rw [HironakaSmoothSubmersionMonomialChartPullback.blockProjection_apply]
  have he := rotateLinear_apply n r ((rotateLinear n r).symm w) (Fin.natAdd n i)
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  exact he.symm

theorem adaptedFibreProjection_monomial (n r k : ℕ) (j : Fin n) (w : ComplexModel (n+r)) :
    adaptedFibreProjection n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) =
      adaptedFibreProjection n r w := by
  ext i
  rw [adaptedFibreProjection_apply,adaptedFibreProjection_apply,monomial_apply]
  have hi : ¬ r+k ≤ (rotateBlocks n r (Fin.natAdd n i)).val := by
    rw [rotateBlocks_fibre]
    omega
  simp only [hi,false_and,if_false]

theorem adaptedTargetProjection_monomial (n r k : ℕ) (j : Fin n) (w : ComplexModel (n+r)) :
    adaptedTargetProjection n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) =
      monomial k j (adaptedTargetProjection n r w) := by
  ext i
  simp only [adaptedTargetProjection_apply,monomial_apply,rotateBlocks_target]
  have he : (rotateBlocks n r (Fin.castAdd r i) ≠ rotateBlocks n r (Fin.castAdd r j)) ↔ i ≠ j := by
    constructor
    · intro h hij
      exact h (congrArg (fun l => rotateBlocks n r (Fin.castAdd r l)) hij)
    · intro h hij
      apply h
      have hi := (rotateBlocks n r).injective hij
      apply Fin.ext
      simpa only [Fin.val_castAdd] using congrArg Fin.val hi
  have hle : r+k ≤ r+i.val ↔ k ≤ i.val := Nat.add_le_add_iff_left
  simp only [he,hle]

theorem fibreFirstSplit_monomial (n r k : ℕ) (j : Fin n) (w : ComplexModel (n+r)) :
    fibreFirstSplit n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) =
      (adaptedFibreProjection n r w,monomial k j (adaptedTargetProjection n r w)) := by
  apply Prod.ext
  · exact adaptedFibreProjection_monomial n r k j w
  · exact adaptedTargetProjection_monomial n r k j w

section OriginalCharts
variable {n r : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]

theorem exists_actual_adapted_flat_charts {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (C : Set X) (k : ℕ)
    (hflat : ∀ z ∈ flatDomain Φ, z ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f y) z) ∈ complexCoordinatePlane n k)
    (j : Fin n) (hj : k ≤ j.val) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
      (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C)),
      (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧
      c.y₀ = f y ∧ c.k = k ∧ c.j = j ∧
      c'.y₀ = y ∧ c'.k = r+k ∧ c'.j = rotateBlocks n r (Fin.castAdd r j) ∧
      c.target = monomial k j ⁻¹' (S : Set (ComplexModel n)) ∧
      c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) ∧
      ∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w) := by
  obtain ⟨R,S,Ψ,hR0,hS0,hSΦ,hΨsrc,hΨ0,hΨtarget,hd,hinv⟩ :=
    exists_adapted_product_centre_coordinates hf Φ h0 C k hflat
  have hcenter : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) ∈ S := by
    rw [h0]
    exact hS0
  let Φ' := restrictTarget Φ S hSΦ hcenter
  let c : FlatChart n C :=
    { y₀ := f y
      k := k
      Φ := Φ'
      hsrc := fun q hq => hΦsrc hq.1
      hflat := fun hz hzΦ => hflat _ ⟨hz,hzΦ.1⟩
      j := j
      hj := hj }
  let c' : FlatChart (n+r) (f ⁻¹' C) :=
    { y₀ := y
      k := r+k
      Φ := Ψ
      hsrc := hΨsrc
      hflat := fun hz hzΨ => (hd _ ⟨hz,hzΨ⟩).2.2
      j := rotateBlocks n r (Fin.castAdd r j)
      hj := by rw [rotateBlocks_target]; omega }
  have ht : c.target = monomial k j ⁻¹' (S : Set (ComplexModel n)) := rfl
  have hs : c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) := by
    ext w
    change monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w ∈ Ψ.target ↔ _
    rw [hΨtarget]
    change fibreFirstSplit n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) ∈
      (R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n)) ↔ _
    rw [fibreFirstSplit_monomial]
    rfl
  refine ⟨R,S,c,c',hR0,hS0,rfl,rfl,rfl,rfl,rfl,rfl,ht,hs,?_⟩
  intro w hw
  have hparam : monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w ∈ Ψ.target := hw
  have he := hinv _ hparam
  rw [adaptedTargetProjection_monomial] at he
  exact he


def flatChartMap {f : Y → X} {C : Set X}
    (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C)) :
    BlowupSpace (n+r) (f ⁻¹' C) → BlowupSpace n C :=
  fun p => c.invFun (adaptedTargetProjection n r (c'.toFun p))

private theorem flatChartMap_submersionAt {f : Y → X} {C : Set X}
    [Fact (IsClosedSubmanifold n C)] [Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C))]
    (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C))
    (R : TopologicalSpace.Opens (ComplexModel r))
    (hdom : c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target))
    (p : BlowupSpace (n+r) (f ⁻¹' C)) (hp : p ∈ c'.source) :
    Manifold.IsSubmersionAtOfComplement (ComplexModel r)
      𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ (flatChartMap c c') p := by
  have drop_mem {w : ComplexModel (n+r)} (hw : w ∈ c'.target) :
      adaptedTargetProjection n r w ∈ c.target := by
    rw [hdom] at hw
    exact hw.2
  have hG : flatChartMap c c' p ∈ c.source := c.map_target (drop_mem (c'.map_source hp))
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
    ((fibreFirstSplit n r).trans (ContinuousLinearEquiv.prodComm ℂ (ComplexModel r) (ComplexModel n)))
    c'.homeo c.homeo hp hG
    (IsManifold.subset_maximalAtlas (atlasHomeo_mem_atlas _ (Or.inl ⟨c',rfl⟩)))
    (IsManifold.subset_maximalAtlas (atlasHomeo_mem_atlas _ (Or.inl ⟨c,rfl⟩)))
  · intro q hq
    exact c.map_target (drop_mem (c'.map_source hq))
  · intro w hw
    have hw' : w ∈ c'.target := by
      have hw0 : w ∈ c'.homeo.target := by simpa using hw
      have ht : c'.homeo.target = c'.target := by
        exact congrArg (fun e => e.target) (atlasHomeo_toPartialEquiv c'.toPartialEquiv (Or.inl ⟨c',rfl⟩))
      rwa [ht] at hw0
    change c.toFun (c.invFun (adaptedTargetProjection n r (c'.toFun (c'.invFun w)))) =
      adaptedTargetProjection n r w
    rw [c'.right_inv hw',c.right_inv (drop_mem hw')]

theorem exists_actual_smooth_flat_chart_map {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (k : ℕ) (hflat : ∀ z ∈ flatDomain Φ, z ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f y) z) ∈ complexCoordinatePlane n k)
    (j : Fin n) (hj : k ≤ j.val) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
      (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C)),
      (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧
      c.y₀ = f y ∧ c.k = k ∧ c.j = j ∧
      c'.y₀ = y ∧ c'.k = r+k ∧ c'.j = rotateBlocks n r (Fin.castAdd r j) ∧
      c.target = monomial k j ⁻¹' (S : Set (ComplexModel n)) ∧
      c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) ∧
      ∀ p ∈ c'.source, flatChartMap c c' p ∈ c.source ∧
        Manifold.IsSubmersionAtOfComplement (ComplexModel r)
          𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ (flatChartMap c c') p ∧
        f p.base = (flatChartMap c c' p).base := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  obtain ⟨R,S,c,c',hR0,hS0,hy,hk,hj',hy',hk',hj'',ht,hs,hpoint⟩ :=
    exists_actual_adapted_flat_charts (hf.isSubmersionAt y) Φ hΦsrc h0 C k hflat j hj
  refine ⟨R,S,c,c',hR0,hS0,hy,hk,hj',hy',hk',hj'',ht,hs,?_⟩
  intro p hp
  have hw : c'.toFun p ∈ c'.target := c'.map_source hp
  have hdrop : adaptedTargetProjection n r (c'.toFun p) ∈ c.target := by
    rw [hs] at hw
    exact hw.2
  refine ⟨c.map_target hdrop,flatChartMap_submersionAt c c' R hs p hp,?_⟩
  change f p.base = (c.invFun (adaptedTargetProjection n r (c'.toFun p))).base
  rw [c.base_invFun hdrop,← c'.pt_toFun hp]
  exact hpoint _ hw

end OriginalCharts
end
end Hironaka.HironakaSmoothSubmersionAdaptedBlowupCharts
