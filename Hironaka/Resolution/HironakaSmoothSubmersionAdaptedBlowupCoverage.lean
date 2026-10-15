/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionAdaptedBlowupCharts
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionAdaptedBlowupCoverage
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupConstruction BlowupSpaceTangent
  BlowupMonomialCharts HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaSmoothSubmersionAdaptedBlowupCharts
noncomputable section

theorem exists_original_target_normal_index (n r k : ℕ) (a : Fin (n+r)) (ha : r+k ≤ a.val) :
    ∃! j : Fin n, k ≤ j.val ∧ rotateBlocks n r (Fin.castAdd r j) = a := by
  let j : Fin n := ⟨a.val-r,by omega⟩
  have he : rotateBlocks n r (Fin.castAdd r j) = a := by
    apply Fin.ext
    rw [rotateBlocks_target]
    dsimp [j]
    omega
  refine ⟨j,⟨by dsimp [j]; omega,he⟩,?_⟩
  intro i hi
  have hval := congrArg Fin.val (hi.2.trans he.symm)
  simp only [rotateBlocks_target] at hval
  exact Fin.ext (by omega)

section OriginalCharts
variable {n r : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]

theorem exists_actual_matching_flat_chart_at_exceptional_point {f : Y → X} {C : Set X}
    (p : BlowupSpace (n+r) (f ⁻¹' C)) (hpC : p.base ∈ f ⁻¹' C)
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f p.base)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f p.base) (f p.base)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f p.base)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f p.base) (f p.base)) = 0)
    (k : ℕ) (hflat : ∀ z ∈ flatDomain Φ, z ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f p.base) z) ∈ complexCoordinatePlane n k) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
      (j : Fin n) (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C)),
      k ≤ j.val ∧ (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧
      c.y₀ = f p.base ∧ c.k = k ∧ c.j = j ∧
      c'.y₀ = p.base ∧ c'.k = r+k ∧ c'.j = rotateBlocks n r (Fin.castAdd r j) ∧
      c.target = monomial k j ⁻¹' (S : Set (ComplexModel n)) ∧
      c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) ∧
      p ∈ c'.source ∧
      ∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w) := by
  obtain ⟨R,S,Ψ,hR0,hS0,hSΦ,hΨsrc,hΨ0,hΨtarget,hd,hinv⟩ :=
    exists_adapted_product_centre_coordinates hf Φ h0 C k hflat
  have hΨflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel (n+r)) p.base).source →
      chartAt (ComplexModel (n+r)) p.base z ∈ Ψ.source →
      (z ∈ f ⁻¹' C ↔ Ψ.toFun (chartAt (ComplexModel (n+r)) p.base z) ∈
        complexCoordinatePlane (n+r) (r+k)) := fun hz hΨ => (hd _ ⟨hz,hΨ⟩).2.2
  have hnot := BlowupSpace.dirVec_not_mem hpC
  rw [mem_tangentSpace_iff hΨsrc hΨflat (mem_flatDomain_self Ψ) hpC] at hnot
  push Not at hnot
  obtain ⟨a,ha,hne⟩ := hnot
  obtain ⟨j,⟨hj,hja⟩,-⟩ := exists_original_target_normal_index n r k a ha
  have hcenter : Φ.toFun (chartAt (ComplexModel n) (f p.base) (f p.base)) ∈ S := by
    rw [h0]
    exact hS0
  let Φ' := restrictTarget Φ S hSΦ hcenter
  let c : FlatChart n C :=
    { y₀ := f p.base
      k := k
      Φ := Φ'
      hsrc := fun q hq => hΦsrc hq.1
      hflat := fun hz hzΦ => hflat _ ⟨hz,hzΦ.1⟩
      j := j
      hj := hj }
  let c' : FlatChart (n+r) (f ⁻¹' C) :=
    { y₀ := p.base
      k := r+k
      Φ := Ψ
      hsrc := hΨsrc
      hflat := hΨflat
      j := rotateBlocks n r (Fin.castAdd r j)
      hj := by rw [hja]; exact ha }
  have ht : c.target = monomial k j ⁻¹' (S : Set (ComplexModel n)) := rfl
  have hs : c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) := by
    ext w
    change monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w ∈ Ψ.target ↔ _
    rw [hΨtarget]
    change fibreFirstSplit n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) ∈
      (R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n)) ↔ _
    rw [fibreFirstSplit_monomial]
    rfl
  have hp : p ∈ c'.source := by
    refine ⟨mem_flatDomain_self Ψ,?_⟩
    change extVal (flatCoord Ψ (rotateBlocks n r (Fin.castAdd r j))) p ≠ 0
    rw [extVal_of_mem hpC,hja]
    exact hne
  refine ⟨R,S,j,c,c',hj,hR0,hS0,rfl,rfl,rfl,rfl,rfl,rfl,ht,hs,hp,?_⟩
  intro w hw
  have hparam : monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w ∈ Ψ.target := hw
  have he := hinv _ hparam
  rw [adaptedTargetProjection_monomial] at he
  exact he


theorem exists_original_exceptional_matching_charts {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) :
    IsClosedSubmanifold (n+r) (f ⁻¹' C) ∧
    ∀ (p : BlowupSpace (n+r) (f ⁻¹' C)), p.base ∈ f ⁻¹' C →
      ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
        (k : ℕ) (j : Fin n) (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C)),
        k ≤ j.val ∧ (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧
        c.y₀ = f p.base ∧ c.k = k ∧ c.j = j ∧
        c'.y₀ = p.base ∧ c'.k = r+k ∧ c'.j = rotateBlocks n r (Fin.castAdd r j) ∧
        c.target = monomial k j ⁻¹' (S : Set (ComplexModel n)) ∧
        c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) ∧
        p ∈ c'.source ∧
        ∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w) := by
  refine ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC,?_⟩
  intro p hpC
  obtain ⟨k,-,-,Φ,hΦsrc,h0,hflat⟩ := hC.2 (f p.base) hpC
  obtain ⟨R,S,j,c,c',hj,hR0,hS0,hy,hk,hj',hy',hk',hj'',ht,hs,hp,hpoint⟩ :=
    exists_actual_matching_flat_chart_at_exceptional_point p hpC (hf.isSubmersionAt p.base)
      Φ hΦsrc h0 k (fun z hz => hflat hz.1 hz.2)
  exact ⟨R,S,k,j,c,c',hj,hR0,hS0,hy,hk,hj',hy',hk',hj'',ht,hs,hp,hpoint⟩

end OriginalCharts
end
end Hironaka.HironakaSmoothSubmersionAdaptedBlowupCoverage
