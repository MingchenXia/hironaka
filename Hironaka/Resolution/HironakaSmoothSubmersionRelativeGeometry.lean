/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionNormalCrossings
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeMonomial
import Hironaka.Blowup.SimultaneousNormalCrossings

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSmoothSubmersionRelativeGeometry
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open NormalCrossings BlowupFlatCoordinates RegularAtDimTransport SimultaneousNormalCrossings
  DivisorExponentAlong MarkedIdeals ResolutionInvariantSpec HironakaSmoothSubmersionMonomialOrdering
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionDivisorExponents OrderTaylor RelativePrincipalizationSpan HadamardBridge
noncomputable section

private def linearCoordinates {n : ℕ} (L : ComplexModel n ≃L[ℂ] ComplexModel n) :
    LocalHolomorphicEquivAt (n := n) 0 where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := L
  invFun := L.symm
  toFun_holomorphic := L.differentiable.differentiableOn
  invFun_holomorphic := L.symm.differentiable.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => L.symm_apply_apply _
  right_inv := fun _ _ => L.apply_symm_apply _

private theorem regularAtDim_of_coordinate_family {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {A : Set X} {x : X}
    (hx : x ∈ A) (S : Finset (Fin n))
    (hA : IsCoordinateFamilyAt n (fun _ : Unit => A) (fun _ => S) x) :
    RegularAtDim (n := n) A x (n-S.card) := by
  classical
  obtain ⟨Φ,hsrc,h0,hflat⟩ := hA
  obtain ⟨σ,hσ⟩ := exists_perm_nested (X := S) (Y := S) subset_rfl
  let L : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).toContinuousLinearEquiv
  have happ (u : ComplexModel n) (i : Fin n) : L u (σ i) = u i := by
    simp [L,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
  let Ψ := LocalHolomorphicEquivAt.comp Φ (linearCoordinates L) h0
  refine ⟨Nat.sub_le _ _,hx,Ψ,fun u hu => hsrc hu.1,?_,?_⟩
  · change L (Φ.toFun _) = 0
    rw [h0,map_zero]
  · intro z hz hzΨ
    have h := hflat () hx hz hzΨ.1
    change z ∈ A ↔ L (Φ.toFun ((complexChartAt (n := n) x).val z)) ∈
      complexCoordinatePlane n (n-S.card)
    rw [h]
    constructor
    · intro hu j hj
      obtain ⟨i,rfl⟩ := σ.surjective j
      rw [happ]
      exact hu i ((hσ i).1.mp hj)
    · intro hu i hi
      rw [← happ]
      exact hu (σ i) ((hσ i).1.mpr hi)

private theorem card_last_coordinates (n j : ℕ) (hj : j ≤ n) :
    (Finset.univ.filter fun i : Fin n => j ≤ i.val).card = n-j := by
  classical
  let e : Fin (n-j) ↪ Fin n :=
    ⟨fun i => ⟨j+i.val,by omega⟩,fun a b h => Fin.ext (by
      have h' := congrArg Fin.val h
      change j+a.val = j+b.val at h'
      omega)⟩
  have he : Finset.univ.map e = Finset.univ.filter fun i : Fin n => j ≤ i.val := by
    ext i
    simp only [Finset.mem_map,Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨a,rfl⟩
      change j ≤ j+a.val
      omega
    · intro hi
      refine ⟨⟨i.val-j,by omega⟩,?_⟩
      apply Fin.ext
      change j+(i.val-j) = i.val
      omega
  rw [← he,Finset.card_map,Finset.card_fin]

variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- One internally lifted chart supplies every whole original family member with the same cutting indices. -/
theorem isCoordinateFamilyAt_preimage_submersion {ι : Type*} {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (A : ι → Set X) (S : ι → Finset (Fin n)) (hA : IsCoordinateFamilyAt n A S (f y)) :
    ∃ ρ : Fin n ↪ Fin m,
      IsCoordinateFamilyAt m (fun i => f ⁻¹' A i) (fun i => (S i).map ρ) y := by
  classical
  obtain ⟨Φ,hsrc,h0,hflat⟩ := hA
  obtain ⟨Ξ,ρ,hΞsrc,hΞ0,hΞdict⟩ :=
    exists_lifted_coordinates (n := n) (m := m) (f := f) (y := y) hf Φ h0
  refine ⟨ρ,Ξ,hΞsrc,hΞ0,?_⟩
  intro i hyi z hz hzΞ
  have hd := hΞdict z ⟨hz,hzΞ⟩
  have horig := hflat i hyi hd.1.1 hd.1.2
  change f z ∈ A i ↔ Ξ.toFun (chartAt (ComplexModel m) y z) ∈ coordSubspace ((S i).map ρ)
  rw [horig]
  constructor
  · intro h j hj
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hj
    change flatCoord Ξ (ρ l) z = 0
    rw [hd.2 l]
    exact h l hl
  · intro h j hj
    change flatCoord Φ j (f z) = 0
    rw [← hd.2 j]
    exact h (ρ j) (Finset.mem_map_of_mem ρ hj)

/-- True original regularity produces the actual preimage flattening with the exact added fibre dimension. -/
theorem regularAtDim_preimage_submersion {f : Y → X} {y : Y}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
    {N : Set X} {j : ℕ} (hN : RegularAtDim (n := n) N (f y) j) :
    RegularAtDim (n := m) (f ⁻¹' N) y (j+(m-n)) := by
  classical
  obtain ⟨hj,hyN,Φ,hsrc,h0,hflat⟩ := hN
  let S := Finset.univ.filter fun i : Fin n => j ≤ i.val
  have hcoord : IsCoordinateFamilyAt n (fun _ : Unit => N) (fun _ => S) (f y) :=
    ⟨Φ,hsrc,h0,fun _ _ _ hz hzΦ => by
      simpa only [S,coordSubspace_eq_complexCoordinatePlane] using hflat hz hzΦ⟩
  obtain ⟨ρ,hρ⟩ := isCoordinateFamilyAt_preimage_submersion hf _ _ hcoord
  have hymem : y ∈ f ⁻¹' N := hyN
  have hreg := regularAtDim_of_coordinate_family (A := f ⁻¹' N) (x := y) hymem (S.map ρ) hρ
  have hc : (S.map ρ).card = n-j := by
    rw [Finset.card_map]
    exact card_last_coordinates n j hj
  have hn := dimension_le_of_submersionAt hf
  have he : m-(S.map ρ).card = j+(m-n) := by rw [hc]; omega
  exact he ▸ hreg

variable {f : Y → X}
variable (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
include hf

/-- Actual closed original submanifolds have genuine closed submanifold preimages. -/
theorem isClosedSubmanifold_preimage_submersion {N : Set X} (hN : IsClosedSubmanifold n N) :
    IsClosedSubmanifold m (f ⁻¹' N) := by
  refine ⟨hN.1.preimage hf.contMDiff.continuous,?_⟩
  intro y hy
  obtain ⟨j,hj⟩ := hN.2 (f y) hy
  exact ⟨j+(m-n),regularAtDim_preimage_submersion (hf.isSubmersionAt y) hj⟩

/-- Actual normal crossings of the original centre pull back with the entire indexed boundary. -/
theorem hasNormalCrossings_preimage_submersion {C : Set X} {E : List (Set X)}
    (hC : HasNormalCrossings n C E) :
    HasNormalCrossings m (f ⁻¹' C) (E.map (f ⁻¹' ·)) := by
  classical
  intro y hy
  obtain ⟨S₀,S,hcoord,hcard⟩ := hC (f y) hy
  obtain ⟨ρ,hρ⟩ := isCoordinateFamilyAt_preimage_submersion (hf.isSubmersionAt y) _ _ hcoord
  let ix : Fin (E.map (f ⁻¹' ·)).length → Fin E.length := fun i =>
    ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
  have hget : ∀ i : Fin (E.map (f ⁻¹' ·)).length,
      (E.map (f ⁻¹' ·)).get i = f ⁻¹' E.get (ix i) := by
    intro i
    simp only [List.get_eq_getElem,List.getElem_map]
    rfl
  refine ⟨S₀.map ρ,fun i => (S (ix i)).map ρ,?_,?_⟩
  · exact NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hρ (Option.map ix)
      (fun o => by cases o with
        | none => rfl
        | some i => exact hget i)
      (fun o => by cases o <;> rfl)
  · intro i hyi
    rw [Finset.card_map]
    exact hcard (ix i) (by simpa only [hget,mem_preimage] using hyi)

/-- Original transversality is internally retained by the injective actual coordinate map. -/
theorem isTransverse_preimage_submersion {N : Set X} {E : List (Set X)}
    (hN : IsTransverse n N E) :
    IsTransverse m (f ⁻¹' N) (E.map (f ⁻¹' ·)) := by
  classical
  intro y hy
  obtain ⟨S₀,S,hcoord,hcard⟩ := hN (f y) hy
  obtain ⟨ρ,hρ⟩ := isCoordinateFamilyAt_preimage_submersion (hf.isSubmersionAt y) _ _ hcoord
  let ix : Fin (E.map (f ⁻¹' ·)).length → Fin E.length := fun i =>
    ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
  have hget : ∀ i : Fin (E.map (f ⁻¹' ·)).length,
      (E.map (f ⁻¹' ·)).get i = f ⁻¹' E.get (ix i) := by
    intro i
    simp only [List.get_eq_getElem,List.getElem_map]
    rfl
  refine ⟨S₀.map ρ,fun i => (S (ix i)).map ρ,?_,?_⟩
  · exact NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hρ (Option.map ix)
      (fun o => by cases o with
        | none => rfl
        | some i => exact hget i)
      (fun o => by cases o <;> rfl)
  · intro i hyi
    have h := hcard (ix i) (by simpa only [hget,mem_preimage] using hyi)
    exact ⟨by simpa only [Finset.card_map] using h.1,by simpa using h.2⟩

omit [IsComplexManifold m Y] in
/-- The genuine section/filter equality produces a nonzero germ along the whole original preimage. -/
theorem isNonzeroAlongAt_preimage_submersion {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {y : Y} (hne : IsNonzeroAlongAt N I (f y)) :
    IsNonzeroAlongAt (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) y := by
  obtain ⟨g,hg,hfreq⟩ := hne
  refine ⟨g ∘ f,?_,?_⟩
  · have hfh : ∀ᶠ w in 𝓝 y, MDifferentiableAt
        𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w :=
      Eventually.of_forall fun w => (hf.contMDiff w).mdifferentiableAt (by simp)
    exact GermIdeal.mem_pullback_iff.mpr <| isInSpanAt_of_eq_mul ⟨g,hg,rfl⟩
      (holomorphicAt_comp_map hfh (GermIdeal.IsCoherent.holomorphicAt_mem hI hg)) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp)
  · rw [← map_nhds_submersion_eq (hf.isSubmersionAt y),Filter.frequently_map] at hfreq
    exact hfreq

/-- Every genuine original well-formed field is internally supplied on the entire actual marked preimage. -/
theorem isWellFormed_markedPullback_submersion (M : MarkedIdeal n X) (hM : M.IsWellFormed) :
    (HironakaSmoothSubmersionCoefficientIdeals.markedPullback (m := m) f M).IsWellFormed where
  isClosedSubmanifold_N := isClosedSubmanifold_preimage_submersion hf hM.isClosedSubmanifold_N
  isCoherent := GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hM.isCoherent
  isSNCDivisor := isSNCDivisor_preimage_submersion hf M.E hM.isSNCDivisor
  isTransverse := isTransverse_preimage_submersion hf hM.isTransverse

/-- Genuine original invariant domains produce the whole actual domain with the correct added fibre dimension. -/
theorem isInvDomain_markedPullback_submersion (M : MarkedIdeal n X) {k : ℕ}
    (hM : IsInvDomain k M) :
    IsInvDomain (k+(m-n))
      (HironakaSmoothSubmersionCoefficientIdeals.markedPullback (m := m) f M) where
  isWellFormed := isWellFormed_markedPullback_submersion hf M hM.isWellFormed
  dimLE := by
    intro y hy
    obtain ⟨j,hjk,hj⟩ := hM.dimLE (f y) hy
    exact ⟨j+(m-n),Nat.add_le_add_right hjk _,
      regularAtDim_preimage_submersion (hf.isSubmersionAt y) hj⟩
  one_le_d := hM.one_le_d
  isNonzeroAlongAt := fun y hy =>
    isNonzeroAlongAt_preimage_submersion hf hM.isWellFormed.isCoherent (hM.isNonzeroAlongAt (f y) hy)

end
end Hironaka.HironakaSmoothSubmersionRelativeGeometry
