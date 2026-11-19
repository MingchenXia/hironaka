import Hironaka.Resolution.HironakaActualLocalTangentGenerators
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPointwiseDerivativeGenerators
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GermIdealOrder DerivativeIdealAlong GiraudAlong TangentDirectionAlong
open DerivativeIdealAlongCoherent RelativePrincipalizationSpan BlowupFlatCoordinates
open HironakaActualLocalTangentGenerators
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
 [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {N : Set M} {I : GermIdeal n M} {x : M} {k : ℕ}

theorem exists_iterated_local_generators
 (hI : I.IsCoherent) (hN : RegularAtDim (n := n) N x k) :
 ∀ j : ℕ, ∃ (U : Set M), IsOpen U ∧ x ∈ U ∧
   ∃ (r : ℕ) (s : Fin r → M → ℂ),
     (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U) ∧
     ∀ y ∈ U, ∀ g, (iterDerivIdealAlong N I j).mem y g ↔
       IsInSpanAt (n := n) (· ∈ range s) y g
 | 0 => hI x
 | j+1 => by
  classical
  obtain ⟨U, hUo, hxU, r, s, hs, hgen⟩ := exists_iterated_local_generators hI hN j
  obtain ⟨-, -, Φ, hΦsrc, -, hflat⟩ := hN
  have hU'o : IsOpen (U ∩ flatDomain Φ) := hUo.inter (isOpen_flatDomain Φ)
  have hhol : ∀ i, ∀ z ∈ U, HolomorphicAt n (s i) z := fun i z hz =>
    eventually_of_mem (hUo.mem_nhds hz) fun w hw => (hs i w hw).mdifferentiableAt (hUo.mem_nhds hw)
  have hfam : ∀ c z, z ∈ U ∩ flatDomain Φ → HolomorphicAt n (derivFamilyAlong Φ k s c) z := by
    rintro (i | j | ij) z hz
    · exact hhol i z hz.1
    · by_cases hj : k ≤ j.1
      · simpa [derivFamilyAlong, hj] using holomorphicAt_flatCoord Φ j hz.2
      · simpa [derivFamilyAlong, hj] using holomorphicAt_const (n := n) (x := z) (0 : ℂ)
    · by_cases hj : ij.2.1 < k
      · simpa [derivFamilyAlong, hj] using holomorphicAt_flatPartial ij.2 hz.2 (hhol ij.1 z hz.1)
      · simpa [derivFamilyAlong, hj] using holomorphicAt_const (n := n) (x := z) (0 : ℂ)
  let eqv := Fintype.equivFin (Fin r ⊕ Fin n ⊕ (Fin r × Fin n))
  refine ⟨U ∩ flatDomain Φ, hU'o, ⟨hxU, mem_flatDomain_self Φ⟩,
    Fintype.card (Fin r ⊕ Fin n ⊕ (Fin r × Fin n)), fun c => derivFamilyAlong Φ k s (eqv.symm c), ?_, ?_⟩
  · intro c z hz
    exact (hfam _ z hz).self_of_nhds.mdifferentiableWithinAt
  · intro z hz g
    have hrange : range (fun c => derivFamilyAlong Φ k s (eqv.symm c)) = range (derivFamilyAlong Φ k s) := by
      ext t
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨eqv c, by simp⟩
    rw [hrange]
    exact derivIdealAlong_mem_iff_of_generators hΦsrc hflat hU'o inter_subset_right
      (fun i => (hs i).mono inter_subset_left) (fun w hw => hgen w hw.1) hz g

theorem exists_tangent_of_coherent_pointwise_regular
 (hI : I.IsCoherent) (hN : RegularAtDim (n := n) N x k) {d : ℕ} (hd : 1 ≤ d)
 (hx : x ∈ cosupport n N I d) (hmax : ¬ OrderGE n N I x (d+1)) :
 ∃ (U : Set M) (u : M → ℂ), x ∈ U ∧ IsTangentDirectionAlong N I d U u := by
 apply exists_tangent_of_local_generators (fun y g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hN hd hx hmax
 exact exists_iterated_local_generators hI hN (d-1)
end
end Hironaka.HironakaActualPointwiseDerivativeGenerators
