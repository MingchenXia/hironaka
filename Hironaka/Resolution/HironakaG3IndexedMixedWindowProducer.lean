import Hironaka.Resolution.HironakaG3OrderedFiniteWindows
import Hironaka.Resolution.HironakaG3LocalMixedSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedWindowProducer
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers RestrictEmptyTower NormalCrossings HironakaBaseChange
  HironakaAdmissibleSequence HironakaEmbeddedAnalyticLocal HironakaG3FiniteMixedBadLocus
  HironakaG3LocalMixedSeparation HironakaG3MixedOrderedSeparation HironakaG3OrderedFiniteWindows
  HironakaActualLocallyFiniteBoundary

/-- Any sorted finite component and indexed-boundary windows produce an
actual local mixed separator, even when components lie inside the boundary. -/
theorem sorted_window_producer {n : ℕ} {X B₀ : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (s : Finset ι) (r : Finset κ)
    (b : B₀ → X) (hb : IsOpenHoloEmbedding n b)
    (hK : ∃ K : Set X, IsCompact K ∧ range b ⊆ K) :
    let l := s.sort (· ≤ ·)
    let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
    ∃ (Y : CMfd.{0} n) (T : BlowupTower B₀ Y) (Ef : List (Set Y)),
      CanonicalMixedSeparation (((r.sort (· ≤ ·)).map D).map (b ⁻¹' ·))
        (l.map (fun a => (b ⁻¹' (V a).carrier,(V a).dim))) T Ef ∧
      CentresOver (b ⁻¹' mixedBadLocus W) T ∧
      IsAdmissibleBlowupSequence n B₀ (((r.sort (· ≤ ·)).map D).map (b ⁻¹' ·))
        (b ⁻¹' mixedBadLocus W) Y T.proj Ef ∧ IsSNCDivisor n Ef ∧
      (List.finRange l.length).Pairwise (fun a c =>
        Disjoint (strictTransform n T.proj (b ⁻¹' (W a).carrier))
          (strictTransform n T.proj (b ⁻¹' (W c).carrier))) := by
  dsimp only
  let l := s.sort (· ≤ ·)
  let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
  have he : Injective l.get := (s.sort_nodup (· ≤ ·)).injective_get
  obtain ⟨Y,T,Ef,hTree,hOver,hAdm,hEf,hDis⟩ := exists_local_irreducible_mixed_separation W
    (fun a => hDim (l.get a))
    (fun a c hac => hDistinct (l.get a) (l.get c) (fun h => hac (he h)))
    ((r.sort (· ≤ ·)).map D) (sorted_boundary_snc D hD r) b hb hK
  refine ⟨Y,T,Ef,?_,hOver,hAdm,hEf,hDis⟩
  have hmap : (List.finRange l.length).map (fun a => (b ⁻¹' (W a).carrier,(W a).dim)) =
      l.map (fun a => (b ⁻¹' (V a).carrier,(V a).dim)) := by
    change (List.finRange l.length).map ((fun a => (b ⁻¹' (V a).carrier,(V a).dim)) ∘ l.get) = _
    rw [← List.map_map,List.map_get_finRange]
  rw [← hmap]
  exact hTree
end
end Hironaka.HironakaG3IndexedMixedWindowProducer
