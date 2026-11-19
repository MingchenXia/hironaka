import Hironaka.Resolution.HironakaActualNonregularCompanionNaturality
import Hironaka.Invariant.ContactEquivalenceAlong

/-! A tangent direction on an actual open restriction is a genuine tangent
direction of the SAME original ambient function on its actual open image.
Only the original coherent ideal and closed smooth carrier are assumed;
no global holomorphic extension or tangent certificate downstairs is input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOpenTangentDescent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers RelativePrincipalizationSpan GermIdealPullbackCalculus GermIdealTotalTransform
  TangentDirectionAlong DerivativeIdealAlong DerivativeIdealAlongCoherent DerivativeIdealAlongEtale
  HironakaActualNonregularCompanionNaturality GiraudAlong InvertibleIdealQuotient
variable {n : ℕ} {X : CMfd.{u} n}

theorem isTangentDirectionAlong_of_open_pullback
    (N : Set X) (hN : IsClosedSubmanifold n N) (I : GermIdeal n X) (hI : I.IsCoherent)
    (μ : ℕ) (U : Opens X) (W : Set U) (v : X → ℂ)
    (hu : IsTangentDirectionAlong ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) μ W (v ∘ Subtype.val)) :
    IsTangentDirectionAlong N I μ ((Subtype.val : U → X) '' W) v := by
  have hIhol : ∀x g,I.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  have hD := isCoherent_iterDerivIdealAlong hI hN (μ-1)
  have hDhol : ∀x g,(iterDerivIdealAlong N I (μ-1)).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hD hg
  have hMem (p : U) (hp : p∈W) : (iterDerivIdealAlong N I (μ-1)).mem p.val v := by
    have hpu := hu.mem p hp
    rw [←pullback_val_iterDerivIdealAlong U hIhol (μ-1)] at hpu
    have hi := isLocalInverseAt_val (n := n) U p
    have hg := (mem_pullback_iff_of_span_closed hDhol
      (fun _ _ hg => GermIdealTotalTransform.mem_of_isInSpanAt_mem hD hg) hi).mp hpu
    have heq : ((v ∘ Subtype.val) ∘ openInv U p)=ᶠ[𝓝 p.val] v := by
      filter_upwards [hi.right_inv] with x hx
      exact congrArg v hx
    exact GermIdealTotalTransform.mem_of_isInSpanAt_mem hD
      (DerivativeIdeal.isInSpanAt_congr (isInSpanAt_self hg (hDhol _ _ hg)) heq)
  refine ⟨U.isOpen.isOpenMap_subtype_val _ hu.isOpen,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := hx
    exact hMem p hp
  · intro x hx hx0
    obtain ⟨p,hp,rfl⟩ := hx
    obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one p hp hx0
    have hi := isLocalInverseAt_val (n := n) U p
    have hAt := hi.left_inv.self_of_nhds
    have hξ' : IsTangentField ((Subtype.val : U → X) ⁻¹' N) e ξ (openInv U p p.val) := by
      rw [hAt]
      exact hξ
    let e' := complexChartAt (n := n) p.val
    let ξ' := transferField (openInv U p) (Subtype.val : U → X) e e' ξ
    have ht : IsTangentField ((openInv U p) ⁻¹' ((Subtype.val : U → X) ⁻¹' N)) e' ξ' p.val :=
      isTangentField_transfer hi.symm (mem_complexChartAt_source p.val) hξ'
    have hSet : ∀ᶠx in 𝓝 p.val,
        x∈(openInv U p) ⁻¹' ((Subtype.val : U → X) ⁻¹' N) ↔ x∈N := by
      filter_upwards [hi.right_inv] with x hx
      change (openInv U p x).val∈N ↔ x∈N
      rw [hx]
    have htN := isTangentField_congr_set ht hSet
    have hvhol := holomorphicAt_of_mem_iterDerivIdealAlong hIhol (μ-1) p.val v (hMem p hp)
    have hd := (fieldDeriv_transfer hi.symm (mem_complexChartAt_source p.val) hξ'.mem_source ξ hvhol).self_of_nhds
    change fieldDeriv e' ξ' v p.val=fieldDeriv e ξ (v ∘ Subtype.val) (openInv U p p.val) at hd
    rw [hAt] at hd
    exact ⟨e',ξ',htN,by rw [hd];exact hne⟩

end
end Hironaka.HironakaActualOpenTangentDescent
