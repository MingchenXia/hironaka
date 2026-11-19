import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Paracompactness of the same original source of an actual proper map

Whole compact fibres yield finite original cover families. Native closedness
spreads these to actual target neighborhoods, and a native locally finite
refinement on the original base pulls back to the same source.
No source/countability/compactness certificate or new space record is input.
Blueprint: `embedded-blowup-paracompact.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Topology

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupParacompact

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem exists_finite_fibre_neighborhood {α : Type*}
    (p : Y → X) (hp : IsProperMap p) (O : α → Set Y)
    (hO : ∀ a, IsOpen (O a)) (hcover : ⋃ a, O a = univ) (x : X) :
    ∃ (s : Finset α) (W : Set X), IsOpen W ∧ x ∈ W ∧
      p ⁻¹' W ⊆ ⋃ a ∈ s, O a := by
  classical
  obtain ⟨s, hs⟩ := (hp.isCompact_preimage (K := {x}) isCompact_singleton).elim_finite_subcover
    O hO (by rw [hcover]; exact subset_univ _)
  let A : Set Y := ⋃ a ∈ s, O a
  have hA : IsOpen A := isOpen_iUnion fun a => isOpen_iUnion fun _ => hO a
  let W : Set X := (p '' Aᶜ)ᶜ
  have hW : IsOpen W := (hp.isClosedMap _ hA.isClosed_compl).isOpen_compl
  refine ⟨s, W, hW, ?_, ?_⟩
  · rintro ⟨y, hy, hpy⟩
    exact hy (hs hpy)
  · intro y hy
    by_contra hyA
    exact hy ⟨y, hyA, rfl⟩

/-- Derive the native paracompactness class on the SAME original source
from the actual proper map and original target paracompactness. -/
theorem paracompactSpace_of_isProperMap [ParacompactSpace X]
    (p : Y → X) (hp : IsProperMap p) : ParacompactSpace Y := by
  classical
  constructor
  intro α O hO hcover
  choose S W hW hxW hcontain using exists_finite_fibre_neighborhood p hp O hO hcover
  obtain ⟨V, hVo, hVcover, hVfinite, hVsub⟩ := precise_refinement W hW
    (iUnion_eq_univ_iff.mpr (fun x => ⟨x, hxW x⟩))
  let B := (x : X) × S x
  let T : B → Set Y := fun b => p ⁻¹' V b.1 ∩ O b.2.val
  have hTo : ∀ b, IsOpen (T b) := fun b =>
    ((hVo b.1).preimage hp.continuous).inter (hO b.2.val)
  have hTcover : ⋃ b, T b = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro y
    obtain ⟨x, hx⟩ := iUnion_eq_univ_iff.mp hVcover (p y)
    have hyA : y ∈ ⋃ a ∈ S x, O a := hcontain x (hVsub x hx)
    obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hyA
    exact ⟨⟨x, a, ha⟩, hx, hya⟩
  have hTfinite : LocallyFinite T := by
    intro y
    obtain ⟨N, hN, hfinite⟩ := (hVfinite.preimage_continuous hp.continuous) y
    refine ⟨N, hN, (hfinite.biUnion fun x _ => finite_range (Sigma.mk x)).subset ?_⟩
    rintro ⟨x, a, ha⟩ ⟨z, ⟨hzV, _hzO⟩, hzN⟩
    exact mem_iUnion₂.mpr ⟨x, ⟨z, hzV, hzN⟩, mem_range_self (⟨a, ha⟩ : S x)⟩
  refine ⟨range T, (Subtype.val : range T → Set Y), ?_, ?_, hTfinite.on_range, ?_⟩
  · rintro ⟨_, ⟨b, rfl⟩⟩
    exact hTo b
  · rw [iUnion_subtype, biUnion_range]
    exact hTcover
  · rintro ⟨_, ⟨b, rfl⟩⟩
    exact ⟨b.2.val, inter_subset_right⟩

end Hironaka.Analytic.Unibranch.EmbeddedBlowupParacompact
