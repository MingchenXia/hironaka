/- Complete original prerequisites; statements and mathematical proofs are unchanged. -/
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedIdeal

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaOriginalGlobalPrincipalization

noncomputable section



open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences


open RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus


section OpenDescent

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {ι : Type v}



/-- A coherent ideal is invertible if its actual restrictions to a covering family
of open subsets are invertible. -/
theorem isInvertible_of_open_cover {𝔞 : GermIdeal n Y} (h𝔞 : 𝔞.IsCoherent)
    (O : ι → Opens Y) (hcover : ∀ y : Y, ∃ i, y ∈ O i)
    (hinv : ∀ i, (GermIdeal.pullback (m := n) (Subtype.val : O i → Y) 𝔞).IsInvertible) :
    𝔞.IsInvertible := by
  intro y
  obtain ⟨i, hy⟩ := hcover y
  obtain ⟨U, hU, hyU, h, hh, hnon, hgen⟩ := hinv i ⟨y, hy⟩
  let H := extendOpens (O i) h
  have hH : H ∘ (Subtype.val : O i → Y) = h :=
    funext fun q => extendOpens_val (O i) h q
  refine ⟨Subtype.val '' U, (O i).isOpen.isOpenMap_subtype_val U hU,
    ⟨⟨y, hy⟩, hyU, rfl⟩, H, ?_, ?_, ?_⟩
  · rintro z ⟨q, hq, rfl⟩
    have hq' : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
        (H ∘ (Subtype.val : O i → Y)) q := by
      rw [hH]
      exact (hh q hq).mdifferentiableAt (hU.mem_nhds hq)
    exact ((mdifferentiableAt_comp_val_iff (O i)).mp hq').mdifferentiableWithinAt
  · rintro W hW hWU ⟨z, hz⟩
    have hsub : (Subtype.val : O i → Y) ⁻¹' W ⊆ U := by
      intro q hq
      obtain ⟨q', hq', he⟩ := hWU hq
      exact (Subtype.ext he : q' = q) ▸ hq'
    have hne : ((Subtype.val : O i → Y) ⁻¹' W).Nonempty := by
      obtain ⟨q, _, he⟩ := hWU hz
      refine ⟨q, ?_⟩
      change q.val ∈ W
      rw [he]
      exact hz
    obtain ⟨q, hq, hq0⟩ := hnon _ (hW.preimage continuous_subtype_val) hsub hne
    exact ⟨q.val, hq, by simpa only [H, extendOpens_val] using hq0⟩
  · rintro z ⟨q, hq, rfl⟩ g
    have hge : extendOpens (O i) (g ∘ Subtype.val) =ᶠ[𝓝 q.val] g := by
      filter_upwards [(O i).isOpen.mem_nhds q.property] with z hz
      exact extendOpens_val (O i) (g ∘ Subtype.val) ⟨z, hz⟩
    constructor
    · intro hg
      have hlocal := (hgen q hq (g ∘ Subtype.val)).mp
        (MarkedIdealRestrictOpen.comp_val_mem_pullback_val (O i) h𝔞 hg)
      have hspan : IsInSpanAt (n := n) (· = H) q.val
          (extendOpens (O i) (g ∘ Subtype.val)) :=
        (isInSpanAt_comp_val_iff (O i)).mp (hlocal.mono fun s hs => by
          exact ⟨H, rfl, hs.trans hH.symm⟩)
      exact IsInSpanAt.congr' hspan hge
    · intro hg
      have hlocal : IsInSpanAt (n := n) (· = h) q (g ∘ Subtype.val) :=
        (isInSpanAt_comp contMDiff_subtype_val hg).mono fun s hs => by
          obtain ⟨s', rfl, rfl⟩ := hs
          exact hH
      have hmem := (MarkedIdealRestrictOpen.mem_pullback_val_iff (O i) h𝔞).mp
        ((hgen q hq (g ∘ Subtype.val)).mpr hlocal)
      exact HomogenizedIdeal.mem_congr h𝔞 hmem hge


end OpenDescent


end


end Hironaka.HironakaOriginalGlobalPrincipalization
