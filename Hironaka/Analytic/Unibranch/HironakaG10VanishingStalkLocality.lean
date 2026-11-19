import Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity

/-! # Locality of native reduced vanishing ideals -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkLocality

open Hironaka HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity

/-- Sets which agree near a point have identical native reduced vanishing
  ideals at that point. -/
theorem vanishingIdealAt_eq_of_eventually {X : LocallyRingedSpace.{0}}
    (A B : Set X) (x : X) (h : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    vanishingIdealAt X A x = vanishingIdealAt X B x := by
  have hle : ∀ (A B : Set X), (∀ᶠ y in 𝓝 x, y ∈ A → y ∈ B) →
      vanishingIdealAt X B x ≤ vanishingIdealAt X A x := by
    intro A B hab
    obtain ⟨U,hUsub,hUopen,hxU⟩ := mem_nhds_iff.mp hab
    apply Ideal.span_le.mpr
    rintro g ⟨W,hxW,t,ht,hvan⟩
    let T : Opens X.toTopCat := W ⊓ ⟨U,hUopen⟩
    have hxT : x ∈ T := ⟨hxW,hxU⟩
    let t' := X.presheaf.map (homOfLE (show T ≤ W from inf_le_left)).op t
    apply Ideal.subset_span
    refine ⟨T,hxT,t', ?_, ?_⟩
    · exact (X.presheaf.germ_res_apply (homOfLE (show T ≤ W from inf_le_left)) x hxT t).trans ht
    · intro y hy hyA
      rw [X.presheaf.germ_res_apply (homOfLE (show T ≤ W from inf_le_left)) y hy t]
      exact hvan y hy.1 (hUsub hy.2 hyA)
  exact le_antisymm (hle B A (h.mono fun _ h => h.mpr))
    (hle A B (h.mono fun _ h => h.mp))

/-- The same locality statement for the native whole stalk image. -/
theorem intrinsicCentreStalkRange_eq_of_eventually {X : LocallyRingedSpace.{0}}
    (A B : Set X) (x : X) (h : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    intrinsicCentreStalkRange X A x = intrinsicCentreStalkRange X B x := by
  rw [← vanishingIdealAt_eq_intrinsicCentreStalkRange,
    ← vanishingIdealAt_eq_intrinsicCentreStalkRange]
  exact vanishingIdealAt_eq_of_eventually A B x h

end Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkLocality
