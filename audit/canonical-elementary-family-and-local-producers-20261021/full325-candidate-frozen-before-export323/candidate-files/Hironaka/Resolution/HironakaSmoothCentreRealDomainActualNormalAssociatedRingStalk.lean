/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf

/-! The existing whole associated-ring stalk map is an isomorphism.
Multiplication is the independent representative multiplication already defined
on the section ring and whole original ring. Finite support supplies one common
actual neighbourhood for injectivity; no comparison certificate is an input. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite

namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingStalk
noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualNormalLayerStalk
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The existing ring restriction has the literal componentwise additive map. -/
theorem actualNormalAssociatedRingRestrict_toAddMonoidHom (A : GermIdeal n M) (C : Set M)
    (U V : Opens M) (hUV : U ≤ V) :
    (actualNormalAssociatedRingRestrict A C U V hUV).toAddMonoidHom =
      DirectSum.map (fun q => actualNormalLayerRestrict A C q U V hUV) := by
  apply DirectSum.addHom_ext
  intro q x
  exact (actualNormalAssociatedRingRestrict_of A C U V hUV q x).trans
    (DirectSum.map_of (fun k => actualNormalLayerRestrict A C k U V hUV) q x).symm

/-- Every actual ring restriction retains every original degree component. -/
theorem actualNormalAssociatedRingRestrict_apply (A : GermIdeal n M) (C : Set M)
    (U V : Opens M) (hUV : U ≤ V) (s : actualNormalAssociatedRingSection A C V) (q : ℕ) :
    actualNormalAssociatedRingRestrict A C U V hUV s q =
      actualNormalLayerRestrict A C q U V hUV (s q) := by
  change (actualNormalAssociatedRingRestrict A C U V hUV).toAddMonoidHom s q = _
  rw [actualNormalAssociatedRingRestrict_toAddMonoidHom]
  exact DirectSum.map_apply _ q s

/-- The existing whole ring germ has the literal componentwise additive map. -/
theorem actualNormalAssociatedRingSectionGermHom_toAddMonoidHom (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (y : M) (hy : y ∈ U) :
    (actualNormalAssociatedRingSectionGermHom A C U y hy).toAddMonoidHom =
      DirectSum.map (fun q => actualNormalLayerSectionGermHom A C q U y hy) := by
  apply DirectSum.addHom_ext
  intro q x
  exact (actualNormalAssociatedRingSectionGermHom_of A C U y hy q x).trans
    (DirectSum.map_of (fun k => actualNormalLayerSectionGermHom A C k U y hy) q x).symm

/-- Every original whole ring germ retains every actual homogeneous component. -/
theorem actualNormalAssociatedRingSectionGermHom_apply (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualNormalAssociatedRingSection A C U) (q : ℕ) :
    actualNormalAssociatedRingSectionGermHom A C U y hy s q =
      actualNormalLayerSectionGermHom A C q U y hy (s q) := by
  change (actualNormalAssociatedRingSectionGermHom A C U y hy).toAddMonoidHom s q = _
  rw [actualNormalAssociatedRingSectionGermHom_toAddMonoidHom]
  exact DirectSum.map_apply _ q s

/-- Genuine layer restrictions compose on each original section class. -/
private theorem layerRestrict_comp (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U V W : Opens M) (hUV : U ≤ V) (hVW : V ≤ W) (s : actualNormalLayerSection A C q W) :
    actualNormalLayerRestrict A C q U W (hUV.trans hVW) s =
      actualNormalLayerRestrict A C q U V hUV (actualNormalLayerRestrict A C q V W hVW s) :=
  ConcreteCategory.congr_hom ((actualNormalLayerPresheaf A C q).map_comp
    (homOfLE hVW).op (homOfLE hUV).op) s

/-- A zero whole ring germ vanishes on one genuine smaller original open. -/
theorem actualNormalAssociatedRingSectionGermHom_zero_neighbourhood (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualNormalAssociatedRingSection A C U)
    (hs : actualNormalAssociatedRingSectionGermHom A C U y hy s = 0) :
    ∃ (V : Opens M) (hVU : V ≤ U), y ∈ V ∧ actualNormalAssociatedRingRestrict A C V U hVU s = 0 := by
  classical
  have hdegree (q : ℕ) : (actualNormalLayerPresheaf A C q).germ U y hy (s q) = 0 := by
    apply actualNormalLayerStalkToWholeHom_injective A hA C q y
    rw [actualNormalLayerStalkToWholeHom_germ, map_zero]
    rw [← actualNormalAssociatedRingSectionGermHom_apply, hs]
    rfl
  have hfinite (S : Finset ℕ) :
      ∃ (V : Opens M) (hVU : V ≤ U), y ∈ V ∧
        ∀ q ∈ S, actualNormalLayerRestrict A C q V U hVU (s q) = 0 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨U, le_rfl, hy, by simp⟩
    | @insert i S _ ih =>
      obtain ⟨V, hVU, hyV, hV⟩ := ih
      let L := actualNormalLayerPresheaf A C i
      have hz : L.germ U y hy (s i) = L.germ U y hy 0 := by
        simpa only [map_zero] using hdegree i
      obtain ⟨W, hyW, iU, _, he⟩ := L.germ_eq y hy hy (s i) 0 hz
      have hWU : W ≤ U := leOfHom iU
      have hW : actualNormalLayerRestrict A C i W U hWU (s i) = 0 := by
        exact he.trans (map_zero _)
      have hZU : V ⊓ W ≤ U := inf_le_left.trans hVU
      refine ⟨V ⊓ W, hZU, ⟨hyV, hyW⟩, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · rw [layerRestrict_comp A C q (V ⊓ W) W U inf_le_right hWU, hW, map_zero]
      · rw [layerRestrict_comp A C q (V ⊓ W) V U inf_le_left hVU, hV q hq, map_zero]
  obtain ⟨V, hVU, hyV, hV⟩ := hfinite s.support
  refine ⟨V, hVU, hyV, ?_⟩
  apply DFinsupp.ext
  intro q
  rw [actualNormalAssociatedRingRestrict_apply]
  by_cases hq : q ∈ s.support
  · exact hV q hq
  · have hsq : s q = 0 := by simpa only [DFinsupp.mem_support_iff, not_not] using hq
    simp only [hsq, map_zero, DFinsupp.zero_apply]

/-- Original coherence proves injectivity of the existing genuine whole ring-stalk map. -/
theorem actualNormalAssociatedRingStalkToWholeHom_injective (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) :
    Function.Injective (actualNormalAssociatedRingStalkToWholeHom A C y) := by
  have hkernel (v : ((actualNormalAssociatedRingPresheaf A C).stalk y).carrier)
      (hv : actualNormalAssociatedRingStalkToWholeHom A C y v = 0) : v = 0 := by
    let G := actualNormalAssociatedRingPresheaf A C
    obtain ⟨U, hyU, s, rfl⟩ := G.exists_germ_eq v
    change actualNormalAssociatedRingSection A C U at s
    change actualNormalAssociatedRingStalkToWholeHom A C y
      ((actualNormalAssociatedRingPresheaf A C).germ U y hyU s) = 0 at hv
    rw [actualNormalAssociatedRingStalkToWholeHom_germ A C U y hyU s] at hv
    obtain ⟨V, hVU, hyV, hV⟩ :=
      actualNormalAssociatedRingSectionGermHom_zero_neighbourhood A hA C U y hyU s hv
    have he : G.germ U y hyU s = G.germ U y hyU 0 := by
      apply G.germ_ext V hyV (homOfLE hVU) (homOfLE hVU)
      change actualNormalAssociatedRingRestrict A C V U hVU s =
        actualNormalAssociatedRingRestrict A C V U hVU 0
      rw [hV, map_zero]
    simpa only [map_zero] using he
  intro a b hab
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hab, sub_self]

/-- Actual degree surjectivity supplies every whole finite-support ring class. -/
theorem actualNormalAssociatedRingStalkToWholeHom_surjective (A : GermIdeal n M)
    (C : Set M) (y : M) :
    Function.Surjective (actualNormalAssociatedRingStalkToWholeHom A C y) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of q z =>
    obtain ⟨v, hv⟩ := actualNormalLayerStalkToWholeHom_surjective A C q y z
    obtain ⟨U, hyU, s, rfl⟩ := (actualNormalLayerPresheaf A C q).exists_germ_eq v
    change actualNormalLayerSection A C q U at s
    refine ⟨(actualNormalAssociatedRingPresheaf A C).germ U y hyU
      (DirectSum.of (fun k => actualNormalLayerSection A C k U) q s), ?_⟩
    rw [actualNormalAssociatedRingStalkToWholeHom_germ, actualNormalAssociatedRingSectionGermHom_of]
    rw [actualNormalLayerStalkToWholeHom_germ] at hv
    rw [hv]
  | add a b ha hb =>
    obtain ⟨va, hva⟩ := ha
    obtain ⟨vb, hvb⟩ := hb
    exact ⟨va + vb, by rw [map_add, hva, hvb]⟩

/-- The SAME actual ring-colimit map is a ring equivalence with the whole original graded ring. -/
def actualNormalAssociatedRingStalkWholeEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    ((actualNormalAssociatedRingPresheaf A C).stalk y).carrier ≃+* actualWholeNormalAssociatedRing A C y :=
  RingEquiv.ofBijective (actualNormalAssociatedRingStalkToWholeHom A C y)
    ⟨actualNormalAssociatedRingStalkToWholeHom_injective A hA C y,
      actualNormalAssociatedRingStalkToWholeHom_surjective A C y⟩

/-- Every original entire section germ retains its existing whole original class formula. -/
theorem actualNormalAssociatedRingStalkWholeEquiv_germ (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U) (s : actualNormalAssociatedRingSection A C U) :
    actualNormalAssociatedRingStalkWholeEquiv A hA C y
      ((actualNormalAssociatedRingPresheaf A C).germ U y hy s) =
    actualNormalAssociatedRingSectionGermHom A C U y hy s :=
  actualNormalAssociatedRingStalkToWholeHom_germ A C U y hy s

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingStalk
