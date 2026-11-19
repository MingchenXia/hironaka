import Hironaka.Geometry.MonomialBlowupTowerCharts
import Hironaka.Geometry.PolynomialNodeResolution

/-!
# The actual regular projective alteration of a finite-product node

The final source is the actual finite global original-prefix blowup tower.
Its complete native chart cover is constructed internally by induction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupTowerRegular

open MonomialBlowupTower MonomialBlowupTowerCharts

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A]

/-- Every actual finite prefix stage has its actual internally constructed node chart cover. -/
theorem nonempty_charts (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) : Nonempty (ChartData l a.length a.prod b.prod) := by
  induction a using List.reverseRecOn generalizing b with
  | nil =>
    have hbl : l = b := by simpa using hab
    subst b
    exact ⟨initialCharts l (List.prod_ne_zero hl)⟩
  | append_singleton a t ih =>
    have hprev : l = a ++ t :: b := by simpa only [List.append_assoc, List.singleton_append] using hab
    obtain ⟨S⟩ := ih (t :: b) hprev
    have htmem : t ∈ l := by rw [hprev]; simp
    have ht : t ≠ 0 := by
      intro h
      exact hl (h ▸ htmem)
    have hb : b.prod ≠ 0 := List.prod_ne_zero (by
      intro h
      apply hl
      rw [hprev]
      exact List.mem_append_right _ (List.mem_cons_of_mem t h))
    have hprefix : (l.take (a.length + 1)).prod = a.prod * t := by
      rw [hprev]
      exact nextPrefix_prod a t b
    obtain ⟨S'⟩ := nextCharts b S hprefix ht hb htmem
    simpa only [List.length_append, List.length_singleton, List.prod_append, List.prod_singleton]
      using (show Nonempty (ChartData l (a.length + 1) (a.prod * t) b.prod) from ⟨S'⟩)

variable [IsRegularRing A]

/-- The actual final global original-prefix blowup has regular actual stalks. -/
theorem resolution_isRegular (l : List A) (hl : (0 : A) ∉ l)
    (hparam : ∀ t ∈ l, ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme (resolved l) := by
  obtain ⟨S⟩ := nonempty_charts l hl l [] (by simp)
  apply IsRegularScheme.of_openCover S.openCover
  intro i
  cases i with
  | none => exact MonomialBlowupIteration.terminalNode_isRegular
  | some i => exact RegularNode.isRegularScheme_nodeQuotient (S.factor i) (hparam _ (S.factor_mem i))

/-- A genuine regular projective alteration of the actual finite-product node, with no caller chart data. -/
theorem regular_projective_alteration (l : List A) (hl : (0 : A) ∉ l)
    (hparam : ∀ t ∈ l, ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme (resolved l) ∧ IsProjectiveOver (resolutionMorphism l) ∧
      IsAlteration (resolutionMorphism l) :=
  ⟨resolution_isRegular l hl hparam, resolution_isProjective l, resolution_isAlteration l hl⟩

end Hironaka.Geometry.MonomialBlowupTowerRegular

namespace Hironaka.Geometry.MonomialBlowupTowerRegular

open AlgebraicGeometry MvPolynomial MonomialBlowupTower

universe u

/-- Arbitrary finite monomials in actual polynomial coordinates have the actual regular projective alteration. -/
theorem polynomial_regular_projective_alteration (K : Type u) [Field K]
    {ι : Type u} [Finite ι] (l : List ι) :
    let factors := l.map (fun i ↦ (X i : MvPolynomial ι K))
    IsRegularScheme (resolved factors) ∧ IsProjectiveOver (resolutionMorphism factors) ∧
      IsAlteration (resolutionMorphism factors) := by
  apply regular_projective_alteration
  · intro h
    obtain ⟨i, _, hi⟩ := List.mem_map.mp h
    exact X_ne_zero i hi
  · intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    exact fun p _ hp ↦ PolynomialNodeResolution.coordinate_not_mem_square K i p hp

end Hironaka.Geometry.MonomialBlowupTowerRegular
