import Hironaka.Geometry.MonomialBlowupTowerBase
import Hironaka.Geometry.MonomialBlowupIteration
import Hironaka.Geometry.ReducedClosedSubscheme
import Hironaka.Geometry.ProjectiveIdentity

/-!
# The actual global original-prefix blowup tower of a finite-product node

Every stage is defined by the native global blowup of the actual pullback
of the specified original two-generator ideal sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTower

open Algebra.NodeBlowupChart Algebra.MonomialBlowupIteration MonomialBlowupTowerBase

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The actual original finite-product node scheme. -/
abbrev original (l : List A) : Scheme.{u} := Spec (CommRingCat.of (Node A l.prod))

/-- The actual original prefix centre whose pullback is blown up at stage `n`. -/
def originalCenter (l : List A) (n : ℕ) : (original l).IdealSheafData :=
  SpecIdealSheaf.specIdealSheaf (Node A l.prod)
    (prefixCenter l.prod (l.take (n + 1)).prod)

/-- The actual native global blowup tower of all original prefix centres. -/
abbrev tower (l : List A) (n : ℕ) : Over (original l) := stage (originalCenter l) n

/-- The actual final scheme after processing every factor. -/
abbrev resolved (l : List A) : Scheme.{u} := (tower l l.length).left

/-- Its actual structure morphism to the original node. -/
abbrev resolutionMorphism (l : List A) : resolved l ⟶ original l := (tower l l.length).hom

/-- The original prefix product at the next actual stage has its exact split-list formula. -/
theorem nextPrefix_prod (a : List A) (t : A) (b : List A) :
    ((a ++ t :: b).take (a.length + 1)).prod = a.prod * t := by
  rw [List.take_append]
  simp [List.take_of_length_le (Nat.le_succ a.length)]

variable [IsDomain A]

/-- Every original prefix centre has actual proper support, proved at the genuine zero prime. -/
theorem originalCenter_support_ne_top (l : List A) (hl : (0 : A) ∉ l) (n : ℕ) :
    (originalCenter l n).support ≠ ⊤ := by
  let : IsDomain (Node A l.prod) := Algebra.NodeDomain.nodeQuotient_isDomain l.prod (List.prod_ne_zero hl)
  let x : original l := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Node A l.prod))
  intro h
  have hx : x ∈ (originalCenter l n).support := by rw [h]; trivial
  change x ∈ ((SpecIdealSheaf.specIdealSheaf (Node A l.prod)
    (prefixCenter l.prod (l.take (n + 1)).prod)).support : Set (Spec (CommRingCat.of (Node A l.prod)))) at hx
  rw [ReducedClosedSubscheme.specIdealSheaf_support] at hx
  have hu := hx (Ideal.subset_span (Set.mem_insert (coordinate l.prod 0) _))
  exact Algebra.NodeDomain.nodeCoordinate_ne_zero l.prod (List.prod_ne_zero hl) 0 hu

variable [IsNoetherianRing A]

/-- Every actual finite global stage is an alteration, with nonzero ideals and domain facts internal. -/
theorem tower_isAlteration (l : List A) (hl : (0 : A) ∉ l) (n : ℕ) :
    IsAlteration (tower l n).hom := by
  let : IsDomain (Node A l.prod) := Algebra.NodeDomain.nodeQuotient_isDomain l.prod (List.prod_ne_zero hl)
  let : IsIntegral (original l) := inferInstance
  exact stage_isAlteration (originalCenter l) (originalCenter_support_ne_top l hl) n

/-- In particular the actual final global original-prefix blowup is an alteration. -/
theorem resolution_isAlteration (l : List A) (hl : (0 : A) ∉ l) :
    IsAlteration (resolutionMorphism l) := tower_isAlteration l hl l.length

omit [IsDomain A] in
/-- Every actual stage is projective over the original node coordinate ring. -/
theorem tower_isProjective (l : List A) (n : ℕ) : IsProjectiveOver (tower l n).hom := by
  simpa only [Category.comp_id] using stage_comp_isProjective (originalCenter l)
    (𝟙 (original l)) (ProjectiveIdentity.isProjectiveOver_id_spec (Node A l.prod)) n

omit [IsDomain A] in
/-- The actual finite original-prefix resolution morphism is projective. -/
theorem resolution_isProjective (l : List A) : IsProjectiveOver (resolutionMorphism l) :=
  tower_isProjective l l.length

end Hironaka.Geometry.MonomialBlowupTower
