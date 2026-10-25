/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubset
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Native whole subset-complex exactness from genuine NONEMPTY component maps

Only native Mathlib linear/homology criteria and own original subset complexes.
No exactness at the empty subset and no finite-index assumption is introduced.
The actual geometric local exactness must be derived by each concrete producer.
-/
open CategoryTheory
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech.SubsetNonemptyExactness
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R ι : Type u} [CommRing R] [LinearOrder ι]
  {F G H : Finset ι ⥤ ModuleCat.{u} R} (α : F ⟶ G) (β : G ⟶ H)
  (hlocal : ∀ S : Finset ι, S.Nonempty →
    Function.Exact (α.app S).hom (β.app S).hom ∧
      Function.Injective (α.app S).hom ∧ Function.Surjective (β.app S).hom)
include hlocal

private theorem original_comp_zero : subsetCechComplexMap α ≫ subsetCechComplexMap β=0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext S
  change (β.app S).hom ((α.app S).hom
    ((show subsetCechCardPiece F (n+1) from x).val S))=0
  by_cases hS : S.card=n+1
  · exact ((hlocal S (Finset.card_pos.mp (by omega))).1 _).mpr ⟨_, rfl⟩
  · rw [(show subsetCechCardPiece F (n+1) from x).property S hS, map_zero, map_zero]

/-- SAME native original cochain maps form an ENTIRE short complex using ONLY original nonempty exactness. -/
def sequence : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (subsetCechComplexMap α) (subsetCechComplexMap β) (original_comp_zero α β hlocal)

/-- Actual native original component exactness on NONEMPTY subsets proves WHOLE original complex short exactness. -/
theorem sequence_shortExact : (sequence α β hlocal).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let T := (sequence α β hlocal).map (HomologicalComplex.eval _ _ n)
  change T.ShortExact
  have hinj : Function.Injective T.f.hom := by
    intro x y hxy
    apply Subtype.ext
    funext S
    by_cases hS : S.card=n+1
    · apply (hlocal S (Finset.card_pos.mp (by omega))).2.1
      exact congrArg (fun z : subsetCechCardPiece G (n+1) => z.val S) hxy
    · exact ((show subsetCechCardPiece F (n+1) from x).property S hS).trans
        ((show subsetCechCardPiece F (n+1) from y).property S hS).symm
  have hsurj : Function.Surjective T.g.hom := by
    intro y
    have hx (S : Finset ι) (hS : S.card=n+1) :
        ∃ x : G.obj S, (β.app S).hom x=(show subsetCechCardPiece H (n+1) from y).val S :=
      (hlocal S (Finset.card_pos.mp (by omega))).2.2 _
    let x : subsetCechCardPiece G (n+1) := ⟨fun S =>
      if hS : S.card=n+1 then Classical.choose (hx S hS) else 0,
      by intro S hS; exact dif_neg hS⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext S
    change (β.app S).hom (x.val S)=(show subsetCechCardPiece H (n+1) from y).val S
    by_cases hS : S.card=n+1
    · change (β.app S).hom (if h : S.card=n+1 then Classical.choose (hx S h) else 0)=_
      rw [dif_pos hS]
      exact Classical.choose_spec (hx S hS)
    · change (β.app S).hom (if h : S.card=n+1 then Classical.choose (hx S h) else 0)=_
      rw [dif_neg hS, map_zero, (show subsetCechCardPiece H (n+1) from y).property S hS]
  have hexact : Function.Exact T.f.hom T.g.hom := by
    intro y
    constructor
    · intro hy
      have hx (S : Finset ι) (hS : S.card=n+1) :
          ∃ x : F.obj S, (α.app S).hom x=(show subsetCechCardPiece G (n+1) from y).val S := by
        apply ((hlocal S (Finset.card_pos.mp (by omega))).1 _).mp
        exact congrArg (fun z : subsetCechCardPiece H (n+1) => z.val S) hy
      let x : subsetCechCardPiece F (n+1) := ⟨fun S =>
        if hS : S.card=n+1 then Classical.choose (hx S hS) else 0,
        by intro S hS; exact dif_neg hS⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      funext S
      change (α.app S).hom (x.val S)=(show subsetCechCardPiece G (n+1) from y).val S
      by_cases hS : S.card=n+1
      · change (α.app S).hom (if h : S.card=n+1 then Classical.choose (hx S h) else 0)=_
        rw [dif_pos hS]
        exact Classical.choose_spec (hx S hS)
      · change (α.app S).hom (if h : S.card=n+1 then Classical.choose (hx S h) else 0)=_
        rw [dif_neg hS, map_zero, (show subsetCechCardPiece G (n+1) from y).property S hS]
    · rintro ⟨x, rfl⟩
      exact congrArg (fun k => k.hom x) T.zero
  exact ModuleCat.shortComplex_shortExact T hexact hinj hsurj

end DeJongAlterations.Geometry.ProperSteinProjectiveCech.SubsetNonemptyExactness
