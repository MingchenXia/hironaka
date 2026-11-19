/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Componentwise
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransport
import Hironaka.Resolution.Algebraic.Kol07.Remark33Warning63
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The weak transform and the boundary along the componentwise sequence

The weak transform along the single blow-up `π_Z` equals the iterated weak transform along the
`c` blow-ups of the irreducible components, and the final reduced total transforms (Hironaka's
boundaries) agree. Both are read on the end result of the componentwise sequence `ofCenters c D`,
carried to the single blow-up `B_Z X` along the canonical isomorphism `e` of
`Hironaka/Resolution/Algebraic/Kol07/ComponentwiseBlowUp.lean`.

* Boundary. Hironaka's `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))` [Hir64, Main Theorem II (iii)]
  depends on supports only: after the whole sequence the boundary is the vanishing ideal of
  `Π⁻¹(V(E₀) ∪ V(Z))`, and so is the boundary of the single blow-up pulled back along `e`, for a
  reduced `E₀` (with no blow-up at all the boundary sequence stays at `E₀`, a radical only when
  `E₀` is reduced). Along an isomorphism the inverse image of a vanishing ideal is the vanishing
  ideal of the preimage (`comap_vanishingIdeal_of_isIso`).
* Weak transform. The center has snc with the empty family (`hasSncWith_empty_of_smooth`), so
  `isOrderSeq_ofCenters` applies with `E = ∅`. Along a smooth blow-up sequence of order `d`
  Hironaka's weak transforms are Kollár's marked transforms ([Kol07, Remark 67];
  `markedTransformSeq_eq_weakTransformSeq`), and the marked transform of [Kol07, Definition 60]
  iterated says the marked transform after the whole sequence is the colon of `Π^* J` by the
  `d`-th power of the product of the centers pulled up to the end result
  (`IsOrderSeq.markedTransformSeq_last_eq_colon`: exact division at each stage,
  `colon_pow_eq_of_mul_eq`). For the single blow-up the same reads `(π_Z^* J) : F_Z^d`, and `F_Z`
  pulls back along `e` to the product of the pulled-up components.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Inverse images along isomorphisms -/

section Iso

variable {Y : Scheme.{u}} (e : Y ⟶ X) [IsIso e]

/-- The inverse image along an isomorphism is the direct image along its inverse: the two are
adjoint (`map_gc`) and `comap` along an isomorphism is invertible. -/
theorem comap_eq_map_inv (I : X.IdealSheafData) : I.comap e = I.map (inv e) := by
  refine le_antisymm ?_ ?_
  · have h := Scheme.IdealSheafData.le_map_comap (I.comap e) (inv e)
    rwa [← comap_comp, IsIso.inv_hom_id, comap_id] at h
  · have h : ((I.map (inv e)).comap (inv e)).comap e ≤ I.comap e :=
      Scheme.IdealSheafData.comap_mono e (Scheme.IdealSheafData.comap_map_le I (inv e))
    rwa [← comap_comp, IsIso.hom_inv_id, comap_id] at h

/-- The inverse image of a vanishing ideal along an isomorphism is the vanishing ideal of the
preimage (Mathlib's `map_vanishingIdeal` read along the inverse). -/
theorem comap_vanishingIdeal_of_isIso (S : Closeds X) :
    (vanishingIdeal S).comap e = vanishingIdeal (S.preimage e.continuous) := by
  rw [comap_eq_map_inv e, map_vanishingIdeal]
  congr 1
  have h1 : ∀ x : X, e ((inv e) x) = x := fun x =>
    congrArg (fun φ : X ⟶ X => φ x) (IsIso.inv_hom_id e)
  have h2 : ∀ y : Y, (inv e) (e y) = y := fun y =>
    congrArg (fun φ : Y ⟶ Y => φ y) (IsIso.hom_inv_id e)
  apply le_antisymm
  · rw [Closeds.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    change e ((inv e) x) ∈ (S : Set X)
    rw [h1]; exact hx
  · intro y hy
    rw [Closeds.mem_closure]
    exact subset_closure ⟨e y, hy, h2 y⟩

end Iso

/-! ### The boundary along the componentwise sequence -/

section Boundary

/-- The support of a vanishing ideal is the closed set it vanishes on. -/
theorem support_vanishingIdeal_eq (S : Closeds X) : (vanishingIdeal S).support = S :=
  SetLike.coe_injective (coe_support_vanishingIdeal S)

/-- The set underlying Hironaka's boundary after the whole componentwise sequence: the preimage
under the composite of `V(E₀) ∪ V(Z)`, `Z = ∏ i, D i` (no hypotheses; supports only). -/
theorem coe_support_boundarySeq_ofCenters_last (c : ℕ) (D : Fin c → X.IdealSheafData)
    (E₀ : X.IdealSheafData) :
    ((((ofCenters c D).boundarySeq E₀ (Fin.last _)).support : Closeds _) : Set _) =
      (ofCenters c D).stageMap (Fin.last _) ⁻¹'
        ((E₀.support : Set X) ∪ ((∏ i, D i).support : Set X)) := by
  induction c generalizing X with
  | zero =>
    change (E₀.support : Set X) =
      (𝟙 X : X ⟶ X) ⁻¹' ((E₀.support : Set X) ∪ ((∏ i : Fin 0, D i).support : Set X))
    rw [Fin.prod_univ_zero, one_eq_top, support_top, Closeds.coe_bot, Set.union_empty]
    rfl
  | succ c ih =>
    change ((((ofCenters c fun i => (D i.succ).comap ((D 0).blowUpπ)).boundarySeq
      (E₀.reducedTransform (D 0)) (Fin.last _)).support : Closeds _) : Set _) =
        ((ofCenters c fun i => (D i.succ).comap ((D 0).blowUpπ)).stageMap (Fin.last _) ≫
          (D 0).blowUpπ) ⁻¹' _
    rw [ih]
    have hcomp : ⇑((ofCenters c fun i => (D i.succ).comap ((D 0).blowUpπ)).stageMap
        (Fin.last _) ≫
        (D 0).blowUpπ) = ⇑(D 0).blowUpπ ∘
          ⇑((ofCenters c fun i => (D i.succ).comap ((D 0).blowUpπ)).stageMap
              (Fin.last _)) := rfl
    rw [hcomp, Set.preimage_comp]
    congr 1
    unfold reducedTransform
    have hpre : ∀ (S : Closeds X), ((S.preimage (D 0).blowUpπ.continuous : Closeds _) : Set _) =
        (D 0).blowUpπ ⁻¹' (S : Set X) := fun _ => rfl
    rw [coe_support_vanishingIdeal, Closeds.coe_sup, support_finset_prod, ← Finset.sup_eq_iSup,
      Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, hpre, hpre, Fin.prod_univ_succ,
      support_mul, Closeds.coe_sup, support_finset_prod, ← Finset.sup_eq_iSup,
      Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.preimage_union, Set.preimage_union,
      Set.preimage_iUnion₂, Set.union_assoc]
    congr 2
    refine Set.iUnion₂_congr fun i _ => ?_
    change ((((D i.succ).comap (D 0).blowUpπ).support : Closeds _) : Set _) =
      (D 0).blowUpπ ⁻¹' (((D i.succ).support : Closeds X) : Set X)
    rw [Scheme.IdealSheafData.support_comap]
    exact hpre _

/-- Along the componentwise sequence the boundary of a vanishing-ideal boundary stays a vanishing
ideal: the vanishing ideal of its own support. -/
theorem boundarySeq_ofCenters_last_eq_vanishingIdeal_support (c : ℕ) (D : Fin c → X.IdealSheafData)
    (E₀ : X.IdealSheafData) (hE₀ : vanishingIdeal E₀.support = E₀) :
    (ofCenters c D).boundarySeq E₀ (Fin.last _) =
      vanishingIdeal ((ofCenters c D).boundarySeq E₀ (Fin.last _)).support := by
  induction c generalizing X with
  | zero => exact hE₀.symm
  | succ c ih =>
    change (ofCenters c fun i => (D i.succ).comap (D 0).blowUpπ).boundarySeq
      (E₀.reducedTransform (D 0)) (Fin.last _) = _
    exact ih _ _ (support_vanishingIdeal_eq _ ▸ rfl)

/-- The final reduced total transforms agree, in the general form with the center `Z` a variable:
Hironaka's boundary after the componentwise sequence of the `D i` with `∏ i, D i = Z` is the
inverse image, under any morphism `e` over `X` to `B_Z X` (necessarily the canonical isomorphism),
of the boundary of the single blow-up, for a reduced `E₀`. -/
theorem boundarySeq_ofCenters_last' {c : ℕ} (D : Fin c → X.IdealSheafData) (Z : X.IdealSheafData)
    (hZ : ∏ i, D i = Z) (e : (ofCenters c D).last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = (ofCenters c D).composite) (E₀ : X.IdealSheafData)
    [IsReduced E₀.subscheme] :
    (ofCenters c D).boundarySeq E₀ (Fin.last _) = (E₀.reducedTransform Z).comap e := by
  subst hZ
  obtain ⟨e₀, he₀, huniq⟩ := exists_iso_last_ofCenters c D
  obtain rfl : e = e₀.hom := huniq e he
  have hE₀ : vanishingIdeal E₀.support = E₀ := by
    rw [vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]
  rw [boundarySeq_ofCenters_last_eq_vanishingIdeal_support c D E₀ hE₀]
  change _ = (vanishingIdeal _).comap e₀.hom
  rw [comap_vanishingIdeal_of_isIso]
  congr 1
  refine SetLike.coe_injective ?_
  rw [coe_support_boundarySeq_ofCenters_last]
  change (ofCenters c D).composite ⁻¹' _ =
    e₀.hom ⁻¹' (((∏ i, D i).blowUpπ) ⁻¹' ((E₀.support : Set X)) ∪
      (∏ i, D i).blowUpπ ⁻¹' (((∏ i, D i).support : Set X)))
  rw [← he₀, ← Set.preimage_union]
  rfl

/-- The final reduced total transforms agree: Hironaka's boundary after the componentwise sequence
of the `D i` is the inverse image, under any morphism `e` over `X` to the blow-up along the product
(necessarily the canonical isomorphism), of the boundary of the single blow-up, for a reduced
`E₀`. -/
theorem boundarySeq_ofCenters_last {c : ℕ} (D : Fin c → X.IdealSheafData)
    (e : (ofCenters c D).last ⟶ (∏ i, D i).blowUp)
    (he : e ≫ (∏ i, D i).blowUpπ = (ofCenters c D).composite) (E₀ : X.IdealSheafData)
    [IsReduced E₀.subscheme] :
    (ofCenters c D).boundarySeq E₀ (Fin.last _) = (E₀.reducedTransform (∏ i, D i)).comap e :=
  boundarySeq_ofCenters_last' D _ rfl e he E₀

end Boundary

/-! ### The components of a regular center (the statements without a field) -/

section Components

variable [NoetherianSpace X] (Z : X.IdealSheafData)

/-- The listed components of a regular closed subscheme have pairwise disjoint supports. -/
theorem pairwise_disjoint_support_orderedComponent (hZ : IsRegular Z.subscheme) :
    Pairwise fun i j => Disjoint (Z.componentFamily.nth i).support
      (Z.componentFamily.nth j).support := fun _ _ hij =>
  pairwise_disjoint_support_componentFamily Z hZ ((monoEquivOfFin _ rfl).injective.ne hij)

/-- Every center of `Z.componentwiseSeq`, for a regular `Z`, is irreducible (towards clause (i) of
[Hir64, Main Theorem II]). -/
theorem irreducibleSpace_center_componentwiseSeq (hZ : IsRegular Z.subscheme)
    (i : Fin Z.componentwiseSeq.length) : IrreducibleSpace (Z.componentwiseSeq.center i).subscheme
:=
  irreducibleSpace_center_ofCenters _ (pairwise_disjoint_support_orderedComponent Z hZ)
    (fun _ => irreducibleSpace_subscheme_componentFamily Z _) i

/-- Every center of `Z.componentwiseSeq`, for a regular `Z`, is regular (towards clause (i) of
[Hir64, Main Theorem II]). -/
theorem isRegular_center_componentwiseSeq (hZ : IsRegular Z.subscheme)
    (i : Fin Z.componentwiseSeq.length) : IsRegular (Z.componentwiseSeq.center i).subscheme :=
  isRegular_center_ofCenters _ (pairwise_disjoint_support_orderedComponent Z hZ)
    (fun _ => isRegular_subscheme_componentFamily Z hZ _) i

/-- For a regular center `Z`, Hironaka's boundary after the componentwise sequence is the inverse
image of the boundary after the single blow-up along `Z`, for a reduced `E₀`. -/
theorem boundarySeq_componentwiseSeq_last (hZ : IsRegular Z.subscheme)
    (e : Z.componentwiseSeq.last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = Z.componentwiseSeq.composite) (E₀ : X.IdealSheafData)
    [IsReduced E₀.subscheme] :
    Z.componentwiseSeq.boundarySeq E₀ (Fin.last _) = (E₀.reducedTransform Z).comap e := by
  unfold componentwiseSeq
  exact boundarySeq_ofCenters_last' _ Z
    ((DivisorFamily.prod_orderedComponent _).trans
        (prod_componentFamily_eq Z hZ)) e he
    E₀

end Components

/-! ### The weak transform along the componentwise sequence -/

section Weak

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include f n

/-- The marked transform of [Kol07, Definition 60] iterated along a smooth blow-up sequence of
order `d` (compare [Kol07, Warning 63]): the marked transform after the whole sequence is the colon
of `Π^* J` by the `d`-th power of the product of the centers pulled up to the end result. Exact
division at each stage (`pow_mul_markedTransform`, `colon_pow_eq_of_mul_eq`) and the colon of a
colon (`colon_colon`). -/
theorem IsOrderSeq.markedTransformSeq_last_eq_colon {S : BlowUpSequence X} {J : X.IdealSheafData}
    {E : DivisorFamily X} {d : ℕ} (h : S.IsOrderSeq f J E d) :
    S.markedTransformSeq J d (Fin.last _) =
      (J.comap S.composite).colon ((∏ i : Fin S.length,
        (S.center i).comap (S.stageMapBetween (Fin.last _) i.castSucc (Fin.le_last _))) ^ d) := by
  induction S with
  | nil X =>
    have : IsEmpty (Fin (nil X).length) := ⟨fun i => i.elim0⟩
    change J = (J.comap (𝟙 X)).colon ((∏ i : Fin (nil X).length,
      (((nil X).center i).comap ((nil X).stageMapBetween (Fin.last _) i.castSucc (Fin.le_last _)) :
        X.IdealSheafData)) ^ d)
    rw [Fintype.prod_empty, one_pow, one_eq_top, colon_top, comap_id]
  | cons X D rest ih =>
    obtain ⟨⟨hD, hsnc, hord⟩, ht⟩ := (isOrderSeq_cons_iff f J E d D rest).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hmw : J.weakTransform D = J.markedTransform D d :=
      weakTransform_eq_markedTransform_of_smooth f n D J hord
    have hle : J.LeOrdAlong D.support (d : ℕ∞) := fun η hη => (hord η hη).ge
    have hmul : (D.comap D.blowUpπ) ^ d * J.markedTransform D d = J.comap
        D.blowUpπ :=
      pow_mul_markedTransform D J d (pow_dvd_comap_of_leOrdAlong f n D J hle)
    change rest.markedTransformSeq (J.markedTransform D d) d (Fin.last _) = _
    rw [← hmw, ih (D.blowUpπ ≫ f) ht, hmw]
    have hcomap : (J.markedTransform D d).comap rest.composite =
        (J.comap (rest.composite ≫ D.blowUpπ)).colon
          ((D.comap (rest.composite ≫ D.blowUpπ)) ^ d) := by
      symm
      apply colon_pow_eq_of_mul_eq
      · rw [comap_comp]
        exact isInvertible_comap_stageMap rest (blowUp.isInvertible_comap_π D) _
      · rw [comap_comp, ← comap_pow, ← comap_mul, hmul, ← comap_comp]
    rw [hcomap]
    refine (colon_colon _ _ _).trans ?_
    change (J.comap (rest.composite ≫ D.blowUpπ)).colon
        (D.comap (rest.composite ≫ D.blowUpπ) ^ d *
          ((∏ i : Fin rest.length, (rest.center i).comap
            (rest.stageMapBetween (Fin.last _) i.castSucc (Fin.le_last _)) :
              rest.last.IdealSheafData)) ^ d) =
      (J.comap (rest.composite ≫ D.blowUpπ)).colon
        ((∏ i : Fin (rest.length + 1), ((cons X D rest).center i).comap
          ((cons X D rest).stageMapBetween (Fin.last _) i.castSucc (Fin.le_last _)) :
            rest.last.IdealSheafData) ^ d)
    rw [← mul_pow, Fin.prod_univ_succ]
    congr 3

/-- The weak transform along `π_Z` equals the iterated weak transform, in the general form with
the center `Z` a variable, `∏ i, D i = Z`: Hironaka's `J_c` of the componentwise sequence is the
inverse image, under any morphism `e` over `X` to `B_Z X`, of the weak transform of `J` along
`π_Z`. Both are the colon of `Π^* J` by the `d`-th power of `Π^{-1} Z = ∏ Π^{-1}(D i)`
([Kol07, Remark 67]; `markedTransformSeq_last_eq_colon`). -/
theorem weakTransformSeq_ofCenters_last' {c : ℕ} (D : Fin c → X.IdealSheafData)
    (Z : X.IdealSheafData) (hZeq : ∏ i, D i = Z)
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (hZ : Smooth (Z.subschemeι ≫ f)) {J : X.IdealSheafData} {d : ℕ}
    (hord : J.OrdAlongEq Z.support (d : ℕ∞)) (e : (ofCenters c D).last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = (ofCenters c D).composite) :
    (ofCenters c D).weakTransformSeq J (Fin.last _) = (J.weakTransform Z).comap e := by
  subst hZeq
  obtain ⟨e₀, he₀, huniq⟩ := exists_iso_last_ofCenters c D
  obtain rfl : e = e₀.hom := huniq e he
  have hf : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := hZ
  have hseq : (ofCenters c D).IsOrderSeq f J (DivisorFamily.empty X) d :=
    isOrderSeq_ofCenters f n D hdisj hZ hord (hasSncWith_empty_of_smooth f _)
  have key : ∀ i : Fin (ofCenters c D).length,
      ((ofCenters c D).center i).comap
          ((ofCenters c D).stageMapBetween (Fin.last _) i.castSucc (Fin.le_last _)) =
        (D (Fin.cast (length_ofCenters c D) i)).comap (ofCenters c D).composite := fun i => by
    rw [center_ofCenters, ← comap_comp, stageMapBetween_comp_stageMap]
    rfl
  rw [← IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n hseq (Fin.last _),
    IsOrderSeq.markedTransformSeq_last_eq_colon f n hseq,
    weakTransform_eq_markedTransform_of_smooth f n (∏ i, D i) J hord, markedTransform_eq_colon,
    show (∏ i, D i).exceptionalDivisor = (∏ i, D i).comap (∏ i, D i).blowUpπ from rfl,
    colon_comap_of_flat _ _ (isInvertible_pow (blowUp.isInvertible_comap_π _) d), ← comap_comp,
    he₀, comap_pow, ← comap_comp, he₀, comap_finset_prod, Finset.prod_congr rfl fun i _ => key i]
  congr 2
  exact Fintype.prod_equiv (finCongr (length_ofCenters c D)) _ _ fun _ => rfl

/-- The weak transform along `π_Z` equals the iterated weak transform: for a smooth disjoint union
`Z = ∏ i, D i` of order `d` along each component, Hironaka's `J_c` of the componentwise sequence
is the inverse image, under any morphism over `X` to `B_Z X`, of the weak transform of `J` along
`π_Z`. -/
theorem weakTransformSeq_ofCenters_last {c : ℕ} (D : Fin c → X.IdealSheafData)
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (hZ : Smooth ((∏ i, D i).subschemeι ≫ f)) {J : X.IdealSheafData} {d : ℕ}
    (hord : J.OrdAlongEq (∏ i, D i).support (d : ℕ∞))
    (e : (ofCenters c D).last ⟶ (∏ i, D i).blowUp)
    (he : e ≫ (∏ i, D i).blowUpπ = (ofCenters c D).composite) :
    (ofCenters c D).weakTransformSeq J (Fin.last _) = (J.weakTransform (∏ i, D i)).comap e :=
  weakTransformSeq_ofCenters_last' f n D _ rfl hdisj hZ hord e he

/-- The componentwise sequence of a smooth center `Z` with `ord_Z J = d` and snc with `E` is a
smooth blow-up sequence of order `d` for `(X, J, E)` [Kol07, Definition 66]: a smooth center is
regular (`isRegularLocalRing_stalk`), so it is the product of its components. -/
theorem isOrderSeq_componentwiseSeq [IsNoetherian X] (Z : X.IdealSheafData)
    (hZ : Smooth (Z.subschemeι ≫ f)) {J : X.IdealSheafData} {E : DivisorFamily X} {d : ℕ}
    (hord : J.OrdAlongEq Z.support (d : ℕ∞)) (hsnc : E.HasSncWith Z) :
    Z.componentwiseSeq.IsOrderSeq f J E d := by
  have := hZ
  have hreg : IsRegular Z.subscheme := ⟨fun z =>
    isRegularLocalRing_stalk (Z.subschemeι ≫ f) z⟩
  have hprod : ∏ k, Z.componentFamily.nth k = Z :=
    (DivisorFamily.prod_orderedComponent _).trans (prod_componentFamily_eq Z hreg)
  unfold componentwiseSeq
  refine isOrderSeq_ofCenters f n _ (pairwise_disjoint_support_orderedComponent Z hreg) ?_ ?_ ?_
  · rw [hprod]; exact hZ
  · rw [hprod]; exact hord
  · rw [hprod]; exact hsnc

/-- For a smooth center `Z`, Hironaka's `J_c` of the componentwise sequence is the inverse image
of the weak transform along `π_Z`. -/
theorem weakTransformSeq_componentwiseSeq_last [IsNoetherian X] (Z : X.IdealSheafData)
    (hZ : Smooth (Z.subschemeι ≫ f)) {J : X.IdealSheafData} {d : ℕ}
    (hord : J.OrdAlongEq Z.support (d : ℕ∞)) (e : Z.componentwiseSeq.last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = Z.componentwiseSeq.composite) :
    Z.componentwiseSeq.weakTransformSeq J (Fin.last _) = (J.weakTransform Z).comap e := by
  have := hZ
  have hreg : IsRegular Z.subscheme := ⟨fun z =>
    isRegularLocalRing_stalk (Z.subschemeι ≫ f) z⟩
  exact weakTransformSeq_ofCenters_last' f n _ Z
    ((DivisorFamily.prod_orderedComponent _).trans
        (prod_componentFamily_eq Z hreg))
    (pairwise_disjoint_support_orderedComponent Z hreg) hZ hord e he

end Weak

end Hironaka.Sequence
