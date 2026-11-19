/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
public import Hironaka.Resolution.Algebraic.Kol07.Componentwise
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUp.GlueIdealSheaf
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSmooth
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transport of the order conditions to the componentwise sequence

If `ord_{Z_k} J = d` for every component `Z_k` of a smooth center `Z = ∐ Z_k`, the componentwise
sequence is again a smooth blow-up sequence of order `d` [Kol07, Definition 66]: the intermediate
centers `Z_k'` are smooth with `ord = d` and have simple normal crossings with the running total
transform, because the earlier blow-ups are isomorphisms near `Z_k'`. The proof here makes that
local statement global by the device of [Kol07, Proposition 37]: Definition 66 is local on `X`
(`isOrderSeq_of_covers`, `Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Local.lean`), so cover
`X` by the opens

  `U_k := X ∖ ⋃_{l ≠ k} Z_l` (one for each component) and `U_∞ := X ∖ Z`.

Over `U_k` every center but `Z_k` is empty and `Z ∩ U_k = Z_k ∩ U_k`, so the pulled-back sequence is
a single smooth blow-up of order `d` of `(U_k, J|_{U_k}, E|_{U_k})` preceded and followed by empty
blow-ups [Kol07, Warning 20]; over `U_∞` every blow-up is empty. The pullback of `ofCenters c D`
along an open immersion is `ofCenters` of the inverse images (`pullback_ofCenters`), a sequence all
of whose centers are empty is of order `d` for any triple (`isOrderSeq_ofCenters_top`), and a
sequence with one non-empty center carrying the conditions of Definition 66 is of order `d`
(`isOrderSeq_ofCenters_of_single`: the empty blow-ups are isomorphisms along which the pullback
transport of `Hironaka/Sequence/Pullback*.lean` carries the conditions, the total transform
gaining only empty components, `ExtendsByEmpty`). Descent along the cover is
`isOrderSeq_of_covers`.

## Main declarations

* `hasSncWith_top`, `ordAlongEq_top`, `ExtendsByEmpty.hasSncWith_of`,
  `extendsByEmpty_comap_totalTransform_top`: the empty-center bookkeeping.
* `AlgebraicGeometry.Scheme.BlowUpSequence.pullback_ofCenters`: pullbacks of componentwise
  sequences.
* `isOrderSeq_ofCenters_top`, `isOrderSeq_ofCenters_of_single`, `isOrderSeq_ofCenters` (the
  order condition for the componentwise sequence).
* `isIso_subschemeMap_center_ofCenters`, `irreducibleSpace_center_ofCenters`,
  `isRegular_center_ofCenters`: the intermediate centers are isomorphic to the components.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.BlowUpSequence


variable {X : Scheme.{u}}

/-- The pullback [Kol07, 30.1] of the componentwise sequence of `D 0, …, D (c-1)` along `h` is the
componentwise sequence of the inverse images `h⁻¹ D i`: the squares of `blowUpMap` (`blowUpMap_π`)
carry each pulled-back center across the earlier blow-ups. -/
theorem pullback_ofCenters {Y : Scheme.{u}} (c : ℕ) (D : Fin c → X.IdealSheafData) (h : Y ⟶ X) :
    (ofCenters c D).pullback h = ofCenters c fun i => (D i).comap h := by
  induction c generalizing X Y with
  | zero => rfl
  | succ c ih =>
    have hfun : (fun i : Fin c =>
        ((D i.succ).comap (D 0).blowUpπ).comap (Scheme.Hom.blowUpMap h (D 0))) =
          fun i => ((D i.succ).comap h).comap ((D 0).comap h).blowUpπ := by
      funext i
      rw [← comap_comp, ← comap_comp, blowUpMap_π]
    rw [ofCenters_succ, pullback_cons, ih, hfun]
    rfl

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Empty centers: the empty blow-up of Warning 20 satisfies Definition 66 vacuously -/

/-- The unit ideal sheaf (the empty center) has simple normal crossings with every family: there is
no point to check. -/
theorem hasSncWith_top (E : DivisorFamily X) : E.HasSncWith (⊤ : X.IdealSheafData) := by
  intro x hx
  rw [support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hx
  exact hx.elim

/-- Every ideal sheaf has order `m` along the empty center: there is no generic point to check. -/
theorem ordAlongEq_top (J : X.IdealSheafData) (m : ℕ∞) :
    J.OrdAlongEq (⊤ : X.IdealSheafData).support m := by
  intro η hη
  have hη' := hη.1
  rw [support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hη'
  exact hη'.elim

/-- Simple normal crossings with a closed subscheme extend along an extension by empty components
(the converse of `ExtendsByEmpty.hasSncWith`): a component of the extended family through a point
is a component of the original family through it. -/
theorem _root_.AlgebraicGeometry.ExtendsByEmpty.hasSncWith_of {E₁ E₂ : DivisorFamily X}
    (hext : ExtendsByEmpty E₁ E₂)
    {Z : X.IdealSheafData} (h : E₁.HasSncWith Z) : E₂.HasSncWith Z := by
  obtain ⟨ι, hι, hcomp, htop⟩ := hext
  intro x hx
  obtain ⟨n, z, ⟨hreg, c, hc, hcz⟩, s, hs⟩ := h x hx
  have key : ∀ j : {j // x ∈ (E₂.component j).support}, ∃ i, ι i = j.1 := fun j => by
    by_contra hne
    have hj := j.2
    rw [htop j.1 fun ⟨i, hi⟩ => hne ⟨i, hi⟩, support_top, ← SetLike.mem_coe, Closeds.coe_bot] at hj
    exact hj.elim
  choose g hg using key
  have hmem : ∀ j : {j // x ∈ (E₂.component j).support}, x ∈ (E₁.component (g j)).support :=
    fun j => by
      have hj := j.2
      rwa [← hg j, hcomp] at hj
  refine ⟨n, z, ⟨hreg, fun j => c ⟨g j, hmem j⟩, fun j j' hjj' => ?_, fun j => ?_⟩, s, hs⟩
  · have h1 : g j = g j' := congrArg Subtype.val (hc hjj')
    exact Subtype.ext ((hg j).symm.trans ((congrArg ι h1).trans (hg j')))
  · have := hcz ⟨g j, hmem j⟩
    rw [← hg j, hcomp]
    exact this

/-- The total transform of `E` under the empty blow-up is `E` pulled back along the (isomorphic)
blow-up map, extended by the empty exceptional component ([Kol07, Warning 20];
`extendsByEmpty_totalTransform_top_comap_inv` read on the blow-up). -/
theorem extendsByEmpty_comap_totalTransform_top (E : DivisorFamily X) :
    ExtendsByEmpty (E.comap (⊤ : X.IdealSheafData).blowUpπ) (E.totalTransform ⊤) := by
  change ∃ ι' : E.ι → E.ι ⊕ₗ PUnit.{u + 1}, Function.Injective ι' ∧
    (∀ i, (E.totalTransform ⊤).component (ι' i) = (E.component i).comap
        (⊤ : X.IdealSheafData).blowUpπ) ∧
      ∀ j, j ∉ Set.range ι' → (E.totalTransform ⊤).component j = ⊤
  refine ⟨fun j => toLex (Sum.inl j), fun i i' h => Sum.inl_injective (toLex.injective h),
    fun i => ?_, fun j hj => ?_⟩
  · change (E.component i).strictTransform ⊤ = (E.component i).comap (⊤ : X.IdealSheafData).blowUpπ
    exact strictTransform_top_left _
  · obtain ⟨a, rfl⟩ := toLex.surjective j
    rcases a with j₂ | u
    · exact (hj ⟨j₂, rfl⟩).elim
    · change (⊤ : X.IdealSheafData).exceptionalDivisor = ⊤
      exact exceptionalDivisor_top

/-! ### Sequences with at most one non-empty center -/

section Single

variable {k : Type u} [Field k] [CharZero k]

omit [CharZero k] in
/-- A componentwise sequence all of whose centers are empty is a smooth blow-up sequence of order
`d` for every triple ([Kol07, Warning 20 and 32]: empty blow-ups may be interspersed freely). -/
theorem isOrderSeq_ofCenters_top (f : X ⟶ Spec (.of k)) (c : ℕ) (J : X.IdealSheafData)
    (E : DivisorFamily X) (d : ℕ) :
    (ofCenters c fun _ : Fin c => (⊤ : X.IdealSheafData)).IsOrderSeq f J E d := by
  induction c generalizing X with
  | zero => exact ⟨isSmooth_nil f, fun i => i.elim0⟩
  | succ c ih =>
    rw [ofCenters_succ, isOrderSeq_cons_iff]
    refine ⟨⟨inferInstance, hasSncWith_top E, ordAlongEq_top J d⟩, ?_⟩
    have hall : (fun i : Fin c => ((fun _ : Fin (c + 1) => (⊤ : X.IdealSheafData)) i.succ).comap
        (⊤ : X.IdealSheafData).blowUpπ) = fun _ => ⊤ := funext fun _ => comap_top _
    rw [hall]
    exact ih _ _ _

/-- A componentwise sequence with a single non-empty center `D k₀`, which is smooth over `k`, has
order `d` for `J` and has simple normal crossings with `E`, is a smooth blow-up sequence of order
`d` for `(X, J, E)`: the empty blow-ups before `D k₀` are isomorphisms [Kol07, Warning 20] along
which the pullback transport carries the conditions (`smooth_subschemeι_comap_comp`,
`ordAlongEq_comap_of_smooth`, `hasSncWith_comap_of_smooth`), the weak transform along an empty
blow-up being the inverse image (`weakTransform_top_left`) and the total transform the inverse
image extended by an empty component; the empty blow-ups after it satisfy Definition 66
vacuously. -/
theorem isOrderSeq_ofCenters_of_single (f : X ⟶ Spec (.of k)) [Smooth f] (c : ℕ)
    (D : Fin c → X.IdealSheafData) (k₀ : Fin c) (htop : ∀ l, l ≠ k₀ → D l = ⊤)
    {J : X.IdealSheafData} {E : DivisorFamily X} {d : ℕ}
    (hsm : Smooth ((D k₀).subschemeι ≫ f)) (hord : J.OrdAlongEq (D k₀).support (d : ℕ∞))
    (hsnc : E.HasSncWith (D k₀)) : (ofCenters c D).IsOrderSeq f J E d := by
  induction c generalizing X with
  | zero => exact k₀.elim0
  | succ c ih =>
    rw [ofCenters_succ, isOrderSeq_cons_iff]
    rcases k₀ with ⟨_ | j, hj⟩
    · refine ⟨⟨hsm, hsnc, hord⟩, ?_⟩
      have hall : (fun i : Fin c => (D i.succ).comap (D 0).blowUpπ) = fun _ => ⊤ :=
        funext fun i => by rw [htop i.succ (Fin.succ_ne_zero i), comap_top]
      rw [hall]
      exact isOrderSeq_ofCenters_top _ c _ _ d
    · have h0 : D 0 = ⊤ := htop 0 (Fin.succ_ne_zero ⟨j, Nat.lt_of_succ_lt_succ hj⟩).symm
      rw [h0]
      have hiso : IsIso (⊤ : X.IdealSheafData).blowUpπ := blowUp.isIso_π_top
      have hπ : Smooth (⊤ : X.IdealSheafData).blowUpπ := inferInstance
      have hsm' : Smooth ((D (⟨j, Nat.lt_of_succ_lt_succ hj⟩ : Fin c).succ).subschemeι ≫ f) := hsm
      refine ⟨⟨inferInstance, hasSncWith_top E, ordAlongEq_top J d⟩, ?_⟩
      refine ih ((⊤ : X.IdealSheafData).blowUpπ ≫ f) _ ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ?_ ?_ ?_ ?_
      · intro l hl
        show (D l.succ).comap (⊤ : X.IdealSheafData).blowUpπ = ⊤
        rw [htop l.succ fun h => hl (Fin.succ_injective _ h), comap_top]
      · exact smooth_subschemeι_comap_comp (D _) (⊤ : X.IdealSheafData).blowUpπ f
      · rw [weakTransform_top_left]
        exact ordAlongEq_comap_of_smooth _ hord
      · exact (extendsByEmpty_comap_totalTransform_top E).hasSncWith_of
          (hasSncWith_comap_of_smooth f (⊤ : X.IdealSheafData).blowUpπ hsnc)

end Single

/-! ### The componentwise sequence of a disjoint union is of order `d` -/

section Cover

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include f n

omit [CharZero k] f n [SmoothOfRelativeDimension n f] in
/-- The inverse image of a center along the inclusion of an open set missing its support is the
unit ideal sheaf. -/
theorem comap_ι_eq_top_of_disjoint (D : X.IdealSheafData) (U : X.Opens)
    (h : ∀ x ∈ U, x ∉ D.support) : D.comap U.ι = ⊤ := by
  rw [← support_eq_bot_iff, ← SetLike.coe_set_eq, Closeds.coe_bot]
  refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
  rw [SetLike.mem_coe, mem_support_comap_iff_apply] at hw
  exact h _ (Scheme.Opens.ι_mem w) hw

/-- If the disjoint union `Z = ∏ i, D i` of the pairwise disjoint centers `D i` is smooth over `k`,
has order `d` along each `D i` and has simple normal crossings with `E`, then the componentwise
sequence is a smooth blow-up sequence of order `d` for `(X, J, E)` [Kol07, Definition 66]. Proof:
Definition 66 is local on `X` (`isOrderSeq_of_covers`); on the open `U_k = X ∖ ⋃_{l ≠ k} V(D l)`
the sequence pulls back (`pullback_ofCenters`) to a single blow-up of `Z ∩ U_k = V(D k) ∩ U_k`
among empty ones (`isOrderSeq_ofCenters_of_single`), and on `U_∞ = X ∖ V(Z)` to empty blow-ups
(`isOrderSeq_ofCenters_top`); the conditions on `Z` restrict to the pieces by the pullback
transport along the open immersions. -/
theorem isOrderSeq_ofCenters {c : ℕ} (D : Fin c → X.IdealSheafData)
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (hZ : Smooth ((∏ i, D i).subschemeι ≫ f)) {J : X.IdealSheafData} {E : DivisorFamily X}
    {d : ℕ} (hord : J.OrdAlongEq (∏ i, D i).support (d : ℕ∞)) (hsnc : E.HasSncWith (∏ i, D i)) :
    (ofCenters c D).IsOrderSeq f J E d := by
  classical
  have hf : Smooth f := SmoothOfRelativeDimension.smooth n f
  -- the open pieces: `U (some k₀) = X ∖ ⋃_{l ≠ k₀} V(D l)`, `U none = X ∖ ⋃_l V(D l)`
  let T : Option (Fin c) → Finset (Fin c) := fun o => o.elim Finset.univ Finset.univ.erase
  let U : Option (Fin c) → X.Opens := fun o => ((T o).sup fun l => (D l).support).compl
  have hmemU : ∀ o (x : X), x ∈ U o ↔ ∀ l ∈ T o, x ∉ (D l).support := by
    intro o x
    change x ∈ (((T o).sup fun l => (D l).support).compl : Set X) ↔ _
    rw [Closeds.coe_compl, Set.mem_compl_iff, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
      Set.mem_iUnion₂, not_exists]
    exact forall_congr' fun l => not_exists
  have hdisj' : ∀ {i j : Fin c} {x : X}, x ∈ (D i).support → x ∈ (D j).support → i = j := by
    intro i j x hi hj
    by_contra hij
    have this : Disjoint (D i).support (D j).support := hdisj hij
    rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot] at this
    exact Set.eq_empty_iff_forall_notMem.mp this x ⟨hi, hj⟩
  -- the pieces cover `X`
  have hcov : ∀ x : X, ∃ (o : ULift.{u} (Option (Fin c))) (w : (U o.down).toScheme),
      (U o.down).ι w = x := by
    intro x
    by_cases hx : ∃ k₀, x ∈ (D k₀).support
    · obtain ⟨k₀, hk₀⟩ := hx
      refine ⟨⟨some k₀⟩,
      Scheme.Opens.exists_ι_eq_of_mem ((hmemU (some k₀) x).mpr fun l hl hxl => ?_)⟩
      exact (Finset.mem_erase.mp hl).1 (hdisj' hxl hk₀)
    · exact ⟨⟨none⟩,
        Scheme.Opens.exists_ι_eq_of_mem ((hmemU none x).mpr fun l _ => not_exists.mp hx l)⟩
  -- descent along the cover
  refine isOrderSeq_of_covers (ofCenters c D) f n (fun o : ULift.{u} (Option (Fin c)) =>
    (U o.down).ι) hcov J E fun o => ?_
  rw [pullback_ofCenters]
  have htop : ∀ l ∈ T o.down, (D l).comap (U o.down).ι = ⊤ := fun l hl =>
    comap_ι_eq_top_of_disjoint _ _ fun x hx => (hmemU o.down x).mp hx l hl
  rcases o with ⟨_ | k₀⟩
  · -- `U none`: every center is empty
    have hall : (fun i => (D i).comap (U none).ι) =
        fun _ => (⊤ : (U none).toScheme.IdealSheafData) :=
      funext fun i => htop i (Finset.mem_univ i)
    rw [hall]
    exact isOrderSeq_ofCenters_top _ c _ _ d
  · -- `U (some k₀)`: the single blow-up of `Z ∩ U_{k₀} = V(D k₀) ∩ U_{k₀}`
    have hprod : (∏ i, D i).comap (U (some k₀)).ι = (D k₀).comap (U (some k₀)).ι := by
      rw [comap_finset_prod]
      refine Finset.prod_eq_single k₀ (fun l _ hl => ?_) fun h => (h (Finset.mem_univ _)).elim
      exact (htop l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)).trans one_eq_top.symm
    have hZ' : Smooth (((∏ i, D i).comap (U (some k₀)).ι).subschemeι ≫ (U (some k₀)).ι ≫ f) :=
      smooth_subschemeι_comap_comp _ _ f
    rw [hprod] at hZ'
    refine isOrderSeq_ofCenters_of_single _ c _ k₀
      (fun l hl => htop l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)) hZ' ?_ ?_
    · have := ordAlongEq_comap_of_smooth (U (some k₀)).ι hord
      rwa [hprod] at this
    · have := hasSncWith_comap_of_smooth f (U (some k₀)).ι hsnc
      rwa [hprod] at this

end Cover

/-! ### The intermediate centers are isomorphic to the components -/

section Centers

variable {c : ℕ} (D : Fin c → X.IdealSheafData)

/-- The open `U_{k₀} = X ∖ ⋃_{l ≠ k₀} V(D l)`: away from every center but `D k₀`. -/
def complOthers (k₀ : Fin c) : X.Opens :=
  ((Finset.univ.erase k₀).sup fun l => (D l).support).compl

theorem mem_complOthers_iff (k₀ : Fin c) (x : X) :
    x ∈ complOthers D k₀ ↔ ∀ l, l ≠ k₀ → x ∉ (D l).support := by
  change x ∈ ((((Finset.univ.erase k₀).sup fun l => (D l).support).compl : X.Opens) : Set X) ↔ _
  rw [Closeds.coe_compl, Set.mem_compl_iff, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
    Set.mem_iUnion₂, not_exists]
  refine forall_congr' fun l => ?_
  rw [not_exists, Finset.mem_erase]
  exact ⟨fun h hl => h ⟨hl, Finset.mem_univ l⟩, fun h hl => h hl.1⟩

omit D in
/-- When the first `i` centers of a blow-up sequence are empty, the partial composite `Π_i` is an
isomorphism (a composite of the isomorphisms `π_∅`, [Kol07, Warning 20]). -/
theorem isIso_stageMap_of_center_eq_top (S : BlowUpSequence X) (i : Fin (S.length + 1))
    (h : ∀ j : Fin S.length, j.val < i.val → S.center j = ⊤) : IsIso (S.stageMap i) := by
  induction S with
  | nil X => change IsIso (𝟙 X); infer_instance
  | cons X D rest ih =>
    rcases i with ⟨_ | j, hj⟩
    · change IsIso (𝟙 X); infer_instance
    · have hD : D = ⊤ := h ⟨0, Nat.succ_pos _⟩ (Nat.succ_pos j)
      subst hD
      change IsIso (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ (⊤ : X.IdealSheafData).blowUpπ)
      have h1 : IsIso (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩) :=
        ih ⟨j, Nat.lt_of_succ_lt_succ hj⟩ fun j' hj' =>
          h ⟨j'.val + 1, Nat.succ_lt_succ j'.isLt⟩ (Nat.succ_lt_succ hj')
      have h2 : IsIso (⊤ : X.IdealSheafData).blowUpπ := blowUp.isIso_π_top
      infer_instance

/-- For pairwise disjoint centers, the morphism `V(Z_k') → V(D k)`, the base change of `Π_k` along
`V(D k) → X`, is an isomorphism (the intermediate center `Z_k'` is the isomorphic preimage of
`Z_k`, the earlier blow-ups being isomorphisms near it): over `U_k = X ∖ ⋃_{l ≠ k} V(D l)`, which
contains `V(D k)`, the earlier blow-ups are empty, so the base change of `Π_k` along `U_k → X`
(`isPullback_pullbackStageHom`) is a composite of the isomorphisms of [Kol07, Warning 20]. -/
theorem isIso_subschemeMap_center_ofCenters
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (i : Fin (ofCenters c D).length) :
    IsIso (Scheme.IdealSheafData.subschemeMap
      ((D (Fin.cast (length_ofCenters c D) i)).comap ((ofCenters c D).stageMap i.castSucc))
      (D (Fin.cast (length_ofCenters c D) i)) ((ofCenters c D).stageMap i.castSucc)
      (Scheme.IdealSheafData.le_map_comap _ _)) := by
  classical
  set k₀ := Fin.cast (length_ofCenters c D) i with hk₀
  set U := complOthers D k₀ with hU
  have hdisj' : ∀ {a b : Fin c} {x : X}, x ∈ (D a).support → x ∈ (D b).support → a = b := by
    intro a b x ha hb
    by_contra hab
    have this : Disjoint (D a).support (D b).support := hdisj hab
    rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot] at this
    exact Set.eq_empty_iff_forall_notMem.mp this x ⟨ha, hb⟩
  have hsub : Set.range (D k₀).subschemeι ⊆ Set.range U.ι := by
    rw [range_subschemeι, Scheme.Opens.range_ι]
    intro x hx
    exact (mem_complOthers_iff D k₀ x).mpr fun l hl hxl => hl (hdisj' hxl hx)
  have hσ : IsIso (((ofCenters c D).pullback U.ι).stageMap
      ((ofCenters c D).pullbackStageIdx U.ι i.castSucc)) := by
    refine isIso_stageMap_of_center_eq_top _ _ fun j hj => ?_
    have hj' : ((ofCenters c D).pullback U.ι).center j =
        ((ofCenters c D).center (Fin.cast (length_pullback _ _) j)).comap
          ((ofCenters c D).pullbackStageHom U.ι (Fin.cast (length_pullback _ _) j).castSucc) :=
      center_pullback (ofCenters c D) U.ι (Fin.cast (length_pullback _ _) j)
    rw [hj', center_ofCenters, ← comap_comp, pullbackStageHom_stageMap, comap_comp,
      comap_ι_eq_top_of_disjoint _ _ fun x hx => (mem_complOthers_iff D k₀ x).mp hx _
        (Fin.ne_of_val_ne (Nat.ne_of_lt hj)), comap_top]
  have hsq := isPullback_pullbackStageHom (ofCenters c D) U.ι i.castSucc
  have hsub' : IsPullback ((D k₀).comap ((ofCenters c D).stageMap i.castSucc)).subschemeι
      (Scheme.IdealSheafData.subschemeMap _ _ _ (Scheme.IdealSheafData.le_map_comap _ _))
      ((ofCenters c D).stageMap i.castSucc)
      (IsOpenImmersion.lift U.ι (D k₀).subschemeι hsub ≫ U.ι) := by
    rw [IsOpenImmersion.lift_fac]
    exact isPullback_subschemeι_comap _ _
  have hleft := IsPullback.of_right' hsub' hsq
  have hm := property_of_isPullback (MorphismProperty.isomorphisms Scheme.{u}) hleft.flip
    ((MorphismProperty.isomorphisms.iff _).mpr hσ)
  exact (MorphismProperty.isomorphisms.iff _).mp hm

/-- For pairwise disjoint irreducible centers, every center of the componentwise sequence is
irreducible: `V(Z_k') ≅ V(D k)` (`isIso_subschemeMap_center_ofCenters`). -/
theorem irreducibleSpace_center_ofCenters
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (hirr : ∀ i, IrreducibleSpace (D i).subscheme) (i : Fin (ofCenters c D).length) :
    IrreducibleSpace ((ofCenters c D).center i).subscheme := by
  rw [center_ofCenters]
  have := isIso_subschemeMap_center_ofCenters D hdisj i
  exact (Homeomorph.irreducibleSpace_iff (Scheme.homeoOfIso (asIso
    (Scheme.IdealSheafData.subschemeMap _ _ _ (Scheme.IdealSheafData.le_map_comap _ _))))).mpr
    (hirr _)

/-- For pairwise disjoint regular centers, every center of the componentwise sequence is regular:
the stalks correspond under the isomorphism `V(Z_k') ≅ V(D k)`
(`IsRegularLocalRing.of_ringEquiv`). -/
theorem isRegular_center_ofCenters
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (hreg : ∀ i, IsRegular (D i).subscheme) (i : Fin (ofCenters c D).length) :
    IsRegular ((ofCenters c D).center i).subscheme := by
  rw [center_ofCenters]
  have hm := isIso_subschemeMap_center_ofCenters D hdisj i
  refine ⟨fun z => ?_⟩
  have h1 : IsRegularLocalRing ((D (Fin.cast (length_ofCenters c D) i)).subscheme.presheaf.stalk
      ((Scheme.IdealSheafData.subschemeMap _ _ _ (Scheme.IdealSheafData.le_map_comap _ _)) z)) :=
    (hreg _).isRegularAt _
  exact IsRegularLocalRing.of_ringEquiv (asIso ((Scheme.IdealSheafData.subschemeMap _ _ _
    (Scheme.IdealSheafData.le_map_comap _ _)).stalkMap z)).commRingCatIsoToRingEquiv

end Centers

end Hironaka.Sequence
