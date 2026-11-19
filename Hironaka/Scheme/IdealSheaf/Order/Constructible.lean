/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Constructibility and finiteness of the order function

[Kol07, Definition 47]: `x ↦ ord_x I` is a constructible and upper semicontinuous function on `X`,
and `max-ord_Z I := max{ord_z I : z ∈ Z}`, `max-ord I := max-ord_X I`. [Hau03, Appendix A]: on a
Noetherian scheme "the order of `I` takes only finitely many values", and [Hau03, Appendix B]: the
finite stratification by the order, whose stratum of maximal value is closed, the top locus.

* `{ord = m} = {ord ≥ m} \ {ord ≥ m + 1}` (`setOf_ord_eq_eq_sdiff`) is the difference of two closed
  sets (`Hironaka/Scheme/IdealSheaf/Order/Semicontinuity.lean`), hence locally closed
  (`isLocallyClosed_setOf_ord_eq`) and, on a Noetherian space, constructible
  (`isConstructible_setOf_ord_eq`; `IsClosed.isConstructible`: the complement of a closed set is
  open and compact, hence retrocompact);
* the descending chain of closed sets `{ord ≥ m}` stabilizes, `Closeds X` being well-founded under
  `<` on a Noetherian space, at `{ord = ∞} = ⋂_m {ord ≥ m}`
  (`exists_setOf_le_ord_eq_setOf_ord_eq_top`), which is `{x : I_x = 0}` by Krull; so off `{I_x = 0}`
  the order is bounded by some `m₀` (`exists_ord_le_of_stalkIdeal_ne_bot`) and takes finitely many
  values (`finite_image_ord_setOf_stalkIdeal_ne_bot`, `finite_range_ord`). "`I` nonzero on every
  irreducible component" is `I_η ≠ 0` at each generic point `η`; the stalk ideal at a generization
  `x ⤳ y` is the extension of the one at `y` (`stalkIdeal_specializes`), so `I_y = 0` forces
  `I_η = 0` at the generic point of a component through `y` (`stalkIdeal_eq_bot_of_specializes`,
  `stalkIdeal_ne_bot_of_irreducibleComponents`) and the order is then finite everywhere
  (`ord_ne_top_of_irreducibleComponents`);
* `maxOrd I := maxOrdAlong I univ`; `maxOrdAlong I Z = sSup (ord '' Z)`
  (`maxOrdAlong_eq_sSup_image`) is attained on a nonempty `Z` with `I_x ≠ 0` on `Z`, a nonempty
  finite set of `ℕ∞` containing its supremum (`exists_ord_eq_maxOrdAlong`), and finite
  (`maxOrdAlong_ne_top`); likewise `maxOrd` (`exists_ord_eq_maxOrd`, `maxOrd_ne_top`,
  `isGreatest_range_ord`);
* `topLocus I := {x : ord_x I = maxOrd I}` equals `{ord ≥ maxOrd I}`
  (`topLocus_eq_setOf_le`), which is `{ord = ∞}` or some `{ord ≥ m}`, closed either way
  (`isClosed_topLocus`, no Noetherian hypothesis); every level set is constructible
  (`isConstructible_preimage_ord`) and there are finitely many
  (`finite_range_ord_and_isConstructible_preimage_ord`).

The hypotheses of the main theorems (`Challenge/Algebraic.lean`: quasi-compact and
locally of finite type over a field) give `IsNoetherian X` (`Scheme.Hom.isNoetherian_of_field`),
hence `NoetherianSpace X` by Mathlib.

Used for the maximal order throughout (`Hironaka/Resolution/Algebraic/MaximalContact/Basic.lean`,
`Hironaka/Resolution/Algebraic/Balanced/Order.lean`,
`Hironaka/Scheme/IdealSheaf/Derivative/Properties.lean`,
`Hironaka/Resolution/Algebraic/Hir64/MainTheoremIIN.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Data.lean`,
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedFunctor.lean`,
`Hironaka/Resolution/Algebraic/BoundaryClearing/Basic.lean`, among others).
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory Topology TopologicalSpace

universe u

/-- A closed set in a Noetherian space is constructible — its complement is open and, like every
subset of a Noetherian space, compact, hence retrocompact. -/
theorem _root_.IsClosed.isConstructible {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y]
    {s : Set Y} (hs : IsClosed s) : IsConstructible s :=
  isConstructible_compl.mp ((NoetherianSpace.isCompact sᶜ).isConstructible hs.isOpen_compl)

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- [Kol07, Definition 47]: `max-ord I := max-ord_X I`, the supremum of `ord_x I` over all points
of `X` — `maxOrdAlong` on `Set.univ`. It is attained and finite on a Noetherian `X` with `I_x ≠ 0`
at every point (`exists_ord_eq_maxOrd`, `maxOrd_ne_top`). -/
noncomputable def maxOrd : ℕ∞ := I.maxOrdAlong Set.univ

/-- [Hau03, Appendix B]: the top locus `{x : ord_x I = max-ord I}`, the stratum of maximal order.
It is closed (`isClosed_topLocus`). -/
def topLocus : Set X := {x | I.ord x = I.maxOrd}

/-- `{ord = m} = {ord ≥ m} \ {ord ≥ m + 1}`. -/
theorem setOf_ord_eq_eq_sdiff (m : ℕ) :
    {x | I.ord x = m} = {x | (m : ℕ∞) ≤ I.ord x} \ {x | ((m + 1 : ℕ) : ℕ∞) ≤ I.ord x} := by
  ext x
  change I.ord x = m ↔ (m : ℕ∞) ≤ I.ord x ∧ ¬ ((m + 1 : ℕ) : ℕ∞) ≤ I.ord x
  rw [not_le]
  constructor
  · intro h
    rw [h]
    exact ⟨le_rfl, by exact_mod_cast Nat.lt_succ_self m⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h2)
    rw [← hr] at h1 h2 ⊢
    norm_cast at h1 h2 ⊢
    omega

/-- The stalk at a generization: for `x ⤳ y`, `I_x = I_y 𝒪_{X,x}` — the stalk ideal
at `x` is the extension of the stalk ideal at `y` along the specialization map
`𝒪_{X,y} → 𝒪_{X,x}` (both are the extension of `I(U)` from an affine `U ∋ y`, which contains
`x`). -/
theorem stalkIdeal_specializes {x y : X} (h : x ⤳ y) :
    I.stalkIdeal x = (I.stalkIdeal y).map (X.presheaf.stalkSpecializes h).hom := by
  obtain ⟨U, hyU⟩ := exists_affineOpens_mem y
  rw [I.stalkIdeal_eq_map_germ U hyU, I.stalkIdeal_eq_map_germ U (h.mem_open U.1.2 hyU),
    Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]

/-- `I_y = 0` implies `I_x = 0` for every generization `x ⤳ y`. -/
theorem stalkIdeal_eq_bot_of_specializes {x y : X} (h : x ⤳ y) (hy : I.stalkIdeal y = ⊥) :
    I.stalkIdeal x = ⊥ := by
  rw [I.stalkIdeal_specializes h, hy, Ideal.map_bot]

/-- Kollár's hypothesis `I ≠ 0` on a variety ([Kol07, Definition 47]), read on a reducible `X` as
"nonzero on every irreducible component": if `I` is nonzero at the generic point
of every irreducible component of `X`, then `I_x ≠ 0` at every point — `x` lies on the component
`irreducibleComponent x`, whose generic point `η` generizes `x`. -/
theorem stalkIdeal_ne_bot_of_irreducibleComponents
    (h : ∀ Z ∈ irreducibleComponents X, ∀ η, IsGenericPoint η Z → I.stalkIdeal η ≠ ⊥) (x : X) :
    I.stalkIdeal x ≠ ⊥ := by
  intro hx
  have hgen := (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  exact h _ (irreducibleComponent_mem_irreducibleComponents x) _ hgen
    (I.stalkIdeal_eq_bot_of_specializes (hgen.specializes mem_irreducibleComponent) hx)

/-- If `I` is nonzero on every irreducible component of the locally Noetherian `X`, the order is
finite everywhere (Krull's intersection theorem). -/
theorem ord_ne_top_of_irreducibleComponents [IsLocallyNoetherian X]
    (h : ∀ Z ∈ irreducibleComponents X, ∀ η, IsGenericPoint η Z → I.stalkIdeal η ≠ ⊥) (x : X) :
    I.ord x ≠ ⊤ :=
  fun hx => I.stalkIdeal_ne_bot_of_irreducibleComponents h x ((I.ord_eq_top_iff x).mp hx)

/-- `max-ord_Z I` is the supremum of the set of values `{ord_z I : z ∈ Z}`. -/
theorem maxOrdAlong_eq_sSup_image (Z : Set X) :
    I.maxOrdAlong Z = sSup ((fun x => I.ord x) '' Z) := by
  rw [maxOrdAlong, sSup_image]

/-- `max-ord I = sup_x ord_x I`. -/
theorem maxOrd_eq_iSup : I.maxOrd = ⨆ x, I.ord x := by
  rw [maxOrd, maxOrdAlong, iSup_univ]

/-- `ord_x I ≤ max-ord I`. -/
theorem le_maxOrd (x : X) : I.ord x ≤ I.maxOrd :=
  I.le_maxOrdAlong (Set.mem_univ x)

/-- `max-ord I ≤ m ⟺ ord_x I ≤ m` for every `x`. -/
theorem maxOrd_le_iff {m : ℕ∞} : I.maxOrd ≤ m ↔ ∀ x, I.ord x ≤ m := by
  rw [maxOrd, maxOrdAlong_le_iff]
  simp

/-- The top locus is `{x : ord_x I ≥ max-ord I}`. -/
theorem topLocus_eq_setOf_le : I.topLocus = {x | I.maxOrd ≤ I.ord x} := by
  ext x
  exact ⟨fun h => (h : I.ord x = I.maxOrd).ge, fun h => le_antisymm (I.le_maxOrd x) h⟩

section Field

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- The hypotheses of the main theorems give the Noetherian hypothesis ([Hau03, Appendix A], "all
our schemes will be assumed to be noetherian"): a scheme quasi-compact and locally of finite type
over a field is Noetherian, hence a Noetherian topological space (Mathlib's
`IsNoetherian.noetherianSpace`). -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isNoetherian_of_field [LocallyOfFiniteType f]
    [QuasiCompact f] : IsNoetherian X :=
  haveI := f.isLocallyNoetherian_of_field
  haveI := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

section Smooth

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

omit [CharZero k] in
include f n in
/-- A scheme smooth over a field is locally Noetherian (it is locally of finite type). -/
theorem isLocallyNoetherian_of_smoothOfRelativeDimension : IsLocallyNoetherian X :=
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  f.isLocallyNoetherian_of_field

include f n in
/-- `{ord = m}` is locally closed — the difference of two closed sets. -/
theorem isLocallyClosed_setOf_ord_eq (m : ℕ) : IsLocallyClosed {x | I.ord x = m} := by
  rw [setOf_ord_eq_eq_sdiff, Set.sdiff_eq]
  exact (isClosed_setOf_le_ord f n I m).isLocallyClosed.inter
    (isClosed_setOf_le_ord f n I (m + 1)).isOpen_compl.isLocallyClosed

include f n in
/-- [Kol07, Definition 47]: `{ord = m}` is constructible on a Noetherian `X`. -/
theorem isConstructible_setOf_ord_eq [NoetherianSpace X] (m : ℕ) :
    IsConstructible {x | I.ord x = m} := by
  rw [setOf_ord_eq_eq_sdiff]
  exact (isClosed_setOf_le_ord f n I m).isConstructible.sdiff
    (isClosed_setOf_le_ord f n I (m + 1)).isConstructible

include f n in
/-- The descending chain of closed sets `{ord ≥ m}` stabilizes (`Closeds X` is
well-founded under `<` on a Noetherian space), at `{ord = ∞} = ⋂_m {ord ≥ m}`. -/
theorem exists_setOf_le_ord_eq_setOf_ord_eq_top [NoetherianSpace X] :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → {x | (m : ℕ∞) ≤ I.ord x} = {x | I.ord x = ⊤} := by
  let C : ℕ → Closeds X := fun m => ⟨{x | (m : ℕ∞) ≤ I.ord x}, isClosed_setOf_le_ord f n I m⟩
  have hC : Antitone C := fun a b hab x hx => by
    change (a : ℕ∞) ≤ I.ord x
    exact le_trans (by exact_mod_cast hab) hx
  obtain ⟨m₀, hm₀⟩ := WellFoundedLT.antitone_chain_condition hC
  refine ⟨m₀, fun m hm => ?_⟩
  have heq : {x | (m : ℕ∞) ≤ I.ord x} = {x | (m₀ : ℕ∞) ≤ I.ord x} :=
    congrArg SetLike.coe (hm₀ m hm).symm
  rw [heq, setOf_ord_eq_top_eq_iInter]
  refine Set.Subset.antisymm (fun x hx => Set.mem_iInter.mpr fun m' => ?_) (Set.iInter_subset _ m₀)
  rcases le_or_gt m' m₀ with h' | h'
  · exact le_trans (Nat.cast_le.mpr h' : (m' : ℕ∞) ≤ m₀) hx
  · have : {x | (m' : ℕ∞) ≤ I.ord x} = {x | (m₀ : ℕ∞) ≤ I.ord x} :=
      congrArg SetLike.coe (hm₀ m' h'.le).symm
    rw [this]
    exact hx

include f n in
/-- On `X ∖ {I_x = 0}` the order is bounded by some `m₀`. -/
theorem exists_ord_le_of_stalkIdeal_ne_bot [NoetherianSpace X] :
    ∃ m₀ : ℕ, ∀ x, I.stalkIdeal x ≠ ⊥ → I.ord x ≤ m₀ := by
  obtain ⟨m₀, hm₀⟩ := exists_setOf_le_ord_eq_setOf_ord_eq_top I f n
  refine ⟨m₀, fun x hx => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have h1 : ((m₀ + 1 : ℕ) : ℕ∞) ≤ I.ord x := by
    rw [Nat.cast_succ]
    exact Order.add_one_le_of_lt hlt
  have h2 : x ∈ {x | I.ord x = ⊤} := hm₀ (m₀ + 1) (Nat.le_succ m₀) ▸ h1
  have := isLocallyNoetherian_of_smoothOfRelativeDimension f n
  exact hx ((I.ord_eq_top_iff x).mp h2)

include f n in
/-- [Hau03, Appendix A]: on `X ∖ {I_x = 0}` the order takes finitely many values. -/
theorem finite_image_ord_setOf_stalkIdeal_ne_bot [NoetherianSpace X] :
    ((fun x => I.ord x) '' {x | I.stalkIdeal x ≠ ⊥}).Finite := by
  obtain ⟨m₀, hm₀⟩ := exists_ord_le_of_stalkIdeal_ne_bot I f n
  refine ((Set.finite_le_nat m₀).image (Nat.cast : ℕ → ℕ∞)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have hle : I.ord x ≤ m₀ := hm₀ x hx
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (hle.trans_lt (ENat.natCast_lt_top m₀)).ne
  refine ⟨r, ?_, hr⟩
  rw [← hr] at hle
  exact_mod_cast hle

include f n in
/-- The order takes finitely many values on `X` (`∞` included). -/
theorem finite_range_ord [NoetherianSpace X] : (Set.range fun x => I.ord x).Finite := by
  refine ((finite_image_ord_setOf_stalkIdeal_ne_bot I f n).insert ⊤).subset ?_
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_insert_iff]
  by_cases hx : I.stalkIdeal x = ⊥
  · have := isLocallyNoetherian_of_smoothOfRelativeDimension f n
    exact Or.inl ((I.ord_eq_top_iff x).mpr hx)
  · exact Or.inr ⟨x, hx, rfl⟩

include f n in
/-- `max-ord_Z I` is attained for `Z` nonempty with `I_x ≠ 0` at all `x ∈ Z` — the set of values is
finite and nonempty, so it contains its supremum. -/
theorem exists_ord_eq_maxOrdAlong [NoetherianSpace X] {Z : Set X} (hZ : Z.Nonempty)
    (hI : ∀ x ∈ Z, I.stalkIdeal x ≠ ⊥) : ∃ z ∈ Z, I.ord z = I.maxOrdAlong Z := by
  have hfin : ((fun x => I.ord x) '' Z).Finite :=
    (finite_image_ord_setOf_stalkIdeal_ne_bot I f n).subset (Set.image_mono hI)
  obtain ⟨z, hz, hz'⟩ := (hZ.image fun x => I.ord x).csSup_mem hfin
  exact ⟨z, hz, by rw [maxOrdAlong_eq_sSup_image]; exact hz'⟩

include f n in
/-- `max-ord_Z I` is finite when `I_x ≠ 0` at all `x ∈ Z`. -/
theorem maxOrdAlong_ne_top [NoetherianSpace X] {Z : Set X} (hI : ∀ x ∈ Z, I.stalkIdeal x ≠ ⊥) :
    I.maxOrdAlong Z ≠ ⊤ := by
  obtain ⟨m₀, hm₀⟩ := exists_ord_le_of_stalkIdeal_ne_bot I f n
  exact ((I.maxOrdAlong_le_iff.mpr fun z hz => hm₀ z (hI z hz)).trans_lt
    (ENat.natCast_lt_top m₀)).ne

include f n in
/-- `max-ord I` is attained on a nonempty `X` with `I_x ≠ 0` everywhere. -/
theorem exists_ord_eq_maxOrd [NoetherianSpace X] [Nonempty X] (hI : ∀ x, I.stalkIdeal x ≠ ⊥) :
    ∃ x, I.ord x = I.maxOrd := by
  obtain ⟨z, -, hz⟩ := exists_ord_eq_maxOrdAlong I f n Set.univ_nonempty fun x _ => hI x
  exact ⟨z, hz⟩

include f n in
/-- `max-ord I` is finite when `I_x ≠ 0` everywhere. -/
theorem maxOrd_ne_top [NoetherianSpace X] (hI : ∀ x, I.stalkIdeal x ≠ ⊥) : I.maxOrd ≠ ⊤ :=
  maxOrdAlong_ne_top I f n fun x _ => hI x

include f n in
/-- `max-ord I` is the greatest value of `x ↦ ord_x I` on a nonempty `X` with `I_x ≠ 0` everywhere
(the form in which Main Theorem II takes the maximal order `d`). -/
theorem isGreatest_range_ord [NoetherianSpace X] [Nonempty X] (hI : ∀ x, I.stalkIdeal x ≠ ⊥) :
    IsGreatest (Set.range fun x => I.ord x) I.maxOrd := by
  obtain ⟨x, hx⟩ := exists_ord_eq_maxOrd I f n hI
  refine ⟨⟨x, hx⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact I.le_maxOrd y

include f n in
/-- [Hau03, Appendix B]: the top locus `{ord = max-ord I}` is closed — it is
`{ord ≥ max-ord I}`, that is `{ord = ∞}` when `max-ord I = ∞` and `{ord ≥ m}` when
`max-ord I = m`. -/
theorem isClosed_topLocus : IsClosed I.topLocus := by
  rw [topLocus_eq_setOf_le]
  by_cases h : I.maxOrd = ⊤
  · rw [h]
    simp_rw [top_le_iff]
    exact isClosed_setOf_ord_eq_top f n I
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    rw [← hm]
    exact isClosed_setOf_le_ord f n I m

include f n in
/-- The top locus is nonempty on a nonempty Noetherian `X` with `I_x ≠ 0` everywhere. -/
theorem topLocus_nonempty [NoetherianSpace X] [Nonempty X] (hI : ∀ x, I.stalkIdeal x ≠ ⊥) :
    I.topLocus.Nonempty :=
  exists_ord_eq_maxOrd I f n hI

include f n in
/-- The level set `{ord = ∞}` is constructible (it is closed). -/
theorem isConstructible_setOf_ord_eq_top [NoetherianSpace X] : IsConstructible {x | I.ord x = ⊤} :=
  (isClosed_setOf_ord_eq_top f n I).isConstructible

include f n in
/-- Every level set of `x ↦ ord_x I` is constructible. -/
theorem isConstructible_preimage_ord [NoetherianSpace X] (v : ℕ∞) :
    IsConstructible ((fun x => I.ord x) ⁻¹' {v}) := by
  cases v using ENat.recTopCoe with
  | top => exact isConstructible_setOf_ord_eq_top I f n
  | coe m => exact isConstructible_setOf_ord_eq I f n m

include f n in
/-- [Kol07, Definition 47]: `x ↦ ord_x I` is a constructible function — it takes finitely many
values and every level set is constructible. -/
theorem finite_range_ord_and_isConstructible_preimage_ord [NoetherianSpace X] :
    (Set.range fun x => I.ord x).Finite ∧
      ∀ v : ℕ∞, IsConstructible ((fun x => I.ord x) ⁻¹' {v}) :=
  ⟨finite_range_ord I f n, isConstructible_preimage_ord I f n⟩

end Smooth

end Field

end AlgebraicGeometry.Scheme.IdealSheafData

/-! ### The unit ideal sheaf has maximal order `0` -/

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry Scheme.IdealSheafData

/-- The unit ideal sheaf has maximal order `0` (`ord_top` at every point); in the namespace of
its users, `Hironaka/Resolution/Algebraic/Stage/Base.lean` and
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedNil.lean`. -/
theorem maxOrd_top {X : Scheme.{u}} : (⊤ : X.IdealSheafData).maxOrd = 0 :=
  le_antisymm ((Scheme.IdealSheafData.maxOrd_le_iff _).mpr fun x =>
      by rw [Scheme.IdealSheafData.ord_top]) zero_le

end AlgebraicGeometry
