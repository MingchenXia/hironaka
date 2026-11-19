/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Algebra.Local.OrderFlat
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The order along a center under a field extension

For `σ : k →+* L` a field extension in characteristic zero and `p : X_{L,σ} → X` the projection of
a cartesian square over `Spec σ` (flat, but not smooth or of finite type when `L/k` is infinite),
the order of an ideal at a generic point `η'` of a component of the base-changed center
`(Z)_{L,σ}` equals its order at `η = p η'`, provided the center is smooth over `k`, as the centers
of a smooth blow-up sequence are ([Kol07, Notation 19]; `IsSmooth`). Kollár asserts that the
change of fields "will hold automatically for all blow-up sequence functors that we construct"
[Kol07, 34.2]; this module and its two sibling modules supply the transports.

## The argument

At a generic point `η` of the support of a center `Z` with `V(Z) → Spec k` smooth, the stalk
ideal is the maximal ideal: `𝒪_{X,η}/Z_η` is regular, hence a domain, so `Z_η` is prime, and
`exists_genericPoint_of_isPrime_stalkIdeal` produces the generic point `η₀` of the component
through `η` with `Z_{η₀} = 𝔪_{η₀}` and `η₀ ⤳ η`; `η` being itself a generic point of `Z.support`
(maximal for specialization), `η₀ = η`. The same holds at `η'` on `X_{L,σ}` because
`V(Z.comap p) → Spec L` is the base change of `V(Z) → Spec k` (the closed-subscheme square pasted
on the base-change square) and smoothness is stable under base change. Then
`𝔪_η 𝒪_{η'} = (Z.comap p)_{η'} = 𝔪_{η'}` (`stalkIdeal_comap`), the stalk map is flat
(`Flat.stalkMap`) and local, and `ord_map_eq_of_flat_of_map_maximalIdeal_eq` gives
`ord_{η'}(p^* I) = ord_η I`. No reducedness of the fibre `κ(η) ⊗_k L` is needed, because the
centers are smooth. The `≥ m` form holds along every flat morphism (`ord_le_ord_map`).

With this, the weak transform of [Kol07, Definition 60] commutes with the base change exactly as
with a smooth pullback (`weakTransform_comap_of_orderAlong_of_isPullback_specMap`, by
`weakTransform_eq_markedTransform_of_smooth` on both sides and
`markedTransform_comap_blowUpMap_of_pow_dvd`),
and so do the induced ideals of a smooth blow-up sequence of order `m` along the base-changed
sequence (`IsOrderSeq.weakTransformSeq_pullback_mk_of_isPullback_specMap`, induction with the
stage squares of `Hironaka/Scheme/BlowUpSequence/BaseChange.lean`); the marked transforms commute
with every flat base change (`IsOrderGeSeq.markedTransformSeq_pullback_mk_of_flat`). None of this is
in the sources, which assert the transports without proof.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
  Scheme IdealSheafData BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Generic points of smooth centers -/

section GenericPoint

variable {k : Type u} [Field k]

/-- At a generic point `η` of the support of a center `Z` smooth over `k` (on `X` smooth over
`k`), the stalk ideal of `Z` is the maximal ideal: `𝒪_{X,η}/Z_η` is regular, so `Z_η` is prime,
and the generic point of the component of `V(Z)` through `η`
(`exists_genericPoint_of_isPrime_stalkIdeal`) is `η` itself. Not in the sources. -/
theorem stalkIdeal_eq_maximalIdeal_of_mem_genericPoints (f : X ⟶ Spec (.of k)) [Smooth f]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)] {η : X} (hη : η ∈ Z.support.genericPoints) :
    Z.stalkIdeal η = maximalIdeal (X.presheaf.stalk η) := by
  have hreg : IsRegularLocalRing (X.presheaf.stalk η) :=
    isRegularLocalRing_stalk f η
  have hP : (Z.stalkIdeal η).IsPrime := by
    have := isRegularLocalRing_quotient_stalkIdeal Z f hη.1
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  obtain ⟨η₀, hη₀, hsp, hmax, -, -⟩ := exists_genericPoint_of_isPrime_stalkIdeal Z η
  have heq : η₀ = η := hη.2 hη₀.1 hsp
  subst heq
  exact hmax

end GenericPoint

/-! ### The order at a point under a flat morphism with `𝔪_A B = 𝔪_B` -/

/-- For a flat `p` and a point `η'` at which the stalk ideals of `Z` and of `Z.comap p` are the
maximal ideals, the order of every ideal sheaf is preserved, `ord_{η'}(p^* I) = ord_{p η'} I`
(`ord_map_eq_of_flat_of_map_maximalIdeal_eq`). -/
theorem ord_comap_of_flat_of_stalkIdeal_eq (p : Y ⟶ X) [Flat p] (Z : X.IdealSheafData) {η' : Y}
    (hZ : Z.stalkIdeal (p η') = maximalIdeal (X.presheaf.stalk (p η')))
    (hZ' : (Z.comap p).stalkIdeal η' = maximalIdeal (Y.presheaf.stalk η'))
    (I : X.IdealSheafData) : (I.comap p).ord η' = I.ord (p η') := by
  rw [Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, Scheme.IdealSheafData.ord_eq_ord_stalkIdeal,
    Scheme.IdealSheafData.stalkIdeal_comap]
  let : Algebra (X.presheaf.stalk (p η')) (Y.presheaf.stalk η') := (p.stalkMap η').hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (p η')) (Y.presheaf.stalk η') := Flat.stalkMap p η'
  have : IsLocalHom (algebraMap (X.presheaf.stalk (p η')) (Y.presheaf.stalk η')) :=
    inferInstanceAs (IsLocalHom (p.stalkMap η').hom)
  have h : (maximalIdeal (X.presheaf.stalk (p η'))).map
      (algebraMap (X.presheaf.stalk (p η')) (Y.presheaf.stalk η')) =
        maximalIdeal (Y.presheaf.stalk η') := by
    rw [← hZ, ← hZ']
    exact (Scheme.IdealSheafData.stalkIdeal_comap Z p η').symm
  exact ord_map_eq_of_flat_of_map_maximalIdeal_eq h _

/-! ### The base-changed center is smooth over the extended field -/

/-- The base change of a smooth closed subscheme along any cartesian square is smooth: the
closed-subscheme square `AlgebraicGeometry.isPullback_subschemeι_comap` pasted on the square (one
step of
`Triple.IsBaseChangeOf.isSmooth_pullback`). -/
theorem smooth_subschemeι_comap_comp_of_isPullback {S T : Scheme.{u}} {p : Y ⟶ X} {g' : Y ⟶ T}
    {g : X ⟶ S} {h : T ⟶ S} (sq : IsPullback p g' g h) (Z : X.IdealSheafData)
    [Smooth (Z.subschemeι ≫ g)] : Smooth ((Z.comap p).subschemeι ≫ g') :=
  property_of_isPullback @Smooth
    ((isPullback_subschemeι_comap Z p).flip.paste_vert sq).flip inferInstance

/-! ### The order along a center under a field extension -/

section BaseChange

variable {k : Type u} [Field k] {L : Type u} [Field L] {σ : k →+* L}
  {p : Y ⟶ X} {g' : Y ⟶ Spec (.of L)} {g : X ⟶ Spec (.of k)}

/-- The projection of a base-change square along a field extension is flat
(`IsBaseChangeOf.flat` for an arbitrary cartesian square). -/
theorem flat_of_isPullback_specMap (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ))) :
    Flat p :=
  property_of_isPullback @Flat sq
      (flat_and_surjective_specMap σ).1

/-- The projection of a base-change square along a field extension is surjective
(`IsBaseChangeOf.surjective` for an arbitrary cartesian square; the base change of the surjective
`Spec L → Spec k`, `flat_and_surjective_specMap`). -/
theorem surjective_of_isPullback_specMap
    (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ))) : Function.Surjective p := by
  have hr := range_fst_of_isPullback sq
  rw [← Set.range_eq_univ, hr,
    Set.range_eq_univ.mpr (flat_and_surjective_specMap σ).2.surj,
        Set.preimage_univ]

/-- The base change of a smooth `k`-scheme is a smooth `L`-scheme. -/
theorem smooth_of_isPullback_specMap (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ)))
    [Smooth g] : Smooth g' :=
  property_of_isPullback @Smooth sq.flip inferInstance

/-- The base change of a `k`-scheme smooth of relative dimension `n` is smooth of relative
dimension `n` over `L`. -/
theorem smoothOfRelativeDimension_of_isPullback_specMap
    (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ))) (n : ℕ)
    [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n g' := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  exact property_of_isPullback _ sq.flip inferInstance

/-- The order along a smooth center is preserved by base change along a field extension,
`ord_{(Z)_{L,σ}}(p^* I) = ord_Z I` (needed for the change of fields of [Kol07, 34.2]; not in the
sources): at a generic point `η'` of `(Z)_{L,σ}` both stalk ideals are the maximal ideals
(`stalkIdeal_eq_maximalIdeal_of_mem_genericPoints` on `X` and on `X_{L,σ}`), and the flat local
stalk map preserves the order (`ord_comap_of_flat_of_stalkIdeal_eq`). -/
theorem ordAlongEq_comap_of_isPullback_specMap
    (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ))) [Smooth g] (Z : X.IdealSheafData)
    [Smooth (Z.subschemeι ≫ g)] {I : X.IdealSheafData} {m : ℕ∞}
    (hm : I.OrdAlongEq Z.support m) : (I.comap p).OrdAlongEq (Z.comap p).support m := by
  have : Flat p := flat_of_isPullback_specMap sq
  have : Smooth g' := smooth_of_isPullback_specMap sq
  have : Smooth ((Z.comap p).subschemeι ≫ g') := smooth_subschemeι_comap_comp_of_isPullback sq Z
  intro η' hη'
  have hη := mem_genericPoints_support_of_flat p Z hη'
  rw [ord_comap_of_flat_of_stalkIdeal_eq p Z
    (stalkIdeal_eq_maximalIdeal_of_mem_genericPoints g Z hη)
    (stalkIdeal_eq_maximalIdeal_of_mem_genericPoints g' (Z.comap p) hη') I]
  exact hm _ hη

/-- The `≥ m` form: orders never drop under a local homomorphism, so the condition "order `≥ m`
along the center" transports along every flat morphism. -/
theorem leOrdAlong_comap_of_flat (p : Y ⟶ X) [Flat p] (Z : X.IdealSheafData)
    {I : X.IdealSheafData} {m : ℕ∞} (hm : I.LeOrdAlong Z.support m) :
    (I.comap p).LeOrdAlong (Z.comap p).support m := by
  intro η' hη'
  have hη := mem_genericPoints_support_of_flat p Z hη'
  refine (hm _ hη).trans ?_
  rw [Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, Scheme.IdealSheafData.ord_eq_ord_stalkIdeal,
    Scheme.IdealSheafData.stalkIdeal_comap]
  exact ord_le_ord_map (p.stalkMap η').hom _

/-- Characteristic zero passes to the extension field. -/
theorem charZero_of_ringHom [CharZero k] (σ : k →+* L) : CharZero L := by
  let := σ.toAlgebra
  exact charZero_of_injective_algebraMap σ.injective

/-! ### The weak transform under a field extension -/

/-- In the setting of [Kol07, Definition 66] the weak transform commutes with the base change
along a field extension (the analogue of `weakTransform_comap_of_orderAlong` for a smooth
pullback): both sides are the marked transform with mark `m`
(`weakTransform_eq_markedTransform_of_smooth`; the order along the base-changed center by
`ordAlongEq_comap_of_isPullback_specMap`, the center smooth over `L` by base change), and the
marked transform pulls back along the flat morphism of blow-ups
(`markedTransform_comap_blowUpMap_of_pow_dvd`). -/
theorem weakTransform_comap_of_orderAlong_of_isPullback_specMap [CharZero k]
    (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ))) (n : ℕ)
    [SmoothOfRelativeDimension n g] (D I : X.IdealSheafData) [Smooth (D.subschemeι ≫ g)] {m : ℕ}
    (hm : I.OrdAlongEq D.support (m : ℕ∞)) :
    (I.comap p).weakTransform (D.comap p) = (I.weakTransform D).comap (Scheme.Hom.blowUpMap p
        D) := by
  have : CharZero L := charZero_of_ringHom σ
  have : Flat p := flat_of_isPullback_specMap sq
  have : SmoothOfRelativeDimension n g' := smoothOfRelativeDimension_of_isPullback_specMap sq n
  have : Smooth g := SmoothOfRelativeDimension.smooth n g
  have : Smooth ((D.comap p).subschemeι ≫ g') := smooth_subschemeι_comap_comp_of_isPullback sq D
  rw [weakTransform_eq_markedTransform_of_smooth g n D I hm,
    weakTransform_eq_markedTransform_of_smooth g' n (D.comap p) (I.comap p)
      (ordAlongEq_comap_of_isPullback_specMap sq D hm)]
  exact markedTransform_comap_blowUpMap_of_pow_dvd p D I m
    (pow_dvd_comap_of_leOrdAlong g n D I fun η hη => (hm η hη).ge)

/-- The induced ideals of the base-changed sequence are the inverse images of the induced ideals
under the stage lifts, in the `⟨j, hj⟩` form (the analogue of
`IsOrderSeq.weakTransformSeq_pullback_mk` for a smooth pullback). Induction on the sequence; the
square of the next stage is the base-change square of the blow-up (`isPullback_blowUpMap`) pasted
on the given one. -/
theorem IsOrderSeq.weakTransformSeq_pullback_mk_of_isPullback_specMap [CharZero k]
    (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ))) (n : ℕ)
    [SmoothOfRelativeDimension n g] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq g I E m) (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback p).weakTransformSeq (I.comap p) (S.pullbackStageIdx p ⟨j, hj⟩) =
      (S.weakTransformSeq I ⟨j, hj⟩).comap (S.pullbackStageHom p ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderSeq_cons_iff g I E m D rest).1 hS
      have : Flat p := flat_of_isPullback_specMap sq
      have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ g) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth g n D
      have sq₁ : IsPullback (Scheme.Hom.blowUpMap p D) ((D.comap p).blowUpπ ≫ g')
          (D.blowUpπ ≫ g)
          (Spec.map (CommRingCat.ofHom σ)) :=
        (isPullback_blowUpMap p D).paste_vert sq
      have := ih sq₁ ht j (Nat.lt_of_succ_lt_succ hj)
      rw [← weakTransform_comap_of_orderAlong_of_isPullback_specMap sq n D I hm] at this
      exact this

/-- The induced ideals of the base-changed sequence, for every stage. -/
theorem IsOrderSeq.weakTransformSeq_pullback_of_isPullback_specMap [CharZero k]
    (sq : IsPullback p g' g (Spec.map (CommRingCat.ofHom σ))) (n : ℕ)
    [SmoothOfRelativeDimension n g] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq g I E m) (i : Fin (S.length + 1)) :
    (S.pullback p).weakTransformSeq (I.comap p) (S.pullbackStageIdx p i) =
      (S.weakTransformSeq I i).comap (S.pullbackStageHom p i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderSeq.weakTransformSeq_pullback_mk_of_isPullback_specMap sq n hS j hj

end BaseChange

/-! ### The marked transforms along any flat base change -/

section Marked

variable {k : Type u} [Field k]

/-- The induced marked ideals of a smooth blow-up sequence of order `≥ m` pull back along every
flat morphism, in the `⟨j, hj⟩` form (`IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk`
for
a flat `h`): `markedTransform_comap_blowUpMap_of_pow_dvd` at each stage, the divisibility
`F^m ∣ π^* I` from
the order condition. -/
theorem IsOrderGeSeq.markedTransformSeq_pullback_mk_of_flat [CharZero k] (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Flat h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (hS : S.IsOrderGeSeq f I m E) (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback h).markedTransformSeq (I.comap h) m (S.pullbackStageIdx h ⟨j, hj⟩) =
      (S.markedTransformSeq I m ⟨j, hj⟩).comap (S.pullbackStageHom h ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 hS
      have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have : Flat (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap h D) ht j
          (Nat.lt_of_succ_lt_succ hj)
      rw [← markedTransform_comap_blowUpMap_of_pow_dvd h D I m
        (pow_dvd_comap_of_leOrdAlong f n D I hm)]
        at this
      exact this

/-- The induced marked ideals along a flat base change, for every stage. -/
theorem IsOrderGeSeq.markedTransformSeq_pullback_of_flat [CharZero k] (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Flat h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (hS : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    (S.pullback h).markedTransformSeq (I.comap h) m (S.pullbackStageIdx h i) =
      (S.markedTransformSeq I m i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderGeSeq.markedTransformSeq_pullback_mk_of_flat f n h hS j hj

end Marked

end AlgebraicGeometry
