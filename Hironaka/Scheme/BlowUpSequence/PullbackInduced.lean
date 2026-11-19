/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.FlatBaseChange
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackSmooth
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The induced data of a blow-up sequence under a smooth pullback

Along a smooth morphism `h : Y → X` the induced ideals and divisors of the pulled-back sequence are
the pullbacks of the induced ideals and divisors, and the order conditions of
[Kol07, Definition 66] are preserved ([Wlo05, Proposition 2.4.2]; [Kol07, 34.1]). This module
proves the identifications of the induced data; the transport of the order conditions is in
`Hironaka/Scheme/BlowUpSequence/PullbackSnc.lean`. Its pieces:

* the exceptional divisor of the pulled-back blow-up is the inverse image of the exceptional
  divisor, for every `h` (`exceptionalDivisor_comap`, the defining square of `blowUpMap`);
* nonvanishing on every component is preserved by flat pullback
  (`isNonzeroEverywhere_comap_of_flat`): the local homomorphisms of stalks of a flat morphism are
  faithfully flat, so a nonzero ideal extends to a nonzero ideal;
* the marked transform `𝒪(mF) · π^* I` of [Kol07, Definition 60] commutes with base change along
  the morphism of blow-ups over any `h`, in the domain `F^m ∣ π^* I` of that definition
  (`markedTransform_comap_blowUpMap_of_pow_dvd`): the identity `F^m · π_*^{-1}(I, m) = π^* I`
  pulls back, `comap` being multiplicative, and the uniqueness `eq_markedTransform_of_pow_mul_eq`
  identifies the pullback with the marked transform of the pulled-back data; iterated along a
  sequence of order `≥ m` this gives `IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom`,
  the general form of [Kol07, Lemma 62];
* the strict and total transforms along the sequence commute with flat pullback
  (`strictTransformSeq_pullback`, `totalTransformSeq_pullback`), and the empty divisor family
  pulls back to the empty one (`empty_comap`);
* the order along a center is preserved by smooth pullback (`ordAlongEq_comap_of_smooth`,
  `leOrdAlong_comap_of_smooth`): a flat morphism is generalizing (Mathlib's
  `Flat.generalizingMap`), so the generic points of `h⁻¹|Z|` map to generic points of `|Z|`, where
  `ord_comap_of_smooth` reads the order;
* along a smooth blow-up sequence of order `m` the weak transforms pull back
  (`IsOrderSeq.weakTransformSeq_pullback`): each weak transform is the marked transform with
  control `m`, and the marked transform pulls back.

The statements come in two forms: with a relative dimension `d` of `h`, and with only the
equidimensionality of the source `Y` over `k` (suffix `_of_equidim`, `_of_smooth`), the form
available when the pulled-back triple is given.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Limits Scheme IdealSheafData BlowUpSequence
  TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### The exceptional divisor and the marked transform under base change -/

/-- The exceptional divisor of the pulled-back blow-up is the inverse image of the exceptional
divisor under the morphism of blow-ups over `h`, for every `h` [Wlo05, Proposition 2.4.2,
proof]. -/
theorem exceptionalDivisor_comap (h : Y ⟶ X) (D : X.IdealSheafData) :
    (D.comap h).exceptionalDivisor = D.exceptionalDivisor.comap (Scheme.Hom.blowUpMap h D) := by
  unfold exceptionalDivisor
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    blowUpMap_π]

/-- The marked transform `𝒪(mF) · π^* I` commutes with base change along the morphism of blow-ups
over any `h : Y ⟶ X`, in the domain `F^m ∣ π^* I` of [Kol07, Definition 60]: the identity
`F^m · π_*^{-1}(I, m) = π^* I` pulls back along `blowUpMap h D` through the square `blowUpMap_π`,
and the quotient by the invertible `F_Y^m` is unique (`eq_markedTransform_of_pow_mul_eq`). This is
the general form of [Kol07, Lemma 62], which is the case of the closed immersion of a hypersurface
`H ⊇ Z`; the statement assumes no flatness of `h` and neither `Z ⊊ H` nor `I|_H ≠ 0`. -/
theorem markedTransform_comap_blowUpMap_of_pow_dvd (h : Y ⟶ X) (D I : X.IdealSheafData) (m : ℕ)
    (hd : D.exceptionalDivisor ^ m ∣ I.comap D.blowUpπ) :
    (I.comap h).markedTransform (D.comap h) m = (I.markedTransform D m).comap (Scheme.Hom.blowUpMap
        h D) := by
  symm
  apply eq_markedTransform_of_pow_mul_eq
  rw [exceptionalDivisor_comap, ← Scheme.IdealSheafData.comap_pow,
    ← Scheme.IdealSheafData.comap_mul, pow_mul_markedTransform D I m hd,
    ← Scheme.IdealSheafData.comap_comp, blowUpMap_π,
    Scheme.IdealSheafData.comap_comp]

/-! ### Nonvanishing and the order along a center under pullback -/

/-- Nonvanishing on every irreducible component ([Kol07, Notation 64 (2)]) is preserved by flat
pullback: the stalk map of a flat morphism is faithfully flat, so a nonzero ideal extends to a
nonzero ideal (`comap_stalkMap_map_eq_self`). -/
theorem isNonzeroEverywhere_comap_of_flat (h : Y ⟶ X) [Flat h] {I : X.IdealSheafData}
    (hI : IsNonzeroEverywhere I) : IsNonzeroEverywhere (I.comap h) := by
  intro y hy
  apply hI (h y)
  rw [Scheme.IdealSheafData.stalkIdeal_comap] at hy
  have hker : Ideal.comap (h.stalkMap y).hom ⊥ = ⊥ := by
    have := h.comap_stalkMap_map_eq_self y ⊥
    rwa [Ideal.map_bot] at this
  have := h.comap_stalkMap_map_eq_self y (I.stalkIdeal (h y))
  rw [hy, hker] at this
  exact this.symm

/-- A flat morphism is generalizing [Sta, Tag 01U1], so a generic point of the preimage `h⁻¹|Z|`
maps to a generic point of `|Z|`. -/
theorem mem_genericPoints_support_of_flat (h : Y ⟶ X) [Flat h] (Z : X.IdealSheafData) {η : Y}
    (hη : η ∈ (Z.comap h).support.genericPoints) : h η ∈ Z.support.genericPoints := by
  have hpre : ∀ y : Y, y ∈ (Z.comap h).support ↔ h y ∈ Z.support := fun y => by
    rw [Scheme.IdealSheafData.support_comap]
    exact Iff.rfl
  refine ⟨(hpre η).mp hη.1, ?_⟩
  intro x hx hxη
  obtain ⟨x', hx'η, rfl⟩ := Flat.generalizingMap h hxη
  rw [hη.2 ((hpre x').mpr hx) hx'η]

/-- The order along a center is preserved by smooth pullback, `ord_{Z ×_X Y}(h^* I) = ord_Z I`
("`ord_{x'}(I'_i) = ord_x(I_i)`", [Wlo05, Proposition 2.4.2, proof]; `ord_comap_of_smooth`);
vacuous when the pulled-back center is empty. -/
theorem ordAlongEq_comap_of_smooth (h : Y ⟶ X) [Smooth h] {I Z : X.IdealSheafData} {m : ℕ∞}
    (hm : I.OrdAlongEq Z.support m) : (I.comap h).OrdAlongEq (Z.comap h).support m := by
  intro η hη
  rw [Scheme.IdealSheafData.ord_comap_of_smooth]
  exact hm _ (mem_genericPoints_support_of_flat h Z hη)

/-- The `≥ m` form of `ordAlongEq_comap_of_smooth`. -/
theorem leOrdAlong_comap_of_smooth (h : Y ⟶ X) [Smooth h] {I Z : X.IdealSheafData} {m : ℕ∞}
    (hm : I.LeOrdAlong Z.support m) : (I.comap h).LeOrdAlong (Z.comap h).support m := by
  intro η hη
  rw [Scheme.IdealSheafData.ord_comap_of_smooth]
  exact hm _ (mem_genericPoints_support_of_flat h Z hη)


/-! ### The strict and total transforms under flat base change -/

/-- The colon by a principal ideal commutes with flat base change, `(I : e) S = (I S : φ(e))`
([Mat89, Theorem 7.4 (iii)], for a principal divisor). The inclusion
`⊇` is the equational criterion for flatness [Sta, Tag 00HK]: a relation
`s · φ(e) = Σ_k c_k φ(i_k)` with `i_k ∈ I` is trivial, `s = Σ_j φ(a_j) y_j` with
`e a_j + Σ_k i_k a_{kj} = 0`, so each `a_j ∈ (I : e)`. -/
theorem map_colon_singleton_of_flat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (I : Ideal R) (e : R) :
    (I.colon {e}).map (algebraMap R S) = (I.map (algebraMap R S)).colon {algebraMap R S e} := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hre : r * e ∈ I := by simpa only [smul_eq_mul] using Submodule.mem_colon_singleton.mp hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ hre
  · intro s hs
    have hs' : s * algebraMap R S e ∈ I.map (algebraMap R S) := by
      simpa only [smul_eq_mul] using Submodule.mem_colon_singleton.mp hs
    obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp
      (show s * algebraMap R S e ∈ Submodule.span S (algebraMap R S '' (I : Set R)) from hs')
    have hg' : ∀ i, ∃ a ∈ I, algebraMap R S a = (g i : S) := fun i => (g i).2
    choose a ha hφa using hg'
    have hsum : ∑ i : Fin n, algebraMap R S (a i) * -c i = -(s * algebraMap R S e) := by
      rw [← hg, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hφa, smul_eq_mul, mul_neg, mul_comm]
    have hrel : ∑ i : Fin (n + 1), (Fin.cons e a : Fin (n + 1) → R) i •
        (Fin.cons s (fun i => -c i) : Fin (n + 1) → S) i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Algebra.smul_def]
      rw [hsum, mul_comm, add_neg_cancel]
    obtain ⟨p, A, y, hxy, hfA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
    have hs_eq : s = ∑ j, A 0 j • y j := by simpa only [Fin.cons_zero] using hxy 0
    have hA0 : ∀ j, A 0 j ∈ I.colon {e} := by
      intro j
      rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
      have h0 := hfA j
      rw [Fin.sum_univ_succ, Fin.cons_zero] at h0
      simp only [Fin.cons_succ] at h0
      rw [eq_neg_of_add_eq_zero_left h0]
      exact I.neg_mem (Ideal.sum_mem _ fun i _ => I.mul_mem_right _ (ha i))
    rw [hs_eq]
    exact Ideal.sum_mem _ fun j _ => by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hA0 j))

/-- The colon by an invertible ideal sheaf commutes with flat base change: on stalks
(`stalkIdeal_colon_of_isInvertible` on both sides, `IsInvertible.comap_of_flat`) both sides are
the colon by the image `φ(e)` of a generator of the principal stalk, `map_colon_singleton_of_flat`
([Wlo05, Proposition 2.4.2, proof]). -/
theorem colon_comap_of_flat (h : Y ⟶ X) [Flat h] (J : X.IdealSheafData) {K : X.IdealSheafData}
    (hK : K.IsInvertible) : (J.colon K).comap h = (J.comap h).colon (K.comap h) := by
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro y
  obtain ⟨e, -, he⟩ := hK.exists_mem_nonZeroDivisors_stalkIdeal_eq_span (h y)
  have hφ : (h.stalkMap y).hom.Flat := Flat.stalkMap h y
  rw [Scheme.IdealSheafData.stalkIdeal_comap,
    Scheme.IdealSheafData.stalkIdeal_colon_of_isInvertible J hK,
    Scheme.IdealSheafData.stalkIdeal_colon_of_isInvertible (J.comap h) (hK.comap_of_flat h),
    Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap, he,
    Ideal.colon_span, Ideal.map_span, Set.image_singleton, Ideal.colon_span]
  algebraize [(h.stalkMap y).hom]
  exact map_colon_singleton_of_flat _ e

/-- The saturation `⋃ᵢ (J : Kⁱ)` by an invertible `K` commutes with flat base change, termwise by
`colon_comap_of_flat`. -/
theorem saturate_comap_of_flat (h : Y ⟶ X) [Flat h] (J : X.IdealSheafData) {K : X.IdealSheafData}
    (hK : K.IsInvertible) : (J.saturate K).comap h = (J.comap h).saturate (K.comap h) := by
  unfold Scheme.IdealSheafData.saturate
  rw [Scheme.IdealSheafData.comap_iSup]
  refine iSup_congr fun i => ?_
  rw [colon_comap_of_flat h J (Scheme.IdealSheafData.isInvertible_pow hK i),
    Scheme.IdealSheafData.comap_pow]

/-- The strict transform of a closed subscheme commutes with flat base change along the morphism
of blow-ups over `h` ("`E'_{i+1} = φ_{i+1}^{-1}(E_{i+1})`", [Wlo05, Proposition 2.4.2, proof];
[Kol07, Definition 65]): the strict transform is the saturation of the total transform by the
exceptional divisor, the total transform pulls back along the square `blowUpMap_π`, the
exceptional divisor by `exceptionalDivisor_comap`. -/
theorem strictTransform_comap_of_flat (h : Y ⟶ X) [Flat h] (D J : X.IdealSheafData) :
    (J.comap h).strictTransform (D.comap h) = (J.strictTransform D).comap (Scheme.Hom.blowUpMap h
        D) := by
  have hF : D.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π D
  have hflat : Flat (Scheme.Hom.blowUpMap h D) :=
    property_of_isPullback _ (isPullback_blowUpMap h D)
      inferInstance
  unfold strictTransform strictTransformAlong
  rw [saturate_comap_of_flat (Scheme.Hom.blowUpMap h D) _ hF, ← exceptionalDivisor_comap,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    blowUpMap_π]

/-- The total transform of a divisor family [Kol07, Definition 65] commutes with flat base change:
componentwise, strict transforms to strict transforms and the exceptional divisor to the
exceptional divisor. -/
theorem totalTransform_comap_of_flat (h : Y ⟶ X) [Flat h] (D : X.IdealSheafData)
    (E : DivisorFamily X) :
    (E.comap h).totalTransform (D.comap h) = (E.totalTransform D).comap (Scheme.Hom.blowUpMap h
        D) := by
  unfold DivisorFamily.totalTransform DivisorFamily.comap
  congr 1
  funext i
  dsimp only
  cases ofLex i with
  | inl j => exact strictTransform_comap_of_flat h D (E.component j)
  | inr u => exact exceptionalDivisor_comap h D

/-- `totalTransformSeq_pullback` in the `⟨j, hj⟩` form of the indices: by induction on the
sequence, `totalTransform_comap_of_flat` at the head and the inductive hypothesis for the tail
along `blowUpMap h D`. -/
theorem totalTransformSeq_pullback_mk (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (E : DivisorFamily X) (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback h).totalTransformSeq (E.comap h) (S.pullbackStageIdx h ⟨j, hj⟩) =
      (S.totalTransformSeq E ⟨j, hj⟩).comap (S.pullbackStageHom h ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hflat : Flat (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      have := ih (Scheme.Hom.blowUpMap h D) (E.totalTransform D) j (Nat.lt_of_succ_lt_succ hj)
      rw [← totalTransform_comap_of_flat] at this
      exact this

/-- Along a flat pullback the induced divisor families of `h^* B` for `h^{-1} E` are the inverse
images of those of `B` for `E` under the stage lifts: "the divisors in `E'_i` are the inverse
images of the divisors in `E_i`" [Wlo05, Proposition 2.4.2 (2)]. -/
theorem totalTransformSeq_pullback (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (E : DivisorFamily X) (i : Fin (S.length + 1)) :
    (S.pullback h).totalTransformSeq (E.comap h) (S.pullbackStageIdx h i) =
      (S.totalTransformSeq E i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact totalTransformSeq_pullback_mk S h E j hj

/-- The inverse image of the empty divisor family is the empty divisor family (used where the
divisorial part `E` of a triple is ignored, as in [Kol07, Definition 78]). -/
theorem empty_comap (h : Y ⟶ X) : (DivisorFamily.empty X).comap h = DivisorFamily.empty Y := by
  unfold DivisorFamily.comap DivisorFamily.empty
  congr 1
  funext i
  exact i.elim

/-- `strictTransformSeq_pullback` in the `⟨j, hj⟩` form of the indices: along a flat `h` the
strict transform of `h⁻¹(Y)` along the pulled-back sequence is the inverse image under the stage
lift of the strict transform of `Y`, by induction on the sequence, `strictTransform_comap_of_flat`
at the head and the inductive hypothesis for the tail along `blowUpMap h D`, exactly as
`totalTransformSeq_pullback_mk`. -/
theorem strictTransformSeq_pullback_mk (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (J : X.IdealSheafData) (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback h).strictTransformSeq (J.comap h) (S.pullbackStageIdx h ⟨j, hj⟩) =
      (S.strictTransformSeq J ⟨j, hj⟩).comap (S.pullbackStageHom h ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hflat : Flat (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      have := ih (Scheme.Hom.blowUpMap h D) (J.strictTransform D) j (Nat.lt_of_succ_lt_succ hj)
      rw [← strictTransform_comap_of_flat] at this
      exact this

/-- Along a flat pullback the strict transform of the inverse image of a closed subscheme along
the pulled-back sequence is the inverse image, under the stage lift, of its strict transform along
the original sequence ([Kol07, 30.2 and 34.1]); used for the locality of maximal contact. -/
theorem strictTransformSeq_pullback (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (J : X.IdealSheafData) (i : Fin (S.length + 1)) :
    (S.pullback h).strictTransformSeq (J.comap h) (S.pullbackStageIdx h i) =
      (S.strictTransformSeq J i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact strictTransformSeq_pullback_mk S h J j hj

/-- `strictTransformSeq_pullback` at the stage of the `i`-th center, indexed through
`pullbackCenterIdx` as `center_pullback` is (the two index transports agree definitionally). -/
theorem strictTransformSeq_pullback_castSucc (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (J : X.IdealSheafData) (i : Fin S.length) :
    (S.pullback h).strictTransformSeq (J.comap h) (S.pullbackCenterIdx h i).castSucc =
      (S.strictTransformSeq J i.castSucc).comap (S.pullbackStageHom h i.castSucc) :=
  strictTransformSeq_pullback S h J i.castSucc

/-! ### The induced data of a smooth blow-up sequence under smooth pullback -/

section OrderAlong

variable {k : Type u} [Field k]


/-- The weak transform commutes with base change along a smooth `h` whose source is
equidimensional over `k` (`h ≫ f` smooth of some relative dimension `n'`); no relative dimension
of `h` is needed, as the argument uses `d` only through `d + n`. -/
theorem weakTransform_comap_of_orderAlong_of_equidim [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Smooth h] (n' : ℕ)
    [SmoothOfRelativeDimension n' (h ≫ f)] (D I : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)]
    {m : ℕ} (hm : I.OrdAlongEq D.support (m : ℕ∞)) :
    (I.comap h).weakTransform (D.comap h) = (I.weakTransform D).comap (Scheme.Hom.blowUpMap h
        D) := by
  have hZ : Smooth ((D.comap h).subschemeι ≫ h ≫ f) := smooth_subschemeι_comap_comp D h f
  rw [weakTransform_eq_markedTransform_of_smooth f n D I hm,
    weakTransform_eq_markedTransform_of_smooth (h ≫ f) n' (D.comap h) (I.comap h)
      (ordAlongEq_comap_of_smooth h hm)]
  exact markedTransform_comap_blowUpMap_of_pow_dvd h D I m
    (pow_dvd_comap_of_leOrdAlong f n D I fun η hη => (hm η hη).ge)

/-- In the setting of [Kol07, Definition 66] (ambient scheme smooth and equidimensional over `k`
of characteristic zero, smooth center `Z`, `ord_Z I = m` along every component of `Z`) the weak
transform commutes with base change along the morphism of blow-ups over a smooth `h`
([Wlo05, Proposition 2.4.2, proof]; compare the birational transform of [Kol07, 58] with the
marked transform of [Kol07, Definition 60]): both sides are the marked transform with control `m`
(`weakTransform_eq_markedTransform_of_smooth`; the order is preserved by
`ordAlongEq_comap_of_smooth`, the pulled-back center is smooth over `k` by
`smooth_subschemeι_comap_comp`), and the marked transform pulls back in the domain of Definition
60 (`markedTransform_comap_blowUpMap_of_pow_dvd`, the divisibility `F^m ∣ π^* I` from
`pow_dvd_comap_of_leOrdAlong`). -/
theorem weakTransform_comap_of_orderAlong [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    (D I : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)] {m : ℕ}
    (hm : I.OrdAlongEq D.support (m : ℕ∞)) :
    (I.comap h).weakTransform (D.comap h) = (I.weakTransform D).comap (Scheme.Hom.blowUpMap h
        D) := by
  have hs : Smooth h := SmoothOfRelativeDimension.smooth d h
  have hfd : SmoothOfRelativeDimension (d + n) (h ≫ f) := smoothOfRelativeDimension_comp d n h f
  exact weakTransform_comap_of_orderAlong_of_equidim f n h (d + n) D I hm


/-- The `⟨j, hj⟩` form for a smooth `h` with equidimensional source: the induction of
`IsOrderSeq.weakTransformSeq_pullback_mk` carries the relative dimension `n'` of `h ≫ f`
unchanged, since the blow-up of the source along a smooth center is again of relative dimension
`n'` over `k` (`smoothOfRelativeDimension_blowUpπ_comp_of_smooth`), and the morphism of blow-ups
is smooth by base change. -/
theorem IsOrderSeq.weakTransformSeq_pullback_mk_of_equidim [CharZero k] (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Smooth h] (n' : ℕ)
    [SmoothOfRelativeDimension n' (h ≫ f)] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback h).weakTransformSeq (I.comap h) (S.pullbackStageIdx h ⟨j, hj⟩) =
      (S.weakTransformSeq I ⟨j, hj⟩).comap (S.pullbackStageHom h ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 hS
      have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have hsm : Smooth (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      have hZ : Smooth ((D.comap h).subschemeι ≫ h ≫ f) := smooth_subschemeι_comap_comp D h f
      have hsq : Scheme.Hom.blowUpMap h D ≫ D.blowUpπ ≫ f = (D.comap h).blowUpπ ≫ h ≫ f := by
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ f) (blowUpMap_π h D)
      have hπ' : SmoothOfRelativeDimension n' (Scheme.Hom.blowUpMap h D ≫ D.blowUpπ ≫ f)
          := by
        rw [hsq]
        exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth (h ≫ f) n' (D.comap h)
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap h D) ht j
          (Nat.lt_of_succ_lt_succ hj)
      rw [← weakTransform_comap_of_orderAlong_of_equidim f n h n' D I hm] at this
      exact this

/-- `IsOrderSeq.weakTransformSeq_pullback` in the `⟨j, hj⟩` form: by induction on the sequence,
peeling one blow-up with `isOrderSeq_cons_iff`; the blown-up stage is again smooth of relative
dimension `n` (`smoothOfRelativeDimension_blowUpπ_comp_of_smooth`) and the morphism of blow-ups
is again smooth of relative dimension `d` (base change). -/
theorem IsOrderSeq.weakTransformSeq_pullback_mk [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
    (hS : S.IsOrderSeq f I E m) (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback h).weakTransformSeq (I.comap h) (S.pullbackStageIdx h ⟨j, hj⟩) =
      (S.weakTransformSeq I ⟨j, hj⟩).comap (S.pullbackStageHom h ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 hS
      have hs : Smooth h := SmoothOfRelativeDimension.smooth d h
      have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have := smoothOfRelativeDimension_isStableUnderBaseChange d
      have hd : SmoothOfRelativeDimension d (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap h D) ht j
          (Nat.lt_of_succ_lt_succ hj)
      rw [← weakTransform_comap_of_orderAlong f n h (d := d) D I hm] at this
      exact this


/-- `IsOrderSeq.weakTransformSeq_pullback` for a smooth `h` with equidimensional source. -/
theorem IsOrderSeq.weakTransformSeq_pullback_of_equidim [CharZero k] (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Smooth h] (n' : ℕ)
    [SmoothOfRelativeDimension n' (h ≫ f)] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) (i : Fin (S.length + 1)) :
    (S.pullback h).weakTransformSeq (I.comap h) (S.pullbackStageIdx h i) =
      (S.weakTransformSeq I i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderSeq.weakTransformSeq_pullback_mk_of_equidim f n h n' hS j hj

/-- Along a smooth pullback of a smooth blow-up sequence of order `m` for `(X, I, E)`, the induced
ideals of `h^* B` for `h^* I` are the pullbacks of the induced ideals of `B` under the stage lifts:
"`I'_i = φ_i^*(I_i)`" [Wlo05, Proposition 2.4.2 (2)], for the unmarked transforms of
[Kol07, Definition 66]. -/
theorem IsOrderSeq.weakTransformSeq_pullback [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
    (hS : S.IsOrderSeq f I E m) (i : Fin (S.length + 1)) :
    (S.pullback h).weakTransformSeq (I.comap h) (S.pullbackStageIdx h i) =
      (S.weakTransformSeq I i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderSeq.weakTransformSeq_pullback_mk f n h (d := d) hS j hj


/-- Along a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` the induced marked ideals of
`h^* B` for `(h^* I, m)` are the pullbacks of those of `B` for `(I, m)` along the stage lifts, for
every `h : Y ⟶ X` (the iterated form of [Kol07, Lemma 62], without any hypothesis on `h`), in the
`⟨j, hj⟩` form: by induction on the sequence with `isOrderGeSeq_cons_iff`,
`markedTransform_comap_blowUpMap_of_pow_dvd` at each stage (the order clause `ord_Z I ≥ m` gives
`F^m ∣ π^* I`, `pow_dvd_comap_of_leOrdAlong`). -/
theorem IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk [CharZero k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] (h : Y ⟶ X)
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
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap h D) ht j
          (Nat.lt_of_succ_lt_succ hj)
      rw [← markedTransform_comap_blowUpMap_of_pow_dvd h D I m
        (pow_dvd_comap_of_leOrdAlong f n D I hm)] at this
      exact this

/-- The `Fin` form of `IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk`, for every
`h : Y ⟶ X` (the iterated form of [Kol07, Lemma 62]). -/
theorem IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom [CharZero k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] (h : Y ⟶ X)
    {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (hS : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    (S.pullback h).markedTransformSeq (I.comap h) m (S.pullbackStageIdx h i) =
      (S.markedTransformSeq I m i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk f n h hS j hj

/-- `IsOrderGeSeq.markedTransformSeq_pullback` in the `⟨j, hj⟩` form: by induction on the sequence
with `isOrderGeSeq_cons_iff`, `markedTransform_comap_blowUpMap_of_pow_dvd` at each stage (the order
clause
`ord_Z I ≥ m` gives `F^m ∣ π^* I`). -/
theorem IsOrderGeSeq.markedTransformSeq_pullback_mk [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
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
      have hs : Smooth h := SmoothOfRelativeDimension.smooth d h
      have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have := smoothOfRelativeDimension_isStableUnderBaseChange d
      have hd : SmoothOfRelativeDimension d (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap h D) ht j
          (Nat.lt_of_succ_lt_succ hj)
      rw [← markedTransform_comap_blowUpMap_of_pow_dvd h D I m
        (pow_dvd_comap_of_leOrdAlong f n D I hm)]
        at this
      exact this


/-- `IsOrderGeSeq.markedTransformSeq_pullback` for any smooth `h`, no relative dimension
needed. -/
theorem IsOrderGeSeq.markedTransformSeq_pullback_of_smooth [CharZero k] (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (h : Y ⟶ X)
    {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (hS : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    (S.pullback h).markedTransformSeq (I.comap h) m (S.pullbackStageIdx h i) =
      (S.markedTransformSeq I m i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk f n h hS j hj

/-- Along a smooth pullback of a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` the
induced marked ideals of `h^* B` for `(h^* I, m)` (the transforms of [Kol07, Warning 63 (2)]) are
the pullbacks of those of `B` for `(I, m)` [Wlo05, Proposition 2.4.2 (2)]. -/
theorem IsOrderGeSeq.markedTransformSeq_pullback [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (hS : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    (S.pullback h).markedTransformSeq (I.comap h) m (S.pullbackStageIdx h i) =
      (S.markedTransformSeq I m i).comap (S.pullbackStageHom h i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderGeSeq.markedTransformSeq_pullback_mk f n h (d := d) hS j hj


/-- The induced triple of `h^* B`, for a smooth `h` with equidimensional source. -/
theorem IsOrderSeq.inducedTriple_pullback_of_equidim [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) [Smooth h] (n' : ℕ)
    [SmoothOfRelativeDimension n' (h ≫ f)] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) :
    (S.pullback h).weakTransformSeq (I.comap h) (S.pullbackStageIdx h (Fin.last _)) =
        (S.weakTransformSeq I (Fin.last _)).comap (S.pullbackStageHom h (Fin.last _)) ∧
      (S.pullback h).totalTransformSeq (E.comap h) (S.pullbackStageIdx h (Fin.last _)) =
        (S.totalTransformSeq E (Fin.last _)).comap (S.pullbackStageHom h (Fin.last _)) :=
  ⟨IsOrderSeq.weakTransformSeq_pullback_of_equidim f n h n' hS _,
    totalTransformSeq_pullback S h E _⟩

/-- For a smooth blow-up sequence of order `m`, the induced triple `Π_*^{-1}(X, I, E)` at the end
of the sequence ([Kol07, Definition 66]) of `h^* B` for `(Y, h^* I, h^{-1} E)` is the pullback of
the induced triple of `B` under the last stage lift [Wlo05, Proposition 2.4.2 (2)]. -/
theorem IsOrderSeq.inducedTriple_pullback [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (h : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d h]
    {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
    (hS : S.IsOrderSeq f I E m) :
    (S.pullback h).weakTransformSeq (I.comap h) (S.pullbackStageIdx h (Fin.last _)) =
        (S.weakTransformSeq I (Fin.last _)).comap (S.pullbackStageHom h (Fin.last _)) ∧
      (S.pullback h).totalTransformSeq (E.comap h) (S.pullbackStageIdx h (Fin.last _)) =
        (S.totalTransformSeq E (Fin.last _)).comap (S.pullbackStageHom h (Fin.last _)) := by
  have hs : Smooth h := SmoothOfRelativeDimension.smooth d h
  exact ⟨IsOrderSeq.weakTransformSeq_pullback f n h (d := d) hS _,
    totalTransformSeq_pullback S h E _⟩

end OrderAlong

end AlgebraicGeometry
