/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Transform.Reduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Exceptional
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The strict transform of an integral closed subscheme stays integral off the centers

In the proof of [Kol07, Corollary 22] the resolution of a variety is read off a principalization
of its ideal sheaf in an ambient smooth variety: there is a unique `j` such that
`π_0 ⋯ π_{j−1} : P_j → P` "is a local isomorphism around `η_X`", and then `η_X` is the generic
point of the center `Z_j`. This module supplies the general facts behind that sentence. For a
closed subscheme `V(J)` with `V(J)` integral and a center `D` not containing it (`¬ D ≤ J`):

* the generic point `η` of `V(J)` lies off the center, so the blow-up `π` is an isomorphism near it
  (`blowUp.isIso_π_restrict_compl_support`): exactly one point `η'` of the blow-up lies over `η`,
  and specializations between points off the exceptional divisor are reflected by `π`;
* the strict transform `V(Jˢ)` has support `closure (π⁻¹(V(J)) ∖ π⁻¹(V(D)))`
  (`coe_support_saturate`; this is the strict transform of [Hau14, Definition 6.2]), which is
  `closure {η'}`: `η'` is its generic point;
* `V(Jˢ)` is reduced (`Hironaka/Scheme/BlowUp/Transform/Reduced.lean`), hence integral.

Along a blow-up sequence the same holds at every stage `i` no earlier center of which contains the
strict transform, by structural recursion on the sequence: the strict transform `X̄_i` is
integral, its generic point `η_i` is the unique point of the stage over `η`, and `Π_i η_i = η`,
which is Kollár's "`π_0 ⋯ π_{j−1}` is a local isomorphism around `η_X`" read on the fibre. The
resolution functor of [Kol07, Theorem 36] uses this to locate its end result over the generic
point.

## Conventions

`D.blowUp`, `D.blowUpπ` and `strictTransform D J` are the definitions used in the statements of
the main theorems, definitionally
`AlgebraicGeometry.Scheme.IdealSheafData.blowUp D`, `IdealSheafData.blowUpπ D` and
`strictTransformAlong (IdealSheafData.blowUpπ D) (D.comap (IdealSheafData.blowUpπ D)) J`.
Containment of a center in the strict transform is the ideal inequality `S.center i ≤
S.strictTransformSeq J i.castSucc` (the stop rule `CenterContains` of
`Hironaka/Resolution/Algebraic/Kol07/Thm36/Affine.lean`); "no center before `i` contains the strict
transform" is the hypothesis `∀ m (hm : m < i), ¬ S.center ⟨m, _⟩ ≤ S.strictTransformSeq J ⟨m, _⟩`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence IdealSheafData

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### One blow-up: the fibre over a point off the center, and specializations -/

section OneStep

variable (D : X.IdealSheafData)

/-- A point of `X` lies in the open complement of the center iff it is not in its support. -/
theorem mem_compl_support_iff (x : X) : x ∈ (D.support.compl : X.Opens) ↔ x ∉ D.support :=
  Iff.rfl

/-- The blow-up reflects specializations between points lying off the exceptional divisor (`π` is
an isomorphism over the complement of the center). -/
theorem specializes_of_π_specializes {y y' : IdealSheafData.blowUp D}
    (hy : IdealSheafData.blowUpπ D y ∉ D.support)
    (hy' : IdealSheafData.blowUpπ D y' ∉ D.support) (h : IdealSheafData.blowUpπ D y ⤳
        IdealSheafData.blowUpπ D y') : y ⤳ y' := by
  set W : X.Opens := D.support.compl with hW
  have := blowUp.isIso_π_restrict_compl_support D
  have hyW : y ∈ IdealSheafData.blowUpπ D ⁻¹ᵁ W := hy
  have hy'W : y' ∈ IdealSheafData.blowUpπ D ⁻¹ᵁ W := hy'
  set φ := (IdealSheafData.blowUpπ D ∣_ W).homeomorph with hφ
  have h1 : φ ⟨y, hyW⟩ = ⟨IdealSheafData.blowUpπ D y, hy⟩ :=
    Subtype.ext (morphismRestrict_base_coe (IdealSheafData.blowUpπ D) W ⟨y, hyW⟩)
  have h2 : φ ⟨y', hy'W⟩ = ⟨IdealSheafData.blowUpπ D y', hy'⟩ :=
    Subtype.ext (morphismRestrict_base_coe (IdealSheafData.blowUpπ D) W ⟨y', hy'W⟩)
  have e1 : φ.symm ⟨IdealSheafData.blowUpπ D y, hy⟩ = ⟨y, hyW⟩ := φ.symm_apply_eq.mpr h1.symm
  have e2 : φ.symm ⟨IdealSheafData.blowUpπ D y', hy'⟩ = ⟨y', hy'W⟩ := φ.symm_apply_eq.mpr h2.symm
  have hsub : (⟨IdealSheafData.blowUpπ D y, hy⟩ : W) ⤳ ⟨IdealSheafData.blowUpπ D y', hy'⟩ :=
    (subtype_specializes_iff _ _).mpr h
  have hmap := hsub.map φ.symm.continuous
  rw [e1, e2] at hmap
  exact (subtype_specializes_iff _ _).mp hmap

/-- The blow-up is injective on the points lying off the exceptional divisor. -/
theorem π_eq_of_notMem_support {y y' : IdealSheafData.blowUp D}
    (hy : IdealSheafData.blowUpπ D y ∉ D.support)
    (h : IdealSheafData.blowUpπ D y = IdealSheafData.blowUpπ D y') : y = y' := by
  have hy' : IdealSheafData.blowUpπ D y' ∉ D.support := h ▸ hy
  have h1 : y ⤳ y' := specializes_of_π_specializes D hy hy' (by rw [h])
  have h2 : y' ⤳ y := specializes_of_π_specializes D hy' hy (by rw [h])
  exact (h1.antisymm h2).eq

/-! ### One blow-up: the generic point of the strict transform -/

/-- The generic point of an irreducible closed subscheme `V(J)` not contained in `V(D)` lies off
the center: otherwise `V(J) = closure {η} ⊆ V(D)`. -/
theorem genericPoint_notMem_support_of_not_subset (J : X.IdealSheafData) {η : X}
    (hη : IsGenericPoint η (J.support : Set X))
    (hnot : ¬ (J.support : Set X) ⊆ D.support) : η ∉ D.support := by
  intro hηD
  apply hnot
  rw [← hη.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hηD) D.support.isClosed

/-- The one-blow-up case of "`η_X` is the generic point of `Z_j`" in the proof of
[Kol07, Corollary 22]: the unique point `η'` over the generic point `η` of `V(J)` (off the center)
is the generic point of the strict transform of `V(J)`. Its support is
`closure (π⁻¹(V(J)) ∖ π⁻¹(V(D)))` (`coe_support_saturate`), every point of which is a
specialization of `η'` since `π` reflects specializations off the exceptional divisor. -/
theorem isGenericPoint_strictTransform [IsLocallyNoetherian X] (J : X.IdealSheafData) {η : X}
    (hη : IsGenericPoint η (J.support : Set X)) (hηD : η ∉ D.support) {η' : IdealSheafData.blowUp D}
    (hη' : IdealSheafData.blowUpπ D η' = η) :
    IsGenericPoint η' ((J.strictTransform D).support : Set (IdealSheafData.blowUp D)) := by
  have hLN : IsLocallyNoetherian (IdealSheafData.blowUp D) := blowUp.isLocallyNoetherian D
  set π := IdealSheafData.blowUpπ D with hπ
  have hsupp : ((J.strictTransform D).support : Set (IdealSheafData.blowUp D)) =
      closure (((J.comap π).support : Set (IdealSheafData.blowUp D)) \ ((D.comap π).support : Set
          (IdealSheafData.blowUp D))) :=
    coe_support_saturate (J.comap π) (D.comap π)
  have hmemJ : ∀ y : IdealSheafData.blowUp D, y ∈ (J.comap π).support ↔ π y ∈ J.support := fun y =>
    mem_support_comap_iff_apply J π y
  have hmemD : ∀ y : IdealSheafData.blowUp D, y ∈ (D.comap π).support ↔ π y ∈ D.support := fun y =>
    mem_support_comap_iff_apply D π y
  rw [isGenericPoint_def, hsupp]
  apply le_antisymm
  · -- `closure {η'} ⊆ closure T'`: `η' ∈ T'`
    apply closure_mono
    rw [Set.singleton_subset_iff]
    refine ⟨(hmemJ η').mpr ?_, fun hmem => hηD ?_⟩
    · rw [hη']; exact hη.mem
    · rw [← hη']; exact (hmemD η').mp hmem
  · -- `closure T' ⊆ closure {η'}`: every point of `T'` is a specialization of `η'`
    refine closure_minimal (fun y hy => ?_) isClosed_closure
    rw [← specializes_iff_mem_closure]
    have hyJ : π y ∈ J.support := (hmemJ y).mp hy.1
    have hyD : π y ∉ D.support := fun h => hy.2 ((hmemD y).mpr h)
    have hηy : η ⤳ π y := hη.specializes hyJ
    exact specializes_of_π_specializes D (hη' ▸ hηD) hyD (hη' ▸ hηy)

/-- The strict transform of an irreducible closed subscheme not contained in the center is
irreducible (its support has the generic point `η'`). -/
theorem irreducibleSpace_strictTransform_subscheme [IsLocallyNoetherian X] (J : X.IdealSheafData)
    {η : X} (hη : IsGenericPoint η (J.support : Set X)) (hηD : η ∉ D.support) :
    IrreducibleSpace (J.strictTransform D).subscheme := by
  obtain ⟨η', hη'⟩ := exists_π_eq_of_notMem_support D hηD
  exact irreducibleSpace_subscheme_of_isGenericPoint _
    (isGenericPoint_strictTransform D J hη hηD hη')

/-! ### One blow-up: integrality -/

/-- For a reduced closed subscheme `V(J)`, containment of the supports `V(J) ⊆ V(D)` is the ideal
inequality `D ≤ J` (`vanishingIdeal_support = radical`, and `J` is radical). -/
theorem le_of_support_subset (J : X.IdealSheafData) [IsReduced J.subscheme]
    (h : (J.support : Set X) ⊆ D.support) : D ≤ J := by
  have h1 : J.support ≤ D.support := h
  rw [le_support_iff_le_vanishingIdeal, vanishingIdeal_support,
    radical_eq_self_of_isReduced_subscheme J] at h1
  exact h1

/-- The generic point of an integral closed subscheme `V(J)` (as a point of `X`): the image of the
generic point of the scheme `V(J)`. -/
theorem exists_isGenericPoint_support (J : X.IdealSheafData) [IsIntegral J.subscheme] :
    ∃ η : X, IsGenericPoint η (J.support : Set X) := by
  refine ⟨J.subschemeι (genericPoint J.subscheme), ?_⟩
  rw [isGenericPoint_def, ← J.range_subschemeι, ← Set.image_singleton,
    (Scheme.Hom.isClosedEmbedding J.subschemeι).closure_image_eq, genericPoint_closure,
    Set.image_univ]

/-- The strict transform of an integral closed subscheme `V(J)` along a blow-up whose center does
not contain it (`¬ D ≤ J`) is integral: irreducible by `isGenericPoint_strictTransform` and reduced
by `isReduced_strictTransform_subscheme`. -/
theorem isIntegral_strictTransform_subscheme [IsLocallyNoetherian X] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (hnot : ¬ D ≤ J) : IsIntegral (J.strictTransform D).subscheme := by
  obtain ⟨η, hη⟩ := exists_isGenericPoint_support J
  have hηD : η ∉ D.support :=
    genericPoint_notMem_support_of_not_subset D J hη fun h => hnot (le_of_support_subset D J h)
  have := irreducibleSpace_strictTransform_subscheme D J hη hηD
  have := isReduced_strictTransform_subscheme D J
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end OneStep

/-! ### Along a blow-up sequence -/

section Sequence

/-- Every stage of a blow-up sequence on a locally Noetherian scheme is locally Noetherian
(`blowUp.isLocallyNoetherian` at each step). -/
theorem isLocallyNoetherian_stage :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (S : BlowUpSequence X) (i : Fin (S.length + 1)),
      IsLocallyNoetherian (S.stage i)
  | _, h, .nil _, _ => h
  | _, h, .cons _ _ _, ⟨0, _⟩ => h
  | _, _, .cons X D rest, ⟨j + 1, hj⟩ =>
    have := blowUp.isLocallyNoetherian D
    isLocallyNoetherian_stage rest ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- The strict transform of an integral closed subscheme along a blow-up sequence stays integral at
every stage `n` such that no earlier center contains the strict transform (in the `⟨n, hn⟩` form
of the indices; structural recursion on the sequence). -/
theorem isIntegral_strictTransformSeq_mk (hX : IsLocallyNoetherian X) (S : BlowUpSequence X)
    (J : X.IdealSheafData) (hJ : IsIntegral J.subscheme) (n : ℕ) (hn : n < S.length + 1)
    (h : ∀ m (hm : m < n),
      ¬ S.center ⟨m, by omega⟩ ≤ S.strictTransformSeq J ⟨m, by omega⟩) :
    IsIntegral (S.strictTransformSeq J ⟨n, hn⟩).subscheme := by
  induction S generalizing n with
  | nil X =>
    have h0 : (nil X).length = 0 := rfl
    obtain rfl : n = 0 := by omega
    exact hJ
  | cons X D rest ih =>
    cases n with
    | zero => exact hJ
    | succ n =>
      have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
      have hnot : ¬ D ≤ J := h 0 (Nat.succ_pos n)
      have hint : IsIntegral (J.strictTransform D).subscheme :=
        isIntegral_strictTransform_subscheme D J hnot
      exact ih hLN (J.strictTransform D) hint n (Nat.lt_of_succ_lt_succ hn)
        fun m hm => h (m + 1) (Nat.succ_lt_succ hm)

/-- `isIntegral_strictTransformSeq_mk` in the `Fin` form of the indices: the strict transform of an
integral closed subscheme is integral at every stage `i` no earlier center of which contains the
strict transform. -/
theorem isIntegral_strictTransformSeq [hX : IsLocallyNoetherian X] (S : BlowUpSequence X)
    (J : X.IdealSheafData) [hJ : IsIntegral J.subscheme] (i : Fin (S.length + 1))
    (h : ∀ m : Fin S.length, m.val < i.val → ¬ S.center m ≤ S.strictTransformSeq J m.castSucc) :
    IsIntegral (S.strictTransformSeq J i).subscheme := by
  obtain ⟨n, hn⟩ := i
  exact isIntegral_strictTransformSeq_mk hX S J hJ n hn fun m hm => h ⟨m, by omega⟩ hm

/-- Along a sequence (the proof of [Kol07, Corollary 22]): if no center before stage `n` contains
the strict transform of the integral `V(J)`, the strict transform at stage `n` has a generic point
`η_n`, which is the unique point of the stage over the generic point `η` of `V(J)` (the stage map
`Π_n` is a local isomorphism around `η`). -/
theorem exists_isGenericPoint_strictTransformSeq_mk (hX : IsLocallyNoetherian X)
    (S : BlowUpSequence X) (J : X.IdealSheafData) {η : X}
    (hη : IsGenericPoint η (J.support : Set X)) (hJ : IsReduced J.subscheme) (n : ℕ)
    (hn : n < S.length + 1)
    (h : ∀ m (hm : m < n),
      ¬ S.center ⟨m, by omega⟩ ≤ S.strictTransformSeq J ⟨m, by omega⟩) :
    ∃ η' : S.stage ⟨n, hn⟩,
      IsGenericPoint η' ((S.strictTransformSeq J ⟨n, hn⟩).support : Set (S.stage ⟨n, hn⟩)) ∧
        S.stageMap ⟨n, hn⟩ η' = η ∧ ∀ y, S.stageMap ⟨n, hn⟩ y = η → y = η' := by
  induction S generalizing n with
  | nil X =>
    have h0 : (nil X).length = 0 := rfl
    obtain rfl : n = 0 := by omega
    exact ⟨η, hη, rfl, fun y hy => hy⟩
  | cons X D rest ih =>
    cases n with
    | zero => exact ⟨η, hη, rfl, fun y hy => hy⟩
    | succ n =>
      have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
      have hnot : ¬ D ≤ J := h 0 (Nat.succ_pos n)
      have hηD : η ∉ D.support :=
        genericPoint_notMem_support_of_not_subset D J hη fun hs =>
          hnot (le_of_support_subset D J hs)
      obtain ⟨η₁, hη₁, huniq⟩ :=
        blowUp.existsUnique_preimage_of_notMem_support D hηD
      have hgen₁ : IsGenericPoint η₁ ((J.strictTransform D).support : Set
          D.blowUp) :=
        isGenericPoint_strictTransform D J hη hηD hη₁
      have hred : IsReduced (J.strictTransform D).subscheme :=
        isReduced_strictTransform_subscheme D J
      obtain ⟨η', hgen', hmap', huniq'⟩ := ih hLN (J.strictTransform D) hgen₁ hred n
        (Nat.lt_of_succ_lt_succ hn) fun m hm => h (m + 1) (Nat.succ_lt_succ hm)
      refine ⟨η', hgen', ?_, fun y hy => ?_⟩
      · change IdealSheafData.blowUpπ D (rest.stageMap ⟨n, Nat.lt_of_succ_lt_succ hn⟩ η') = η
        rw [hmap', hη₁]
      · change IdealSheafData.blowUpπ D (rest.stageMap ⟨n, Nat.lt_of_succ_lt_succ hn⟩ y) = η at hy
        exact huniq' y (huniq _ hy)

/-- `exists_isGenericPoint_strictTransformSeq_mk` in the `Fin` form of the indices. -/
theorem exists_isGenericPoint_strictTransformSeq [hX : IsLocallyNoetherian X]
    (S : BlowUpSequence X) (J : X.IdealSheafData) {η : X}
    (hη : IsGenericPoint η (J.support : Set X)) [hJ : IsReduced J.subscheme]
    (i : Fin (S.length + 1))
    (h : ∀ m : Fin S.length, m.val < i.val → ¬ S.center m ≤ S.strictTransformSeq J m.castSucc) :
    ∃ η' : S.stage i, IsGenericPoint η' ((S.strictTransformSeq J i).support : Set (S.stage i)) ∧
      S.stageMap i η' = η ∧ ∀ y, S.stageMap i y = η → y = η' := by
  obtain ⟨n, hn⟩ := i
  exact exists_isGenericPoint_strictTransformSeq_mk hX S J hη hJ n hn
    fun m hm => h ⟨m, by omega⟩ hm

/-- "`π_0 ⋯ π_{j−1}` is a local isomorphism around `η_X`" (the proof of [Kol07, Corollary 22]), in
the form the resolution functor uses: if no center up to stage `m` contains the strict transform
of the integral `V(J)`, no point of the `m`-th center lies over the generic point `η` of `V(J)`.
The only point of stage `m` over `η` is the generic point `η_m` of the strict transform `X̄_m`,
and `η_m ∉ Z_m` since `Z_m` does not contain the irreducible reduced `X̄_m`. -/
theorem notMem_center_support_of_stageMap_eq_mk (hX : IsLocallyNoetherian X)
    (S : BlowUpSequence X) (J : X.IdealSheafData) (hJ : IsIntegral J.subscheme) {η : X}
    (hη : IsGenericPoint η (J.support : Set X)) (m : ℕ) (hm : m < S.length)
    (h : ∀ m' (hm' : m' ≤ m),
      ¬ S.center ⟨m', by omega⟩ ≤ S.strictTransformSeq J ⟨m', by omega⟩)
    (y : S.stage ⟨m, Nat.lt_succ_of_lt hm⟩) (hy : S.stageMap ⟨m, Nat.lt_succ_of_lt hm⟩ y = η) :
    y ∉ (S.center ⟨m, hm⟩).support := by
  have hred : IsReduced J.subscheme := by
    have := hJ
    infer_instance
  obtain ⟨η', hgen, -, huniq⟩ := exists_isGenericPoint_strictTransformSeq_mk hX S J hη hred m
    (Nat.lt_succ_of_lt hm) fun m' hm' => h m' hm'.le
  have hint : IsIntegral (S.strictTransformSeq J ⟨m, Nat.lt_succ_of_lt hm⟩).subscheme :=
    isIntegral_strictTransformSeq_mk hX S J hJ m (Nat.lt_succ_of_lt hm) fun m' hm' => h m' hm'.le
  obtain rfl : y = η' := huniq y hy
  intro hmem
  apply h m le_rfl
  refine le_of_support_subset _ _ ?_
  rw [← hgen.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hmem) (S.center ⟨m, hm⟩).support.isClosed

/-- `notMem_center_support_of_stageMap_eq_mk` in the `Fin` form of the indices: no restricted
center over the generic point before the first containing center. -/
theorem notMem_center_support_of_stageMap_eq [hX : IsLocallyNoetherian X] (S : BlowUpSequence X)
    (J : X.IdealSheafData) [hJ : IsIntegral J.subscheme] {η : X}
    (hη : IsGenericPoint η (J.support : Set X)) (i : Fin S.length)
    (h : ∀ m : Fin S.length, m ≤ i → ¬ S.center m ≤ S.strictTransformSeq J m.castSucc)
    (y : S.stage i.castSucc) (hy : S.stageMap i.castSucc y = η) : y ∉ (S.center i).support := by
  obtain ⟨m, hm⟩ := i
  exact notMem_center_support_of_stageMap_eq_mk hX S J hJ hη m hm
    (fun m' hm' => h ⟨m', by omega⟩ (Fin.mk_le_mk.mpr hm')) y hy

end Sequence

end AlgebraicGeometry
