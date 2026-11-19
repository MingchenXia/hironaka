/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.OffCenters
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.RestrictSubscheme
import Hironaka.Scheme.BlowUpSequence.ClosedImmersionStalk
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformUnion
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The preimage of the singular locus is a simple normal crossing divisor

Clause (3) of [Kol07, Theorem 36] for the resolution of an embedded affine scheme, following the
proof of [Kol07, Theorem 27]: since the last centre `Z_j` is smooth, the resolution
`g : Z_j → X̄` is not an isomorphism over any singular point, so `g⁻¹(Sing X̄)` is the trace on
`Z_j` of the total exceptional divisor `Ex_tot(π_0 ⋯ π_{j−1})`, and `Z_j` has simple normal
crossings with `Ex_tot`, so the trace is a simple normal crossing divisor on `Z_j`. Here `Z_j` is
replaced by the end result `X̄_j` of the truncated restriction, an open subscheme of the centre
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification`), embedded in the ambient stage `A_j` by
the last stage lift `ι` of the closed immersion `emb`.

The witness family is `F := (Ex_tot).comap ι`, the restriction to `X̄_j` of the total transform of
the (empty) boundary at stage `j`:

* `F` has simple normal crossings by the last sentence of [Kol07, Definition 24]: `Ex_tot` has
  simple normal crossings with `Z_j` [Kol07, Theorem 35 (1)], hence with `X̄_j` (the two ideals
  agree along the open subscheme), and no component of `Ex_tot` contains `X̄_j` near any of its
  points, because the generic point of `X̄_j` lies over no centre (no earlier centre contains the
  strict transform of `X`) and hence off `Ex_tot` [Kol07, Definition 25].
* `F.support = g⁻¹(Sing X)`: a point `p` of `X̄_j` on `Ex_tot` lies over a restricted centre
  `Z_m ∩ X̄_m` [Kol07, Definition 25; Definition 30, 30.2], so its image is singular by clause (2)
  (the hypothesis `hno`: no restricted centre over a smooth point); a point `p` off `Ex_tot` lies
  over no centre, so the ambient stage map is an isomorphism on stalks at `ι p` carrying `I_X` onto
  the strict transform, the local ring of `X` at `g p` is that of `X̄_j` at `p`, regular since
  `X̄_j` is smooth by clause (1), so `g p` is a smooth point.

## Main results

* `exists_isSnc_comap_totalTransformSeq_last`: the theorem for a blow-up sequence `T` at its last
  stage, with hypotheses: `T` is a smooth blow-up sequence, the total transform of the boundary
  at the last stage has simple normal crossings with a subscheme `Zc` containing `X̄` as an open
  subscheme, no centre of `T` contains the strict transform of `X`, `X̄` is smooth over `k`, and
  no restricted centre has a point over a smooth point of `X`.
* `exists_isSnc_comap_totalTransformSeq_take`: the same for the truncation `S.take j`, with the
  hypotheses stated at the index `j` of `S`.

The hypotheses are discharged for the principalization sequence `BP TA` at the first-centre index
in `Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36IsoSnc`, giving clause (3) of Theorem
36 for `BR_affine`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace Hironaka.Resolution

open Scheme

variable {k : Type u} [Field k] [CharZero k] {A X : Scheme.{u}}

/-! ### Bookkeeping: divisor-family supports and the last stage lift -/

/-- The support of a divisor family with no members is empty. -/
theorem _root_.AlgebraicGeometry.Scheme.DivisorFamily.coe_support_eq_empty_of_isEmpty
    (E : DivisorFamily A) (hE : IsEmpty E.ι) :
    (E.support : Set A) = ∅ := by
  rw [DivisorFamily.coe_support_eq_iUnion]
  exact Set.iUnion_of_empty _

/-- A point lies on the inverse image family `h⁻¹(E)` iff its image lies on `E`. -/
theorem _root_.AlgebraicGeometry.Scheme.DivisorFamily.mem_comap_support_iff {Y : Scheme.{u}}
    (E : DivisorFamily A) (g : Y ⟶ A)
    (y : Y) : y ∈ (E.comap g).support ↔ g y ∈ E.support := by
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, DivisorFamily.coe_support_eq_iUnion,
    DivisorFamily.coe_support_eq_iUnion, Set.mem_iUnion, Set.mem_iUnion]
  exact exists_congr fun i => mem_support_comap_iff_apply (E.component i) g y

/-- The last stage lift of a closed immersion along a blow-up sequence is a closed immersion
(`isClosedImmersion_pullbackStageHom` at the last index). -/
theorem isClosedImmersion_pullbackLastHom (T : BlowUpSequence A) (emb : X ⟶ A)
    [IsClosedImmersion emb] : IsClosedImmersion (T.pullbackLastHom emb) := by
  have := isClosedImmersion_pullbackStageHom T emb (Fin.last _)
  exact IsClosedImmersion.comp
    (eqToHom (congrArg (T.pullback emb).stage (pullbackStageIdx_last T emb).symm))
    (T.pullbackStageHom emb (Fin.last _))

/-- The kernel of the last stage lift of a closed immersion is the strict transform of its kernel
at the last stage [Kol07, Definition 30, 30.2] (`ker_pullbackStageHom`). -/
theorem ker_pullbackLastHom (T : BlowUpSequence A) (emb : X ⟶ A) [IsClosedImmersion emb] :
    (T.pullbackLastHom emb).ker = T.strictTransformSeq emb.ker (Fin.last _) :=
  (Scheme.Hom.ker_comp_of_isIso
    (eqToHom (congrArg (T.pullback emb).stage (pullbackStageIdx_last T emb).symm))
    (T.pullbackStageHom emb (Fin.last _))).trans
      (ker_pullbackStageHom T emb (Fin.last _))

/-! ### Theorem 36 (3) at the last stage of a sequence -/

/-- Clause (3) of [Kol07, Theorem 36] for the restriction of a blow-up sequence `T` on `A` to a
reduced closed subscheme `X = V(I)`, after the proof of [Kol07, Theorem 27]: given a subscheme `Zc`
of the last stage containing the strict transform `X̄ = V(strictTransformSeq I)` as an open
subscheme, the total transform `Ex_tot` of the boundary having simple normal crossings with `Zc`,
through every point of `X̄` an integral closed subscheme `V(J) ⊆ X` whose strict transform passes
through the point and which no centre of `T` contains (`hcomp`; for an integral `X`, `V(J) = X`
itself; for a reduced `X`, the component through the image of the point), `X̄` smooth over `k` and
no restricted centre over a smooth point of `X`, the family `Ex_tot|_{X̄}` has simple normal
crossings and its support is the preimage of the singular locus of `X`. The generic point of the
strict transform of `V(J)` lies over no centre, hence off `Ex_tot`, so no member of `Ex_tot`
contains `X̄` near the point (`not_stalkIdeal_le_of_specializes_notMem`). -/
theorem exists_isSnc_comap_totalTransformSeq_last_of_forall (f : A ⟶ Spec (CommRingCat.of k))
    [Smooth f] (T : BlowUpSequence A) (hT : T.IsSmooth f) (I : A.IdealSheafData)
    (E : DivisorFamily A) (hE : IsEmpty E.ι) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] (emb : X ⟶ A)
    [IsClosedImmersion emb] (hI : emb.ker = I) {Zc : (T.stage (Fin.last T.length)).IdealSheafData}
    (hle : Zc ≤ T.strictTransformSeq I (Fin.last _))
    [IsOpenImmersion (Scheme.IdealSheafData.inclusion hle)]
    (hsnc : (T.totalTransformSeq E (Fin.last _)).HasSncWith Zc)
    (hcomp : ∀ p ∈ (T.strictTransformSeq I (Fin.last _)).support,
      ∃ J : A.IdealSheafData, IsIntegral J.subscheme ∧ I ≤ J ∧
        p ∈ (T.strictTransformSeq J (Fin.last _)).support ∧
        ∃ η : A, IsGenericPoint η (J.support : Set A) ∧
          ∀ m : Fin T.length, ¬ T.center m ≤ T.strictTransformSeq J m.castSucc)
    (hsmX : Smooth ((T.pullback emb).composite ≫ (X ↘ Spec (CommRingCat.of k))))
    (hno : ∀ x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus, ∀ i : Fin T.length,
      ¬ RestrictedCenterHasPointOver T I i (emb x)) :
    ∃ F : DivisorFamily (T.pullback emb).last, F.IsSnc ∧
      (F.support : Set (T.pullback emb).last) =
        (T.pullback emb).composite ⁻¹' ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  classical
  have hAln : IsLocallyNoetherian A := f.isLocallyNoetherian_of_field
  have hXln : IsLocallyNoetherian X :=
    (X ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have hιci : IsClosedImmersion (T.pullbackLastHom emb) := isClosedImmersion_pullbackLastHom T emb
  have hker : (T.pullbackLastHom emb).ker = T.strictTransformSeq I (Fin.last _) := by
    rw [ker_pullbackLastHom, hI]
  have hEs : (E.support : Set A) = ∅ := DivisorFamily.coe_support_eq_empty_of_isEmpty E hE
  have hcommp : ∀ p : (T.pullback emb).last,
      T.stageMap (Fin.last _) (T.pullbackLastHom emb p) = emb ((T.pullback emb).composite p) :=
    fun p => congrArg (fun g : (T.pullback emb).last ⟶ A => g p)
      (Hironaka.Sequence.pullbackLastHom_comp_composite T emb)
  refine ⟨(T.totalTransformSeq E (Fin.last _)).comap (T.pullbackLastHom emb), ?_, ?_⟩
  · -- simple normal crossings, by the last sentence of Definition 24
    have hsmA := IsSmooth.smooth_stageMap' hT (Fin.last _)
    have hreg : ∀ x : T.last, IsRegularLocalRing (T.last.presheaf.stalk x) := fun x =>
      isRegularLocalRing_stalk (T.stageMap (Fin.last _) ≫ f) x
    have hZ : (T.totalTransformSeq E (Fin.last _)).HasSncWith (T.pullbackLastHom emb).ker := by
      rw [hker]
      exact Hironaka.Snc.HasSncWith.of_isOpenImmersion_inclusion hsnc hle
    have hnot : ∀ (i : (T.totalTransformSeq E (Fin.last _)).ι) (x : T.last),
        x ∈ (T.pullbackLastHom emb).ker.support →
        x ∈ ((T.totalTransformSeq E (Fin.last _)).component i).support →
        ¬ ((T.totalTransformSeq E (Fin.last _)).component i).stalkIdeal x ≤
          (T.pullbackLastHom emb).ker.stalkIdeal x := by
      intro i x hx hxi
      rw [hker] at hx ⊢
      obtain ⟨J, hJint, hIJ, hxJ, η, hη, hnotleJ⟩ := hcomp x hx
      obtain ⟨η', hη', hη'η, -⟩ := exists_isGenericPoint_strictTransformSeq T J hη
        (Fin.last _) fun m _ => hnotleJ m
      have hηE : η' ∉ (T.totalTransformSeq E (Fin.last _)).support := by
        rw [Hironaka.Sequence.mem_support_totalTransformSeq_iff]
        rintro (h | ⟨m, hmi, h⟩)
        · exact Set.eq_empty_iff_forall_notMem.1 hEs _ h
        · refine notMem_center_support_of_stageMap_eq T J hη m
            (fun m' _ => hnotleJ m') _ ?_ h
          rw [← Scheme.Hom.comp_apply, stageMapBetween_comp_stageMap]
          exact hη'η
      refine Hironaka.Snc.not_stalkIdeal_le_of_specializes_notMem _ _ (hη'.specializes hxJ)
        (Scheme.IdealSheafData.support_antitone (strictTransformSeq_mono T hIJ _) hη'.mem)
        fun hmem => hηE ?_
      rw [← SetLike.mem_coe, DivisorFamily.coe_support_eq_iUnion]
      exact Set.mem_iUnion.2 ⟨i, hmem⟩
    exact Hironaka.Snc.isSnc_comap_of_hasSncWith
      ((T.pullback emb).composite ≫ (X ↘ Spec (CommRingCat.of k))) (T.pullbackLastHom emb) hreg
      hZ hnot
  · -- the support: `g⁻¹(Sing X)`
    ext p
    rw [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hp hsm
      have hp' : T.pullbackLastHom emb p ∈ (T.totalTransformSeq E (Fin.last _)).support :=
        (DivisorFamily.mem_comap_support_iff _ _ p).1 hp
      rcases (Hironaka.Sequence.mem_support_totalTransformSeq_iff T E (Fin.last _)
        (T.pullbackLastHom emb p)).1 hp' with h | ⟨m, hmi, h⟩
      · exact Set.eq_empty_iff_forall_notMem.1 hEs _ h
      · refine hno _ hsm m ⟨T.stageMapBetween (Fin.last _) m.castSucc (Nat.le_of_lt hmi)
          (T.pullbackLastHom emb p), h, ?_, ?_⟩
        · refine Hironaka.Sequence.stageMapBetween_mem_support_strictTransformSeq T I _ ?_
          have hmem : T.pullbackLastHom emb p ∈
              ((T.pullbackLastHom emb).ker.support : Set T.last) := by
            rw [Scheme.Hom.support_ker]
            exact subset_closure ⟨p, rfl⟩
          rw [hker] at hmem
          exact hmem
        · have h1 := congrArg (fun g : T.stage (Fin.last _) ⟶ A => g (T.pullbackLastHom emb p))
            (stageMapBetween_comp_stageMap T (i := Fin.last _) (j := m.castSucc)
              (Nat.le_of_lt hmi))
          exact ((Scheme.Hom.comp_apply _ _ _).symm.trans h1).trans (hcommp p)
    · intro hp
      by_contra hpF
      apply hp
      have hoff : ∀ (m : Fin T.length) (hmi : m.val < (Fin.last T.length).val),
          T.stageMapBetween (Fin.last _) m.castSucc (Nat.le_of_lt hmi) (T.pullbackLastHom emb p) ∉
            (T.center m).support := fun m hmi h =>
        hpF ((DivisorFamily.mem_comap_support_iff _ _ p).2
          ((Hironaka.Sequence.mem_support_totalTransformSeq_iff T E _ _).2 (Or.inr ⟨m, hmi, h⟩)))
      have hisoSt : IsIso (@Scheme.Hom.stalkMap T.last A (T.stageMap (Fin.last _))
          (T.pullbackLastHom emb p)) :=
        Hironaka.Sequence.isIso_stalkMap_stageMap_of_forall_notMem T (Fin.last _) _ hoff
      have hstalk :=
        Hironaka.Sequence.stalkIdeal_strictTransformSeq_of_forall_notMem T I (Fin.last _) _ hoff
      have hregp : IsRegularLocalRing ((T.pullback emb).last.presheaf.stalk p) :=
        isRegularLocalRing_stalk
          ((T.pullback emb).composite ≫ (X ↘ Spec (CommRingCat.of k))) p
      have h2 : (T.pullbackLastHom emb).ker.stalkIdeal (T.pullbackLastHom emb p) =
          (emb.ker.stalkIdeal (T.stageMap (Fin.last _) (T.pullbackLastHom emb p))).map
            ((T.stageMap (Fin.last _)).stalkMap (T.pullbackLastHom emb p)).hom := by
        rw [hI, hker]
        exact hstalk
      have hregx := isRegularLocalRing_stalk_of_isIso_stalkMap_of_stalkIdeal_eq
        emb (T.pullbackLastHom emb) (T.stageMap (Fin.last _)) (hcommp p) h2
      exact (Scheme.mem_smoothLocus_iff_isRegularAt (X ↘ Spec (CommRingCat.of k)) _).2 hregx

/-- Clause (3) of [Kol07, Theorem 36] for the restriction of a blow-up sequence `T` on `A` to an
INTEGRAL closed subscheme `X = V(I)`: `exists_isSnc_comap_totalTransformSeq_last_of_forall` with
`V(J) = X` at every point. -/
theorem exists_isSnc_comap_totalTransformSeq_last (f : A ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (T : BlowUpSequence A) (hT : T.IsSmooth f) (I : A.IdealSheafData) (E : DivisorFamily A)
    (hE : IsEmpty E.ι) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsIntegral X] (emb : X ⟶ A)
    [IsClosedImmersion emb] (hI : emb.ker = I) {Zc : (T.stage (Fin.last T.length)).IdealSheafData}
    (hle : Zc ≤ T.strictTransformSeq I (Fin.last _))
    [IsOpenImmersion (Scheme.IdealSheafData.inclusion hle)]
    (hsnc : (T.totalTransformSeq E (Fin.last _)).HasSncWith Zc)
    (hnotle : ∀ m : Fin T.length, ¬ T.center m ≤ T.strictTransformSeq I m.castSucc)
    (hsmX : Smooth ((T.pullback emb).composite ≫ (X ↘ Spec (CommRingCat.of k))))
    (hno : ∀ x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus, ∀ i : Fin T.length,
      ¬ RestrictedCenterHasPointOver T I i (emb x)) :
    ∃ F : DivisorFamily (T.pullback emb).last, F.IsSnc ∧
      (F.support : Set (T.pullback emb).last) =
        (T.pullback emb).composite ⁻¹' ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  have hXln : IsLocallyNoetherian X :=
    (X ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have hInt : IsIntegral I.subscheme := by
    have := IsIntegral.of_isIso emb.toImage
    change IsIntegral emb.ker.subscheme at this
    rwa [hI] at this
  have hη : IsGenericPoint (emb (genericPoint X)) (I.support : Set A) := by
    have h := (genericPoint_spec X).image emb.continuous
    rwa [Set.image_univ, ← Scheme.Hom.support_ker, hI] at h
  exact exists_isSnc_comap_totalTransformSeq_last_of_forall f T hT I E hE emb hI hle hsnc
    (fun p hp => ⟨I, hInt, le_rfl, hp, emb (genericPoint X), hη, hnotle⟩) hsmX hno

/-! ### Transport to the truncation `S.take j` -/

theorem hasSncWith_of_heq {Y₁ Y₂ : Scheme.{u}} (e : Y₁ = Y₂) {E₁ : DivisorFamily Y₁}
    {E₂ : DivisorFamily Y₂} (hE : HEq E₁ E₂) {Z₁ : Y₁.IdealSheafData} {Z₂ : Y₂.IdealSheafData}
    (hZ : HEq Z₁ Z₂) (h : E₁.HasSncWith Z₁) : E₂.HasSncWith Z₂ := by
  subst e
  cases hE
  cases hZ
  exact h

theorem le_of_heq_of_heq {Y₁ Y₂ : Scheme.{u}} (e : Y₁ = Y₂) {a₁ b₁ : Y₁.IdealSheafData}
    {a₂ b₂ : Y₂.IdealSheafData} (ha : HEq a₁ a₂) (hb : HEq b₁ b₂) (h : a₁ ≤ b₁) : a₂ ≤ b₂ := by
  subst e
  cases ha
  cases hb
  exact h

theorem isOpenImmersion_inclusion_of_heq {Y₁ Y₂ : Scheme.{u}} (e : Y₁ = Y₂)
    {a₁ b₁ : Y₁.IdealSheafData} {a₂ b₂ : Y₂.IdealSheafData} (ha : HEq a₁ a₂) (hb : HEq b₁ b₂)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) [IsOpenImmersion (Scheme.IdealSheafData.inclusion h₁)] :
    IsOpenImmersion (Scheme.IdealSheafData.inclusion h₂) := by
  subst e
  cases ha
  cases hb
  infer_instance

/-- Clause (3) of [Kol07, Theorem 36] on the truncation `S.take j`, for a reduced closed
subscheme `X`, with the hypotheses stated at the index `j` of `S` except `hcomp`, which is stated
on the truncation at its last stage (`exists_isSnc_comap_totalTransformSeq_last_of_forall`). -/
theorem exists_isSnc_comap_totalTransformSeq_take_of_forall (f : A ⟶ Spec (CommRingCat.of k))
    [Smooth f] (S : BlowUpSequence A) (hS : S.IsSmooth f) (I : A.IdealSheafData)
    (E : DivisorFamily A) (hE : IsEmpty E.ι) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] (emb : X ⟶ A)
    [IsClosedImmersion emb] (hI : emb.ker = I) {j : ℕ} (hj : j < S.length)
    (hle : S.center ⟨j, hj⟩ ≤ S.strictTransformSeq I ⟨j, Nat.lt_succ_of_lt hj⟩)
    [IsOpenImmersion (Scheme.IdealSheafData.inclusion hle)]
    (hsnc : (S.totalTransformSeq E ⟨j, Nat.lt_succ_of_lt hj⟩).HasSncWith (S.center ⟨j, hj⟩))
    (hcomp : ∀ p ∈ ((S.take j).strictTransformSeq I (Fin.last _)).support,
      ∃ J : A.IdealSheafData, IsIntegral J.subscheme ∧ I ≤ J ∧
        p ∈ ((S.take j).strictTransformSeq J (Fin.last _)).support ∧
        ∃ η : A, IsGenericPoint η (J.support : Set A) ∧
          ∀ m : Fin (S.take j).length,
            ¬ (S.take j).center m ≤ (S.take j).strictTransformSeq J m.castSucc)
    (hsmX : Smooth (((S.take j).pullback emb).composite ≫ (X ↘ Spec (CommRingCat.of k))))
    (hno : ∀ x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus, ∀ i : Fin (S.take j).length,
      ¬ RestrictedCenterHasPointOver (S.take j) I i (emb x)) :
    ∃ F : DivisorFamily ((S.take j).pullback emb).last, F.IsSnc ∧
      (F.support : Set ((S.take j).pullback emb).last) =
        ((S.take j).pullback emb).composite ⁻¹'
          ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  have hlen : (S.take j).length = j := length_take_of_le S hj.le
  have hj₁ : j < (S.take j).length + 1 := by omega
  have hfin : Fin.last (S.take j).length = ⟨j, hj₁⟩ := Fin.ext hlen
  have e₁ : (S.take j).stage (Fin.last _) = (S.take j).stage ⟨j, hj₁⟩ := congrArg _ hfin
  have e₂ : (S.take j).stage ⟨j, hj₁⟩ = S.stage ⟨j, Nat.lt_succ_of_lt hj⟩ :=
    stage_take_mk S j j hj₁ _
  have hT₁ : HEq ((S.take j).totalTransformSeq E (Fin.last _))
      ((S.take j).totalTransformSeq E ⟨j, hj₁⟩) := by rw [hfin]
  have hT₂ := totalTransformSeq_take_heq_mk S E j j hj₁ (Nat.lt_succ_of_lt hj)
  have hS₁ : HEq ((S.take j).strictTransformSeq I (Fin.last _))
      ((S.take j).strictTransformSeq I ⟨j, hj₁⟩) := by rw [hfin]
  have hS₂ := strictTransformSeq_take_heq_mk S I j j hj₁ (Nat.lt_succ_of_lt hj)
  let Zc : ((S.take j).stage (Fin.last (S.take j).length)).IdealSheafData :=
    cast (congrArg Scheme.IdealSheafData (e₁.trans e₂).symm) (S.center ⟨j, hj⟩)
  have hZc : HEq Zc (S.center ⟨j, hj⟩) := cast_heq _ _
  have hle' : Zc ≤ (S.take j).strictTransformSeq I (Fin.last _) :=
    le_of_heq_of_heq (e₁.trans e₂).symm hZc.symm (hS₁.trans hS₂).symm hle
  have : IsOpenImmersion (Scheme.IdealSheafData.inclusion hle') :=
    isOpenImmersion_inclusion_of_heq (e₁.trans e₂).symm hZc.symm (hS₁.trans hS₂).symm hle hle'
  have hsnc' : ((S.take j).totalTransformSeq E (Fin.last _)).HasSncWith Zc :=
    hasSncWith_of_heq (e₁.trans e₂).symm (hT₁.trans hT₂).symm hZc.symm hsnc
  exact exists_isSnc_comap_totalTransformSeq_last_of_forall f (S.take j)
    (isSmooth_take f hS j) I E hE emb hI hle' hsnc' hcomp hsmX hno

/-- Clause (3) of [Kol07, Theorem 36] on the truncation `S.take j`, with the hypotheses stated at
the index `j` of `S`: the total transform at stage `j` has simple normal crossings with the centre
`Z_j`, which contains the strict transform `X̄_j` as an open subscheme; no earlier centre contains
the strict transform; `X̄_j` is smooth over `k`; no restricted centre lies over a smooth point. -/
theorem exists_isSnc_comap_totalTransformSeq_take (f : A ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (S : BlowUpSequence A) (hS : S.IsSmooth f) (I : A.IdealSheafData) (E : DivisorFamily A)
    (hE : IsEmpty E.ι) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsIntegral X] (emb : X ⟶ A)
    [IsClosedImmersion emb] (hI : emb.ker = I) {j : ℕ} (hj : j < S.length)
    (hle : S.center ⟨j, hj⟩ ≤ S.strictTransformSeq I ⟨j, Nat.lt_succ_of_lt hj⟩)
    [IsOpenImmersion (Scheme.IdealSheafData.inclusion hle)]
    (hsnc : (S.totalTransformSeq E ⟨j, Nat.lt_succ_of_lt hj⟩).HasSncWith (S.center ⟨j, hj⟩))
    (hnotle : ∀ m : Fin S.length, m.val < j → ¬ S.center m ≤ S.strictTransformSeq I m.castSucc)
    (hsmX : Smooth (((S.take j).pullback emb).composite ≫ (X ↘ Spec (CommRingCat.of k))))
    (hno : ∀ x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus, ∀ i : Fin (S.take j).length,
      ¬ RestrictedCenterHasPointOver (S.take j) I i (emb x)) :
    ∃ F : DivisorFamily ((S.take j).pullback emb).last, F.IsSnc ∧
      (F.support : Set ((S.take j).pullback emb).last) =
        ((S.take j).pullback emb).composite ⁻¹'
          ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  have hlen : (S.take j).length = j := length_take_of_le S hj.le
  have hj₁ : j < (S.take j).length + 1 := by omega
  have hfin : Fin.last (S.take j).length = ⟨j, hj₁⟩ := Fin.ext hlen
  have e₁ : (S.take j).stage (Fin.last _) = (S.take j).stage ⟨j, hj₁⟩ := congrArg _ hfin
  have e₂ : (S.take j).stage ⟨j, hj₁⟩ = S.stage ⟨j, Nat.lt_succ_of_lt hj⟩ :=
    stage_take_mk S j j hj₁ _
  have hT₁ : HEq ((S.take j).totalTransformSeq E (Fin.last _))
      ((S.take j).totalTransformSeq E ⟨j, hj₁⟩) := by rw [hfin]
  have hT₂ := totalTransformSeq_take_heq_mk S E j j hj₁ (Nat.lt_succ_of_lt hj)
  have hS₁ : HEq ((S.take j).strictTransformSeq I (Fin.last _))
      ((S.take j).strictTransformSeq I ⟨j, hj₁⟩) := by rw [hfin]
  have hS₂ := strictTransformSeq_take_heq_mk S I j j hj₁ (Nat.lt_succ_of_lt hj)
  let Zc : ((S.take j).stage (Fin.last (S.take j).length)).IdealSheafData :=
    cast (congrArg Scheme.IdealSheafData (e₁.trans e₂).symm) (S.center ⟨j, hj⟩)
  have hZc : HEq Zc (S.center ⟨j, hj⟩) := cast_heq _ _
  have hle' : Zc ≤ (S.take j).strictTransformSeq I (Fin.last _) :=
    le_of_heq_of_heq (e₁.trans e₂).symm hZc.symm (hS₁.trans hS₂).symm hle
  have : IsOpenImmersion (Scheme.IdealSheafData.inclusion hle') :=
    isOpenImmersion_inclusion_of_heq (e₁.trans e₂).symm hZc.symm (hS₁.trans hS₂).symm hle hle'
  have hsnc' : ((S.take j).totalTransformSeq E (Fin.last _)).HasSncWith Zc :=
    hasSncWith_of_heq (e₁.trans e₂).symm (hT₁.trans hT₂).symm hZc.symm hsnc
  have hnotle' : ∀ m : Fin (S.take j).length,
      ¬ (S.take j).center m ≤ (S.take j).strictTransformSeq I m.castSucc := by
    intro m hm
    have hmj : m.val < j := lt_of_lt_of_eq m.2 hlen
    refine hnotle ⟨m.val, lt_trans hmj hj⟩ hmj ?_
    exact le_of_heq_of_heq (stage_take_mk S j m.val (Nat.lt_succ_of_lt m.2) _)
      (center_take_heq_mk S j m.val m.2 _)
      (strictTransformSeq_take_heq_mk S I j m.val (Nat.lt_succ_of_lt m.2) _) hm
  exact exists_isSnc_comap_totalTransformSeq_last f (S.take j)
    (isSmooth_take f hS j) I E hE emb hI hle' hsnc' hnotle' hsmX hno

end Hironaka.Resolution
