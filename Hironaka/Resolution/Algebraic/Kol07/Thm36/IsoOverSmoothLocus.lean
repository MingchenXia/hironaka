/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Hironaka.Resolution.Algebraic.Kol07.SurjectiveCompletion
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Smooth.TwoPointEtalePair
import Hironaka.Scheme.Snc.RelativeDimensionConstant
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# No restricted centre over a smooth point

Kollár's argument that a functorial resolution is an isomorphism over the smooth locus
[Kol07, 4.2; Theorem 27, proof]: a resolution is birational, hence an isomorphism over some smooth
point; any two smooth points are étale equivalent; and a resolution functorial under étale
morphisms therefore is an isomorphism over every smooth point. For the resolution of an embedded
affine scheme, the truncated restriction `((BP TA).take j).pullback emb` of
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine`, the statement transported is that no restricted
centre `Z_i ∩ X̄_i`, `i < j`, has a point over `x` (`RestrictedCenterHasPointOver`), and the
functoriality used is that of the whole principalization sequence under smooth surjections [Kol07,
Theorem 35 (4); 34.1]. Two smooth points of `X` are made étale equivalent as embedded points by an
étale pair `ψ, ψ' : W ⟶ A` over `k` with the same inverse image of `I_X`, and the pair is completed
to surjective étale maps (`exists_completion_isPullbackOf`) so that the functoriality applies.

The theorems are stated for an arbitrary assignment `F` of a blow-up sequence to every triple
that is functorial under smooth surjections (the hypothesis `hfun`), and for a truncation index
`j` such that no restricted centre has a point over the generic point of `X` (the hypothesis
`ha`); they are applied to `F := BP` at the first-centre index in
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36IsoSnc`.

## Main results

* `isClosed_setOf_restrictedCenterHasPointOver`: the set of points of `X` over which some
  restricted centre has a point is closed, being the finite union of the images of the closed
  centres of the restriction under its proper stage maps.
* `restrictedCenterHasPointOver_iff_of_etale_pair`: along an étale pair `ψ, ψ'` as above, the
  predicate at `ψ q` is equivalent to the predicate at `ψ' q`.
* `not_restrictedCenterHasPointOver_of_mem_smoothLocus`: for an integral `X`, if no restricted
  centre has a point over the generic point of `X`, then none has a point over any point of the
  smooth locus of `X`. Closed points of the finite-type scheme `X` meet every nonempty locally
  closed subset (Jacobson), which reduces the statement to closed points; the étale pair is taken
  on the open `U₁ = A ∖ emb(X ∖ X^{ns})`, over which `X ∩ U₁ = X^{ns}` is smooth of one relative
  dimension, between a closed point of `X^{ns}` outside the closed exceptional set and any closed
  point of `X^{ns}`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Hironaka Scheme BlowUpSequence
  Hironaka.Sequence TopologicalSpace

namespace Hironaka.Resolution

/-! ### Bookkeeping -/

/-- The predicate `RestrictedCenterHasPointOver` along an equality of sequences and of ideal
sheaves, with indices of the same value. -/
theorem restrictedCenterHasPointOver_congr {Y : Scheme.{u}} {S₁ S₂ : BlowUpSequence Y}
    (e : S₁ = S₂) {J₁ J₂ : Y.IdealSheafData} (eJ : J₁ = J₂) {i₁ : Fin S₁.length}
    {i₂ : Fin S₂.length} (hi : i₁.val = i₂.val) (y : Y) :
    RestrictedCenterHasPointOver S₁ J₁ i₁ y ↔ RestrictedCenterHasPointOver S₂ J₂ i₂ y := by
  subst e
  subst eJ
  obtain rfl : i₁ = i₂ := Fin.ext hi
  exact Iff.rfl

/-- The set of points of the closed subscheme `X` over which some restricted centre has a point
is closed: it is the finite union of the images of the (closed) centres of the restriction of the
sequence to `X` under the proper stage maps [Kol07, Definition 30, 30.2, with the properness of
the stage maps]. -/
theorem isClosed_setOf_restrictedCenterHasPointOver {A X : Scheme.{u}} [IsLocallyNoetherian X]
    (S : BlowUpSequence A) (emb : X ⟶ A) [IsClosedImmersion emb] :
    IsClosed {x : X | ∃ i, RestrictedCenterHasPointOver S emb.ker i (emb x)} := by
  have : {x : X | ∃ i, RestrictedCenterHasPointOver S emb.ker i (emb x)} =
      ⋃ i : Fin S.length, (S.pullback emb).stageMap (S.pullbackCenterIdx emb i).castSucc ''
        (((S.pullback emb).center (S.pullbackCenterIdx emb i)).support : Set _) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨p, hp, hpx⟩ := (restrictedCenterHasPointOver_iff_of_isClosedImmersion S emb i x).2 hi
      exact ⟨i, p, hp, hpx⟩
    · rintro ⟨i, p, hp, hpx⟩
      exact ⟨i, (restrictedCenterHasPointOver_iff_of_isClosedImmersion S emb i x).1 ⟨p, hp, hpx⟩⟩
  rw [this]
  refine isClosed_iUnion_of_finite fun i => ?_
  have := isProper_stageMap (S.pullback emb) (S.pullbackCenterIdx emb i).castSucc
  exact ((S.pullback emb).stageMap (S.pullbackCenterIdx emb i).castSucc).isClosedMap _
    (Closeds.isClosed _)

/-- The predicate, on data given up to equality of the stage and heterogeneous equality of the
centre, the strict transform and the stage map (the shape of the transport lemmas for truncated
sequences in `Hironaka.Scheme.BlowUpSequence.Truncate`). -/
theorem exists_mem_support_iff_of_heq {X : Scheme.{u}} {Y₁ Y₂ : Scheme.{u}} (e : Y₁ = Y₂)
    {c₁ : Y₁.IdealSheafData} {c₂ : Y₂.IdealSheafData} (hc : HEq c₁ c₂)
    {t₁ : Y₁.IdealSheafData} {t₂ : Y₂.IdealSheafData} (ht : HEq t₁ t₂)
    {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (hf : HEq f₁ f₂) (x : X) :
    (∃ p : Y₁, p ∈ c₁.support ∧ p ∈ t₁.support ∧ f₁ p = x) ↔
      ∃ p : Y₂, p ∈ c₂.support ∧ p ∈ t₂.support ∧ f₂ p = x := by
  subst e
  cases hc
  cases ht
  cases hf
  exact Iff.rfl

/-- The restricted centres of the truncation `S.take k` are those of `S` at the same index
(through the transports of stage, centre, strict transform and stage map of
`Hironaka.Scheme.BlowUpSequence.Truncate`). -/
theorem restrictedCenterHasPointOver_take_mk {X : Scheme.{u}} (S : BlowUpSequence X)
    (J : X.IdealSheafData) (k m : ℕ) (hm : m < (S.take k).length) (hm' : m < S.length) (x : X) :
    RestrictedCenterHasPointOver (S.take k) J ⟨m, hm⟩ x ↔
      RestrictedCenterHasPointOver S J ⟨m, hm'⟩ x := by
  unfold RestrictedCenterHasPointOver
  exact exists_mem_support_iff_of_heq (stage_take_mk S k m (Nat.lt_succ_of_lt hm)
    (Nat.lt_succ_of_lt hm')) (center_take_heq_mk S k m hm hm')
    (strictTransformSeq_take_heq_mk S J k m (Nat.lt_succ_of_lt hm) (Nat.lt_succ_of_lt hm'))
    (stageMap_take_heq_mk S k m (Nat.lt_succ_of_lt hm) (Nat.lt_succ_of_lt hm')) x

/-- `restrictedCenterHasPointOver_take_mk` in the `Fin` form. -/
theorem restrictedCenterHasPointOver_take {X : Scheme.{u}} (S : BlowUpSequence X)
    (J : X.IdealSheafData) (k : ℕ) (i : Fin (S.take k).length) (x : X) :
    RestrictedCenterHasPointOver (S.take k) J i x ↔
      RestrictedCenterHasPointOver S J ⟨i.val, lt_of_lt_of_le i.2 (by
        rw [length_take]; exact min_le_right _ _)⟩ x := by
  obtain ⟨m, hm⟩ := i
  exact restrictedCenterHasPointOver_take_mk S J k m hm _ x

variable {k : Type u} [Field k] [CharZero k]

/-! ### Transport along an étale pair -/

/-- Transport along an étale pair [Kol07, 4.2; 34.1]: for an assignment `F` of a blow-up sequence
to every triple that is functorial under smooth surjections (`hfun`), a triple `TA` with empty
boundary, and an étale pair `ψ, ψ' : W ⟶ TA.X.left` over `k` with the same inverse image of `TA.I`,
the restricted centres of the truncation `(F TA).take j` have a point over `ψ q` if and only if
they have one over `ψ' q`. The surjective completion `T'` of the pair carries the pullback data
along both completed maps `g, g'`, so `(F TA).pullback g = F T' = (F TA).pullback g'`; truncation
commutes with pullback, and the predicate transports along the flat stage maps of a pullback, read
at a point `y` of `T'` over `ψ q` and over `ψ' q`. -/
theorem restrictedCenterHasPointOver_iff_of_etale_pair (F : ∀ T : Triple k, BlowUpSequence T.X.left)
    (TA : Triple k)
    (hfun : ∀ (T' : Triple k) (g : T'.X.left ⟶ TA.X.left) [Smooth g], Function.Surjective g →
      T'.IsPullbackOf TA g → F T' = (F TA).pullback g)
    (hE : IsEmpty TA.E.ι) (j : ℕ) {W : Scheme.{u}} [IsAffine W] (ψ ψ' : W ⟶ TA.X.left) [Etale ψ]
    [Etale ψ']
    (hover : ψ ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) = ψ' ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))
    (hI : TA.I.comap ψ = TA.I.comap ψ') (q : W) (i : Fin ((F TA).take j).length) :
    RestrictedCenterHasPointOver ((F TA).take j) TA.I i (ψ q) ↔
      RestrictedCenterHasPointOver ((F TA).take j) TA.I i (ψ' q) := by
  obtain ⟨T', g, g', hg, hg', hs, hs', hp, hp', hy⟩ :=
    exists_completion_isPullbackOf ψ ψ' hover hI hE
  have := hg
  have := hg'
  obtain ⟨y, hy1, hy2⟩ := hy q
  have e : (F TA).pullback g = (F TA).pullback g' :=
    (hfun T' g hs hp).symm.trans (hfun T' g' hs' hp')
  have e' : ((F TA).take j).pullback g = ((F TA).take j).pullback g' := by
    rw [take_pullback, take_pullback, e]
  have eI : TA.I.comap g = TA.I.comap g' := hp.2.1.symm.trans hp'.2.1
  rw [← hy1, ← hy2, ← restrictedCenterHasPointOver_pullback_iff ((F TA).take j) g TA.I i y,
    ← restrictedCenterHasPointOver_pullback_iff ((F TA).take j) g' TA.I i y]
  exact restrictedCenterHasPointOver_congr e' eI rfl y

/-! ### The smooth locus -/

variable (TA : Triple k) {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
  (emb : X ⟶ TA.X.left) [IsClosedImmersion emb] [emb.IsOver (Spec (CommRingCat.of k))]

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))] in
/-- No restricted centre over a smooth point [Kol07, Theorem 27, proof; 4.2]: for an integral
scheme `X` embedded in the ambient of the triple `TA` (empty boundary, ideal the ideal of `X`),
an assignment `F` of blow-up sequences to triples that is functorial under smooth surjections
(`hfun`), and a truncation index `j` such that no restricted centre `Z_i ∩ X̄_i` of `(F TA).take j`
has a point over the generic point of `X` (`ha`), no restricted centre has a point over any point
of the smooth locus of `X`. -/
theorem not_restrictedCenterHasPointOver_of_mem_smoothLocus [IsIntegral X] (hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I) (F : ∀ T : Triple k, BlowUpSequence T.X.left)
    (hfun : ∀ (T' : Triple k) (g : T'.X.left ⟶ TA.X.left) [Smooth g], Function.Surjective g →
      T'.IsPullbackOf TA g → F T' = (F TA).pullback g)
    (j : ℕ)
    (ha : ∀ i, ¬ RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb (genericPoint X)))
    {x : X} (hx : x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus)
    (i : Fin ((F TA).take j).length) :
    ¬ RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x) := by
  classical
  -- the closed locus `B` of the points over which some restricted centre has a point
  have : IsLocallyNoetherian X := (X ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have hB : IsClosed
      {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)} := by
    have := isClosed_setOf_restrictedCenterHasPointOver ((F TA).take j) emb
    rwa [hI] at this
  -- the generic point is smooth and outside `B`
  have hη : genericPoint X ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus :=
    Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField (X ↘ Spec (CommRingCat.of k))
  have hηB : genericPoint X ∉
      {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)} :=
    fun ⟨i, h⟩ => ha i h
  -- closed points: the base point `x₀ ∈ U ∖ B`, and, for a contradiction, `p ∈ B ∩ U`
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of k))
  obtain ⟨x₀, ⟨hx₀U, hx₀B⟩, hx₀c⟩ := nonempty_inter_closedPoints (X := X)
    (Z := ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X) ∩
      {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)}ᶜ)
    ⟨genericPoint X, hη, hηB⟩
    ((X ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen.isLocallyClosed.inter
      hB.isOpen_compl.isLocallyClosed)
  intro hxi
  obtain ⟨p, ⟨hpB, hpU⟩, hpc⟩ := nonempty_inter_closedPoints (X := X)
    (Z := {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)} ∩
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X))
    ⟨x, ⟨i, hxi⟩, hx⟩
    (hB.isLocallyClosed.inter (X ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen.isLocallyClosed)
  apply hx₀B
  -- the ambient open `U₁ = A ∖ emb(X ∖ U)`, with `emb⁻¹(U₁) = U`
  have hemb := emb.isClosedEmbedding
  have hclosed : IsClosed (emb '' (((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ)) :=
    hemb.isClosedMap _ (X ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen.isClosed_compl
  let U₁ : TA.X.left.Opens :=
    ⟨(emb '' (((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ))ᶜ, hclosed.isOpen_compl⟩
  have hmemU₁ : ∀ z : X, emb z ∈ U₁ ↔ z ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus :=
    fun z => by
    change emb z ∈ (emb '' (((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ))ᶜ ↔ _
    rw [Set.mem_compl_iff, Set.mem_image]
    constructor
    · intro h
      by_contra hz
      exact h ⟨z, hz, rfl⟩
    · rintro hz ⟨w, hw, hwz⟩
      exact hw (hemb.injective hwz ▸ hz)
  let V : X.Opens := emb ⁻¹ᵁ U₁
  have hmemV : ∀ z : X, z ∈ V ↔ z ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus :=
    fun z => hmemU₁ z
  -- the restriction `emb ∣_ U₁ : V ⟶ U₁`, a closed immersion with kernel `TA.I.comap U₁.ι`
  have hsq := isPullback_morphismRestrict emb U₁
  have : IsClosedImmersion (emb ∣_ U₁) :=
    property_of_isPullback _ hsq inferInstance
  have hker : (emb ∣_ U₁).ker = TA.I.comap U₁.ι := by
    rw [← hI, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion emb U₁.ι,
      ← hsq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  -- the ambient `U₁` is smooth of the relative dimension `n` of `TA.X.left`
  obtain ⟨n, hn⟩ := TA.smoothOfRelativeDimension
  have : SmoothOfRelativeDimension n (U₁.ι ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) := by
    have h := smoothOfRelativeDimension_comp 0 n U₁.ι (TA.X.left ↘ Spec (CommRingCat.of k))
    rwa [Nat.zero_add] at h
  -- `V = X^{ns}` is smooth over `k` of one relative dimension `d`
  have : Smooth (V.ι ≫ (X ↘ Spec (CommRingCat.of k))) := by
    refine Scheme.Hom.smoothLocus_eq_top_iff.1 ?_
    rw [← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro v _
    exact (hmemV v.1).1 v.2
  have : PreconnectedSpace (V : Scheme.{u}) := by
    have hX : IsPreirreducible (Set.univ : Set X) := PreirreducibleSpace.isPreirreducible_univ
    have : PreirreducibleSpace (V : Scheme.{u}) :=
      Subtype.preirreducibleSpace (hX.open_subset V.isOpen (Set.subset_univ _))
    infer_instance
  have : Nonempty (V : Scheme.{u}) := ⟨⟨genericPoint X, (hmemV _).2 hη⟩⟩
  obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension_of_preconnectedSpace
    (V.ι ≫ (X ↘ Spec (CommRingCat.of k)))
  have hcomp : (emb ∣_ U₁) ≫ (U₁.ι ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) =
      V.ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, HomIsOver.comp_over]
  have : SmoothOfRelativeDimension d
      ((emb ∣_ U₁) ≫ (U₁.ι ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))) := by
    rw [hcomp]; exact hd
  -- the two closed points of `U₁`
  have hx₀V : x₀ ∈ V := (hmemV _).2 hx₀U
  have hpV : p ∈ V := (hmemV _).2 hpU
  have hcl : ∀ (z : X) (hz : z ∈ V), IsClosed ({z} : Set X) →
      IsClosed ({(emb ∣_ U₁) ⟨z, hz⟩} : Set (U₁ : Scheme.{u})) := by
    intro z hz hzc
    have h1 : IsClosed ({emb z} : Set TA.X.left) := by
      have := hemb.isClosedMap _ hzc
      rwa [Set.image_singleton] at this
    have h2 : ({(emb ∣_ U₁) ⟨z, hz⟩} : Set (U₁ : Scheme.{u})) = Subtype.val ⁻¹' {emb z} := by
      ext w
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl
        exact morphismRestrict_base_coe emb U₁ ⟨z, hz⟩
      · intro hw
        apply Subtype.ext
        rw [hw]
        exact (morphismRestrict_base_coe emb U₁ ⟨z, hz⟩).symm
    rw [h2]
    exact h1.preimage continuous_subtype_val
  obtain ⟨W, q, ψ₁, ψ₁', hW, hψ₁, hψ₁', hq, hq', hIψ, hover⟩ :=
    exists_etale_pair_of_isClosedImmersion (U₁.ι ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))
      n d (emb ∣_ U₁) (x := ⟨x₀, hx₀V⟩) (x' := ⟨p, hpV⟩) (hcl x₀ hx₀V hx₀c) (hcl p hpV hpc)
  -- compose with the inclusion of `U₁` and transport
  have hIψ' : TA.I.comap (ψ₁ ≫ U₁.ι) = TA.I.comap (ψ₁' ≫ U₁.ι) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hker, hIψ]
  have hover' : (ψ₁ ≫ U₁.ι) ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) =
      (ψ₁' ≫ U₁.ι) ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) := by
    rw [Category.assoc, Category.assoc]
    exact hover
  obtain ⟨i', hi'⟩ := hpB
  have key := restrictedCenterHasPointOver_iff_of_etale_pair F TA hfun hE j (ψ₁ ≫ U₁.ι)
    (ψ₁' ≫ U₁.ι) hover' hIψ' q i'
  have hq₀ : (ψ₁ ≫ U₁.ι) q = emb x₀ := by
    rw [Scheme.Hom.comp_apply, hq]
    exact morphismRestrict_base_coe emb U₁ ⟨x₀, hx₀V⟩
  have hqp : (ψ₁' ≫ U₁.ι) q = emb p := by
    rw [Scheme.Hom.comp_apply, hq']
    exact morphismRestrict_base_coe emb U₁ ⟨p, hpV⟩
  rw [hq₀, hqp] at key
  exact ⟨i', key.2 hi'⟩

end Hironaka.Resolution
