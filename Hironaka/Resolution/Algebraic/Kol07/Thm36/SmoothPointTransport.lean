/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus
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
# Transport of the restricted centres between two smooth closed points

Kollár's localisation argument [Kol07, 4.2; Theorem 27, proof] says that "any two smooth points of
`X` are étale equivalent" as embedded points, so that a property transported by the functoriality
of the principalization sequence holds at one smooth point iff it holds at another.
`Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus` uses this for an integral `X` with
the generic point as the reference point. This module states the transport itself, for a scheme
`X` whose smooth locus over `k` is smooth of ONE relative dimension `d` (the equidimensionality of
the inputs of [Kol07, Theorem 36], for a reduced `X`: all components have dimension `d`), and the
consequence that one smooth point over which no restricted centre has a point suffices:

* `restrictedCenterHasPointOver_iff_of_mem_smoothLocus`: for two closed points `x, x'` of the
  smooth locus, the restricted centres `Z_i ∩ X̄_i` of the truncated run have a point over `x` iff
  they have one over `x'`. The pair of embedded points is made étale equivalent by the two-point
  étale pair of `Hironaka.Scheme.Smooth.TwoPointEtalePair` on the open
  `U₁ = A ∖ emb(X ∖ X^{ns})` of the ambient, over which `X ∩ U₁ = X^{ns}` is smooth of relative
  dimension `d`, and the pair is completed to surjective étale maps
  (`restrictedCenterHasPointOver_iff_of_etale_pair`).
* `not_restrictedCenterHasPointOver_of_mem_smoothLocus_of_exists`: if some point of the smooth
  locus has no restricted centre over it, no point of the smooth locus has (closed points of the
  Jacobson `X` meet every nonempty locally closed subset, and the set of points over which some
  restricted centre has a point is closed).

Both are stated for an arbitrary assignment `F` of a blow-up sequence to every triple that is
functorial under smooth surjections (the hypothesis `hfun`), and applied to `F := BP` in
`Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex`. The hypothesis on the smooth locus
replaces the integrality of `X` in `not_restrictedCenterHasPointOver_of_mem_smoothLocus`.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Hironaka Scheme BlowUpSequence
  TopologicalSpace

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

variable (TA : Triple k) {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  (emb : X ⟶ TA.X.left) [IsClosedImmersion emb] [emb.IsOver (Spec (CommRingCat.of k))]

/-- Two smooth closed points see the same restricted centres [Kol07, 4.2; Theorem 27, proof]: for
a scheme `X` embedded in the ambient of the triple `TA` (empty boundary, ideal the ideal of `X`)
whose smooth locus over `k` is smooth of one relative dimension `d`, an assignment `F` of blow-up
sequences to triples that is functorial under smooth surjections (`hfun`), and two closed points
`x, x'` of the smooth locus of `X`, the restricted centres of the truncation `(F TA).take j` have a
point over `emb x` iff they have one over `emb x'`. The two embedded points are étale equivalent
through the two-point étale pair on the open `U₁ = A ∖ emb(X ∖ X^{ns})` of the ambient
(`exists_etale_pair_of_isClosedImmersion`), and the pair is completed to surjective étale maps
(`restrictedCenterHasPointOver_iff_of_etale_pair`). -/
theorem restrictedCenterHasPointOver_iff_of_mem_smoothLocus (hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I) {d : ℕ}
    [SmoothOfRelativeDimension d
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))]
    (F : ∀ T : Triple k, BlowUpSequence T.X.left)
    (hfun : ∀ (T' : Triple k) (g : T'.X.left ⟶ TA.X.left) [Smooth g], Function.Surjective g →
      T'.IsPullbackOf TA g → F T' = (F TA).pullback g)
    (j : ℕ) {x x' : X} (hx : x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus)
    (hx' : x' ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus)
    (hxc : IsClosed ({x} : Set X)) (hx'c : IsClosed ({x'} : Set X))
    (i : Fin ((F TA).take j).length) :
    RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x) ↔
      RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x') := by
  classical
  -- the ambient open `U₁ = A ∖ emb(X ∖ X^{ns})`, with `emb⁻¹(U₁) = X^{ns}`
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
  have hpre : emb ⁻¹ᵁ U₁ = (X ↘ Spec (CommRingCat.of k)).smoothLocus :=
    Opens.ext (Set.ext fun z => hmemU₁ z)
  -- the restriction `emb ∣_ U₁ : X^{ns} ⟶ U₁`, a closed immersion with kernel `TA.I.comap U₁.ι`
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
  -- `X^{ns}` is smooth over `k` of relative dimension `d`, the hypothesis
  have hcomp : (emb ∣_ U₁) ≫ (U₁.ι ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) =
      (emb ⁻¹ᵁ U₁).ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, HomIsOver.comp_over]
  have : SmoothOfRelativeDimension d
      ((emb ∣_ U₁) ≫ (U₁.ι ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))) := by
    rw [hcomp, hpre]
    infer_instance
  -- the two closed points of `U₁`
  have hxV : x ∈ emb ⁻¹ᵁ U₁ := (hmemU₁ _).2 hx
  have hx'V : x' ∈ emb ⁻¹ᵁ U₁ := (hmemU₁ _).2 hx'
  have hcl : ∀ (z : X) (hz : z ∈ emb ⁻¹ᵁ U₁), IsClosed ({z} : Set X) →
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
      n d (emb ∣_ U₁) (x := ⟨x, hxV⟩) (x' := ⟨x', hx'V⟩) (hcl x hxV hxc) (hcl x' hx'V hx'c)
  -- compose with the inclusion of `U₁` and transport
  have hIψ' : TA.I.comap (ψ₁ ≫ U₁.ι) = TA.I.comap (ψ₁' ≫ U₁.ι) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hker, hIψ]
  have hover' : (ψ₁ ≫ U₁.ι) ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) =
      (ψ₁' ≫ U₁.ι) ≫ (TA.X.left ↘ Spec (CommRingCat.of k)) := by
    rw [Category.assoc, Category.assoc]
    exact hover
  have key := restrictedCenterHasPointOver_iff_of_etale_pair F TA hfun hE j (ψ₁ ≫ U₁.ι)
    (ψ₁' ≫ U₁.ι) hover' hIψ' q i
  have hq₀ : (ψ₁ ≫ U₁.ι) q = emb x := by
    rw [Scheme.Hom.comp_apply, hq]
    exact morphismRestrict_base_coe emb U₁ ⟨x, hxV⟩
  have hqp : (ψ₁' ≫ U₁.ι) q = emb x' := by
    rw [Scheme.Hom.comp_apply, hq']
    exact morphismRestrict_base_coe emb U₁ ⟨x', hx'V⟩
  rwa [hq₀, hqp] at key

/-- One smooth point suffices [Kol07, 4.2; Theorem 27, proof]: for `X` as in
`restrictedCenterHasPointOver_iff_of_mem_smoothLocus`, if some point `y` of the smooth locus has
no restricted centre of the truncation `(F TA).take j` over it, then no point of the smooth locus
has. The set of points over which some restricted centre has a point is closed
(`isClosed_setOf_restrictedCenterHasPointOver`); closed points of the Jacobson `X` lie in the
nonempty locally closed sets `X^{ns} ∖ B ∋ y` and, for a contradiction, `B ∩ X^{ns}`, and the two
closed points see the same restricted centres. -/
theorem not_restrictedCenterHasPointOver_of_mem_smoothLocus_of_exists (hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I) {d : ℕ}
    [SmoothOfRelativeDimension d
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus.ι ≫ (X ↘ Spec (CommRingCat.of k)))]
    (F : ∀ T : Triple k, BlowUpSequence T.X.left)
    (hfun : ∀ (T' : Triple k) (g : T'.X.left ⟶ TA.X.left) [Smooth g], Function.Surjective g →
      T'.IsPullbackOf TA g → F T' = (F TA).pullback g)
    (j : ℕ)
    (ha : ∃ y ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus,
      ∀ i, ¬ RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb y))
    {x : X} (hx : x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus)
    (i : Fin ((F TA).take j).length) :
    ¬ RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x) := by
  classical
  have : IsLocallyNoetherian X := (X ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  -- the closed locus `B` of the points over which some restricted centre has a point
  have hB : IsClosed
      {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)} := by
    have := isClosed_setOf_restrictedCenterHasPointOver ((F TA).take j) emb
    rwa [hI] at this
  obtain ⟨y, hy, hyB⟩ := ha
  have hyB' : y ∉ {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)} :=
    fun ⟨i, h⟩ => hyB i h
  -- closed points: the base point `x₀ ∈ X^{ns} ∖ B`, and, for a contradiction, `p ∈ B ∩ X^{ns}`
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of k))
  obtain ⟨x₀, ⟨hx₀U, hx₀B⟩, hx₀c⟩ := nonempty_inter_closedPoints (X := X)
    (Z := ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X) ∩
      {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)}ᶜ)
    ⟨y, hy, hyB'⟩
    ((X ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen.isLocallyClosed.inter
      hB.isOpen_compl.isLocallyClosed)
  intro hxi
  obtain ⟨p, ⟨hpB, hpU⟩, hpc⟩ := nonempty_inter_closedPoints (X := X)
    (Z := {x : X | ∃ i, RestrictedCenterHasPointOver ((F TA).take j) TA.I i (emb x)} ∩
      ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X))
    ⟨x, ⟨i, hxi⟩, hx⟩
    (hB.isLocallyClosed.inter (X ↘ Spec (CommRingCat.of k)).smoothLocus.isOpen.isLocallyClosed)
  apply hx₀B
  obtain ⟨i', hi'⟩ := hpB
  exact ⟨i', (restrictedCenterHasPointOver_iff_of_mem_smoothLocus TA emb hE hI (d := d) F hfun j
    hx₀U hpU hx₀c hpc i').2 hi'⟩

end Hironaka.Resolution
