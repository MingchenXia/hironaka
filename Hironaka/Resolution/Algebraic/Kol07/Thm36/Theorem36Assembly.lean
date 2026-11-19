/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BR
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AdmissiblePairs
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36Reduced
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClauseLocality
import Hironaka.Resolution.Algebraic.Kol07.Thm36.LastIsoTransport
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clauses (1)–(3) of Kollár's Theorem 36 for the resolution functor on the class

The three geometric clauses of [Kol07, Theorem 36] for the resolution functor `BR k X`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) on every member `X` of the class
`IsReducedEquidimensional k X` (reduced, smooth locus over `k` of one relative dimension): the end
result is smooth over `k` (1), the composite `Π : X_r → X` is an isomorphism over the smooth locus
of `X` (2), and the preimage of the singular locus is the support of a simple normal crossing
family of divisors on `X_r` (3).

* `theorem36_BRAffine` — on an AFFINE class member. `BRAffine k X` is the affine resolution
  `BR_affine TA emb` of an admissible embedding of codimension `≥ 2`
  (`exists_admissibleEmbedding_of_codim`) with its globally empty blow-ups deleted
  (`BRAffine_eq_eraseEmpty_BR_affine`); the clauses hold for `BR_affine TA emb`
  (`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36Reduced`: the step by which Kollár's
  `BR` is "defined on (possibly reducible) affine schemes" in the proof of Theorem 36, the
  irreducible components of `X` all absorbed at the one truncation index) and pass along the
  isomorphism of the last stages (`Hironaka.Resolution.Algebraic.Kol07.Thm36.LastIsoTransport`).
  On the empty scheme the clauses hold by locality over the empty cover
  (`Hironaka.Resolution.Algebraic.Kol07.Thm36.ClauseLocality`).
* `theorem36_BR` — on every class member, by the descent of [Kol07, Proposition 37]: the pullback
  of `BR k X` along a member of the finite affine cover is the pullback of the affine value on the
  cover scheme `∐ Uᵢ` along the summand inclusion (`BR_pullback_finiteAffineCover_f`, from
  `BR_pullback_affineCoverDesc` of `Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent`), the
  affine clauses restrict along the summand inclusions, and the clauses are local on the base.
* `BR_smooth_last_of_class`, `BR_isIso_over_smoothLocus_of_class`,
  `BR_exists_snc_support_of_class` — the three clauses separately, for the functor `BRFunctor k`
  (whose sequence at `X` is `BR k X` by definition).
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### The affine assembly: clauses (1)–(3) for `BRAffine X`, `X` an affine class member -/

/-- Clauses (1)–(3) of [Kol07, Theorem 36] for `BRAffine k X` on a possibly reducible affine class
member `X`: the clauses for the affine resolution of an admissible embedding of codimension `≥ 2`
(`smooth_composite_BR_affine_of_class`, `isIso_composite_restrict_smoothLocus_BR_affine_of_class`,
`exists_snc_preimage_singularLocus_BR_affine_of_class`), transported along the isomorphism of last
stages of the deletion of the empty blow-ups (`eraseEmptyLastIso`); on the empty scheme by
locality over the empty cover. -/
theorem theorem36_BRAffine (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsAffine X] (hX : X.IsReducedEquidimensional k) :
    Smooth ((BRAffine k X).composite ≫ (X ↘ Spec (CommRingCat.of k))) ∧
    IsIso ((BRAffine k X).composite ∣_ (X ↘ Spec (CommRingCat.of k)).smoothLocus) ∧
    ∃ F : DivisorFamily (BRAffine k X).last, F.IsSnc ∧
      (F.support : Set (BRAffine k X).last) =
        (BRAffine k X).composite ⁻¹' ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  have : IsNoetherian X := (X ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hred : IsReduced X := hX.1
  obtain ⟨d, hd⟩ := hX.2
  rcases isEmpty_or_nonempty X with hXe | hXn
  · -- the empty scheme: locality over the empty cover
    refine ⟨@smooth_composite_of_forall_pullback PEmpty.{u + 1} X (Spec (CommRingCat.of k))
        (fun i => i.elim) (BRAffine k X) (fun i => i.elim) (fun i => i.elim)
        (fun x => isEmptyElim x) (X ↘ Spec (CommRingCat.of k)) (fun i => i.elim), ?_, ?_⟩
    · exact @isIso_morphismRestrict_composite_of_forall_pullback PEmpty.{u + 1} X
        (fun i => i.elim) (BRAffine k X) (fun i => i.elim) (fun i => i.elim)
        (fun x => isEmptyElim x) _ (fun i => i.elim)
    · exact @exists_snc_support_composite_of_forall_pullback PEmpty.{u + 1} X _
        (fun i => i.elim) (BRAffine k X) (fun i => i.elim) (fun i => i.elim)
        (fun x => isEmptyElim x) _ (fun i => i.elim)
  · obtain ⟨TA, emb, hadm, hcodim⟩ := exists_admissibleEmbedding_of_codim (k := k) X
    have hBR : BRAffine k X = (BR_affine TA emb).eraseEmpty :=
      BRAffine_eq_eraseEmpty_BR_affine k X TA emb hadm
    have h1 := smooth_composite_BR_affine_of_class (d := d) TA emb hadm hXn hcodim
    have h2 := isIso_composite_restrict_smoothLocus_BR_affine_of_class (d := d) TA emb hadm hXn
    have h3 := exists_snc_preimage_singularLocus_BR_affine_of_class (d := d) TA emb hadm hXn hcodim
    rw [hBR]
    refine ⟨smooth_composite_of_lastIso (eraseEmptyLastIso _)
      (eraseEmptyLastIso_hom_comp_composite _) _, ?_, ?_⟩
    · exact isIso_composite_restrict_of_lastIso (eraseEmptyLastIso _)
        (eraseEmptyLastIso_hom_comp_composite _) _
    · exact exists_isSnc_support_eq_preimage_of_lastIso (eraseEmptyLastIso _)
        (eraseEmptyLastIso_hom_comp_composite _) (X ↘ Spec (CommRingCat.of k)) _ h3

/-! ### Descent to `BR` along the finite affine cover, and the three clauses separately -/

/-- The descent of [Kol07, Proposition 37]: the pullback of `BR k X` along a member `Uᵢ → X` of
the finite affine cover is the pullback of the affine value on the cover scheme `∐ Uᵢ` along the
summand inclusion (`BR_pullback_affineCoverDesc` with `ι_comp_affineCoverDesc`). -/
theorem BR_pullback_finiteAffineCover_f (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    haveI : CompactSpace X := compactSpace_of_quasiCompact_over k X
    ∀ i, (BR k X).pullback ((finiteAffineCover X).f i) =
      (BRAffine k (affineCoverScheme X)).pullback
        (Sigma.ι (fun i => (finiteAffineCover X).X i) i) := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  intro i
  rw [← BR_pullback_affineCoverDesc (k := k) X hX, ← pullback_comp, ι_comp_affineCoverDesc]

omit [CharZero k] in
/-- The smooth locus of `X` over `k` pulls back along a member of the finite affine cover to the
pullback along the summand inclusion of the smooth locus of the cover scheme
(`Scheme.Hom.preimage_smoothLocus_eq` twice). -/
theorem preimage_smoothLocus_finiteAffineCover_f (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    haveI : CompactSpace X := compactSpace_of_quasiCompact_over k X
    ∀ i, ((finiteAffineCover X).f i) ⁻¹ᵁ (X ↘ Spec (CommRingCat.of k)).smoothLocus =
      (Sigma.ι (fun i => (finiteAffineCover X).X i) i) ⁻¹ᵁ
        (affineCoverScheme X ↘ Spec (CommRingCat.of k)).smoothLocus := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  intro i
  rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  change (finiteAffineCover X).f i ≫ (X ↘ Spec (CommRingCat.of k)) =
    Sigma.ι (fun i => (finiteAffineCover X).X i) i ≫ affineCoverDesc X ≫
      (X ↘ Spec (CommRingCat.of k))
  rw [← Category.assoc, ι_comp_affineCoverDesc]

/-- Clauses (1)–(3) of [Kol07, Theorem 36] for `BR k X` on every class member: the affine clauses
on the cover scheme `∐ Uᵢ` (`theorem36_BRAffine`) descend along the finite affine cover
(`BR_pullback_finiteAffineCover_f`), the clauses being local on the base and stable under
pullback along open immersions. -/
theorem theorem36_BR (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    Smooth ((BR k X).composite ≫ (X ↘ Spec (CommRingCat.of k))) ∧
    IsIso ((BR k X).composite ∣_ (X ↘ Spec (CommRingCat.of k)).smoothLocus) ∧
    ∃ F : DivisorFamily (BR k X).last, F.IsSnc ∧
      (F.support : Set (BR k X).last) =
        (BR k X).composite ⁻¹' ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  have hc : CompactSpace X := compactSpace_of_quasiCompact_over k X
  have : IsNoetherian X := (X ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  obtain ⟨hA1, hA2, hA3⟩ := theorem36_BRAffine (k := k) (affineCoverScheme X) hX.affineCoverScheme
  have hcov : ∀ x : X, ∃ i w, (finiteAffineCover X).f i w = x :=
    fun x => ⟨(finiteAffineCover X).idx x, (finiteAffineCover X).covers x⟩
  refine ⟨?_, ?_, ?_⟩
  · refine smooth_composite_of_forall_pullback (BR k X) (finiteAffineCover X).f hcov _ fun i => ?_
    rw [BR_pullback_finiteAffineCover_f X hX i, ← ι_comp_affineCoverDesc, Category.assoc]
    exact smooth_composite_pullback_of_isOpenImmersion _ _ _ hA1
  · refine isIso_morphismRestrict_composite_of_forall_pullback (BR k X) (finiteAffineCover X).f
      hcov _ fun i => ?_
    rw [BR_pullback_finiteAffineCover_f X hX i, preimage_smoothLocus_finiteAffineCover_f X i]
    exact isIso_morphismRestrict_pullback_of_isOpenImmersion _ _ _ hA2
  · have := hA1
    refine exists_snc_support_composite_of_forall_pullback (BR k X) (finiteAffineCover X).f
      hcov _ fun i => ?_
    rw [BR_pullback_finiteAffineCover_f X hX i]
    have hloc : ((finiteAffineCover X).f i) ⁻¹'
        ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ =
        (Sigma.ι (fun i => (finiteAffineCover X).X i) i) ⁻¹'
          ((affineCoverScheme X ↘ Spec (CommRingCat.of k)).smoothLocus :
            Set (affineCoverScheme X))ᶜ := by
      rw [Set.preimage_compl, Set.preimage_compl]
      congr 1
      exact congrArg SetLike.coe (preimage_smoothLocus_finiteAffineCover_f X i)
    rw [hloc]
    exact exists_snc_support_pullback_of_isOpenImmersion _ _
      (affineCoverScheme X ↘ Spec (CommRingCat.of k)) _ hA3

/-- Clause (1) of [Kol07, Theorem 36] for the functor `BRFunctor k` on a class member: the end
result is smooth over `k`. -/
theorem BR_smooth_last_of_class (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    Smooth (((BRFunctor k).seq X).composite ≫ (X ↘ Spec (CommRingCat.of k))) :=
  (theorem36_BR X hX).1

/-- Clause (2) of [Kol07, Theorem 36] for the functor `BRFunctor k` on a class member: the
composite is an isomorphism over the smooth locus of `X`. -/
theorem BR_isIso_over_smoothLocus_of_class (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    IsIso (((BRFunctor k).seq X).composite ∣_ (X ↘ Spec (CommRingCat.of k)).smoothLocus) :=
  (theorem36_BR X hX).2.1

/-- Clause (3) of [Kol07, Theorem 36] for the functor `BRFunctor k` on a class member: the
preimage of the singular locus is the support of a simple normal crossing family on the end
result. -/
theorem BR_exists_snc_support_of_class (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) :
    ∃ F : DivisorFamily ((BRFunctor k).seq X).last, F.IsSnc ∧
      (F.support : Set ((BRFunctor k).seq X).last) =
        ((BRFunctor k).seq X).composite ⁻¹'
          ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ :=
  (theorem36_BR X hX).2.2

end Hironaka.Resolution
