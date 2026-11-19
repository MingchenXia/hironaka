import Hironaka.Analytic.Unibranch.HironakaG11ModificationCalculus
import Hironaka.Analytic.Unibranch.OriginalLocallySmoothAnalyticCentreBlowup
import Hironaka.Analytic.Unibranch.OriginalSingularContainedCentreThinness

/-!
# Finite blowup sequences with centres in the singular locus (goal G11)

Goal G11 (`g11:general`) asks, for a compact reduced complex space `X`, for a finite sequence of
blowups `X_k → ⋯ → X_1 → X_0 = X`, the `j`-th along a smooth closed subspace `C_j ⊂ X_j` contained
in the singular locus of `X_j`, with `X_k` smooth. This file introduces the ORIGINAL predicate
`IsSingularCentreModification` for such sequences of full morphisms of complex spaces (a finite
modification of `SmoothCentreModification` whose every centre lies in the intrinsic singular locus
of the space being blown up) and proves its general calculus:

* it is a finite modification, closed under composition, surjective (also for empty `X`), proper,
  with compact source over a compact base;
* `isIsoOver_intrinsicRegularLocus`: it is an isomorphism over the regular locus of the ORIGINAL
  space `X`; the preimage of the regular locus of `X` consists of regular points and is dense;
* `isProperBimeromorphic`: it is proper bimeromorphic with exceptional set the intrinsic singular
  locus of `X`; with smooth source it is a resolution (`IsResolution`).

`HasSingularCentreResolution X` is the conclusion of goal G11 for one space;
`HasSingularCentreResolution.exists_endpoint` derives from it the full endpoint (resolution,
surjectivity, properness, compactness, isomorphism over the original regular locus, density),
`hasSingularCentreResolution_of_isSmooth` is the already-smooth case (including empty `X`), and
`HasSingularCentreResolution.of_comp` is the induction step: a singular-centre modification of `X`
whose source has a resolution gives one of `X`. The statement of G11 itself,
`CompactSingularCentreResolution`, is recorded as a proposition; it is NOT proved here (the
canonical driver producing compatible centres is not formalized).

Blueprint: `hironaka-g11-resume-modification-calculus.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11SingularCentreModification

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification OriginalIntrinsicSingularLocus
  OriginalAnalyticClosedSubspaceSmoothCentres

noncomputable section

/-- A blowup step along a smooth closed centre contained in the intrinsic singular locus of the
space being blown up. -/
def IsSingularCentreStep {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) : Prop :=
  ∃ (S : SourceReducedComplexSpace) (i : S ⟶ X), IsSmoothCentreBlowup p i ∧
    range i.hom.left.base ⊆ intrinsicSingularLocus X.obj

/-- Finite compositions of blowups with smooth centres in the singular loci of the successive
spaces (the sequences of `g11:general`), on FULL ORIGINAL morphisms. -/
inductive IsSingularCentreModification : {X Y : SourceReducedComplexSpace} → (Y ⟶ X) → Prop
  | id (X : SourceReducedComplexSpace) : IsSingularCentreModification (𝟙 X)
  | cons {X Y Z : SourceReducedComplexSpace} (f : Z ⟶ Y) (g : Y ⟶ X)
      (hf : IsSingularCentreStep f) (hg : IsSingularCentreModification g) :
      IsSingularCentreModification (f ≫ g)

theorem IsSingularCentreStep.isSmoothCentreStep {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (h : IsSingularCentreStep p) : IsSmoothCentreStep p := by
  obtain ⟨S, i, hi, _⟩ := h
  exact ⟨S, i, hi⟩

/-- A singular-centre step is an isomorphism over the regular locus of its target. -/
theorem IsSingularCentreStep.isIsoOver_intrinsicRegularLocus {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (h : IsSingularCentreStep p) : IsIsoOver p (intrinsicRegularLocus X.obj) := by
  obtain ⟨S, i, hi, hsub⟩ := h
  apply hi.isIsoOver_compl_range.of_isOpen_subset (isOpen_intrinsicRegularLocus X.obj)
  intro x hx hxC
  exact hsub hxC hx

theorem IsSingularCentreStep.isSingularCentreModification {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (h : IsSingularCentreStep p) : IsSingularCentreModification p := by
  simpa only [Category.comp_id] using IsSingularCentreModification.cons p (𝟙 X) h (.id X)

theorem IsSingularCentreModification.toIsModification {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsSingularCentreModification p) : IsModification p := by
  induction hp with
  | id => exact .id _
  | cons f g hf _ ih => exact .cons f g hf.isSmoothCentreStep ih

theorem IsSingularCentreModification.comp {X Y Z : SourceReducedComplexSpace} {f : Z ⟶ Y}
    {g : Y ⟶ X} (hf : IsSingularCentreModification f) (hg : IsSingularCentreModification g) :
    IsSingularCentreModification (f ≫ g) := by
  revert X
  induction hf with
  | id => intro X g hg; simpa only [Category.id_comp] using hg
  | cons f g hf _ ih =>
    intro X h hh
    simpa only [Category.assoc] using IsSingularCentreModification.cons f (g ≫ h) hf (ih hh)

theorem IsSingularCentreModification.surjective {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsSingularCentreModification p) : Function.Surjective p.hom.left.base :=
  hp.toIsModification.surjective

theorem IsSingularCentreModification.isProperMap {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsSingularCentreModification p) : IsProperMap p.hom.left.base :=
  hp.toIsModification.isProperMap

theorem IsSingularCentreModification.source_compact {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsSingularCentreModification p) [CompactSpace X.obj.left] :
    CompactSpace Y.obj.left :=
  hp.toIsModification.source_compact

/-- **A singular-centre modification is an isomorphism over the regular locus of the ORIGINAL
space.** By induction: the earlier composite `g` is an isomorphism over `Reg X`, so the points of
`g⁻¹ Reg X` are regular points of the intermediate space, which the next centre avoids. -/
theorem IsSingularCentreModification.isIsoOver_intrinsicRegularLocus
    {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} (hp : IsSingularCentreModification p) :
    IsIsoOver p (intrinsicRegularLocus X.obj) := by
  induction hp with
  | id => exact IsIsoOver.id_of_isOpen _ (isOpen_intrinsicRegularLocus _)
  | cons f g hf _ ih =>
    apply IsIsoOver.comp ih
    apply hf.isIsoOver_intrinsicRegularLocus.of_isOpen_subset
      ((isOpen_intrinsicRegularLocus _).preimage g.hom.left.base.hom.continuous)
    intro y hy
    exact (ih.mem_intrinsicRegularLocus_iff hy).mpr hy

/-- The preimage of the original regular locus consists of regular points of the source. -/
theorem IsSingularCentreModification.preimage_intrinsicRegularLocus_subset
    {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} (hp : IsSingularCentreModification p) :
    p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj ⊆ intrinsicRegularLocus Y.obj :=
  hp.isIsoOver_intrinsicRegularLocus.preimage_intrinsicRegularLocus_subset subset_rfl

/-- The singular points of the source lie over singular points of the ORIGINAL space. -/
theorem IsSingularCentreModification.intrinsicSingularLocus_subset_preimage
    {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} (hp : IsSingularCentreModification p) :
    intrinsicSingularLocus Y.obj ⊆ p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj :=
  fun _ hy hreg => hy (hp.preimage_intrinsicRegularLocus_subset hreg)

/-- The preimage of the original singular locus is thin. -/
theorem IsSingularCentreModification.interior_preimage_intrinsicSingularLocus
    {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} (hp : IsSingularCentreModification p) :
    interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ :=
  hp.toIsModification.interior_preimage_eq_empty (interior_intrinsicSingularLocus_eq_empty X)

/-- The preimage of the original regular locus is dense in the source. -/
theorem IsSingularCentreModification.dense_preimage_intrinsicRegularLocus
    {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} (hp : IsSingularCentreModification p) :
    Dense (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) :=
  hp.toIsModification.dense_preimage (interior_intrinsicSingularLocus_eq_empty X)

/-- **A singular-centre modification is proper bimeromorphic**, with exceptional set the intrinsic
singular locus of the ORIGINAL space. -/
theorem IsSingularCentreModification.isProperBimeromorphic {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsSingularCentreModification p) : IsProperBimeromorphic p := by
  refine ⟨hp.isProperMap, intrinsicSingularLocus X.obj, isAnalyticSubset_intrinsicSingularLocus X,
    interior_intrinsicSingularLocus_eq_empty X, hp.interior_preimage_intrinsicSingularLocus, ?_⟩
  have hc : (intrinsicSingularLocus X.obj)ᶜ = intrinsicRegularLocus X.obj := by
    show (intrinsicRegularLocus X.obj)ᶜᶜ = _
    exact compl_compl _
  rw [hc]
  exact hp.isIsoOver_intrinsicRegularLocus

/-- With smooth source, a singular-centre modification is a resolution (`def:primdiv`). -/
theorem IsSingularCentreModification.isResolution {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsSingularCentreModification p) (hY : Y.IsSmooth) : IsResolution p :=
  ⟨hY, hp.isProperBimeromorphic⟩

/-- **One step of the G11 sequence from ordinary centre geometry.** A thin analytic subset `S` of
the intrinsic singular locus which is locally a closed submanifold of the ambient charts is the
centre of an actual singular-centre blowup step, an isomorphism off `S`. -/
theorem exists_isSingularCentreStep_of_local_smooth_centres
    (X : SourceReducedComplexSpace) (S : Set X.obj.left) (hS : X.IsAnalyticSubset S)
    (hSing : S ⊆ intrinsicSingularLocus X.obj)
    (hGeom : ∀ (x : X.obj.left), x ∈ S →
      ∃ (e : LocalEmbedding X) (O : Opens e.ambient) (C : Set O)
        (_hC : IsClosedSubmanifold e.dim C)
        (_hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier)
        (d : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier)),
        (givenWindowMorphism e O).hom.left.base d = x ∧
        (givenWindowMorphism e O).hom.left.base ⁻¹' S =
          (Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSingularCentreStep p ∧ IsSingularCentreModification p ∧
      Function.Surjective p.hom.left.base ∧ IsIsoOver p Sᶜ := by
  have hthin := OriginalSingularContainedCentreThinness.interior_eq_empty_of_subset_intrinsicSingularLocus
    X S hSing
  obtain ⟨Y, p, hstep, _hmod, hsurj, hiso⟩ :=
    OriginalLocallySmoothAnalyticCentreBlowup.exists_smoothCentreBlowup_of_local_smooth_centres
      X S hS hthin hGeom
  have hrange := OriginalAnalyticClosedSubspace.inclusion_range X S hS
  have hsing : IsSingularCentreStep p :=
    ⟨_, OriginalAnalyticClosedSubspace.inclusion X S hS, hstep, by rw [hrange]; exact hSing⟩
  exact ⟨Y, p, hsing, hsing.isSingularCentreModification, hsurj, hiso⟩

/-! ### The G11 endpoint -/

/-- The conclusion of goal G11 (`g11:general`) for one space `X`: a finite sequence of blowups with
smooth centres contained in the singular loci of the successive spaces, with smooth final space. -/
def HasSingularCentreResolution (X : SourceReducedComplexSpace) : Prop :=
  ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X), IsSingularCentreModification p ∧ Y.IsSmooth

/-- Goal G11 (`g11:general`), as a proposition: every compact reduced complex space has a
resolution by finitely many blowups with smooth centres in the singular locus. This is the
statement only; it is NOT proved in this file. -/
def CompactSingularCentreResolution : Prop :=
  ∀ (X : SourceReducedComplexSpace), CompactSpace X.obj.left → HasSingularCentreResolution X

/-- **The full G11 endpoint follows from the core statement.** The composite is a finite
modification and a resolution, surjective and proper, an isomorphism over the regular locus of
the ORIGINAL space, with dense preimage of that regular locus and thin preimage of the singular
locus; its source is compact when `X` is. -/
theorem HasSingularCentreResolution.exists_endpoint {X : SourceReducedComplexSpace}
    (h : HasSingularCentreResolution X) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSingularCentreModification p ∧ IsModification p ∧ Y.IsSmooth ∧ IsResolution p ∧
      Function.Surjective p.hom.left.base ∧ IsProperMap p.hom.left.base ∧
      IsIsoOver p (intrinsicRegularLocus X.obj) ∧
      Dense (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ ∧
      (CompactSpace X.obj.left → CompactSpace Y.obj.left) := by
  obtain ⟨Y, p, hp, hY⟩ := h
  exact ⟨Y, p, hp, hp.toIsModification, hY, hp.isResolution hY, hp.surjective, hp.isProperMap,
    hp.isIsoOver_intrinsicRegularLocus, hp.dense_preimage_intrinsicRegularLocus,
    hp.interior_preimage_intrinsicSingularLocus, fun _ => hp.source_compact⟩

/-- The already-smooth case: the identity (zero blowups). -/
theorem hasSingularCentreResolution_of_isSmooth {X : SourceReducedComplexSpace}
    (hX : X.IsSmooth) : HasSingularCentreResolution X :=
  ⟨X, 𝟙 X, .id X, hX⟩

/-- The empty complex space is smooth. -/
theorem isSmooth_of_isEmpty (X : SourceReducedComplexSpace) [IsEmpty X.obj.left] :
    X.IsSmooth :=
  fun x => isEmptyElim x

/-- The empty case of G11: the identity resolves the empty space. -/
theorem hasSingularCentreResolution_of_isEmpty (X : SourceReducedComplexSpace)
    [IsEmpty X.obj.left] : HasSingularCentreResolution X :=
  hasSingularCentreResolution_of_isSmooth (isSmooth_of_isEmpty X)

/-- An isolated point of a complex space is an intrinsic regular point: the regular locus is
dense, so it meets the open singleton. -/
theorem mem_intrinsicRegularLocus_of_isOpen_singleton (X : SourceReducedComplexSpace)
    {x : X.obj.left} (hx : IsOpen ({x} : Set X.obj.left)) : x ∈ intrinsicRegularLocus X.obj := by
  obtain ⟨y, hyx, hy⟩ :=
    (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus X).inter_open_nonempty {x} hx
      (singleton_nonempty x)
  rw [mem_singleton_iff.mp hyx] at hy
  exact hy

/-- A discrete (zero-dimensional) complex space is smooth. -/
theorem isSmooth_of_discreteTopology (X : SourceReducedComplexSpace)
    [DiscreteTopology X.obj.left] : X.IsSmooth :=
  (isSmooth_iff_intrinsicSingularLocus_eq_empty X).mpr
    (eq_empty_iff_forall_notMem.mpr fun _ hx =>
      hx (mem_intrinsicRegularLocus_of_isOpen_singleton X (isOpen_discrete _)))

/-- The zero-dimensional case of G11: the identity resolves a discrete space. -/
theorem hasSingularCentreResolution_of_discreteTopology (X : SourceReducedComplexSpace)
    [DiscreteTopology X.obj.left] : HasSingularCentreResolution X :=
  hasSingularCentreResolution_of_isSmooth (isSmooth_of_discreteTopology X)

/-- **Induction step for G11.** A singular-centre modification of `X` whose source has a
resolution gives a resolution of `X`. -/
theorem HasSingularCentreResolution.of_comp {X Z : SourceReducedComplexSpace} {q : Z ⟶ X}
    (hq : IsSingularCentreModification q) (h : HasSingularCentreResolution Z) :
    HasSingularCentreResolution X := by
  obtain ⟨Y, p, hp, hY⟩ := h
  exact ⟨Y, p ≫ q, hp.comp hq, hY⟩

end

end Hironaka.Analytic.Unibranch.HironakaG11SingularCentreModification
