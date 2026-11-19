import Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup
import Hironaka.Analytic.Unibranch.OriginalBimeromorphicSourceIso
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneral
import Hironaka.Resolution.HironakaG11IntrinsicRegularOpenImmersion

/-!
# Finite modification calculus for goal G11

General facts about the ORIGINAL modification predicates of `SmoothCentreModification` and the
isomorphism-over predicate of `Resolution`, used to fold finitely many blowups of complex spaces:

* `IsIsoOver.comp`: isomorphisms over `U` and over the preimage of `U` compose; the identity is an
  isomorphism over every open set; the set of an isomorphism-over witness is open;
* `IsIsoOver.mem_intrinsicRegularLocus_iff`: over the open set of an isomorphism-over witness, the
  source and target have the SAME intrinsic regular points (native charts are transported through
  the actual open immersions, in every dimension);
* `IsProperBimeromorphic.surjective`: a proper bimeromorphic map is surjective (its image is
  closed and contains the dense good open set); hence every smooth-centre step and every finite
  modification is surjective, including over the empty space;
* `IsModification.interior_preimage_eq_empty`: a finite modification pulls thin sets back to thin
  sets;
* `IsIdealBlowup.exists_iso`: two ideal blowups of the SAME ideal are isomorphic over the base (the
  universal property), and therefore every smooth-centre blowup is an isomorphism over the
  complement of its centre (`IsSmoothCentreBlowup.isIsoOver_compl_range`), whichever blowup object
  realises it.

No resolution, global embedding, compactness or Kähler hypothesis is used.
Blueprint: `hironaka-g11-resume-modification-calculus.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

open Hironaka HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11IntrinsicRegularOpenImmersion

noncomputable section

private theorem openImmersion_lift' {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  let : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

/-- The set over which a morphism is an isomorphism is open (it is the range of an open
immersion). -/
theorem IsIsoOver.isOpen {X Y : SourceReducedComplexSpace} {F : Y ⟶ X} {U : Set X.obj.left}
    (hF : IsIsoOver F U) : IsOpen U := by
  obtain ⟨V, j, _hj, _hjr, hjF, hjFr⟩ := hF
  rw [← hjFr]
  exact hjF.base_open.isOpen_range

/-- The identity is an isomorphism over every open set. -/
theorem IsIsoOver.id_of_isOpen (X : SourceReducedComplexSpace) {U : Set X.obj.left}
    (hU : IsOpen U) : IsIsoOver (𝟙 X) U := by
  let Q : Opens X.obj.left := ⟨U, hU⟩
  let j := X.obj.left.ofRestrict Q.isOpenEmbedding
  have hj : LocallyRingedSpace.IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  have hjj : j ≫ (𝟙 X : X ⟶ X).hom.left = j := Category.comp_id j
  have hj' : LocallyRingedSpace.IsOpenImmersion (j ≫ (𝟙 X : X ⟶ X).hom.left) := by
    rw [hjj]
    exact hj
  refine ⟨X.obj.left.restrict Q.isOpenEmbedding, j, hj, ?_, hj', ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  · rw [hjj]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩

/-- **Composition of isomorphisms over open sets.** If `g` is an isomorphism over `U` and `f` is
an isomorphism over `g⁻¹ U`, then `f ≫ g` is an isomorphism over `U`. -/
theorem IsIsoOver.comp {X Y Z : SourceReducedComplexSpace} {f : Z ⟶ Y} {g : Y ⟶ X}
    {U : Set X.obj.left} (hg : IsIsoOver g U) (hf : IsIsoOver f (g.hom.left.base ⁻¹' U)) :
    IsIsoOver (f ≫ g) U := by
  obtain ⟨V, j, hj, hjr, hjg, hjgr⟩ := hg
  obtain ⟨V', j', hj', hj'r, hj'f, hj'fr⟩ := hf
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let : LocallyRingedSpace.IsOpenImmersion (j ≫ g.hom.left) := hjg
  let : LocallyRingedSpace.IsOpenImmersion (j' ≫ f.hom.left) := hj'f
  have hr : range (j' ≫ f.hom.left).base ⊆ range j.base := by
    intro x hx
    rw [hj'fr] at hx
    rw [hjr]
    exact hx
  let k := LocallyRingedSpace.IsOpenImmersion.lift j (j' ≫ f.hom.left) hr
  let : LocallyRingedSpace.IsOpenImmersion k := openImmersion_lift' j (j' ≫ f.hom.left) hr
  have hkj : k ≫ j = j' ≫ f.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j (j' ≫ f.hom.left) hr
  have hksurj : ∀ v : V, ∃ w : V', k.base w = v := by
    intro v
    have hv : j.base v ∈ range (j' ≫ f.hom.left).base := by
      rw [hj'fr, ← hjr]
      exact ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := hv
    refine ⟨w, hj.base_open.injective ?_⟩
    have hh := congrArg (fun F => F.base w) hkj
    exact hh.trans hw
  have hcomp : j' ≫ (f ≫ g).hom.left = k ≫ (j ≫ g.hom.left) := by
    change j' ≫ (f.hom.left ≫ g.hom.left) = _
    rw [← Category.assoc, ← hkj, Category.assoc]
  refine ⟨V', j', hj', hj'r, ?_, ?_⟩
  · rw [hcomp]
    infer_instance
  · rw [hcomp]
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      rw [← hjgr]
      exact ⟨k.base w, rfl⟩
    · intro hx
      rw [← hjgr] at hx
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, hw⟩ := hksurj v
      refine ⟨w, ?_⟩
      change (j ≫ g.hom.left).base (k.base w) = _
      rw [hw]

/-- **Regular points are transported through an isomorphism over `U`.** Over `U`, a point of the
source is an intrinsic regular point exactly when its image is one (native charts in every
dimension, through the actual open immersions of the witness). -/
theorem IsIsoOver.mem_intrinsicRegularLocus_iff {X Y : SourceReducedComplexSpace} {F : Y ⟶ X}
    {U : Set X.obj.left} (hF : IsIsoOver F U) {y : Y.obj.left} (hy : F.hom.left.base y ∈ U) :
    y ∈ intrinsicRegularLocus Y.obj ↔ F.hom.left.base y ∈ intrinsicRegularLocus X.obj := by
  obtain ⟨V, j, hj, hjr, hjF, _⟩ := hF
  have hyr : y ∈ range j.base := by
    rw [hjr]
    exact hy
  obtain ⟨v, rfl⟩ := hyr
  have hcomm : j ≫ Y.obj.hom = (j ≫ F.hom.left) ≫ X.obj.hom := by
    rw [Category.assoc, Over.w F.hom]
  exact mem_intrinsicRegularLocus_iff_of_openImmersions j (j ≫ F.hom.left) hj hjF hcomm v

theorem IsIsoOver.preimage_inter_intrinsicRegularLocus {X Y : SourceReducedComplexSpace}
    {F : Y ⟶ X} {U : Set X.obj.left} (hF : IsIsoOver F U) :
    F.hom.left.base ⁻¹' (U ∩ intrinsicRegularLocus X.obj) =
      F.hom.left.base ⁻¹' U ∩ intrinsicRegularLocus Y.obj := by
  ext y
  constructor
  · rintro ⟨hyU, hyR⟩
    exact ⟨hyU, (hF.mem_intrinsicRegularLocus_iff hyU).mpr hyR⟩
  · rintro ⟨hyU, hyR⟩
    exact ⟨hyU, (hF.mem_intrinsicRegularLocus_iff hyU).mp hyR⟩

/-- An isomorphism over the regular locus maps the preimage of the regular locus into the
regular locus of the source. -/
theorem IsIsoOver.preimage_intrinsicRegularLocus_subset {X Y : SourceReducedComplexSpace}
    {F : Y ⟶ X} {U : Set X.obj.left} (hF : IsIsoOver F U)
    (hU : intrinsicRegularLocus X.obj ⊆ U) :
    F.hom.left.base ⁻¹' intrinsicRegularLocus X.obj ⊆ intrinsicRegularLocus Y.obj :=
  fun _ hy => (hF.mem_intrinsicRegularLocus_iff (hU hy)).mpr hy

/-- **A proper bimeromorphic map is surjective**: its image is closed and contains the dense
complement of its thin exceptional set. -/
theorem IsProperBimeromorphic.surjective {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsProperBimeromorphic p) : Function.Surjective p.hom.left.base := by
  obtain ⟨hprop, Z, _hZa, hZt, _hpre, V, j, _hj, _hjr, _hjp, hjpr⟩ := hp
  have hclosed : IsClosed (range p.hom.left.base) := hprop.isClosedMap.isClosed_range
  have hsub : Zᶜ ⊆ range p.hom.left.base := by
    rw [← hjpr]
    rintro _ ⟨v, rfl⟩
    exact ⟨j.base v, rfl⟩
  have hdense : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp hZt
  have hcl : closure (range p.hom.left.base) = univ := (hdense.mono hsub).closure_eq
  rw [hclosed.closure_eq] at hcl
  exact Set.range_eq_univ.mp hcl

end

end Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

namespace Hironaka.Analytic.Unibranch.SmoothCentreModification

open Hironaka HironakaSingularModuleSheafStalk
  SourceReducedComplexSpace

noncomputable section

/-- **Uniqueness of ideal blowups.** Two ideal blowups of the SAME ideal of `X` are isomorphic
over `X`, by their universal properties. -/
theorem IsIdealBlowup.exists_iso {X Y Y' : SourceReducedComplexSpace} {p : Y ⟶ X}
    {p' : Y' ⟶ X} {B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf)}
    {b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)}
    (hp : IsIdealBlowup p B b) (hp' : IsIdealBlowup p' B b) :
    ∃ e : Y ≅ Y', e.hom ≫ p' = p := by
  obtain ⟨L, hL, _⟩ := hp'.2 Y p hp.1
  obtain ⟨L', hL', _⟩ := hp.2 Y' p' hp'.1
  have h₁ : L ≫ L' = 𝟙 Y := by
    obtain ⟨M, _, hM⟩ := hp.2 Y p hp.1
    have ha := hM (L ≫ L') (show (L ≫ L') ≫ p = p by rw [Category.assoc, hL', hL])
    have hb := hM (𝟙 Y) (Category.id_comp p)
    exact ha.trans hb.symm
  have h₂ : L' ≫ L = 𝟙 Y' := by
    obtain ⟨M, _, hM⟩ := hp'.2 Y' p' hp'.1
    have ha := hM (L' ≫ L) (show (L' ≫ L) ≫ p' = p' by rw [Category.assoc, hL, hL'])
    have hb := hM (𝟙 Y') (Category.id_comp p')
    exact ha.trans hb.symm
  exact ⟨⟨L, L', h₁, h₂⟩, hL⟩

/-- **Every smooth-centre blowup is an isomorphism off its centre**, whichever blowup object
realises it: it is isomorphic over `X` to the constructed blowup of the same intrinsic centre
ideal, which is an isomorphism over the complement of the centre. -/
theorem IsSmoothCentreBlowup.isIsoOver_compl_range {X Y S : SourceReducedComplexSpace}
    {p : Y ⟶ X} {i : S ⟶ X} (h : IsSmoothCentreBlowup p i) :
    IsIsoOver p (range i.hom.left.base)ᶜ := by
  obtain ⟨hS, hi, hstalk, hC, hthin, hIdeal, _hPB⟩ := h
  obtain ⟨Y₀, p₀, hStep₀, _, _, hIso₀⟩ :=
    OriginalSmoothCentreBlowup.exists_smoothCentreBlowup X S i hS hi hstalk hC hthin
  obtain ⟨e, he⟩ := hIdeal.exists_iso hStep₀.2.2.2.2.2.1
  rw [← he]
  exact hIso₀.precomp_iso e

theorem IsSmoothCentreBlowup.surjective {X Y S : SourceReducedComplexSpace}
    {p : Y ⟶ X} {i : S ⟶ X} (h : IsSmoothCentreBlowup p i) :
    Function.Surjective p.hom.left.base :=
  h.2.2.2.2.2.2.surjective

theorem IsSmoothCentreStep.surjective {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (h : IsSmoothCentreStep p) : Function.Surjective p.hom.left.base := by
  obtain ⟨S, i, hi⟩ := h
  exact hi.surjective

theorem IsSmoothCentreStep.isProperBimeromorphic {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (h : IsSmoothCentreStep p) : IsProperBimeromorphic p := by
  obtain ⟨S, i, hi⟩ := h
  exact hi.2.2.2.2.2.2

/-- **A finite modification is surjective**, including over the empty space. -/
theorem IsModification.surjective {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsModification p) : Function.Surjective p.hom.left.base := by
  induction hp with
  | id => exact Function.surjective_id
  | cons f g hf _ ih => exact ih.comp hf.surjective

/-- A finite modification pulls thin sets back to thin sets. -/
theorem IsModification.interior_preimage_eq_empty {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsModification p) :
    ∀ {A : Set X.obj.left}, interior A = ∅ → interior (p.hom.left.base ⁻¹' A) = ∅ := by
  induction hp with
  | id => exact fun hA => hA
  | cons f g hf _ ih =>
    intro A hA
    obtain ⟨_, E, _, _, hpre, hiso⟩ := hf.isProperBimeromorphic
    have h := IsIsoOver.interior_preimage_eq_empty (F := f) hiso hpre (ih hA)
    exact h

/-- A finite modification has dense preimage of every dense set with thin complement. -/
theorem IsModification.dense_preimage {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsModification p) {A : Set X.obj.left} (hA : interior Aᶜ = ∅) :
    Dense (p.hom.left.base ⁻¹' A) := by
  have h := hp.interior_preimage_eq_empty hA
  rw [preimage_compl] at h
  simpa only [compl_compl] using interior_eq_empty_iff_dense_compl.mp h

end

end Hironaka.Analytic.Unibranch.SmoothCentreModification
