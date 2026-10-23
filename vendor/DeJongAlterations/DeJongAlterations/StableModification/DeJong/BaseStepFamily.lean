import DeJongAlterations.StableModification.DeJong.BaseStepFibers
import DeJongAlterations.StableModification.DeJong.BaseStepProjective
import DeJongAlterations.StableModification.DeJong.BaseStepSections
import DeJongAlterations.Geometry.AlterationDominatingBaseChange
import DeJongAlterations.Geometry.BoundaryEnlargement
import DeJongAlterations.Geometry.CartierDominantPullback
import DeJongAlterations.Geometry.CurveFibrationBaseChangeGenericFiber

/-!
# The end of the base step: induction hypothesis and semi-stable resolution

The last part of de Jong's base step 4.22 (`dejong96-alterations:page-0025`, `page-0026`):
once the variety `X` has been replaced by a nodal curve `C → S` over a projective variety
of dimension `d - 1`, with the boundary contained in disjoint sections `τ_i(S)` and in the
preimage of a proper closed `B ⊊ S` outside which `C → S` is smooth, one applies the
induction hypothesis to `(S, B)`, pulls the family back to the resulting regular projective
`S''` with strict normal crossings divisor over `B`, and resolves the semi-stable situation
4.23 by `SemistableResolution k` (de Jong 4.23–4.28). Pulling back the Cartier divisor
(Codex `Geometry.CartierDominantPullback.isEffectiveCartierDivisor_comap`), shrinking the
boundary (4.9, Codex `Geometry.BoundaryEnlargement.shrinkBoundary`) and composing (4.4,
Codex `Geometry.ProjectiveReduction.compOutput`) gives the alteration of `X`.

* `PreparedFamily p Z d`: the data produced by steps S1–S5 (PLAN-DJ-MAIN §3.4).
* `nonempty_alterationWithBoundary_of_preparedFamily` (steps S6–S8).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Helpers

variable {X Y : Scheme.{u}}

/-- A morphism to an irreducible scheme whose image contains the generic point is dominant. -/
theorem isDominant_of_genericPoint_mem_range [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : genericPoint Y ∈ Set.range f) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_spec Y]
  exact closure_mono (Set.singleton_subset_iff.mpr h)

/-- A morphism to an integral scheme whose generic fibre is geometrically integral is
dominant. -/
theorem isDominant_of_geometricallyIntegral_genericFiber [IsIntegral Y] (f : X ⟶ Y)
    (h : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y))) : IsDominant f := by
  have : IsIntegral (f.fiber (genericPoint Y)) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (f.fiberToSpecResidueField (genericPoint Y))
  obtain ⟨z⟩ := (inferInstance : Nonempty (f.fiber (genericPoint Y)))
  apply isDominant_of_genericPoint_mem_range
  refine ⟨f.fiberι _ z, ?_⟩
  have : f.fiberι (genericPoint Y) z ∈ f ⁻¹' {genericPoint Y} := by
    rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
  exact this

/-- A projection of a fibre product of integral schemes over an alteration is an alteration,
when the fibre product is integral and the other factor dominates the base. -/
theorem isAlteration_pullback_fst {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X]
    [IsAlteration g] [IsDominant f] [IsIntegral (pullback f g)] :
    IsAlteration (pullback.fst f g) := by
  have hg : IsAlteration g := inferInstance
  have : IsIntegral Y := hg.sourceIntegral
  have : IsIntegral S := hg.targetIntegral
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g)
    (genericPoint X) (genericPoint Y)
    (by rw [genericPoint_map_of_isDominant f, genericPoint_map_of_isDominant g])
  have : IsDominant (𝟙 (pullback f g) ≫ pullback.fst f g) := by
    rw [Category.id_comp]; exact isDominant_of_genericPoint_mem_range _ ⟨z, hz₁⟩
  have : IsDominant (𝟙 (pullback f g) ≫ pullback.snd f g) := by
    rw [Category.id_comp]; exact isDominant_of_genericPoint_mem_range _ ⟨z, hz₂⟩
  have := Geometry.AlterationDominatingBaseChange.first_isAlteration f g (𝟙 (pullback f g))
  simpa using this

end Helpers

variable {k : Type u} [Field k]

/-- **The prepared family of the base step** (the output of steps S1–S5 of PLAN-DJ-MAIN §3.4,
i.e. of de Jong 4.11–4.22 with Temkin's theorem in place of 4.13–4.21). For a variety
`X` with boundary `Z ⊆ X`: a projective variety `S` of dimension at most `d - 1`, a proper
nodal curve `C → S` with `C` projective over `k` and geometrically integral generic fibre,
an alteration `C → X` over `k`, a proper closed `B ⊊ S` outside of which `C → S` is smooth,
and pairwise disjoint sections `τ_i : S → C` into the smooth locus such that the preimage of
`Z` lies in `⋃ τ_i(S) ∪ g⁻¹(B)` (de Jong 4.22, the situation before 4.23). -/
structure PreparedFamily {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (Z : Set X) (d : ℕ) where
  /-- The base `S`. -/
  base : Scheme.{u}
  /-- The structure morphism of the base. -/
  baseStructure : base ⟶ Spec (.of k)
  baseVariety : IsVariety baseStructure
  baseProjective : IsProjectiveOver baseStructure
  baseDim : topologicalKrullDim base ≤ ((d - 1 : ℕ) : WithBot ℕ∞)
  /-- The total space `C` of the curve family. -/
  curve : Scheme.{u}
  /-- The curve family `g : C → S`. -/
  fibration : curve ⟶ base
  nodal : IsNodalCurve fibration
  proper : IsProper fibration
  curveProjective : IsProjectiveOver (fibration ≫ baseStructure)
  genericFiber : letI := baseVariety
    GeometricallyIntegral (fibration.fiberToSpecResidueField (genericPoint base))
  /-- The alteration `C → X`. -/
  map : curve ⟶ X
  mapAlteration : IsAlteration map
  mapOver : map ≫ p = fibration ≫ baseStructure
  /-- The degeneration locus `B ⊊ S`. -/
  bad : Closeds base
  bad_ne_top : bad ≠ ⊤
  smooth_off_bad : ∀ x, fibration x ∉ (bad : Set base) → IsSmoothAt fibration x
  /-- The number of sections. -/
  n : ℕ
  /-- The sections `τ_i : S → C`. -/
  sections : Fin n → (base ⟶ curve)
  sections_spec : ∀ i, sections i ≫ fibration = 𝟙 base
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (sections i)) (Set.range (sections j))
  sections_smooth : ∀ i y, IsSmoothAt fibration (sections i y)
  cover : ∀ x, map x ∈ Z → x ∈ ⋃ i, Set.range (sections i) ∨ fibration x ∈ (bad : Set base)

/-- **Steps S6–S8 of the base step** (de Jong 4.22 end, 4.23, 4.4, 4.9). Given the induction
hypothesis in dimension `d - 1` and the semi-stable resolution statement, a prepared family
for `(X, Supp D)`, with `D` an effective Cartier divisor, gives an alteration with boundary
of `(X, Supp D)`. -/
theorem nonempty_alterationWithBoundary_of_preparedFamily [IsAlgClosed k]
    (hEND : SemistableResolution k) {d : ℕ} (IH : TheoremUpTo k (d - 1))
    {X : Scheme.{u}} {p : X ⟶ Spec (.of k)} [IsVariety p]
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (F : PreparedFamily p (D.support : Set X) d) :
    Nonempty (AlterationWithBoundary p (D.support : Set X)) := by
  let := F.baseVariety
  have : IsProper F.baseStructure := F.baseProjective.isProper
  let := F.nodal
  let := F.proper
  let := F.mapAlteration
  have hGI := F.genericFiber
  -- the induction hypothesis on `(S, B)`
  obtain ⟨e₀⟩ := IH F.base F.baseStructure F.baseVariety F.baseDim F.bad F.bad_ne_top
  let Y := e₀.compactification
  let pY := e₀.compactificationStructure
  let a : Y ⟶ F.base := Geometry.BoundaryEnlargement.compactificationMap e₀
  have : IsAlteration a := Geometry.BoundaryEnlargement.compactificationMap_isAlteration e₀
  have haY : a ≫ F.baseStructure = pY :=
    Geometry.BoundaryEnlargement.compactificationMap_structure e₀
  have hbd : (e₀.boundary.support : Set Y) = a ⁻¹' (F.bad : Set F.base) :=
    Geometry.BoundaryEnlargement.boundary_support_eq_preimage e₀
  have : IsVariety pY := e₀.compactificationVariety
  have : IsProper pY := e₀.projective.isProper
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated pY
  have : IsIntegral F.curve := F.mapAlteration.sourceIntegral
  have : IsDominant F.fibration := isDominant_of_geometricallyIntegral_genericFiber _ hGI
  -- the pulled back family `C ×_S S'' → S''`
  let g' := pullback.snd F.fibration a
  have : IsIntegral (pullback F.fibration a) :=
    isIntegral_of_flat_of_isIntegral_genericFiber g'
      (Geometry.CurveFibrationBaseChange.genericFiber_isIntegral F.fibration hGI a)
  have hvar : IsVariety (g' ≫ pY) := {}
  have hcomp : g' ≫ pY = pullback.fst F.fibration a ≫ F.fibration ≫ F.baseStructure := by
    rw [← haY, ← pullback.condition_assoc]
  have hproj : IsProjectiveOver (g' ≫ pY) := by
    rw [hcomp]
    exact isProjectiveOver_pullback F.fibration a F.baseStructure F.curveProjective
      (by rw [haY]; exact e₀.projective)
  have hsmooth : ∀ x, g' x ∉ (e₀.boundary.support : Set Y) → IsSmoothAt g' x := by
    intro x hx
    rw [hbd] at hx
    apply isSmoothAt_pullback_snd
    apply F.smooth_off_bad
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact hx
  -- the pulled back sections
  let τ : Fin F.n → (Y ⟶ pullback F.fibration a) := fun i ↦
    pullback.lift (a ≫ F.sections i) (𝟙 Y) (by
      rw [Category.assoc, F.sections_spec, Category.comp_id, Category.id_comp])
  have hτg : ∀ i, τ i ≫ g' = 𝟙 Y := fun i ↦ pullback.lift_snd _ _ _
  have hτr : ∀ i, τ i ≫ pullback.fst F.fibration a = a ≫ F.sections i :=
    fun i ↦ pullback.lift_fst _ _ _
  have hrange : ∀ i, Set.range (τ i) =
      pullback.fst F.fibration a ⁻¹' Set.range (F.sections i) := fun i ↦
    range_eq_preimage_of_isPullback_section (IsPullback.of_hasPullback F.fibration a)
      (F.sections i) (F.sections_spec i) (τ i) (hτr i) (hτg i)
  have hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (τ i)) (Set.range (τ j)) := by
    intro i j hij
    rw [hrange, hrange]
    exact (F.disjoint i j hij).preimage _
  have hτsm : ∀ i y, IsSmoothAt g' (τ i y) := by
    intro i y
    apply isSmoothAt_pullback_snd
    rw [← Scheme.Hom.comp_apply, hτr, Scheme.Hom.comp_apply]
    exact F.sections_smooth i (a y)
  -- the semi-stable resolution 4.23–4.28
  obtain ⟨dEND, -⟩ := hEND Y pY e₀.compactificationVariety e₀.projective e₀.regular
    e₀.boundary e₀.normalCrossings (pullback F.fibration a) g' hvar hproj inferInstance hsmooth
    F.n τ hτg hdisj hτsm
  -- the alteration `C ×_S S'' → X`
  let πX := pullback.fst F.fibration a ≫ F.map
  have : IsAlteration (pullback.fst F.fibration a) := isAlteration_pullback_fst F.fibration a
  have : IsAlteration πX := IsAlteration.comp _ _
  have hπXp : πX ≫ p = g' ≫ pY := by
    rw [hcomp, Category.assoc, F.mapOver]
  -- the pulled back Cartier divisor and the shrunken boundary
  let E := D.comap πX
  have hE : IsEffectiveCartierDivisor E :=
    Geometry.CartierDominantPullback.isEffectiveCartierDivisor_comap πX D hD
  have hEsupp : (E.support : Set (pullback F.fibration a : Scheme.{u})) = πX ⁻¹' D.support := by
    simp [E]
  have hZ'closed : IsClosed ((⋃ i, Set.range (τ i)) ∪
      g' ⁻¹' (e₀.boundary.support : Set Y)) := by
    refine IsClosed.union (isClosed_iUnion_of_finite fun i ↦ ?_)
      (e₀.boundary.support.isClosed.preimage g'.continuous)
    have := isClosedImmersion_of_comp_eq_id g' (τ i) (hτg i)
    exact (τ i).isClosedEmbedding.isClosed_range
  let Z' : Closeds (pullback F.fibration a : Scheme.{u}) := ⟨_, hZ'closed⟩
  have hle : E.support ≤ Z' := by
    intro x hx
    have hx' : F.map (pullback.fst F.fibration a x) ∈ (D.support : Set X) := by
      have : x ∈ πX ⁻¹' D.support := hEsupp ▸ hx
      exact this
    rcases F.cover _ hx' with h | h
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      left
      exact Set.mem_iUnion.mpr ⟨i, (hrange i).symm ▸ hi⟩
    · right
      change g' x ∈ (e₀.boundary.support : Set Y)
      rw [hbd]
      change F.fibration (pullback.fst F.fibration a x) ∈ (F.bad : Set F.base) at h
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply] at h
      exact h
  have d1 := Geometry.BoundaryEnlargement.shrinkBoundary E hE Z' hle dEND
  have d2 : AlterationWithBoundary (πX ≫ p) (E.support : Set _) := hπXp ▸ d1
  exact ⟨Geometry.ProjectiveReduction.compOutput πX hEsupp d2⟩

end DeJongAlterations.StableModification.DeJong
