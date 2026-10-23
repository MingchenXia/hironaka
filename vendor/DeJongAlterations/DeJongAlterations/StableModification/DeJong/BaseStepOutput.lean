import DeJongAlterations.StableModification.DeJong.BaseStepFamily
import DeJongAlterations.StableModification.DeJong.Dimension
import DeJongAlterations.Geometry.CurveFibrationMarkedOpenSmooth

/-!
# Temkin's output in the base step

Steps S3–S5 of PLAN-DJ-MAIN §3.4: de Jong's base step 4.22 (`dejong96-alterations:page-0025`,
`page-0026`) with Temkin's stable modification theorem (Temkin Thm 1.5 + Thm 1.1,
`semi-stable.tex` l.1713–1716, l.1771–1775) in place of the moduli argument 4.17–4.21.

`TemkinInput p Z d` packages a multipointed curve `(C, D)` over a normal projective variety
`S` of dimension at most `d - 1`, satisfying the hypotheses of `TemkinStableModification k`,
together with an alteration `C → X` and a proper closed `B ⊊ S` such that the preimage of the
boundary `Z ⊆ X` lies in `D ∪ g⁻¹(B)`. Temkin's theorem gives a generically étale alteration
`S' → S`, a semi-stable pair `(C', D')` over `S'` and an `S'`-morphism
`β : C' → C ×_S S'`, projective and an isomorphism over a nonempty open `U ⊆ S'`, matching
the marks over `U`. Then:

* `C'` is integral with geometrically integral generic fibre (`β` is an isomorphism over the
  generic point; `C ×_S S'` is flat over `S'` with geometrically integral generic fibre), so
  `C' → C → X` is an alteration;
* `C' → S'` is smooth over `U ∩ ψ⁻¹(V)`, where `V ⊆ S` is the open over which `C → S` is
  smooth (it contains the generic point, Codex
  `Geometry.CurveFibrationMarkedOpen.exists_nonempty_dense_smooth_base_open`);
* after the projective alteration `S'' → S'` of `exists_split_marks` the marks become
  disjoint sections, and the boundary is contained in the sections and the preimage of
  `B'' := (S' ∖ U) ∪ ψ⁻¹(B ∪ (S ∖ V))` (de Jong 4.22: "a component of `β⁻¹(Z)` not equal to
  some `τ_i(Y)` has image of codimension one, as `β` is an isomorphism over `U`").

The result is `preparedFamily_of_temkinInput`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]

/-- **The input of Temkin's theorem in the base step** (steps S1–S2 of PLAN-DJ-MAIN §3.4):
a multipointed curve `(C, D)` over a normal projective variety `S` of dimension at most
`d - 1` satisfying the hypotheses of `TemkinStableModification k`, with geometrically
integral generic fibre and `C → S` proper, an alteration `C → X` over `k`, and a proper
closed `B ⊆ S` such that the preimage of `Z` lies in `D ∪ g⁻¹(B)`. -/
structure TemkinInput {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (Z : Set X) (d : ℕ) where
  /-- The base `S`. -/
  base : Scheme.{u}
  /-- The structure morphism of the base. -/
  baseStructure : base ⟶ Spec (.of k)
  baseVariety : IsVariety baseStructure
  baseNormal : IsNormalScheme base
  baseProjective : IsProjectiveOver baseStructure
  baseDim : topologicalKrullDim base ≤ ((d - 1 : ℕ) : WithBot ℕ∞)
  /-- The curve `C`. -/
  curve : Scheme.{u}
  /-- The curve family `g : C → S`. -/
  fibration : curve ⟶ base
  /-- The marks `D ⊆ C`. -/
  marks : curve.IdealSheafData
  curveProjective : IsProjectiveOver (fibration ≫ baseStructure)
  multipointed : IsMultipointedCurve fibration marks
  genericSmooth : letI := baseVariety
    Smooth (fibration.fiberToSpecResidueField (genericPoint base))
  genericSemistable : letI := baseVariety
    IsSemistablePair (fibration.fiberToSpecResidueField (genericPoint base))
      (fiberMarks fibration marks (genericPoint base))
  genericFiber : letI := baseVariety
    GeometricallyIntegral (fibration.fiberToSpecResidueField (genericPoint base))
  proper : IsProper fibration
  /-- The alteration `C → X`. -/
  map : curve ⟶ X
  mapAlteration : IsAlteration map
  mapOver : map ≫ p = fibration ≫ baseStructure
  /-- The bad closed set `B ⊆ S`. -/
  bad : Closeds base
  genericPoint_not_mem_bad : letI := baseVariety
    genericPoint base ∉ (bad : Set base)
  cover : ∀ x, map x ∈ Z → x ∈ (marks.support : Set curve) ∨ fibration x ∈ (bad : Set base)

/-- A nonempty open subset of an irreducible scheme contains its generic point. -/
theorem genericPoint_mem_of_nonempty {Y : Scheme.{u}} [IrreducibleSpace Y] (U : Y.Opens)
    (hU : Nonempty U) : genericPoint Y ∈ U :=
  ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by
    obtain ⟨⟨y, hy⟩⟩ := hU
    exact ⟨y, Set.mem_univ _, hy⟩)

/-- **Steps S3–S5 of the base step.** Temkin's stable modification theorem turns a
`TemkinInput` into a `PreparedFamily`. -/
theorem preparedFamily_of_temkinInput [IsAlgClosed k] (hTSM : TemkinStableModification k)
    {X : Scheme.{u}} {p : X ⟶ Spec (.of k)} {Z : Set X} {d : ℕ} (I : TemkinInput p Z d) :
    Nonempty (PreparedFamily p Z d) := by
  let := I.baseVariety
  let := I.proper
  let := I.multipointed.flat
  let := I.multipointed.locallyOfFinitePresentation
  let := I.mapAlteration
  let := I.genericSmooth
  have hGI := I.genericFiber
  have : IsIntegral I.curve := I.mapAlteration.sourceIntegral
  have : QuasiSeparatedSpace I.base := quasiSeparatedSpace_of_quasiSeparated I.baseStructure
  obtain ⟨S', ψ, C', D', β, hψ, hss', hfin', hβproj, U, hU, hβiso, hmarks⟩ :=
    hTSM I.base I.baseStructure I.baseVariety I.baseNormal I.baseProjective I.curve
      I.fibration I.marks I.curveProjective I.multipointed I.genericSmooth I.genericSemistable
      I.genericFiber
  -- notation
  let g := I.fibration
  let pS := I.baseStructure
  let q := pullback.snd g ψ
  let g' := β ≫ q
  let := hψ
  have : IsIntegral S' := hψ.sourceIntegral
  have : IsNodalCurve g' := hss'.nodal
  have : IsProper β := hβproj.isProper
  have hvarS' : IsVariety (ψ ≫ pS) := {}
  have : IsProper pS := I.baseProjective.isProper
  have : IsProper (ψ ≫ pS) := inferInstance
  have : QuasiSeparatedSpace S' := quasiSeparatedSpace_of_quasiSeparated (ψ ≫ pS)
  have hη'U : genericPoint S' ∈ U := genericPoint_mem_of_nonempty U hU
  have hψη : ψ (genericPoint S') = genericPoint I.base := genericPoint_map_of_isDominant ψ
  -- the generic fibre of `C ×_S S' → S'`
  have hGIq : GeometricallyIntegral (q.fiberToSpecResidueField (genericPoint S')) := by
    have hg : GeometricallyIntegral (g.fiberToSpecResidueField (ψ (genericPoint S'))) := by
      rw [hψη]; exact hGI
    exact MorphismProperty.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback g ψ) (genericPoint S')) hg
  -- the generic fibre of `C' → S'`
  have hGI' : GeometricallyIntegral (g'.fiberToSpecResidueField (genericPoint S')) := by
    obtain ⟨E, hE⟩ := exists_fiberIso_of_isIso_morphismRestrict β q U hβiso _ hη'U
    rw [← hE]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral E.hom _).mpr hGIq
  have hdomg : IsDominant g := isDominant_of_geometricallyIntegral_genericFiber g hGI
  have hdomq : IsDominant q := isDominant_of_geometricallyIntegral_genericFiber q hGIq
  have hdomg' : IsDominant g' := isDominant_of_geometricallyIntegral_genericFiber g' hGI'
  have hintP : IsIntegral (pullback g ψ) := isIntegral_of_flat_of_isIntegral_genericFiber q
    (Geometry.CurveFibrationBaseChange.genericFiber_isIntegral g hGI ψ)
  have hintC' : IsIntegral C' := isIntegral_of_flat_of_isIntegral_genericFiber g'
    (GeometricallyIntegral.isIntegral_of_subsingleton (g'.fiberToSpecResidueField _))
  -- `β` is an alteration
  let W := q ⁻¹ᵁ U
  have hWne : Nonempty W := by
    obtain ⟨z, hz⟩ : genericPoint S' ∈ Set.range q := by
      have := hdomq.denseRange
      exact ⟨_, genericPoint_map_of_isDominant q⟩
    exact ⟨⟨z, by change q z ∈ U; rw [hz]; exact hη'U⟩⟩
  have hβ : IsAlteration β := by
    have hgenW : genericPoint (pullback g ψ : Scheme.{u}) ∈ W := genericPoint_mem_of_nonempty W hWne
    have hdom : IsDominant β := by
      apply isDominant_of_genericPoint_mem_range
      obtain ⟨v, hv⟩ := (asIso (β ∣_ W)).hom.surjective ⟨_, hgenW⟩
      refine ⟨(β ⁻¹ᵁ W).ι v, ?_⟩
      have h1 : β ((β ⁻¹ᵁ W).ι v) = W.ι ((β ∣_ W) v) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
      have h2 : (β ∣_ W) v = ⟨_, hgenW⟩ := hv
      rw [h1, h2]
      rfl
    exact { sourceIntegral := hintC', targetIntegral := hintP,
            genericallyFinite := ⟨W, hWne, inferInstance⟩ }
  have hfstψ : IsAlteration (pullback.fst g ψ) := isAlteration_pullback_fst g ψ
  -- the open over which `C → S` is smooth
  obtain ⟨V, hVne, -, hVsm, -⟩ :=
    Geometry.CurveFibrationMarkedOpen.exists_nonempty_dense_smooth_base_open g
  have hηV : genericPoint I.base ∈ V := genericPoint_mem_of_nonempty V hVne
  have hsm' : ∀ x : C', g' x ∈ U → ψ (g' x) ∈ V → IsSmoothAt g' x := by
    intro x hxU hxV
    have hxW : x ∈ β ⁻¹ᵁ W := hxU
    have h1 : IsSmoothAt q (β x) := by
      apply isSmoothAt_pullback_snd
      apply (isSmoothAt_iff_mem_smoothLocus g _).mpr
      apply hVsm
      change g (pullback.fst g ψ (β x)) ∈ V
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact hxV
    have h2 : IsSmoothAt (W.ι ≫ q) ((β ∣_ W) ⟨x, hxW⟩) := by
      rw [isSmoothAt_comp_iff_of_isOpenImmersion]
      have : W.ι ((β ∣_ W) ⟨x, hxW⟩) = β x := by
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        rfl
      rw [this]
      exact h1
    have h3 : IsSmoothAt ((β ∣_ W) ≫ W.ι ≫ q) ⟨x, hxW⟩ := by
      have := (isSmoothAt_iso_comp_iff (asIso (β ∣_ W)) (W.ι ≫ q) ⟨x, hxW⟩).mpr h2
      exact this
    have h4 : (β ∣_ W) ≫ W.ι ≫ q = (β ⁻¹ᵁ W).ι ≫ g' := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [h4, isSmoothAt_comp_iff_of_isOpenImmersion] at h3
    exact h3
  -- splitting the marks
  have : Etale (D'.subschemeι ≫ g') := hss'.etale
  have : IsFinite (D'.subschemeι ≫ g') := hfin'
  obtain ⟨S'', ν, n, τ, hν, hvar'', hproj'', hτ, hdisj, hτD, hcovD⟩ :=
    exists_split_marks (ψ ≫ pS) g' D'
  let := hν
  have : IsIntegral S'' := hν.sourceIntegral
  have hνη : ν (genericPoint S'') = genericPoint S' := genericPoint_map_of_isDominant ν
  -- the new bad set
  have hB'closed : IsClosed ((U : Set S')ᶜ ∪ ψ ⁻¹' ((I.bad : Set I.base) ∪ (V : Set I.base)ᶜ)) :=
    U.isOpen.isClosed_compl.union
      ((I.bad.isClosed.union V.isOpen.isClosed_compl).preimage ψ.continuous)
  let B'' : Closeds S'' :=
    ⟨ν ⁻¹' ((U : Set S')ᶜ ∪ ψ ⁻¹' ((I.bad : Set I.base) ∪ (V : Set I.base)ᶜ)),
    hB'closed.preimage ν.continuous⟩
  have hB''mem : ∀ y : S'', y ∉ (B'' : Set S'') ↔
      ν y ∈ U ∧ ψ (ν y) ∉ (I.bad : Set I.base) ∧ ψ (ν y) ∈ V := by
    intro y
    simp only [B'', Closeds.coe_mk, Set.mem_preimage, Set.mem_union, Set.mem_compl_iff,
      not_or, not_not, SetLike.mem_coe]
  have hB''mem' : ∀ y : S'', y ∈ (B'' : Set S'') ↔
      ν y ∉ U ∨ ψ (ν y) ∈ (I.bad : Set I.base) ∨ ψ (ν y) ∉ V := by
    intro y
    simp only [B'', Closeds.coe_mk, Set.mem_preimage, Set.mem_union, Set.mem_compl_iff,
      SetLike.mem_coe]
  -- generic fibre of the final family
  have hGI'' : GeometricallyIntegral
      ((pullback.snd g' ν).fiberToSpecResidueField (genericPoint S'')) := by
    have hg : GeometricallyIntegral (g'.fiberToSpecResidueField (ν (genericPoint S''))) := by
      rw [hνη]; exact hGI'
    exact MorphismProperty.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback g' ν) (genericPoint S'')) hg
  have hint'' : IsIntegral (pullback g' ν) := by
    have : QuasiSeparatedSpace S'' := quasiSeparatedSpace_of_quasiSeparated (ν ≫ ψ ≫ pS)
    exact isIntegral_of_flat_of_isIntegral_genericFiber (pullback.snd g' ν)
      (Geometry.CurveFibrationBaseChange.genericFiber_isIntegral g' hGI' ν)
  have hfst'' : IsAlteration (pullback.fst g' ν) := isAlteration_pullback_fst g' ν
  -- projectivity of the final curve
  have hT : IsProjectiveOver (pullback.fst q ν ≫ q ≫ ψ ≫ pS) := by
    have H := isProjectiveOver_pullback g (ν ≫ ψ) pS I.curveProjective
      (by simpa using hproj'')
    have H' := IsProjectiveOver.comp_isClosedImmersion H (pullbackLeftPullbackSndIso g ψ ν).hom
    have e : (pullbackLeftPullbackSndIso g ψ ν).hom ≫ pullback.fst g (ν ≫ ψ) ≫ g ≫ pS =
        pullback.fst q ν ≫ q ≫ ψ ≫ pS := by
      rw [pullbackLeftPullbackSndIso_hom_fst_assoc, pullback.condition_assoc]
    rwa [e] at H'
  have hrel := hβproj.pullback_snd (pullback.fst q ν)
  have hP := hrel.isProjectiveOver hT
  have hcurveProj : IsProjectiveOver (pullback.snd g' ν ≫ ν ≫ ψ ≫ pS) := by
    have H' := IsProjectiveOver.comp_isClosedImmersion hP (pullbackRightPullbackFstIso q ν β).inv
    have h1 : pullback.fst q ν ≫ q ≫ ψ ≫ pS = pullback.snd q ν ≫ ν ≫ ψ ≫ pS :=
      pullback.condition_assoc _
    have e : (pullbackRightPullbackFstIso q ν β).inv ≫ pullback.snd β (pullback.fst q ν) ≫
        pullback.fst q ν ≫ q ≫ ψ ≫ pS = pullback.snd g' ν ≫ ν ≫ ψ ≫ pS := by
      rw [h1, ← pullbackRightPullbackFstIso_hom_snd_assoc, Iso.inv_hom_id_assoc]
    rwa [e] at H'
  -- the prepared family
  refine ⟨{
    base := S''
    baseStructure := ν ≫ ψ ≫ pS
    baseVariety := hvar''
    baseProjective := hproj''
    baseDim := ?_
    curve := pullback g' ν
    fibration := pullback.snd g' ν
    nodal := inferInstance
    proper := inferInstance
    curveProjective := hcurveProj
    genericFiber := hGI''
    map := pullback.fst g' ν ≫ β ≫ pullback.fst g ψ ≫ I.map
    mapAlteration := ?_
    mapOver := ?_
    bad := B''
    bad_ne_top := ?_
    smooth_off_bad := ?_
    n := n
    sections := τ
    sections_spec := hτ
    disjoint := hdisj
    sections_smooth := ?_
    cover := ?_ }⟩
  · rw [topologicalKrullDim_eq_of_isAlteration (ψ ≫ pS) ν,
      topologicalKrullDim_eq_of_isAlteration pS ψ]
    exact I.baseDim
  · have : IsAlteration (pullback.fst g ψ ≫ I.map) := IsAlteration.comp _ _
    have : IsAlteration (β ≫ pullback.fst g ψ ≫ I.map) := IsAlteration.comp _ _
    exact IsAlteration.comp _ _
  · have h1 : I.map ≫ p = g ≫ pS := I.mapOver
    have h2 : pullback.fst g ψ ≫ g ≫ pS = q ≫ ψ ≫ pS := pullback.condition_assoc _
    have h3 : pullback.fst g' ν ≫ g' ≫ ψ ≫ pS = pullback.snd g' ν ≫ ν ≫ ψ ≫ pS :=
      pullback.condition_assoc _
    calc (pullback.fst g' ν ≫ β ≫ pullback.fst g ψ ≫ I.map) ≫ p
        = pullback.fst g' ν ≫ β ≫ pullback.fst g ψ ≫ (I.map ≫ p) := by
          simp only [Category.assoc]
      _ = pullback.fst g' ν ≫ β ≫ (pullback.fst g ψ ≫ g ≫ pS) := by rw [h1]
      _ = pullback.fst g' ν ≫ (β ≫ q) ≫ ψ ≫ pS := by rw [h2, Category.assoc]
      _ = pullback.snd g' ν ≫ ν ≫ ψ ≫ pS := h3
  · intro h
    have hmem : genericPoint S'' ∉ (B'' : Set S'') := by
      rw [hB''mem, hνη, hψη]
      exact ⟨hη'U, I.genericPoint_not_mem_bad, hηV⟩
    rw [h] at hmem
    exact hmem trivial
  · intro x hx
    rw [hB''mem] at hx
    obtain ⟨hxU, -, hxV⟩ := hx
    apply isSmoothAt_pullback_snd
    have h : g' (pullback.fst g' ν x) = ν (pullback.snd g' ν x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    apply hsm'
    · rw [h]; exact hxU
    · rw [h]; exact hxV
  · intro i y
    apply isSmoothAt_pullback_snd
    exact hss'.smoothAlong _ (hτD i y)
  · intro x hx
    let c := pullback.fst g ψ (β (pullback.fst g' ν x))
    have h1 : g' (pullback.fst g' ν x) = ν (pullback.snd g' ν x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have hgc : g c = ψ (ν (pullback.snd g' ν x)) := by
      rw [← h1]
      change (pullback.fst g ψ ≫ g) _ = _
      rw [pullback.condition]
      rfl
    rcases I.cover c hx with hc | hc
    · by_cases hU' : ν (pullback.snd g' ν x) ∈ U
      · left
        have hD' : pullback.fst g' ν x ∈ (D'.support : Set C') := by
          apply (hmarks _ (by rw [h1]; exact hU')).mpr
          exact hc
        obtain ⟨i, hi⟩ := hcovD x hD'
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      · right
        exact (hB''mem' _).mpr (Or.inl hU')
    · right
      exact (hB''mem' _).mpr (Or.inr (Or.inl (by rw [← hgc]; exact hc)))

end DeJongAlterations.StableModification.DeJong
