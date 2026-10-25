import DeJongAlterations.StableModification.Global.Spread

/-!
# Local stable pieces around the valuation rings of `RZ_{K(S)ᵃ}(S)`

Nodes G1, G3′ and (as a hypothesis) G4 of `PLAN-T5.md` (§2.1 steps 1–2; Temkin, *Stable
modification of relative curves*, `semi-stable.tex`, proof of Theorem 1.5, T:3379–3394).

Let `S` be a projective variety over `k`, `(C, D)` a multipointed `S`-curve projective over `k`
whose generic fibre is smooth, geometrically integral and, with the marks, semi-stable, and `L`
an algebraically closed algebraic extension of `K(S)`. For a valuation ring `W ∈ RZ_L(S)`:

1. `W` has finite height and equal characteristic, and `(C, D) ×_S Spec W` is a curve over `W`
   in the situation of Temkin's §4.5 (node G1, `Global.isValuationCurve_pullback`); lane T45B's
   `ValuationStableExistence` gives a stable, numerically stable η-modification projective over
   `W`;
2. lane LIM3's `exists_semistable_projective_etaModification_of_isIso_fiberMap` descends it to a
   projective semi-stable η-modification over the spectrum `T_B = Spec B` of a finitely generated
   subalgebra `B ⊆ W` of the sections of an affine open of `S`; its marks are the transported
   marks (G-marks, `genericMarksCondition_of_forall`), so it is a spread model (`IsSpreadModel`);
3. the geometric fibre over a geometric point at the centre of `W` is the geometric fibre of
   the stable modification over the closed point of `W`, hence numerically stable; by node G4
   (`StableOpenNbhd`, a hypothesis) numerical stability holds over an open neighbourhood `O` of the
   centre, and an affine neighbourhood `T' ⊆ O` of the centre is a local stable piece containing
   `W` in its Riemann–Zariski space (`exists_localStablePiece`).

Blueprint: `sm-global.tex`, `thm:sm-global-local-piece`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective IsMultipointedCurve)
open Curves (pullbackCompMap IsStableModification)
open RiemannZariskiSpace

set_option backward.isDefEq.respectTransparency false in
/-- **Local stable pieces** (`PLAN-T5.md` §2.1 steps 1–2, nodes G1, G3′, G4). In the situation of
`DeJong.TemkinStableModification` (without normality of `S`), for `L` an algebraically closed
algebraic extension of `K(S)`, existence of stable modifications over valuation rings (lane
T45B, `ValuationStableExistence`) and the spreading of numerical stability (node G4,
`StableOpenNbhd k`) give, for every valuation ring `W ∈ RZ_L(S)`, a local stable piece `T` with
`W ∈ RZ_L(T)`. -/
theorem exists_localStablePiece {k : Type u} [Field k] {S C : Scheme.{u}}
    (pS : S ⟶ Spec (.of k)) [IsVariety pS] (hSp : IsProjectiveOver pS) (g : C ⟶ S)
    (D : C.IdealSheafData) (hC : IsProjectiveOver (g ≫ pS)) (hD : IsMultipointedCurve g D)
    (hsm : Smooth (g.fiberToSpecResidueField (genericPoint S)))
    (hss : IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
      (DeJong.fiberMarks g D (genericPoint S)))
    (hgi : GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)))
    {L : Type u} [Field L] [IsAlgClosed L] [Algebra S.functionField L]
    [Algebra.IsAlgebraic S.functionField L]
    (hE : ValuationStableExistence.{u}) (hO : StableOpenNbhd k)
    (W : RiemannZariskiSpace L) (hW : W ∈ ofScheme (functionFieldPoint S L)) :
    ∃ P : LocalStablePiece pS g D L, W ∈ ofScheme P.ηT := by
  classical
  set η := functionFieldPoint S L with hηdef
  have : IsProper pS := hSp.isProper
  have : S.IsSeparated := ⟨by rw [← terminal.comp_from pS]; infer_instance⟩
  have : Flat g := hD.flat
  have : LocallyOfFinitePresentation g := hD.locallyOfFinitePresentation
  have : IsProper (g ≫ pS) := hC.isProper
  have : IsProper g := IsProper.of_comp g pS
  have hfin : Finite (PrimeSpectrum W.valuationSubring) :=
    finite_primeSpectrum_of_mem (pS := pS) W hW
  obtain ⟨p, hp⟩ := exists_expChar_of_mem (pS := pS) W hW
  obtain ⟨ψ, hψ⟩ := hW
  -- an affine open around the centre of `W`
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hcV₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ψ (specClosedPoint W))) isOpen_univ
  obtain ⟨hηV₀, hWV₀⟩ := mem_ofOpen_of_extension ψ hψ hcV₀
  let A := Γ(S, V₀)
  let : Algebra k A := Geometry.RationalCoordinateMap.sectionAlgebra pS ⟨V₀, hV₀⟩
  have : Algebra.FiniteType k A :=
    Geometry.FunctionFieldDimension.affineSections_finiteType pS ⟨V₀, hV₀⟩
  let : Algebra A L := (sectionsToField η V₀ hηV₀).toAlgebra
  have hWA : W ∈ ofAlgebra A L := hWV₀
  let V : ofAlgebra A L := ⟨W, hWA⟩
  -- the approximating system of `W`
  let R := Limits.valuationSubalgebra V
  let Dg := (Limits.fgDiagram R).op ⋙ Scheme.Spec
  let c := Limits.fgSpecCone R
  let B₀ : (Limits.FGSubalgebra A R)ᵒᵖ := op ⊥
  let a₀ : Dg.obj B₀ ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap A (⊥ : Limits.FGSubalgebra A R).1)) ≫ hV₀.fromSpec
  let toR : Spec (.of L) ⟶ c.pt := Spec.map (CommRingCat.ofHom (algebraMap R L))
  have htoSpec : toSpecValuationSubring W = toR := rfl
  have hkey : (toR ≫ c.π.app B₀) ≫ a₀ = η := by
    rw [show toR ≫ c.π.app B₀ = _ from
      Limits.specMap_comp_fgSpecCone_π_app V (⊥ : Limits.QASystem V)]
    simp only [a₀]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert SpecMap_sectionsToField_fromSpec η hV₀ hηV₀ using 3
    ext x
    rfl
  let ψ' : c.pt ⟶ S := c.π.app B₀ ≫ a₀
  have hψ' : toSpecValuationSubring W ≫ ψ' = η := by
    rw [htoSpec, ← Category.assoc]
    exact hkey
  have hψψ' : ψ = ψ' := extension_unique hψ hψ'
  subst hψψ'
  -- the stable modification over `W` (lane T45B)
  have hV := isValuationCurve_pullback hC hD hsm hss hgi W ψ' hψ'
  obtain ⟨C', β, D', hstab, hnum, hproj⟩ :=
    hE L W.valuationSubring ⟨p, hp⟩ _ (pullback.snd g ψ') (D.comap (pullback.fst g ψ')) hV
  -- the model of `C ×_S Spec W` at the bottom level of the system
  let m : Limits.Model Dg c (pullback.snd g ψ') B₀ :=
    { Y := pullback g a₀
      fY := pullback.snd g a₀
      g := pullback.lift (pullback.fst g ψ') (pullback.snd g ψ' ≫ c.π.app B₀)
        (by rw [pullback.condition, Category.assoc])
      isPullback := IsPullback.of_right (by
          rw [pullback.lift_fst]
          exact IsPullback.of_hasPullback g _)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g a₀) }
  have hm : m.IsFP := ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd g a₀)),
    inferInstanceAs (QuasiCompact (pullback.snd g a₀)),
    inferInstanceAs (QuasiSeparated (pullback.snd g a₀))⟩
  have : Flat m.fY := inferInstanceAs (Flat (pullback.snd g a₀))
  let p₀ : m.Y ⟶ Spec (.of k) := pullback.fst g a₀ ≫ g ≫ pS
  have hmg : m.g ≫ pullback.fst g a₀ = pullback.fst g ψ' := pullback.lift_fst _ _ _
  have hβ : IsRelativelyProjective (m.g ≫ p₀) β := by
    have h1 := Projectivity.isRelativelyProjective_of_isProjectiveOver (pullback.snd g ψ') β hproj
    have e : m.g ≫ p₀ = pullback.snd g ψ' ≫
        Spec.map (CommRingCat.ofHom (Spec.preimage (ψ' ≫ pS)).hom) := by
      simp only [p₀, CommRingCat.ofHom_hom, Spec.map_preimage]
      rw [reassoc_of% hmg, pullback.condition_assoc]
    rw [e, Projectivity.isRelativelyProjective_comp_specMap_iff]
    exact h1
  have hη : IsOpen ({genericPoint c.pt} : Set c.pt) :=
    Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite (.of W.valuationSubring)
  have : IsIso (Curves.fiberMap β (pullback.snd g ψ') (genericPoint c.pt)) :=
    hstab.isIso_fiberMap
  obtain ⟨B, a, M, M', t, βB, DB, UB, hM, hM', ht, htg, hβB, hpb, hprojB, hssB, hDB, hUBc, hUB,
    hisoB, hUBne, heta⟩ :=
    Limits.SpreadModification.exists_semistable_projective_etaModification_of_isIso_fiberMap k
      m hm p₀ β hβ hstab.isSemistablePair hη
  -- the base `T_B = Spec B` and the identification `M.Y ≅ C ×_S T_B`
  let tB : Dg.obj B ⟶ S := Dg.map a ≫ a₀
  have hcw : c.π.app B ≫ Dg.map a = c.π.app B₀ := c.w a
  have Hpt : IsPullback (t ≫ pullback.fst g a₀) M.fY g tB :=
    ht.paste_horiz (IsPullback.of_hasPullback g a₀)
  let e := Hpt.isoPullback
  have he₁ : e.hom ≫ pullback.fst g tB = t ≫ pullback.fst g a₀ := Hpt.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd g tB = M.fY := Hpt.isoPullback_hom_snd
  let β' : M'.Y ⟶ pullback (C := Scheme.{u}) g tB := βB ≫ e.hom
  have hβ'snd : β' ≫ pullback.snd g tB = M'.fY := by
    rw [Category.assoc, he₂, hβB]
  -- the generic point of `T_B`
  have : IsIntegral (Dg.obj B) :=
    inferInstanceAs (IsIntegral (Spec (.of (B.unop.1 : Subalgebra A L))))
  have : IsAffine (Dg.obj B) := inferInstanceAs (IsAffine (Spec (.of (B.unop.1 : Subalgebra A L))))
  have hdomB : IsDominant (c.π.app B) := by
    refine isDominant_SpecMap_of_injective _ fun x y hxy ↦ ?_
    have := congrArg Subtype.val hxy
    exact Subtype.ext this
  have : IsIntegral c.pt := inferInstanceAs (IsIntegral (Spec (.of W.valuationSubring)))
  have hgenB : c.π.app B (genericPoint c.pt) = genericPoint (Dg.obj B) :=
    genericPoint_map_of_isDominant (X := c.pt) (Y := Dg.obj B) (c.π.app B)
  have hgenW : ψ' (genericPoint c.pt) = genericPoint S := apply_genericPoint_of_extension W ψ' hψ'
  have htB : tB (genericPoint (Dg.obj B)) = genericPoint S := by
    rw [← hgenB, ← Scheme.Hom.comp_apply, reassoc_of% hcw]
    exact hgenW
  -- the iso locus
  have hqcU : QuasiCompact UB.ι :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := UB.ι)).mpr
      (isCompact_iff_compactSpace.mp hUBc)
  have hisoβ' : IsIso (β' ∣_ (pullback.snd g tB ⁻¹ᵁ UB)) := by
    rw [morphismRestrict_comp]
    have hpre : e.hom ⁻¹ᵁ (pullback.snd g tB ⁻¹ᵁ UB) = M.fY ⁻¹ᵁ UB := by
      rw [← Scheme.Hom.comp_preimage, he₂]
    have h1 : IsIso (βB ∣_ (e.hom ⁻¹ᵁ (pullback.snd g tB ⁻¹ᵁ UB))) := by rw [hpre]; exact hisoB
    have h2 : IsIso (e.hom ∣_ (pullback.snd g tB ⁻¹ᵁ UB)) :=
      isIso_morphismRestrict_of_isOpenImmersion e.hom _ (fun x _ ↦ e.hom.homeomorph.surjective x)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  have hηUB : genericPoint (Dg.obj B) ∈ UB :=
    ((genericPoint_spec (Dg.obj B)).mem_open_set_iff UB.isOpen).mpr (by simpa using hUBne)
  have : IsIso (Curves.fiberMap β' (pullback.snd g tB) (genericPoint (Dg.obj B))) :=
    Limits.SpreadModification.isIso_pullbackCompMap_of_isIso_morphismRestrict β' _ UB _ (by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      change (Dg.obj B).fromSpecResidueField (genericPoint (Dg.obj B)) x ∈ UB
      rw [Scheme.fromSpecResidueField_apply]
      exact hηUB)
  -- G-marks: the descended marks are the transported marks
  have HX : IsPullback M'.g (β ≫ pullback.snd g ψ') M'.fY (c.π.app B) := by
    have := hpb.paste_vert M.isPullback
    rwa [hβB] at this
  have hcomp : M'.g ≫ β' ≫ pullback.fst g tB = β ≫ pullback.fst g ψ' := by
    simp only [β', Category.assoc, he₁]
    rw [reassoc_of% hpb.w, reassoc_of% htg, hmg]
  have hss' : IsSemistablePair (β' ≫ pullback.snd g tB) DB := by rw [hβ'snd]; exact hssB
  have hpts : ∀ x : M'.Y, (β' ≫ pullback.snd g tB) x = genericPoint (Dg.obj B) →
      (x ∈ (DB.support : Set M'.Y) ↔ (β' ≫ pullback.fst g tB) x ∈ (D.support : Set C)) := by
    intro x hx
    have hx₀ : M'.fY x = c.π.app B (genericPoint c.pt) := by
      rw [← hβ'snd, hx, hgenB]
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := M'.fY)
      (g := c.π.app B) x (genericPoint c.pt) hx₀
    set x' := HX.isoPullback.inv z
    have hx'₁ : M'.g x' = x := by
      rw [← hz₁, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
    have hx'₂ : (β ≫ pullback.snd g ψ') x' = genericPoint c.pt := by
      rw [← hz₂, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]
      rfl
    have h1 : x ∈ (DB.support : Set M'.Y) ↔ x' ∈ (D'.support : Set C') := by
      rw [← hDB, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
        Set.mem_preimage, hx'₁]
    have h2 := mem_genericMarksClosure_iff β (pullback.snd g ψ') (D.comap (pullback.fst g ψ'))
      (genericPoint c.pt) x' hx'₂
    have hme : D' = Curves.genericMarksClosure β (pullback.snd g ψ')
        (D.comap (pullback.fst g ψ')) (genericPoint c.pt) := hstab.marks_eq
    rw [← hme, Scheme.IdealSheafData.support_comap] at h2
    have hc' : (β' ≫ pullback.fst g tB) (M'.g x') = pullback.fst g ψ' (β x') := by
      rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
    rw [h1, h2, ← hx'₁, hc']
    rfl
  have hgm := genericMarksCondition_of_forall tB htB hss β' DB hss' hpts
  -- the spread model over `T_B`
  have hsp : IsSpreadModel (tB ≫ pS) (pullback.snd g tB) (D.comap (pullback.fst g tB)) β' DB :=
    { flat := inferInstance
      isSemistablePair := hss'
      genericMarks := hgm
      isRelativelyProjective := IsRelativelyProjective.comp_iso hprojB e.hom (by
        rw [← pullback.condition_assoc, reassoc_of% he₁])
      isoLocus := ⟨UB, hUBne, hqcU, hisoβ'⟩ }
  -- numerical stability at a geometric point over the centre of `W`
  let K := AlgebraicClosure (IsLocalRing.ResidueField W.valuationSubring)
  let fK : W.valuationSubring →+* K :=
    (algebraMap (IsLocalRing.ResidueField W.valuationSubring) K).comp
      (IsLocalRing.residue W.valuationSubring)
  let b : Spec (.of K) ⟶ c.pt := Spec.map (CommRingCat.ofHom fK)
  have hb : ∀ x, b x = specClosedPoint W := fun x ↦ by
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hx
    have : IsLocalHom (algebraMap (IsLocalRing.ResidueField W.valuationSubring) K) :=
      ⟨fun r hr ↦ isUnit_iff_ne_zero.mpr fun h ↦ hr.ne_zero (by rw [h, map_zero])⟩
    have : IsLocalHom (IsLocalRing.residue W.valuationSubring) := inferInstance
    have : IsLocalHom fK := RingHom.isLocalHom_comp _ _
    exact IsLocalRing.comap_closedPoint fK
  have hnb := hnum K b
  have H₁ : IsPullback M'.g β β' (M.g ≫ e.hom) := by
    have := hpb.paste_horiz (IsPullback.of_horiz_isIso (fst := 𝟙 M'.Y) (snd := βB) (f := β')
      (g := e.hom) ⟨by rw [Category.id_comp]⟩)
    rwa [Category.comp_id] at this
  have H₂ : IsPullback (M.g ≫ e.hom) (pullback.snd g ψ') (pullback.snd g tB) (c.π.app B) := by
    have := M.isPullback.paste_horiz (IsPullback.of_horiz_isIso (fst := e.hom) (snd := M.fY)
      (f := pullback.snd g tB) (g := 𝟙 (Dg.obj B)) ⟨by rw [he₂, Category.comp_id]⟩)
    rwa [Category.comp_id] at this
  have hnB : NumericallyStableFibre β' (pullback.snd g tB) DB (b ≫ c.π.app B) := by
    rw [← numericallyStableFibre_iff_of_isPullback H₁ H₂ DB b, hDB]
    exact hnb
  -- spreading of numerical stability (node G4)
  have hlftB : LocallyOfFiniteType tB := by
    have e1 : Dg.map a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A (⊥ : Limits.FGSubalgebra A R).1)) =
          Spec.map (CommRingCat.ofHom (algebraMap A (B.unop.1 : Subalgebra A L))) := by
      change Spec.map _ ≫ _ = _
      rw [← Spec.map_comp]
      congr 1
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap A (B.unop.1 : Subalgebra A L)))) :=
      Limits.locallyOfFiniteType_specMap B.unop
    simp only [tB, a₀]
    rw [← Category.assoc, e1]
    infer_instance
  have : IsAffineHom tB := isAffineHom_of_isAffine_of_isSeparated tB
  have : IsVariety (tB ≫ pS) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)
        (f := tB ≫ pS)).mpr inferInstance }
  have hqrp : IsRelativelyProjective (tB ≫ pS) (pullback.snd g tB) :=
    (Projectivity.isRelativelyProjective_of_isProjectiveOver pS g hC).pullback_snd tB
  obtain ⟨O, hzO, hOst⟩ := hO (Dg.obj B) (tB ≫ pS) inferInstance (pullback g tB)
    (pullback.snd g tB) hqrp M'.Y β' hsp.isRelativelyProjective DB hss'
    (c.π.app B (specClosedPoint W)) K (b ≫ c.π.app B)
    (fun x ↦ by rw [Scheme.Hom.comp_apply, hb]; rfl) hnB
  -- an affine neighbourhood `T' ⊆ O` of the centre
  have hex : ∃ T' : (Dg.obj B).Opens, IsAffineOpen T' ∧ c.π.app B (specClosedPoint W) ∈ T' ∧
      (T' : Set (Dg.obj B)) ⊆ O := by
    obtain ⟨_, ⟨T', hT', rfl⟩, h1, h2⟩ := (Dg.obj B).isBasis_affineOpens.exists_subset_of_mem_open
      hzO O.isOpen
    exact ⟨T', hT', h1, h2⟩
  obtain ⟨T', hT', hzT', hT'O⟩ := hex
  have : IsAffine T'.toScheme := hT'
  have : Nonempty T' := ⟨⟨_, hzT'⟩⟩
  have hdomR : IsDominant toR := isDominant_SpecMap_of_injective _ Subtype.val_injective
  have hgenR : toR (genericPoint (Spec (.of L))) = genericPoint c.pt :=
    genericPoint_map_of_isDominant (X := Spec (.of L)) (Y := c.pt) toR
  have hgenT : genericPoint (Dg.obj B) ∈ T' :=
    ((genericPoint_spec (Dg.obj B)).mem_open_set_iff T'.isOpen).mpr ⟨_, trivial, hzT'⟩
  have hrη : Set.range (toR ≫ c.π.app B) ⊆ Set.range T'.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : y = genericPoint (Spec (.of L)) := Subsingleton.elim _ _
    rw [hy, Scheme.Hom.comp_apply, hgenR]
    have h := hgenT
    rw [← hgenB] at h
    exact h
  let ηT : Spec (.of L) ⟶ T'.toScheme := IsOpenImmersion.lift T'.ι (toR ≫ c.π.app B) hrη
  have hηT : ηT ≫ T'.ι = toR ≫ c.π.app B := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant ηT := by
    have : IsDominant (ηT ≫ T'.ι) := by rw [hηT]; infer_instance
    exact isDominant_of_comp_isOpenImmersion ηT T'.ι
  have hrW : Set.range (c.π.app B) ⊆ Set.range T'.ι := by
    rw [Scheme.Opens.range_ι]
    exact range_subset_of_specClosedPoint_mem (V := W) (S := Dg.obj B) (c.π.app B) hzT'
  let φW : Spec (.of W.valuationSubring) ⟶ T'.toScheme :=
    IsOpenImmersion.lift T'.ι (c.π.app B) hrW
  -- the base change of the spread model to `T'` is a stable model
  have hsp' := hsp.pullback T'.ι (genericPoint_eq_of_isOpenImmersion T'.ι)
  have hnum' : IsNumericallyStable (pullbackCompMap β' (pullback.snd g tB) T'.ι)
      (pullback.snd (pullback.snd g tB) T'.ι)
      (DB.comap (pullback.fst (β' ≫ pullback.snd g tB) T'.ι)) := by
    intro K' _ _ a'
    rw [numericallyStableFibre_pullback_iff]
    obtain ⟨y⟩ : Nonempty (Spec (.of K')) := inferInstance
    refine hOst (T'.ι (a' y)) (hT'O (a' y).2) K' (a' ≫ T'.ι) fun x ↦ ?_
    rw [Subsingleton.elim x y]
    rfl
  have hstab' := hsp'.toIsStableModel hnum'
  let E := pullbackLeftPullbackSndIso g tB T'.ι
  have hD' : (D.comap (pullback.fst g (T'.ι ≫ tB))).comap E.hom =
      (D.comap (pullback.fst g tB)).comap (pullback.fst (pullback.snd g tB) T'.ι) := by
    simp only [← Scheme.IdealSheafData.comap_comp, E, pullbackLeftPullbackSndIso_hom_fst]
  have hm := hstab'.comp_iso E.hom (pullbackLeftPullbackSndIso_hom_snd g tB T'.ι) hD'
  rw [show T'.ι ≫ tB ≫ pS = (T'.ι ≫ tB) ≫ pS from (Category.assoc _ _ _).symm] at hm
  refine ⟨{ T := T'.toScheme
            t := T'.ι ≫ tB
            V := V₀
            isAffineOpen := hV₀
            preimage_eq_top := ?_
            ηT := ηT
            comp_ηT := ?_
            X := _
            β := _
            D' := _
            isStableModel := hm }, φW, ?_⟩
  · simp only [tB, a₀, Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self,
      Scheme.Hom.preimage_top]
  · rw [reassoc_of% hηT]
    simp only [tB]
    rw [reassoc_of% hcw]
    exact hkey
  · change toSpecValuationSubring W ≫ φW = ηT
    rw [← cancel_mono T'.ι, Category.assoc, IsOpenImmersion.lift_fac, hηT, htoSpec]

end DeJongAlterations.StableModification.Global
