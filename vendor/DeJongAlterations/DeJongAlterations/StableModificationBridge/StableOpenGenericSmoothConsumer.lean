import DeJongAlterations.StableModification.Global.MainConn

/-! The actual main consumer needs corrected stable-openness ONLY for its genuinely smooth
native generic fibre. The extra premise is DERIVED inside the actual descended-model proof.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace DeJongAlterations.StableModification.Global
universe u
open DeJong (IsSemistablePair IsRelativelyProjective IsMultipointedCurve)
open Curves (pullbackCompMap IsStableModification)
open RiemannZariskiSpace

def StableOpenNbhdConnGenericSmooth (k : Type u) [Field k] : Prop :=
  ∀ (U : Scheme.{u}) (pU : U ⟶ Spec (.of k)) (hU : IsVariety pU),
    letI : IsVariety pU := hU
    ∀ (C : Scheme.{u}) (q : C ⟶ U), IsRelativelyProjective pU q →
    ∀ (X : Scheme.{u}) (β : X ⟶ C), IsRelativelyProjective (q ≫ pU) β →
    ∀ (D' : X.IdealSheafData), IsSemistablePair (β ≫ q) D' →
    Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint U)) →
    ∀ (z : U) (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ U), (∀ x, a x = z) →
      NumericallyStableFibre β q D' a → NoContractedClopen β q a →
      ∃ O : U.Opens, z ∈ O ∧ ∀ z' ∈ O, IsNumericallyStableAt β q D' z'


set_option backward.isDefEq.respectTransparency false in
/-- **Local stable pieces from the corrected spreading statement** (`PLAN-T5.md` §2.1 steps 1–2,
nodes G1, G3′, G4; ERRATA DJA-O36). The proof of `exists_localStablePiece` with
`StableOpenNbhdConnGenericSmooth k` in place of `StableOpenNbhd k`: the extra hypothesis `NoContractedClopen` at
the geometric point over the centre of `W` holds for the stable modification over `W`
(`noContractedClopen_of_isStableModification`: Zariski connectedness of its closed fibre, which
maps onto the closed fibre of `C ×_S Spec W`, of dimension one) and transports to the descended
model. For every valuation ring `W ∈ RZ_L(S)` there is a local stable piece `T` with
`W ∈ RZ_L(T)`. -/
theorem exists_localStablePiece_conn_genericSmooth {k : Type u} [Field k] {S C : Scheme.{u}}
    (pS : S ⟶ Spec (.of k)) [IsVariety pS] (hSp : IsProjectiveOver pS) (g : C ⟶ S)
    (D : C.IdealSheafData) (hC : IsProjectiveOver (g ≫ pS)) (hD : IsMultipointedCurve g D)
    (hsm : Smooth (g.fiberToSpecResidueField (genericPoint S)))
    (hss : IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
      (DeJong.fiberMarks g D (genericPoint S)))
    (hgi : GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)))
    {L : Type u} [Field L] [IsAlgClosed L] [Algebra S.functionField L]
    [Algebra.IsAlgebraic S.functionField L]
    (hE : ValuationStableExistence.{u}) (hO : StableOpenNbhdConnGenericSmooth k)
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
  have hsmB : Smooth ((β' ≫ pullback.snd g tB).fiberToSpecResidueField
      (genericPoint (Dg.obj B))) := by
    let : Smooth ((pullback.snd g tB).fiberToSpecResidueField (genericPoint (Dg.obj B))) :=
      smooth_fiber_pullback_snd g hsm tB htB
    rw [← Curves.fiberMap_fiberToSpecResidueField β' (pullback.snd g tB)
      (genericPoint (Dg.obj B))]
    infer_instance
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
  let t₀ : Spec (.of W.valuationSubring) := IsLocalRing.closedPoint W.valuationSubring
  let K := AlgebraicClosure ((Spec (.of W.valuationSubring)).residueField t₀)
  let ι : (Spec (.of W.valuationSubring)).residueField t₀ ⟶ .of K :=
    CommRingCat.ofHom (algebraMap ((Spec (.of W.valuationSubring)).residueField t₀) K)
  let b : Spec (.of K) ⟶ c.pt := Spec.map ι ≫ (Spec (.of W.valuationSubring)).fromSpecResidueField t₀
  have hb : ∀ x, b x = specClosedPoint W := fun x ↦ by
    change (Spec (.of W.valuationSubring)).fromSpecResidueField t₀ (Spec.map ι x) = _
    rw [Scheme.fromSpecResidueField_apply]
    rfl
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
  -- no contracted clopen subset at the centre (ERRATA DJA-O36)
  have hfibW : ((pullback.snd g ψ') ⁻¹' {IsLocalRing.closedPoint W.valuationSubring}).Nontrivial := by
    have : IsIntegral (pullback g ψ') := hV.isIntegral
    have : UniversallyClosed (pullback.snd g ψ') := inferInstance
    refine nontrivial_preimage_snd_of_hasPureFiberDimension hD.pureFibers ψ' ?_
    exact Cohomology.Connected.nonempty_fiber_of_flat (pullback.snd g ψ') _
  have hιint : ι.hom.IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  have hncb : NoContractedClopen β (pullback.snd g ψ') b :=
    noContractedClopen_of_isStableModification hV hstab hproj hfibW ι hιint
  have hncB : NoContractedClopen β' (pullback.snd g tB) (b ≫ c.π.app B) :=
    (noContractedClopen_iff_of_isPullback H₁ H₂ b).mp hncb
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
    (pullback.snd g tB) hqrp M'.Y β' hsp.isRelativelyProjective DB hss' hsmB
    (c.π.app B (specClosedPoint W)) K (b ≫ c.π.app B)
    (fun x ↦ by rw [Scheme.Hom.comp_apply, hb]; rfl) hnB hncB
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


/-- **A locally projective stable modification exists, from the corrected spreading statement**
(`PLAN-T5.md` §1.2, node G8; obligations E1–E4 of PLAN-OM3 §6; ERRATA DJA-O36). The statement of
`hasLocallyProjectiveStableModification` with `StableOpenNbhdConnGenericSmooth k` in place of
`StableOpenNbhd k`. -/
theorem hasLocallyProjectiveStableModification_conn_genericSmooth {k : Type u} [Field k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhdConnGenericSmooth k) :
    ∀ (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) (_ : IsVariety pS), IsNormalScheme S →
      IsProjectiveOver pS →
      ∀ (C : Scheme.{u}) (g : C ⟶ S) (D : C.IdealSheafData),
        IsProjectiveOver (g ≫ pS) → IsMultipointedCurve g D →
        Smooth (g.fiberToSpecResidueField (genericPoint S)) →
        IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
          (DeJong.fiberMarks g D (genericPoint S)) →
        GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)) →
        HasLocallyProjectiveStableModification k pS g D := by
  intro S pS hv _ hSp C g D hC hD hsm hss hgi
  have : IsProper pS := hSp.isProper
  have : S.IsSeparated := ⟨by rw [← terminal.comp_from pS]; infer_instance⟩
  have : IsProper (g ≫ pS) := hC.isProper
  have : IsProper g := IsProper.of_comp g pS
  let L := AlgebraicClosure S.functionField
  have hUo : StableModelUniqueOver pS g D L :=
    stableModelUniqueOver_of hU hC hD hsm hss hgi
      (fun W hW ↦ finite_primeSpectrum_of_mem (pS := pS) W hW)
      (fun W hW ↦ exists_expChar_of_mem (pS := pS) W hW)
  exact hasLocallyProjectiveStableModification_of_pieces pS hSp g D hC hD L
    (fun W hW ↦ exists_localStablePiece_conn_genericSmooth pS hSp g D hC hD hsm hss hgi hE hO W hW)
    (fun P₁ P₂ W h₁ h₂ ↦ exists_comparisonPiece hUo P₁ P₂ W h₁ h₂)

/-- **Temkin's stable modification theorem from the corrected spreading statement**
(`DeJong.TemkinStableModification k`, Temkin Thm 1.5 with Thm 1.1; `PLAN-T5.md` §1.1, node G8;
ERRATA DJA-O36): the statement of `temkinStableModification` with `StableOpenNbhdConnGenericSmooth k` in place
of `StableOpenNbhd k`. -/
theorem temkinStableModification_conn_genericSmooth {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhdConnGenericSmooth k) (hP : StableModificationProjectivity k) :
    DeJong.TemkinStableModification k :=
  temkinStableModification_of_hasLocallyProjective hP
    (hasLocallyProjectiveStableModification_conn_genericSmooth hE hU hO)

/-- **De Jong's alteration theorem from the corrected inputs** (blueprint `cor:sm-gso-dejong`):
from existence and uniqueness of stable modifications over valuation rings, the corrected
spreading of numerical stability `StableOpenNbhdConnGenericSmooth k` (ERRATA DJA-O36) and the projectivity of
locally projective stable modifications. -/
theorem deJongAlterationTheorem_conn_genericSmooth {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhdConnGenericSmooth k) (hP : StableModificationProjectivity k) :
    DeJongAlterationTheorem k :=
  DeJong.deJongAlterationTheorem_of_stableModification (temkinStableModification_conn_genericSmooth hE hU hO hP)


end DeJongAlterations.StableModification.Global
