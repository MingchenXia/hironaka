import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
import Hironaka.Resolution.HironakaActualAnalyticSubspace

/-! Genuine auxiliary native quotient LRS for an ORIGINAL coherent ideal.
The literal existing A+I_C^q quotient at C=univ,q=1 is EXACTLY A.
No radical, tensor realization or altered reduced category is used.
BP FIRST: hironaka-nonreduced-analytic-quotient-model.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaNonreducedAnalyticQuotientModel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk
  HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
  HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The whole actual vanishing ideal of the ENTIRE ambient space is zero. -/
theorem whole_univ_ideal_eq_bot (y : M) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (univ : Set M)) y = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨f,hf,hmem,rfl⟩
  apply Ideal.mem_bot.mpr
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [actualOriginalFunctionGerm_chart,map_zero]
  have he : f =ᶠ[nhds y] fun _ => 0 := hmem.2.mono fun z hz => hz (mem_univ z)
  rw [chartTranslatedGerm_congr_original y f (fun _ => 0) hf (holomorphicAt_const 0) he]
  rfl

/-- Every true open has zero whole section ideal for vanishing on the ambient space. -/
theorem section_univ_ideal_eq_bot (U : Opens M) :
    actualSectionIdeal (vanishingIdeal (n := n) (univ : Set M)) U = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro s hs
  apply Ideal.mem_bot.mpr
  apply ContMDiffMap.ext
  intro z
  exact (actualSectionIdeal_vanishing_iff (n := n) univ U s).mp hs z.val z.property (mem_univ _)

/-- The existing literal section remainder is EXACTLY the original nonradical section ideal. -/
theorem remainderSectionIdeal_eq (A : GermIdeal n M) (U : Opens M) :
    actualRemainderSectionIdeal A univ 1 U = actualSectionIdeal A U := by
  simp only [actualRemainderSectionIdeal,actualCentrePowerSectionIdeal,
    section_univ_ideal_eq_bot,pow_one,sup_bot_eq]

/-- The same exact specialization holds in EVERY whole actual ambient stalk. -/
theorem wholeRemainderIdeal_eq (A : GermIdeal n M) (y : M) :
    actualWholeRemainderIdeal A univ 1 y = actualWholeSheafStalkIdeal A y := by
  simp only [actualWholeRemainderIdeal,whole_univ_ideal_eq_bot,pow_one,sup_bot_eq]

/-- Existing genuine native quotient presheaf, with its original section restrictions. -/
abbrev quotientPresheaf (A : GermIdeal n M) : (TopCat.of M).Presheaf CommRingCat :=
  actualRemainderQuotientPresheaf A univ 1

/-- Every literal section ring is the quotient by the SAME entire original ideal A. -/
def quotientSectionEquiv (A : GermIdeal n M) (U : Opens M) :
    ((quotientPresheaf A).obj (op U)).carrier ≃+*
      (actualComplexSection (n := n) U ⧸ actualSectionIdeal A U) :=
  Ideal.quotEquivOfEq (remainderSectionIdeal_eq A U)

/-- Existing coherent quotient-stalk theorem specialized to the exact original ideal A. -/
def rawStalkWholeEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    ((quotientPresheaf A).stalk y).carrier ≃+*
      (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal A y) :=
  (actualRemainderQuotientStalkWholeEquiv A hA univ 1 y).trans
    (Ideal.quotEquivOfEq (wholeRemainderIdeal_eq A y))

/-- EVERY actual quotient-section numerator retains its whole original quotient germ. -/
theorem rawStalkWholeEquiv_germ_mk (A : GermIdeal n M) (hA : A.IsCoherent)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) U) :
    rawStalkWholeEquiv A hA y ((quotientPresheaf A).germ U y hy
      (Ideal.Quotient.mk (actualRemainderSectionIdeal A univ 1 U) s)) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal A y)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) := by
  change Ideal.quotEquivOfEq (wholeRemainderIdeal_eq A y)
    (actualRemainderQuotientStalkWholeEquiv A hA univ 1 y _) = _
  rw [actualRemainderQuotientStalkWholeEquiv_germ_mk]
  rfl

/-- The genuine original ambient quotient morphism, before inverse image or sheafification. -/
def quotientAmbientPresheafMap (A : GermIdeal n M) :
    (actualComplexStructureSheaf (n := n) M).presheaf ⟶ quotientPresheaf A where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (actualRemainderSectionIdeal A univ 1 (unop U)))
  naturality _ _ _ := by ext s; rfl

private def ambientStalkHom (A : GermIdeal n M) (y : M) :
    actualComplexStructureStalk (n := n) y →+* ((quotientPresheaf A).stalk y).carrier :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
    (quotientAmbientPresheafMap A)).hom

private theorem rawStalkWholeEquiv_ambient (A : GermIdeal n M) (hA : A.IsCoherent)
    (y : M) (r : actualComplexStructureStalk (n := n) y) :
    rawStalkWholeEquiv A hA y (ambientStalkHom A y r) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal A y) r := by
  obtain ⟨U,hy,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  change rawStalkWholeEquiv A hA y
    (((TopCat.Presheaf.stalkFunctor CommRingCat y).map (quotientAmbientPresheafMap A))
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact rawStalkWholeEquiv_germ_mk A hA U y hy s

/-- The true inverse-image quotient presheaf on the original support; no reduced sheaf is used. -/
def quotientModelPresheaf (A : GermIdeal n M) : (TopCat.of A.zeroLocus).Presheaf CommRingCat :=
  (TopCat.Presheaf.pullback CommRingCat (actualSubspaceTopInclusion A.zeroLocus)).obj
    (quotientPresheaf A)

/-- Actual native ring sheafification on the genuine original zero locus. -/
def quotientModelSheaf (A : GermIdeal n M) : (TopCat.of A.zeroLocus).Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of A.zeroLocus)) CommRingCat).obj
    (quotientModelPresheaf A)

/-- The actual sheafification unit, retaining every original presheaf section. -/
def quotientModelUnit (A : GermIdeal n M) :
    quotientModelPresheaf A ⟶ (quotientModelSheaf A).presheaf :=
  toSheafify (Opens.grothendieckTopology (TopCat.of A.zeroLocus)) (quotientModelPresheaf A)

/-- The genuine sheafification unit induces its native ring-stalk isomorphism. -/
def quotientUnitStalkIso (A : GermIdeal n M) (x : A.zeroLocus) :
    (quotientModelPresheaf A).stalk x ≅ (quotientModelSheaf A).presheaf.stalk x := by
  let f := (TopCat.Presheaf.stalkFunctor (X := TopCat.of A.zeroLocus) CommRingCat x).map
    (quotientModelUnit A)
  have hf : IsIso f := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := TopCat.of A.zeroLocus) x CommRingCat (quotientModelPresheaf A)
  exact @asIso _ _ _ _ f hf

/-- WHOLE native quotient stalk: the ORIGINAL ideal A, including all its nilpotent structure. -/
def quotientStalkWholeEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus) :
    ((quotientModelSheaf A).presheaf.stalk x).carrier ≃+*
      (actualComplexStructureStalk (n := n) x.val ⧸ actualWholeSheafStalkIdeal A x.val) :=
  (quotientUnitStalkIso A x).symm.commRingCatIsoToRingEquiv.trans
    ((TopCat.Presheaf.stalkPullbackIso CommRingCat
      (actualSubspaceTopInclusion A.zeroLocus) (quotientPresheaf A) x).symm.commRingCatIsoToRingEquiv.trans
      (rawStalkWholeEquiv A hA x.val))

/-- The ENTIRE actual preferred-chart quotient by the original, possibly nonradical ideal. -/
def quotientStalkChartEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus) :
    ((quotientModelSheaf A).presheaf.stalk x).carrier ≃+*
      (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal A x.val x.val (mem_chart_source _ x.val)) :=
  (quotientStalkWholeEquiv A hA x).trans
    (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := n) x.val)
      (map_actualWholeSheafStalkIdeal A x.val).symm)

/-- Locality is derived from original zero-locus membership, never from a radical replacement. -/
theorem chartIdeal_le_maximalIdeal (A : GermIdeal n M) (x : A.zeroLocus) :
    wholeChartStalkIdeal A x.val x.val (mem_chart_source _ x.val) ≤
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨f,hf,hmem,rfl⟩
  apply (HolGerm.mem_maximalIdeal_iff _).mpr
  have hf0 : f x.val = 0 := x.property f hmem
  simpa [chartTranslatedGerm,translatedGerm,HolGerm.eval_mk,
    (chartAt (ComplexModel n) x.val).left_inv (mem_chart_source _ x.val)] using hf0

/-- The actual whole chart quotient is a nontrivial local ring at every support point. -/
theorem chartQuotient_isLocalRing (A : GermIdeal n M) (x : A.zeroLocus) :
    IsLocalRing (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal A x.val x.val (mem_chart_source _ x.val)) := by
  let I := wholeChartStalkIdeal A x.val x.val (mem_chart_source _ x.val)
  have hI : I ≠ ⊤ := by
    intro he
    have hle := chartIdeal_le_maximalIdeal A x
    change I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) at hle
    rw [he] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (HolGerm (ComplexModel n))).ne_top (top_le_iff.mp hle)
  let : Nontrivial (HolGerm (ComplexModel n) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Locality of EVERY actual quotient sheaf stalk is internally proved. -/
theorem quotientStalk_isLocalRing (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus) :
    IsLocalRing ((quotientModelSheaf A).presheaf.stalk x).carrier := by
  let := chartQuotient_isLocalRing A x
  exact (quotientStalkChartEquiv A hA x).symm.isLocalRing

/-- Genuine auxiliary native LRS; the original reduced category is unchanged. -/
@[implicit_reducible]
def quotientLocallyRingedSpace (A : GermIdeal n M) (hA : A.IsCoherent) : LocallyRingedSpace where
  carrier := TopCat.of A.zeroLocus
  presheaf := (quotientModelSheaf A).presheaf
  IsSheaf := (quotientModelSheaf A).property
  isLocalRing := quotientStalk_isLocalRing A hA

@[implicit_reducible]
private def inclusionRingedHom (A : GermIdeal n M) (hA : A.IsCoherent) :
    (quotientLocallyRingedSpace A hA).toPresheafedSpace ⟶
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M).toPresheafedSpace where
  base := actualSubspaceTopInclusion A.zeroLocus
  c := quotientAmbientPresheafMap A ≫
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
      (actualSubspaceTopInclusion A.zeroLocus)).unit.app (quotientPresheaf A) ≫
    (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion A.zeroLocus)).map
      (quotientModelUnit A)

private theorem inclusionRingedHom_stalk (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus)
    (r : actualComplexStructureStalk (n := n) x.val) :
    quotientStalkWholeEquiv A hA x ((inclusionRingedHom A hA).stalkMap x r) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal A x.val) r := by
  let Q := quotientPresheaf A
  let P := quotientModelPresheaf A
  let S := (quotientModelSheaf A).presheaf
  let i := actualSubspaceTopInclusion A.zeroLocus
  let u := quotientModelUnit A
  let E : Q.stalk x.val ≅ P.stalk x := TopCat.Presheaf.stalkPullbackIso CommRingCat i Q x
  have hfactor : (inclusionRingedHom A hA).stalkMap x r =
      (quotientUnitStalkIso A x).hom (E.hom (ambientStalkHom A x.val r)) := by
    obtain ⟨U,hx,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
    have hxZ : x ∈ (Opens.map i).obj U := hx
    have hAmbient : ambientStalkHom A x.val ((actualComplexStructureSheaf (n := n) M).presheaf.germ U x.val hx s) =
        Q.germ U x.val hx ((quotientAmbientPresheafMap A).app (op U) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x.val hx (quotientAmbientPresheafMap A) s
    have hP := ConcreteCategory.congr_hom
      (TopCat.Presheaf.germ_stalkPullbackHom CommRingCat i Q x U hx)
      ((quotientAmbientPresheafMap A).app (op U) s)
    simp only [ConcreteCategory.comp_apply] at hP
    have hS := TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map i).obj U) x hxZ u
      (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app Q).app (op U)
        ((quotientAmbientPresheafMap A).app (op U) s))
    have hP' : E.hom (Q.germ U x.val hx ((quotientAmbientPresheafMap A).app (op U) s)) =
        P.germ ((Opens.map i).obj U) x hxZ
          (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app Q).app (op U)
            ((quotientAmbientPresheafMap A).app (op U) s)) := hP
    have hFirst : (inclusionRingedHom A hA).stalkMap x
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U x.val hx s) =
        S.germ ((Opens.map i).obj U) x hxZ
          (u.app (op ((Opens.map i).obj U))
            (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app Q).app (op U)
              ((quotientAmbientPresheafMap A).app (op U) s))) :=
      PresheafedSpace.stalkMap_germ_apply (inclusionRingedHom A hA) U x hx s
    exact hFirst.trans (hS.symm.trans
      ((congrArg (fun a => (TopCat.Presheaf.stalkFunctor CommRingCat x).map u a) hP'.symm).trans
        (congrArg (fun a => (TopCat.Presheaf.stalkFunctor CommRingCat x).map u (E.hom a)) hAmbient.symm)))
  change rawStalkWholeEquiv A hA x.val
    (E.inv ((quotientUnitStalkIso A x).inv ((inclusionRingedHom A hA).stalkMap x r))) = _
  rw [hfactor,CategoryTheory.Iso.hom_inv_id_apply,CategoryTheory.Iso.hom_inv_id_apply]
  exact rawStalkWholeEquiv_ambient A hA x.val r

private theorem inclusionRingedHom_stalk_surjective (A : GermIdeal n M) (hA : A.IsCoherent)
    (x : A.zeroLocus) : Function.Surjective ((inclusionRingedHom A hA).stalkMap x) := by
  intro q
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (quotientStalkWholeEquiv A hA x q)
  refine ⟨r,(quotientStalkWholeEquiv A hA x).injective ?_⟩
  rw [inclusionRingedHom_stalk,hr]

/-- Actual FULL original quotient inclusion; its stalk maps are proved local. -/
@[implicit_reducible]
def quotientInclusion (A : GermIdeal n M) (hA : A.IsCoherent) :
    quotientLocallyRingedSpace A hA ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M where
  toHom := inclusionRingedHom A hA
  prop x := IsLocalHom.of_surjective _ (inclusionRingedHom_stalk_surjective A hA x)

/-- The original coherent ideal gives a genuinely closed support inclusion. -/
theorem quotientInclusion_isClosedEmbedding (A : GermIdeal n M) (hA : A.IsCoherent) :
    Topology.IsClosedEmbedding (quotientInclusion A hA).base :=
  (OrderTaylor.isClosed_zeroLocus_of_isCoherent hA).isClosedEmbedding_subtypeVal

/-- EVERY original ambient germ maps to its exact quotient class; this is the full scalar square. -/
theorem quotientInclusion_stalk (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus)
    (r : actualComplexStructureStalk (n := n) x.val) :
    quotientStalkWholeEquiv A hA x ((quotientInclusion A hA).stalkMap x r) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal A x.val) r :=
  inclusionRingedHom_stalk A hA x r

/-- The ENTIRE original ideal, not its radical, is the actual whole inclusion kernel. -/
theorem quotientInclusion_stalk_kernel (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus) :
    RingHom.ker ((quotientInclusion A hA).stalkMap x).hom = actualWholeSheafStalkIdeal A x.val := by
  ext r
  constructor
  · intro hr
    have hz := congrArg (quotientStalkWholeEquiv A hA x) hr
    rw [quotientInclusion_stalk,map_zero] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro hr
    apply (quotientStalkWholeEquiv A hA x).injective
    rw [quotientInclusion_stalk,map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- SAME whole ring equivalence, linear over the ORIGINAL ambient stalk through its actual structural map. -/
def quotientStalkAlgEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus) :
    letI : Algebra (actualComplexStructureStalk (n := n) x.val)
      ((quotientModelSheaf A).presheaf.stalk x).carrier := ((quotientInclusion A hA).stalkMap x).hom.toAlgebra
    ((quotientModelSheaf A).presheaf.stalk x).carrier ≃ₐ[actualComplexStructureStalk (n := n) x.val]
      (actualComplexStructureStalk (n := n) x.val ⧸ actualWholeSheafStalkIdeal A x.val) := by
  letI : Algebra (actualComplexStructureStalk (n := n) x.val)
      ((quotientModelSheaf A).presheaf.stalk x).carrier := ((quotientInclusion A hA).stalkMap x).hom.toAlgebra
  exact { quotientStalkWholeEquiv A hA x with commutes' r := quotientInclusion_stalk A hA x r }

/-- Every original quotient section maps through the actual adjunction and sheafification units. -/
def quotientSectionMap (A : GermIdeal n M) (U : Opens M) :
    (actualComplexSection (n := n) U ⧸ actualSectionIdeal A U) →+*
      (((quotientModelSheaf A).presheaf.obj
        (op ((Opens.map (actualSubspaceTopInclusion A.zeroLocus)).obj U)))).carrier :=
  ((quotientModelUnit A).app (op ((Opens.map (actualSubspaceTopInclusion A.zeroLocus)).obj U))).hom.comp
    ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
      (actualSubspaceTopInclusion A.zeroLocus)).unit.app (quotientPresheaf A)).app (op U)).hom.comp
      (quotientSectionEquiv A U).symm.toRingHom)

/-- ALL actual original quotient-section numerators retain their complete original quotient germ. -/
theorem quotientSectionMap_germ_mk (A : GermIdeal n M) (hA : A.IsCoherent)
    (U : Opens M) (x : A.zeroLocus) (hx : x.val ∈ U) (s : actualComplexSection (n := n) U) :
    quotientStalkWholeEquiv A hA x ((quotientModelSheaf A).presheaf.germ
      ((Opens.map (actualSubspaceTopInclusion A.zeroLocus)).obj U) x hx
        (quotientSectionMap A U (Ideal.Quotient.mk (actualSectionIdeal A U) s))) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal A x.val)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U x.val hx s) := by
  have h := PresheafedSpace.stalkMap_germ_apply (inclusionRingedHom A hA) U x hx s
  change quotientStalkWholeEquiv A hA x ((quotientModelSheaf A).presheaf.germ
    ((Opens.map (actualSubspaceTopInclusion A.zeroLocus)).obj U) x hx
      ((inclusionRingedHom A hA).c.app (op U) s)) = _
  exact (congrArg (quotientStalkWholeEquiv A hA x) h.symm).trans
    (inclusionRingedHom_stalk A hA x _)

/-- Any ORIGINAL nonzero nilpotent quotient class remains a nonzero nilpotent in the actual native stalk. -/
theorem nonzero_nilpotent_class (A : GermIdeal n M) (hA : A.IsCoherent) (x : A.zeroLocus)
    (r : actualComplexStructureStalk (n := n) x.val) (k : ℕ)
    (hr : r ∉ actualWholeSheafStalkIdeal A x.val) (hk : r^k ∈ actualWholeSheafStalkIdeal A x.val) :
    (quotientInclusion A hA).stalkMap x r ≠ 0 ∧ ((quotientInclusion A hA).stalkMap x r)^k = 0 := by
  have hker (s : actualComplexStructureStalk (n := n) x.val) :
      (quotientInclusion A hA).stalkMap x s = 0 ↔ s ∈ actualWholeSheafStalkIdeal A x.val := by
    change s ∈ RingHom.ker ((quotientInclusion A hA).stalkMap x).hom ↔ _
    rw [quotientInclusion_stalk_kernel]
  exact ⟨fun hz => hr ((hker r).mp hz),by rw [← map_pow]; exact (hker (r^k)).mpr hk⟩

end
end Hironaka.HironakaNonreducedAnalyticQuotientModel
