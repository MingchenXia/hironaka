import Hironaka.Resolution.HironakaActualAnalyticSourceShearTaylor
import Hironaka.Resolution.HironakaActualZeroNormalizedCurrentFamily
import Hironaka.Resolution.HironakaActualInheritedAdaptedWholePrefix
import Hironaka.Resolution.HironakaActualNormalAllDirectionAnalyticSaturation

/-! Arbitrary source directions internally produce a genuine analytic adapted
source and the SAME zero-normalized CURRENT analytic family. The analytic
source ideal is the literal image by the actual source shear and permutation.
No analytic realization, current family, diagram or prefix certificate is an
input. This does not compare the original and adapted geometric target charts.
Blueprint: hironaka-actual-analytic-adapted-current-family-extension.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticAdaptedCurrentFamily
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
 HironakaActualFormalInitialDiagram HironakaActualReducedBasisDivision
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticDirectionRemovalQuotient
 HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
 HironakaActualFormalBlowupAllDirections HironakaActualFormalStrictGenerators
 HironakaActualNormalMarkedDirection HironakaActualNormalAllDirectionConverse
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualNormalZeroOwnerSupport HironakaActualNormalZeroFormalSaturation
 HironakaActualOriginalFormalHSTransfer HironakaActualUnshiftedInitialHSTransfer
 HironakaActualFixedInheritedSelectorPermutation HironakaActualInheritedSourcePermutationFamily
 HironakaActualInheritedSourceOwnerPermutation HironakaActualInheritedWholePrefixNormalization
 HironakaActualRelativeStandardnessNormalPivotPriority HironakaActualAnalyticSourceShearTaylor
 HironakaActualZeroNormalizedCurrentFamily
variable {n : ℕ}

def actualAnalyticNormalAdaptedSourceIdeal
    (I : Ideal (HolGerm (ComplexModel (n+1)))) (q e f : Fin (n+1))
    (b : Fin (n+1) → ℂ) : Ideal (HolGerm (ComplexModel (n+1))) :=
  Ideal.map (actualPermutationGermEquiv (normalPivotEquiv q f)).toRingEquiv.toRingHom
    (Ideal.map (actualAnalyticDirectionShearGermEquiv (Set.Ici q) f
      (fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
        actualNormalMarkedDirection (Set.Ici q) e b f)).toRingEquiv.toRingHom I)

private theorem taylor_permutation_map {m : ℕ} (p : Fin m ≃ Fin m)
    (I : Ideal (HolGerm (ComplexModel m))) :
    Ideal.map (actualUnshiftedTaylorAlgHom m).toRingHom
        (Ideal.map (actualPermutationGermEquiv p).toRingEquiv.toRingHom I)=
      Ideal.map (MvPowerSeries.rename p).toRingHom
        (Ideal.map (actualUnshiftedTaylorAlgHom m).toRingHom I) := by
  rw [Ideal.map_map,Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro g
  exact actualTaylor_actualPermutationGermEquiv p g

private theorem cast_vertex_val {m : ℕ} {V W : Finset (Fin m →₀ ℕ)} (h : V=W) (a : V) :
    (sourceVertexSetCast h a).val=a.val := by cases h;rfl

/-- The arbitrary-direction formal adaptation is realized by actual analytic
source maps, then the same normalized members become a current analytic source.
Only original source powers, retained actual orders and original whole prefixes
are inputs. The literal current ideal and every current structural property are
internally constructed. -/
theorem exists_actual_analytic_adapted_current_family
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin (n+1)) (hqe : q≤e) (b : Fin (n+1) → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k) :
    ∃f : Fin (n+1),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      let IS:=actualAnalyticNormalAdaptedSourceIdeal I q e f b
      ∃GS : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) IS),
      ∃ES : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I) ≃
          actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) IS),
        (∀a,(ES a).val=Finsupp.domCongr (normalPivotEquiv q f) a.val) ∧
        (∀a,GS.germs (ES a)=actualPermutationGermEquiv (normalPivotEquiv q f)
          (actualAnalyticDirectionShearGermEquiv (Set.Ici q) f
            (fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
              actualNormalMarkedDirection (Set.Ici q) e b f) (G.germs a))) ∧
        (∀a,GS.germs a∈IS) ∧ (∀k,ActualInheritedPrefixReducedAt GS k) ∧
        ∃hpS : ∀a,GS.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
          (∀a,sameAnalyticZeroNormalizedVertex (n+1) IS GS q hpS a∈
            IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val) ∧
          let J:=sameAnalyticZeroNormalizedIdeal (n+1) IS GS q hpS
          actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) J)=
            actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) IS) ∧
          ∃hV : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) IS)=
              actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) J),
          ∃GT : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) J),
            (∀a,GT.germs (sourceVertexSetCast hV a)=sameAnalyticZeroNormalizedVertex (n+1) IS GS q hpS a) ∧
            Ideal.span (range GT.germs)=J ∧ (∀a,GT.germs a∈J) ∧
            (∀k,ActualInheritedPrefixReducedAt GT k) ∧
            ∀ℓ,hilbertSamuelValue J ℓ=hilbertSamuelValue I ℓ := by
  let K:=analyticZeroTaylorIdeal (n+1) I
  let B:=analyticZeroMonicFamily (n+1) I G hmem
  have hpF (a : actualInitialVertices MonomialOrder.degLex K) :
      B.series a∈actualFormalCoordinateIdeal (n+1) (Set.Ici q)^normalExponentDegree a.val :=
    actualTaylor_mem_coordinateCentre_pow (Set.Ici q) _ (G.germs a) (hp a)
  have hoF (a : actualInitialVertices MonomialOrder.degLex K) :
      actualNormalizedFormalMember (Set.Ici q) e hqe b (normalExponentDegree a.val)
        (B.series a) (hpF a)∈genuineFormalVariables (n+1)^normalExponentDegree a.val := by
    have h:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (n+1)).toRingHom (hOrder a)
    change actualUnshiftedTaylorAlgHom (n+1)
      (sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a)∈
      Ideal.map (actualUnshiftedTaylorAlgHom (n+1)).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val) at h
    rw [map_actualUnshifted_maximal_pow,actualTaylor_sameAnalyticNormalNormalizedVertex] at h
    exact h
  obtain ⟨f,hqf,hvf,E,BP,hpP,hlabel,hliteral,hoP,hHSP,_hStrict⟩:=
    exists_same_formal_normal_adapted_family_of_marked_orders K B q e hqe b hpF hoF
  let KP:=actualNormalAdaptedSourceIdeal K q e f b
  let p:=normalPivotEquiv q f
  let w (i : Fin (n+1)):=actualNormalMarkedDirection (Set.Ici q) e b i /
    actualNormalMarkedDirection (Set.Ici q) e b f
  let IS:=actualAnalyticNormalAdaptedSourceIdeal I q e f b
  have hIS : analyticZeroTaylorIdeal (n+1) IS=KP := by
    dsimp only [IS,analyticZeroTaylorIdeal,actualAnalyticNormalAdaptedSourceIdeal]
    rw [taylor_permutation_map,map_actualTaylor_analytic_source_shear (Set.Ici q) f hqf]
    rfl
  let F : actualInitialVertices MonomialOrder.degLex KP → HolGerm (ComplexModel (n+1)):=
    fun a=>actualPermutationGermEquiv p
      (actualAnalyticDirectionShearGermEquiv (Set.Ici q) f w (G.germs (E.symm a)))
  have hF (a : actualInitialVertices MonomialOrder.degLex KP) :
      actualUnshiftedTaylorAlgHom (n+1) (F a)=BP.series a := by
    dsimp only [F]
    rw [actualTaylor_actualPermutationGermEquiv,actualTaylor_analytic_source_shear (Set.Ici q) f hqf]
    simpa only [p,w,B,analyticZeroMonicFamily,normalPivotRename,Equiv.apply_symm_apply] using
      (hliteral (E.symm a)).symm
  have hPure (a : actualInitialVertices MonomialOrder.degLex KP)
      (i : Fin (n+1)) (hi : i≤q) : a.val i=0 :=
    pure_tail_of_monic_normal_mark_and_normalized_order q a.val (BP.series a)
      (BP.monic a) (hpP a) (hoP a) i hi
  have hval (a : actualInitialVertices MonomialOrder.degLex K) (i : Fin (n+1)) :
      (E a).val (p i)=a.val i := by
    rw [hlabel]
    simp only [p,sourceExponentPermutation_apply,Equiv.symm_apply_apply]
  have hdegree (a : actualInitialVertices MonomialOrder.degLex K) :
      normalExponentDegree (E a).val=normalExponentDegree a.val := by
    rw [hlabel]
    exact sourceExponentPermutation_degree p a.val
  have hSourceLegal (a : actualInitialVertices MonomialOrder.degLex K) :
      (↑a.val.support : Set (Fin (n+1)))⊆Set.Ici q\{f} := by
    intro i hi
    have hine:=Finsupp.mem_support_iff.mp hi
    refine ⟨?_,?_⟩
    · by_contra hiq
      have hlt : i < q := lt_of_not_ge hiq
      have hpi : p i=i:=normalPivotEquiv_tangent q f hqf i hlt
      exact hine ((hval a i).symm.trans (hPure (E a) (p i) (by rw [hpi];exact le_of_lt hlt)))
    · simp only [Set.mem_singleton_iff]
      intro hif
      subst i
      exact hine ((hval a f).symm.trans (hPure (E a) (p f)
        (by rw [show p f=q from normalPivotEquiv_pivot q f hqf])))
  have hPrefixF : ∀a c : actualInitialVertices MonomialOrder.degLex KP,
      normalExponentDegree c.val<normalExponentDegree a.val →∀α,c.val≤α →
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (n+1) (F a))=0 := by
    intro a c hca α hcα
    obtain ⟨a,rfl⟩:=E.surjective a
    obtain ⟨c,rfl⟩:=E.surjective c
    rw [hF,hliteral]
    apply shear_rename_cone_zero (Set.Ici q) f hqf w p c.val (hSourceLegal c) (B.series a)
      (hred (normalExponentDegree c.val) a (by simpa only [hdegree] using hca) c le_rfl) α
    simpa only [hlabel] using hcα
  let hV0:=congrArg (actualInitialVertices MonomialOrder.degLex) hIS.symm
  let GS : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) IS):=
    { germs:=sourceRawFamilyCast hV0 F
      monic:=by
        intro a
        obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV0).surjective a
        rw [sourceRawFamilyCast_apply,cast_vertex_val,hF]
        exact BP.monic a
      lower:=by
        intro a β hβ
        obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV0).surjective a
        rw [sourceRawFamilyCast_apply,hF]
        exact BP.lower a β (by simpa only [cast_vertex_val] using hβ) }
  have hGS (a) : GS.germs (sourceVertexSetCast hV0 a)=F a:=sourceRawFamilyCast_apply hV0 F a
  have hMember : ∀a,GS.germs a∈IS := by
    intro a
    obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV0).surjective a
    rw [hGS]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hmem (E.symm a)))
  have hPrefix : ∀k,ActualInheritedPrefixReducedAt GS k := by
    intro k a ha c hc α hcα
    obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV0).surjective a
    obtain ⟨c,rfl⟩:=(sourceVertexSetCast hV0).surjective c
    rw [hGS]
    apply hPrefixF a c (by simpa only [cast_vertex_val] using lt_of_le_of_lt hc ha) α
    simpa only [cast_vertex_val] using hcα
  have hpS : ∀a,GS.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    intro a
    obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV0).surjective a
    apply (mem_analytic_ideal_iff_actualUnshifted_extension (n+1) _ _).mpr
    rw [Ideal.map_pow,map_actualAnalyticCoordinateIdeal_taylor,hGS,hF,cast_vertex_val]
    exact hpP a
  have hoS : ∀a,sameAnalyticZeroNormalizedVertex (n+1) IS GS q hpS a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val := by
    intro a
    obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV0).surjective a
    have hNorm : actualUnshiftedTaylorAlgHom (n+1)
        (sameAnalyticZeroNormalizedVertex (n+1) IS GS q hpS (sourceVertexSetCast hV0 a))=
        sameMonicZeroNormalizedVertex KP BP q hpP a := by
      apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val) (actualFormalExceptional_ne_zero q))
      have hProduct:=congrArg (actualUnshiftedTaylorAlgHom (n+1))
        (sameAnalyticZeroNormalizedVertex_product (n+1) IS GS q hpS (sourceVertexSetCast hV0 a))
      have hPullback : actualUnshiftedTaylorAlgHom (n+1)
          (actualAnalyticBlowupPullback (Set.Ici q) q (fun _=>0) (GS.germs (sourceVertexSetCast hV0 a)))=
          actualFormalBlowup (Set.Ici q) q (fun _=>0)
            (actualUnshiftedTaylorAlgHom (n+1) (GS.germs (sourceVertexSetCast hV0 a))) :=
        DFunLike.congr_fun (actualTaylor_analyticBlowupPullback (Set.Ici q) q (fun _=>0)) _
      rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate,cast_vertex_val,hPullback,hGS,hF] at hProduct
      exact hProduct.trans (actualNormalizedFormalMember_spec (Set.Ici q) q
        (Set.mem_Ici.mpr le_rfl) (fun _=>0) (normalExponentDegree a.val) (BP.series a) (hpP a)).symm
    apply (mem_analytic_ideal_iff_actualUnshifted_extension (n+1) _ _).mpr
    rw [map_actualUnshifted_maximal_pow,hNorm,cast_vertex_val]
    exact hoP a
  obtain ⟨hD,hV,GT,hGT,hSpan,hMT,hPT,hHST⟩:=
    exists_same_zero_normalized_current_family IS GS hMember q hpS hoS hPrefix
  have hHSS (ℓ : ℕ) : hilbertSamuelValue IS ℓ=hilbertSamuelValue I ℓ := by
    rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,
      hilbertSamuelValue_eq_actual_unshifted_formal_extension]
    change genuineFormalHilbertSamuelValue (n+1) (analyticZeroTaylorIdeal (n+1) IS) ℓ=
      genuineFormalHilbertSamuelValue (n+1) K ℓ
    rw [hIS]
    exact hHSP ℓ
  refine ⟨f,hqf,hvf,GS,E.trans (sourceVertexSetCast hV0),?_,?_,hMember,hPrefix,
    hpS,hoS,hD,hV,GT,hGT,hSpan,hMT,hPT,fun ℓ=>(hHST ℓ).trans (hHSS ℓ)⟩
  · intro a
    change (sourceVertexSetCast hV0 (E a)).val=_
    rw [cast_vertex_val,hlabel]
  · intro a
    change GS.germs (sourceVertexSetCast hV0 (E a))=_
    rw [hGS]
    simp only [F,p,w,Equiv.symm_apply_apply]

end
end Hironaka.HironakaActualAnalyticAdaptedCurrentFamily
