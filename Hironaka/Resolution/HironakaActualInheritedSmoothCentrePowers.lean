import Hironaka.Resolution.HironakaActualInheritedHSContactContainment
import Hironaka.Resolution.HironakaSmoothCentreNearbyIdeal
import Hironaka.Resolution.HironakaActualPointGeometricBennett

/-! Actual ordinary orders on a smooth centre give the SAME members'
whole centre powers. An arbitrary supplied genuine flattening is retained;
no preservation of old heads, prefix support or selectors by that map is
asserted, and no centre hV or desired normal-power certificate is input. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualInheritedSmoothCentrePowers
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HolomorphicTaylorTail HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalIdeal
  HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaActualPointGeometricBennett HironakaActualInheritedHSContactContainment
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
  HironakaActualFormalInitialDiagram HironakaRelativeNormalMonomialBasis

variable {n : ℕ}

private theorem iterDeriv_zero_of_translated_maximal_power
    (q : ℕ) (p : ComplexModel n) (f : ComplexModel n → ℂ) (hf : HolAt f p)
    (hpower : translatedGerm p f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    (L : List (ComplexModel n)) (hL : L.length < q) : iterDeriv L f p = 0 := by
  have hjet := (mem_maximalIdeal_pow_iff_iteratedFDeriv (translated_holomorphic p hf) q).mp hpower
  have hz := hjet L.length hL
  rw [iteratedFDeriv_comp_add_right, zero_add] at hz
  obtain ⟨W, hWf, hW, hpW⟩ := eventually_nhds_iff.mp hf
  have hdiff : DifferentiableOn ℂ f W := fun z hz => (hWf z hz).differentiableWithinAt
  rw [OrderMultiplicativity.iterDeriv_eq_iteratedFDeriv hW hdiff L hpW, hz]
  rfl

/-- Actual ordinary orders at all nearby points of the plane internally
kill the WHOLE relative Taylor tuple and give its entire normal power. -/
theorem mem_normalIdeal_pow_of_nearby_point_orders (d t q : ℕ)
    (f : ComplexModel (d+t) → ℂ) (U : Set (ComplexModel (d+t)))
    (hU : IsOpen U) (h0U : (0 : ComplexModel (d+t)) ∈ U)
    (hhol : ∀ p ∈ U, HolAt f p)
    (horders : ∀ p (hp : p ∈ U), p ∈ complexCoordinatePlane (d+t) d →
      translatedGerm p f (hhol p hp) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q) :
    HolGerm.mk f (hhol 0 h0U) ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  apply mem_normalIdeal_pow_of_normalTaylorCoefficients_eq_zero d t q _
  funext w
  apply (relativeTaylorCoefficient_mk_eq_zero_iff d t (List.ofFn w.2) (hhol 0 h0U)).mpr
  have ht : Tendsto (tangentInclusion d t) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
  filter_upwards [ht.eventually (hU.mem_nhds h0U)] with c hc
  exact iterDeriv_zero_of_translated_maximal_power q (tangentInclusion d t c) f
    (hhol _ hc) (horders _ hc (tangentInclusion_mem_plane d t c))
    ((List.ofFn w.2).map (normalVector d t))
    (by simpa only [List.length_map, List.length_ofFn] using w.1.isLt)

private theorem maximal_power_reflects_genuine_equiv
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
    (q : ℕ) (g : HolGerm (ComplexModel n))
    (hEg : E g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) :
    g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  have hmap : Ideal.map E.symm.toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) =
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
    change Ideal.map (E.symm : HolGerm (ComplexModel n) →+* HolGerm (ComplexModel n))
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) = _
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective
      (E.symm : HolGerm (ComplexModel n) →+* HolGerm (ComplexModel n)) E.symm.surjective]
  have hm := Ideal.mem_map_of_mem E.symm.toRingEquiv.toRingHom hEg
  rw [hmap] at hm
  change E.symm (E g) ∈ _ at hm
  simpa only [AlgEquiv.symm_apply_apply] using hm

private theorem chartTranslatedGerm_model_point (x p : ComplexModel n)
    (hp : p ∈ (chartAt (ComplexModel n) x).source)
    (f : ComplexModel n → ℂ) (hf : HolomorphicAt n f p) :
    chartTranslatedGerm x p hp f hf =
      translatedGerm p f (hf.mono fun _ hz => hz.differentiableAt) := by
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp [chartAt_self_eq]

private theorem nearby_pullback_original_function
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (0 : ComplexModel n) 0))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) (0 : ComplexModel n)).target)
    (a : ComplexModel n) (ha : a ∈ Φ.target) (f : ComplexModel n → ℂ)
    (hf : HolAt f (actualFlatteningInverseMap 0 Φ a))
    (hF : HolAt (f ∘ actualFlatteningInverseMap 0 Φ) a) :
    actualNearbyGermEquiv Φ a ha
      (translatedGerm a (f ∘ actualFlatteningInverseMap 0 Φ) hF) =
        translatedGerm (actualFlatteningInverseMap 0 Φ a) f hf := by
  have heq : ((f ∘ actualFlatteningInverseMap 0 Φ) ∘ actualAffineTranslation n a) =
      (fun z => (f ∘ actualFlatteningInverseMap 0 Φ) (z+a)) := by
    funext z
    exact congrArg (f ∘ actualFlatteningInverseMap 0 Φ) (add_comm a z)
  have htr : HolAt ((f ∘ actualFlatteningInverseMap 0 Φ) ∘ actualAffineTranslation n a) 0 := by
    rw [heq]
    exact translated_holomorphic a hF
  have h := actualNearbyGermEquiv_original_function 0 Φ hsrc a ha f
    (hf.mono fun _ hz => hz.mdifferentiableAt) htr
  have hleft : HolGerm.mk ((f ∘ actualFlatteningInverseMap 0 Φ) ∘ actualAffineTranslation n a) htr =
      translatedGerm a (f ∘ actualFlatteningInverseMap 0 Φ) hF := by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg (f ∘ actualFlatteningInverseMap 0 Φ) (add_comm a z)
  rw [hleft] at h
  exact h.trans (chartTranslatedGerm_model_point _ _ _ _ _)

/-- ANY SAME supplied true flattening transports genuine point orders
to BOTH the exact inverse-image germ's normal power and the original
whole centre power. It does not assume preservation of old presentation
heads/support or a centre normal-flatness/canonical-power certificate. -/
theorem actual_member_mem_smooth_centre_power_in_flattening (d t q : ℕ)
    (C : Set (ComplexModel (d+t)))
    (f : ComplexModel (d+t) → ℂ) (U : Set (ComplexModel (d+t)))
    (hU : IsOpen U) (h0U : (0 : ComplexModel (d+t)) ∈ U)
    (hhol : ∀ p ∈ U, HolAt f p)
    (horders : ∀ p (hp : p ∈ U), p ∈ C →
      translatedGerm p f (hhol p hp) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (0 : ComplexModel (d+t)) 0))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) (0 : ComplexModel (d+t))).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) (0 : ComplexModel (d+t)) 0) = 0)
    (hflat : ∀ {y : ComplexModel (d+t)}, y ∈ (chartAt (ComplexModel (d+t)) 0).source →
      chartAt (ComplexModel (d+t)) 0 y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) 0 y) ∈ complexCoordinatePlane (d+t) d)) :
    let h0T := actualFlattening_target_zero_mem (0 : ComplexModel (d+t)) Φ h0
    let E := actualNearbyGermEquiv Φ 0 h0T
    E.symm (HolGerm.mk f (hhol 0 h0U)) ∈ normalIdeal d t ^ q ∧
      HolGerm.mk f (hhol 0 h0U) ∈
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) C) ^ q := by
  let η := actualFlatteningInverseMap (0 : ComplexModel (d+t)) Φ
  let F := f ∘ η
  have h0T := actualFlattening_target_zero_mem (0 : ComplexModel (d+t)) Φ h0
  have hη0 : η 0 = 0 := actualFlatteningInverseMap_zero (0 : ComplexModel (d+t)) Φ h0
  have hη (a : ComplexModel (d+t)) (ha : a ∈ Φ.target) : DifferentiableAt ℂ η a :=
    mdifferentiableAt_iff_differentiableAt.mp
      (actualFlatteningInverseMap_mdifferentiable (0 : ComplexModel (d+t)) Φ hsrc a ha)
  have hηOn : DifferentiableOn ℂ η Φ.target := fun a ha => (hη a ha).differentiableWithinAt
  let V := Φ.target ∩ η ⁻¹' U
  have hV : IsOpen V :=
    hηOn.continuousOn.isOpen_inter_preimage Φ.isOpen_target hU
  have h0V : (0 : ComplexModel (d+t)) ∈ V := by
    refine ⟨h0T, ?_⟩
    change η 0 ∈ U
    rw [hη0]
    exact h0U
  have hhat : ∀ a ∈ V, HolAt F a := by
    intro a ha
    filter_upwards [hV.mem_nhds ha] with b hb
    exact ((hhol (η b) hb.2).self_of_nhds).comp b (hη b hb.1)
  have hpoint : ∀ a (ha : a ∈ V), a ∈ complexCoordinatePlane (d+t) d →
      translatedGerm a F (hhat a ha) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
    intro a ha hplane
    have hdom := actualNearbyPoint_mem_flatDomain (0 : ComplexModel (d+t)) Φ hsrc a ha.1
    have hpC : η a ∈ C := by
      apply (hflat hdom.1 hdom.2).mpr
      rw [actualNearbyPoint_chart_value (0 : ComplexModel (d+t)) Φ hsrc a ha.1,
        Φ.right_inv a ha.1]
      exact hplane
    have hrep := nearby_pullback_original_function Φ hsrc a ha.1 f
      (hhol (η a) ha.2) (hhat a ha)
    apply maximal_power_reflects_genuine_equiv (actualNearbyGermEquiv Φ a ha.1) q _
    rw [hrep]
    exact horders (η a) ha.2 hpC
  have hN := mem_normalIdeal_pow_of_nearby_point_orders d t q F V hV h0V hhat hpoint
  let E := actualNearbyGermEquiv Φ 0 h0T
  have hrep : E (HolGerm.mk F (hhat 0 h0V)) = HolGerm.mk f (hhol 0 h0U) := by
    have h := nearby_pullback_original_function Φ hsrc 0 h0T f
      (hhol (η 0) h0V.2) (hhat 0 h0V)
    change E (translatedGerm 0 F (hhat 0 h0V)) =
      translatedGerm (η 0) f (hhol (η 0) h0V.2) at h
    simpa only [translatedGerm, hη0, add_zero] using h
  have hsymm : E.symm (HolGerm.mk f (hhol 0 h0U)) = HolGerm.mk F (hhat 0 h0V) := by
    apply E.injective
    rw [E.apply_symm_apply, hrep]
  have hmap : Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) =
      originalCoherentOriginIdeal (vanishingIdeal (n := d+t) C) ^ q := by
    have h := whole_nearby_vanishing_stalk_pow_eq_map (0 : ComplexModel (d+t)) C Φ hsrc hflat
      0 h0T (by simp [complexCoordinatePlane]) q
    simpa only [actualFlatteningInverseMap_zero (0 : ComplexModel (d+t)) Φ h0,
      wholeChartStalkIdeal_model_zero] using h.symm
  change E.symm (HolGerm.mk f (hhol 0 h0U)) ∈ normalIdeal d t ^ q ∧ _
  refine ⟨by rw [hsymm]; exact hN, ?_⟩
  have hm := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hN
  change E (HolGerm.mk F (hhat 0 h0V)) ∈
    Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) at hm
  rwa [hrep, hmap] at hm

/-- Original coherent HS constancy and the SAME current inherited whole
presentation produce every member's genuine smooth-centre power, with
no new canonical family, rank, hV or desired normal-power premise. -/
theorem actual_inherited_family_mem_hs_centre_powers (d t : ℕ)
    (A : GermIdeal (d+t) (ComplexModel (d+t))) (hA : A.IsCoherent)
    (G : ActualAnalyticInheritedFamily (d+t) 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (C : Set (ComplexModel (d+t))) (hreg : RegularAtDim (n := d+t) C 0 d)
    (hHS : ∀ p ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A p ℓ = hilbertSamuelAt A 0 ℓ) :
    ∀ a : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A),
      G.germs a ∈ originalCoherentOriginIdeal (vanishingIdeal (n := d+t) C) ^ normalExponentDegree a.val := by
  obtain ⟨_, _, Φ, hsrc, h0, hflat⟩ := hreg
  obtain ⟨H, hg, hG, U, hU, h0U, _hH, _hgen, hhol, horders⟩ :=
    exists_actual_inherited_hs_locus_member_orders A hA G hspan hred
  intro a
  have hpoint : ∀ p (hp : p ∈ U), p ∈ C →
      translatedGerm p (H a) (hhol p hp a) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ normalExponentDegree a.val := by
    intro p hp hCp
    exact horders p hp (fun _ _ => hHS p hCp _) a
  have hpow := actual_member_mem_smooth_centre_power_in_flattening d t
    (normalExponentDegree a.val) C (H a) U hU h0U (fun p hp => hhol p hp a) hpoint Φ hsrc h0 hflat
  rw [← hG a]
  exact hpow.2

end
end Hironaka.HironakaActualInheritedSmoothCentrePowers
