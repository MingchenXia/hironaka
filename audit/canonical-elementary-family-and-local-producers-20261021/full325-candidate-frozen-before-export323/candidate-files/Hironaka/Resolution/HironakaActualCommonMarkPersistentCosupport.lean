/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPersistentHSIdealRigidity
import Hironaka.Resolution.HironakaActualWeightedCoefficientCompression

/-!
# Actual common-mark control at persistent Hilbert--Samuel points

Whole generated-ideal factorization and exceptional cancellation retain one
prescribed family. Genuine Hilbert--Samuel profiles detect all entire point
powers. Actual centre admissibility then puts the whole common-mark control
inside the normalized-member ideal, hence in the actual point power at a
persistent geometric strict-transform point. No joint maximal-contact chart,
recursive tracking or finite persistent phase is asserted.
Blueprint: `hironaka-actual-common-mark-persistent-cosupport-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCommonMarkPersistentCosupport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  GermIdealOrder OkaRelationSheaf HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualAnalyticVertexCoefficientData HironakaActualFormalInitialDiagram
  HironakaActualFormalCoordinatePowerDivision HironakaActualCoefficientPresentationCentrePower
  HironakaActualPersistentHSIdealRigidity HironakaRelativeNormalIdeal
  HironakaSmoothCentreCoherentDomain HironakaActualPointGeometricBennett

section Algebra
variable {R S ι : Type*} [CommRing R] [CommRing S]

private theorem principal_mul_span (x : S) (H : ι → S) :
    Ideal.span {x}*Ideal.span (range H)=Ideal.span (range (fun i => x*H i)) := by
  rw [Ideal.span_mul_span']
  congr 1
  ext y
  simp only [Set.mem_mul,Set.mem_singleton_iff,Set.mem_range]
  constructor
  · rintro ⟨a,rfl,b,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨x,rfl,H i,⟨i,rfl⟩,rfl⟩

/-- The whole original image retains precisely the SAME weighted family at the common mark. -/
theorem map_span_common_mark_factor (f : R →+* S) (G : ι → R) (w : ι → ℕ)
    (x : S) (H : ι → S) (m : ℕ) (hm : ∀ i, m≤w i)
    (hH : ∀ i, x^(w i)*H i=f (G i)) :
    Ideal.map f (Ideal.span (range G))=
      Ideal.span {x^m}*Ideal.span (range (fun i => x^(w i-m)*H i)) := by
  rw [Ideal.map_span,principal_mul_span,← range_comp]
  apply congrArg Ideal.span
  congr 1
  funext i
  change f (G i)=x^m*(x^(w i-m)*H i)
  rw [← hH i,← mul_assoc,← pow_add,Nat.add_sub_of_le (hm i)]

variable [IsDomain S]

private theorem colon_principal_mul (x : S) (hx : x≠0) (J : Ideal S) :
    (Ideal.span {x}*J).colon {x}=J := by
  ext y
  rw [Submodule.mem_colon_singleton]
  change y*x ∈ Ideal.span {x}*J ↔ y ∈ J
  rw [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨z,hz,he⟩
    have hzy : z=y := mul_left_cancel₀ hx (he.trans (mul_comm y x))
    simpa only [hzy] using hz
  · intro hy
    exact ⟨y,hy,mul_comm x y⟩

/-- Exact ENTIRE common-mark colon, with all original positions and weights retained. -/
theorem colon_span_common_mark_eq (f : R →+* S) (G : ι → R) (w : ι → ℕ)
    (x : S) (hx : x≠0) (H : ι → S) (m : ℕ) (hm : ∀ i, m≤w i)
    (hH : ∀ i, x^(w i)*H i=f (G i)) :
    (Ideal.map f (Ideal.span (range G))).colon {x^m}=
      Ideal.span (range (fun i => x^(w i-m)*H i)) := by
  rw [map_span_common_mark_factor f G w x H m hm hH]
  exact colon_principal_mul _ (pow_ne_zero _ hx) _

/-- Actual common-mark control is contained in the whole unchanged normalized-family ideal. -/
theorem colon_span_common_mark_le_normalized_span (f : R →+* S) (G : ι → R) (w : ι → ℕ)
    (x : S) (hx : x≠0) (H : ι → S) (m : ℕ) (hm : ∀ i, m≤w i)
    (hH : ∀ i, x^(w i)*H i=f (G i)) :
    (Ideal.map f (Ideal.span (range G))).colon {x^m}≤Ideal.span (range H) := by
  rw [colon_span_common_mark_eq f G w x hx H m hm hH]
  apply Ideal.span_le.mpr
  rintro y ⟨i,rfl⟩
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
end Algebra

section ActualPointPowers
variable {n : ℕ}

/-- A true single HS value detects membership of the ENTIRE ideal in the matching point power. -/
theorem le_maximal_pow_iff_hilbertSamuelValue_eq_bot
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    I≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(ℓ+1) ↔
      hilbertSamuelValue I ℓ=hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel n))) ℓ := by
  let A := (I.restrictScalars ℂ).map (finiteJet (ℓ+1))
  have hrange : A≤LinearMap.range (finiteJet (n := n) (ℓ+1)) := by
    rintro v ⟨g,hg,rfl⟩
    exact LinearMap.mem_range_self _ _
  have hdim := Submodule.finrank_mono hrange
  have hzero : A=⊥ ↔ I≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(ℓ+1) := by
    constructor
    · intro h g hg
      have hm : finiteJet (ℓ+1) g ∈ A := Submodule.mem_map.mpr ⟨g,hg,rfl⟩
      rw [h] at hm
      have hk := LinearMap.mem_ker.mpr (show finiteJet (ℓ+1) g=0 from hm)
      rwa [ker_finiteJet] at hk
    · intro h
      apply eq_bot_iff.mpr
      rintro v ⟨g,hg,rfl⟩
      have hk : g ∈ LinearMap.ker (finiteJet (ℓ+1)) := by
        rw [ker_finiteJet]
        exact h hg
      exact LinearMap.mem_ker.mp hk
  have hb : ((⊥ : Ideal (HolGerm (ComplexModel n))).restrictScalars ℂ).map (finiteJet (ℓ+1))=⊥ := by
    simp
  rw [hilbertSamuelValue,hilbertSamuelValue,
    finrank_quotient_eq_jet_rank_sub_ideal_image_rank,
    finrank_quotient_eq_jet_rank_sub_ideal_image_rank,hb,finrank_bot, Nat.sub_zero]
  change I≤_ ↔ Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ+1)))-Module.finrank ℂ A=
    Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ+1)))
  rw [← hzero,← Submodule.finrank_eq_zero]
  omega

/-- Equal genuine original HS profiles preserve EVERY whole point-power inclusion. -/
theorem le_maximal_pow_iff_of_entire_hs_eq
    (I J : Ideal (HolGerm (ComplexModel n)))
    (hHS : ∀ ℓ : ℕ, hilbertSamuelValue I ℓ=hilbertSamuelValue J ℓ) (q : ℕ) :
    I≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
      J≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  cases q with
  | zero => simp
  | succ ℓ => rw [le_maximal_pow_iff_hilbertSamuelValue_eq_bot,
      le_maximal_pow_iff_hilbertSamuelValue_eq_bot,hHS ℓ]

/-- Each genuine coordinate-centre germ vanishes at the actual model origin. -/
theorem actualAnalyticCoordinateIdeal_le_maximal (A : Set (Fin n)) :
    actualAnalyticCoordinateIdeal A≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  apply Ideal.span_le.mpr
  rintro g ⟨i,hi,rfl⟩
  apply (HolGerm.mem_maximalIdeal_iff _).mpr
  simp [coordinateGerm]
end ActualPointPowers

/-- Actual centre admissibility internally constructs true common-mark quotients of the SAME generators. -/
theorem exists_actual_common_mark_quotients {n : ℕ} {ι : Type*}
    (I : Ideal (HolGerm (ComplexModel n))) (A : Set (Fin n))
    (e : Fin n) (he : e∈A) (b : Fin n → ℂ) (m : ℕ)
    (G : ι → HolGerm (ComplexModel n)) (hG : Ideal.span (range G)=I)
    (hcentre : I≤actualAnalyticCoordinateIdeal A^m) :
    ∃ K : ι → HolGerm (ComplexModel n),
      (∀ i, (coordinateGerm e)^m*K i=actualAnalyticBlowupPullback A e b (G i)) ∧
      Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I=
        Ideal.span {(coordinateGerm e)^m}*Ideal.span (range K) ∧
      (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I).colon {(coordinateGerm e)^m}=
        Ideal.span (range K) ∧
      Ideal.span (range K)≤actualAnalyticNormalizedMemberIdeal I A e b := by
  have hg (i : ι) : G i∈I := hG ▸ Ideal.subset_span ⟨i,rfl⟩
  choose K hK hT using fun i => exists_actualAnalyticBlowup_quotient A e he b m (G i) (hcentre (hg i))
  have hmap := map_span_common_mark_factor (actualAnalyticBlowupPullback A e b).toRingHom
    G (fun _ => m) (coordinateGerm e) K m (fun _ => le_rfl) hK
  simp only [Nat.sub_self,pow_zero,one_mul,hG] at hmap
  refine ⟨K,hK,hmap,?_,?_⟩
  · rw [hmap]
    exact colon_principal_mul _ (pow_ne_zero _ (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e)) _
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    exact Ideal.subset_span ⟨m,G i,hg i,hcentre (hg i),hK i⟩

/-- The ENTIRE actual common-mark colon lies in the entire normalized-member ideal. -/
theorem actual_common_mark_control_le_normalized {n : ℕ}
    (I : Ideal (HolGerm (ComplexModel n))) (A : Set (Fin n))
    (e : Fin n) (he : e∈A) (b : Fin n → ℂ) (m : ℕ)
    (hcentre : I≤actualAnalyticCoordinateIdeal A^m) :
    (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I).colon {(coordinateGerm e)^m}≤
      actualAnalyticNormalizedMemberIdeal I A e b := by
  have hgen : Ideal.span (range (fun g : I => (g : HolGerm (ComplexModel n))))=I := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by rintro _ ⟨g,rfl⟩; exact g.property)
    · intro g hg
      exact Ideal.subset_span ⟨⟨g,hg⟩,rfl⟩
  obtain ⟨K,hK,hmap,hcolon,hle⟩ := exists_actual_common_mark_quotients I A e he b m _ hgen hcentre
  rw [hcolon]
  exact hle

/-- Actual entire HS persistence forces genuine common-mark controlled cosupport in the normal chart. -/
theorem actual_common_mark_control_le_maximal_pow_of_persistent_hs (d t m : ℕ) (ht : 2≤t)
    (W : Set (ComplexModel (d+t))) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : I=originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
    (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hP : ∀ a, P.generator a ∈ normalIdeal d t^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (hcentre : I≤normalIdeal d t^m) (j : Fin t) (b : Fin (d+t) → ℂ)
    (hHS : ∀ ℓ : ℕ, hilbertSamuelAt (vanishingIdeal (n := d+t)
        (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ=
      hilbertSamuelValue I ℓ) :
    (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom I).colon
      {(coordinateGerm (j.natAdd d))^m}≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^m := by
  have he : j.natAdd d∈actualTangentCentreVariables d t := ⟨j,rfl⟩
  have hc : I≤actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^m := by
    rwa [actualAnalyticCoordinateIdeal_normal]
  have hnorm := actual_common_mark_control_le_normalized I _ _ he b m hc
  rw [actual_normalized_ideal_eq_geometric_of_persistent_hs d t ht W I hI P hP j b hHS] at hnorm
  apply hnorm.trans
  apply (le_maximal_pow_iff_of_entire_hs_eq I _ (fun ℓ => ?_) m).mp
  · exact hc.trans (pow_le_pow_left' (actualAnalyticCoordinateIdeal_le_maximal _) m)
  · simpa only [hilbertSamuelAt_model_zero] using (hHS ℓ).symm

/-- Every literal analytic representative of a common-mark quotient has genuine order-m point vanishing. -/
theorem actual_common_mark_quotient_vanishes_of_persistent_hs (d t m : ℕ) (ht : 2≤t)
    (W : Set (ComplexModel (d+t))) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : I=originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
    (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hP : ∀ a, P.generator a ∈ normalIdeal d t^
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (hcentre : I≤normalIdeal d t^m) (j : Fin t) (b : Fin (d+t) → ℂ)
    (hHS : ∀ ℓ : ℕ, hilbertSamuelAt (vanishingIdeal (n := d+t)
        (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ=
      hilbertSamuelValue I ℓ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g∈I)
    (f : ComplexModel (d+t) → ℂ) (hf : HolAt f 0)
    (hprod : (coordinateGerm (j.natAdd d))^m*HolGerm.mk f hf=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b g) :
    VanishesToOrderOn (d+t) univ 0 m f := by
  have hmem : HolGerm.mk f hf ∈
      (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom I).colon
        {(coordinateGerm (j.natAdd d))^m} := by
    rw [Submodule.mem_colon_singleton]
    change HolGerm.mk f hf*(coordinateGerm (j.natAdd d))^m∈_
    rw [mul_comm,hprod]
    exact Ideal.mem_map_of_mem _ hg
  have hm := actual_common_mark_control_le_maximal_pow_of_persistent_hs d t m ht W I hI P hP hcentre j b hHS hmem
  exact ⟨f,(mem_maximalIdeal_pow_iff_point_power hf m).mp hm,Eventually.of_forall (fun _ _ => rfl)⟩

end
end Hironaka.HironakaActualCommonMarkPersistentCosupport
