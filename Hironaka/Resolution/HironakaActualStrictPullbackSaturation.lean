/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualStrictRadicalPullback
import Hironaka.Resolution.HironakaRelativeNormalAnalyticGraphQuotient
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
/-!
# The whole geometric strict ideal is the genuine exceptional saturation

Actual coherent colon generators and analytic Nullstellensatz prove a genuine
off-divisor membership-to-whole-power criterion. Literal rational inverse
functions identify the independently defined WHOLE pullback vanishing ideals
off the exceptional coordinate, without a supplied inverse or smoothness
certificate. The original analytic subset internally supplies coherence;
actual holomorphic sheaf/ring pullback compatibility then proves its ENTIRE
geometric strict ideal is the saturation of its WHOLE total pullback ideal.
Actual Noetherianity chooses ONE fixed finite power colon equal to that ideal.
No radicality, desired ideal equality or Hilbert--Samuel persistence is input.

Blueprint: `hironaka-actual-strict-pullback-saturation-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualStrictPullbackSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  OkaRelationSheaf OkaCoherence OkaIdealOperations RelativePrincipalizationSpan
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalAnalyticGraphQuotient HironakaActualPointGeometricBennett
  HironakaActualPointExceptionalVanishing HironakaActualNormalBlowupExceptionalLocus
  HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientPresentationCentrePower
  HironakaActualStrictExceptionalRegularity HironakaActualStrictRadicalPullback
variable {n : ℕ}

/-- Genuine coherent-colon generators and analytic Nullstellensatz turn ALL nearby off-divisor membership into a whole original power. -/
theorem exists_coordinate_power_mul_mem_of_off_divisor_membership
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent)
    (G : ComplexModel n → ℂ) (hG : HolAt G 0) (e : Fin n)
    (hOff : ∀ᶠ y in 𝓝 (0 : ComplexModel n),y e≠0→I.mem y G) :
    ∃ N : ℕ,(coordinateGerm e)^N*HolGerm.mk G hG∈originalCoherentOriginIdeal I := by
  have hfg := germIdeal_actual_finitely_generated I hI
  obtain ⟨U,hU,h0U,μ,hμ,H,hH,hgen⟩ := IdealFGAt.colon (okaProperty_euclidean n) hfg hG
  let := hμ
  let E := Fintype.equivFin μ
  let F := fun j : Fin (Fintype.card μ) => H (E.symm j)
  have hH0 (i : μ) : HolAt (H i) 0 := holAt_of_differentiableOn hU (hH i) h0U
  have hF (i) : HolAt (F i) 0 := hH0 (E.symm i)
  let L := (originalCoherentOriginIdeal I).colon {HolGerm.mk G hG}
  have hmem (i : μ) : HolGerm.mk (H i) (hH0 i)∈L := by
    rw [Submodule.mem_colon_singleton,smul_eq_mul,← HolGerm.mk_mul _ _ (hH0 i) hG]
    apply (mk_mem_originalCoherentOriginIdeal_iff I hI _).mpr
    exact ((hgen 0 h0U (H i)).mpr (inSpanAt_self hH0 i)).2
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n),(∀ i,F i z=0)→z e=0 := by
    filter_upwards [hOff,hU.mem_nhds h0U] with z hz hzU hzF
    by_contra hze
    have hcolon : colonIdeal I.mem G z (fun _ => (1 : ℂ)) := by
      refine ⟨holAt_const 1 z,?_⟩
      simpa only [one_mul] using hz hze
    obtain ⟨_hone,a,_ha,he⟩ := (hgen z hzU (fun _ => (1 : ℂ))).mp hcolon
    have hez := he.self_of_nhds
    have hHz (i : μ) : H i z=0 := by
      simpa only [F,Equiv.symm_apply_apply] using hzF (E i)
    simp only [hHz,mul_zero,Finset.sum_const_zero] at hez
    exact one_ne_zero hez
  have he : HolAt (fun z : ComplexModel n => z e) 0 :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hc : coordinateGerm e∈L.radical := by
    apply RueckertNullstellensatz.vanishingIdeal_le_radical L F (fun i => ⟨hF i,hmem (E.symm i)⟩)
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr hzero
  obtain ⟨N,hN⟩ := Ideal.mem_radical_iff.mp hc
  exact ⟨N,Submodule.mem_colon_singleton.mp hN⟩

/-- The actual rational inverse, holomorphic on the genuine open exceptional complement. -/
def actualBlowupInverse (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) : ComplexModel n → ComplexModel n :=
  fun x => (EuclideanSpace.equiv (Fin n) ℂ).symm (fun i =>
    if i∈A then if i=e then x e else x i/x e-b i else x i)

private theorem blowup_exceptional_coordinate (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (y : ComplexModel n) : actualAnalyticBlowupMap A e b y e=y e := by
  simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate]

private theorem inverse_exceptional_coordinate (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (x : ComplexModel n) : actualBlowupInverse A e b x e=x e := by simp [actualBlowupInverse]

theorem actualBlowupInverse_differentiableAt (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (x : ComplexModel n) (hx : x e≠0) : DifferentiableAt ℂ (actualBlowupInverse A e b) x := by
  apply (differentiableAt_piLp 2).mpr
  intro i
  change DifferentiableAt ℂ (fun x : ComplexModel n =>
    if i∈A then if i=e then x e else x i/x e-b i else x i) x
  split_ifs
  · exact (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
  · have hi : DifferentiableAt ℂ (fun z : ComplexModel n => z i) x :=
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
    have he : DifferentiableAt ℂ (fun z : ComplexModel n => z e) x :=
      (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
    have hinv : DifferentiableAt ℂ (fun z : ComplexModel n => (z e)⁻¹) x :=
      (hasDerivAt_inv hx).differentiableAt.comp x he
    simpa only [div_eq_mul_inv,Pi.mul_apply] using (hi.mul hinv).sub_const (b i)
  · exact (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt

theorem actualBlowupInverse_left (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (y : ComplexModel n) (hy : y e≠0) :
    actualBlowupInverse A e b (actualAnalyticBlowupMap A e b y)=y := by
  ext i
  change (if i∈A then if i=e then actualAnalyticBlowupMap A e b y e else
    actualAnalyticBlowupMap A e b y i/actualAnalyticBlowupMap A e b y e-b i else
    actualAnalyticBlowupMap A e b y i)=y i
  simp only [blowup_exceptional_coordinate]
  by_cases hiA : i∈A
  · by_cases hie : i=e
    · subst i
      simp only [if_pos hiA,ite_true]
    · simp only [if_pos hiA,if_neg hie]
      rw [actualAnalyticBlowupMap_apply]
      simp only [actualAnalyticBlowupCoordinate,if_pos hiA,if_neg hie]
      field_simp
      ring
  · simp [hiA,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate]

theorem actualBlowupInverse_right (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (x : ComplexModel n) (hx : x e≠0) :
    actualAnalyticBlowupMap A e b (actualBlowupInverse A e b x)=x := by
  ext i
  rw [actualAnalyticBlowupMap_apply]
  unfold actualAnalyticBlowupCoordinate
  rw [inverse_exceptional_coordinate]
  by_cases hiA : i∈A
  · by_cases hie : i=e
    · subst i
      simp only [if_pos hiA,ite_true]
    · simp only [if_pos hiA,if_neg hie]
      have hi : actualBlowupInverse A e b x i=x i/x e-b i := by simp [actualBlowupInverse,hiA,hie]
      rw [hi]
      field_simp
      ring
  · simp [hiA,actualBlowupInverse]

private theorem inverse_holomorphic_near (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (x : ComplexModel n) (hx : x e≠0) :
    ∀ᶠ z in 𝓝 x,DifferentiableAt ℂ (actualBlowupInverse A e b) z := by
  filter_upwards [(EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hx] with z hz
  exact actualBlowupInverse_differentiableAt A e b z hz

/-- Literal actual inverse functions prove the ENTIRE independently defined vanishing-ideal pullback off the divisor. -/
theorem pullback_vanishingIdeal_mem_iff_off_coordinate
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (W : Set (ComplexModel n))
    (y : ComplexModel n) (hy : y e≠0) (G : ComplexModel n → ℂ) :
    (GermIdeal.pullback (m := n) (actualAnalyticBlowupMap A e b) (vanishingIdeal (n := n) W)).mem y G ↔
      (vanishingIdeal (n := n) ((actualAnalyticBlowupMap A e b) ⁻¹' W)).mem y G := by
  constructor
  · exact BlowupStrictIdeal.pullback_vanishingIdeal_le (differentiable_actualAnalyticBlowupMap A e b).continuous W y G
  · rintro ⟨hG,hzero⟩
    let π := actualAnalyticBlowupMap A e b
    let R := actualBlowupInverse A e b
    let x := π y
    have hxe : x e≠0 := by simpa only [x,π,blowup_exceptional_coordinate] using hy
    have hRx : R x=y := actualBlowupInverse_left A e b y hy
    have ht : Tendsto R (𝓝 x) (𝓝 y) := by
      have h : Tendsto R (𝓝 x) (𝓝 (R x)) :=
        (actualBlowupInverse_differentiableAt A e b x hxe).continuousAt.tendsto
      rwa [hRx] at h
    have hsource : HolAt (G∘R) x := by
      filter_upwards [inverse_holomorphic_near A e b x hxe,ht.eventually hG] with z hz hGz
      exact hGz.differentiableAt.comp z hz
    have hsourceZero : ∀ᶠ z in 𝓝 x,z∈W→(G∘R) z=0 := by
      filter_upwards [ht.eventually hzero,
        (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hxe] with z hz hze hzW
      apply hz
      change actualAnalyticBlowupMap A e b (actualBlowupInverse A e b z)∈W
      rw [actualBlowupInverse_right A e b z hze]
      exact hzW
    refine ⟨hG,1,fun _ => (G∘R)∘π,fun _ _ => 1,?_,?_,?_⟩
    · exact fun _ => ⟨G∘R,⟨hsource.mono fun _ h => h.mdifferentiableAt,hsourceZero⟩,rfl⟩
    · exact fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const
    · filter_upwards [(EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hy] with z hz
      simp only [Fin.sum_univ_one,one_mul]
      change G z=G (actualBlowupInverse A e b (actualAnalyticBlowupMap A e b z))
      rw [actualBlowupInverse_left A e b z hz]

/-- Genuine origin germ composition of a holomorphic map fixing zero. -/
def actualHolomorphicOriginPullback {m : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ η) (hη0 : η 0=0) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel m) :=
  compAlgHom η (Eventually.of_forall fun z =>
    (hη.contMDiffAt (x := z)).mdifferentiableAt (by simp) |>.differentiableAt) hη0

/-- Entire original sheaf and ring pullbacks coincide under actual holomorphic maps fixing zero. -/
theorem originalOriginIdeal_holomorphic_pullback_eq {m : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ η) (hη0 : η 0=0)
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) :
    originalCoherentOriginIdeal (GermIdeal.pullback (m := m) η I)=
      Ideal.map (actualHolomorphicOriginPullback η hη hη0).toRingHom (originalCoherentOriginIdeal I) := by
  have hp : ∀ᶠ z in 𝓝 (0 : ComplexModel m),DifferentiableAt ℂ η z :=
    Eventually.of_forall fun z => (hη.contMDiffAt (x := z)).mdifferentiableAt (by simp) |>.differentiableAt
  have hJ := GermIdealPullbackCalculus.isCoherent_pullback hη hI
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    let S := fun s : ComplexModel m → ℂ => ∃ a,I.mem (η 0) a ∧ s=a∘η
    have hS : ∀ s,S s→HolAt s 0 := by
      rintro _ ⟨a,ha,rfl⟩
      have ha0 : I.mem 0 a := by simpa only [hη0] using ha
      exact holomorphic_comp η hp hη0 ((GermIdeal.IsCoherent.holomorphicAt_mem hI ha0).mono fun _ h => h.differentiableAt)
    apply whole_origin_span_mem _ S hS ?_ hf hIf
    rintro s ⟨a,ha,rfl⟩
    have ha0 : I.mem 0 a := by simpa only [hη0] using ha
    have hah : HolAt a 0 := (GermIdeal.IsCoherent.holomorphicAt_mem hI ha0).mono fun _ h => h.differentiableAt
    change HolGerm.mk (a∘η) _∈Ideal.map (compAlgHom η hp hη0).toRingHom (originalCoherentOriginIdeal I)
    rw [← compAlgHom_mk η hp hη0 a hah]
    exact Ideal.mem_map_of_mem _ ((mk_mem_originalCoherentOriginIdeal_iff I hI hah).mpr ha0)
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    change compAlgHom η hp hη0 (HolGerm.mk f hf)∈originalCoherentOriginIdeal (GermIdeal.pullback (m := m) η I)
    rw [compAlgHom_mk]
    have hc := holomorphic_comp η hp hη0 hf
    apply (mk_mem_originalCoherentOriginIdeal_iff _ hJ hc).mpr
    refine ⟨hc.mono (fun _ h => h.mdifferentiableAt),1,fun _ => f∘η,fun _ _ => 1,?_,?_,?_⟩
    · exact fun _ => ⟨f,by simpa only [hη0] using hIf,rfl⟩
    · exact fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const
    · exact Eventually.of_forall fun _ => by simp

private theorem contMDiff_blowup (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualAnalyticBlowupMap A e b) := by
  have hp (i : Fin n) : ContDiff ℂ ∞ (fun z : ComplexModel n => z i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff
  have hc (i : Fin n) : ContDiff ℂ ∞ (actualAnalyticBlowupCoordinate A e b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp e
    · exact (hp e).mul ((contDiff_const (c := b i)).add (hp i))
    · exact hp i
  exact ((EuclideanSpace.equiv (Fin n) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff

/-- Actual original analytic geometry ALONE identifies the WHOLE geometric strict ideal with exceptional saturation of the WHOLE total pullback. -/
theorem mem_original_analytic_strict_ideal_iff_exists_coordinate_power
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n := d+t) W)
    (g : HolGerm (ComplexModel (d+t))) :
    g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) ↔
      ∃ N : ℕ,(coordinateGerm (j.natAdd d))^N*g∈
        Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) := by
  let A := actualTangentCentreVariables d t
  let e := j.natAdd d
  let π := actualAnalyticBlowupMap A e b
  let I := vanishingIdeal (n := d+t) W
  let J := GermIdeal.pullback (m := d+t) π I
  have hI : I.IsCoherent := CartanIrreducible.cartanCoherence W hW
  have hπ := contMDiff_blowup A e b
  have hπ0 : π 0=0 := actualAnalyticBlowupMap_zero A e b
  have hJ : J.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hπ hI
  have hmap : originalCoherentOriginIdeal J=
      Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I) := by
    exact originalOriginIdeal_holomorphic_pullback_eq π hπ hπ0 I hI
  have hπnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),DifferentiableAt ℂ π z :=
    Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap A e b).differentiableAt
  have htπ : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (0 : ComplexModel (d+t))) := by
    have h : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (π 0)) := hπ.continuous.tendsto 0
    rwa [hπ0] at h
  constructor
  · intro hg
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    have hzero := (mk_mem_original_vanishing_origin_ideal_iff _ G hG).mp hg
    obtain ⟨U,hUprop,hU,h0U⟩ := eventually_nhds_iff.mp (hG.and hzero)
    have hOff : ∀ᶠ y in 𝓝 (0 : ComplexModel (d+t)),y e≠0→J.mem y G := by
      filter_upwards [hU.mem_nhds h0U] with y hy hye
      apply (pullback_vanishingIdeal_mem_iff_off_coordinate A e b W y hye G).mpr
      have hGU : DifferentiableOn ℂ G U := fun z hz => (hUprop z hz).1.differentiableWithinAt
      refine ⟨(holAt_of_differentiableOn hU hGU hy).mono (fun _ h => h.mdifferentiableAt),?_⟩
      filter_upwards [hU.mem_nhds hy,
        (EuclideanSpace.proj e : ComplexModel (d+t) →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hye]
        with z hz hze hzW
      apply (hUprop z hz).2
      rw [strictTransform,exceptionalLocus_actual_normal_blowup_eq d t ht j b]
      exact subset_closure ⟨hzW,hze⟩
    obtain ⟨N,hN⟩ := exists_coordinate_power_mul_mem_of_off_divisor_membership J hJ G hG e hOff
    exact ⟨N,by rwa [hmap] at hN⟩
  · rintro ⟨N,hN⟩
    apply (coordinate_pow_mul_mem_geometric_strict_ideal_iff d t ht j b W N g).mp
    have hle : Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I)≤
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨F,hF,hFW,rfl⟩
      change actualAnalyticBlowupPullback A e b (HolGerm.mk F hF)∈
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (strictTransform (d+t) π W))
      rw [actualAnalyticBlowupPullback,compAlgHom_mk]
      apply (mk_mem_original_vanishing_origin_ideal_iff _ (F∘π) _).mpr
      apply eventually_zero_on_closure_of_eventually_continuous (F∘π)
        (π ⁻¹' W\exceptionalLocus (d+t) π)
        ((holomorphic_comp π hπnear hπ0 hF).mono fun _ h => h.continuousAt)
      filter_upwards [htπ.eventually hFW.2] with z hz hzS
      exact hz hzS.1
    exact hle hN

private theorem mem_origin_colon_chain_iff {R : Type*} [CommRing R]
    (I : Ideal R) (a : R) (q : ℕ) (x : R) : x∈actualOriginColonChain I a q ↔ a^q*x∈I := by
  induction q generalizing x with
  | zero => simp only [actualOriginColonChain,pow_zero,one_mul]
  | succ q ih =>
    rw [actualOriginColonChain,Submodule.mem_colon_singleton,smul_eq_mul,ih]
    simp only [pow_succ,mul_assoc,mul_left_comm,mul_comm]

private theorem exists_fixed_power_colon {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (a : R) : ∃ N : ℕ,∀ x : R,(∃ q : ℕ,a^q*x∈I)↔a^N*x∈I := by
  let f : ℕ →o Submodule R R := ⟨actualOriginColonChain I a,actualOriginColonChain_monotone I a⟩
  obtain ⟨N,hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) f
  refine ⟨N,fun x => ⟨?_,fun hx => ⟨N,hx⟩⟩⟩
  rintro ⟨q,hq⟩
  have hq' := (mem_origin_colon_chain_iff I a q x).mpr hq
  have hm := actualOriginColonChain_monotone I a (le_max_left q N) hq'
  have hs : actualOriginColonChain I a (max q N)=actualOriginColonChain I a N :=
    (hN (max q N) (le_max_right q N)).symm
  rw [hs] at hm
  exact (mem_origin_colon_chain_iff I a N x).mp hm

/-- ONE genuine finite colon, internally selected by actual Noetherianity, equals the ENTIRE original geometric strict ideal. -/
theorem exists_original_analytic_strict_fixed_power_colon
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n := d+t) W) :
    ∃ N : ℕ,
      (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
        (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))).colon {(coordinateGerm (j.natAdd d))^N}=
      originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
        (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) := by
  let := isNoetherianRing_holGerm_euclidean (d+t)
  obtain ⟨N,hN⟩ := exists_fixed_power_colon
    (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
      (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))) (coordinateGerm (j.natAdd d))
  refine ⟨N,?_⟩
  ext g
  rw [Submodule.mem_colon_singleton,smul_eq_mul,mul_comm]
  exact (hN g).symm.trans (mem_original_analytic_strict_ideal_iff_exists_coordinate_power d t ht j b W hW g).symm

end
end Hironaka.HironakaActualStrictPullbackSaturation
