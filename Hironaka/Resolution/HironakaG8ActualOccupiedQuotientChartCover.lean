import Hironaka.Resolution.HironakaG8OccupiedQuotientAtlasRestart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ActualOccupiedQuotientChartCover
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualWeightedNormalPadding HironakaActualRelativeNormalGeometry HironakaActualCentreJointJets
  IdealWeightPowers GermIdealOrder HironakaG8OccupiedQuotientAtlasRestart
  ResolutionInvariantSpec HironakaG8PrincipalRetainedEpochFinite DivisorExponentAlong
  HironakaG8NativeRestartQuotientChartProvider HironakaG8NativeRelativeClearing

private theorem principal_mul_generated_family
    {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (u : X → ℂ) (f : ι → X → ℂ) (hu : ∀ x, HolomorphicAt n u x)
    (hf : ∀ x i, HolomorphicAt n (f i) x) :
    (finiteFunctionIdeal (n := n) (fun _ : Unit => u)).mul (finiteFunctionIdeal f) =
      finiteFunctionIdeal (fun i => u * f i) := by
  ext x g
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (mem_mul_iff.mp hg)
    rintro _ ⟨a,b,ha,hb,rfl⟩
    have ha' : IsInSpanAt (n := n) (fun z => z ∈ range (fun _ : Unit => u)) x a := ha
    have hb' : IsInSpanAt (n := n) (fun z => z ∈ range f) x b := hb
    obtain ⟨N,s,c,hs,hc,hEq⟩ := MarkedIdealOperationsAlong.IsInSpanOnAt.mul (W := univ)
      (IsInSpanAt.restrict ha') (IsInSpanAt.restrict hb')
    refine ⟨ha'.1.mul hb'.1,N,s,c,?_,hc,hEq.mono fun _ h => h trivial⟩
    intro i
    obtain ⟨_,_,⟨_,rfl⟩,⟨j,rfl⟩,h⟩ := hs i
    exact ⟨j,h.symm⟩
  · intro hg
    apply mem_mul_iff.mpr
    refine IsInSpanAt.mono ?_ hg
    rintro _ ⟨i,rfl⟩
    exact ⟨u,f i,isInSpanAt_self ⟨(),rfl⟩ (hu x),isInSpanAt_self ⟨i,rfl⟩ (hf x i),rfl⟩

private theorem denominator_power_ideal_of_generator
    {n : ℕ} {Y : CMfd.{0} n} (D : GermIdeal n Y)
    (u : Y → ℂ) (hu : ∀ y, HolomorphicAt n u y) (d : ℕ)
    (hU : finiteFunctionIdeal (n := n) (fun _ : Unit => u) = D) :
    IdealWeightPowers.idealPow D d = finiteFunctionIdeal (n := n) (fun _ : Unit => u^d) := by
  ext x a
  have huGen (g : Y → ℂ) :
      D.mem x g ↔
        IsInSpanAt (n := n) (· = u) x g := by
    rw [← hU]
    change IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u)) x g ↔ _
    exact ⟨IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm),
      IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩)⟩
  change _ ↔ IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u^d)) x a
  rw [HironakaSharpActualProductNewExceptionalFactor.idealPow_principal_mem_iff (hu x) huGen]
  exact ⟨IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩),
    IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm)⟩


private theorem pullback_exceptional_generator_on_open
    {n : ℕ} {Y : CMfd.{0} n}
    (D : GermIdeal n Y) (V : Opens Y) (u : Y → ℂ)
    (hu : ∀ z ∈ V, HolomorphicAt n u z)
    (hGen : ∀ z ∈ V, ∀ g, D.mem z g ↔ IsInSpanAt (n := n) (· = u) z g) :
    GermIdeal.pullback (m := n) (Subtype.val : V → Y) D =
      finiteFunctionIdeal (n := n) (fun _ : Unit => u ∘ Subtype.val) := by
  ext z g
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨f,hf,rfl⟩
    have h := isInSpanAt_comp (f := (Subtype.val : V → Y)) contMDiff_subtype_val
      ((hGen z.val z.property f).mp hf)
    refine IsInSpanAt.mono ?_ h
    rintro _ ⟨b,rfl,rfl⟩
    exact ⟨(),rfl⟩
  · intro hg
    apply GermIdeal.mem_pullback_iff.mpr
    apply IsInSpanAt.mono _ hg
    rintro _ ⟨_,rfl⟩
    exact ⟨u,(hGen z.val z.property u).mpr (isInSpanAt_self rfl (hu z.val z.property)),rfl⟩

/-- Every genuine target point of the actual blowup has an open chart
carrying an actual exceptional equation and all simultaneous analytic
coefficient quotient equations. The source centre orders come entirely
from admissibility of the whole weighted source record. -/
theorem exists_local_weighted_quotient_functions
    {n : ℕ} {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (F i))
    (hCut : C ⊆ cosupport n univ (weightedFunctionIdeal w F) (weightedCommonMark w))
    (y : Y) :
    ∃ (V : Opens Y), y ∈ V ∧
      ∃ (u : V → ℂ) (q : ι → V → ℂ),
        MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) u ∧
        (∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (q i)) ∧
        finiteFunctionIdeal (n := n) (fun _ : Unit => u) =
          GermIdeal.pullback (m := n) (Subtype.val : V → Y) (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal ∧
        ∀ i (z : V), F i (π z.val) = u z ^ w i * q i z := by
  classical
  let D := (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal
  obtain ⟨O,hO,hy,u,hu,_,hGen⟩ := (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible y
  have hu' (z : Y) (hz : z ∈ O) : HolomorphicAt n u z :=
    holomorphicAt_of_mdifferentiableOn hO hu hz
  have hDiv (i : ι) : (idealPow D (w i)).mem y (F i ∘ π) := by
    let J := finiteFunctionIdeal (n := n) (fun _ : Unit => F i)
    have hJC : C ⊆ cosupport n univ J (w i) := by
      intro x hx
      have hx' := hCut hx
      rw [cosupport_weightedFunctionIdeal w hw F hF] at hx'
      exact mem_iInter.mp hx' i
    have hJ : J.IsCoherent := isCoherent_finiteFunctionIdeal _ (fun _ => hF i)
    have hP := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hJ hπ.1 hJC
    have hPull : (GermIdeal.pullback (m := n) π J).Le (idealPow D (w i)) := by
      rw [← BlowupExceptionalDivisor.pullback_idealPow_vanishingIdeal hπ]
      exact pullback_le_pullback hP
    apply hPull y _
    change (GermIdeal.pullback (m := n) π (finiteFunctionIdeal (fun _ : Unit => F i))).mem y _
    rw [finiteFunctionIdeal_pullback _ (fun _ => hF i) π hπ.contMDiff]
    exact isInSpanAt_self ⟨(),rfl⟩ (Eventually.of_forall fun z => (hF i).comp
      (hπ.contMDiff.mdifferentiable (by simp)) z)
  have hQuot (i : ι) : ∃ a : Y → ℂ, HolomorphicAt n a y ∧
      ∀ᶠ z in 𝓝 y, F i (π z) = a z * u z ^ w i := by
    have hs := (HironakaSharpActualProductNewExceptionalFactor.idealPow_principal_mem_iff
      (hu' y hy) (hGen y hy) (w i) (F i ∘ π)).mp (hDiv i)
    obtain ⟨_,a,ha,heq⟩ := isInSpanAt_eq_iff.mp hs
    exact ⟨a,ha,heq⟩
  choose a ha hEq using hQuot
  have hGood : ∀ᶠ z in 𝓝 y, (∀ i, MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) z) ∧
      ∀ i, F i (π z) = a i z * u z ^ w i :=
    (eventually_all.mpr ha).and (eventually_all.mpr hEq)
  obtain ⟨W,hWSub,hWO,hyW⟩ := mem_nhds_iff.mp hGood
  let V : Opens Y := ⟨W ∩ O,hWO.inter hO⟩
  have hV (z : V) : z.val ∈ O := z.property.2
  have hVal (z : V) : MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (Subtype.val : V → Y) z :=
    (contMDiff_subtype_val (n := ∞) z).mdifferentiableAt (by simp)
  refine ⟨V,⟨hyW,hy⟩,u ∘ Subtype.val,fun i => a i ∘ Subtype.val,?_,?_,?_,?_⟩
  · intro z
    exact (hu' z.val (hV z)).self_of_nhds.comp z
      (hVal z)
  · intro i z
    exact ((hWSub z.property.1).1 i).comp z (hVal z)
  · exact (pullback_exceptional_generator_on_open D V u (fun z hz => hu' z hz.2)
      (fun z hz => hGen z hz.2)).symm
  · intro i z
    exact ((hWSub z.property.1).2 i).trans (mul_comm _ _)

/-- On the chosen target subwindow the actual native controlled record has
the whole weighted quotient ideal, with no target ideal equality input. -/
theorem pullback_controlled_weighted_quotient_ideal
    {n : ℕ} {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (Q : MarkedIdeal n X) (hq : IsInvDomain n Q) (hN : Q.N = univ)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (hC : Q.IsAdmissibleCentre C)
    (w : ι → ℕ) (hMark : Q.d = weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (F i))
    (hGen : Q.ideal = weightedFunctionIdeal w F)
    (V : Opens Y) (u : V → ℂ) (q : ι → V → ℂ)
    (hu : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) u)
    (hqHol : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (q i))
    (huIdeal : finiteFunctionIdeal (n := n) (fun _ : Unit => u) =
      GermIdeal.pullback (m := n) (Subtype.val : V → Y) (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
    (hEq : ∀ i (z : V), F i (π z.val) = u z ^ w i * q i z) :
    (MarkedIdeal.pullback (Subtype.val : V → Y) (Q.geoTransform C π)).ideal =
      weightedFunctionIdeal w q := by
  let B := CMfd.of (n := n) V
  let D := (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal
  let L := GermIdeal.pullback (m := n) (Subtype.val : V → Y) D
  let e := fun i => weightedCommonMark w / w i
  let R := weightedFunctionIdeal (n := n) w q
  have hR : R.IsCoherent := isCoherent_weightedFunctionIdeal w q hqHol
  have hu' (z : V) : HolomorphicAt n u z := Eventually.of_forall fun p => hu p
  have hPow := denominator_power_ideal_of_generator (Y := B) L u hu' (weightedCommonMark w) huIdeal
  have hTot : GermIdeal.pullback (m := n) (Subtype.val : V → Y)
      (GermIdeal.pullback (m := n) π Q.ideal) = (idealPow L (weightedCommonMark w)).mul R := by
    rw [← GermIdealTotalTransform.pullback_comp hπ.contMDiff contMDiff_subtype_val hq.isWellFormed.isCoherent,
      hGen,hPow]
    change GermIdeal.pullback (m := n) (π ∘ (Subtype.val : V → Y))
      (finiteFunctionIdeal (fun i => F i^e i)) =
      (finiteFunctionIdeal (fun _ : Unit => u ^ weightedCommonMark w)).mul
        (finiteFunctionIdeal (fun i => q i ^ e i))
    have hq' (z : V) (i : ι) : HolomorphicAt n (q i ^ e i) z :=
      Eventually.of_forall fun p => ((hqHol i).pow _) p
    rw [finiteFunctionIdeal_pullback _ (fun i => (hF i).pow _) _
      (hπ.contMDiff.comp contMDiff_subtype_val),
      principal_mul_generated_family (X := B) (u ^ weightedCommonMark w) (fun i => q i ^ e i)
        (fun z => CompanionReduction.holomorphicAt_pow_of (hu' z) _) hq']
    apply congrArg (finiteFunctionIdeal (n := n))
    funext i z
    change F i (π z.val) ^ e i = u z ^ weightedCommonMark w * q i z ^ e i
    rw [hEq,mul_pow,← pow_mul]
    change u z ^ (w i*(weightedCommonMark w / w i)) * q i z ^ e i = _
    rw [weight_mul_compressionExponent]
  have hQ1 : (Q.geoTransform C π).IsWellFormed :=
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hq (.step .refl C π hπ) ⟨trivial,hC⟩).isWellFormed
  have hD : D.IsCoherent := DivisorMetric.isCoherent_of_isInvertible (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible
  have hInit := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN hq.isWellFormed.isCoherent hC
  have hCtl := BlowupControlledTransform.pullback_eq_mul_controlledTransform hπ hq.isWellFormed.isCoherent hInit
  rw [← geoTransform_ideal_eq_controlledTransform hN hq.isWellFormed.isCoherent hπ] at hCtl
  rw [hCtl, GermIdealTotalTransform.pullback_mul contMDiff_subtype_val
    (GermIdealPullbackCalculus.isCoherent_idealPow hD _) hQ1.isCoherent,
    BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val hD, hMark] at hTot
  have hInv : L.IsInvertible := GermIdealTotalTransform.isInvertible_pullback
    (g := (Subtype.val : V → Y)) contMDiff_subtype_val
    (by rw [HironakaBaseChange.exceptionalLocus_val,interior_empty])
    (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible
  let A := MarkedIdeal.pullback (Subtype.val : V → Y) (Q.geoTransform C π)
  change (idealPow L (weightedCommonMark w)).mul A.ideal =
    (idealPow L (weightedCommonMark w)).mul R at hTot
  have h := congrArg (fun I => InvertibleIdealQuotient.colon I (idealPow L (weightedCommonMark w))) hTot
  have hi := BlowupExceptionalDivisor.isInvertible_idealPow hInv (weightedCommonMark w)
  have hA : A.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hQ1 V
  rw [BlowupControlledTransform.colon_mul_eq hi hA.isCoherent,
    BlowupControlledTransform.colon_mul_eq hi hR] at h
  exact h

/-- Complete raw nonfactor witnesses persist on the literal restriction
to an arbitrary target window. -/
theorem hasNoBoundaryFactor_pullback_val
    {n : ℕ} {Y : CMfd.{0} (n+1)} (Q : MarkedIdeal (n+1) Y)
    (hq : Q.IsWellFormed) (hNo : HasNoBoundaryFactor Q) (V : Opens Y) :
    HasNoBoundaryFactor (A := CMfd.of (n := n+1) V) (MarkedIdeal.pullback (Subtype.val : V → Y) Q) := by
  let A := MarkedIdeal.pullback (Subtype.val : V → Y) Q
  have hA : A.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hq V
  intro y hy i hi
  have hyQ : y.val ∈ Q.N := hy
  let j : Fin Q.E.length := ⟨i.val,by simpa [A,MarkedIdeal.pullback] using i.isLt⟩
  have hGet : A.E.get i = (Subtype.val : V → Y) ⁻¹' Q.E.get j := by
    simp [A,MarkedIdeal.pullback,j]
  have hiQ : y.val ∈ Q.E.get j := by
    change y ∈ A.E.get i at hi
    rw [hGet] at hi
    exact hi
  obtain ⟨g,hg,hNot⟩ := hNo y.val hyQ j hiQ
  have hgHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hq.isCoherent hg
  have hg' : A.ideal.mem y (g ∘ Subtype.val) := by
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨g,hg,rfl⟩
      (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall fun z : V => (contMDiff_subtype_val (n := ∞) z).mdifferentiableAt (by simp)) hgHol)
  refine ⟨g ∘ Subtype.val,hg',?_⟩
  intro hBad
  apply hNot
  apply (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem_of_isWellFormed hq hyQ j hgHol).mpr
  have hvHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA.isCoherent hg'
  have hVan := (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem_of_isWellFormed hA hy i hvHol).mp hBad
  refine ⟨hgHol,?_⟩
  rw [← V.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq y]
  apply Filter.eventually_map.mpr
  filter_upwards [hVan.2] with z hz hzE
  apply hz
  exact ⟨hzE.1,by rw [hGet]; exact hzE.2⟩

/-- The actual controlled cut is covered by genuine target windows,
each carrying the required low-source and weighted-native quotient data.
Only initial coefficient generation and target boundary nonfactor remain. -/
theorem actual_occupied_quotient_charts_cover
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    (P Q : MarkedIdeal (n+1) X) (hq : IsInvDomain (n+1) Q)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (n+1) C π)
    (hQC : Q.IsAdmissibleCentre C) (hQNo' : HasNoBoundaryFactor (Q.geoTransform C π))
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (hRaw : Q = ⟨univ,P.E,weightedFunctionIdeal w F,weightedCommonMark w⟩)
    (y : Y) : ∃ V : Opens Y, y ∈ V ∧ Nonempty (OccupiedCutNativeChart (ι := ι) P hπ V
      (MarkedIdeal.pullback (Subtype.val : V → Y) (Q.geoTransform C π)) d) := by
  have hCut : C ⊆ cosupport (n+1) univ (weightedFunctionIdeal w F) (weightedCommonMark w) := by
    have h := hQC.2.1
    rwa [hRaw] at h
  obtain ⟨V,hy,u,q,hu,hqHol,huIdeal,hQuot⟩ :=
    exists_local_weighted_quotient_functions hπ w hw F hF hCut y
  have hQN : Q.N = univ := congrArg MarkedIdeal.N hRaw
  have hQM := congrArg (fun A : MarkedIdeal (n+1) X => A.d) hRaw
  have hQI := congrArg (fun A : MarkedIdeal (n+1) X => A.ideal) hRaw
  have hQE := congrArg (fun A : MarkedIdeal (n+1) X => A.E) hRaw
  have hI := pullback_controlled_weighted_quotient_ideal Q hq hQN hπ hQC w hQM F hF hQI
    V u q hu hqHol huIdeal hQuot
  have hQ1 : (Q.geoTransform C π).IsWellFormed :=
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hq (.step .refl C π hπ) ⟨trivial,hQC⟩).isWellFormed
  let Qv := MarkedIdeal.pullback (Subtype.val : V → Y) (Q.geoTransform C π)
  have hRawv : Qv = ⟨univ,(MarkedIdeal.pullback (Subtype.val : V → Y) (P.geoTransform C π)).E,
      weightedFunctionIdeal w q,weightedCommonMark w⟩ := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hI hQM
    · change (Subtype.val : V → Y) ⁻¹' (Q.geoTransform C π).N = univ
      rw [geoTransform_N_eq_univ hQN hπ,preimage_univ]
    · have hBound : (Q.geoTransform C π).E = (P.geoTransform C π).E := by
        change Q.E.map _ ++ _ = P.E.map _ ++ _
        rw [hQE]
      exact congrArg (fun E : List (Set Y) => E.map ((Subtype.val : V → Y) ⁻¹' ·)) hBound
  let U : Opens X := ⊤
  have hMaps (z : V) : π z.val ∈ U := mem_univ _
  have hFv (i : ι) : MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (F i ∘ (Subtype.val : U → X)) :=
    (hF i).comp ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp))
  have hGenU : (MarkedIdeal.pullback (Subtype.val : U → X) P).ideal =
      finiteFunctionIdeal (fun i => (F i ∘ (Subtype.val : U → X)) ^ (d/w i)) := by
    change GermIdeal.pullback (m := n+1) (Subtype.val : U → X) P.ideal = _
    rw [hGen,finiteFunctionIdeal_pullback _ (fun i => (hF i).pow _) _ contMDiff_subtype_val]
    rfl
  refine ⟨V,hy,⟨⟨U,hMaps,w,hw,hWeights,hDvd,fun i => F i ∘ Subtype.val,hFv,hGenU,
    q,hqHol,u,hu,huIdeal,?_,hRawv,hasNoBoundaryFactor_pullback_val (Q.geoTransform C π) hQ1 hQNo' V⟩⟩⟩
  exact hQuot

/-- A real native source state gives an actual declared atlas on the whole
target of its occupied cut, with a verified quotient chart at every point. -/
theorem actual_native_occupied_quotient_atlas
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    (P Q : MarkedIdeal (n+1) X) (hq : IsInvDomain (n+1) Q)
    {W : Set X} {H : ℕ → ℕ} (hNative : HironakaG11PresLineState.NativeHSState Q W H)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (n+1) C π)
    (hQC : Q.IsAdmissibleCentre C) (hQNo' : HasNoBoundaryFactor (Q.geoTransform C π))
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (hRaw : Q = ⟨univ,P.E,weightedFunctionIdeal w F,weightedCommonMark w⟩) :
    let W' := strictTransform (n+1) π W
    ∃ A : NativeWindows Y Y W' (P.geoTransform C π).E H (HironakaG8NativePhaseCertificate.phaseLevel W' H),
      (∀ y, y ∈ A.openSet y) ∧ A.mark = Q.d ∧ (∀ y, A.exponent y = 1) ∧
      (∀ y, A.record y = MarkedIdeal.pullback (Subtype.val : A.openSet y → Y) (Q.geoTransform C π)) ∧
      ∀ y, Nonempty (OccupiedCutNativeChart (ι := ι) P hπ (A.openSet y) (A.record y) d) := by
  intro W'
  classical
  choose U hU hChart using fun y => actual_occupied_quotient_charts_cover P Q hq hπ hQC hQNo'
    w hw d hWeights hDvd F hF hGen hRaw y
  have hD1 := InvDomainTowerAlong.isInvDomain_geoTransformAlong hq (.step .refl C π hπ) ⟨trivial,hQC⟩
  have hNative1 := hNative.geoTransform hQC.1 hQC.2.1 hπ
  have hEqE := congrArg (fun A : MarkedIdeal (n+1) X => A.E) hRaw
  have hBound : (Q.geoTransform C π).E = (P.geoTransform C π).E := by
    change Q.E.map _ ++ _ = P.E.map _ ++ _
    rw [hEqE]
  let A : NativeWindows Y Y W' (P.geoTransform C π).E H (HironakaG8NativePhaseCertificate.phaseLevel W' H) :=
    { openSet := U
      record := fun y => MarkedIdeal.pullback (Subtype.val : U y → Y) (Q.geoTransform C π)
      domain := fun y => InvDomainTowerAlong.isInvDomain_pullback_val (U y) hD1
      native := fun y => hNative1.restrict (U y)
      boundary := fun y => congrArg (fun E : List (Set Y) => E.map ((Subtype.val : U y → Y) ⁻¹' ·)) hBound
      exponent := fun _ => 1
      positive := fun _ => le_rfl
      mark := Q.d
      commonMark := by
        intro y
        change Q.d*1 = Q.d
        exact Nat.mul_one Q.d
      covers := fun y _ => ⟨y,hU y⟩ }
  exact ⟨A,hU,rfl,fun _ => rfl,fun _ => rfl,hChart⟩

/-- A source with an already retained native maximal-order state and
the same normalized coefficient family has low nonmonomial order at
most the normalization mark everywhere. Thus it cannot at the same
time supply a strictly higher occupied entrance into that mark. -/
theorem normalized_source_order_cap_of_native_state
    {n : ℕ} {X : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q)
    (hPN : P.N = univ) {W : Set X} {H : ℕ → ℕ}
    (hNative : HironakaG11PresLineState.NativeHSState Q W H)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ) (hd : 1 < d)
    (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (hRaw : Q = ⟨univ,P.E,weightedFunctionIdeal w F,weightedCommonMark w⟩) :
    ∀ x : X, NonmonomialOrderLocal.nmOrd P x ≤ d := by
  let R : MarkedIdeal (n+1) X := {P with d := d}
  have hR : IsInvDomain (n+1) R :=
    ⟨⟨hp.isWellFormed.1,hp.isWellFormed.2,hp.isWellFormed.3,hp.isWellFormed.4⟩,
      hp.dimLE,by exact Nat.le_of_lt hd,hp.isNonzeroAlongAt⟩
  have hRShape : R = ⟨univ,P.E,finiteFunctionIdeal (fun i => F i ^ (d/w i)),d⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hPN rfl hGen rfl
  have hClass : HironakaG8LocalHistory.LocWPEquiv Q R := by
    have hR' := hR
    rw [hRShape] at hR' ⊢
    have hQ' := hq
    rw [hRaw] at hQ' ⊢
    exact (HironakaG8NativeCommonDenominatorReduction.common_denominator_native_boundary_class
      w hw F hF d (Nat.zero_lt_of_lt hd) hWeights hDvd P.E hR' hQ').1
  have hQd : Q.d = weightedCommonMark w := congrArg MarkedIdeal.d hRaw
  have hQn : Q.N = univ := congrArg MarkedIdeal.N hRaw
  have hLarge : 1 < Q.d := hd.trans_le ((Nat.le_of_dvd (weightedCommonMark_pos w hw) hDvd).trans_eq hQd.symm)
  have hMax := native_source_cap_of_state Q hNative hLarge
  have hOrd : ∀ x ∈ Q.cosupp,
      HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder Q.N Q.ideal x = Q.d := by
    intro x hx
    have hGe := HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff
      hq.isWellFormed.isClosedSubmanifold_N hq.isWellFormed.isCoherent hq.isNonzeroAlongAt
      (Q.cosupp_subset_N hx)
    exact le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge fun h => hMax x ((hGe _).mpr h)))
      ((hGe _).mp hx)
  have hRCap := HironakaG8EqualWeightNativeThresholds.reference_cap_of_native_active_order Q R hq hR
    (HironakaG11InvBMClass.SameCarrierDim.of_N_eq (hQn.trans hPN.symm)) hClass hOrd
  intro x
  apply NonmonomialOrderLocal.nmOrd_le_of_notMem
  intro hx
  apply hRCap x
  exact DerivativeIdealTower.cosupport_subset_of_le
    (NonmonomialTransformAlong.le_nonmonomialPartAlong_self hp.isWellFormed.isCoherent) (d+1) hx

end
end Hironaka.HironakaG8ActualOccupiedQuotientChartCover
