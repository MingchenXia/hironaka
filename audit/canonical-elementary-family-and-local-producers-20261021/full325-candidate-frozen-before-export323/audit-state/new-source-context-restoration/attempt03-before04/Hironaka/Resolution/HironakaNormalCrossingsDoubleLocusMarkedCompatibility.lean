/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsDoubleLocusSeparation
import Hironaka.Resolution.HironakaNormalCrossingsMarkedAdmissibility

/-! # Actual marking-one compatibility for ideals vanishing on the NC double locus

Actual coordinate axes in the NC double locus force zero linear jets at every
triple-or-higher point. Coherent Hadamard division then produces the square of
the true highest centre ideal, leaving an exceptional factor after the actual
marking-one controlled division. The input concerns the original zero locus;
no transformed cosupport or stage-admissibility certificate is supplied.
Blueprint: `hironaka-normal-crossings-double-locus-marked-compatibility-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsDoubleLocusMarkedCompatibility
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsDoubleLocusSeparation
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsSeparationChoiceComparison
  BlowupFlatCoordinates HolomorphicTaylorTail OrderTaylor HadamardBridge
  IdealWeightPowers GermIdealOrder RelativePrincipalizationSpan
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupControlledTransform InvertibleIdealQuotient BlowupExceptionalDivisor

noncomputable section
variable {n : ℕ}

/-- Actual axis vanishing forces the whole constant and linear jet to vanish. -/
theorem inNormalPow_two_of_axis_vanishing (hn : 0 < n) {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ w in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F w)
    (haxes : ∀ i : Fin n, ∀ᶠ t : ℂ in 𝓝 0,
      F (t • (EuclideanSpace.single i 1 : ComplexModel n)) = 0) :
    InNormalPow 0 (0 : ComplexModel n) 2 F := by
  have hF0 : F 0 = 0 := by
    simpa using (haxes ⟨0,hn⟩).self_of_nhds
  have hd (i : Fin n) : fderiv ℂ F 0 (EuclideanSpace.single i 1) = 0 := by
    have hcurve : HasDerivAt (fun t : ℂ => t • (EuclideanSpace.single i 1 : ComplexModel n))
        (EuclideanSpace.single i 1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const (EuclideanSpace.single i 1 : ComplexModel n)
    have hcomp : HasDerivAt (fun t : ℂ => F (t • (EuclideanSpace.single i 1 : ComplexModel n)))
        (fderiv ℂ F 0 (EuclideanSpace.single i 1)) 0 := by
      exact hF.self_of_nhds.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
    exact hcomp.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq (haxes i))
  have hlin : (fderiv ℂ F 0).toLinearMap = 0 := by
    apply (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.ext
    intro i
    simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe,LinearMap.zero_apply] using hd i
  have hd0 : fderiv ℂ F 0 = 0 := by
    ext w
    exact LinearMap.congr_fun hlin w
  apply inNormalPow_of_iterDeriv_eq_zero 2 (fun _ _ => rfl) hF
  refine Eventually.of_forall fun w hw L hL => ?_
  have hw0 : w = 0 := by ext i; exact hw i (Nat.zero_le _)
  subst w
  cases L with
  | nil => exact hF0
  | cons v L =>
      cases L with
      | nil => simp [iterDeriv,dirDeriv,hd0]
      | cons u L => simp only [List.length_cons] at hL; omega

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Any actual germ vanishing on the NC double locus has zero constant and
linear jet at every point with at least three original branches. -/
theorem mem_pointIdeal_sq_of_vanishes_doubleLocus {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {x : X}
    (hx : 3 ≤ branchMultiplicity hH x) {g : X → ℂ} (hg : HolomorphicAt n g x)
    (hvan : ∀ᶠ y in 𝓝 x, 2 ≤ branchMultiplicity hH y → g y = 0) :
    (idealPow (pointIdeal n x) 2).mem x g := by
  classical
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 x
  have hScard : 3 ≤ S.card := by
    rw [← branchMultiplicity_eq_card hH Φ h0 S hflat]
    exact hx
  have hn : 0 < n := by have := branchMultiplicity_le hH x; omega
  let φ : ComplexModel n → X := fun w => (chartAt (ComplexModel n) x).symm (Φ.invFun w)
  let ψ : X → ComplexModel n := fun y => Φ.toFun (chartAt (ComplexModel n) x y)
  let F : ComplexModel n → ℂ := g ∘ φ
  have hT : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ Φ.target := by
    rw [← h0]
    exact Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun Φ.center_mem_source)
  have hφT : Tendsto φ (𝓝 0) (𝓝 x) := by
    rw [← h0]
    exact tendsto_flatInverse Φ (mem_flatDomain_self Φ)
  have hφd : ∀ w ∈ Φ.target,
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.invFun w :=
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).mdifferentiableAt
    exact (mdifferentiableAt_chart_symm (hsrc (Φ.mapsTo_invFun hw))).comp w h1
  have hFd : ∀ᶠ w in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F w := by
    filter_upwards [hT.eventually_nhds,hφT.eventually hg.eventually] with w hw hgw
    have hφw : ∀ᶠ w' in 𝓝 w,
        MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w' :=
      hw.mono fun w' hw' => hφd w' hw'
    exact mdifferentiableAt_iff_differentiableAt.mp
      (holomorphicAt_comp_map hφw hgw).self_of_nhds
  have haxes (i : Fin n) : ∀ᶠ t : ℂ in 𝓝 0,
      F (t • (EuclideanSpace.single i 1 : ComplexModel n)) = 0 := by
    have hcurve : Tendsto (fun t : ℂ => t • (EuclideanSpace.single i 1 : ComplexModel n))
        (𝓝 0) (𝓝 (0 : ComplexModel n)) := by
      have hcontinuous : Continuous (fun t : ℂ => t • (EuclideanSpace.single i 1 : ComplexModel n)) :=
        continuous_id.smul continuous_const
      simpa using hcontinuous.tendsto (0 : ℂ)
    filter_upwards [hcurve.eventually hT,hcurve.eventually (hφT.eventually hvan)]
      with t ht hgt
    apply hgt
    obtain ⟨hyD,hycoord⟩ := flatInverse_mem Φ ht hsrc
    rw [branchMultiplicity_eq_filter_card hH Φ S hflat hyD]
    have hsub : S.erase i ⊆ S.filter (fun j => flatCoord Φ j (φ (t • EuclideanSpace.single i 1)) = 0) := by
      intro j hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hj,?_⟩
      have heq := congrArg (fun w : ComplexModel n => w j) hycoord
      change flatCoord Φ j (φ (t • EuclideanSpace.single i 1)) = _ at heq
      rw [heq]
      simp [Finset.ne_of_mem_erase hj]
    have hcard : 2 ≤ (S.erase i).card := by
      by_cases hi : i ∈ S
      · rw [Finset.card_erase_of_mem hi]; omega
      · rw [Finset.erase_eq_of_notMem hi]; omega
    exact hcard.trans (Finset.card_le_card hsub)
  have hFpow := inNormalPow_two_of_axis_vanishing hn hFd haxes
  have hψ : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ y := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun
        (chartAt (ComplexModel n) x y) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).mdifferentiableAt
    exact h1.comp y (mdifferentiableAt_chart hy.1)
  have hψI : ∀ i : Fin n, 0 ≤ i.val →
      (pointIdeal n x).mem x (fun y => ψ y i) := by
    intro i _
    apply mem_pointIdeal_of_apply_eq_zero (holomorphicAt_flatCoord Φ i (mem_flatDomain_self Φ))
    change Φ.toFun (chartAt (ComplexModel n) x x) i = 0
    rw [h0]
    rfl
  have hψx : ψ x = 0 := h0
  apply mem_idealPow_of_inNormalPow hψx hψ hψI 2 hFpow
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
  change g y = g ((chartAt (ComplexModel n) x).symm (Φ.invFun
    (Φ.toFun (chartAt (ComplexModel n) x y))))
  rw [flatInverse_flat Φ hy]

/-- The original double-locus vanishing condition internally forces a WHOLE
square-centre ideal containment at any triple-or-higher highest stratum. -/
theorem ideal_le_highestCentre_square_of_doubleLocus_subset_zeroLocus
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 3 ≤ r)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r)
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hvan : {x | 2 ≤ branchMultiplicity hH x} ⊆ I.zeroLocus) :
    I.Le (idealPow (vanishingIdeal (n := n) {x | r ≤ branchMultiplicity hH x}) 2) := by
  have hC : IsClosedSubmanifold n {x | r ≤ branchMultiplicity hH x} :=
    ⟨isClosed_branchMultiplicity_superlevel hH r,
      fun _ hx => ⟨n-r,regularAtDim_highest_superlevel hH hbound hx⟩⟩
  apply le_idealPow_vanishingIdeal_of_subset_cosupport hI hC
  intro x hx
  refine ⟨mem_univ x,fun g hg => ?_⟩
  have hgvan : ∀ᶠ y in 𝓝 x, 2 ≤ branchMultiplicity hH y → g y = 0 := by
    filter_upwards [eventually_mem_of_isCoherent hI hg] with y hgy hy
    exact hvan hy g hgy
  have hgpow := mem_pointIdeal_sq_of_vanishes_doubleLocus hH (hr.trans hx)
    (GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hgvan
  exact ⟨g,hgpow,Eventually.of_forall fun _ _ => rfl⟩

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- Actual square-centre containment leaves an exceptional factor after the
literal marking-one controlled division, on the whole exceptional divisor. -/
theorem exceptional_subset_controlled_cosupport_of_square
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (I : GermIdeal n X)
    (hle : I.Le (idealPow (vanishingIdeal (n := n) C) 2)) :
    π ⁻¹' C ⊆ cosupport n univ (controlledTransform hπ I 1) 1 := by
  let D := exceptionalDivisor hπ
  have hDc : D.ideal.IsCoherent := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  have hpowone : idealPow D.ideal 1 = D.ideal :=
    FactorizationFromResolution.idealPow_one_of_isCoherent hDc
  have hpowtwo : idealPow D.ideal 2 = D.ideal.mul D.ideal := by
    rw [show (2 : ℕ) = 1+1 from rfl,idealPow_succ,hpowone]
  have hpull := pullback_le_idealPow_exceptionalDivisor hπ hle
  have hcontrolled : (controlledTransform hπ I 1).Le D.ideal := by
    intro y g hg
    change (colon (GermIdeal.pullback (m := n) π I) (idealPow D.ideal 1)).mem y g at hg
    rw [hpowone] at hg
    have hh : (colon (idealPow D.ideal 2) D.ideal).mem y g :=
      ⟨hg.1,fun f hf => hpull y _ (hg.2 f hf)⟩
    rw [hpowtwo,colon_mul_eq D.isInvertible hDc] at hh
    exact hh
  have hhol (y : Y) (g : Y → ℂ) (hg : (controlledTransform hπ I 1).mem y g) :
      HolomorphicAt n g y := hg.1
  rw [cosupport_one hhol,univ_inter]
  intro y hy g hg
  have hyD : y ∈ D.support := by
    rwa [support_exceptionalDivisor hπ]
  exact hyD g (hcontrolled y g hg)

omit [IsComplexManifold n X] in
private theorem branchMultiplicity_congr {H K : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hK : IsNormalCrossingsCarrier (n := n) K)
    (heq : H = K) (x : X) : branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

omit [IsComplexManifold n X] in
private theorem ambient_mark_one_cosupp (M : MarkedIdeal n X)
    (hN : M.N = univ) (hd : M.d = 1) (hI : M.ideal.IsCoherent) :
    M.cosupp = M.ideal.zeroLocus := by
  change cosupport n M.N M.ideal M.d = _
  rw [hN,hd,cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg),univ_inter]

/-- The original double-locus hypothesis produces actual centre admissibility
and is preserved by the LITERAL marking-one controlled transform. -/
theorem doubleLocus_strict_subset_controlled_cosupport
    (M : MarkedIdeal n X) (hN : M.N = univ) (hd : M.d = 1) (hw : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    {π : Y → X}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π)
    (hvan : {x | 2 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ⊆ M.ideal.zeroLocus)
    (hp : IsNormalCrossingsCarrier (n := n) (strictTransform n π H)) :
    M.IsAdmissibleCentre {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ∧
      {z | 2 ≤ branchMultiplicity hp z} ⊆
        (M.geoTransform {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π).cosupp := by
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  have hcos := ambient_mark_one_cosupp M hN hd hw.isCoherent
  have hC : IsClosedSubmanifold n {x | r ≤ branchMultiplicity hH x} :=
    ⟨isClosed_branchMultiplicity_superlevel hH r,
      fun _ hx => ⟨n-r,regularAtDim_highest_superlevel hH hbound hx⟩⟩
  refine ⟨⟨hC,?_,hasNormalCrossings_highest_boundary h hbound⟩,?_⟩
  · rw [hcos]
    intro x hx
    exact hvan (hr.trans hx)
  · intro z hz
    change 2 ≤ branchMultiplicity hp z at hz
    by_cases hzC : r ≤ branchMultiplicity hH (π z)
    · by_cases hr3 : 3 ≤ r
      · have hsq := ideal_le_highestCentre_square_of_doubleLocus_subset_zeroLocus
          hH hr3 hbound M.ideal hw.isCoherent hvan
        have hExc := exceptional_subset_controlled_cosupport_of_square hπ M.ideal hsq hzC
        change z ∈ cosupport n (M.geoTransform _ π).N (M.geoTransform _ π).ideal (M.geoTransform _ π).d
        rw [geoTransform_N_eq_univ hN hπ,geoTransform_ideal_eq_controlledTransform hN hw.isCoherent hπ,
          geoTransform_d,hd]
        exact hExc
      · have hgeo := geoStrictTransform_highest_eq_strictTransform hH hr hbound hπ
        have hnc := isNormalCrossingsCarrier_strict_highest hH hbound hπ
        have hdrop : branchMultiplicity hp z ≤ r-1 := by
          rw [branchMultiplicity_congr hp hnc hgeo.symm z]
          exact branchMultiplicity_strict_highest_le hH hbound hπ z
        omega
    · apply TransformOffCentre.mem_cosupp_geoTransform_of_mem_cosupp M
        hw.isClosedSubmanifold_N.1 hπ hzC
      rw [hcos]
      exact hvan (hz.trans (branchMultiplicity_strict_highest_le_image hH hr hbound hπ hp z))

/-- Genuine higher-centre histories preserve double-locus cosupport and derive
every test-step admissibility for the SAME original ambient marking-one ideal. -/
theorem higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
    {A : CMfd.{u} n} (M : MarkedIdeal n A) (hN : M.N = univ) (hd : M.d = 1)
    (hw : M.IsWellFormed) {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hvan : {x | 2 ≤ branchMultiplicity hH x} ⊆ M.ideal.zeroLocus) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      HironakaStageCenters.StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      (hp : IsNormalCrossingsCarrier (n := n) (strictTransform n T.proj H)) →
      IsGeoTestTower M T ∧
        {x | 2 ≤ branchMultiplicity hp x} ⊆ (geoTransformAlong M T).cosupp
  | _,.refl,_,hp => by
      refine ⟨trivial,?_⟩
      have hs : strictTransform n (id : A → A) H = H := by
        simp [strictTransform,exceptionalLocus_id,hH.1.closure_eq]
      intro x hx
      change x ∈ M.cosupp
      rw [ambient_mark_one_cosupp M hN hd hw.isCoherent]
      apply hvan
      change 2 ≤ branchMultiplicity hp x at hx
      rwa [branchMultiplicity_congr hp hH hs x] at hx
  | _,.step T C π hπ,hc,hp => by
      obtain ⟨hh,r,hr,hbound,hceq,_⟩ := hc.2
      have hcur := isNormalCrossingsCarrier_of_boundaryAdapted hh
      obtain ⟨hT,hdouble⟩ := higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
        M hN hd hw hH hvan T hc.1 hcur
      have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
      have hNT : (geoTransformAlong M T).N = univ :=
        (pullback_eq_mul_geoTransformAlong M hN hw.isCoherent T hT).1
      have hdT : (geoTransformAlong M T).d = 1 := by rw [d_geoTransformAlong,hd]
      have hvanT : {x | 2 ≤ branchMultiplicity hcur x} ⊆ (geoTransformAlong M T).ideal.zeroLocus := by
        rwa [ambient_mark_one_cosupp _ hNT hdT hwT.isCoherent] at hdouble
      have hπ' : IsBlowupAlong n {x | r ≤ branchMultiplicity hcur x} π := hceq ▸ hπ
      have hs : strictTransform n (BlowupTower.step T C π hπ).proj H =
          strictTransform n π (strictTransform n T.proj H) := by
        rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp
          T.contMDiff_proj hπ.contMDiff]
      have hp' : IsNormalCrossingsCarrier (n := n)
          (strictTransform n π (strictTransform n T.proj H)) := hs ▸ hp
      obtain ⟨hadm,hnext⟩ := doubleLocus_strict_subset_controlled_cosupport
        (geoTransformAlong M T) hNT hdT hwT hh hr hbound hπ' hvanT hp'
      rw [← hceq] at hadm hnext
      refine ⟨⟨hT,hadm⟩,?_⟩
      intro z hz
      apply hnext
      change 2 ≤ branchMultiplicity hp' z
      change 2 ≤ branchMultiplicity hp z at hz
      rwa [branchMultiplicity_congr hp hp' hs z] at hz

private theorem stage_double_subset_cosupp
    {A : CMfd.{u} n} (M : MarkedIdeal n A) (hN : M.N = univ) (hd : M.d = 1)
    (hw : M.IsWellFormed) {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hvan : {x | 2 ≤ branchMultiplicity hH x} ⊆ M.ideal.zeroLocus) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      HironakaStageCenters.StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      HironakaStageCenters.StageCentres (fun R _ =>
        ∃ hp : IsNormalCrossingsCarrier (n := n) (strictTransform n R.proj H),
          {x | 2 ≤ branchMultiplicity hp x} ⊆ (geoTransformAlong M R).cosupp) T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,hc => by
      have hp := isNormalCrossingsCarrier_of_boundaryAdapted (Classical.choose hc.2)
      exact ⟨stage_double_subset_cosupp M hN hd hw hH hvan T hc.1,
        hp,(higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
          M hN hd hw hH hvan T hc.1 hp).2⟩

/-- An arbitrary original coherent ambient ideal vanishing on the original
double locus internally makes the genuine natural prephase a marking-one test
tower. All actual intermediate double-locus cosupports are derived. -/
theorem naturalSeparation_isGeoTestTower_of_doubleLocus_subset_zeroLocus
    {A : CMfd.{u} n} (I : GermIdeal n A) (hI : I.IsCoherent)
    {H : Set A} {E : List (Set A)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    (hvan : {x | 2 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ⊆ I.zeroLocus) :
    let M : MarkedIdeal n A := ⟨univ,E,I,1⟩
    let o := naturalSeparation M h
    IsGeoTestTower M o.T ∧
      HironakaStageCenters.StageCentres (fun R _ =>
        ∃ hp : IsNormalCrossingsCarrier (n := n) (strictTransform n R.proj H),
          {x | 2 ≤ branchMultiplicity hp x} ⊆ (geoTransformAlong M R).cosupp) o.T ∧
      o.T.length ≤ n-1 ∧
      NormalCrossings.IsSNCDivisor n ((geoTransformAlong M o.T).E ++ [strictTransform n o.T.proj H]) ∧
      RestrictEmptyTower.CentresOver
        {x | 2 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} o.T ∧
      IsIsomorphismOver n o.T.proj
        {x | 2 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}ᶜ ∧
      RestrictEmptyTower.CentresOver I.zeroLocus o.T ∧
      IsIsomorphismOver n o.T.proj I.zeroLocusᶜ := by
  let M : MarkedIdeal n A := ⟨univ,E,I,1⟩
  let o := naturalSeparation M h
  have hE := isSNCDivisor_of_boundaryAdapted h
  have hw : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hI,hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  have hp := isNormalCrossingsCarrier_of_boundaryAdapted o.pair
  obtain ⟨ht,_⟩ := higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
    M rfl rfl hw hH hvan o.T o.centres hp
  obtain ⟨hlen,_,_,hsnc,_,hcover,hiso⟩ := naturalSeparation_doubleLocus_geometry M h
  obtain ⟨_,_,_,_,_,hIcover,hIiso⟩ := naturalSeparation_permitted_geometry M h
    (isClosed_zeroLocus_of_isCoherent hI) hvan
  exact ⟨ht,stage_double_subset_cosupp M rfl rfl hw hH hvan o.T o.centres,
    hlen,hsnc,hcover,hiso,hIcover,hIiso⟩

end
end Hironaka.HironakaNormalCrossingsDoubleLocusMarkedCompatibility
