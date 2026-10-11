/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaGeneralThreeNonspecialAnalyticLoci

/-!
# Actual dimension-three Step 1 nonspecial curve envelope

Genuine maximal-order remainder and actual transverse original-member traces
internally yield a closed analytic dimension-one envelope containing every
nonspecial current point. Finite analytic union dimension is proved from true
irreducible regular-component closures. Actual original domain3/canonical
invFamily3 inputs internally produce the companion envelope and all whole
special/higher-level top-lower-entry thresholds on the actual mask patch.
Finite lower-threshold curve gluing, whole General3 and global G3 remain open.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaDimensionThreeStepOneCurveEnvelope
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GlobalComponents RegularLocusComponent AnalyticDimensionBasics
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  MarkedIdeals MarkedIdeals.MarkedIdeal CodimOneSupportAlong NormalCrossings
  SimultaneousNormalCrossings HomogenizedIdealAlong GermIdealOrder BoundaryCount MemberInterLocusAlong DivisorExponentAlong
open Hironaka

noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- True maximal-order remainder drops twice in an actual smooth carrier of dimension at most three. -/
theorem dimLE_cosupport_diff_codimOnePartAlong_of_dimLE_three
    {N : Set M} {I : GermIdeal n M} {d : ℕ}
    (hI : I.IsCoherent) (hN : IsClosedSubmanifold n N) (hd : 1 ≤ d)
    (hmax : IsMaximalOrderAlong N I d) (hdim : ResolutionInvariantSpec.DimLE n N 3) :
    DimLE (n := n) (cosupport n N I d \ codimOnePartAlong N I d) 1 := by
  intro y j hy
  obtain ⟨k, hk, hyN⟩ := hdim y hy.2.1.1.1
  cases k with
  | zero =>
    have hj : j ≤ 0 := BlowupStrictSubmanifold.le_of_regularAtDim_subset hy hyN (fun _ hz => hz.1.1)
    omega
  | succ k =>
    have hlt := lt_of_regularAtDim_cosupport_diff_codimOnePartAlong hI hN hd hmax hyN hy
    omega

/-- The actual indexed boundary coordinate cannot remain a free trace coordinate. -/
theorem dimLE_inter_get_of_dimLE_three (hn : 0 < n) {N : Set M}
    (hdim : ResolutionInvariantSpec.DimLE n N 3)
    {E : List (Set M)} (hE : IsSNCDivisor n E) (htrans : IsTransverse n N E)
    (i : Fin E.length) : DimLE (n := n) (N ∩ E.get i) 2 := by
  intro x j hx
  have hxi : x ∈ E.get i := hx.2.1.2
  have hxN : x ∈ N := hx.2.1.1
  have hnc := MemberInterAlong.hasNormalCrossings_inter_memberInter htrans {i}
  rw [memberInter_singleton] at hnc
  obtain ⟨kC, kN, Φ, σ, hΦsrc, hσN, -, hflat⟩ :=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn
      (inter_subset_left : N ∩ E.get i ⊆ N) hE htrans hnc hx.2.1
  have hCflat := fun {y : M} (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hyΦ : chartAt (ComplexModel n) x y ∈ Φ.source) => (hflat hy hyΦ).1
  have hNflat := fun {y : M} (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hyΦ : chartAt (ComplexModel n) x y ∈ Φ.source) => (hflat hy hyΦ).2.1
  have hxsrc := mem_chart_source (ComplexModel n) x
  have hCreg : RegularAtDim (n := n) (N ∩ E.get i) x (min kC n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun {y} hy hyΦ => by rw [complexCoordinatePlane_min]; exact hCflat hy hyΦ)
      hx.2.1 hxsrc Φ.center_mem_source
  have hNreg : RegularAtDim (n := n) N x (min kN n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun {y} hy hyΦ => by rw [complexCoordinatePlane_min]; exact hNflat hy hyΦ)
      hxN hxsrc Φ.center_mem_source
  obtain ⟨d, hd, hxNd⟩ := hdim x hxN
  have hdN : min kN n ≤ 3 := (RegularPointDimension.eq_of_regularAtDim hNreg hxNd) ▸ hd
  have hσlt : (σ i).1 < min kN n := lt_min (hσN i hxi) (σ i).2
  have hσC : min kC n ≤ (σ i).1 := by
    by_contra hnot
    have hσkC : (σ i).1 < kC := lt_of_lt_of_le (Nat.lt_of_not_ge hnot) (min_le_left _ _)
    let p := Φ.toFun (chartAt (ComplexModel n) x x)
    let v : ComplexModel n := EuclideanSpace.single (σ i) 1
    have hpC : p ∈ complexCoordinatePlane n kC :=
      (hCflat hxsrc Φ.center_mem_source).mp hx.2.1
    have hpT : p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
    have htarget : ∀ᶠ τ : ℂ in 𝓝 0, p + τ • v ∈ Φ.target := by
      have hc : Continuous (fun τ : ℂ => p + τ • v) := continuous_const.add (continuous_id.smul continuous_const)
      have ht : Tendsto (fun τ : ℂ => p + τ • v) (𝓝 0) (𝓝 p) := by
        simpa using hc.continuousAt.tendsto (x := 0)
      exact ht.eventually (Φ.isOpen_target.mem_nhds hpT)
    have hzero : ∀ᶠ τ : ℂ in 𝓝 0, (p + τ • v) (σ i) = 0 := by
      filter_upwards [htarget] with τ hτ
      let y : M := (chartAt (ComplexModel n) x).symm (Φ.invFun (p + τ • v))
      have hinv : Φ.invFun (p + τ • v) ∈ Φ.source := Φ.mapsTo_invFun hτ
      have hcharts : Φ.invFun (p + τ • v) ∈ (chartAt (ComplexModel n) x).target := hΦsrc hinv
      have hys : y ∈ (chartAt (ComplexModel n) x).source :=
        (chartAt (ComplexModel n) x).mapsTo_symm hcharts
      have hchart : chartAt (ComplexModel n) x y = Φ.invFun (p + τ • v) :=
        (chartAt (ComplexModel n) x).right_inv hcharts
      have hyΦ : chartAt (ComplexModel n) x y ∈ Φ.source := hchart ▸ hinv
      have hval : Φ.toFun (chartAt (ComplexModel n) x y) = p + τ • v := by
        rw [hchart, Φ.right_inv _ hτ]
      have hyC : y ∈ N ∩ E.get i := (hCflat hys hyΦ).mpr (by
        rw [hval]
        intro r hr
        have hri : r ≠ σ i := by intro heq; subst r; omega
        simp [p, v, hpC r hr, hri])
      have hz := ((hflat hys hyΦ).2.2 i hxi).mp hyC.2
      rwa [hval] at hz
    have hpzero : p (σ i) = 0 := ((hflat hxsrc Φ.center_mem_source).2.2 i hxi).mp hxi
    have hτzero : ∀ᶠ τ : ℂ in 𝓝 0, τ = 0 := hzero.mono (fun τ h => by
      simpa [v, hpzero] using h)
    have hid : HasDerivAt (fun τ : ℂ => τ) 1 0 := hasDerivAt_id 0
    have hz : HasDerivAt (fun τ : ℂ => τ) 0 0 :=
      (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hτzero
    exact one_ne_zero (hid.unique hz)
  have hj := RegularPointDimension.eq_of_regularAtDim hx hCreg
  omega

/-- Actual unselected smooth trace components have genuinely thin cosupport intersection. -/
theorem analytic_dimone_inter_remainingComponents {H A : Set M}
    (hH : IsClosedSubmanifold n H) (hdim : DimLE (n := n) H 2)
    (hA : IsComplexAnalyticSubset (n := n) A) :
    IsComplexAnalyticSubset (n := n) (A ∩ remainingComponents (n := n) H A) ∧
      DimLE (n := n) (A ∩ remainingComponents (n := n) H A) 1 := by
  have hHa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH
  have hrem := isClosedSubmanifold_remainingComponents hH A
  have hrema := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hrem
  have hsub : remainingComponents (n := n) H A ⊆ H := by
    rintro x ⟨B, ⟨hB, -⟩, hxB⟩
    exact subset_of_mem_globalComponents hHa hB hxB
  have hdimrem : DimLE (n := n) (remainingComponents (n := n) H A) 2 := by
    intro x k hx
    obtain ⟨j, hxH⟩ := hH.2 x (hsub hx.2.1)
    exact (BlowupStrictSubmanifold.le_of_regularAtDim_subset hx hxH hsub).trans (hdim x j hxH)
  exact ⟨hA.inter hrema, ThinDimensionDrop.dimLE_pred_of_thin hrema
    inter_subset_right (thin_inter_remainingComponents hH hA) hdimrem⟩

/-- A real regular component of an analytic union lies entirely in one member by analytic irreducibility. -/
theorem analytic_dimLE_union {A B : Set M} {d : ℕ}
    (hA : IsComplexAnalyticSubset (n := n) A) (hdA : DimLE (n := n) A d)
    (hB : IsComplexAnalyticSubset (n := n) B) (hdB : DimLE (n := n) B d) :
    IsComplexAnalyticSubset (n := n) (A ∪ B) ∧ DimLE (n := n) (A ∪ B) d := by
  have hU := HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hA hB
  refine ⟨hU, ?_⟩
  intro x j hx
  let C := closure (component (n := n) (A ∪ B) x)
  have hCmem := closure_component_mem_globalComponents hx
  have hC := isComplexAnalyticallyIrreducible_of_mem_globalComponents hU hCmem
  have hCsub : C ⊆ A ∪ B := subset_of_mem_globalComponents hU hCmem
  have hCeq : C = (C ∩ A) ∪ (C ∩ B) := by
    ext y
    constructor
    · intro hy
      exact (hCsub hy).elim (fun ha => Or.inl ⟨hy, ha⟩) (fun hb => Or.inr ⟨hy, hb⟩)
    · exact fun hy => hy.elim (fun ha => ha.1) (fun hb => hb.1)
  have hxC : RegularAtDim (n := n) C x j :=
    regularAtDim_closure_component hx (mem_component_self hx)
  rcases hC.eq_left_or_eq_right (hC.analytic.inter hA) (hC.analytic.inter hB)
      inter_subset_left inter_subset_left hCeq with hCA | hCB
  · have hs : C ⊆ A := by
      intro y hy
      change y ∈ closure (component (n := n) (A ∪ B) x) at hy
      exact (hCA ▸ hy).2
    exact DimensionMonotone.DimLE.anti hA hs hdA x j hxC
  · have hs : C ⊆ B := by
      intro y hy
      change y ∈ closure (component (n := n) (A ∪ B) x) at hy
      exact (hCB ▸ hy).2
    exact DimensionMonotone.DimLE.anti hB hs hdB x j hxC

/-- The actual finite indexed analytic union preserves every genuine regular-dimension bound. -/
theorem analytic_dimLE_finset_union {ι : Type*} (t : Finset ι)
    (A : ι → Set M) {d : ℕ}
    (hA : ∀ i ∈ t, IsComplexAnalyticSubset (n := n) (A i))
    (hdA : ∀ i ∈ t, DimLE (n := n) (A i) d) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t, A i) ∧ DimLE (n := n) (⋃ i ∈ t, A i) d := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    exact ⟨by simp, fun _ _ hx => False.elim (notMem_empty _ hx.2.1)⟩
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨htA, htd⟩ := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hdA j (Finset.mem_insert_of_mem hj))
    exact analytic_dimLE_union (hA i (Finset.mem_insert_self i t))
      (hdA i (Finset.mem_insert_self i t)) htA htd

section ActualStepOne
open BlowupTowers BlowupTowerTransforms StepOneValue StepOneLowerDomain
  HironakaBoundaryCountAnalyticSuperlevels CanonicalCentres
variable {X Y : CMfd.{u} n}

/-- The literal barMarked tower and actual old-member traces internally produce a curve envelope. -/
theorem exists_analytic_dimone_nonspecial_envelope
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hdim : ResolutionInvariantSpec.DimLE n 𝔍.N 3)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 1 ∧ Z ⊆ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
      ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, ¬ IsSpecial 𝔍 T y → y ∈ Z := by
  classical
  let m := geoTransformAlong (barMarked 𝔍) T
  let E := origMembers 𝔍 T
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf : m.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T hT
  have hdT : 1 ≤ m.d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hmaxT : IsMaximalOrderAlong m.N m.ideal m.d :=
    isMaximalOrderAlong_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
      (isMaximalOrderAlong_barMarked 𝔍 h𝔍 hd hmax) T hT
  have hdimT : ResolutionInvariantSpec.DimLE n m.N 3 :=
    InvDomainTowerAlong.dimLE_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent hdim T hT
  have hA := isComplexAnalyticSubset_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N hdT
  have hE : IsSNCDivisor n E := NormalCrossingsComparison.isSNCDivisor_of_sublist hwf.isSNCDivisor
    (List.take_sublist 𝔍.E.length m.E)
  have htr : IsTransverse n m.N E := NormalCrossingsComparison.isTransverse_of_forall_mem
    hwf.isTransverse (fun H hH => List.take_subset 𝔍.E.length _ hH)
  let Z₀ := m.cosupp \ codimOnePartAlong m.N m.ideal m.d
  have hZ₀ : IsComplexAnalyticSubset (n := n) Z₀ :=
    isComplexAnalyticSubset_cosupport_diff_codimOnePartAlong hwf.isCoherent hwf.isClosedSubmanifold_N hdT hmaxT
  have hZ₀dim : DimLE (n := n) Z₀ 1 :=
    dimLE_cosupport_diff_codimOnePartAlong_of_dimLE_three hwf.isCoherent hwf.isClosedSubmanifold_N hdT hmaxT hdimT
  let B := fun i : Fin E.length => m.cosupp ∩ remainingComponents (n := n) (m.N ∩ E.get i) m.cosupp
  have hB : ∀ i, IsComplexAnalyticSubset (n := n) (B i) ∧ DimLE (n := n) (B i) 1 := by
    intro i
    have hH := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hwf.isClosedSubmanifold_N.1 hE htr {i}
    rw [memberInter_singleton] at hH
    exact analytic_dimone_inter_remainingComponents hH
      (dimLE_inter_get_of_dimLE_three hn hdimT hE htr i) hA
  obtain ⟨hBU, hBUdim⟩ := analytic_dimLE_finset_union Finset.univ B
    (fun i _ => (hB i).1) (fun i _ => (hB i).2)
  obtain ⟨hZ, hZdim⟩ := analytic_dimLE_union hZ₀ hZ₀dim hBU hBUdim
  refine ⟨Z₀ ∪ (⋃ i ∈ (Finset.univ : Finset (Fin E.length)), B i), hZ, hZdim, ?_, ?_⟩
  · rintro y (hy | hy)
    · exact hy.1
    · obtain ⟨i, -, hyi⟩ := mem_iUnion₂.mp hy
      exact hyi.1
  intro y hy hsp
  by_cases hz : level 𝔍 T y = 0
  · exact Or.inl ⟨hy, fun hyR => hsp (Or.inl ⟨hz, hyR⟩)⟩
  · have hpos : 1 ≤ level 𝔍 T y := Nat.one_le_iff_ne_zero.mpr hz
    have hcount : 0 < (Finset.univ.filter (fun i : Fin E.length => y ∈ E.get i)).card := hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hcount
    have hyi : y ∈ E.get i := (Finset.mem_filter.mp hi).2
    have hH := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hwf.isClosedSubmanifold_N.1 hE htr {i}
    rw [memberInter_singleton] at hH
    have hnot : y ∉ selectedComponents (n := n) (m.N ∩ E.get i) m.cosupp := by
      intro hsel
      have hyL : y ∈ memberInterLocus m.N E m.cosupp := by
        change y ∈ memberInterLocus m.N E (cosupport n m.N m.ideal m.d)
        rw [memberInterLocus_eq_componentUnion hn m.N hwf.isClosedSubmanifold_N E hE htr hA m.cosupp_subset_N]
        refine mem_iUnion.mpr ⟨{i}, ?_⟩
        rwa [memberInter_singleton]
      exact hsp (Or.inr ⟨hpos, hyL⟩)
    have hyrem : y ∈ remainingComponents (n := n) (m.N ∩ E.get i) m.cosupp := by
      rw [remainingComponents_eq_diff_selected hH]
      exact ⟨⟨m.cosupp_subset_N hy, hyi⟩, hnot⟩
    exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, ⟨hy, hyrem⟩⟩)


open HironakaGeneralThreeNonspecialAnalyticLoci
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- Original actual General3 inputs internally supply all companion geometry for the genuine curve envelope. -/
theorem exists_actual_companion_dimone_nonspecial_envelope (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    ∃ Z : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) Z ∧
      DimLE (n := n) Z 1 ∧ Z ⊆ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp ∧
      ∀ p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp,
        ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p → p ∈ Z := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ :=
    actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK
  simpa only [hb.2.2] using
    exists_analytic_dimone_nonspecial_envelope hn (companionAt m T x)
      hK.isWellFormed hK.one_le_d hmax hK.dimLE (companionTailAt m T x) hb.1

/-- Every actual top lower-entry General3 threshold is analytic on the whole real mask patch, for all levels. -/
theorem isComplexAnalyticSubset_general_three_top_threshold_on_actual_patch (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) (s : ℕ) :
    IsComplexAnalyticSubset (n := n)
      ((Subtype.val : patchAt m T x → Y) ⁻¹' {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (orderAt m T x, toLex (Sum.inr
          ((toLex (s, (⊤ : WithTop (ValTy 2))) : ℕ ×ₗ WithTop (ValTy 2)) :
            WithTop (ℕ ×ₗ WithTop (ValTy 2))))) ≤ (invFamily hn 3).inv m T y}) := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ :=
    actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    (companionAt m T x) hK hmax hn (companionTailAt m T x) hcanK
  rw [general_superlevel_pullback_eq_actual_companion_threshold hn m h T hcan x hx hq]
  simpa only [WithTop.coe_le_coe, hb.2.2] using
    isComplexAnalyticSubset_stepOneInvM_top_superlevel (invFamily hn 2) hn
      (companionAt m T x) hK.isWellFormed hK.one_le_d hmax (companionTailAt m T x) hb.1 s

end ActualStepOne
end
end Hironaka.HironakaDimensionThreeStepOneCurveEnvelope
