import Hironaka.MarkedIdeal.CodimOneSupportAlongRemainder
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Resolution.HironakaStepOneDimZeroAnalyticSuperlevels

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Actual whole maximal-order Step 1 superlevels in carrier dimension two

The genuine transformed geometry produces an analytic zero-dimensional
envelope for all nonspecial points. Every threshold of the literal masked
Step 1 value, including its actual lower history, is therefore analytic.
The full General2 companion/history descent and global G3 sequence remain open.
Blueprint: `hironaka-dimension-two-step-one-superlevels-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaDimensionTwoStepOneAnalyticSuperlevels

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GlobalComponents RegularLocusComponent HironakaDimensionGlobalComponents
  HironakaStepOneSpecialAnalyticLoci HironakaOneDimensionalCanonicalSuperlevels
  NormalCrossings BoundaryCount MemberInterLocusAlong DivisorExponentAlong AnalyticDimensionBasics
  MarkedIdeals MarkedIdeals.MarkedIdeal CodimOneSupportAlong GermIdealOrder HomogenizedIdealAlong

open Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine components which are not contained in the actual analytic set. -/
def remainingComponents (H A : Set M) : Set M :=
  ⋃₀ {B | B ∈ globalComponents (n := n) H ∧ ¬ B ⊆ A}

private theorem component_closed_of_smooth {H : Set M} (hH : IsClosedSubmanifold n H)
    (c : M) : closure (component (n := n) H c) = component (n := n) H c := by
  have hreg : regularPoints (n := n) H = H :=
    Subset.antisymm (regularPoints_subset H) (fun y hy => hH.2 y hy)
  have heq : component (n := n) H c = connectedComponentIn H c := by
    unfold component
    rw [hreg]
  rw [heq]
  by_cases hc : c ∈ H
  · exact Subset.antisymm
      (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hc))
        (closure_minimal (connectedComponentIn_subset H c) hH.1)) subset_closure
  · simp [connectedComponentIn_eq_empty hc]

/-- The real locally finite component subfamily is closed and smooth. -/
theorem isClosedSubmanifold_remainingComponents {H : Set M}
    (hH : IsClosedSubmanifold n H) (A : Set M) :
    IsClosedSubmanifold n (remainingComponents (n := n) H A) := by
  have hHa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH
  refine ⟨isClosed_sUnion_globalComponents_subfamily hHa (fun _ h => h.1), ?_⟩
  rintro x ⟨B, ⟨hB, hBA⟩, hxB⟩
  obtain ⟨c, ⟨k, hc⟩, rfl⟩ := hB
  rw [component_closed_of_smooth hH c] at hxB
  obtain ⟨U, hU, hxU, hHU⟩ := exists_open_inter_subset_component hc hxB
  refine ⟨k, RegularPointDimension.regularAtDim_of_inter_eq hU hxU ?_
    (regularAtDim_of_mem_component hc hxB)⟩
  apply Subset.antisymm
  · intro y hy
    exact ⟨mem_sUnion.mpr ⟨closure (component (n := n) H c),
      ⟨closure_component_mem_globalComponents hc, hBA⟩, subset_closure (hHU hy)⟩, hy.2⟩
  · rintro y ⟨⟨C, ⟨hC, -⟩, hyC⟩, hyU⟩
    exact ⟨subset_of_mem_globalComponents hHa hC hyC, hyU⟩

/-- Actual smooth components partition the carrier, so the unselected
union is the genuine complement of the selected union in the carrier. -/
theorem remainingComponents_eq_diff_selected {H : Set M}
    (hH : IsClosedSubmanifold n H) (A : Set M) :
    remainingComponents (n := n) H A = H \ selectedComponents (n := n) H A := by
  classical
  have hHa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH
  have heq : ∀ {B C : Set M}, B ∈ globalComponents (n := n) H →
      C ∈ globalComponents (n := n) H → (B ∩ C).Nonempty → B = C := by
    rintro B C ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨x, hxB, hxC⟩
    rw [component_closed_of_smooth hH b, component_closed_of_smooth hH c] at *
    exact (connectedComponentIn_eq hxB).trans (connectedComponentIn_eq hxC).symm
  apply Subset.antisymm
  · rintro x ⟨B, ⟨hB, hBA⟩, hxB⟩
    refine ⟨subset_of_mem_globalComponents hHa hB hxB, ?_⟩
    rintro ⟨C, ⟨hC, hCA⟩, hxC⟩
    exact hBA ((heq hB hC ⟨x, hxB, hxC⟩).symm ▸ hCA)
  · rintro x ⟨hxH, hxsel⟩
    have hxU : x ∈ ⋃₀ globalComponents (n := n) H := by
      rw [sUnion_globalComponents hHa]
      exact hxH
    obtain ⟨B, hB, hxB⟩ := hxU
    exact ⟨B, ⟨hB, fun hBA => hxsel ⟨B, ⟨hB, hBA⟩, hxB⟩⟩, hxB⟩

/-- Analytic continuation proves genuine thinness on the actual remaining
smooth components, rather than assuming an absence-of-component certificate. -/
theorem thin_inter_remainingComponents {H A : Set M} (hH : IsClosedSubmanifold n H)
    (hA : IsComplexAnalyticSubset (n := n) A) :
    ∀ O : Set M, IsOpen O →
      O ∩ remainingComponents (n := n) H A ⊆ A ∩ remainingComponents (n := n) H A →
      O ∩ remainingComponents (n := n) H A = ∅ := by
  intro O hO hsub
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxO, B, ⟨hB, hBA⟩, hxB⟩
  obtain ⟨c, hc, rfl⟩ := hB
  rw [component_closed_of_smooth hH c] at hxB
  apply hBA
  rw [component_closed_of_smooth hH c]
  refine component_subset_of_isOpen hA hO ⟨x, hxO, hxB⟩ ?_
  rintro y ⟨hyO, hyC⟩
  exact (hsub ⟨hyO, ⟨closure (component (n := n) H c),
    ⟨⟨c, hc, rfl⟩, hBA⟩, subset_closure hyC⟩⟩).1

/-- Genuine analytic equations survive removal of the actual relatively
open and closed codimension-one part. -/
theorem isComplexAnalyticSubset_cosupport_diff_codimOnePartAlong
    {N : Set M} {I : GermIdeal n M} {d : ℕ}
    (hI : I.IsCoherent) (hN : IsClosedSubmanifold n N) (hd : 1 ≤ d)
    (hmax : IsMaximalOrderAlong N I d) :
    IsComplexAnalyticSubset (n := n)
      (cosupport n N I d \ codimOnePartAlong N I d) := by
  have hA := isComplexAnalyticSubset_cosupport_along hI hN hd
  have hR := isClosed_codimOnePartAlong hI hN hd hmax
  apply AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq hA
    (isClosed_cosupport_diff_codimOnePartAlong hI hN)
  intro x hx
  refine ⟨(codimOnePartAlong N I d)ᶜ, hR.isOpen_compl, hx.2, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
  tauto

/-- Actual maximal-order remainder dimension drops twice in a genuine
carrier of dimension at most two, including zero-dimensional pieces. -/
theorem dimLE_cosupport_diff_codimOnePartAlong_of_dimLE_two
    {N : Set M} {I : GermIdeal n M} {d : ℕ}
    (hI : I.IsCoherent) (hN : IsClosedSubmanifold n N) (hd : 1 ≤ d)
    (hmax : IsMaximalOrderAlong N I d) (hdim : ResolutionInvariantSpec.DimLE n N 2) :
    DimLE (n := n) (cosupport n N I d \ codimOnePartAlong N I d) 0 := by
  intro y j hy
  obtain ⟨k, hk, hyN⟩ := hdim y hy.2.1.1.1
  cases k with
  | zero =>
    exact BlowupStrictSubmanifold.le_of_regularAtDim_subset hy hyN (fun _ hz => hz.1.1)
  | succ k =>
    have hlt := lt_of_regularAtDim_cosupport_diff_codimOnePartAlong hI hN hd hmax hyN hy
    omega

/-- Actual adapted coordinates force the transverse trace to have one less
free coordinate than its genuine dimension-at-most-two carrier. -/
theorem dimLE_inter_get_of_dimLE_two (hn : 0 < n) {N : Set M}
    (hdim : ResolutionInvariantSpec.DimLE n N 2)
    {E : List (Set M)} (hE : IsSNCDivisor n E) (htrans : IsTransverse n N E)
    (i : Fin E.length) : DimLE (n := n) (N ∩ E.get i) 1 := by
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
  have hdN : min kN n ≤ 2 := (RegularPointDimension.eq_of_regularAtDim hNreg hxNd) ▸ hd
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

/-- Genuine analytic continuation and thin dimension drop make the
unselected actual curve-component trace closed analytic of dimension zero. -/
theorem analytic_dimzero_inter_remainingComponents {H A : Set M}
    (hH : IsClosedSubmanifold n H) (hdim : DimLE (n := n) H 1)
    (hA : IsComplexAnalyticSubset (n := n) A) :
    IsComplexAnalyticSubset (n := n) (A ∩ remainingComponents (n := n) H A) ∧
      DimLE (n := n) (A ∩ remainingComponents (n := n) H A) 0 := by
  have hHa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH
  have hrem := isClosedSubmanifold_remainingComponents hH A
  have hrema := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hrem
  have hsub : remainingComponents (n := n) H A ⊆ H := by
    rintro x ⟨B, ⟨hB, -⟩, hxB⟩
    exact subset_of_mem_globalComponents hHa hB hxB
  have hdimrem : DimLE (n := n) (remainingComponents (n := n) H A) 1 := by
    intro x k hx
    obtain ⟨j, hxH⟩ := hH.2 x (hsub hx.2.1)
    exact (BlowupStrictSubmanifold.le_of_regularAtDim_subset hx hxH hsub).trans (hdim x j hxH)
  exact ⟨hA.inter hrema, ThinDimensionDrop.dimLE_pred_of_thin hrema
    inter_subset_right (thin_inter_remainingComponents hH hA) hdimrem⟩

/-- A genuine finite union of analytic dimension-zero sets retains both properties. -/
theorem analytic_dimzero_union {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hAdim : DimLE (n := n) A 0)
    (hB : IsComplexAnalyticSubset (n := n) B) (hBdim : DimLE (n := n) B 0) :
    IsComplexAnalyticSubset (n := n) (A ∪ B) ∧ DimLE (n := n) (A ∪ B) 0 := by
  have hdisc := (isDiscrete_of_analytic_dimLE_zero hA hAdim).union
    (isDiscrete_of_analytic_dimLE_zero hB hBdim) hA.isClosed hB.isClosed
  refine ⟨HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hA hB, ?_⟩
  intro x j hx
  obtain ⟨U, hU, hUZ⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdisc x hx.2.1
  have hxU : x ∈ U := (show x ∈ U ∩ (A ∪ B) by rw [hUZ]; exact mem_singleton x).1
  have hreg : RegularAtDim (n := n) (A ∪ B) x 0 := by
    rcases hx.2.1 with hxA | hxB
    · apply RegularPointDimension.regularAtDim_of_inter_eq hU hxU _
        (regularAtDim_zero_of_analytic_dimLE_zero hA hAdim hxA)
      apply Subset.antisymm
      · exact fun y hy => ⟨Or.inl hy.1, hy.2⟩
      · intro y hy
        have hyx : y = x := mem_singleton_iff.mp (hUZ ▸ (⟨hy.2, hy.1⟩ : y ∈ U ∩ (A ∪ B)))
        exact ⟨hyx ▸ hxA, hy.2⟩
    · apply RegularPointDimension.regularAtDim_of_inter_eq hU hxU _
        (regularAtDim_zero_of_analytic_dimLE_zero hB hBdim hxB)
      apply Subset.antisymm
      · exact fun y hy => ⟨Or.inr hy.1, hy.2⟩
      · intro y hy
        have hyx : y = x := mem_singleton_iff.mp (hUZ ▸ (⟨hy.2, hy.1⟩ : y ∈ U ∩ (A ∪ B)))
        exact ⟨hyx ▸ hxB, hy.2⟩
  exact (RegularPointDimension.eq_of_regularAtDim hx hreg).le

/-- The actual finite indexed union is analytic and zero-dimensional. -/
theorem analytic_dimzero_finset_union {ι : Type*} (t : Finset ι)
    (A : ι → Set M) (hA : ∀ i ∈ t, IsComplexAnalyticSubset (n := n) (A i))
    (hdim : ∀ i ∈ t, DimLE (n := n) (A i) 0) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t, A i) ∧
      DimLE (n := n) (⋃ i ∈ t, A i) 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    exact ⟨by simp, fun _ _ hx => False.elim (notMem_empty _ hx.2.1)⟩
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨htA, htdim⟩ := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hdim j (Finset.mem_insert_of_mem hj))
    exact analytic_dimzero_union (hA i (Finset.mem_insert_self i t))
      (hdim i (Finset.mem_insert_self i t)) htA htdim

section ActualStepOne

universe u v
open BlowupTowers BlowupTowerTransforms StepOneValue StepOneLowerDomain
  HironakaBoundaryCountAnalyticSuperlevels CanonicalCentres
variable {k : ℕ} {X Y : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- Actual maximal-order geometry and actual original boundary traces
internally produce one closed analytic zero-dimensional nonspecial envelope. -/
theorem exists_analytic_dimzero_nonspecial_envelope
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hdim : ResolutionInvariantSpec.DimLE n 𝔍.N 2)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
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
  have hdimT : ResolutionInvariantSpec.DimLE n m.N 2 :=
    InvDomainTowerAlong.dimLE_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent hdim T hT
  have hA := isComplexAnalyticSubset_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N hdT
  have hE : IsSNCDivisor n E := NormalCrossingsComparison.isSNCDivisor_of_sublist hwf.isSNCDivisor
    (List.take_sublist 𝔍.E.length m.E)
  have htr : IsTransverse n m.N E := NormalCrossingsComparison.isTransverse_of_forall_mem
    hwf.isTransverse (fun H hH => List.take_subset 𝔍.E.length _ hH)
  let Z₀ := m.cosupp \ codimOnePartAlong m.N m.ideal m.d
  have hZ₀ : IsComplexAnalyticSubset (n := n) Z₀ :=
    isComplexAnalyticSubset_cosupport_diff_codimOnePartAlong hwf.isCoherent hwf.isClosedSubmanifold_N hdT hmaxT
  have hZ₀dim : DimLE (n := n) Z₀ 0 :=
    dimLE_cosupport_diff_codimOnePartAlong_of_dimLE_two hwf.isCoherent hwf.isClosedSubmanifold_N hdT hmaxT hdimT
  let B := fun i : Fin E.length => m.cosupp ∩ remainingComponents (n := n) (m.N ∩ E.get i) m.cosupp
  have hB : ∀ i, IsComplexAnalyticSubset (n := n) (B i) ∧ DimLE (n := n) (B i) 0 := by
    intro i
    have hH := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hwf.isClosedSubmanifold_N.1 hE htr {i}
    rw [memberInter_singleton] at hH
    exact analytic_dimzero_inter_remainingComponents hH
      (dimLE_inter_get_of_dimLE_two hn hdimT hE htr i) hA
  obtain ⟨hBU, hBUdim⟩ := analytic_dimzero_finset_union Finset.univ B
    (fun i _ => (hB i).1) (fun i _ => (hB i).2)
  obtain ⟨hZ, hZdim⟩ := analytic_dimzero_union hZ₀ hZ₀dim hBU hBUdim
  refine ⟨Z₀ ∪ (⋃ i ∈ (Finset.univ : Finset (Fin E.length)), B i), hZ, hZdim, ?_⟩
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

/-- Every actual full masked Step 1 threshold is globally analytic in
carrier dimension at most two; the actual historical lower value is retained. -/
theorem isComplexAnalyticSubset_stepOneInvM_superlevel
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hdim : ResolutionInvariantSpec.DimLE n 𝔍.N 2)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) (s : ℕ) (α : WithTop Λ) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y} := by
  classical
  let A : Set Y := {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
    toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y}
  let P : Set Y := {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
    toLex (s, (⊤ : WithTop Λ)) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y}
  have hP : IsComplexAnalyticSubset (n := n) P :=
    isComplexAnalyticSubset_stepOneInvM_top_superlevel R hn 𝔍 h𝔍 hd hmax T hT s
  obtain ⟨Z, hZ, hZdim, hcover⟩ := exists_analytic_dimzero_nonspecial_envelope hn 𝔍 h𝔍 hd hmax hdim T hT
  have hAZ : A \ P ⊆ Z := by
    intro y hy
    apply hcover y hy.1.1
    intro hsp
    apply hy.2
    have hsame : toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y ↔
        toLex (s, (⊤ : WithTop Λ)) ≤ Seq.StepOneValueMasked.stepOneInvM R 𝔍 T y := by
      simp [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL,
        hsp, Prod.Lex.toLex_le_toLex]
    exact ⟨hy.1.1, hsame.mp hy.1.2⟩
  have hB : IsComplexAnalyticSubset (n := n) (A \ P) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (isClosedSubmanifold_subset_of_analytic_dimLE_zero hZ hZdim hAZ)
  have hPA : P ⊆ A := by
    intro y hy
    refine ⟨hy.1, le_trans ?_ hy.2⟩
    rw [Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl, le_top⟩
  have hEq : P ∪ (A \ P) = A := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact hPA hy
      · exact hy.1
    · intro hy
      by_cases hyP : y ∈ P
      · exact Or.inl hyP
      · exact Or.inr ⟨hy, hyP⟩
  change IsComplexAnalyticSubset (n := n) A
  rw [← hEq]
  exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hP hB

/-- This is the actual dimension-one canonical lower invariant used in the
actual dimension-two maximal-order recursion, with all historical entries. -/
theorem isComplexAnalyticSubset_canonical_stepOne_two_superlevel
    (hn : 0 < n) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hdim : ResolutionInvariantSpec.DimLE n 𝔍.N 2)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (s : ℕ) (α : WithTop (ValTy 1)) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        toLex (s, α) ≤ Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) 𝔍 T y} :=
  isComplexAnalyticSubset_stepOneInvM_superlevel (invFamily hn 1) hn 𝔍 h𝔍 hd hmax hdim T hT s α

end ActualStepOne

end
end Hironaka.HironakaDimensionTwoStepOneAnalyticSuperlevels
