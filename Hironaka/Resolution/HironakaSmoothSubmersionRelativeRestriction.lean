/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Support.RestrictedIdealExtensionExact
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.MarkedIdeal.RestrictedIdealExtension

/-! Entire original vanishing ideals and restricted marked records under genuine submersions.
The original closed submanifold and coherent ideal are the geometric inputs.
No caller flattening, ideal-equality or restriction certificate is used by the whole consumers.
Higher invariant equality, general blowup base change and complete G2 remain open.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSmoothSubmersionRelativeRestriction
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open NormalCrossings BlowupFlatCoordinates RegularAtDimTransport SimultaneousNormalCrossings
  DivisorExponentAlong MarkedIdeals ResolutionInvariantSpec HironakaSmoothSubmersionMonomialOrdering
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionDivisorExponents OrderTaylor RelativePrincipalizationSpan HadamardBridge
  RestrictedIdealExtension GermIdealPullbackCalculus IdealOrderArithmetic
  HironakaSmoothSubmersionCoefficientIdeals
noncomputable section

private def linearCoordinates {n : ℕ} (L : ComplexModel n ≃L[ℂ] ComplexModel n) :
    LocalHolomorphicEquivAt (n := n) 0 where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := L
  invFun := L.symm
  toFun_holomorphic := L.differentiable.differentiableOn
  invFun_holomorphic := L.symm.differentiable.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => L.symm_apply_apply _
  right_inv := fun _ _ => L.apply_symm_apply _

variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold n X] [IsComplexManifold m Y]

/-- The actual finite family retains every original coordinate and literal zero entry. -/
private def coordinateFamily {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n)) : Fin n → X → ℂ :=
  fun i => if i ∈ S then flatCoord Φ i else fun _ => 0

/-- The entire original coordinate-zero ideal, including an empty cutting family. -/
theorem vanishingIdeal_mem_iff_coordinate_family {A : Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
        (z ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ coordSubspace S))
    (g : X → ℂ) :
    (vanishingIdeal (n := n) A).mem x g ↔
      IsInSpanAt (n := n) (· ∈ range (coordinateFamily Φ S)) x g := by
  classical
  obtain ⟨σ,hσ⟩ := exists_perm_nested (X := S) (Y := S) subset_rfl
  let L : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).toContinuousLinearEquiv
  have happ (u : ComplexModel n) (i : Fin n) : L u (σ i) = u i := by
    simp [L,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
  let Ψ := LocalHolomorphicEquivAt.comp Φ (linearCoordinates L) h0
  have hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) x).target := fun _ hu => hsrc hu.1
  have hΨflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Ψ.source →
        (z ∈ A ↔ Ψ.toFun (chartAt (ComplexModel n) x z) ∈
          complexCoordinatePlane n (n-S.card)) := by
    intro z hz hzΨ
    rw [hflat hz hzΨ.1]
    constructor
    · intro hu j hj
      obtain ⟨i,rfl⟩ := σ.surjective j
      change L (Φ.toFun (chartAt (ComplexModel n) x z)) (σ i) = 0
      rw [happ]
      exact hu i ((hσ i).1.mp hj)
    · intro hu i hi
      rw [← happ]
      exact hu (σ i) ((hσ i).1.mpr hi)
  constructor
  · intro hg
    obtain ⟨b,hb0,hb,he⟩ := exists_eq_sum_flatCoord Ψ hΨsrc hΨflat (mem_flatDomain_self Ψ) hg
    refine ⟨hg.1,n,coordinateFamily Φ S,fun i => b (σ i),fun i => ⟨i,rfl⟩,
      fun i => hb (σ i),?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    calc
      ∑ j, b j z * flatCoord Ψ j z = ∑ i, b (σ i) z * flatCoord Ψ (σ i) z :=
        (Equiv.sum_comp σ fun j => b j z * flatCoord Ψ j z).symm
      _ = ∑ i, b (σ i) z * coordinateFamily Φ S i z := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp only [coordinateFamily,hi,if_true]
          congr 1
          exact happ (Φ.toFun (chartAt (ComplexModel n) x z)) i
        · have hlt : (σ i).val < n-S.card := Nat.lt_of_not_le fun h => hi ((hσ i).1.mp h)
          rw [hb0 (σ i) hlt]
          simp
  · intro hg
    apply VanishingIdealCoherent.mem_vanishingIdeal_of_isInSpanAt (g := coordinateFamily Φ S) _ hg
    intro i
    by_cases hi : i ∈ S
    · simp only [coordinateFamily,hi,if_true]
      refine ⟨holomorphicAt_flatCoord Φ i (mem_flatDomain_self Φ),?_⟩
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with z hz hzA
      exact ((hflat hz.1 hz.2).mp hzA) i hi
    · simp only [coordinateFamily,hi,if_false]
      exact ⟨holomorphicAt_const 0,Eventually.of_forall fun _ _ => rfl⟩

/-- Actual finite original presentations pull back with the genuine two ambient dimensions. -/
theorem pullback_mem_iff_finite_family {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} {y : Y} {r : ℕ} (s : Fin r → X → ℂ)
    (hs : ∀ i, HolomorphicAt n (s i) (f y))
    (hgen : ∀ a, I.mem (f y) a ↔ IsInSpanAt (n := n) (· ∈ range s) (f y) a)
    (g : Y → ℂ) :
    (GermIdeal.pullback (m := m) f I).mem y g ↔
      IsInSpanAt (n := m) (· ∈ range (fun i => s i ∘ f)) y g := by
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hf ((hgen a).mp ha))
    rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
    rintro _ ⟨i,rfl⟩
    exact ⟨s i,(hgen _).mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨i,rfl⟩ (hs i)),rfl⟩

/-- Entire sums of coherent original ideals pull back in arbitrary ambient dimensions. -/
theorem pullback_sumIdeal_dimensions {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    GermIdeal.pullback (m := m) f (sumIdeal I J) =
      sumIdeal (GermIdeal.pullback (m := m) f I) (GermIdeal.pullback (m := m) f J) := by
  have hfat : ∀ {y : Y}, ∀ᶠ z in 𝓝 y,
      ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  have h𝔞 : ∀ x g, I.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  have h𝔟 : ∀ x g, J.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_,fun hg => ?_⟩)
  · refine mem_sumIdeal_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨_,K,r,c,hr,hc,hsum⟩ := mem_sumIdeal_iff.mp ha
    have heq : (fun p => ∑ k, (c k ∘ f) p * (r k ∘ f) p) =ᶠ[𝓝 y] a ∘ f :=
      ((hf.continuous.tendsto y).eventually hsum).mono fun p hp => hp.symm
    refine DerivativeIdeal.isInSpanAt_congr (IsInSpanAt.sum Finset.univ fun k _ => ?_) heq
    refine IsInSpanAt.mul_left ((hc k).comp_contMDiff hfat) ?_
    rcases hr k with hrk | hrk
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inl ?_)
        ((h𝔞 _ _ hrk).comp_contMDiff hfat)
      exact GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
        ⟨r k,hrk,rfl⟩ ((h𝔞 _ _ hrk).comp_contMDiff hfat))
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inr ?_)
        ((h𝔟 _ _ hrk).comp_contMDiff hfat)
      exact GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
        ⟨r k,hrk,rfl⟩ ((h𝔟 _ _ hrk).comp_contMDiff hfat))
  · refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg))
    rintro _ (hs | hs)
    · exact (GermIdeal.mem_pullback_iff.mp hs).mono fun _ ⟨a,ha,h⟩ =>
        ⟨a,le_sumIdeal_left' (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) _ a ha,h⟩
    · exact (GermIdeal.mem_pullback_iff.mp hs).mono fun _ ⟨b,hb,h⟩ =>
        ⟨b,le_sumIdeal_right' (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) _ b hb,h⟩

private theorem span_zero {d : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] (P : (Z → ℂ) → Prop) (z : Z) :
    IsInSpanAt (n := d) P z (fun _ => 0) := by
  refine ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,fun i => i.elim0,
    fun i => i.elim0,Eventually.of_forall fun _ => ?_⟩
  simp

private theorem vanishingIdeal_unit_presentation {d : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] {C : Set Z} (hC : IsClosed C) {z : Z}
    (hz : z ∉ C) (g : Z → ℂ) :
    (vanishingIdeal (n := d) C).mem z g ↔
      IsInSpanAt (n := d) (· ∈ range (fun _ : Fin 1 => fun _ : Z => (1 : ℂ))) z g := by
  constructor
  · intro hg
    exact isInSpanAt_of_eq_mul ⟨0,rfl⟩ hg.1 hg.1
      (Eventually.of_forall fun _ => by simp)
  · intro hg
    refine ⟨hg.1,?_⟩
    filter_upwards [hC.isOpen_compl.mem_nhds hz] with w hw hwC
    exact (hw hwC).elim

/-- ONLY the original closed submanifold and genuine submersion produce the whole ideal equality. -/
theorem pullback_vanishingIdeal_submersion {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {N : Set X} (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) N) =
      vanishingIdeal (n := m) (f ⁻¹' N) := by
  classical
  apply GermIdeal.ext
  funext y g
  apply propext
  by_cases hy : f y ∈ N
  · obtain ⟨j,hj,_,Φ,hsrc,h0,hflat⟩ := hN.2 (f y) hy
    let S := Finset.univ.filter fun i : Fin n => j ≤ i.val
    have hflatΦ : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) (f y)).source →
        chartAt (ComplexModel n) (f y) z ∈ Φ.source →
          (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (f y) z) ∈ coordSubspace S) := by
      intro z hz hzΦ
      simp only [S,coordSubspace_eq_complexCoordinatePlane]
      change z ∈ N ↔ Φ.toFun ((complexChartAt (n := n) (f y)).val z) ∈ complexCoordinatePlane n j
      exact hflat hz hzΦ
    obtain ⟨Ξ,ρ,hΞsrc,hΞ0,hΞdict⟩ :=
      exists_lifted_coordinates (n := n) (m := m) (f := f) (y := y) (hf.isSubmersionAt y) Φ h0
    have hflatΞ : ∀ {z : Y}, z ∈ (chartAt (ComplexModel m) y).source →
        chartAt (ComplexModel m) y z ∈ Ξ.source →
          (z ∈ f ⁻¹' N ↔ Ξ.toFun (chartAt (ComplexModel m) y z) ∈ coordSubspace (S.map ρ)) := by
      intro z hz hzΞ
      have hd := hΞdict z ⟨hz,hzΞ⟩
      change f z ∈ N ↔ Ξ.toFun (chartAt (ComplexModel m) y z) ∈ coordSubspace (S.map ρ)
      rw [hflatΦ hd.1.1 hd.1.2]
      constructor
      · intro h i hi
        obtain ⟨i,hSi,rfl⟩ := Finset.mem_map.mp hi
        change flatCoord Ξ (ρ i) z = 0
        exact (hd.2 i).trans (h i hSi)
      · intro h i hi
        change flatCoord Φ i (f z) = 0
        rw [← hd.2 i]
        exact h (ρ i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    have hs : ∀ i, HolomorphicAt n (coordinateFamily Φ S i) (f y) := by
      intro i
      by_cases hi : i ∈ S
      · simpa only [coordinateFamily,hi,if_true] using
          holomorphicAt_flatCoord Φ i (mem_flatDomain_self Φ)
      · simpa only [coordinateFamily,hi,if_false] using holomorphicAt_const (n := n) (M := X) 0
    rw [pullback_mem_iff_finite_family hf.contMDiff _ hs
      (vanishingIdeal_mem_iff_coordinate_family Φ S hsrc h0 hflatΦ) g,
      vanishingIdeal_mem_iff_coordinate_family Ξ (S.map ρ) hΞsrc hΞ0 hflatΞ g]
    constructor
    · intro hg
      refine IsInSpanAt.trans ?_ hg
      rintro _ ⟨i,rfl⟩
      by_cases hi : i ∈ S
      · have hip : ρ i ∈ S.map ρ := Finset.mem_map.mpr ⟨i,hi,rfl⟩
        have hh : HolomorphicAt m (coordinateFamily Ξ (S.map ρ) (ρ i)) y := by
          simpa only [coordinateFamily,hip,if_true] using
            holomorphicAt_flatCoord Ξ (ρ i) (mem_flatDomain_self Ξ)
        refine DerivativeIdeal.isInSpanAt_congr
          (InvertibleIdealQuotient.isInSpanAt_self ⟨ρ i,rfl⟩ hh) ?_
        filter_upwards [(isOpen_flatDomain Ξ).mem_nhds (mem_flatDomain_self Ξ)] with z hz
        simp only [coordinateFamily,hi,hip,if_true,Function.comp_apply]
        exact (hΞdict z hz).2 i
      · simpa only [coordinateFamily,hi,if_false,Function.comp_def] using
          span_zero (· ∈ range (coordinateFamily Ξ (S.map ρ))) y
    · intro hg
      refine IsInSpanAt.trans ?_ hg
      rintro _ ⟨i,rfl⟩
      by_cases hi : i ∈ S.map ρ
      · obtain ⟨i,hSi,rfl⟩ := Finset.mem_map.mp hi
        have hip : ρ i ∈ S.map ρ := Finset.mem_map.mpr ⟨i,hSi,rfl⟩
        have hh : HolomorphicAt m (coordinateFamily Φ S i ∘ f) y :=
          (hs i).comp_contMDiff (Eventually.of_forall fun z => hf.contMDiff.contMDiffAt (x := z))
        refine DerivativeIdeal.isInSpanAt_congr
          (InvertibleIdealQuotient.isInSpanAt_self ⟨i,rfl⟩ hh) ?_
        filter_upwards [(isOpen_flatDomain Ξ).mem_nhds (mem_flatDomain_self Ξ)] with z hz
        simp only [coordinateFamily,hSi,hip,if_true,Function.comp_apply]
        exact ((hΞdict z hz).2 i).symm
      · simpa only [coordinateFamily,hi,if_false] using
          span_zero (· ∈ range (fun i => coordinateFamily Φ S i ∘ f)) y
  · have hCy := hN.1.preimage hf.contMDiff.continuous
    rw [pullback_mem_iff_finite_family hf.contMDiff (fun _ : Fin 1 => fun _ : X => (1 : ℂ))
      (fun _ => holomorphicAt_const 1) (vanishingIdeal_unit_presentation hN.1 hy) g,
      vanishingIdeal_unit_presentation hCy hy g]
    rfl

/-- The entire original restriction is retained under genuine submersions. -/
theorem pullback_restrictOn_submersion {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {N : Set X} (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent) :
    GermIdeal.pullback (m := m) f (restrictOn n N I) =
      restrictOn m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) := by
  rw [restrictOn_eq_sum_vanishingIdeal hI,
    pullback_sumIdeal_dimensions hf.contMDiff hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN),
    pullback_vanishingIdeal_submersion hf hN,
    restrictOn_eq_sum_vanishingIdeal (isCoherent_pullback hf.contMDiff hI)]

/-- Coherence is internally inherited for the actual whole pulled restricted ideal. -/
theorem isCoherent_restrictOn_preimage_submersion {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {N : Set X} (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent) :
    (restrictOn m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I)).IsCoherent := by
  rw [← pullback_restrictOn_submersion hf hN hI]
  exact isCoherent_pullback hf.contMDiff (isCoherent_restrictOn_of_isClosedSubmanifold hI hN)

/-- Every actual marked field, including all literal ordered boundary entries, is retained. -/
theorem markedPullback_restricted_record {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) :
    markedPullback (m := m) f {M with ideal := restrictOn n M.N M.ideal} =
      {markedPullback (m := m) f M with
        ideal := restrictOn m (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal)} := by
  simp only [markedPullback]
  congr 1
  exact pullback_restrictOn_submersion hf hN hI

end
end Hironaka.HironakaSmoothSubmersionRelativeRestriction
