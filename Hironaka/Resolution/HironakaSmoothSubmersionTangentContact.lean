/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.TangentFieldUnivExact
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeDifferentialIdeals
import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.Analytic.AnalyticSubsetOpens
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionTangentContact
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates DerivativeIdealAlong DerivativeIdealAlongCoherent
  TangentDirectionAlong GiraudAlong RelativePrincipalizationSpan InvertibleIdealQuotient
  HironakaSmoothSubmersionRelativeDifferentialIdeals HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaSmoothSubmersionComposition HomogenizedIdealAlong GermIdealPullbackCalculus
  GermIdealOrder
noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

theorem isTangentField_of_notMem {N : Set X} (hN : IsClosed N) {x : X} (hx : x ∉ N)
    (e : ComplexChart n X) (ξ : Fin n → X → ℂ) (he : x ∈ e.val.source)
    (hξ : ∀ i, HolomorphicAt n (ξ i) x) : IsTangentField N e ξ x := by
  refine ⟨he,hξ,?_⟩
  intro g hg
  refine ⟨holomorphicAt_fieldDeriv he hξ hg.1,?_⟩
  filter_upwards [hN.isOpen_compl.mem_nhds hx] with z hz hzN
  exact (hz hzN).elim

theorem exists_nonzero_tangentField_preimage_add {t : ℕ} {Y : CMfd.{u} (n+t)} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    {N : Set X} (hN : IsClosedSubmanifold n N) (y : Y) (u : X → ℂ)
    (hu : HolomorphicAt n u (f y)) (e : ComplexChart n X) (ξ : Fin n → X → ℂ)
    (hξ : IsTangentField N e ξ (f y)) (hne : fieldDeriv e ξ u (f y) ≠ 0) :
    ∃ (e' : ComplexChart (n+t) Y) (ξ' : Fin (n+t) → Y → ℂ),
      IsTangentField (f ⁻¹' N) e' ξ' y ∧ fieldDeriv e' ξ' (u ∘ f) y ≠ 0 := by
  by_cases hyN : f y ∈ N
  · obtain ⟨k,_,_,Φ,hΦsrc,h0,hflat⟩ := hN.2 (f y) hyN
    obtain ⟨j,hjk,hju⟩ := exists_flatPartial_ne_zero hΦsrc hflat (mem_flatDomain_self Φ) hyN hu hξ hne
    let Ψ := adaptedCoordinates (hf.isSubmersionAt y) Φ h0
    have hΨsrc := (adaptedCoordinates_dictionary (hf.isSubmersionAt y) Φ h0).1
    have hΨflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel (n+t)) y).source →
        chartAt (ComplexModel (n+t)) y z ∈ Ψ.source →
        (z ∈ f ⁻¹' N ↔ Ψ.toFun (chartAt (ComplexModel (n+t)) y z) ∈
          complexCoordinatePlane (n+t) (t+k)) := by
      intro z hz hzΨ
      exact adaptedCoordinates_whole_centre (hf.isSubmersionAt y) Φ h0 N k
        (fun w hw => hflat hw.1 hw.2) z ⟨hz,hzΨ⟩
    have hjshift : (actualTargetIndex n t j).val < t+k := by
      change t+j.val < t+k
      omega
    refine ⟨complexChartAt (n := n+t) y,
      flatField Ψ (EuclideanSpace.single (actualTargetIndex n t j) 1),
      isTangentField_flatField hΨsrc hΨflat (single_mem_complexCoordinatePlane hjshift)
        (mem_flatDomain_self Ψ),?_⟩
    change flatPartial Ψ (actualTargetIndex n t j) (u ∘ f) y ≠ 0
    rw [adaptedCoordinates_flatPartial_target hf Φ h0 hΦsrc u y (mem_flatDomain_self Ψ) hu j]
    exact hju
  · let Φ := centeredCoordinates (n := n) (f y)
    have hΦsrc := centeredCoordinates_source (n := n) (f y)
    have h0 := centeredCoordinates_zero (n := n) (f y)
    have hflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) (f y)).source →
        chartAt (ComplexModel n) (f y) z ∈ Φ.source →
        (z ∈ (univ : Set X) ↔ Φ.toFun (chartAt (ComplexModel n) (f y) z) ∈
          complexCoordinatePlane n n) := by
      intro z _ _
      constructor
      · intro _ j hj
        exact (Nat.not_le_of_lt j.isLt hj).elim
      · intro _
        exact mem_univ z
    have hξU := isTangentField_univ hξ.mem_source hξ.holomorphicAt
    obtain ⟨j,_,hju⟩ := exists_flatPartial_ne_zero hΦsrc hflat (mem_flatDomain_self Φ)
      (mem_univ (f y)) hu hξU hne
    let Ψ := adaptedCoordinates (hf.isSubmersionAt y) Φ h0
    refine ⟨complexChartAt (n := n+t) y,
      flatField Ψ (EuclideanSpace.single (actualTargetIndex n t j) 1),
      isTangentField_of_notMem (hN.1.preimage hf.contMDiff.continuous) hyN
        (complexChartAt (n := n+t) y) _ (mem_complexChartAt_source y)
        (fun i => holomorphicAt_flatField _ i (mem_flatDomain_self Ψ)),?_⟩
    change flatPartial Ψ (actualTargetIndex n t j) (u ∘ f) y ≠ 0
    rw [adaptedCoordinates_flatPartial_target hf Φ h0 hΦsrc u y (mem_flatDomain_self Ψ) hu j]
    exact hju

theorem exists_nonzero_tangentField_preimage {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {N : Set X} (hN : IsClosedSubmanifold n N) (y : Y) (u : X → ℂ)
    (hu : HolomorphicAt n u (f y)) (e : ComplexChart n X) (ξ : Fin n → X → ℂ)
    (hξ : IsTangentField N e ξ (f y)) (hne : fieldDeriv e ξ u (f y) ≠ 0) :
    ∃ (e' : ComplexChart m Y) (ξ' : Fin m → Y → ℂ),
      IsTangentField (f ⁻¹' N) e' ξ' y ∧ fieldDeriv e' ξ' (u ∘ f) y ≠ 0 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le
    (HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hf.isSubmersionAt y))
  exact exists_nonzero_tangentField_preimage_add hf hN y u hu e ξ hξ hne

theorem isTangentDirectionAlong_preimage {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N I μ U u) :
    IsTangentDirectionAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ (f ⁻¹' U) (u ∘ f) := by
  refine ⟨hu.isOpen.preimage hf.contMDiff.continuous,?_,?_⟩
  · intro y hy
    rw [← HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong hf I hI N hN]
    have huh : HolomorphicAt n u (f y) :=
      GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_iterDerivIdealAlong hI hN (μ-1)) (hu.mem (f y) hy)
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨u,hu.mem (f y) hy,rfl⟩
      (huh.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt))
  · intro y hy hy0
    obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one (f y) hy hy0
    have huh : HolomorphicAt n u (f y) :=
      GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_iterDerivIdealAlong hI hN (μ-1)) (hu.mem (f y) hy)
    exact exists_nonzero_tangentField_preimage hf hN y u huh e ξ hξ hne

theorem isMaximalOrderAlong_preimage {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) (N : Set X) (μ : ℕ)
    (hmax : IsMaximalOrderAlong N I μ) :
    IsMaximalOrderAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ := by
  intro y hy
  apply hmax (f y)
  exact ⟨hy.1,(orderGE_preimage_iff (hf.isSubmersionAt y)
    (fun a ha => GermIdeal.IsCoherent.holomorphicAt_mem hI ha) N (μ+1)).mp hy.2⟩

theorem exists_joint_original_contact_direction {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} (hμ : 1 ≤ μ) (y : Y)
    (hy : y ∈ GermIdealOrder.cosupport m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ)
    (hmax : ¬ OrderGE n N I (f y) (μ+1)) :
    ∃ (U : Set X) (u : X → ℂ), f y ∈ U ∧ IsTangentDirectionAlong N I μ U u ∧
      IsTangentDirectionAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ (f ⁻¹' U) (u ∘ f) := by
  have hyt : f y ∈ GermIdealOrder.cosupport n N I μ :=
    ⟨hy.1,(orderGE_preimage_iff (hf.isSubmersionAt y)
      (fun a ha => GermIdeal.IsCoherent.holomorphicAt_mem hI ha) N μ).mp hy.2⟩
  obtain ⟨U,u,hyU,hu⟩ := exists_isTangentDirectionAlong hI hN hμ hyt hmax
  exact ⟨U,u,hyU,hu,isTangentDirectionAlong_preimage hf hI hN hu⟩

def contactCarrier (N U : Set X) (u : X → ℂ) : Set X := N ∩ {x | u x = 0} ∩ U

theorem contactCarrier_preimage {m : ℕ} {Y : CMfd.{u} m} (f : Y → X)
    (N U : Set X) (u : X → ℂ) :
    f ⁻¹' contactCarrier N U u = contactCarrier (f ⁻¹' N) (f ⁻¹' U) (u ∘ f) := by
  ext y
  rfl

theorem positive_regular_contact_carrier_dimension
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X}
    {μ : ℕ} {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N I μ U u)
    {x : X} {k : ℕ} (hk : RegularAtDim (n := n) N x k) (hxU : x ∈ U) (hx0 : u x = 0) :
    0 < k := by
  obtain ⟨hkn,hxN,Φ,hΦsrc,_,hflat⟩ := hk
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one x hxU hx0
  have huh : HolomorphicAt n u x :=
    holomorphicAt_of_mem_iterDerivIdealAlong
      (fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) (μ-1) x u (hu.mem x hxU)
  obtain ⟨j,hjk,_⟩ := exists_flatPartial_ne_zero hΦsrc hflat (mem_flatDomain_self Φ) hxN huh hξ hne
  omega

theorem exists_joint_contact_regular_dimensions {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N I μ U u)
    (y : Y) (hy : y ∈ contactCarrier (f ⁻¹' N) (f ⁻¹' U) (u ∘ f)) :
    ∃ k : ℕ, 0 < k ∧ RegularAtDim (n := n) N (f y) k ∧
      RegularAtDim (n := n) (contactCarrier N U u) (f y) (k-1) ∧
      RegularAtDim (n := m) (f ⁻¹' N) y (k+(m-n)) ∧
      RegularAtDim (n := m) (contactCarrier (f ⁻¹' N) (f ⁻¹' U) (u ∘ f)) y ((k-1)+(m-n)) := by
  have hyt : f y ∈ contactCarrier N U u := hy
  obtain ⟨k,hk,hc⟩ := hu.regularAtDim_contact
    (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hN hyt
  refine ⟨k,positive_regular_contact_carrier_dimension hI hu hk hyt.2 hyt.1.2,hk,hc,
    regularAtDim_preimage_submersion (hf.isSubmersionAt y) hk,?_⟩
  rw [← contactCarrier_preimage]
  exact regularAtDim_preimage_submersion (hf.isSubmersionAt y) hc

theorem isClosedSubmanifold_contact_in_open
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} (U : TopologicalSpace.Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong N I μ (U : Set X) u) :
    IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' contactCarrier N (U : Set X) u) := by
  have hhol : ∀ x ∈ (U : Set X), HolomorphicAt n u x := fun x hx =>
    holomorphicAt_of_mem_iterDerivIdealAlong
      (fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) (μ-1) x u (hu.mem x hx)
  refine ⟨isClosed_preimage_val_inter_zeroSet hN.1 hhol,?_⟩
  intro x hx
  obtain ⟨k,_,hc⟩ := hu.regularAtDim_contact
    (fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hN hx
  exact ⟨k-1,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hc⟩

theorem exists_joint_original_closed_contacts {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} (hμ : 1 ≤ μ) (y : Y)
    (hy : y ∈ cosupport m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ)
    (hmax : ¬ OrderGE n N I (f y) (μ+1)) :
    ∃ (U : TopologicalSpace.Opens X) (u : X → ℂ), f y ∈ U ∧
      IsTangentDirectionAlong N I μ (U : Set X) u ∧
      IsTangentDirectionAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ (f ⁻¹' (U : Set X)) (u ∘ f) ∧
      IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' contactCarrier N (U : Set X) u) ∧
      let V : TopologicalSpace.Opens Y := ⟨f ⁻¹' (U : Set X),U.isOpen.preimage hf.contMDiff.continuous⟩
      IsClosedSubmanifold m ((Subtype.val : V → Y) ⁻¹' contactCarrier (f ⁻¹' N) (V : Set Y) (u ∘ f)) ∧
      cosupport n N I μ ∩ (U : Set X) ⊆ contactCarrier N (U : Set X) u ∧
      cosupport m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ ∩ (V : Set Y) ⊆
        contactCarrier (f ⁻¹' N) (V : Set Y) (u ∘ f) := by
  obtain ⟨W,u,hyW,hu,hup⟩ := exists_joint_original_contact_direction hf hI hN hμ y hy hmax
  let U : TopologicalSpace.Opens X := ⟨W,hu.isOpen⟩
  let V : TopologicalSpace.Opens Y := ⟨f ⁻¹' (U : Set X),U.isOpen.preimage hf.contMDiff.continuous⟩
  have hIp := isCoherent_pullback hf.contMDiff hI
  have hNp := isClosedSubmanifold_preimage_submersion hf hN
  refine ⟨U,u,hyW,hu,hup,isClosedSubmanifold_contact_in_open hI hN U hu,
    isClosedSubmanifold_contact_in_open hIp hNp V hup,?_,?_⟩
  · intro x hx
    exact ⟨⟨hx.1.1,hu.cosupport_inter_subset
      (fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hμ hx⟩,hx.2⟩
  · intro x hx
    exact ⟨⟨hx.1.1,hup.cosupport_inter_subset
      (fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem hIp hg) hμ hx⟩,hx.2⟩

end
end Hironaka.HironakaSmoothSubmersionTangentContact
