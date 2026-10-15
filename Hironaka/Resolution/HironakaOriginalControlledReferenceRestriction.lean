/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

/-! Controlled relative ideal inclusion on a smaller strict carrier, with
admissibility only for the genuine full reference record. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalControlledReferenceRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient RestrictedIdealWeight
  RestrictedIdealExtension RestrictedIdealQuotient RestrictLeCalculus
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  BlowupTowers BlowupStrictSubmanifold GermIdealPullbackCalculus IdealWeightPowers
  GermIdealTotalTransform GermIdealOrder

section Germs
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

private theorem product_colon_restrictLe (W : Set M) (A L : GermIdeal n M) :
    RestrictLe W (L.mul (colonAlong n W A L)) A := by
  intro x _ f hf
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (mem_mul_iff.mp hf))
  rintro s ⟨a,b,ha,hb,rfl⟩
  exact (hb.2 a ha).2

variable [IsComplexManifold n M]

private theorem cancel_restrictLe_of_left_holomorphic {W : Set M}
    {A B L : GermIdeal n M}
    (hA : ∀ x f,A.mem x f → HolomorphicAt n f x)
    (hB : B.IsCoherent) (hL : IsInvertibleAlong n W L)
    (h : RestrictLe W (A.mul L) (B.mul L)) : RestrictLe W A B := by
  intro x hx f hf
  obtain ⟨U,hU,hxU,l,hld,hnon,hgen⟩ := hL x hx
  have hl : HolomorphicAt n l x := holomorphicAt_of_mdifferentiableOn hU hld hxU
  have hlmem : L.mem x l := (hgen x hxU l).mpr (isInSpanAt_self rfl hl)
  have hfhol := hA x f hf
  obtain ⟨N,s,a,hs,ha,hsum⟩ := h x hx _ (mem_mul_of_mem_mem hf hlmem (hfhol.mul hl))
  have hfac : ∀ i,∃ t : M → ℂ,B.mem x t ∧ s i =ᶠ[𝓝 x] fun y => l y*t y := by
    intro i
    obtain ⟨-,K,v,c,hv,hc,hvsum⟩ := mem_mul_iff.mp (hs i)
    choose p q hp hq hpq using hv
    choose e he heq using fun j => (isInSpanAt_eq_iff.mp ((hgen x hxU (q j)).mp (hq j))).2
    have hphol : ∀ j,HolomorphicAt n (p j) x := fun j => GermIdeal.IsCoherent.holomorphicAt_mem hB (hp j)
    refine ⟨fun y => ∑ j,(c j y*e j y)*p j y,?_,?_⟩
    · exact mem_of_isInSpanAt_mem hB
        ⟨HolomorphicAt.sum _ (fun j _ => ((hc j).mul (he j)).mul (hphol j)),K,p,
          (fun j y => c j y*e j y),hp,(fun j => (hc j).mul (he j)),Eventually.of_forall (fun _ => rfl)⟩
    · filter_upwards [hvsum,eventually_all.mpr heq] with y hy hy'
      rw [hy,Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hpq j]
      show c j y*(p j y*q j y)=l y*(c j y*e j y*p j y)
      rw [hy' j]
      ring
  choose t ht hteq using hfac
  have hthol : ∀ i,HolomorphicAt n (t i) x := fun i => GermIdeal.IsCoherent.holomorphicAt_mem hB (ht i)
  refine ⟨N,t,a,ht,ha,?_⟩
  apply eventuallyEq_within_of_mul_eventuallyEq_within hU hnon hxU hfhol
    (HolomorphicAt.sum _ (fun i _ => (ha i).mul (hthol i)))
  filter_upwards [hsum,eventually_all.mpr hteq] with y hy hy' hyW
  rw [mul_comm (l y) (f y),hy hyW,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hy' i]
  ring
end Germs

section Step
variable {n : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Same-mark relative inclusion passes to the genuine controlled ideals on a
smaller closed strict carrier; only the full reference centre is admissible. -/
theorem restrictLe_geoTransform_of_admissible_reference
    (B K : MarkedIdeal n X) (hN : IsClosedSubmanifold n B.N)
    (hI : B.ideal.IsCoherent) (hS : IsClosed K.N) (hSN : K.N ⊆ B.N)
    (hd : K.d=B.d) {C : Set X} (hC : B.IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hle : RestrictLe K.N K.ideal B.ideal) :
    RestrictLe (K.geoTransform C π).N (K.geoTransform C π).ideal (B.geoTransform C π).ideal := by
  have hsub : (K.geoTransform C π).N ⊆ (B.geoTransform C π).N := by
    change closure (π ⁻¹' (K.N \ C)) ⊆ closure (π ⁻¹' (B.N \ C))
    exact closure_mono (fun _ hy => ⟨hSN hy.1,hy.2⟩)
  have hpb := RestrictLeCalculus.restrictLe_pullback hπ.contMDiff
    (W := (K.geoTransform C π).N)
    (fun _ hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hS hy) hI hle
  have hBfactor := MarkedIdealOperationsAlong.MarkedIdeal.restrictLe_pullback_geoTransform hN hI hC hπ
  have hBfactor' := restrictLe_mono hsub hBfactor.1
  rw [←hd] at hBfactor'
  have hA := product_colon_restrictLe (K.geoTransform C π).N
    (GermIdeal.pullback (m := n) π K.ideal)
    (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) K.d)
  have hBcoh := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hI hC hπ
  refine cancel_restrictLe_of_left_holomorphic
    (fun _ _ hf => hf.1) hBcoh (isInvertibleAlong_geoStrictTransform hπ K.N K.d) ?_
  rw [mul_comm' (K.geoTransform C π).ideal,mul_comm' (B.geoTransform C π).ideal]
  exact RestrictLe.trans (RestrictLe.trans hA hpb) hBfactor'
end Step

section History
variable {n : ℕ} {X : CMfd.{u} n}

/-- The real original reference TEST internally supplies every later reference
geometry; no TEST of the smaller record is used. -/
theorem restrictLe_geoTransformAlong_of_reference_test
    (B K : MarkedIdeal n X) (hB : B.IsWellFormed) (hS : IsClosed K.N)
    (hSN : K.N ⊆ B.N) (hd : K.d=B.d) (hle : RestrictLe K.N K.ideal B.ideal) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower B T →
    IsClosed (geoTransformAlong K T).N ∧
    (geoTransformAlong K T).N ⊆ (geoTransformAlong B T).N ∧
    (geoTransformAlong K T).d=(geoTransformAlong B T).d ∧
    RestrictLe (geoTransformAlong K T).N (geoTransformAlong K T).ideal (geoTransformAlong B T).ideal
  | _,.refl,_ => ⟨hS,hSN,hd,hle⟩
  | _,.step T C π hπ,hT => by
    obtain ⟨hClosed,hSub,hD,hLe⟩ := restrictLe_geoTransformAlong_of_reference_test B K hB hS hSN hd hle T hT.1
    have hBT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hB T hT.1
    refine ⟨isClosed_closure,?_,hD,?_⟩
    · change closure (π ⁻¹' ((geoTransformAlong K T).N \ C)) ⊆
        closure (π ⁻¹' ((geoTransformAlong B T).N \ C))
      exact closure_mono (fun _ hy => ⟨hSub hy.1,hy.2⟩)
    · exact restrictLe_geoTransform_of_admissible_reference _ _ hBT.isClosedSubmanifold_N
        hBT.isCoherent hClosed hSub hD hT.2 hπ hLe

/-- Current reference cosupport gives smaller cosupport on the actual smaller
current carrier; that carrier membership is not silently assumed globally. -/
theorem reference_cosupp_inter_carrier_subset
    (B K : MarkedIdeal n X) (hB : B.IsWellFormed) (hS : IsClosed K.N)
    (hSN : K.N ⊆ B.N) (hd : K.d=B.d) (hle : RestrictLe K.N K.ideal B.ideal)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower B T) :
    (geoTransformAlong B T).cosupp ∩ (geoTransformAlong K T).N ⊆ (geoTransformAlong K T).cosupp := by
  obtain ⟨-,hSub,hD,hLe⟩ := restrictLe_geoTransformAlong_of_reference_test B K hB hS hSN hd hle T hT
  rintro x ⟨hxB,hxK⟩
  have hx : x ∈ cosupport n (geoTransformAlong K T).N (geoTransformAlong B T).ideal
      (geoTransformAlong K T).d := by
    refine ⟨hxK,?_⟩
    rw [hD]
    exact fun g hg => (hxB.2 g hg).mono_set hSub
  exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hLe _ hx
end History
end
end Hironaka.HironakaOriginalControlledReferenceRestriction
