/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFixedFlatteningBlowupCoordinates
import Hironaka.Resolution.HironakaActualOpenCoordinateStrictSquare
import Hironaka.Resolution.HironakaActualFlatCoordinateIntrinsicHS
import Hironaka.Resolution.HironakaActualPointGeometricBennett
import Hironaka.Blowup.BlowupExistenceCodimOne

/-!
# Whole original and strict-transform HS dictionaries in one fixed flattening

The literal model subset lives on the genuine target of the supplied
flattening. Its whole vanishing origin ideal is the same original flattened
ideal used by the normal-layer producers. Whole open-coordinate strict sets
and intrinsic HS functions are then transported across the actual polynomial
square, including exceptional points. No inequality or vertex compatibility
is a premise or conclusion.
Blueprint: `hironaka-actual-fixed-flattening-hs-comparison-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualFixedFlatteningHSComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates HironakaHolomorphicJetChartInvariance
  HironakaActualFlatCoordinateIntrinsicHS HironakaActualVanishingIntrinsicHSTransport
  HironakaActualOpenCoordinateStrictSquare HironakaActualAnalyticBlowupTaylor
  HironakaActualFixedFlatteningBlowupCoordinates HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations RelativePrincipalizationSpan
  InvertibleIdealQuotient HadamardBridge

section Original
variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The literal model subset, with the true target domain retained. -/
def actualFixedFlatteningSet (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) (W : Set X) :
    Set (ComplexModel n) := Φ.target ∩ actualFlatteningInverseMap x Φ ⁻¹' W

/-- At every true target point the actual inverse pullback is precisely the whole model vanishing germ. -/
theorem flattened_vanishing_mem_iff (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (W : Set X) (a : ComplexModel n) (ha : a ∈ Φ.target) (f : ComplexModel n → ℂ) :
    (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ).mem a f ↔
      (vanishingIdeal (n := n) (actualFixedFlatteningSet x Φ W)).mem a f := by
  let F : X → ComplexModel n := fun y => Φ.toFun (chartAt (ComplexModel n) x y)
  have hi : actualFlatteningInverseMap x Φ a ∈ flatDomain Φ := (flatInverse_mem Φ ha hsrc).1
  have hFa : F (actualFlatteningInverseMap x Φ a)=a := (flatInverse_mem Φ ha hsrc).2
  have hFfat : ∀ᶠ y in 𝓝 (actualFlatteningInverseMap x Φ a),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) F y := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hi] with y hy
    exact (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).mdifferentiableAt.comp y
      (mdifferentiableAt_chart hy.1)
  have hFt : Tendsto F (𝓝 (actualFlatteningInverseMap x Φ a)) (𝓝 a) := by
    simpa only [hFa] using hFfat.self_of_nhds.continuousAt.tendsto
  have hit := (actualFlatteningInverseMap_mdifferentiable x Φ hsrc a ha).continuousAt.tendsto
  constructor
  · rintro ⟨hf,N,s,c,hs,_hc,he⟩
    refine ⟨hf,?_⟩
    have hall : ∀ᶠ w in 𝓝 a, ∀ i, w ∈ actualFixedFlatteningSet x Φ W → s i w=0 := by
      refine eventually_all.mpr fun i => ?_
      obtain ⟨g,hg,hsg⟩ := hs i
      filter_upwards [hit.eventually hg.2] with w hw hwA
      rw [hsg]
      exact hw hwA.2
    filter_upwards [he,hall] with w hew hw hwA
    rw [hew]
    exact Finset.sum_eq_zero fun i _ => by rw [hw i hwA,mul_zero]
  · rintro ⟨hf,hfA⟩
    let g : X → ℂ := f ∘ F
    have hg : HolomorphicAt n g (actualFlatteningInverseMap x Φ a) :=
      holomorphicAt_comp_map hFfat (by simpa only [hFa] using hf)
    have hgW : (vanishingIdeal (n := n) W).mem (actualFlatteningInverseMap x Φ a) g := by
      refine ⟨hg,?_⟩
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hi,hFt.eventually hfA] with y hy hfy hyW
      apply hfy
      refine ⟨Φ.mapsTo_toFun hy.2,?_⟩
      change actualFlatteningInverseMap x Φ (F y) ∈ W
      have hInvF : actualFlatteningInverseMap x Φ (F y)=y := flatInverse_flat Φ hy
      exact hInvF.symm ▸ hyW
    change IsInSpanAt (n := n) (fun s => ∃ q,
      (vanishingIdeal (n := n) W).mem (actualFlatteningInverseMap x Φ a) q ∧
        s=q ∘ actualFlatteningInverseMap x Φ) a f
    apply isInSpanAt_of_eq_mul (s := g ∘ actualFlatteningInverseMap x Φ)
      ⟨g,hgW,rfl⟩ hf (holomorphicAt_const 1)
    filter_upwards [Φ.isOpen_target.mem_nhds ha] with w hw
    change f w=1 * f (Φ.toFun (chartAt (ComplexModel n) x (actualFlatteningInverseMap x Φ w)))
    rw [actualNearbyPoint_chart_value x Φ hsrc w hw,Φ.right_inv w hw,one_mul]

/-- The SAME translated original flattened origin ideal is the whole model vanishing origin ideal. -/
theorem originalFlattenedVanishingOriginIdeal_eq_model (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) (W : Set X) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ) 0)=
      originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet x Φ W)) := by
  have h0T := actualFlattening_target_zero_mem x Φ h0
  have hmem (f : ComplexModel n → ℂ) :
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ) 0).mem 0 f ↔
        (vanishingIdeal (n := n) (actualFixedFlatteningSet x Φ W)).mem 0 f := by
    change IsInSpanAt (n := n) (fun s => ∃ g,
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ).mem (0+0) g ∧
        s=g ∘ actualAffineTranslation n 0) 0 f ↔ _
    simp only [zero_add]
    simp_rw [flattened_vanishing_mem_iff x Φ hsrc W 0 h0T]
    have ht : actualAffineTranslation n 0=id := funext fun _ => zero_add _
    rw [ht]
    exact BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff
  unfold originalCoherentOriginIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨f,hf,hIf,rfl⟩
    exact ⟨f,hf,(hmem f).mp hIf,rfl⟩
  · rintro ⟨f,hf,hIf,rfl⟩
    exact ⟨f,hf,(hmem f).mpr hIf,rfl⟩

/-- The original whole intrinsic HS at x is exactly that of the supplied flattening's literal model at zero. -/
theorem hilbertSamuelAt_eq_fixedFlattening_model (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) (W : Set X) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) (actualFixedFlatteningSet x Φ W)) 0 ℓ := by
  let V : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  have h0V : (0 : ComplexModel n) ∈ V := actualFlattening_target_zero_mem x Φ h0
  let v0 : V := ⟨0,h0V⟩
  have hA : (Subtype.val : V → ComplexModel n) ⁻¹' actualFixedFlatteningSet x Φ W=
      (fun q : V => actualFlatteningInverseMap x Φ q) ⁻¹' W := by
    ext q
    exact and_iff_right q.2
  have h := hilbertSamuelAt_vanishing_actual_flat_inverse Φ hsrc W v0 ℓ
  change hilbertSamuelAt (vanishingIdeal (n := n)
    ((fun q : V => actualFlatteningInverseMap x Φ q) ⁻¹' W)) v0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W) (actualFlatteningInverseMap x Φ 0) ℓ at h
  rw [actualFlatteningInverseMap_zero x Φ h0] at h
  exact h.symm.trans ((congrArg (fun S : Set V => hilbertSamuelAt (vanishingIdeal (n := n) S) v0 ℓ) hA).symm.trans
    (hilbertSamuelAt_vanishing_actual_open_any V (actualFixedFlatteningSet x Φ W) v0 ℓ))

end Original

section Strict
variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The same whole original strict set is exactly the model strict set on the entire true source target. -/
theorem strictTransform_eq_fixedFlattening_preimage {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (z : Y) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (j : Fin n) (b : Fin n → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hnormal : ∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
      π y ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
        actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b (Θ.toFun (chartAt (ComplexModel n) z y)))
    (W : Set X) :
    let U : Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
    (fun q : U => actualFlatteningInverseMap z Θ q) ⁻¹' strictTransform n π W=
      (Subtype.val : U → ComplexModel n) ⁻¹'
        strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b)
          (actualFixedFlatteningSet (π z) Φ W) := by
  let DX : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let DY : Opens Y := ⟨flatDomain Θ,isOpen_flatDomain Θ⟩
  let V : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let U : Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
  let a : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ DX :=
    (actualFlatCoordinateDiffeomorph Φ hΦsrc).symm
  let c : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ DY :=
    (actualFlatCoordinateDiffeomorph Θ hΘsrc).symm
  let P := actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b
  have hnorm (q : U) : π (c q : Y) ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π (c q : Y)))=P q := by
    have hy := (c q).2
    have h := hnormal (c q) hy.1 hy.2
    have hc : Θ.toFun (chartAt (ComplexModel n) z (c q : Y))=(q : ComplexModel n) :=
      (flatInverse_mem Θ q.2 hΘsrc).2
    rw [hc] at h
    exact h
  have hPinto (q : U) : P q ∈ V := by
    change P q ∈ Φ.target
    rw [← (hnorm q).2]
    exact Φ.mapsTo_toFun (hnorm q).1.2
  let Q : U → V := fun q => ⟨P q,hPinto q⟩
  have hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P := by
    intro q
    apply MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt'
    exact Eventually.of_forall fun _ =>
      (differentiable_actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b).differentiableAt.mdifferentiableAt
  have hQ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ Q :=
    BlowupRestrictOpen.contMDiff_opens_mk (hP.comp contMDiff_subtype_val) hPinto
  have hcomm (q : U) : π (c q : Y)=(a (Q q) : X) := by
    change π (c q : Y)=(chartAt (ComplexModel n) (π z)).symm (Φ.invFun (P q))
    rw [← (hnorm q).2]
    exact (flatInverse_flat Φ (hnorm q).1).symm
  have hA : (Subtype.val : V → ComplexModel n) ⁻¹' actualFixedFlatteningSet (π z) Φ W=
      (fun q : V => (a q : X)) ⁻¹' W := by
    ext q
    exact and_iff_right q.2
  have hglobal := strictTransform_actual_open_coordinate_square π Q hπ hQ DX DY a c hcomm W
  have hmodel := strictTransform_actual_open_coordinate_square P Q hP hQ V U
    (Diffeomorph.refl _ _ _) (Diffeomorph.refl _ _ _) (fun _ => rfl)
      (actualFixedFlatteningSet (π z) Φ W)
  change strictTransform n Q ((Subtype.val : V → ComplexModel n) ⁻¹'
    actualFixedFlatteningSet (π z) Φ W)=
      (Subtype.val : U → ComplexModel n) ⁻¹' strictTransform n P (actualFixedFlatteningSet (π z) Φ W) at hmodel
  rw [hA] at hmodel
  exact hglobal.symm.trans hmodel

/-- Every original strict-transform intrinsic HS value is the same model strict-transform value at zero. -/
theorem hilbertSamuelAt_strict_eq_fixedFlattening_model {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (z : Y) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (j : Fin n) (b : Fin n → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
    (hnormal : ∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
      π y ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
        actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b (Θ.toFun (chartAt (ComplexModel n) z y)))
    (W : Set X) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b)
          (actualFixedFlatteningSet (π z) Φ W))) 0 ℓ := by
  let U : Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
  have h0U : (0 : ComplexModel n) ∈ U := actualFlattening_target_zero_mem z Θ hΘ0
  let u0 : U := ⟨0,h0U⟩
  have hstrict := strictTransform_eq_fixedFlattening_preimage hπ z k Φ hΦsrc j b Θ hΘsrc hnormal W
  have hleft := hilbertSamuelAt_vanishing_actual_flat_inverse Θ hΘsrc (strictTransform n π W) u0 ℓ
  change hilbertSamuelAt (vanishingIdeal (n := n)
    ((fun q : U => actualFlatteningInverseMap z Θ q) ⁻¹' strictTransform n π W)) u0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W))
        (actualFlatteningInverseMap z Θ 0) ℓ at hleft
  rw [actualFlatteningInverseMap_zero z Θ hΘ0] at hleft
  calc
    _ = hilbertSamuelAt (vanishingIdeal (n := n)
        ((fun q : U => actualFlatteningInverseMap z Θ q) ⁻¹' strictTransform n π W)) u0 ℓ := hleft.symm
    _ = hilbertSamuelAt (vanishingIdeal (n := n)
        ((Subtype.val : U → ComplexModel n) ⁻¹'
          strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b)
            (actualFixedFlatteningSet (π z) Φ W))) u0 ℓ := by rw [hstrict]
    _ = _ := hilbertSamuelAt_vanishing_actual_open_any U _ u0 ℓ

/-- The actual blowup constructs both entire original/model HS equalities for the unchanged supplied flattening. -/
theorem exists_actual_fixed_flattening_blowup_hs_comparisons {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (z : Y) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n k))
    (W : Set X) :
    ∃ (j : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z)),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧ k ≤ j.val ∧
      (∀ i : Fin n, i.val < k → b i=0) ∧ b j=0 ∧
      (∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y ∈ Θ.source →
        π y ∈ flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
          actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b (Θ.toFun (chartAt (ComplexModel n) z y))) ∧
      originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) (π z) Φ) 0)=
        originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet (π z) Φ W)) ∧
      ∀ ℓ : ℕ,
        (hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ=
          hilbertSamuelAt (vanishingIdeal (n := n) (actualFixedFlatteningSet (π z) Φ W)) 0 ℓ) ∧
        (hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n := n)
            (strictTransform n (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b)
              (actualFixedFlatteningSet (π z) Φ W))) 0 ℓ) := by
  obtain ⟨j,b,Θ,hΘsrc,hΘ0,hj,hbt,hbj,hnormal⟩ :=
    exists_actual_fixed_flattening_blowup_coordinates hπ z k Φ hΦsrc hΦ0 hflat
  refine ⟨j,b,Θ,hΘsrc,hΘ0,hj,hbt,hbj,hnormal,
    originalFlattenedVanishingOriginIdeal_eq_model (π z) Φ hΦsrc hΦ0 W,?_⟩
  intro ℓ
  exact ⟨hilbertSamuelAt_eq_fixedFlattening_model (π z) Φ hΦsrc hΦ0 W ℓ,
    hilbertSamuelAt_strict_eq_fixedFlattening_model hπ.contMDiff z k Φ hΦsrc j b Θ hΘsrc hΘ0 hnormal W ℓ⟩

end Strict
end
end Hironaka.HironakaActualFixedFlatteningHSComparison
