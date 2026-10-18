/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHolomorphicJetRankLoci

/-! Genuine fibre HS semicontinuity for independent parameter and normal dimensions. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHolomorphicFibreHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm HironakaHolomorphicPointJets
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
variable {r n : ℕ}

theorem actualIndependentParameter_iteratedFDeriv_slice {D : Set (ComplexModel r × ComplexModel n)}
    (hD : IsOpen D) {F : ComplexModel r × ComplexModel n → ℂ}
    (hF : DifferentiableOn ℂ F D) {p : ComplexModel r} (hp : (p, 0) ∈ D) (j : ℕ) :
    iteratedFDeriv ℂ j (fun z => F (p, z)) 0 =
      (iteratedFDeriv ℂ j F (p, 0)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℂ (ComplexModel r) (ComplexModel n)) := by
  let b : ComplexModel r × ComplexModel n := (p, 0)
  let L := ContinuousLinearMap.inr ℂ (ComplexModel r) (ComplexModel n)
  let Fs : ComplexModel r × ComplexModel n → ℂ := fun u => F (u + b)
  let S : Set (ComplexModel r × ComplexModel n) := (fun u => u + b) ⁻¹' D
  have hS : IsOpen S := hD.preimage (continuous_id.add continuous_const)
  have h0 : (0 : ComplexModel r × ComplexModel n) ∈ S := by simpa [S, b] using hp
  have hAn : AnalyticOnNhd ℂ Fs S := by
    intro u hu
    exact (HolomorphicAnalytic.analyticAt_of_differentiableOn hD hF hu).comp
      (f := fun w : ComplexModel r × ComplexModel n => w + b) (x := u)
      (analyticAt_id.add analyticAt_const)
  have hpre : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hL0 : L (0 : ComplexModel n) ∈ S := by simpa only [map_zero] using h0
  have hEq := L.iteratedFDerivWithin_comp_right
    (hAn.contDiffOn hS.uniqueDiffOn (n := (⊤ : ℕ∞ω))) hS.uniqueDiffOn hpre.uniqueDiffOn hL0
    (i := j) (by exact le_top)
  have hLeft : ContDiffAt ℂ j (Fs ∘ L) (0 : ComplexModel n) :=
    ((hAn (L 0) hL0).comp (L.analyticAt 0)).contDiffAt.of_le le_top
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hLeft hL0,
    show L (0 : ComplexModel n) = 0 from map_zero L,
    iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn
      ((hAn 0 h0).contDiffAt.of_le le_top) h0] at hEq
  have hslice : Fs ∘ L = fun z => F (p, z) := by
    funext z
    change F ((0, z) + (p, 0)) = F (p, z)
    congr 1
    ext <;> simp
  rw [hslice] at hEq
  simpa only [Fs, iteratedFDeriv_comp_add_right, zero_add, b] using hEq

private def fixedMultilinearEvaluation (j : ℕ)
    (v : Fin j → (ComplexModel r × ComplexModel n)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin j => ComplexModel r × ComplexModel n) ℂ →L[ℂ] ℂ where
  toFun A := A v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

/-- True partial derivatives of an original joint holomorphic function vary holomorphically. -/
theorem actualNormalDerivative_analytic {U : Set (ComplexModel r)}
    {D : Set (ComplexModel r × ComplexModel n)} (hD : IsOpen D)
    {F : ComplexModel r × ComplexModel n → ℂ} (hF : DifferentiableOn ℂ F D)
    (hU : ∀ p ∈ U, (p, 0) ∈ D) (j : ℕ) (v : Fin j → ComplexModel n) :
    AnalyticOnNhd ℂ (fun p => iteratedFDeriv ℂ j (fun z => F (p, z)) 0 v) U := by
  have hAn : AnalyticOnNhd ℂ F D := fun _ hx =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn hD hF hx
  intro p hp
  have hDer := (hAn.iteratedFDeriv j) (p, 0) (hU p hp)
  have hSlice : AnalyticAt ℂ (fun p : ComplexModel r => (p, (0 : ComplexModel n))) p :=
    (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel n)).analyticAt p
  have hDerSlice := hDer.comp (f := fun x : ComplexModel r => (x, (0 : ComplexModel n))) (x := p) hSlice
  have hEv := ((fixedMultilinearEvaluation j (fun k => (0, v k))).analyticAt _).comp hDerSlice
  apply hEv.congr
  filter_upwards [hSlice.continuousAt.eventually (hD.mem_nhds (hU p hp))] with x hx
  exact congrArg (fun A : ContinuousMultilinearMap ℂ (fun _ : Fin j => ComplexModel n) ℂ => A v)
    (actualIndependentParameter_iteratedFDeriv_slice hD hF hx j).symm


section ActualFibre
variable {s : ℕ} {D : Set (ComplexModel r × ComplexModel n)} (hD : IsOpen D)
  (G : Fin s → ComplexModel r × ComplexModel n → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) D)
include hD hG

/-- Actual original joint holomorphicity on the REAL domain gives genuine normal germs at every parameter. -/
theorem actualFibre_holomorphic (p : ComplexModel r) (hp : (p,0) ∈ D) (i : Fin s) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun w => G i (p,w)) z := by
  have hc : Continuous (fun z : ComplexModel n => (p,z)) := continuous_const.prodMk continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually (hD.mem_nhds hp)] with z hz
  exact ((hG i).differentiableAt (hD.mem_nhds hz)).comp z
    ((differentiableAt_const p).prodMk differentiableAt_id)

/-- The entire actual original fibre ideal, in the ORIGINAL normal germ ring and scalar action. -/
def actualFibreIdeal (p : ComplexModel r) (hp : (p,0) ∈ D) : Ideal (HolGerm (ComplexModel n)) :=
  translatedIdeal (fun i z => G i (p,z)) 0 (actualFibre_holomorphic hD G hG p hp)

/-- BOTH whole original fibre ideal directions retain the SAME original generator germs. -/
theorem actualFibreIdeal_eq_original_span (p : ComplexModel r) (hp : (p,0) ∈ D) :
    actualFibreIdeal hD G hG p hp = Ideal.span (range fun i =>
      HolGerm.mk (fun z => G i (p,z)) (actualFibre_holomorphic hD G hG p hp i)) := by
  unfold actualFibreIdeal translatedIdeal
  congr 1
  apply congrArg Set.range
  funext i
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp

/-- Actual normal-derivative Macaulay entries, with independently varying original parameters. -/
def actualFibreMacaulayMatrix (q : ℕ) (p : ComplexModel r) :
    Matrix (monomialIndex n q) (monomialIndex n q × Fin s) ℂ :=
  originalMacaulayMatrix q (fun i z => G i (p,z)) 0

/-- The entries are holomorphic on ONE actual parameter open, with arbitrary independent fibre dimension. -/
theorem actualFibreMacaulayMatrix_entry_analytic {U : Set (ComplexModel r)}
    (hU : ∀ p ∈ U, (p,0) ∈ D) (q : ℕ) (a : monomialIndex n q)
    (b : monomialIndex n q × Fin s) :
    AnalyticOnNhd ℂ (fun p => actualFibreMacaulayMatrix G q p a b) U := by
  have hcol : DifferentiableOn ℂ
      (fun u : ComplexModel r × ComplexModel n => wordFunction b.1 u.2 * G b.2 u) D := by
    intro u hu
    exact (((differentiable_wordFunction b.1).differentiableAt.comp u differentiableAt_snd).mul
      ((hG b.2).differentiableAt (hD.mem_nhds hu))).differentiableWithinAt
  simpa only [actualFibreMacaulayMatrix,originalMacaulayMatrix,add_zero] using
    actualNormalDerivative_analytic hD hcol hU a.1.val
      (fun k => EuclideanSpace.basisFun (Fin n) ℂ (a.2 k))

/-- The EXISTING whole fibre HS equals the rank of its ACTUAL original normal-jet matrix. -/
theorem hilbertSamuelValue_actualFibreIdeal_eq_rank (p : ComplexModel r) (hp : (p,0) ∈ D) (ℓ : ℕ) :
    hilbertSamuelValue (actualFibreIdeal hD G hG p hp) ℓ =
      Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ+1))) -
        Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) (fun i z => G i (p,z)) 0)) :=
  hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank ℓ _ _ (actualFibre_holomorphic hD G hG p hp)

/-- Every actual finite fibre-HS superlevel is closed in the SAME REAL parameter open. -/
theorem isClosed_actualFibreHS_superlevel (U : TopologicalSpace.Opens (ComplexModel r))
    (hU : ∀ p ∈ U, (p,0) ∈ D) (ℓ k : ℕ) :
    IsClosed {p : U | k ≤ hilbertSamuelValue (actualFibreIdeal hD G hG p (hU p p.property)) ℓ} := by
  let d := Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ+1)))
  by_cases hk : k ≤ d
  · have hentry (a : monomialIndex n (ℓ+1)) (b : monomialIndex n (ℓ+1) × Fin s) :
        Continuous (fun p : U => actualFibreMacaulayMatrix G (ℓ+1) p a b) := by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact ((actualFibreMacaulayMatrix_entry_analytic hD G hG hU (ℓ+1) a b) p p.property).continuousAt.comp
        continuous_subtype_val.continuousAt
    have hc (rows : Fin (d-k+1) → monomialIndex n (ℓ+1))
        (cols : Fin (d-k+1) → monomialIndex n (ℓ+1) × Fin s) :
        Continuous (fun p : U => originalMacaulayMinor (ℓ+1) (fun i z => G i (p,z)) rows cols 0) := by
      exact (continuous_pi fun i => continuous_pi fun j => hentry (rows i) (cols j)).matrix_det
    have heq : {p : U | k ≤ hilbertSamuelValue (actualFibreIdeal hD G hG p (hU p p.property)) ℓ} =
        ⋂ (rows : Fin (d-k+1) → monomialIndex n (ℓ+1))
          (cols : Fin (d-k+1) → monomialIndex n (ℓ+1) × Fin s),
          {p : U | originalMacaulayMinor (ℓ+1) (fun i z => G i (p,z)) rows cols 0=0} := by
      ext p
      simp only [mem_ofPred_eq,mem_iInter]
      exact hilbertSamuelValue_translatedIdeal_ge_iff_minors ℓ k _ _
        (actualFibre_holomorphic hD G hG p (hU p p.property)) hk
    rw [heq]
    exact isClosed_iInter fun rows => isClosed_iInter fun cols => isClosed_eq (hc rows cols) continuous_const
  · have heq : {p : U | k ≤ hilbertSamuelValue (actualFibreIdeal hD G hG p (hU p p.property)) ℓ} = ∅ := by
      ext p
      constructor
      · intro hp
        change k ≤ hilbertSamuelValue (actualFibreIdeal hD G hG p (hU p p.property)) ℓ at hp
        rw [hilbertSamuelValue_actualFibreIdeal_eq_rank hD G hG] at hp
        exact False.elim (hk (hp.trans (Nat.sub_le _ _)))
      · intro hp
        cases hp
    rw [heq]
    exact isClosed_empty

/-- ANY literal coordinatewise ENTIRE fibre-HS superlevel is closed on that same actual open. -/
theorem isClosed_actualFibreHS_entire_superlevel (U : TopologicalSpace.Opens (ComplexModel r))
    (hU : ∀ p ∈ U, (p,0) ∈ D) (h : ℕ → ℕ) :
    IsClosed {p : U | ∀ ℓ, h ℓ ≤ hilbertSamuelValue (actualFibreIdeal hD G hG p (hU p p.property)) ℓ} := by
  have heq : {p : U | ∀ ℓ, h ℓ ≤ hilbertSamuelValue (actualFibreIdeal hD G hG p (hU p p.property)) ℓ} =
      ⋂ ℓ, {p : U | h ℓ ≤ hilbertSamuelValue (actualFibreIdeal hD G hG p (hU p p.property)) ℓ} := by
    ext p
    simp only [mem_ofPred_eq,mem_iInter]
  rw [heq]
  exact isClosed_iInter fun ℓ => isClosed_actualFibreHS_superlevel hD G hG U hU ℓ (h ℓ)
end ActualFibre
end
end Hironaka.HironakaActualHolomorphicFibreHS
