import Hironaka.Resolution.FactorizationFromResolution
import Hironaka.Blowup.BlowupSequenceTotalTransform
import Hironaka.Blowup.BlowupExistence
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

/-! Actual disjoint-centre blowups commute by their genuine universal properties.
Blueprint: `hironaka-disjoint-blowup-commutation.tex`. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaDisjointBlowupCommutation

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers GermIdealTotalTransform

variable {n : ℕ} {X Y W Z Q : CMfd.{u} n}

private theorem first_centre_invertible_on_double
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    {E : Set Y} {q : Z → Y} (hq : IsBlowupAlong n E q) :
    (GermIdeal.pullback (m := n) (π ∘ q) (vanishingIdeal (n := n) C)).IsInvertible := by
  rw [pullback_comp hπ.contMDiff hq.contMDiff
    (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)]
  exact isInvertible_pullback hq.contMDiff
    (BlowupExceptionalDivisor.interior_exceptionalLocus_eq_empty hq) hπ.2.2.2.1

private theorem both_original_centres_invertible
    {C D : Set X} {π : Y → X} {ρ : W → X}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ) (hCD : Disjoint C D)
    {q : Z → Y} (hq : IsBlowupAlong n (π ⁻¹' D) q) :
    (GermIdeal.pullback (m := n) (π ∘ q) (vanishingIdeal (n := n) C)).IsInvertible ∧
    (GermIdeal.pullback (m := n) (π ∘ q) (vanishingIdeal (n := n) D)).IsInvertible := by
  refine ⟨first_centre_invertible_on_double hπ hq, ?_⟩
  rw [pullback_comp hπ.contMDiff hq.contMDiff
    (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hρ),
    FactorizationFromResolution.pullback_vanishingIdeal_eq_of_disjoint hπ hρ.1.1 hCD]
  exact hq.2.2.2.1

private theorem exists_double_comparison_map
    {C D : Set X} {π : Y → X} {ρ : W → X}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ) (hCD : Disjoint C D)
    {q : Z → Y} (hq : IsBlowupAlong n (π ⁻¹' D) q)
    {r : Q → W} (hr : IsBlowupAlong n (ρ ⁻¹' C) r) :
    ∃ e : Z → Q, ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e ∧
      (ρ ∘ r) ∘ e = π ∘ q := by
  obtain ⟨hInvC, hInvD⟩ := both_original_centres_invertible hπ hρ hCD hq
  obtain ⟨a, ⟨ha, hρa⟩, _⟩ := hρ.2.2.2.2 n Z (π ∘ q)
    (hπ.contMDiff.comp hq.contMDiff) hInvD
  have hInvR : (GermIdeal.pullback (m := n) a (vanishingIdeal (n := n) (ρ ⁻¹' C))).IsInvertible := by
    rw [← FactorizationFromResolution.pullback_vanishingIdeal_eq_of_disjoint hρ hπ.1.1 hCD.symm,
      ← pullback_comp hρ.contMDiff ha (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ),
      hρa]
    exact hInvC
  obtain ⟨e, ⟨he, hre⟩, _⟩ := hr.2.2.2.2 n Z a ha hInvR
  refine ⟨e, he, ?_⟩
  calc
    (ρ ∘ r) ∘ e = ρ ∘ (r ∘ e) := rfl
    _ = ρ ∘ a := by rw [hre]
    _ = π ∘ q := hρa

private theorem double_endomap_eq_id
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    {E : Set Y} {q : Z → Y} (hq : IsBlowupAlong n E q)
    (k : Z → Z) (hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ k)
    (hbase : (π ∘ q) ∘ k = π ∘ q) : k = id := by
  obtain ⟨_, _, huniq⟩ := hπ.2.2.2.2 n Z (π ∘ q)
    (hπ.contMDiff.comp hq.contMDiff) (first_centre_invertible_on_double hπ hq)
  have hqk : q ∘ k = q :=
    (huniq (q ∘ k) ⟨hq.contMDiff.comp hk, hbase⟩).trans
      (huniq q ⟨hq.contMDiff, rfl⟩).symm
  exact BlowupUniqueness.eq_id_of_comp_eq hq hk hqk

/-- ANY two REAL double blowups at disjoint original centres have an
internally constructed genuine biholomorphism over the actual base. -/
theorem disjoint_double_blowup_comparison
    {C D : Set X} {π : Y → X} {ρ : W → X}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ) (hCD : Disjoint C D)
    {q : Z → Y} (hq : IsBlowupAlong n (π ⁻¹' D) q)
    {r : Q → W} (hr : IsBlowupAlong n (ρ ⁻¹' C) r) :
    ∃ e : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Q,
      (ρ ∘ r) ∘ e = π ∘ q := by
  obtain ⟨e, he, hbaseE⟩ := exists_double_comparison_map hπ hρ hCD hq hr
  obtain ⟨b, hb, hbaseB⟩ := exists_double_comparison_map hρ hπ hCD.symm hr hq
  have hbe : b ∘ e = id := double_endomap_eq_id hπ hq (b ∘ e) (hb.comp he) (by
    calc
      (π ∘ q) ∘ (b ∘ e) = ((π ∘ q) ∘ b) ∘ e := rfl
      _ = (ρ ∘ r) ∘ e := by rw [hbaseB]
      _ = π ∘ q := hbaseE)
  have heb : e ∘ b = id := double_endomap_eq_id hρ hr (e ∘ b) (he.comp hb) (by
    calc
      (ρ ∘ r) ∘ (e ∘ b) = ((ρ ∘ r) ∘ e) ∘ b := rfl
      _ = (π ∘ q) ∘ b := by rw [hbaseE]
      _ = ρ ∘ r := hbaseB)
  exact ⟨⟨⟨e, b, congrFun hbe, congrFun heb⟩, he, hb⟩, hbaseE⟩

private theorem preimage_centre_geometry
    {C D : Set X} {π : Y → X} {ρ : W → X}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ) (hCD : Disjoint C D) :
    IsClosedSubmanifold n (π ⁻¹' D) ∧ interior (π ⁻¹' D) = ∅ := by
  refine ⟨⟨hρ.1.1.preimage hπ.contMDiff.continuous, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨k, hk⟩ := hρ.1.2 (π z) hz
    have hzExc : z ∉ exceptionalLocus n π := fun he =>
      disjoint_left.mp hCD (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ he) hz
    exact ⟨k, RegularAtDimTransport.regularAtDim_of_preimage hπ.contMDiff hzExc
      isOpen_univ (mem_univ z) (fun _ _ => Iff.rfl) hk⟩
  · exact BlowupSequenceTotalTransform.interior_preimage_eq_empty hπ.contMDiff
      (BlowupExceptionalDivisor.interior_exceptionalLocus_eq_empty hπ) hρ.2.1

/-- Original REAL disjoint-centre blowups internally construct BOTH actual
pulled-centre blowups and their genuine comparison; no pulled-centre geometry,
comparison or inverse is supplied as a certificate. -/
theorem exists_disjoint_double_blowups
    {C D : Set X} {π : Y → X} {ρ : W → X}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ) (hCD : Disjoint C D) :
    ∃ (Z Q : CMfd.{u} n) (q : Z → Y) (r : Q → W),
      IsBlowupAlong n (π ⁻¹' D) q ∧ IsBlowupAlong n (ρ ⁻¹' C) r ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Q,
        (ρ ∘ r) ∘ e = π ∘ q := by
  obtain ⟨hD, hDInt⟩ := preimage_centre_geometry hπ hρ hCD
  obtain ⟨hC, hCInt⟩ := preimage_centre_geometry hρ hπ hCD.symm
  obtain ⟨Z, tZ, cZ, mZ, q, hq⟩ := BlowupExistence.exists_isBlowupAlong (π ⁻¹' D) hD hDInt
  let : TopologicalSpace Z := tZ
  let : ChartedSpace (ComplexModel n) Z := cZ
  let : IsComplexManifold n Z := mZ
  obtain ⟨Q, tQ, cQ, mQ, r, hr⟩ := BlowupExistence.exists_isBlowupAlong (ρ ⁻¹' C) hC hCInt
  let : TopologicalSpace Q := tQ
  let : ChartedSpace (ComplexModel n) Q := cQ
  let : IsComplexManifold n Q := mQ
  exact ⟨⟨Z⟩, ⟨Q⟩, q, r, hq, hr, disjoint_double_blowup_comparison hπ hρ hCD hq hr⟩

end

end Hironaka.HironakaDisjointBlowupCommutation
