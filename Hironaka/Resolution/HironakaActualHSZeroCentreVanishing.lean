/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHolomorphicJetRankLoci
import Hironaka.Resolution.HironakaRelativeNormalIdeal

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHSZeroCentreVanishing
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalIdeal HironakaHolomorphicJetMonomialSpan

/-- The ORIGINAL whole order-zero quotient is positive exactly for genuine proper original ideals. -/
theorem hilbertSamuelValue_zero_pos_iff_ne_top {n : ℕ}
    (I : Ideal (HolGerm (ComplexModel n))) : 0<hilbertSamuelValue I 0 ↔ I ≠ ⊤ := by
  constructor
  · intro hpos heq
    rw [heq] at hpos
    unfold hilbertSamuelValue at hpos
    rw [top_sup_eq,Module.finrank_zero_of_subsingleton] at hpos
    exact (Nat.lt_irrefl 0) hpos
  · intro hproper
    have hIm := IsLocalRing.le_maximalIdeal hproper
    rw [hilbertSamuelValue,Nat.zero_add,pow_one,sup_eq_right.mpr hIm]
    let : FiniteDimensional ℂ (HolGerm (ComplexModel n) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) := by
      have hfd := finiteDimensional_quotient_maximalIdeal_pow n 1
      rw [pow_one] at hfd
      exact hfd
    let : Nontrivial (HolGerm (ComplexModel n) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) :=
      Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal (HolGerm (ComplexModel n))).ne_top
    exact Module.finrank_pos

/-- The actual open and ordinary holomorphic functions supply the TRUE unchanged local germs at every real point. -/
theorem actual_family_holomorphicAt {n : ℕ} {ι : Type*}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (G : ι → ComplexModel n → ℂ)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) (p : ComplexModel n) (hp : p ∈ U) (i : ι) :
    ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z :=
  eventually_of_mem (hU.mem_nhds hp) fun _z hz => (hG i).differentiableAt (hU.mem_nhds hz)

/-- The SAME original family, proper origin ideal and ordinary HS constancy internally force every actual centre value zero. -/
theorem actual_hs_zero_constant_tangent_generators_vanish (d t : ℕ) {ι : Type*}
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U) (h0 : (0 : ComplexModel (d+t)) ∈ U)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U)
    (hproper : translatedIdeal G 0 (actual_family_holomorphicAt hU G hG 0 h0) ≠ ⊤)
    (hconstant : ∀ (c : ComplexModel d) (hc : tangentInclusion d t c ∈ U),
      hilbertSamuelValue (translatedIdeal G (tangentInclusion d t c)
        (actual_family_holomorphicAt hU G hG _ hc)) 0=
      hilbertSamuelValue (translatedIdeal G 0 (actual_family_holomorphicAt hU G hG 0 h0)) 0) :
    ∀ (c : ComplexModel d) (_hc : tangentInclusion d t c ∈ U) (i : ι), G i (tangentInclusion d t c)=0 := by
  intro c hc i
  have hpos := (hilbertSamuelValue_zero_pos_iff_ne_top
    (translatedIdeal G 0 (actual_family_holomorphicAt hU G hG 0 h0))).mpr hproper
  have hpointpos : 0<hilbertSamuelValue (translatedIdeal G (tangentInclusion d t c)
      (actual_family_holomorphicAt hU G hG _ hc)) 0 := by
    rw [hconstant c hc]
    exact hpos
  have hpointproper := (hilbertSamuelValue_zero_pos_iff_ne_top _).mp hpointpos
  have hmem : translatedGerm (tangentInclusion d t c) (G i)
      (actual_family_holomorphicAt hU G hG _ hc i) ∈
      translatedIdeal G (tangentInclusion d t c) (actual_family_holomorphicAt hU G hG _ hc) :=
    Ideal.subset_span ⟨i,rfl⟩
  have hzero := (HolGerm.mem_maximalIdeal_iff _).mp (IsLocalRing.le_maximalIdeal hpointproper hmem)
  simpa [translatedGerm,HolGerm.eval_mk] using hzero


private theorem coordinate_word_mem_pow (n m : ℕ) (v : Fin m → Fin n) :
    (∏ k : Fin m, coordinateGerm (v k)) ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ,pow_succ']
    apply Ideal.mul_mem_mul
    · apply (HolGerm.mem_maximalIdeal_iff _).mpr
      simp [coordinateGerm,HolGerm.eval_mk]
    · exact ih (Fin.tail v)

/-- The genuine entire original coordinate-word product belongs to its actual degree power, including the empty word. -/
theorem actual_wordMonomial_mem_maximalIdeal_pow {n r : ℕ} (w : monomialIndex n r) :
    wordMonomial w ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^w.1.val :=
  coordinate_word_mem_pow n w.1.val w.2

/-- Actual generator vanishing kills every NEW maximal-length word in the SAME original next finite-jet space. -/
theorem actual_new_maxword_generator_finiteJet_zero {n q : ℕ}
    (w : monomialIndex n (q+1)) (hw : w.1.val=q) (p : ComplexModel n)
    (g : ComplexModel n → ℂ) (hg : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ g z) (hzero : g p=0) :
    finiteJet (q+1) (wordMonomial w*translatedGerm p g hg)=0 := by
  have hgm : translatedGerm p g hg ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    simpa [translatedGerm,HolGerm.eval_mk] using hzero
  have hwm := actual_wordMonomial_mem_maximalIdeal_pow w
  rw [hw] at hwm
  apply (LinearMap.mem_ker).mp
  rw [ker_finiteJet]
  change wordMonomial w*translatedGerm p g hg ∈
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+1)
  rw [pow_succ]
  exact Ideal.mul_mem_mul hwm hgm

end
end Hironaka.HironakaActualHSZeroCentreVanishing
