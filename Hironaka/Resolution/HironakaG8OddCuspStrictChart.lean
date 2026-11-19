import Hironaka.Resolution.HironakaG8OddCuspGeometricSource
import Hironaka.Blowup.BlowupExistenceOriginUniversal
import Hironaka.Blowup.BlowupStrictIdeal

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8OddCuspStrictChart
noncomputable section

open Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaG8OddCuspGeometricSource HironakaG8OddCuspVanishingStalk
  BlowupExistenceOriginModel BlowupExistenceOriginGenerator BlowupExistenceOriginUniversal
  BlowupStrictSubmanifold BlowupStrictIdeal

private abbrev X := ComplexModel 3

theorem embedded_cusp_mem_iff (p : ℕ) (z : X) :
    z ∈ embeddedCuspSet p ↔ z 1 ^ 2 = z 0 ^ p ∧ z 2 = 0 := by
  constructor
  · intro hz
    exact ⟨sub_eq_zero.mp (by simpa [embeddedCuspEquations] using hz 0),
      by simpa [embeddedCuspEquations] using hz 1⟩
  · rintro ⟨h1,h2⟩ i
    fin_cases i
    · simpa [embeddedCuspEquations] using sub_eq_zero.mpr h1
    · simpa [embeddedCuspEquations] using h2

private theorem cusp_eq_zero_of_coord_zero {p : ℕ} (hp : 0 < p) {z : X}
    (hz : z ∈ embeddedCuspSet p) (h0 : z 0 = 0) : z = 0 := by
  obtain ⟨h1,h2⟩ := (embedded_cusp_mem_iff p z).mp hz
  rw [h0,zero_pow hp.ne'] at h1
  have h1' : z 1 = 0 := by
    by_contra hn
    exact pow_ne_zero 2 hn h1
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1'
  · exact h2

/-- The punctured cusp is dense in its whole literal reduced analytic carrier. -/
theorem cusp_subset_closure_punctured (p : ℕ) (hp : 0 < p) :
    embeddedCuspSet p ⊆ closure (embeddedCuspSet p \ ({0} : Set X)) := by
  intro z hz
  by_cases hn : z = 0
  · subst z
    let γ : ℂ → X := fun t =>
      t^2 • EuclideanSpace.single (0 : Fin 3) (1 : ℂ) +
        t^p • EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
    have hγ : Continuous γ := (continuous_id.pow 2 |>.smul continuous_const).add
      ((continuous_id.pow p).smul continuous_const)
    have hγ0 : γ 0 = 0 := by simp [γ,zero_pow hp.ne']
    have hγCoord (t : ℂ) : γ t 0 = t^2 ∧ γ t 1 = t^p ∧ γ t 2 = 0 := by
      refine ⟨?_,?_,?_⟩
      · simp [γ,show (0 : Fin 3) ≠ 1 by decide]
      · simp [γ,show (1 : Fin 3) ≠ 0 by decide]
      · simp [γ,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide]
    apply mem_closure_iff.mpr
    intro U hU h0U
    obtain ⟨t,ht,htNe⟩ := mem_closure_iff.mp ((dense_compl_singleton (0 : ℂ)) 0)
      (γ ⁻¹' U) (hU.preimage hγ) (show γ 0 ∈ U by rwa [hγ0])
    obtain ⟨h0,h1,h2⟩ := hγCoord t
    refine ⟨γ t,ht,⟨(embedded_cusp_mem_iff p _).mpr ⟨?_,h2⟩,?_⟩⟩
    · rw [h0,h1,← pow_mul,← pow_mul,mul_comm p 2]
    · intro h
      have h0' : γ t 0 = 0 := congrArg (fun x : X => x 0) (mem_singleton_iff.mp h)
      exact (pow_ne_zero 2 (fun h => htNe (mem_singleton_iff.mpr h))) (h0.symm.trans h0')
  · exact subset_closure ⟨hz,fun h => hn (mem_singleton_iff.mp h)⟩

/-- Literal coordinate substitution in the genuine point blowup's first chart. -/
theorem first_chart_originProj_coords (z : X) :
    originProj (originMk (0 : Fin 3) z) 0 = z 0 ∧
    originProj (originMk (0 : Fin 3) z) 1 = z 0 * z 1 ∧
    originProj (originMk (0 : Fin 3) z) 2 = z 0 * z 2 := by
  refine ⟨?_,?_,?_⟩
  · simp
  · simp [show (1 : Fin 3) ≠ 0 by decide]
  · simp [show (2 : Fin 3) ≠ 0 by decide]

/-- Cancelling the exceptional powers in both equations gives the exact
punctured preimage of the cusp in the first chart. -/
theorem first_chart_punctured_cusp_iff (p : ℕ) (hp : 2 ≤ p) (z : X) :
    originProj (originMk (0 : Fin 3) z) ∈ embeddedCuspSet p \ ({0} : Set X) ↔
      z ∈ embeddedCuspSet (p-2) ∧ z 0 ≠ 0 := by
  obtain ⟨h0,h1,h2⟩ := first_chart_originProj_coords z
  have he : originProj (originMk (0 : Fin 3) z) = 0 ↔ z 0 = 0 := by
    rw [originProj_eq_zero_iff (originMk_mem_originSource 0 z),originGen_originMk]
  have hPow : z 0 ^ p = z 0 ^ 2 * z 0 ^ (p-2) := by
    rw [← pow_add,show 2+(p-2) = p by omega]
  change (originProj (originMk 0 z) ∈ embeddedCuspSet p ∧
    originProj (originMk 0 z) ∉ ({0} : Set X)) ↔ _
  simp only [mem_singleton_iff,he,embedded_cusp_mem_iff,h0,h1,h2,hPow,mul_pow]
  constructor
  · rintro ⟨⟨ha,hb⟩,hc⟩
    exact ⟨⟨mul_left_cancel₀ (pow_ne_zero 2 hc) ha,(mul_eq_zero.mp hb).resolve_left hc⟩,hc⟩
  · rintro ⟨⟨ha,hb⟩,hc⟩
    exact ⟨⟨congrArg (fun w => z 0 ^ 2 * w) ha,by rw [hb,mul_zero]⟩,hc⟩

/-- The first blowup chart has exactly the reduced exponent p−2 cusp,
including its exceptional point. The equality uses literal closure. -/
theorem first_chart_geoStrictTransform_cusp (p : ℕ) (hp : 2 < p) :
    (originMk (0 : Fin 3)) ⁻¹' geoStrictTransform originProj ({0} : Set X) (embeddedCuspSet p) =
      embeddedCuspSet (p-2) := by
  ext z
  constructor
  · intro hz
    by_contra hNot
    let N : Set (OriginBlowup 3) :=
      originSource 0 ∩ originCoord 0 ⁻¹' (embeddedCuspSet (p-2))ᶜ
    have hN : IsOpen N := (continuousOn_originCoord 0).isOpen_inter_preimage
      (isOpen_originSource 0) (embedded_cusp_isAnalytic (p-2)).isClosed.isOpen_compl
    have hzN : originMk (0 : Fin 3) z ∈ N := ⟨originMk_mem_originSource 0 z,by
      change originCoord 0 (originMk 0 z) ∉ embeddedCuspSet (p-2)
      rwa [originCoord_originMk]⟩
    obtain ⟨a,haN,ha⟩ := mem_closure_iff.mp hz N hN hzN
    have hA := (first_chart_punctured_cusp_iff p hp.le (originCoord 0 a)).mp (by
      rwa [originMk_originCoord haN.1])
    exact haN.2 hA.1
  · intro hz
    have hC := cusp_subset_closure_punctured (p-2) (by omega) hz
    apply mem_closure_iff.mpr
    intro V hV hv
    obtain ⟨a,ha,haS⟩ := mem_closure_iff.mp hC
      (originMk (0 : Fin 3) ⁻¹' V) (hV.preimage (continuous_originMk 0)) hv
    refine ⟨originMk 0 a,ha,(first_chart_punctured_cusp_iff p hp.le a).mpr ⟨haS.1,?_⟩⟩
    intro h0
    exact haS.2 (mem_singleton_iff.mpr (cusp_eq_zero_of_coord_zero (by omega) haS.1 h0))

/-- The same exact chart equation for the library strict transform. -/
theorem first_chart_strictTransform_cusp (p : ℕ) (hp : 2 < p) :
    (originMk (0 : Fin 3)) ⁻¹' strictTransform 3 originProj (embeddedCuspSet p) =
      embeddedCuspSet (p-2) := by
  rw [← geoStrictTransform_eq_strictTransform (isBlowupAlong_originProj (by decide : 0 < 3))
    (cusp_subset_closure_punctured p hp.pos)]
  exact first_chart_geoStrictTransform_cusp p hp

/-- When p>4 is odd, the exact transformed chart remains singular at zero. -/
theorem first_chart_strictTransform_cusp_singular (p : ℕ) (hp : 4 < p) (hOdd : Odd p) :
    (0 : X) ∈ singularSet (n := 3)
      ((originMk (0 : Fin 3)) ⁻¹' strictTransform 3 originProj (embeddedCuspSet p)) := by
  rw [first_chart_strictTransform_cusp p (by omega)]
  have hOdd' : Odd (p-2) := by
    obtain ⟨k,hk⟩ := hOdd
    exact ⟨k-1,by omega⟩
  exact embedded_odd_cusp_singular_at_zero (p-2) hOdd' (by omega)

end
end Hironaka.HironakaG8OddCuspStrictChart

#print axioms Hironaka.HironakaG8OddCuspStrictChart.first_chart_strictTransform_cusp_singular
