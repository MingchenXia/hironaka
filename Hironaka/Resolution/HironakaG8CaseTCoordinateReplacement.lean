import Hironaka.Resolution.HironakaG8GeneralCentreTransverseFrame

set_option autoImplicit false

/-!
# A specified-pivot coordinate replacement retaining every other coordinate

API extraction of the existing actual inverse-function construction in
`HironakaG8GeneralCentreTransverseFrame.exists_coordinate_replacement`.
The pivot is specified by its ordinary nonzero scalar partial derivative,
and every off-pivot coordinate identity is retained. The existing theorem
and all of its statements remain unchanged. This is reusable coordinate
API work, not a Case T proof or original-goal credit.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CaseTCoordinateReplacement

open RegularAtDimTransport

noncomputable section

variable {n : ℕ}

private def replaceCoordinate (f : ComplexModel n → ℂ) (i : Fin n)
    (z : ComplexModel n) : ComplexModel n :=
  z + (f z - z i) • EuclideanSpace.single i (1 : ℂ)

private theorem replaceCoordinate_apply (f : ComplexModel n → ℂ) (i j : Fin n)
    (z : ComplexModel n) :
    replaceCoordinate f i z j = if j = i then f z else z j := by
  by_cases hji : j = i
  · subst j
    simp [replaceCoordinate]
  · simp [replaceCoordinate, hji]

/-- An actual holomorphic scalar function replaces a specified coordinate
whose partial derivative is nonzero. The other coordinates are literally
unchanged, so any original boundary equations using them survive. -/
theorem exists_coordinate_replacement_at {f : ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (h0U : (0 : ComplexModel n) ∈ U)
    (hf : DifferentiableOn ℂ f U) (hf0 : f 0 = 0) (i : Fin n)
    (hi : fderiv ℂ f 0 (EuclideanSpace.single i 1) ≠ 0) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) 0,
      Ψ.source ⊆ U ∧ Ψ.toFun 0 = 0 ∧
      (∀ z, Ψ.toFun z i = f z) ∧
      ∀ z j, j ≠ i → Ψ.toFun z j = z j := by
  classical
  let D := fderiv ℂ f 0
  let eᵢ : ComplexModel n := EuclideanSpace.single i (1 : ℂ)
  let L : ComplexModel n →L[ℂ] ComplexModel n :=
    ContinuousLinearMap.id ℂ _ + (D - EuclideanSpace.proj i).smulRight eᵢ
  have hFd : DifferentiableOn ℂ (replaceCoordinate f i) U :=
    differentiableOn_id.add ((hf.sub (EuclideanSpace.proj i).differentiableOn).smul_const eᵢ)
  have hFL : HasFDerivAt (replaceCoordinate f i) L 0 :=
    (hasFDerivAt_id 0).add
      (((hf.differentiableAt (hU.mem_nhds h0U)).hasFDerivAt.sub
        (EuclideanSpace.proj i).hasFDerivAt).smul_const eᵢ)
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hcoords : ∀ j : Fin n, j ≠ i → w j = 0 := by
      intro j hji
      have hj := congrArg (fun z : ComplexModel n => z j) hw
      simpa [L, eᵢ, hji] using hj
    have hwi : w = w i • eᵢ := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [eᵢ]
      · simp [eᵢ, hji, hcoords j hji]
    have hDzero : D w = 0 := by
      have hiw := congrArg (fun z : ComplexModel n => z i) hw
      simpa [L, eᵢ] using hiw
    have hcoeff : w i = 0 := by
      rw [hwi, map_smul] at hDzero
      exact (smul_eq_zero.mp hDzero).resolve_right hi
    rw [hwi, hcoeff, zero_smul]
  have hFinj : Function.Injective (fderiv ℂ (replaceCoordinate f i) 0) := by
    rw [hFL.fderiv]
    exact hLinj
  obtain ⟨Ψ, hΨU, hΨF, _hinv⟩ := exists_localHolomorphicEquivAt hU h0U hFd hFinj
  refine ⟨Ψ, hΨU, ?_, ?_, ?_⟩
  · rw [hΨF]
    simp [replaceCoordinate, hf0]
  · intro z
    rw [hΨF, replaceCoordinate_apply, if_pos rfl]
  · intro z j hji
    rw [hΨF, replaceCoordinate_apply, if_neg hji]

end

end Hironaka.HironakaG8CaseTCoordinateReplacement
