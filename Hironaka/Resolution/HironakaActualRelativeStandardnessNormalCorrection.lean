import Hironaka.Resolution.HironakaActualRelativeStandardnessIdealIntersection
import Hironaka.Resolution.HironakaRelativeNormalFibreHilbertSamuel

/-!
# Original-germ normal corrections from a free actual normal truncation

This bridge uses the same original tangent scalar action and entire normal
ideal powers. Its freeness premise must be supplied by a separate producer.
-/

set_option autoImplicit false

namespace Hironaka.HironakaActualRelativeStandardnessNormalCorrection

noncomputable section

open HolGerm HironakaRelativeNormalIdeal
  HironakaRelativeNormalFibreHilbertSamuel
  HironakaActualRelativeStandardnessIdealIntersection

/-- A free original normal quotient internally corrects the same ideal numerator. -/
theorem exists_original_normal_power_correction (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d + t)))) (q : ℕ)
    (hfree : letI := tangentAlgebra d t
      Module.Free (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d + t)) ⧸ (I ⊔ normalIdeal d t ^ q)))
    (g : HolGerm (ComplexModel (d + t))) (hg : g ∈ I)
    (hgpow : g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q) :
    ∃ g' : HolGerm (ComplexModel (d + t)), g' ∈ I ∧ g' ∈ normalIdeal d t ^ q ∧
      g - g' ∈ originalBaseMaximalIdeal d t := by
  let := tangentAlgebra d t
  let B := HolGerm (ComplexModel d)
  let R := HolGerm (ComplexModel (d + t))
  let J := IsLocalRing.maximalIdeal B
  let : Module.Free B (R ⧸ (I ⊔ normalIdeal d t ^ q)) := hfree
  have hBase : J • (⊤ : Submodule B R) =
      (originalBaseMaximalIdeal d t).restrictScalars B := by
    rw [Ideal.smul_top_eq_map]
    rfl
  have hPower := fibreMaximalIdeal_power_eq d t q (⊥ : Ideal R)
  simp only [bot_sup_eq] at hPower
  have hgSup : g ∈ originalBaseMaximalIdeal d t ⊔ normalIdeal d t ^ q := by
    rw [← hPower]
    exact Ideal.mem_sup_right hgpow
  have hgJ : g ∈ (J • (⊤ : Submodule B R)) ⊔ (normalIdeal d t ^ q).restrictScalars B := by
    obtain ⟨a, ha, n, hn, he⟩ := Submodule.mem_sup.mp hgSup
    refine Submodule.mem_sup.mpr ⟨a, ?_, n, hn, he⟩
    rw [hBase]
    exact ha
  obtain ⟨h, hh, hRemainder⟩ :=
    exists_ideal_correction_of_projective I (normalIdeal d t ^ q) J g hg hgJ
  refine ⟨g - h, hRemainder.1, hRemainder.2, ?_⟩
  have hLe : J • I.restrictScalars B ≤ J • (⊤ : Submodule B R) :=
    smul_mono_right J le_top
  have hInBase : h ∈ J • (⊤ : Submodule B R) := hLe hh
  rw [hBase] at hInBase
  change h ∈ originalBaseMaximalIdeal d t at hInBase
  simpa only [sub_sub_cancel] using hInBase

end

end Hironaka.HironakaActualRelativeStandardnessNormalCorrection
