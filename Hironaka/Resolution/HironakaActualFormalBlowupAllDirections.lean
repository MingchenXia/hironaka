/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalMonomialBlowupReflection

/-! Actual centered shear inverses supply genuine injectivity and whole-power reflection in every formal blowup direction. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalBlowupAllDirections
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalMonomialBlowupReflection
variable {n : ℕ}

/-- The genuine centered linear shear in the SAME original coordinate ring. -/
def actualFormalCenterShearCoordinates (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) : MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.X i+if i ∈ A\{e} then MvPowerSeries.C (b i)*MvPowerSeries.X e else 0

/-- The literal true centered shear coordinates have actual zero constant coefficients internally. -/
theorem actualFormalCenterShearCoordinates_constant_zero (A : Set (Fin n)) (e : Fin n)
    (b : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries.constantCoeff (actualFormalCenterShearCoordinates A e b i)=0 := by
  simp only [actualFormalCenterShearCoordinates]
  split_ifs <;> simp

/-- The GENUINE formal complex algebra substitution supplied by the actual centered shear. -/
def actualFormalCenterShear (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalCenterShearCoordinates_constant_zero A e b))

/-- Every actual variable has exactly its true centered shear image. -/
theorem actualFormalCenterShear_X (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    actualFormalCenterShear A e b (MvPowerSeries.X i)=actualFormalCenterShearCoordinates A e b i :=
  MvPowerSeries.substAlgHom_X _ i

/-- The SAME actual exceptional variable is fixed by the true shear. -/
theorem actualFormalCenterShear_exceptional (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    actualFormalCenterShear A e b (MvPowerSeries.X e)=MvPowerSeries.X e := by
  simp [actualFormalCenterShear_X,actualFormalCenterShearCoordinates]

private theorem centerShear_C (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (c : ℂ) :
    actualFormalCenterShear A e b (MvPowerSeries.C c)=MvPowerSeries.C c := by
  rw [actualFormalCenterShear,MvPowerSeries.substAlgHom_apply,MvPowerSeries.subst_C]

private theorem centerShear_inverse_coordinates (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) :
    actualFormalCenterShear A e (fun j => -b j) (actualFormalCenterShearCoordinates A e b i)=
      MvPowerSeries.X i := by
  rw [actualFormalCenterShearCoordinates,map_add]
  by_cases hi : i ∈ A\{e}
  · rw [if_pos hi,map_mul,centerShear_C,actualFormalCenterShear_exceptional,actualFormalCenterShear_X]
    rw [actualFormalCenterShearCoordinates,if_pos hi]
    rw [map_neg]
    ring
  · rw [if_neg hi,map_zero,add_zero,actualFormalCenterShear_X,actualFormalCenterShearCoordinates,if_neg hi,add_zero]

/-- GENUINE formal substitution composition proves inverse shears on EVERY actual formal series. -/
theorem actualFormalCenterShear_left_inverse (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalCenterShear A e (fun i => -b i) (actualFormalCenterShear A e b F)=F := by
  dsimp only [actualFormalCenterShear]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply,MvPowerSeries.substAlgHom_apply]
  have hf : (fun i => MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalCenterShearCoordinates_constant_zero A e (fun j => -b j)))
      (actualFormalCenterShearCoordinates A e b i))=MvPowerSeries.X := by
    funext i
    exact centerShear_inverse_coordinates A e b i
  rw [hf,MvPowerSeries.subst_self]
  rfl

/-- The SAME genuine centered shears are inverse in BOTH actual directions. -/
theorem actualFormalCenterShear_right_inverse (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalCenterShear A e b (actualFormalCenterShear A e (fun i => -b i) F)=F := by
  simpa only [neg_neg] using actualFormalCenterShear_left_inverse A e (fun i => -b i) F

/-- The ACTUAL formal complex algebra automorphism is internally constructed from the genuine shear inverse. -/
def actualFormalCenterShearAlgEquiv (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    MvPowerSeries (Fin n) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun := actualFormalCenterShear A e b
  invFun := actualFormalCenterShear A e (fun i => -b i)
  left_inv := actualFormalCenterShear_left_inverse A e b
  right_inv := actualFormalCenterShear_right_inverse A e b
  map_mul' := (actualFormalCenterShear A e b).map_mul
  map_add' := (actualFormalCenterShear A e b).map_add
  commutes' := (actualFormalCenterShear A e b).commutes

/-- The true centered shear maps the WHOLE actual selected-center ideal into itself. -/
theorem map_coordinateIdeal_centerShear_le (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) :
    Ideal.map (actualFormalCenterShear A e b).toRingHom (actualFormalCoordinateIdeal n A) ≤
      actualFormalCoordinateIdeal n A := by
  rw [actualFormalCoordinateIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨G,⟨i,hi,rfl⟩,rfl⟩
  change actualFormalCenterShear A e b (MvPowerSeries.X i) ∈ _
  rw [actualFormalCenterShear_X,actualFormalCenterShearCoordinates]
  apply Ideal.add_mem
  · exact Ideal.subset_span ⟨i,hi,rfl⟩
  · split_ifs
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e,he,rfl⟩)
    · exact Ideal.zero_mem _

/-- Actual inverse shears supply BOTH WHOLE selected-center ideal image directions. -/
theorem map_coordinateIdeal_centerShear (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) :
    Ideal.map (actualFormalCenterShear A e b).toRingHom (actualFormalCoordinateIdeal n A)=
      actualFormalCoordinateIdeal n A := by
  apply le_antisymm (map_coordinateIdeal_centerShear_le A e he b)
  have hcomp : (actualFormalCenterShear A e b).toRingHom.comp
      (actualFormalCenterShear A e (fun i => -b i)).toRingHom=
        RingHom.id (MvPowerSeries (Fin n) ℂ) := by
    apply RingHom.ext
    intro F
    exact actualFormalCenterShear_right_inverse A e b F
  have h := Ideal.map_mono (f := (actualFormalCenterShear A e b).toRingHom)
    (map_coordinateIdeal_centerShear_le A e he (fun i => -b i))
  rw [Ideal.map_map,hcomp,Ideal.map_id] at h
  exact h

/-- EVERY actual center power is preserved as the SAME whole ideal by the true shear. -/
theorem map_coordinate_power_centerShear (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (d : ℕ) :
    Ideal.map (actualFormalCenterShear A e b).toRingHom (actualFormalCoordinateIdeal n A ^ d)=
      actualFormalCoordinateIdeal n A ^ d := by
  rw [Ideal.map_pow,map_coordinateIdeal_centerShear A e he b]

/-- BOTH center-power membership directions are constructed from the SAME genuine inverse maps. -/
theorem mem_coordinate_power_iff_centerShear (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F ∈ actualFormalCoordinateIdeal n A ^ d ↔
      actualFormalCenterShear A e b F ∈ actualFormalCoordinateIdeal n A ^ d := by
  constructor
  · intro hF
    have h := Ideal.mem_map_of_mem (actualFormalCenterShear A e b).toRingHom hF
    rw [map_coordinate_power_centerShear A e he b d] at h
    exact h
  · intro hF
    have h := Ideal.mem_map_of_mem (actualFormalCenterShear A e (fun i => -b i)).toRingHom hF
    rw [map_coordinate_power_centerShear A e he (fun i => -b i) d] at h
    change actualFormalCenterShear A e (fun i => -b i) (actualFormalCenterShear A e b F) ∈ _ at h
    rwa [actualFormalCenterShear_left_inverse] at h

/-- GENUINE formal substitution composition factors the SAME arbitrary-direction chart through the actual zero chart. -/
theorem actualFormalBlowup_eq_zero_comp_centerShear (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalBlowup A e b F=
      actualFormalBlowup A e (fun _ => 0) (actualFormalCenterShear A e b F) := by
  symm
  dsimp only [actualFormalBlowup,actualFormalCenterShear]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply,MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.substAlgHom_apply]
  congr 1
  funext i
  change actualFormalBlowup A e (fun _ => 0) (actualFormalCenterShearCoordinates A e b i)=
    actualFormalBlowupCoordinates A e b i
  rw [actualFormalCenterShearCoordinates,map_add]
  have hC (c : ℂ) : actualFormalBlowup A e (fun _ => 0) (MvPowerSeries.C c)=MvPowerSeries.C c := by
    rw [actualFormalBlowup,MvPowerSeries.substAlgHom_apply,MvPowerSeries.subst_C]
  by_cases hi : i ∈ A
  · by_cases hie : i=e
    · subst i
      simp [actualFormalBlowup_X,actualFormalBlowupCoordinates,he]
    · rw [if_pos (show i ∈ A\{e} from ⟨hi,by simpa using hie⟩),map_mul,hC,
        actualFormalBlowup_X,actualFormalBlowup_X]
      simp [actualFormalBlowupCoordinates,hi,hie,he]
      ring
  · rw [if_neg (show i ∉ A\{e} from fun h => hi h.1),map_zero,add_zero,actualFormalBlowup_X]
    simp [actualFormalBlowupCoordinates,hi]

/-- Every actual blowup direction is genuinely injective, using only the internally constructed true shear inverse. -/
theorem actualFormalBlowup_injective (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) : Function.Injective (actualFormalBlowup A e b) := by
  intro F G h
  rw [actualFormalBlowup_eq_zero_comp_centerShear A e he b F,
    actualFormalBlowup_eq_zero_comp_centerShear A e he b G] at h
  have hs := actualFormalBlowup_zero_injective A e h
  exact (actualFormalCenterShearAlgEquiv A e b).injective hs

/-- BOTH whole center-power exceptional-divisibility directions hold in EVERY actual chart direction. -/
theorem mem_coordinate_power_iff_blowup_exceptional_dvd (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F ∈ actualFormalCoordinateIdeal n A ^ d ↔
      (MvPowerSeries.X e)^d ∣ actualFormalBlowup A e b F := by
  rw [actualFormalBlowup_eq_zero_comp_centerShear A e he b F,
    ← mem_coordinate_power_iff_blowup_zero_exceptional_dvd A e he d]
  exact mem_coordinate_power_iff_centerShear A e he b d F

/-- The SAME arbitrary-direction chart reflects the whole actual exceptional principal power to the true center power. -/
theorem comap_exceptional_power_blowup (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (d : ℕ) :
    Ideal.comap (actualFormalBlowup A e b).toRingHom (Ideal.span {(MvPowerSeries.X e)^d})=
      actualFormalCoordinateIdeal n A ^ d := by
  ext F
  change actualFormalBlowup A e b F ∈ Ideal.span {(MvPowerSeries.X e)^d} ↔ _
  exact Ideal.mem_span_singleton.trans (mem_coordinate_power_iff_blowup_exceptional_dvd A e he b d F).symm

/-- True nonzero normalized quotients are supplied INTERNALLY in EVERY actual chart direction. -/
theorem actualNormalizedFormalMember_ne_zero (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) (hne : F ≠ 0) :
    actualNormalizedFormalMember A e he b d F hF ≠ 0 := by
  intro h
  have hs := actualNormalizedFormalMember_spec A e he b d F hF
  rw [h,mul_zero] at hs
  apply hne
  apply actualFormalBlowup_injective A e he b
  simpa using hs.symm

end
end Hironaka.HironakaActualFormalBlowupAllDirections
