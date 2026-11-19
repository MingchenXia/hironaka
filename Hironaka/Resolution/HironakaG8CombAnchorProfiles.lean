import Hironaka.Resolution.HironakaG8CombExactLocalArrangement
import Hironaka.Resolution.HironakaG8FiniteLinearBranchProfile
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Mathlib.Data.List.FinRange
import Hironaka.Resolution.HironakaActualRegularIntrinsicHSProfile

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CombAnchorProfiles
noncomputable section

open Hironaka.HolomorphicIdealSheaves HironakaHolomorphicJetChartInvariance
  HironakaG8VariableCombArrangement HironakaG8CombExactLocalArrangement
  HironakaG8FiniteLinearBranchProfile HironakaActualVanishingIntrinsicHSTransport

private def coord (i : Fin 3) : LinearBranch 3 := EuclideanSpace.proj (𝕜 := ℂ) i
private def unit (i : Fin 3) : Ambient := EuclideanSpace.single i 1
private def moving (j : Tooth) : LinearBranch 3 := coord 2 - slope j • coord 0

private theorem coord_unit (i j : Fin 3) : coord i (unit j) = if i = j then 1 else 0 := by
  change (EuclideanSpace.single j (1 : ℂ)) i = _
  simp

private theorem moving_apply (j : Tooth) (z : Ambient) :
    moving j z = z 2 - slope j * z 0 := rfl

private theorem moving_unit_two (j : Tooth) : moving j (unit 2) = 1 := by
  change coord 2 (unit 2) - slope j * coord 0 (unit 2) = _
  simp [coord_unit,show (0 : Fin 3) ≠ 2 by decide]

private theorem moving_unit_zero (j : Tooth) : moving j (unit 0) = -slope j := by
  change coord 2 (unit 0) - slope j * coord 0 (unit 0) = _
  simp [coord_unit,show (2 : Fin 3) ≠ 0 by decide]

private def branches (k : ℕ) : List (LinearBranch 3) :=
  coord 0 :: coord 1 :: (List.finRange (k+1)).map (fun j => moving ⟨k,j⟩)

private theorem branches_nonzero (k : ℕ) : ∀ a ∈ branches k, a ≠ 0 := by
  intro a ha hn
  have zz (i : Fin 3) : a (unit i) = 0 := by rw [hn]; rfl
  simp only [branches,List.mem_cons,List.mem_map] at ha
  rcases ha with h | h | ⟨j,_,h⟩
  · have hz := zz 0
    rw [h] at hz
    exact one_ne_zero (((coord_unit (0 : Fin 3) 0).trans (if_pos rfl)).symm.trans hz)
  · have hz := zz 1
    rw [h] at hz
    exact one_ne_zero (((coord_unit (1 : Fin 3) 1).trans (if_pos rfl)).symm.trans hz)
  · have hz := zz 2
    rw [← h] at hz
    exact one_ne_zero (by simpa only [moving_unit_two] using hz)

private theorem branches_separate (k : ℕ) :
    (branches k).Pairwise (fun a b => ∃ z, a z = 0 ∧ b z ≠ 0) := by
  simp only [branches,List.pairwise_cons,List.mem_cons,List.mem_map]
  refine ⟨?_,?_,?_⟩
  · rintro b (rfl | ⟨j,_,rfl⟩)
    · exact ⟨unit 1,by simp [coord_unit,show (0 : Fin 3) ≠ 1 by decide],by simp [coord_unit]⟩
    · exact ⟨unit 2,by simp [coord_unit,show (0 : Fin 3) ≠ 2 by decide],by simp [moving_unit_two]⟩
  · rintro b ⟨j,_,rfl⟩
    exact ⟨unit 2,by simp [coord_unit,show (1 : Fin 3) ≠ 2 by decide],by simp [moving_unit_two]⟩
  · rw [List.pairwise_map]
    have hp := List.nodup_finRange (k+1)
    apply hp.imp
    intro i j hij
    let z : Ambient := unit 0 + slope ⟨k,i⟩ • unit 2
    have hz (a : Fin (k+1)) : moving ⟨k,a⟩ z = slope ⟨k,i⟩ - slope ⟨k,a⟩ := by
      simp [z,map_add,map_smul,moving_unit_zero,moving_unit_two,sub_eq_add_neg,add_comm]
    refine ⟨z,by rw [hz,sub_self],?_⟩
    rw [hz,sub_ne_zero]
    exact fun h => hij (slope_injective_at k h)

private def translation (k : ℕ) :
    Ambient ≃ₘ⟮𝓘(ℂ,ComplexModel 3),𝓘(ℂ,ComplexModel 3)⟯ Ambient :=
  { toFun := fun z => z - anchor k
    invFun := fun z => z + anchor k
    left_inv := by intro z; exact sub_add_cancel _ _
    right_inv := by intro z; exact add_sub_cancel_right _ _
    contMDiff_toFun := contMDiff_id.sub contMDiff_const
    contMDiff_invFun := contMDiff_id.add contMDiff_const }

private theorem translation_zero (k : ℕ) : translation k (anchor k) = 0 := sub_self _

private theorem translated_equation (k : ℕ) :
    (translation k) ⁻¹' {z | branchProduct (branches k) z = 0} =
      {z : Ambient | z 0 = 0} ∪ {z | z 1 = 0} ∪ ⋃ j : Fin (k+1), toothPlane ⟨k,j⟩ := by
  ext z
  obtain ⟨ha0,ha1,ha2⟩ := anchor_coords k
  have h0 : (translation k z) 0 = z 0 := by
    change coord 0 (z - anchor k) = coord 0 z
    rw [map_sub]
    change z 0 - anchor k 0 = z 0
    rw [ha0,sub_zero]
  have h1 : (translation k z) 1 = z 1 := by
    change coord 1 (z - anchor k) = coord 1 z
    rw [map_sub]
    change z 1 - anchor k 1 = z 1
    rw [ha1,sub_zero]
  have h2 : (translation k z) 2 = z 2 - (k : ℂ) := by
    change coord 2 (z - anchor k) = coord 2 z - (k : ℂ)
    rw [map_sub]
    change z 2 - anchor k 2 = z 2 - (k : ℂ)
    rw [ha2]
  change branchProduct (branches k) (translation k z) = 0 ↔ _
  rw [branchProduct_eq_zero_iff]
  simp only [branches,List.mem_cons,List.mem_map,Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a,rfl | rfl | ⟨j,_,rfl⟩,ha⟩
    · exact Or.inl (Or.inl (h0.symm ▸ ha))
    · exact Or.inl (Or.inr (h1.symm ▸ ha))
    · rw [moving_apply,h0,h2,sub_eq_zero] at ha
      exact Or.inr ⟨j,by
        change z 2 = (k : ℂ) + slope ⟨k,j⟩ * z 0
        linear_combination ha⟩
  · rintro ((ha | ha) | ⟨j,ha⟩)
    · exact ⟨coord 0,Or.inl rfl,by change (translation k z) 0 = 0; rwa [h0]⟩
    · exact ⟨coord 1,Or.inr (Or.inl rfl),by change (translation k z) 1 = 0; rwa [h1]⟩
    · refine ⟨moving ⟨k,j⟩,Or.inr (Or.inr ⟨j,by simp,rfl⟩),?_⟩
      rw [moving_apply,h0,h2]
      change z 2 = (k : ℂ) + slope ⟨k,j⟩ * z 0 at ha
      linear_combination ha

/-- The exact original reduced profile grows with the level of the tooth. -/
theorem comb_anchor_profile (k l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 3) comb) (anchor k) l =
      Nat.choose (3+l) 3 - (if k+3 ≤ l then Nat.choose (3+(l-(k+3))) 3 else 0) := by
  let A := {z : Ambient | branchProduct (branches k) z = 0}
  let U : Opens Ambient := ⟨toothWindow k,toothWindow_isOpen k⟩
  let x : U := ⟨anchor k,anchor_mem_window k⟩
  have hSame : (Subtype.val : U → Ambient) ⁻¹' comb =
      (Subtype.val : U → Ambient) ⁻¹' ((translation k) ⁻¹' A) := by
    ext z
    have hZ := Set.ext_iff.mp (comb_exact_window k) z.val
    rw [← translated_equation k] at hZ
    exact ⟨fun h => (hZ.mp ⟨h,z.property⟩).1,fun h => (hZ.mpr ⟨h,z.property⟩).1⟩
  have hs := hilbertSamuelAt_vanishing_actual_open_any (n := 3) U comb x l
  have ht := hilbertSamuelAt_vanishing_actual_open_any (n := 3) U ((translation k) ⁻¹' A) x l
  rw [hSame] at hs
  change _ = hilbertSamuelAt (vanishingIdeal (n := 3) comb) (anchor k) l at hs
  rw [← hs,ht]
  change hilbertSamuelAt (vanishingIdeal (n := 3) ((translation k) ⁻¹' A)) (anchor k) l = _
  rw [hilbertSamuelAt_vanishing_actual_biholomorphic_any,translation_zero]
  have hh := origin_profile_of_finite_linear_arrangement (branches k)
    (branches_nonzero k) (branches_separate k) l
  have hLen : (branches k).length = k+3 := by simp [branches]
  simpa only [hLen] using hh

/-- The actual reduced anchor profiles form a strictly increasing
sequence in the Hilbert–Samuel order used by the native phases. -/
theorem comb_anchor_profile_strictMono :
    StrictMono (fun k => toLex (hilbertSamuelAt (vanishingIdeal (n := 3) comb) (anchor k))) := by
  intro k m hkm
  refine ⟨k+3,?_,?_⟩
  · intro l hl
    change hilbertSamuelAt (vanishingIdeal (n := 3) comb) (anchor k) l =
      hilbertSamuelAt (vanishingIdeal (n := 3) comb) (anchor m) l
    rw [comb_anchor_profile,comb_anchor_profile,if_neg (by omega),if_neg (by omega)]
  · change hilbertSamuelAt (vanishingIdeal (n := 3) comb) (anchor k) (k+3) <
      hilbertSamuelAt (vanishingIdeal (n := 3) comb) (anchor m) (k+3)
    rw [comb_anchor_profile,comb_anchor_profile,if_pos le_rfl,if_neg (by omega)]
    simp only [Nat.sub_self,add_zero,Nat.choose_self,Nat.sub_zero]
    have hh : 0 < Nat.choose (3+(k+3)) 3 := Nat.choose_pos (by omega)
    omega

open HironakaEmbeddedAnalytic HironakaActualRegularIntrinsicHSProfile

/-- Every anchor is singular for the actual reduced comb. -/
theorem anchor_mem_singularSet (k : ℕ) : anchor k ∈ singularSet (n := 3) comb := by
  apply mem_singularSet_iff.mpr
  have hMem : anchor k ∈ spine := ⟨(anchor_coords k).1,(anchor_coords k).2.1⟩
  refine ⟨spine_subset_comb hMem,?_⟩
  intro d hreg
  have h₁ := hilbertSamuelAt_actual_regular hreg.1 hreg 1
  rw [comb_anchor_profile,if_neg (by omega),Nat.sub_zero,Nat.choose_succ_self_right,
    Nat.choose_succ_self_right] at h₁
  have hd : d = 3 := by omega
  subst d
  have h₂ := hilbertSamuelAt_actual_regular hreg.1 hreg (k+3)
  rw [comb_anchor_profile,if_pos le_rfl,Nat.sub_self,add_zero,Nat.choose_self] at h₂
  have hPos : 0 < Nat.choose (3+(k+3)) 3 := Nat.choose_pos (by omega)
  omega

end
end Hironaka.HironakaG8CombAnchorProfiles

#print axioms Hironaka.HironakaG8CombAnchorProfiles.comb_anchor_profile_strictMono

#print axioms Hironaka.HironakaG8CombAnchorProfiles.anchor_mem_singularSet
