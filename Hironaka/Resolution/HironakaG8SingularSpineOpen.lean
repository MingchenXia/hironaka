import Hironaka.Resolution.HironakaG8AnalyticSpineCover
import Hironaka.Resolution.HironakaG8FiniteLinearBranchProfile
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Resolution.HironakaActualRegularIntrinsicHSProfile

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SingularSpineOpen
noncomputable section

open Hironaka.HolomorphicIdealSheaves HironakaHolomorphicJetChartInvariance
  HironakaG8VariableCombArrangement HironakaG8AnalyticSpineCover
  HironakaG8FiniteLinearBranchProfile HironakaActualVanishingIntrinsicHSTransport
  HironakaEmbeddedAnalytic HironakaActualRegularIntrinsicHSProfile

private def c (i : Fin 3) : LinearBranch 3 := EuclideanSpace.proj (𝕜 := ℂ) i
private def basis (i : Fin 3) : Ambient := EuclideanSpace.single i 1

private theorem c_basis (i j : Fin 3) : c i (basis j) = if i = j then 1 else 0 := by
  change (EuclideanSpace.single j (1 : ℂ)) i = _
  simp

private def crossing : Set Ambient := {x | x 0 = 0} ∪ {x | x 1 = 0}

private theorem crossing_profile_zero (l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 3) crossing) 0 l =
      Nat.choose (3+l) 3 - (if 2 ≤ l then Nat.choose (3+(l-2)) 3 else 0) := by
  let L : List (LinearBranch 3) := [c 0,c 1]
  have hc (i : Fin 3) : c i ≠ 0 := by
    intro hi
    have h := c_basis i i
    rw [hi,if_pos rfl] at h
    exact zero_ne_one h
  have hN : ∀ a ∈ L, a ≠ 0 := by
    intro a ha
    change a ∈ [c 0,c 1] at ha
    rcases List.mem_cons.mp ha with h | h
    · rw [h]
      exact hc 0
    · have hh : a = c 1 := List.mem_singleton.mp h
      rw [hh]
      exact hc 1
  have hSep : L.Pairwise (fun a b => ∃ z, a z = 0 ∧ b z ≠ 0) := by
    change List.Pairwise _ [c 0,c 1]
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_singleton _ _⟩
    intro a ha
    have hh : a = c 1 := List.mem_singleton.mp ha
    rw [hh]
    exact ⟨basis 1,by simp [c_basis,show (0 : Fin 3) ≠ 1 by decide],by simp [c_basis]⟩
  have he : {z | branchProduct L z = 0} = crossing := by
    ext z
    change z 0 * (z 1 * 1) = 0 ↔ _
    simp [crossing,mul_eq_zero]
  simpa only [he,show L.length = 2 from rfl] using
    origin_profile_of_finite_linear_arrangement L hN hSep l

private def translate (x : Ambient) :
    Ambient ≃ₘ⟮𝓘(ℂ,ComplexModel 3),𝓘(ℂ,ComplexModel 3)⟯ Ambient :=
  { toFun := fun z => z-x
    invFun := fun z => z+x
    left_inv := fun _ => sub_add_cancel _ _
    right_inv := fun _ => add_sub_cancel_right _ _
    contMDiff_toFun := contMDiff_id.sub contMDiff_const
    contMDiff_invFun := contMDiff_id.add contMDiff_const }

private theorem crossing_profile_on_spine (x : Ambient) (hx : x ∈ spine) (l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 3) crossing) x l =
      Nat.choose (3+l) 3 - (if 2 ≤ l then Nat.choose (3+(l-2)) 3 else 0) := by
  have hp : translate x ⁻¹' crossing = crossing := by
    ext z
    change c 0 (z-x) = 0 ∨ c 1 (z-x) = 0 ↔ z 0 = 0 ∨ z 1 = 0
    rw [map_sub,map_sub]
    change z 0 - x 0 = 0 ∨ z 1 - x 1 = 0 ↔ _
    rw [hx.1,hx.2,sub_zero,sub_zero]
  have hh := hilbertSamuelAt_vanishing_actual_biholomorphic_any (translate x) crossing x l
  rw [hp,show translate x x = 0 from sub_self _] at hh
  exact hh.trans (crossing_profile_zero l)

private def noToothWindow : Set Ambient := {x | ‖x 0‖ < 1 ∧ ‖x 2 + 1‖ < 1/2}

private theorem noToothWindow_isOpen : IsOpen noToothWindow := by
  change IsOpen ({x | ‖c 0 x‖ < (1 : ℝ)} ∩ {x | ‖c 2 x + 1‖ < 1/2})
  exact (isOpen_lt (c 0).continuous.norm continuous_const).inter
    (isOpen_lt ((c 2).continuous.add continuous_const).norm continuous_const)

private theorem no_tooth_in_window {x : Ambient} (hx : x ∈ noToothWindow) (j : Tooth) :
    x ∉ toothPlane j := by
  intro hp
  have hBase : (j.1 : ℂ) + 1 = (x 2+1) - slope j * x 0 := by
    change x 2 = (j.1 : ℂ) + slope j * x 0 at hp
    rw [hp]
    ring
  have hLower : 1 ≤ ‖(j.1 : ℂ) + 1‖ := by
    rw [← Nat.cast_succ,Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos j.1
  rw [hBase] at hLower
  have hUpper := norm_sub_le (x 2+1) (slope j * x 0)
  have hProduct : ‖slope j * x 0‖ ≤ (1/4 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (1/4 : ℝ) * 1 := mul_le_mul (slope_norm_le j) hx.1.le (norm_nonneg _) (by norm_num)
      _ = _ := mul_one _
  have hZ : ‖x 2 + 1‖ < (1/2 : ℝ) := hx.2
  linarith

private theorem crossing_inside_window {x : Ambient} (hx : x ∈ noToothWindow) :
    x ∈ comb ↔ x ∈ crossing := by
  constructor
  · rintro (h | h)
    · exact h
    · obtain ⟨j,hj⟩ := mem_iUnion.mp h
      exact (no_tooth_in_window hx j hj).elim
  · exact Or.inl

private theorem comb_profile_inside_window {x : Ambient} (hx : x ∈ noToothWindow) (hSp : x ∈ spine)
    (l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 3) comb) x l =
      Nat.choose (3+l) 3 - (if 2 ≤ l then Nat.choose (3+(l-2)) 3 else 0) := by
  let U : Opens Ambient := ⟨noToothWindow,noToothWindow_isOpen⟩
  let y : U := ⟨x,hx⟩
  have hh : (Subtype.val : U → Ambient) ⁻¹' comb =
      (Subtype.val : U → Ambient) ⁻¹' crossing := by
    ext z
    exact crossing_inside_window z.property
  have ha := hilbertSamuelAt_vanishing_actual_open_any (n := 3) U comb y l
  have hb := hilbertSamuelAt_vanishing_actual_open_any (n := 3) U crossing y l
  rw [hh] at ha
  exact ha.symm.trans (hb.trans (crossing_profile_on_spine x hSp l))

/-- The ordinary double crossing gives a nonempty, genuine open patch
of singular points on the holomorphically parameterized comb spine. -/
theorem exists_singular_open_on_spine :
    ∃ O : Set (ComplexModel 1), IsOpen O ∧ O.Nonempty ∧
      ∀ z ∈ O, spineParameter z ∈ singularSet (n := 3) comb := by
  let O : Set (ComplexModel 1) := {z | ‖z 0 + 1‖ < 1/2}
  have ho : IsOpen O :=
    isOpen_lt (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).continuous.add continuous_const).norm)
      continuous_const
  refine ⟨O,ho,⟨EuclideanSpace.single (0 : Fin 1) (-1 : ℂ),?_⟩,?_⟩
  · change ‖(EuclideanSpace.single (0 : Fin 1) (-1 : ℂ)) 0 + 1‖ < 1/2
    norm_num
  · intro z hz
    let x := spineParameter z
    have h0 : x 0 = 0 := by
      change z 0 * (EuclideanSpace.single (2 : Fin 3) (1 : ℂ)) 0 = 0
      simp [show (0 : Fin 3) ≠ 2 by decide]
    have h1 : x 1 = 0 := by
      change z 0 * (EuclideanSpace.single (2 : Fin 3) (1 : ℂ)) 1 = 0
      simp [show (1 : Fin 3) ≠ 2 by decide]
    have h2 : x 2 = z 0 := by
      change z 0 * (EuclideanSpace.single (2 : Fin 3) (1 : ℂ)) 2 = _
      simp
    have hW : x ∈ noToothWindow := by
      change ‖x 0‖ < 1 ∧ ‖x 2 + 1‖ < 1/2
      rw [h0,h2,norm_zero]
      exact ⟨zero_lt_one,hz⟩
    have hSp : x ∈ spine := ⟨h0,h1⟩
    refine mem_singularSet_iff.mpr ⟨spine_subset_comb hSp,?_⟩
    intro d hd
    have hDepth₁ := hilbertSamuelAt_actual_regular hd.1 hd 1
    rw [comb_profile_inside_window hW hSp,if_neg (by omega),Nat.sub_zero,
      Nat.choose_succ_self_right,Nat.choose_succ_self_right] at hDepth₁
    have hd' : d = 3 := by omega
    subst d
    have hDepth₂ := hilbertSamuelAt_actual_regular hd.1 hd 2
    rw [comb_profile_inside_window hW hSp,if_pos (by decide),Nat.sub_self,add_zero,
      Nat.choose_self] at hDepth₂
    have hp : 0 < Nat.choose (3+2) 3 := Nat.choose_pos (by decide)
    omega

end
end Hironaka.HironakaG8SingularSpineOpen

#print axioms Hironaka.HironakaG8SingularSpineOpen.exists_singular_open_on_spine
