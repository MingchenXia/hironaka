/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.CoordinatePlaneDivision

/-!
# Relative Hadamard division in the actual singular cylinder ideal

Actual coordinate perturbations prove density away from each fibre coordinate.
Holomorphic coordinate division therefore preserves the SAME entire original
vanishing ideal. Finite relative Hadamard decomposition retains every quotient
coefficient inside that ideal; no smoothness, coherence or desired pullback
ideal equality is assumed.
Blueprint: `hironaka-actual-cylinder-relative-hadamard-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualCylinderRelativeHadamard
noncomputable section
open Hironaka.HolomorphicIdealSheaves CoordinatePlaneDivision HadamardBridgeAlong
variable {n : ℕ}

/-- Actual coordinate perturbations stay in the same cylinder and approach every point on the coordinate zero set. -/
theorem cylinder_subset_closure_coordinate_complement
    (S : Set (ComplexModel n)) (i : Fin n)
    (hS : ∀ z∈S,∀ a : ℂ,setCoord z i a∈S) :
    S⊆closure (S\{z | z i=0}) := by
  intro z hz
  by_cases hzi : z i=0
  · apply Metric.mem_closure_iff.mpr
    intro ε hε
    let a : ℂ := (ε/2 : ℝ)
    have ha : a≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (half_pos hε))
    refine ⟨setCoord z i a,⟨hS z hz a,?_⟩,?_⟩
    · simpa using ha
    · calc
        dist z (setCoord z i a)=‖setCoord z i a-z‖ := by rw [dist_comm,dist_eq_norm]
        _ ≤ ‖a-z i‖ := norm_setCoord_sub_le z i a
        _ = ε/2 := by simp [a,hzi]; positivity
        _ < ε := by linarith
  · exact subset_closure ⟨hz,hzi⟩

/-- Genuine cylinder density, not an ideal-equality premise, forces each holomorphic quotient to vanish on the SAME set. -/
theorem mem_vanishingIdeal_of_coord_mul
    (S : Set (ComplexModel n)) (i : Fin n)
    (hS : ∀ z∈S,∀ a : ℂ,setCoord z i a∈S)
    {q : ComplexModel n} {H : ComplexModel n → ℂ} (hH : HolomorphicAt n H q)
    (hprod : (vanishingIdeal (n := n) S).mem q (fun z => z i*H z)) :
    (vanishingIdeal (n := n) S).mem q H := by
  have hD := cylinder_subset_closure_coordinate_complement S i hS
  obtain ⟨O,hOsub,hO,hqO⟩ := _root_.mem_nhds_iff.mp (hH.and hprod.2)
  refine ⟨hH,?_⟩
  filter_upwards [hO.mem_nhds hqO] with z hz hzS
  let T : Set (ComplexModel n) := (S\{y | y i=0})∩O
  have hzcl : z∈closure T := by
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨y,hyV,hyS⟩ := mem_closure_iff_nhds.mp (hD hzS) (V∩O)
      (inter_mem hV (hO.mem_nhds hz))
    exact ⟨y,hyV.1,hyS,hyV.2⟩
  have : NeBot (𝓝[T] z) := mem_closure_iff_nhdsWithin_neBot.mp hzcl
  have hzero : ∀ᶠ y in 𝓝[T] z,H y=0 := eventually_nhdsWithin_of_forall fun y hy => by
    have hmul := (hOsub hy.2).2 hy.1.1
    exact (mul_eq_zero.mp hmul).resolve_left hy.1.2
  have hzero' : H =ᶠ[𝓝[T] z] fun _ => 0 := hzero
  have ht0 : Tendsto H (𝓝[T] z) (𝓝 0) := tendsto_const_nhds.congr' hzero'.symm
  have htH : Tendsto H (𝓝[T] z) (𝓝 (H z)) :=
    (hOsub hz).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique htH ht0

/-- One literal coordinate Taylor quotient remains in the SAME actual vanishing ideal. -/
theorem exists_relative_coord_quotient_mem_vanishingIdeal
    (S : Set (ComplexModel n)) (i : Fin n)
    (hS : ∀ z∈S,∀ a : ℂ,setCoord z i a∈S)
    {q : ComplexModel n} (hq : q i=0) {F : ComplexModel n → ℂ}
    (hF : (vanishingIdeal (n := n) S).mem q F) :
    (vanishingIdeal (n := n) S).mem q (fun z => F (setCoord z i 0)) ∧
      ∃ H : ComplexModel n → ℂ,(vanishingIdeal (n := n) S).mem q H ∧
        ∀ᶠ z in 𝓝 q,F z-F (setCoord z i 0)=z i*H z := by
  let P : ComplexModel n → ComplexModel n := fun z => setCoord z i 0
  have hP : Differentiable ℂ P :=
    (differentiable_setCoord i).comp (differentiable_id.prodMk (differentiable_const 0))
  have hPq : P q=q := by simpa only [P,← hq] using setCoord_self q i
  have hnear : Tendsto P (𝓝 q) (𝓝 q) := by
    convert hP.continuous.continuousAt.tendsto using 1
    rw [hPq]
  have hFdiff : ∀ᶠ z in 𝓝 q,DifferentiableAt ℂ F z :=
    hF.1.mono fun _ hz => mdifferentiableAt_iff_differentiableAt.mp hz
  have hF'diff : ∀ᶠ z in 𝓝 q,DifferentiableAt ℂ (F∘P) z := by
    filter_upwards [hnear.eventually hFdiff] with z hz
    exact hz.comp z (hP z)
  have hF' : (vanishingIdeal (n := n) S).mem q (F∘P) := by
    refine ⟨hF'diff.mono (fun _ hz => hz.mdifferentiableAt),?_⟩
    filter_upwards [hnear.eventually hF.2] with z hz hzS
    exact hz (hS z hzS 0)
  have hG : (vanishingIdeal (n := n) S).mem q (fun z => F z-(F∘P) z) := by
    refine ⟨(hFdiff.and hF'diff).mono (fun _ hz => (hz.1.sub hz.2).mdifferentiableAt),?_⟩
    filter_upwards [hF.2,hF'.2] with z hz hz' hzS
    rw [hz hzS,hz' hzS,sub_self]
  obtain ⟨H,hH,heq⟩ := exists_eq_coord_mul (G := fun z => F z-(F∘P) z)
    (hFdiff.and hF'diff |>.mono fun z hz => hz.1.sub hz.2) hq
    (Eventually.of_forall fun z hz => by
      simp only [Function.comp_apply,P,sub_eq_zero]
      rw [← hz,setCoord_self])
  have hHhol : HolomorphicAt n H q := hH.mono fun _ hz => hz.mdifferentiableAt
  have hprod : (vanishingIdeal (n := n) S).mem q (fun z => z i*H z) := by
    have hcoord : HolomorphicAt n (fun z : ComplexModel n => z i) q :=
      Eventually.of_forall fun z => (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt.mdifferentiableAt
    refine ⟨hcoord.mul hHhol,?_⟩
    filter_upwards [heq,hG.2] with z hz hz' hzS
    rw [← hz]
    exact hz' hzS
  exact ⟨hF',H,mem_vanishingIdeal_of_coord_mul S i hS hHhol hprod,heq⟩


/-- Genuine finite Hadamard decomposition with EVERY coefficient in the SAME actual cylinder ideal. -/
theorem exists_sum_coord_mul_mem_vanishingIdeal (r : ℕ) :
    ∀ (k : ℕ),k+r=n → ∀ (S : Set (ComplexModel n)) (F : ComplexModel n → ℂ) (q : ComplexModel n),
      q∈complexCoordinatePlane n k →
      (∀ (i : Fin n),k≤ i.val → ∀ z∈S,∀ a : ℂ,setCoord z i a∈S) →
      (vanishingIdeal (n := n) S).mem q F →
      (∀ᶠ z in 𝓝 q,z∈complexCoordinatePlane n k → F z=0) →
      ∃ H : Fin n → ComplexModel n → ℂ,
        (∀ i : Fin n,i.val<k → H i=0) ∧
        (∀ i,(vanishingIdeal (n := n) S).mem q (H i)) ∧
        ∀ᶠ z in 𝓝 q,F z=∑ i,z i*H i z := by
  induction r with
  | zero =>
    intro k hk S F q _hq _hS _hF hvan
    refine ⟨fun _ _ => 0,fun _ _ => rfl,?_,?_⟩
    · exact fun _ => ⟨holomorphicAt_const 0,Eventually.of_forall fun _ _ => rfl⟩
    · filter_upwards [hvan] with z hz
      have hp : z∈complexCoordinatePlane n k := fun i hi => by have hin:=i.isLt; omega
      simp [hz hp]
  | succ r ih =>
    intro k hk S F q hq hS hF hvan
    have hkn : k<n := by omega
    let i : Fin n := ⟨k,hkn⟩
    have hqi : q i=0 := hq i le_rfl
    obtain ⟨hF',Hk,hHk,hHkeq⟩ := exists_relative_coord_quotient_mem_vanishingIdeal
      S i (hS i le_rfl) hqi hF
    let F' : ComplexModel n → ℂ := fun z => F (setCoord z i 0)
    have hnear : Tendsto (fun z : ComplexModel n => setCoord z i 0) (𝓝 q) (𝓝 q) := by
      rw [Metric.tendsto_nhds_nhds]
      exact fun ε hε => ⟨ε,hε,fun {z} hz => by
        rw [dist_eq_norm] at hz ⊢
        exact (norm_setCoord_zero_sub_le hqi).trans_lt hz⟩
    have hq' : q∈complexCoordinatePlane n (k+1) := fun j hj => hq j (by omega)
    have hvan' : ∀ᶠ z in 𝓝 q,z∈complexCoordinatePlane n (k+1) → F' z=0 := by
      filter_upwards [hnear.eventually hvan] with z hz hmem
      refine hz fun j hj => ?_
      by_cases hji : j=i
      · subst j
        simp
      · simp only [setCoord_apply,hji,if_false]
        exact hmem j (by have hval : j.val≠k := fun h => hji (Fin.ext h); omega)
    obtain ⟨H',hH'0,hH'J,hH'eq⟩ := ih (k+1) (by omega) S F' q hq'
      (fun j hj => hS j (by omega)) hF' hvan'
    refine ⟨Function.update H' i Hk,?_,?_,?_⟩
    · intro j hj
      have hji : j≠i := fun h => by subst j; simp [i] at hj
      rw [Function.update_of_ne hji]
      exact hH'0 j (by omega)
    · intro j
      by_cases hji : j=i
      · subst j
        simpa using hHk
      · simpa [Function.update_of_ne hji] using hH'J j
    · filter_upwards [hHkeq,hH'eq] with z h1 h2
      have hsum : ∑ j,z j*Function.update H' i Hk j z =
          z i*Hk z+∑ j,z j*H' j z := by
        rw [← Finset.add_sum_erase (a := i) _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase (a := i) _ (fun j => z j*H' j z) (Finset.mem_univ i)]
        simp only [Function.update_self]
        rw [hH'0 i (by simp [i]),Pi.zero_apply,mul_zero,zero_add]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hsum,← h1,← h2]
      change F z=(F z-F' z)+F' z
      ring

/-- The literal product carrier, with no geometric regularity assumed for its original base. -/
def cylinderCarrier (k t : ℕ) (W : Set (ComplexModel k)) : Set (ComplexModel (k+t)) :=
  {z | WithLp.toLp 2 (fun i : Fin k => z (i.castAdd t))∈W}

private theorem cylinder_setCoord {k t : ℕ} (W : Set (ComplexModel k))
    (i : Fin (k+t)) (hi : k≤ i.val) (z : ComplexModel (k+t))
    (hz : z∈cylinderCarrier k t W) (a : ℂ) : setCoord z i a∈cylinderCarrier k t W := by
  change WithLp.toLp 2 (fun j : Fin k => setCoord z i a (j.castAdd t))∈W
  have he : WithLp.toLp 2 (fun j : Fin k => setCoord z i a (j.castAdd t))=
      WithLp.toLp 2 (fun j : Fin k => z (j.castAdd t)) := by
    ext j
    have hji : j.castAdd t≠i := by
      intro h
      subst i
      exact (Nat.not_le_of_gt j.isLt) hi
    simp only [setCoord_apply,hji,if_false]
  rw [he]
  exact hz

/-- True relative difference on the literal singular product, with ALL quotients in its original ideal. -/
theorem exists_cylinder_relative_difference (k t : ℕ) (W : Set (ComplexModel k))
    (F : ComplexModel (k+t) → ℂ)
    (hF : (vanishingIdeal (n := k+t) (cylinderCarrier k t W)).mem 0 F) :
    ∃ H : Fin (k+t) → ComplexModel (k+t) → ℂ,
      (∀ i : Fin (k+t),i.val<k → H i=0) ∧
      (∀ i,(vanishingIdeal (n := k+t) (cylinderCarrier k t W)).mem 0 (H i)) ∧
      ∀ᶠ z in 𝓝 0,F z-F (planeRetract k z)=∑ i,z i*H i z := by
  let S := cylinderCarrier k t W
  let P := planeRetract (n := k+t) k
  have hP : Tendsto P (𝓝 0) (𝓝 0) := by simpa using P.continuous.tendsto 0
  have hPS : ∀ z∈S,P z∈S := by
    intro z hz
    change WithLp.toLp 2 (fun i : Fin k => P z (i.castAdd t))∈W
    have he : WithLp.toLp 2 (fun i : Fin k => P z (i.castAdd t))=
        WithLp.toLp 2 (fun i : Fin k => z (i.castAdd t)) := by
      ext i
      simp only [P,planeRetract_apply,Fin.val_castAdd,if_pos i.isLt]
    rw [he]
    exact hz
  have hFdiff : ∀ᶠ z in 𝓝 (0 : ComplexModel (k+t)),DifferentiableAt ℂ F z :=
    hF.1.mono fun _ hz => mdifferentiableAt_iff_differentiableAt.mp hz
  have hF'diff : ∀ᶠ z in 𝓝 (0 : ComplexModel (k+t)),DifferentiableAt ℂ (F∘P) z := by
    filter_upwards [hP.eventually hFdiff] with z hz
    exact hz.comp z P.differentiableAt
  have hF'van : ∀ᶠ z in 𝓝 (0 : ComplexModel (k+t)),z∈S → (F∘P) z=0 := by
    filter_upwards [hP.eventually hF.2] with z hz hzS
    exact hz (hPS z hzS)
  have hG : (vanishingIdeal (n := k+t) S).mem 0 (fun z => F z-(F∘P) z) := by
    refine ⟨(hFdiff.and hF'diff).mono (fun _ hz => (hz.1.sub hz.2).mdifferentiableAt),?_⟩
    filter_upwards [hF.2,hF'van] with z hz hz' hzS
    rw [hz hzS,hz' hzS,sub_self]
  apply exists_sum_coord_mul_mem_vanishingIdeal t k rfl S (fun z => F z-(F∘P) z) 0
  · intro i hi
    rfl
  · exact fun i hi z hz a => cylinder_setCoord W i hi z hz a
  · exact hG
  · exact Eventually.of_forall fun z hz => by
      change F z-F (planeRetract k z)=0
      rw [planeRetract_of_mem hz,sub_self]

end
end Hironaka.HironakaActualCylinderRelativeHadamard
