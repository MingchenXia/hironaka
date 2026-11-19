import Hironaka.Resolution.HironakaG8ActualHighestProfileRestart
import Hironaka.Resolution.HironakaG8WholeMarkOnePrefixCriterion
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked
import Hironaka.Blowup.BlowupExistenceOriginModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8ChronologicalRestartObstruction
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaActualCoherentWeightedCoefficientMarked GermIdealOrder
  CanonicalCentres GeneralValue NonmonomialOrderLocal ResolutionDriver BlowupExistenceOriginModel
  HironakaG8LocalHistory HironakaG11PresLineState HironakaActualHistoricalOriginalSingularReference
  HironakaEmbeddedAnalytic

/-- An actual chronological canonical first centre must dominate every
active competitor of the original advanced record, even a competitor
outside the selected strict-profile atlas. -/
theorem not_canonical_restart_step_of_higher_residual_competitor
    {n : ℕ} {X Y Z : CMfd.{0} (n+1)}
    (M : MarkedIdeal (n+1) X) (P : BlowupTower X Y)
    {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong (n+1) C π)
    {x y : Y} (hx : x ∈ C) (hy : y ∈ (geoTransformAlong M P).cosupp)
    (hHigher : nmOrd (geoTransformAlong M P) x < nmOrd (geoTransformAlong M P) y) :
    ¬ IsCanonical M ((canonicalInvariant (n+1)).inv M) (.step P C π hπ) := by
  intro hCan
  rcases hCan.2 with hEmpty | hMax
  · simp [hEmpty] at hx
  · have hxMax : x ∈ maxLocus ((canonicalInvariant (n+1)).inv M P) (geoTransformAlong M P).cosupp :=
      hMax ▸ hx
    exact (not_lt_of_ge (hxMax.2 y hy)) (genInv_lt_of_nmOrd_lt _ M hHigher)

/-- At mark one a divided controlled family can have extra support on the
exceptional hypersurface. A chart on which one generator retains an
exceptional factor therefore cannot identify its active set with that of
the strict family merely by removing the common exceptional factor. -/
theorem controlled_chart_has_extra_active_point
    {n : ℕ} {Y : CMfd.{0} n} (B : MarkedIdeal n Y)
    (g u h : Y → ℂ) (y : Y)
    (hB : B.N = univ) (hMark : B.d = 1)
    (hIdeal : B.ideal = finiteFunctionIdeal (fun b : Bool => if b then g else (fun z => u z * h z)))
    (hg : HolomorphicAt n g y) (hu : HolomorphicAt n u y) (hh : HolomorphicAt n h y)
    (hgy : g y = 0) (huy : u y = 0) (hhy : h y ≠ 0) :
    y ∈ B.cosupp ∧
      y ∉ cosupport n univ (finiteFunctionIdeal (fun b : Bool => if b then g else h)) 1 := by
  have hControlled (b : Bool) : HolomorphicAt n ((fun b : Bool => if b then g else (fun z => u z * h z)) b) y := by
    cases b
    · simpa using hu.mul hh
    · simpa using hg
  have hStrict (b : Bool) : HolomorphicAt n ((fun b : Bool => if b then g else h) b) y := by
    cases b
    · simpa using hh
    · simpa using hg
  refine ⟨?_,?_⟩
  · change y ∈ cosupport n B.N B.ideal B.d
    rw [hB,hIdeal,hMark,mem_cosupport_finiteFunctionIdeal_iff _ _ _ hControlled]
    intro b
    apply (vanishesToOrderOn_one_iff (mem_univ y) (hControlled b)).mpr
    cases b <;> simp [hgy,huy]
  · rw [mem_cosupport_finiteFunctionIdeal_iff _ _ _ hStrict]
    intro hZero
    exact hhy ((vanishesToOrderOn_one_iff (mem_univ y) (hStrict false)).mp (hZero false))

/-- A single active point outside the strict transform rules out ordinary
local weak equivalence between the whole advanced record and any fresh
native record selected from that strict transform. -/
theorem not_locWPEquiv_fresh_native_of_active_off_strict
    {n : ℕ} {Y : CMfd.{0} n} {B Q : MarkedIdeal n Y} {W : Set Y} {H : ℕ → ℕ}
    (hNative : NativeHSState Q W H) {y : Y} (hy : y ∈ B.cosupp) (hyW : y ∉ W) :
    ¬ LocWPEquiv B Q := by
  intro hClass
  have hyQ : y ∈ Q.cosupp := hClass.cosupp_eq_base ▸ hy
  obtain ⟨m,X₀,W₀,a,hW₀,ha,hH⟩ := hNative.1
  rw [hNative.cosupp_eq,← hH] at hyQ
  have hyS := actual_original_singular_profile_locus_subset_current_singular
    W₀ hW₀ a ha W hNative.2.1 hyQ
  exact hyW (singularSet_subset W hyS)

/-- The actual origin-blowup chart pulls back the two cusp equations to
`u*w` and `u²*(v²-u³)`. The divided mark-one family has an extra active
exceptional point relative to the family obtained by saturation. -/
theorem embedded_cusp_origin_chart_extra_controlled_support :
    let X := CMfd.of (n := 3) (ComplexModel 3)
    let u : X → ℂ := fun z => z 0
    let v : X → ℂ := fun z => z 1
    let w : X → ℂ := fun z => z 2
    let h : X → ℂ := fun z => v z ^ 2 - u z ^ 3
    let p : X → X := fun z => originProj (originMk 0 z)
    let B : MarkedIdeal 3 X :=
      ⟨univ, [], finiteFunctionIdeal (fun b : Bool => if b then w else (fun z => u z * h z)), 1⟩
    (∀ z, w (p z) = u z * w z ∧
      v (p z) ^ 2 - u (p z) ^ 5 = u z * (u z * h z)) ∧
    ∃ y : X, u y = 0 ∧ h y ≠ 0 ∧ y ∈ B.cosupp ∧
      y ∉ cosupport 3 univ (finiteFunctionIdeal (fun b : Bool => if b then w else h)) 1 ∧
      originMk 0 y ∉ closure (originProj ⁻¹' {z : X | w z = 0 ∧ v z ^ 2 - u z ^ 5 = 0} \
        originProj ⁻¹' ({0} : Set X)) := by
  intro X u v w h p B
  have hProj (z : X) (i : Fin 3) :
      p z i = z 0 * (if i = 0 then 1 else z i) := by
    change (z 0 • gen 0 z : ComplexModel 3) i = _
    rfl
  have hU (z : X) : u (p z) = u z := by
    exact (hProj z 0).trans (by simp [u])
  have hV (z : X) : v (p z) = u z * v z := by
    exact (hProj z 1).trans (by norm_num [u,v])
  have hW (z : X) : w (p z) = u z * w z := by
    exact (hProj z 2).trans (by simp [u,w,show (2 : Fin 3) ≠ 0 by decide])
  have hEquation (z : X) : v (p z) ^ 2 - u (p z) ^ 5 = u z * (u z * h z) := by
    rw [hU,hV]
    dsimp [h]
    ring
  refine ⟨fun z => ⟨hW z,hEquation z⟩,?_⟩
  let y : X := PiLp.single 2 (1 : Fin 3) (1 : ℂ)
  have huy : u y = 0 := by norm_num [u,y,PiLp.single_apply]
  have hvy : v y = 1 := by norm_num [v,y,PiLp.single_apply]
  have hwy : w y = 0 := by simp [w,y,show (2 : Fin 3) ≠ 1 by decide]
  have hhy : h y ≠ 0 := by simp [h,huy,hvy]
  have hHol (i : Fin 3) (x : X) : HolomorphicAt 3 (fun z : X => z i) x :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.mdifferentiableAt
  have hhh : HolomorphicAt 3 h y := (hHol 1 y).mono fun _ hy =>
    (hy.pow 2).sub (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiableAt.mdifferentiableAt).pow 3)
  obtain ⟨ha,hna⟩ := controlled_chart_has_extra_active_point B w u h y rfl rfl rfl
    (hHol 2 y) (hHol 0 y) hhh hwy huy hhy
  refine ⟨y,huy,hhy,ha,hna,?_⟩
  have hCont (i : Fin 3) : Continuous (fun z : X => z i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).continuous
  have hHCont : Continuous h := ((hCont 1).pow 2).sub ((hCont 0).pow 3)
  let N : Set (OriginBlowup 3) := originSource 0 ∩ originCoord 0 ⁻¹' ({0}ᶜ : Set ℂ).preimage h
  have hN : IsOpen N := (continuousOn_originCoord 0).isOpen_inter_preimage
    (isOpen_originSource 0) (hHCont.isOpen_preimage _ (isClosed_singleton.isOpen_compl))
  have hyN : originMk 0 y ∈ N := ⟨originMk_mem_originSource 0 y, by
    change h (originCoord 0 (originMk 0 y)) ∉ ({0} : Set ℂ)
    rw [originCoord_originMk]
    exact fun hb => hhy (mem_singleton_iff.mp hb)⟩
  intro hNear
  obtain ⟨r,hrN,hrA⟩ := mem_closure_iff.mp hNear N hN hyN
  let z : X := originCoord 0 r
  have hzr : originMk 0 z = r := originMk_originCoord hrN.1
  have hzU : u z ≠ 0 := by
    intro hz
    apply hrA.2
    change originProj r = 0
    rw [← hzr]
    change (z 0 • gen 0 z : ComplexModel 3) = 0
    change z 0 = 0 at hz
    rw [hz,zero_smul]
  have hzEq : v (p z) ^ 2 - u (p z) ^ 5 = 0 := by
    change v (originProj (originMk 0 z)) ^ 2 - u (originProj (originMk 0 z)) ^ 5 = 0
    rw [hzr]
    exact hrA.1.2
  rw [hEquation] at hzEq
  exact hrN.2 (mem_singleton_iff.mpr ((mul_eq_zero.mp ((mul_eq_zero.mp hzEq).resolve_left hzU)).resolve_left hzU))

end
end Hironaka.HironakaG8ChronologicalRestartObstruction
