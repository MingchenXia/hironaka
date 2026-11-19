import Hironaka.Resolution.HironakaG8ChronologicalRestartObstruction

/-! # Extra controlled support accumulates at the strict cusp -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CuspRestartNoShrink
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualCoherentWeightedCoefficientMarked BlowupExistenceOriginModel
  HironakaG8ChronologicalRestartObstruction HironakaG8LocalHistory HironakaG11PresLineState
  MarkedIdealBiholomorphism RelativePrincipalizationSpan

set_option maxHeartbeats 1500000 in
/-- Every open chart neighborhood of the strict cusp's point over the
origin contains active controlled points off the actual strict transform.
Shrinking around that point still retains extra controlled support. -/
theorem cusp_extra_controlled_support_in_every_chart_neighborhood
    (U : Opens (ComplexModel 3)) (hU : (0 : ComplexModel 3) ∈ U) :
    let X := CMfd.of (n := 3) (ComplexModel 3)
    let u : X → ℂ := fun z => z 0
    let v : X → ℂ := fun z => z 1
    let w : X → ℂ := fun z => z 2
    let h : X → ℂ := fun z => v z ^ 2 - u z ^ 3
    let B : MarkedIdeal 3 X :=
      ⟨univ, [], finiteFunctionIdeal (fun b : Bool => if b then w else (fun z => u z * h z)), 1⟩
    ∃ y : X, y ∈ U ∧ u y = 0 ∧ y ∈ B.cosupp ∧
      originMk 0 y ∉ closure (originProj ⁻¹' {z : X | w z = 0 ∧ v z ^ 2 - u z ^ 5 = 0} \
        originProj ⁻¹' ({0} : Set X)) := by
  intro X u v w h B
  let a : ℂ → ComplexModel 3 := fun t => t • PiLp.single 2 (1 : Fin 3) (1 : ℂ)
  have ha : Continuous a := continuous_id.smul continuous_const
  have ha0 : a 0 = 0 := zero_smul _ _
  obtain ⟨t,htU,ht⟩ := mem_closure_iff.mp ((dense_compl_singleton (0 : ℂ)) 0)
    (a ⁻¹' (U : Set (ComplexModel 3))) (U.isOpen.preimage ha) (show a 0 ∈ U by rwa [ha0])
  let y : X := a t
  have huy : u y = 0 := by simp [u,y,a,show (0 : Fin 3) ≠ 1 by decide]
  have hvy : v y = t := by simp [v,y,a]
  have hwy : w y = 0 := by simp [w,y,a,show (2 : Fin 3) ≠ 1 by decide]
  have hhy : h y ≠ 0 := by
    have hnt : t ≠ 0 := fun ht' => ht (mem_singleton_iff.mpr ht')
    simpa [h,huy,hvy] using (pow_ne_zero 2 hnt)
  have hHol (i : Fin 3) (x : X) : HolomorphicAt 3 (fun z : X => z i) x :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.mdifferentiableAt
  have hhh : HolomorphicAt 3 h y := (hHol 1 y).mono fun _ hy =>
    (hy.pow 2).sub (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiableAt.mdifferentiableAt).pow 3)
  have hActive := (controlled_chart_has_extra_active_point B w u h y rfl rfl rfl
    (hHol 2 y) (hHol 0 y) hhh hwy huy hhy).1
  refine ⟨y,htU,huy,hActive,?_⟩
  have hEquation := (embedded_cusp_origin_chart_extra_controlled_support).1
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
  have hzEq : v (originProj (originMk 0 z)) ^ 2 - u (originProj (originMk 0 z)) ^ 5 = 0 := by
    rw [hzr]
    exact hrA.1.2
  have hzFact : u z * (u z * h z) = 0 := ((hEquation z).2).symm.trans hzEq
  exact hrN.2 (mem_singleton_iff.mpr ((mul_eq_zero.mp ((mul_eq_zero.mp hzFact).resolve_left hzU)).resolve_left hzU))

set_option maxHeartbeats 1500000 in
/-- On each such open, a fresh strict-transform HS record is impossible as
a local weak class representative of the entire divided controlled record. -/
theorem cusp_controlled_not_fresh_native_on_any_chart_neighborhood
    (U : Opens (ComplexModel 3)) (hU : (0 : ComplexModel 3) ∈ U) :
    let X := CMfd.of (n := 3) (ComplexModel 3)
    let u : X → ℂ := fun z => z 0
    let v : X → ℂ := fun z => z 1
    let w : X → ℂ := fun z => z 2
    let h : X → ℂ := fun z => v z ^ 2 - u z ^ 3
    let B : MarkedIdeal 3 X :=
      ⟨univ, [], finiteFunctionIdeal (fun b : Bool => if b then w else (fun z => u z * h z)), 1⟩
    let A : Set X := originMk 0 ⁻¹' closure
      (originProj ⁻¹' {z : X | w z = 0 ∧ v z ^ 2 - u z ^ 5 = 0} \
        originProj ⁻¹' ({0} : Set X))
    ∀ (Q : MarkedIdeal 3 (CMfd.of (n := 3) U)) (H : ℕ → ℕ),
      NativeHSState Q ((Subtype.val : U → X) ⁻¹' A) H →
      ¬ LocWPEquiv (MarkedIdeal.pullback (Subtype.val : U → X) B) Q := by
  intro X u v w h B A Q H hQ
  obtain ⟨y,hy,_,hActive,hStrict⟩ :=
    cusp_extra_controlled_support_in_every_chart_neighborhood U hU
  have hCoord (i : Fin 3) : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ)
      (fun z : X => z i) := (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.mdifferentiable
  have hGen (b : Bool) : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ)
      ((fun b : Bool => if b then w else (fun z => u z * h z)) b) := by
    cases b
    · change MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ) (fun z : X => u z * h z)
      have hh : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ) h := by
        intro x
        exact ((hCoord 1 x).pow 2).sub ((hCoord 0 x).pow 3)
      intro x
      exact (hCoord 0 x).mul (hh x)
    · simpa [w] using hCoord 2
  have hCoh : B.ideal.IsCoherent := isCoherent_finiteFunctionIdeal _ hGen
  have hCos := MarkedIdealRestrictOpen.cosupp_pullback_val B
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCoh hg) U
  let z : U := ⟨y,hy⟩
  have hz : z ∈ (MarkedIdeal.pullback (Subtype.val : U → X) B).cosupp := hCos.symm ▸ hActive
  exact not_locWPEquiv_fresh_native_of_active_off_strict hQ hz hStrict

end
end Hironaka.HironakaG8CuspRestartNoShrink
