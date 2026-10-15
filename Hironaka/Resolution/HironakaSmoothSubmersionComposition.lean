/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionNormalCrossings
import Hironaka.Analytic.HolomorphicAnalytic
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionComposition
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates BlowupTowers
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionMonomialOrdering
noncomputable section

section Coordinates
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (x : X)

def centeredCoordinates : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) where
  source := (chartAt (ComplexModel n) x).target
  target := (fun w => w + chartAt (ComplexModel n) x x) ⁻¹' (chartAt (ComplexModel n) x).target
  isOpen_source := (chartAt (ComplexModel n) x).open_target
  isOpen_target := (chartAt (ComplexModel n) x).open_target.preimage (continuous_id.add continuous_const)
  center_mem_source := (chartAt (ComplexModel n) x).map_source (mem_chart_source _ x)
  toFun := fun w => w - chartAt (ComplexModel n) x x
  invFun := fun w => w + chartAt (ComplexModel n) x x
  toFun_holomorphic := (differentiable_id.sub_const _).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const _).differentiableOn
  mapsTo_toFun := fun w hw => by
    change w - chartAt (ComplexModel n) x x + chartAt (ComplexModel n) x x ∈
      (chartAt (ComplexModel n) x).target
    simpa using hw
  mapsTo_invFun := fun _ hw => hw
  left_inv := fun _ _ => sub_add_cancel _ _
  right_inv := fun _ _ => add_sub_cancel_right _ _

omit [IsComplexManifold n X] in
theorem centeredCoordinates_source :
    (centeredCoordinates x).source ⊆ (chartAt (ComplexModel n) x).target := subset_rfl

omit [IsComplexManifold n X] in
theorem centeredCoordinates_zero :
    (centeredCoordinates x).toFun (chartAt (ComplexModel n) x x) = 0 := sub_self _

def holomorphicChart
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    OpenPartialHomeomorph X (ComplexModel n) :=
  (chartAt (ComplexModel n) x).trans Φ.toOpenPartialHomeomorph

theorem holomorphicChart_mem_maximalAtlas
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    holomorphicChart x Φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ X := by
  have hΦ : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ.toFun Φ.source :=
    ((HolomorphicAnalytic.analyticOnNhd_of_differentiableOn Φ.isOpen_source
      Φ.toFun_holomorphic).contDiffOn Φ.isOpen_source.uniqueDiffOn).contMDiffOn
  have hΦi : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ.invFun Φ.target :=
    ((HolomorphicAnalytic.analyticOnNhd_of_differentiableOn Φ.isOpen_target
      Φ.invFun_holomorphic).contDiffOn Φ.isOpen_target.uniqueDiffOn).contMDiffOn
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact hΦ.comp ((contMDiffOn_chart (n := ∞)).mono inter_subset_left) (fun _ hz => hz.2)
  · exact (contMDiffOn_chart_symm (n := ∞)).comp
      (hΦi.mono inter_subset_left) (fun w hw => hsrc (Φ.mapsTo_invFun hw.1))
end Coordinates

section Composites
variable {n r s : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)}
  {Z : CMfd.{u} ((n+r)+s)} {f : Y → X} {h : Z → Y} {z : Z}

theorem submersionAt_composition_add
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f (h z))
    (hh : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel ((n+r)+s))
      𝓘(ℂ, ComplexModel (n+r)) ∞ h z) :
    Manifold.IsSubmersionAtOfComplement (ComplexModel r × ComplexModel s)
      𝓘(ℂ, ComplexModel ((n+r)+s)) 𝓘(ℂ, ComplexModel n) ∞ (f ∘ h) z := by
  let Φ := centeredCoordinates (n := n) (f (h z))
  let Ψ := liftedCoordinatesAdd hf Φ (centeredCoordinates_zero _)
  have hdΨ := liftedCoordinatesAdd_dictionary hf Φ (centeredCoordinates_zero _)
  let Ω := liftedCoordinatesAdd hh Ψ hdΨ.2.1
  have hdΩ := liftedCoordinatesAdd_dictionary hh Ψ hdΨ.2.1
  let E₁ : ComplexModel ((n+r)+s) ≃L[ℂ] (ComplexModel (n+r) × ComplexModel s) :=
    EuclideanSpace.finAddEquivProd.toContinuousLinearEquiv
  let E₂ : ComplexModel (n+r) ≃L[ℂ] (ComplexModel n × ComplexModel r) :=
    EuclideanSpace.finAddEquivProd.toContinuousLinearEquiv
  let E := (E₁.trans (ContinuousLinearEquiv.prodCongr E₂ (.refl ℂ (ComplexModel s)))).trans
    (ContinuousLinearEquiv.prodAssoc ℂ (ComplexModel n) (ComplexModel r) (ComplexModel s))
  let a := holomorphicChart z Ω
  let b := holomorphicChart (f (h z)) Φ
  have haz : z ∈ a.source := mem_flatDomain_self Ω
  have hbz : (f ∘ h) z ∈ b.source := mem_flatDomain_self Φ
  have hdom (w : Z) (hw : w ∈ a.source) :
      h w ∈ flatDomain Ψ ∧ f (h w) ∈ flatDomain Φ :=
    ⟨(hdΩ.2.2 w hw).1,(hdΨ.2.2 (h w) (hdΩ.2.2 w hw).1).1⟩
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts E a b haz hbz
    (holomorphicChart_mem_maximalAtlas z Ω hdΩ.1)
    (holomorphicChart_mem_maximalAtlas (f (h z)) Φ (centeredCoordinates_source _))
  · intro w hw
    exact (hdom w hw).2
  · intro v hv
    have hv' : v ∈ a.target := by simpa only [mfld_simps] using hv
    have hw : a.symm v ∈ a.source := a.map_target hv'
    have hhdom := hdom (a.symm v) hw
    have had : a (a.symm v) = v := a.right_inv hv'
    have he (j : Fin n) : (E v).1 j = v (Fin.castAdd s (Fin.castAdd r j)) := by
      simp [E,E₁,E₂,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
        LinearIsometryEquiv.piLpCongrLeft_apply]
    change b ((f ∘ h) (a.symm v)) = (E v).1
    ext j
    rw [he]
    exact (((hdΩ.2.2 (a.symm v) hw).2 (Fin.castAdd r j)).trans
      ((hdΨ.2.2 (h (a.symm v)) hhdom.1).2 j)).symm.trans
      (congrArg (fun w : ComplexModel ((n+r)+s) => w (Fin.castAdd s (Fin.castAdd r j))) had)
end Composites

theorem isSubmersionAt_composition {n m ℓ : ℕ} {X : CMfd.{u} n}
    {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ} {f : Y → X} {h : Z → Y} {z : Z}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f (h z))
    (hh : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h z) :
    Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ (f ∘ h) z := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt hf)
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt hh)
  exact (submersionAt_composition_add hf hh).isSubmersionAt

theorem isSubmersion_composition {n m ℓ : ℕ} {X : CMfd.{u} n}
    {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ} {f : Y → X} {h : Z → Y}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ (f ∘ h) := by
  by_cases hZ : Nonempty Z
  · obtain ⟨z⟩ := hZ
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt (hf.isSubmersionAt (h z)))
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt (hh.isSubmersionAt z))
    apply Manifold.IsSubmersionOfComplement.isSubmersion (F := ComplexModel r × ComplexModel s)
    intro w
    exact submersionAt_composition_add (hf.isSubmersionAt (h w)) (hh.isSubmersionAt w)
  · have : IsEmpty Z := not_nonempty_iff.mp hZ
    apply Manifold.IsSubmersionOfComplement.isSubmersion (F := ComplexModel 0)
    intro z
    exact (IsEmpty.false z).elim

end
end Hironaka.HironakaSmoothSubmersionComposition
