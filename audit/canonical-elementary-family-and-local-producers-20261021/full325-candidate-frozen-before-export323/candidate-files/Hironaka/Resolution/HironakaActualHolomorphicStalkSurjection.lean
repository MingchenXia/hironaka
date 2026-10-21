/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicLifting

/-!
# Actual native holomorphic stalk surjections produce genuine local left inverses

Original coordinate germs are lifted through the independently constructed
native stalk map. True colimit equalities and finite original coordinate
assembly produce a literal local holomorphic left inverse; its actual
coordinate derivative is then injective by the complex chain rule.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHolomorphicStalkSurjection
noncomputable section
open HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspaceIntrinsicLifting
variable {d n : ℕ} {O : Opens (ComplexModel d)} {V : Opens (ComplexModel n)}
  {f : O → V}

/-- Surjectivity of the ACTUAL native stalk map lifts each original coordinate to a real target function. -/
theorem exists_local_coordinate_stalk_lift
    (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ f) (x : O)
    (hsurj : Function.Surjective ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x)) (j : Fin d) :
    ∃ (U : Opens V) (_hxU : f x ∈ U) (t : actualComplexSection (n := n) U)
      (W : Opens O) (_hxW : x ∈ W) (hWU : ∀ y ∈ W,f y ∈ U),
      ∀ (y : O) (hy : y ∈ W),t ⟨f y,hWU y hy⟩ = y.val j := by
  let K := ChartedSpace.locallyRingedSpaceMap f hf
  let A := (actualComplexStructureSheaf (n := d) O).presheaf
  let B := (actualComplexStructureSheaf (n := n) V).presheaf
  let a := actualCoordinateSection O j
  obtain ⟨r,hr⟩ := hsurj (A.germ ⊤ x (by trivial) a)
  obtain ⟨U,hxU,t,ht⟩ := B.exists_germ_eq r
  let P := (Opens.map K.base).obj U
  let b := K.c.app (op U) t
  have he : A.germ P x hxU b = A.germ ⊤ x (by trivial) a := by
    calc
      _ = K.stalkMap x (B.germ U (f x) hxU t) :=
        (LocallyRingedSpace.stalkMap_germ_apply K U x hxU t).symm
      _ = K.stalkMap x r := congrArg (K.stalkMap x) ht
      _ = _ := hr
  obtain ⟨W,hxW,iP,iTop,hsections⟩ := A.germ_eq x hxU (by trivial) b a he
  have hWU : ∀ y ∈ W,f y ∈ U := fun y hy => leOfHom iP hy
  refine ⟨U,hxU,t,W,hxW,hWU,?_⟩
  intro y hy
  have hv := congrArg (fun s : actualComplexSection (n := d) W => s ⟨y,hy⟩) hsections
  exact hv

/-- Finite genuine coordinate lifts construct an ACTUAL holomorphic local left inverse. -/
theorem exists_actual_local_holomorphic_left_inverse
    (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ f) (x : O)
    (hsurj : Function.Surjective ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x)) :
    ∃ (T : Opens V) (_hxT : f x ∈ T) (S : Opens O) (_hxS : x ∈ S)
      (H : T → ComplexModel d)
      (_hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel d) ∞ H)
      (hST : ∀ y ∈ S,f y ∈ T),
      ∀ (y : O) (hy : y ∈ S),H ⟨f y,hST y hy⟩ = y.val := by
  classical
  choose U hxU t W hxW hWU hcoords using fun j : Fin d => exists_local_coordinate_stalk_lift hf x hsurj j
  let T : Opens V := ⨅ j : Fin d,U j
  let S : Opens O := ⨅ j : Fin d,W j
  have hTU : ∀ j : Fin d,T ≤ U j := fun j => iInf_le U j
  have hSW : ∀ j : Fin d,S ≤ W j := fun j => iInf_le W j
  have hxT : f x ∈ T := by
    change f x ∈ (T : Set V)
    simp only [T,Opens.coe_iInf,Set.mem_iInter]
    exact hxU
  have hxS : x ∈ S := by
    change x ∈ (S : Set O)
    simp only [S,Opens.coe_iInf,Set.mem_iInter]
    exact hxW
  have hST : ∀ y ∈ S,f y ∈ T := by
    intro y hy
    change f y ∈ (T : Set V)
    simp only [T,Opens.coe_iInf,Set.mem_iInter]
    exact fun j => hWU j y (hSW j hy)
  let H : T → ComplexModel d := fun z =>
    (EuclideanSpace.equiv (Fin d) ℂ).symm (fun j => t j ⟨z.val,hTU j z.property⟩)
  have hcomponents : ∀ j : Fin d,ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞
      (fun z : T => t j ⟨z.val,hTU j z.property⟩) := by
    intro j
    exact (smoothSheaf.contMDiff_section (t j)).comp (contMDiff_inclusion (hTU j))
  have hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel d) ∞ H :=
    (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap.contMDiff.comp
      (contMDiff_pi_space.mpr hcomponents)
  refine ⟨T,hxT,S,hxS,H,hH,hST,?_⟩
  intro y hy
  ext j
  exact hcoords j y (hSW j hy)

section Extension
variable {k r : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel k) M]

/-- A fixed actual total coordinate representative, used only near points in its genuine open domain. -/
def actualOpenVectorExtension (U : Opens M) (g : U → ComplexModel r) : M → ComplexModel r := by
  classical
  exact fun z => if hz : z ∈ U then g ⟨z,hz⟩ else 0

/-- The actual total representative retains EVERY original value inside the genuine open. -/
theorem actualOpenVectorExtension_apply (U : Opens M) (g : U → ComplexModel r) (x : U) :
    actualOpenVectorExtension U g x.val = g x := by
  simp only [actualOpenVectorExtension,dif_pos x.property]

/-- Original local holomorphy on the true open gives actual holomorphy of the representative at the included point. -/
theorem actualOpenVectorExtension_contMDiffAt (U : Opens M) (g : U → ComplexModel r) (x : U)
    (hg : ContMDiffAt 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel r) ∞ g x) :
    ContMDiffAt 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel r) ∞ (actualOpenVectorExtension U g) x.val := by
  have he : (fun z : U => actualOpenVectorExtension U g z.val) = g := by
    funext z
    exact actualOpenVectorExtension_apply U g z
  apply (contMDiffAt_subtype_iff (x := x)).mp
  rw [he]
  exact hg

end Extension

/-- Actual stalk surjectivity forces injectivity of the genuine original coordinate derivative, by a real local left inverse. -/
theorem injective_fderiv_of_native_stalk_surjective
    (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ f) (x : O)
    (hsurj : Function.Surjective ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x)) :
    Function.Injective (fderiv ℂ (actualOpenVectorExtension O (fun y : O => (f y).val)) x.val) := by
  obtain ⟨T,hxT,S,hxS,H,hH,hST,hleft⟩ := exists_actual_local_holomorphic_left_inverse hf x hsurj
  let f₀ : ComplexModel d → ComplexModel n := actualOpenVectorExtension O (fun y : O => (f y).val)
  let H₀ : V → ComplexModel d := actualOpenVectorExtension T H
  let H₁ : ComplexModel n → ComplexModel d := actualOpenVectorExtension V H₀
  have hfVec : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ (fun y : O => (f y).val) :=
    (contMDiff_subtype_val (U := V)).comp hf
  have hF : DifferentiableAt ℂ f₀ x.val :=
    mdifferentiableAt_iff_differentiableAt.mp
      ((actualOpenVectorExtension_contMDiffAt O (fun y : O => (f y).val) x hfVec.contMDiffAt).mdifferentiableAt (by simp))
  have hH₀ : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel d) ∞ H₀ (f x) :=
    actualOpenVectorExtension_contMDiffAt T H ⟨f x,hxT⟩ hH.contMDiffAt
  have hH₁ : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel d) ∞ H₁ (f x).val :=
    actualOpenVectorExtension_contMDiffAt V H₀ (f x) hH₀
  have hfx : f₀ x.val = (f x).val := actualOpenVectorExtension_apply O _ x
  have hG : DifferentiableAt ℂ H₁ (f₀ x.val) := by
    rw [hfx]
    exact mdifferentiableAt_iff_differentiableAt.mp (hH₁.mdifferentiableAt (by simp))
  have hSopen : IsOpen ((Subtype.val : O → ComplexModel d) '' (S : Set O)) :=
    O.isOpen.isOpenMap_subtype_val _ S.isOpen
  have hxSimage : x.val ∈ (Subtype.val : O → ComplexModel d) '' (S : Set O) := ⟨x,hxS,rfl⟩
  have hcomp : H₁ ∘ f₀ =ᶠ[nhds x.val] (id : ComplexModel d → ComplexModel d) := by
    filter_upwards [hSopen.mem_nhds hxSimage] with z hz
    obtain ⟨y,hy,rfl⟩ := hz
    calc
      H₁ (f₀ y.val) = H₁ (f y).val := congrArg H₁ (actualOpenVectorExtension_apply O _ y)
      _ = H₀ (f y) := actualOpenVectorExtension_apply V H₀ (f y)
      _ = H ⟨f y,hST y hy⟩ := actualOpenVectorExtension_apply T H ⟨f y,hST y hy⟩
      _ = y.val := hleft y hy
  have hD : (fderiv ℂ H₁ (f₀ x.val)).comp (fderiv ℂ f₀ x.val) =
      ContinuousLinearMap.id ℂ (ComplexModel d) := by
    calc
      _ = fderiv ℂ (H₁ ∘ f₀) x.val := (fderiv_comp x.val hG hF).symm
      _ = fderiv ℂ (id : ComplexModel d → ComplexModel d) x.val := hcomp.fderiv_eq
      _ = _ := fderiv_id
  have hleftD : ∀ v : ComplexModel d,(fderiv ℂ H₁ (f₀ x.val)) ((fderiv ℂ f₀ x.val) v) = v := by
    intro v
    exact congrArg (fun L : ComplexModel d →L[ℂ] ComplexModel d => L v) hD
  intro u v huv
  exact (hleftD u).symm.trans ((congrArg (fderiv ℂ H₁ (f₀ x.val)) huv).trans (hleftD v))

end
end Hironaka.HironakaActualHolomorphicStalkSurjection
