import Hironaka.Resolution.HironakaActualProjectionTestRecord
import Hironaka.Resolution.HironakaSmoothSubmersionBlowupCartesian
import Hironaka.Blowup.BlowupSourceBiholomorphism

/-! The literal product of an actual native blowup with the complex line.
The actual Cartesian universal property constructs the source comparison;
no target-shaped blowup, comparison or future history is an input.
Blueprint FIRST: `hironaka-actual-product-blowup.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProductBlowup
noncomputable section
open Hironaka.BlowupSequences BlowupTowers ProductComplexManifold
  HironakaActualProjectionTestRecord HironakaAuxiliaryGraphGeometry
  HironakaSmoothSubmersionBlowupLift HironakaSmoothSubmersionBlowupCartesian
  HironakaSmoothSubmersionBlowupPivotCompatibility
  HironakaSharpActualCurveSuccessorLocalBlowup
open scoped ProductComplexManifold
variable {n : ℕ} {X D : CMfd.{u} n} {C : Set X} {π : D→X}

/-- The literal whole product map on the actual summed-dimension products. -/
def productMap (π : D→X) : projectionAmbient D→projectionAmbient X :=
  fun p => (π p.1,p.2)

/-- Only the original native blowup is input. Its literal product with
the line satisfies the entire original native blowup predicate. -/
theorem native_product_blowup (hπ : IsBlowupAlong n C π) :
    IsBlowupAlong (n+1) ((Prod.fst : projectionAmbient X→X) ⁻¹' C) (productMap π) := by
  have hp : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞
      (Prod.fst : projectionAmbient X→X) :=
    isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  obtain ⟨Z,ρ,hρ,hg,hSquare,hCone⟩ := exists_original_smooth_cartesian_blowup
    (n := n) (m := n+1) (X := X) (D := D) (Y := projectionAmbient X)
    (f := (Prod.fst : projectionAmbient X→X)) hp hπ
  let g : Z→D := actualLift hp hπ hρ
  have hProduct : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞
      (productMap π) :=
    contMDiff_prodMk
      (hπ.contMDiff.comp (contMDiff_fst (n := n) (m := 1) (X := D) (Y := ComplexModel 1)))
      (contMDiff_snd (n := n) (m := 1) (X := D) (Y := ComplexModel 1))
  have hFst : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞
      (Prod.fst : projectionAmbient D→D) :=
    contMDiff_fst (n := n) (m := 1) (X := D) (Y := ComplexModel 1)
  obtain ⟨f,hf,_hfUnique⟩ := hCone (n+1) (projectionAmbient D) (productMap π)
    Prod.fst hProduct hFst (fun _ => rfl)
  let e : Z→projectionAmbient D := fun z => (g z,(ρ z).2)
  have he : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ e :=
    contMDiff_prodMk hg.contMDiff
      ((contMDiff_snd (n := n) (m := 1) (X := X) (Y := ComplexModel 1)).comp hρ.contMDiff)
  have hef (p : projectionAmbient D) : e (f p)=p := by
    apply Prod.ext
    · exact congrFun hf.2.2 p
    · exact congrArg (fun w : projectionAmbient X => w.2) (congrFun hf.2.1 p)
  have hfe (z : Z) : f (e z)=z := by
    apply actualLift_joint_unique hp hπ hρ
    · rw [show ρ (f (e z))=productMap π (e z) from congrFun hf.2.1 (e z)]
      apply Prod.ext
      · exact congrFun hSquare z
      · rfl
    · exact congrFun hf.2.2 (e z)
  let F : projectionAmbient D ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ Z :=
    { toFun := f
      invFun := e
      left_inv := hef
      right_inv := hfe
      contMDiff_toFun := hf.1
      contMDiff_invFun := he }
  have hBlowup := isBlowupAlong_comp_diffeomorph F hρ
  have hMap : ρ ∘ F=productMap π := hf.2.1
  exact hMap ▸ hBlowup

end
end Hironaka.HironakaActualProductBlowup
