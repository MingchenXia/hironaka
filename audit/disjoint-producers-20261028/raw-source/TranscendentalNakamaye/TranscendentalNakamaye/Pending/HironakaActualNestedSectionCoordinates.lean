import TranscendentalNakamaye.Pending.HironakaActualMaskSectionRepresentative
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace TranscendentalNakamaye.Pending.HironakaActualNestedSectionCoordinates
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves
 HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
 HironakaActualCentreJointJets
variable {n : ℕ}

def globalImage (U : Opens (ComplexModel n)) (W : Opens U) : Opens (ComplexModel n) :=
 ⟨(Subtype.val : U → ComplexModel n) '' (W : Set U),U.isOpen.isOpenMap_subtype_val _ W.isOpen⟩

private theorem image_mem_U (U : Opens (ComplexModel n)) (W : Opens U) (x : globalImage U W) : x.val ∈ U := by
 obtain ⟨y,_hy,he⟩ := x.property
 exact he ▸ y.property

private theorem image_mem_W (U : Opens (ComplexModel n)) (W : Opens U) (x : globalImage U W) :
 (⟨x.val,image_mem_U U W x⟩ : U) ∈ W := by
 obtain ⟨y,hy,he⟩ := x.property
 have h : (⟨x.val,image_mem_U U W x⟩ : U) = y := Subtype.ext he.symm
 exact h ▸ hy

def baseEquiv (U : Opens (ComplexModel n)) (W : Opens U) :
 W ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ globalImage U W where
 toFun x := ⟨x.val.val,⟨x.val,x.property,rfl⟩⟩
 invFun x := ⟨⟨x.val,image_mem_U U W x⟩,image_mem_W U W x⟩
 left_inv _ := rfl
 right_inv _ := rfl
 contMDiff_toFun := by
   apply (ContMDiff.subtypeVal_comp_iff (globalImage U W) _).mp
   change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
     ((Subtype.val : U → ComplexModel n) ∘ (Subtype.val : W → U))
   exact contMDiff_subtype_val.comp contMDiff_subtype_val
 contMDiff_invFun := by
   apply (ContMDiff.subtypeVal_comp_iff W _).mp
   apply (ContMDiff.subtypeVal_comp_iff U _).mp
   exact contMDiff_subtype_val

def productWindow (U : Opens (ComplexModel n)) (W : Opens U) : Opens (productOpen U) :=
 ⟨projection U ⁻¹' W,W.isOpen.preimage (projection_contMDiff U).continuous⟩

private theorem product_mem_U (U : Opens (ComplexModel n)) (W : Opens U)
 (z : productOpen (globalImage U W)) : tangentProjection n 1 z.val ∈ U := by
 obtain ⟨x,_hx,he⟩ := z.property
 exact he ▸ x.property

private theorem product_mem_W (U : Opens (ComplexModel n)) (W : Opens U)
 (z : productOpen (globalImage U W)) :
 projection U (⟨z.val,product_mem_U U W z⟩ : productOpen U) ∈ W := by
 obtain ⟨x,hx,he⟩ := z.property
 have h : projection U (⟨z.val,product_mem_U U W z⟩ : productOpen U) = x := Subtype.ext he.symm
 exact h ▸ hx

def productEquiv (U : Opens (ComplexModel n)) (W : Opens U) :
 productWindow U W ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ productOpen (globalImage U W) where
 toFun z := ⟨z.val.val,⟨projection U z.val,z.property,rfl⟩⟩
 invFun z := ⟨⟨z.val,product_mem_U U W z⟩,product_mem_W U W z⟩
 left_inv _ := rfl
 right_inv _ := rfl
 contMDiff_toFun := by
   apply (ContMDiff.subtypeVal_comp_iff (productOpen (globalImage U W)) _).mp
   change ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞
     ((Subtype.val : productOpen U → ComplexModel (n+1)) ∘
       (Subtype.val : productWindow U W → productOpen U))
   exact contMDiff_subtype_val.comp contMDiff_subtype_val
 contMDiff_invFun := by
   apply (ContMDiff.subtypeVal_comp_iff (productWindow U W) _).mp
   apply (ContMDiff.subtypeVal_comp_iff (productOpen U) _).mp
   exact contMDiff_subtype_val

def windowSection (U : Opens (ComplexModel n)) (W : Opens U) (x : W) : productWindow U W :=
 ⟨zeroSection U x.val,by
   change projection U (zeroSection U x.val) ∈ W
   have he : projection U (zeroSection U x.val) = x.val := Subtype.ext (tangentProjection_tangentInclusion n 1 x.val.val)
   rw [he];exact x.property⟩

def windowProjection (U : Opens (ComplexModel n)) (W : Opens U) (z : productWindow U W) : W :=
 ⟨projection U z.val,z.property⟩

theorem section_square (U : Opens (ComplexModel n)) (W : Opens U) (x : W) :
 productEquiv U W (windowSection U W x) = zeroSection (globalImage U W) (baseEquiv U W x) := rfl

theorem projection_square (U : Opens (ComplexModel n)) (W : Opens U) (z : productWindow U W) :
 baseEquiv U W (windowProjection U W z) = projection (globalImage U W) (productEquiv U W z) := rfl

theorem carrier_iff (U : Opens (ComplexModel n)) (W : Opens U) (A : Set W) (z : productWindow U W) :
 (windowProjection U W z ∈ A ∧ actualJointNormalProjection n 1 z.val.val = 0) ↔
 productEquiv U W z ∈ liftedCarrier (baseEquiv U W '' A) := by
 change (_ ∧ _) ↔ (projection (globalImage U W) (productEquiv U W z) ∈ baseEquiv U W '' A ∧ _)
 rw [←projection_square]
 constructor
 · rintro ⟨ha,hq⟩
   exact ⟨⟨_,ha,rfl⟩,hq⟩
 · rintro ⟨⟨x,hx,he⟩,hq⟩
   have h : x = windowProjection U W z := (baseEquiv U W).injective he
   exact ⟨h ▸ hx,hq⟩
end
end TranscendentalNakamaye.Pending.HironakaActualNestedSectionCoordinates
