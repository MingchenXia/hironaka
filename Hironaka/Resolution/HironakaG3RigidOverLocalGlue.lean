import Hironaka.Resolution.HironakaG3RTowerClass
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3RigidOverLocalGlue
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3RGluedUniqueness
variable {n : ℕ} {X X₁ X₂ : CMfd.{u} n}

def window (P : X₁ → X) (hP : Continuous P) (U : Opens X) : Opens X₁ :=
  ⟨P ⁻¹' (U : Set X),U.isOpen.preimage hP⟩

/-- Rigidity for maps over an actual projection. -/
def RigidOver (P : X₂ → X) : Prop :=
  ∀ (Z : CMfd.{u} n) (f g : Z → X₂),
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f →
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g →
    exceptionalLocus n f = ∅ → (∀ z, P (f z) = P (g z)) → f = g

/-- Covering actual tower charts provide rigidity. -/
theorem rigid_of_tower_charts {𝒞 : LocalTowerClass X} {P : X₂ → X}
    (hch : ∀ x, ∃ c : TowerChart 𝒞 X₂ P, x ∈ c.U) : RigidOver P := by
  intro Z f g hf hg he hp
  exact eq_of_proj_eq_of_charts hch f g hf hg he hp

/-- An actual finite-tower projection is rigid. -/
theorem rigid_of_tower (T : BlowupTower X X₂) : RigidOver T.proj := by
  intro Z f g hf hg he hp
  exact HironakaG3RGluedUniqueness.eq_of_proj_eq T f g hf hg (by rw [he,interior_empty]) hp

/-- Restriction over a base open retains actual-map rigidity. -/
theorem rigid_of_open_restriction {P : X₂ → X} (hP : Continuous P)
    (hR : RigidOver P) (A : Opens X) :
    RigidOver (X := CMfd.of (n := n) A) (X₂ := CMfd.of (n := n) (window P hP A))
      (fun z : window P hP A => (⟨P z.val,z.property⟩ : A)) := by
  intro Z f g hf hg he hp
  have hh : (Subtype.val ∘ f) = (Subtype.val ∘ g) := by
    apply hR Z _ _ (contMDiff_subtype_val.comp hf) (contMDiff_subtype_val.comp hg)
    · rwa [exceptionalLocus_val_comp hf]
    · intro z
      exact congrArg Subtype.val (hp z)
  funext z
  exact Subtype.ext (congrFun hh z)

/-- Any two local over-base biholomorphisms agree on their actual overlap. -/
theorem local_over_maps_agree {P₁ : X₁ → X} {P₂ : X₂ → X}
    (hP₁ : Continuous P₁) (hP₂ : Continuous P₂)
    (hR₂ : RigidOver P₂)
    (U V : Opens X)
    (φ : (CMfd.of (n := n) (window P₁ hP₁ U)) ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) (window P₂ hP₂ U)))
    (ψ : (CMfd.of (n := n) (window P₁ hP₁ V)) ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) (window P₂ hP₂ V)))
    (hφ : ∀ z, P₂ (φ z).val = P₁ z.val)
    (hψ : ∀ z, P₂ (ψ z).val = P₁ z.val)
    (z : X₁) (hzU : z ∈ window P₁ hP₁ U) (hzV : z ∈ window P₁ hP₁ V) :
    (φ ⟨z,hzU⟩).val = (ψ ⟨z,hzV⟩).val := by
  let O : Opens X₁ := window P₁ hP₁ U ⊓ window P₁ hP₁ V
  let iU : O → window P₁ hP₁ U := fun o => ⟨o.val,o.property.1⟩
  let iV : O → window P₁ hP₁ V := fun o => ⟨o.val,o.property.2⟩
  have hiU : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ iU :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hiV : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ iV :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  let f : O → X₂ := Subtype.val ∘ φ ∘ iU
  let g : O → X₂ := Subtype.val ∘ ψ ∘ iV
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f :=
    contMDiff_subtype_val.comp (φ.contMDiff.comp hiU)
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g :=
    contMDiff_subtype_val.comp (ψ.contMDiff.comp hiV)
  have hexc : exceptionalLocus n f = ∅ := by
    change exceptionalLocus n (Subtype.val ∘ (φ ∘ iU)) = ∅
    rw [exceptionalLocus_val_comp (φ.contMDiff.comp hiU), exceptionalLocus_diffeo_comp φ hiU,
      exceptionalLocus_opens_mk contMDiff_subtype_val, HironakaBaseChange.exceptionalLocus_val]
  have heq := hR₂ (CMfd.of (n := n) O) f g hf hg hexc
    (fun o => (hφ (iU o)).trans (hψ (iV o)).symm)
  exact congrFun heq ⟨z,hzU,hzV⟩

variable {ι : Type v} {P₁ : X₁ → X} {P₂ : X₂ → X}
  (hP₁ : Continuous P₁) (hP₂ : Continuous P₂) (U : ι → Opens X)
  (hcover : ∀ x : X, ∃ i, x ∈ U i)
  (φ : ∀ i, (CMfd.of (n := n) (window P₁ hP₁ (U i))) ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) (window P₂ hP₂ (U i))))

/-- The pointwise map defined from an actual local over-base equivalence. -/
def gluedLocalMap (z : X₁) : X₂ :=
  let i := (hcover (P₁ z)).choose
  (φ i ⟨z,(hcover (P₁ z)).choose_spec⟩).val

theorem gluedLocalMap_eq 
    (hR₂ : RigidOver P₂)
    (hφ : ∀ i z, P₂ (φ i z).val = P₁ z.val)
    (i : ι) (z : X₁) (hz : z ∈ window P₁ hP₁ (U i)) :
    gluedLocalMap hP₁ hP₂ U hcover φ z = (φ i ⟨z,hz⟩).val := by
  exact local_over_maps_agree hP₁ hP₂ hR₂ _ _ _ _
    (hφ ((hcover (P₁ z)).choose)) (hφ i) z (hcover (P₁ z)).choose_spec hz

theorem gluedLocalMap_proj (hφ : ∀ i z, P₂ (φ i z).val = P₁ z.val) (z : X₁) :
    P₂ (gluedLocalMap hP₁ hP₂ U hcover φ z) = P₁ z := by
  exact hφ _ _

theorem gluedLocalMap_contMDiff 
    (hR₂ : RigidOver P₂)
    (hφ : ∀ i z, P₂ (φ i z).val = P₁ z.val) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (gluedLocalMap hP₁ hP₂ U hcover φ) := by
  intro z
  let i := (hcover (P₁ z)).choose
  let V := window P₁ hP₁ (U i)
  have hz : z ∈ V := (hcover (P₁ z)).choose_spec
  have hEq : (fun p : V => gluedLocalMap hP₁ hP₂ U hcover φ p.val) =
      (fun p : V => (φ i p).val) := by
    funext p
    exact gluedLocalMap_eq hP₁ hP₂ U hcover φ hR₂ hφ i p.val p.property
  have hh := ((contMDiff_subtype_val (n := ∞)).comp (φ i).contMDiff) ⟨z,hz⟩
  change ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
    (fun p : V => (φ i p).val) ⟨z,hz⟩ at hh
  rw [← hEq] at hh
  exact contMDiffAt_subtype_iff.mp hh


include hcover in
/-- Actual local over-base biholomorphisms glue uniquely by tower-chart rigidity. -/
theorem existsUnique_gluedLocalDiffeomorph (hR₁ : RigidOver P₁) (hR₂ : RigidOver P₂)
    (hφ : ∀ i z, P₂ (φ i z).val = P₁ z.val) :
    ∃! Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X₂,
      ∀ z, P₂ (Φ z) = P₁ z := by
  let ψ := fun i => (φ i).symm
  have hψ : ∀ i z, P₁ (ψ i z).val = P₂ z.val := by
    intro i z
    have h := hφ i ((φ i).symm z)
    simpa only [Diffeomorph.apply_symm_apply] using h.symm
  let F := gluedLocalMap hP₁ hP₂ U hcover φ
  let G := gluedLocalMap hP₂ hP₁ U hcover ψ
  have hF : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ F :=
    gluedLocalMap_contMDiff hP₁ hP₂ U hcover φ hR₂ hφ
  have hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ G :=
    gluedLocalMap_contMDiff hP₂ hP₁ U hcover ψ hR₁ hψ
  have hpF : ∀ z, P₂ (F z) = P₁ z := gluedLocalMap_proj hP₁ hP₂ U hcover φ hφ
  have hpG : ∀ z, P₁ (G z) = P₂ z := gluedLocalMap_proj hP₂ hP₁ U hcover ψ hψ
  have hGF : G ∘ F = id :=
    (hR₁ X₁ id _ contMDiff_id (hG.comp hF) exceptionalLocus_id
      (fun z => ((hpG _).trans (hpF z)).symm)).symm
  have hFG : F ∘ G = id :=
    (hR₂ X₂ id _ contMDiff_id (hF.comp hG) exceptionalLocus_id
      (fun z => ((hpF _).trans (hpG z)).symm)).symm
  let Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X₂ :=
    { toFun := F, invFun := G, left_inv := congrFun hGF, right_inv := congrFun hFG,
      contMDiff_toFun := hF, contMDiff_invFun := hG }
  refine ⟨Φ,hpF,?_⟩
  intro Φ' hΦ'
  apply Diffeomorph.ext
  intro z
  exact congrFun (hR₂ X₁ Φ' F Φ'.contMDiff hF
    (eq_empty_of_forall_notMem (MarkedIdealTowerTransport.notMem_exceptionalLocus Φ'))
    (fun z => (hΦ' z).trans (hpF z).symm)) z

end
end Hironaka.HironakaG3RigidOverLocalGlue
