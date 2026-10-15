/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Resolution.HironakaSmoothSubmersionNormalCrossings

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionMonomialChartPullback
open BlowupMonomialCharts
noncomputable section

def splitCoordinates (r n : ℕ) :
    ComplexModel (r+n) ≃L[ℂ] (ComplexModel r × ComplexModel n) :=
  EuclideanSpace.finAddEquivProd.toContinuousLinearEquiv

def fibreProjection (r n : ℕ) (w : ComplexModel (r+n)) : ComplexModel r :=
  (splitCoordinates r n w).1

def blockProjection (r n : ℕ) (w : ComplexModel (r+n)) : ComplexModel n :=
  (splitCoordinates r n w).2

def joinCoordinates (r n : ℕ) (a : ComplexModel r) (b : ComplexModel n) : ComplexModel (r+n) :=
  (splitCoordinates r n).symm (a,b)

theorem fibreProjection_join (r n : ℕ) (a : ComplexModel r) (b : ComplexModel n) :
    fibreProjection r n (joinCoordinates r n a b) = a := by
  exact congrArg Prod.fst ((splitCoordinates r n).apply_symm_apply (a,b))

theorem blockProjection_join (r n : ℕ) (a : ComplexModel r) (b : ComplexModel n) :
    blockProjection r n (joinCoordinates r n a b) = b := by
  exact congrArg Prod.snd ((splitCoordinates r n).apply_symm_apply (a,b))

theorem joinCoordinates_projections (r n : ℕ) (w : ComplexModel (r+n)) :
    joinCoordinates r n (fibreProjection r n w) (blockProjection r n w) = w :=
  (splitCoordinates r n).symm_apply_apply w

theorem fibreProjection_apply (r n : ℕ) (w : ComplexModel (r+n)) (i : Fin r) :
    fibreProjection r n w i = w (Fin.castAdd n i) := by
  simp [fibreProjection,splitCoordinates,EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd,LinearIsometryEquiv.piLpCongrLeft_apply]

theorem blockProjection_apply (r n : ℕ) (w : ComplexModel (r+n)) (i : Fin n) :
    blockProjection r n w i = w (Fin.natAdd r i) := by
  simp [blockProjection,splitCoordinates,EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd,LinearIsometryEquiv.piLpCongrLeft_apply]

theorem contMDiff_fibreProjection (r n : ℕ) :
    ContMDiff 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel r) ∞ (fibreProjection r n) :=
  (ContinuousLinearMap.fst ℂ (ComplexModel r) (ComplexModel n)).contDiff.contMDiff.comp
    (splitCoordinates r n).contDiff.contMDiff

theorem contMDiff_blockProjection (r n : ℕ) :
    ContMDiff 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞ (blockProjection r n) :=
  (ContinuousLinearMap.snd ℂ (ComplexModel r) (ComplexModel n)).contDiff.contMDiff.comp
    (splitCoordinates r n).contDiff.contMDiff

theorem contMDiff_joinCoordinates (r n : ℕ) :
    ContMDiff 𝓘(ℂ, ComplexModel r × ComplexModel n)
      𝓘(ℂ, ComplexModel (r+n)) ∞ (fun p : ComplexModel r × ComplexModel n => joinCoordinates r n p.1 p.2) :=
  (splitCoordinates r n).symm.contDiff.contMDiff

def fibreInclusion (r n : ℕ) : ComplexModel r →L[ℂ] ComplexModel (r+n) :=
  (splitCoordinates r n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel n))

def blockInclusion (r n : ℕ) : ComplexModel n →L[ℂ] ComplexModel (r+n) :=
  (splitCoordinates r n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ (ComplexModel r) (ComplexModel n))

theorem joinCoordinates_eq_add (r n : ℕ) (a : ComplexModel r) (b : ComplexModel n) :
    joinCoordinates r n a b = fibreInclusion r n a + blockInclusion r n b := by
  change (splitCoordinates r n).symm (a,b) =
    (splitCoordinates r n).symm (a,0) + (splitCoordinates r n).symm (0,b)
  rw [← map_add]
  simp only [Prod.mk_add_mk,add_zero,zero_add]

theorem fibreProjection_monomial (r n k : ℕ) (j : Fin n) (w : ComplexModel (r+n)) :
    fibreProjection r n (monomial (r+k) (Fin.natAdd r j) w) = fibreProjection r n w := by
  ext i
  rw [fibreProjection_apply,fibreProjection_apply,monomial_apply]
  have hi : ¬ r+k ≤ (Fin.castAdd n i).val := by simp only [Fin.val_castAdd]; omega
  simp only [Fin.val_castAdd] at hi ⊢
  simp only [hi,false_and,if_false]

theorem blockProjection_monomial (r n k : ℕ) (j : Fin n) (w : ComplexModel (r+n)) :
    blockProjection r n (monomial (r+k) (Fin.natAdd r j) w) =
      monomial k j (blockProjection r n w) := by
  ext i
  simp only [blockProjection_apply,monomial_apply,Fin.val_natAdd]
  have he : (Fin.natAdd r i ≠ Fin.natAdd r j) ↔ i ≠ j := by
    constructor
    · intro hi hij; exact hi (congrArg (Fin.natAdd r) hij)
    · intro hi hij; apply hi; apply Fin.ext
      have hv := congrArg Fin.val hij
      simpa only [Fin.val_natAdd,Nat.add_left_cancel_iff] using hv
  have hle : r+k ≤ r+i.val ↔ k ≤ i.val := Nat.add_le_add_iff_left
  simp only [he,hle]

theorem monomial_eq_join (r n k : ℕ) (j : Fin n) (w : ComplexModel (r+n)) :
    monomial (r+k) (Fin.natAdd r j) w =
      joinCoordinates r n (fibreProjection r n w) (monomial k j (blockProjection r n w)) := by
  rw [← fibreProjection_monomial r n k j w,← blockProjection_monomial r n k j w,
    joinCoordinates_projections]

/-- Actual global model charts give a true projection submersion with the SAME fibre complement. -/
theorem isSubmersionOfComplement_blockProjection (r n : ℕ) :
    Manifold.IsSubmersionOfComplement (ComplexModel r)
      𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞ (blockProjection r n) := by
  intro x
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
    ((splitCoordinates r n).trans (ContinuousLinearEquiv.prodComm ℂ (ComplexModel r) (ComplexModel n)))
    (chartAt (ComplexModel (r+n)) x) (chartAt (ComplexModel n) (blockProjection r n x))
    (mem_chart_source _ x) (mem_chart_source _ (blockProjection r n x))
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
  · intro z hz
    exact mem_univ _
  · intro z hz
    rfl

theorem isSubmersion_blockProjection (r n : ℕ) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞ (blockProjection r n) :=
  (isSubmersionOfComplement_blockProjection r n).isSubmersion

variable {ℓ : ℕ} {P : Type u} [TopologicalSpace P]
  [ChartedSpace (ComplexModel ℓ) P] [IsComplexManifold ℓ P]

/-- The literal real coordinate lift, defined independently of any result certificate. -/
def coneLift (r n : ℕ) (u : P → ComplexModel (r+n)) (v : P → ComplexModel n) :
    P → ComplexModel (r+n) :=
  fun p => joinCoordinates r n (fibreProjection r n (u p)) (v p)

omit [IsComplexManifold ℓ P] in
theorem coneLift_contMDiff (r n : ℕ)
    (u : P → ComplexModel (r+n)) (v : P → ComplexModel n)
    (hu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ u)
    (hv : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v) :
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ (coneLift r n u v) := by
  have hfu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel r) ∞
      (fun p => fibreProjection r n (u p)) := (contMDiff_fibreProjection r n).comp hu
  have he : coneLift r n u v = fun p =>
      fibreInclusion r n (fibreProjection r n (u p)) + blockInclusion r n (v p) :=
    funext (fun p => joinCoordinates_eq_add r n _ _)
  rw [he]
  exact ((fibreInclusion r n).contDiff.contMDiff.comp hfu).add
    ((blockInclusion r n).contDiff.contMDiff.comp hv)

omit [TopologicalSpace P] in
theorem coneLift_projection (r n k : ℕ) (j : Fin n)
    (u : P → ComplexModel (r+n)) (v : P → ComplexModel n)
    (hc : blockProjection r n ∘ u = monomial k j ∘ v) :
    monomial (r+k) (Fin.natAdd r j) ∘ coneLift r n u v = u := by
  funext p
  change monomial (r+k) (Fin.natAdd r j) (joinCoordinates r n _ _) = u p
  rw [monomial_eq_join,fibreProjection_join,blockProjection_join]
  have hp : monomial k j (v p) = blockProjection r n (u p) := (congrFun hc p).symm
  rw [hp]
  exact joinCoordinates_projections r n (u p)

omit [TopologicalSpace P] in
theorem coneLift_drop (r n : ℕ) (u : P → ComplexModel (r+n)) (v : P → ComplexModel n) :
    blockProjection r n ∘ coneLift r n u v = v :=
  funext (fun p => blockProjection_join r n (fibreProjection r n (u p)) (v p))

omit [TopologicalSpace P] in
theorem coneLift_unique (r n k : ℕ) (j : Fin n)
    (u w : P → ComplexModel (r+n)) (v : P → ComplexModel n)
    (hσ : monomial (r+k) (Fin.natAdd r j) ∘ w = u)
    (hv : blockProjection r n ∘ w = v) : w = coneLift r n u v := by
  funext p
  have ha : fibreProjection r n (w p) = fibreProjection r n (u p) := by
    rw [← fibreProjection_monomial r n k j (w p)]
    exact congrArg (fibreProjection r n) (congrFun hσ p)
  calc w p = joinCoordinates r n (fibreProjection r n (w p)) (blockProjection r n (w p)) :=
        (joinCoordinates_projections r n (w p)).symm
    _ = joinCoordinates r n (fibreProjection r n (u p)) (v p) := by
      have hp : blockProjection r n (w p) = v p := congrFun hv p
      rw [ha,hp]
    _ = coneLift r n u v p := rfl

omit [IsComplexManifold ℓ P] in
/-- Explicit actual lift of ANY holomorphic compatible cone, including exceptional cones. -/
theorem existsUnique_monomial_lift (r n k : ℕ) (j : Fin n)
    (u : P → ComplexModel (r+n)) (v : P → ComplexModel n)
    (hu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ u)
    (hv : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v)
    (hc : blockProjection r n ∘ u = monomial k j ∘ v) :
    ∃! w : P → ComplexModel (r+n),
      ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ w ∧
      monomial (r+k) (Fin.natAdd r j) ∘ w = u ∧ blockProjection r n ∘ w = v := by
  refine ⟨coneLift r n u v,⟨coneLift_contMDiff r n u v hu hv,
    coneLift_projection r n k j u v hc,coneLift_drop r n u v⟩,?_⟩
  intro w hw
  exact coneLift_unique r n k j u w v hw.2.1 hw.2.2

/-- The literal source product-open base. -/
def baseProductOpen (r n : ℕ) (R : TopologicalSpace.Opens (ComplexModel r))
    (S : TopologicalSpace.Opens (ComplexModel n)) : TopologicalSpace.Opens (ComplexModel (r+n)) :=
  ⟨{w | fibreProjection r n w ∈ R ∧ blockProjection r n w ∈ S},
    (R.isOpen.preimage (contMDiff_fibreProjection r n).continuous).inter
      (S.isOpen.preimage (contMDiff_blockProjection r n).continuous)⟩

def targetChartOpen (k : ℕ) {n : ℕ} (j : Fin n)
    (S : TopologicalSpace.Opens (ComplexModel n)) : TopologicalSpace.Opens (ComplexModel n) :=
  ⟨monomial k j ⁻¹' S,S.isOpen.preimage (contDiff_monomial k j).continuous⟩

def sourceChartOpen (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n)) :
    TopologicalSpace.Opens (ComplexModel (r+n)) :=
  ⟨{w | fibreProjection r n w ∈ R ∧ monomial k j (blockProjection r n w) ∈ S},
    (R.isOpen.preimage (contMDiff_fibreProjection r n).continuous).inter
      (S.isOpen.preimage ((contDiff_monomial k j).continuous.comp
        (contMDiff_blockProjection r n).continuous))⟩

def baseOpenProjection (r n : ℕ) (R : TopologicalSpace.Opens (ComplexModel r))
    (S : TopologicalSpace.Opens (ComplexModel n)) (w : baseProductOpen r n R S) : S :=
  ⟨blockProjection r n w.val,w.property.2⟩

def targetOpenProjection (k : ℕ) {n : ℕ} (j : Fin n)
    (S : TopologicalSpace.Opens (ComplexModel n)) (w : targetChartOpen k j S) : S :=
  ⟨monomial k j w.val,w.property⟩

def sourceOpenProjection (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
    (w : sourceChartOpen r n k j R S) : baseProductOpen r n R S :=
  ⟨monomial (r+k) (Fin.natAdd r j) w.val,by
    change fibreProjection r n (monomial (r+k) (Fin.natAdd r j) w.val) ∈ R ∧
      blockProjection r n (monomial (r+k) (Fin.natAdd r j) w.val) ∈ S
    rw [fibreProjection_monomial,blockProjection_monomial]
    exact w.property⟩

def liftedOpenProjection (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
    (w : sourceChartOpen r n k j R S) : targetChartOpen k j S :=
  ⟨blockProjection r n w.val,w.property.2⟩

theorem contMDiff_baseOpenProjection (r n : ℕ) (R : TopologicalSpace.Opens (ComplexModel r))
    (S : TopologicalSpace.Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞ (baseOpenProjection r n R S) := by
  apply (ContMDiff.subtypeVal_comp_iff S _).mp
  exact (contMDiff_blockProjection r n).comp contMDiff_subtype_val

theorem contMDiff_targetOpenProjection (k : ℕ) {n : ℕ} (j : Fin n)
    (S : TopologicalSpace.Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (targetOpenProjection k j S) := by
  apply (ContMDiff.subtypeVal_comp_iff S _).mp
  exact (contDiff_monomial k j).contMDiff.comp contMDiff_subtype_val

theorem contMDiff_sourceOpenProjection (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel (r+n)) ∞
      (sourceOpenProjection r n k j R S) := by
  apply (ContMDiff.subtypeVal_comp_iff (baseProductOpen r n R S) _).mp
  exact (contDiff_monomial (r+k) (Fin.natAdd r j)).contMDiff.comp contMDiff_subtype_val

theorem contMDiff_liftedOpenProjection (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞
      (liftedOpenProjection r n k j R S) := by
  apply (ContMDiff.subtypeVal_comp_iff (targetChartOpen k j S) _).mp
  exact (contMDiff_blockProjection r n).comp contMDiff_subtype_val

omit [IsComplexManifold ℓ P] in
theorem existsUnique_open_monomial_lift (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
    (u : P → baseProductOpen r n R S) (v : P → targetChartOpen k j S)
    (hu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ u)
    (hv : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v)
    (hc : baseOpenProjection r n R S ∘ u = targetOpenProjection k j S ∘ v) :
    ∃! w : P → sourceChartOpen r n k j R S,
      ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ w ∧
      sourceOpenProjection r n k j R S ∘ w = u ∧ liftedOpenProjection r n k j R S ∘ w = v := by
  let U : P → ComplexModel (r+n) := fun p => (u p).val
  let V : P → ComplexModel n := fun p => (v p).val
  have hU : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ U :=
    contMDiff_subtype_val.comp hu
  have hV : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ V :=
    contMDiff_subtype_val.comp hv
  have hraw : blockProjection r n ∘ U = monomial k j ∘ V :=
    funext (fun p => congrArg Subtype.val (congrFun hc p))
  let w : P → sourceChartOpen r n k j R S := fun p =>
    ⟨coneLift r n U V p,by
      change fibreProjection r n (joinCoordinates r n _ _) ∈ R ∧
        monomial k j (blockProjection r n (joinCoordinates r n _ _)) ∈ S
      rw [fibreProjection_join,blockProjection_join]
      exact ⟨(u p).property.1,(v p).property⟩⟩
  have hw : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ w := by
    apply (ContMDiff.subtypeVal_comp_iff (sourceChartOpen r n k j R S) _).mp
    exact coneLift_contMDiff r n U V hU hV
  have hσ : sourceOpenProjection r n k j R S ∘ w = u := by
    funext p
    apply Subtype.ext
    exact congrFun (coneLift_projection r n k j U V hraw) p
  have hd : liftedOpenProjection r n k j R S ∘ w = v := by
    funext p
    apply Subtype.ext
    exact congrFun (coneLift_drop r n U V) p
  refine ⟨w,⟨hw,hσ,hd⟩,?_⟩
  intro z hz
  have he : (fun p => (z p).val) = coneLift r n U V :=
    coneLift_unique r n k j U (fun p => (z p).val) V
      (funext (fun p => congrArg Subtype.val (congrFun hz.2.1 p)))
      (funext (fun p => congrArg Subtype.val (congrFun hz.2.2 p)))
  funext p
  exact Subtype.ext (congrFun he p)

end
end Hironaka.HironakaSmoothSubmersionMonomialChartPullback
