/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionBlowupLocalCones
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionBlowupPivotCompatibility
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates BlowupMonomialCharts
  BlowupConstruction BlowupSpaceTangent HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaSmoothSubmersionAdaptedBlowupCharts HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionUniversalBlowupChartEquality HironakaSmoothSubmersionBlowupCompatiblePoints
  HironakaSmoothSubmersionBlowupChoiceGeometry HironakaSmoothSubmersionBlowupLocalCones
  HironakaSmoothSubmersionAdaptedBlowupCoverage
noncomputable section

def repivot {n : ℕ} {X : CMfd.{u} n} {C : Set X} (c : FlatChart n C)
    (j : Fin n) (hj : c.k ≤ j.val) : FlatChart n C := {c with j := j, hj := hj}

theorem repivot_eq_self_of_pivot {n : ℕ} {X : CMfd.{u} n} {C : Set X}
    (c : FlatChart n C) (i : Fin n) (hi : c.k ≤ i.val) (he : i = c.j) : repivot c i hi = c := by
  subst i
  rfl

section Ratio
variable {n r : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X} {C : Set X}

theorem matching_pivot_extended_support (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C))
    (hk : c'.k = r+c.k) (hj : c'.j = rotateBlocks n r (Fin.castAdd r c.j))
    (hdrop : MapsTo (adaptedTargetProjection n r) c'.target c.target)
    (q : BlowupSpace (n+r) (f ⁻¹' C)) (hq : q ∈ c'.source) (i : Fin n) (hi : c.k ≤ i.val) :
    extVal (c'.τ (rotateBlocks n r (Fin.castAdd r i))) q ≠ 0 ↔
      extVal (c.τ i) (flatChartMap c c' q) ≠ 0 := by
  have hparam := hdrop (c'.map_source hq)
  have hz : flatChartMap c c' q ∈ c.source := c.map_target hparam
  by_cases hij : i = c.j
  · subst i
    rw [← hj]
    exact iff_of_true hq.2 hz.2
  · have hi' : c'.k ≤ (rotateBlocks n r (Fin.castAdd r i)).val := by
      rw [hk,rotateBlocks_target]; omega
    have hij' : rotateBlocks n r (Fin.castAdd r i) ≠ c'.j := by
      rw [hj]
      intro he
      have he' := (rotateBlocks n r).injective he
      apply hij
      exact Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val he')
    have he : c.toFun (flatChartMap c c' q) = adaptedTargetProjection n r (c'.toFun q) :=
      c.right_inv hparam
    have hiEq := congrArg (fun w : ComplexModel n => w i) he
    rw [c.toFun_apply_normal _ hi hij,adaptedTargetProjection_apply,
      c'.toFun_apply_normal _ hi' hij'] at hiEq
    constructor
    · intro hne
      have hr := div_ne_zero hne hq.2
      rw [← hiEq] at hr
      exact (div_ne_zero_iff.mp hr).1
    · intro hne
      have hr := div_ne_zero hne hz.2
      rw [hiEq] at hr
      exact (div_ne_zero_iff.mp hr).1
end Ratio

theorem exists_original_matching_pivot_family {n r : ℕ}
    {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X} {C : Set X}
    (p : BlowupSpace (n+r) (f ⁻¹' C)) (hpC : p.base ∈ f ⁻¹' C)
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f p.base)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f p.base) (f p.base)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f p.base)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f p.base) (f p.base)) = 0)
    (k : ℕ) (hflat : ∀ z ∈ flatDomain Φ, z ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f p.base) z) ∈ complexCoordinatePlane n k) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r))
      (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C)),
      c'.k = r+c.k ∧ c'.j = rotateBlocks n r (Fin.castAdd r c.j) ∧ p ∈ c'.source ∧
      ∀ (i : Fin n) (hi : c.k ≤ i.val)
        (hi' : c'.k ≤ (rotateBlocks n r (Fin.castAdd r i)).val),
        (repivot c' (rotateBlocks n r (Fin.castAdd r i)) hi').target =
          (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ (repivot c i hi).target) ∧
        ∀ w ∈ (repivot c' (rotateBlocks n r (Fin.castAdd r i)) hi').target,
          f ((repivot c' (rotateBlocks n r (Fin.castAdd r i)) hi').pt w) =
            (repivot c i hi).pt (adaptedTargetProjection n r w) := by
  obtain ⟨R,S,Ψ,hR0,hS0,hSΦ,hΨsrc,hΨ0,hΨtarget,hd,hinv⟩ :=
    exists_adapted_product_centre_coordinates hf Φ h0 C k hflat
  have hΨflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel (n+r)) p.base).source →
      chartAt (ComplexModel (n+r)) p.base z ∈ Ψ.source →
      (z ∈ f ⁻¹' C ↔ Ψ.toFun (chartAt (ComplexModel (n+r)) p.base z) ∈
        complexCoordinatePlane (n+r) (r+k)) := fun hz hΨ => (hd _ ⟨hz,hΨ⟩).2.2
  have hnot := BlowupSpace.dirVec_not_mem hpC
  rw [mem_tangentSpace_iff hΨsrc hΨflat (mem_flatDomain_self Ψ) hpC] at hnot
  push Not at hnot
  obtain ⟨a,ha,hne⟩ := hnot
  obtain ⟨j,⟨hj,hja⟩,-⟩ := exists_original_target_normal_index n r k a ha
  have hcenter : Φ.toFun (chartAt (ComplexModel n) (f p.base) (f p.base)) ∈ S := by
    rw [h0]
    exact hS0
  let Φ' := restrictTarget Φ S hSΦ hcenter
  let c : FlatChart n C :=
    { y₀ := f p.base
      k := k
      Φ := Φ'
      hsrc := fun q hq => hΦsrc hq.1
      hflat := fun hz hzΦ => hflat _ ⟨hz,hzΦ.1⟩
      j := j
      hj := hj }
  let c' : FlatChart (n+r) (f ⁻¹' C) :=
    { y₀ := p.base
      k := r+k
      Φ := Ψ
      hsrc := hΨsrc
      hflat := hΨflat
      j := rotateBlocks n r (Fin.castAdd r j)
      hj := by rw [hja]; exact ha }
  have hp : p ∈ c'.source := by
    refine ⟨mem_flatDomain_self Ψ,?_⟩
    change extVal (flatCoord Ψ (rotateBlocks n r (Fin.castAdd r j))) p ≠ 0
    rw [extVal_of_mem hpC,hja]
    exact hne
  refine ⟨R,c,c',rfl,rfl,hp,?_⟩
  intro i hi hi'
  constructor
  · ext w
    change monomial (r+k) (rotateBlocks n r (Fin.castAdd r i)) w ∈ Ψ.target ↔ _
    rw [hΨtarget]
    change fibreFirstSplit n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r i)) w) ∈
      (R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n)) ↔ _
    rw [fibreFirstSplit_monomial]
    rfl
  · intro w hw
    have he := hinv (monomial (r+k) (rotateBlocks n r (Fin.castAdd r i)) w) hw
    rw [adaptedTargetProjection_monomial] at he
    exact he


section CanonicalUnique
variable {n r : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X}

theorem canonical_actualLift_joint_unique
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
      (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    ∀ p q : BlowupSpace (n+r) (f ⁻¹' C), p.base = q.base →
      actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ' p =
      actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ' q → p = q := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  intro p q hbase hG
  by_cases hpC : p.base ∈ f ⁻¹' C
  · obtain ⟨k,-,-,Φ,hΦsrc,h0,hflat⟩ := hC.2 (f p.base) hpC
    obtain ⟨R,c,c',hk,hj,hp,hfam⟩ := exists_original_matching_pivot_family p hpC
      (hf.isSubmersionAt p.base) Φ hΦsrc h0 k (fun z hz => hflat hz.1 hz.2)
    have hj' : c'.k ≤ (rotateBlocks n r (Fin.castAdd r c.j)).val := by rw [← hj]; exact c'.hj
    have hrep : repivot c' (rotateBlocks n r (Fin.castAdd r c.j)) hj' = c' :=
      repivot_eq_self_of_pivot c' _ hj' hj.symm
    obtain ⟨hdom,hpoint⟩ := hfam c.j c.hj hj'
    rw [hrep] at hdom hpoint
    change c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) at hdom
    change ∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w) at hpoint
    have hdrop : MapsTo (adaptedTargetProjection n r) c'.target c.target := by
      intro w hw; rw [hdom] at hw; exact hw.2
    have hpG := canonical_actualLift_eqOn_flatChart hf hCi c c' R hdom hpoint hp
    have hpZ : flatChartMap c c' p ∈ c.source := c.map_target (hdrop (c'.map_source hp))
    have hqC : q.base ∈ f ⁻¹' C := by rw [← hbase]; exact hpC
    have hqdom : q.base ∈ c'.dom := by rw [← hbase]; exact hp.1
    have hnot := BlowupSpace.dirVec_not_mem hqC
    rw [mem_tangentSpace_iff c'.hsrc c'.hflat hqdom hqC] at hnot
    push Not at hnot
    obtain ⟨a,ha,hne⟩ := hnot
    have ha' : r+c.k ≤ a.val := by rwa [hk] at ha
    obtain ⟨i,⟨hi,hia⟩,-⟩ := exists_original_target_normal_index n r c.k a ha'
    have hi' : c'.k ≤ (rotateBlocks n r (Fin.castAdd r i)).val := by rw [hia]; exact ha
    let ci := repivot c i hi
    let ci' := repivot c' (rotateBlocks n r (Fin.castAdd r i)) hi'
    have hqi : q ∈ ci'.source := by
      refine ⟨hqdom,?_⟩
      change extVal (c'.τ (rotateBlocks n r (Fin.castAdd r i))) q ≠ 0
      rw [extVal_of_mem hqC,hia]
      exact hne
    obtain ⟨hdomi,hpointi⟩ := hfam i hi hi'
    have hdropi : MapsTo (adaptedTargetProjection n r) ci'.target ci.target := by
      intro w hw; rw [hdomi] at hw; exact hw.2
    have hqG := canonical_actualLift_eqOn_flatChart hf hCi ci ci' R hdomi hpointi hqi
    have he : flatChartMap ci ci' q = flatChartMap c c' p := hqG.symm.trans (hG.symm.trans hpG)
    have hsupport := matching_pivot_extended_support ci ci' hk rfl hdropi q hqi c.j c.hj
    have hneq : extVal (c'.τ (rotateBlocks n r (Fin.castAdd r c.j))) q ≠ 0 := by
      apply hsupport.mpr
      change extVal (c.τ c.j) (flatChartMap ci ci' q) ≠ 0
      rw [he]
      exact hpZ.2
    have hq : q ∈ c'.source := ⟨hqdom,by rwa [← hj] at hneq⟩
    apply matching_chart_joint_point_unique c c' hk hj hdrop p q hp hq hbase
    exact hpG.symm.trans (hG.trans (canonical_actualLift_eqOn_flatChart hf hCi c c' R hdom hpoint hq))
  · exact eq_of_base_eq_of_not_mem hbase hpC
end CanonicalUnique


section ChosenUnique
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {C : Set X} {π : D → X} {π' : D' → Y}

theorem actualLift_joint_unique
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (p q : D') (hbase : π' p = π' q)
    (hG : actualLift hf hπ hπ' p = actualLift hf hπ hπ' q) : p = q := by
  have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt
    (hf.isSubmersionAt (π' p))
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hnm
  subst m
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) := ⟨(actual_source_centre hf hπ).1⟩
  obtain ⟨a,b,_,hb,he⟩ := exists_actual_comparison_conjugate hf hπ hπ'
  have hbase' : (b p).base = (b q).base := (hb p).trans (hbase.trans (hb q).symm)
  have hG' := congrArg a hG
  rw [he] at hG'
  have heq := canonical_actualLift_joint_unique hf C hπ.1 hπ.2.1 (b p) (b q) hbase'
    (by simpa only [Function.comp_apply,Diffeomorph.apply_symm_apply] using hG')
  exact b.injective heq

theorem existsUnique_actual_compatible_point
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (y : Y) (z : D) (hsquare : π z = f y) :
    ∃! p : D', π' p = y ∧ actualLift hf hπ hπ' p = z := by
  have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hf.isSubmersionAt y)
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hnm
  subst m
  obtain ⟨p,hpbase,hpG⟩ := exists_actual_compatible_point hf hπ hπ' y z hsquare
  refine ⟨p,⟨hpbase,hpG⟩,?_⟩
  intro q hq
  exact actualLift_joint_unique hf hπ hπ' q p (hq.1.trans hpbase.symm) (hq.2.trans hpG.symm)
end ChosenUnique

end
end Hironaka.HironakaSmoothSubmersionBlowupPivotCompatibility
