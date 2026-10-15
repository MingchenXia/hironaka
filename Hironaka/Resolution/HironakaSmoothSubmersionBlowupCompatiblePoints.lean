/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionBlowupChoiceGeometry
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionBlowupCompatiblePoints
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates BlowupMonomialCharts
  BlowupConstruction BlowupSpaceTangent HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaSmoothSubmersionAdaptedBlowupCharts HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionUniversalBlowupChartEquality HironakaSmoothSubmersionBlowupChoiceGeometry
noncomputable section
section LocalPair
variable {n r : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]

theorem exists_actual_target_matching_point {f : Y → X} {y : Y} {C : Set X}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (hyC : f y ∈ C) (z : BlowupSpace n C) (hb : z.base = f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) (k : ℕ)
    (hflat : ∀ q ∈ flatDomain Φ, q ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f y) q) ∈ complexCoordinatePlane n k) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n))
      (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C))
      (p : BlowupSpace (n+r) (f ⁻¹' C)),
      (0 : ComplexModel r) ∈ R ∧ (0 : ComplexModel n) ∈ S ∧
      c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) ∧
      (∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w)) ∧
      z ∈ c.source ∧ p ∈ c'.source ∧ p.base = y ∧ flatChartMap c c' p = z := by
  have hzC : z.base ∈ C := by rw [hb]; exact hyC
  have hzflat : z.base ∈ flatDomain Φ := by rw [hb]; exact mem_flatDomain_self Φ
  have hnot := BlowupSpace.dirVec_not_mem hzC
  rw [mem_tangentSpace_iff hΦsrc (fun hz hΦ => hflat _ ⟨hz,hΦ⟩) hzflat hzC] at hnot
  push Not at hnot
  obtain ⟨j,hj,hjne⟩ := hnot
  obtain ⟨R,S,Ψ,hR0,hS0,hSΦ,hΨsrc,hΨ0,hΨtarget,hd,hinv⟩ :=
    exists_adapted_product_centre_coordinates hf Φ h0 C k hflat
  have hcenter : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) ∈ S := by
    rw [h0]; exact hS0
  let Φ' := restrictTarget Φ S hSΦ hcenter
  let c : FlatChart n C :=
    { y₀ := f y, k := k, Φ := Φ', hsrc := fun q hq => hΦsrc hq.1
      hflat := fun hz hzΦ => hflat _ ⟨hz,hzΦ.1⟩, j := j, hj := hj }
  let c' : FlatChart (n+r) (f ⁻¹' C) :=
    { y₀ := y, k := r+k, Φ := Ψ, hsrc := hΨsrc
      hflat := fun hz hzΨ => (hd _ ⟨hz,hzΨ⟩).2.2
      j := rotateBlocks n r (Fin.castAdd r j), hj := by rw [rotateBlocks_target]; omega }
  have hs : c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) := by
    ext w
    change monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w ∈ Ψ.target ↔ _
    rw [hΨtarget]
    change fibreFirstSplit n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) ∈
      (R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n)) ↔ _
    rw [fibreFirstSplit_monomial]
    rfl
  have hpoint : ∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w) := by
    intro w hw
    have he := hinv (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) hw
    rw [adaptedTargetProjection_monomial] at he
    exact he
  have hcz : z ∈ c.source := by
    refine ⟨?_,?_⟩
    · rw [hb]
      exact ⟨mem_chart_source _ _,Φ.center_mem_source,hcenter⟩
    · change extVal (flatCoord Φ j) z ≠ 0
      rw [extVal_of_mem hzC]
      exact hjne
  let w := (fibreFirstSplit n r).symm (0,c.toFun z)
  have hw : w ∈ c'.target := by
    rw [hs]
    change fibreFirstSplit n r ((fibreFirstSplit n r).symm (0,c.toFun z)) ∈ (R : Set (ComplexModel r)) ×ˢ c.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨hR0,c.map_source hcz⟩
  have hwmono : monomial c'.k c'.j w = 0 := by
    apply (fibreFirstSplit n r).injective
    change fibreFirstSplit n r (monomial (r+k) (rotateBlocks n r (Fin.castAdd r j)) w) = fibreFirstSplit n r 0
    rw [fibreFirstSplit_monomial,map_zero]
    have hsw : fibreFirstSplit n r w = (0,c.toFun z) :=
      (fibreFirstSplit n r).apply_symm_apply _
    have hfib : adaptedFibreProjection n r w = 0 := congrArg Prod.fst hsw
    have hdrop : adaptedTargetProjection n r w = c.toFun z := congrArg Prod.snd hsw
    rw [hfib,hdrop]
    change (0,monomial k j (c.toFun z)) = (0,0)
    have hh := c.flat_pt (c.map_source hcz)
    rw [c.pt_toFun hcz,hb] at hh
    have he : monomial k j (c.toFun z) = 0 := hh.symm.trans h0
    exact congrArg (fun v : ComplexModel n => ((0 : ComplexModel r),v)) he
  let p := c'.invFun w
  have hp : p ∈ c'.source := c'.map_target hw
  have hbase : p.base = y := by
    rw [c'.base_invFun hw]
    change (chartAt (ComplexModel (n+r)) y).symm (Ψ.invFun (monomial c'.k c'.j w)) = y
    rw [hwmono,← hΨ0,Ψ.left_inv _ Ψ.center_mem_source,(chartAt (ComplexModel (n+r)) y).left_inv (mem_chart_source _ _)]
  have hmap : flatChartMap c c' p = z := by
    change c.invFun (adaptedTargetProjection n r (c'.toFun (c'.invFun w))) = z
    rw [c'.right_inv hw]
    have he : adaptedTargetProjection n r w = c.toFun z :=
      congrArg Prod.snd ((fibreFirstSplit n r).apply_symm_apply (0,c.toFun z))
    rw [he,c.left_inv hcz]
  exact ⟨R,S,c,c',p,hR0,hS0,hs,hpoint,hcz,hp,hbase,hmap⟩
end LocalPair
section CanonicalPairs
variable {n r : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X}

theorem exists_canonical_exceptional_compatible_point
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅)
    (y : Y) (z : BlowupSpace n C) (hyC : f y ∈ C) (hz : z.base = f y) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
      (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    ∃ p : BlowupSpace (n+r) (f ⁻¹' C), p.base = y ∧
      actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ' p = z := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  obtain ⟨k,-,-,Φ,hΦsrc,h0,hflat⟩ := hC.2 (f y) hyC
  obtain ⟨R,S,c,c',p,_,_,hs,hpoint,_,hp,hbase,hmap⟩ :=
    exists_actual_target_matching_point (hf.isSubmersionAt y) hyC z hz Φ hΦsrc h0 k
      (fun q hq => hflat hq.1 hq.2)
  refine ⟨p,hbase,?_⟩
  exact (canonical_actualLift_eqOn_flatChart hf hCi c c' R hs hpoint hp).trans hmap

theorem exists_canonical_compatible_point
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅)
    (y : Y) (z : BlowupSpace n C) (hz : z.base = f y) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
      (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    ∃ p : BlowupSpace (n+r) (f ⁻¹' C), p.base = y ∧
      actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ' p = z := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  by_cases hyC : f y ∈ C
  · exact exists_canonical_exceptional_compatible_point hf C hC hCi y z hyC hz
  · let p : BlowupSpace (n+r) (f ⁻¹' C) := offPoint y hyC
    refine ⟨p,rfl,?_⟩
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
      (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    let G := actualLift (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ'
    have hproj : (G p).base = f y := congrFun (actualLift_proj_comm (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ') p
    exact eq_of_base_eq_of_not_mem (hproj.trans hz.symm) (by rw [hproj]; exact hyC)
end CanonicalPairs

section ChosenPairs
variable {n r : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} (n+r)}
  {f : Y → X} {C : Set X} {π : D → X} {π' : D' → Y}

theorem exists_actual_compatible_point
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong (n+r) (f ⁻¹' C) π')
    (y : Y) (z : D) (hz : π z = f y) :
    ∃ p : D', π' p = y ∧ actualLift hf hπ hπ' p = z := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) := ⟨(actual_source_centre hf hπ).1⟩
  obtain ⟨a,b,ha,hb,he⟩ := exists_actual_comparison_conjugate hf hπ hπ'
  have haz : (a z).base = f y := (ha z).trans hz
  obtain ⟨P,hP,hGP⟩ := exists_canonical_compatible_point hf C hπ.1 hπ.2.1 y (a z) haz
  refine ⟨b.symm P,?_,?_⟩
  · have hh : π' (b.symm P) = P.base := by
      simpa only [Diffeomorph.apply_symm_apply,BlowupConstruction.blowupProj] using (hb (b.symm P)).symm
    exact hh.trans hP
  · rw [he]
    change a.symm (actualLift (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf
      (isBlowupAlong_blowupProj (n := n) (C := C) hπ.2.1)
      (isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) (actual_source_centre hf hπ).2) (b (b.symm P))) = z
    rw [Diffeomorph.apply_symm_apply,hGP,Diffeomorph.symm_apply_apply]

theorem actualLift_surjective
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong (n+r) (f ⁻¹' C) π')
    (hs : Function.Surjective f) : Function.Surjective (actualLift hf hπ hπ') := by
  intro z
  obtain ⟨y,hy⟩ := hs (π z)
  obtain ⟨p,_,hp⟩ := exists_actual_compatible_point hf hπ hπ' y z hy.symm
  exact ⟨p,hp⟩
end ChosenPairs
end
end Hironaka.HironakaSmoothSubmersionBlowupCompatiblePoints
