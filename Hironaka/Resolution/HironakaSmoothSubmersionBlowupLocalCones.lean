/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionBlowupCompatiblePoints
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionBlowupLocalCones
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates BlowupMonomialCharts
  BlowupConstruction BlowupSpaceTangent HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaSmoothSubmersionAdaptedBlowupCharts HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionUniversalBlowupChartEquality HironakaSmoothSubmersionBlowupCompatiblePoints
  HironakaSmoothSubmersionGlobalBlowupSubmersion HironakaSmoothSubmersionBlowupChoiceGeometry
noncomputable section

private theorem contMDiffOn_flatCoordinates {n : ℕ} {X : CMfd.{u} n} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun q => Φ.toFun (chartAt (ComplexModel n) x q)) (flatDomain Φ) := by
  intro q hq
  have hΦ : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ.toFun
      (chartAt (ComplexModel n) x q) :=
    (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source hq.2).contMDiffAt
  have hc : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (chartAt (ComplexModel n) x) q :=
    (contMDiffOn_chart (n := ∞)).contMDiffAt ((chartAt (ComplexModel n) x).open_source.mem_nhds hq.1)
  exact (hΦ.comp q hc).contMDiffWithinAt


private theorem flatChart_coordinates_contMDiffOn {n : ℕ} {X : CMfd.{u} n} {C : Set X}
    [Fact (IsClosedSubmanifold n C)] (c : FlatChart n C) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c.toFun c.source := by
  intro q hq
  have hm := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  exact (contMDiffAt_of_mem_maximalAtlas hm hq).contMDiffWithinAt

private theorem flatChart_inverse_contMDiffOn {n : ℕ} {X : CMfd.{u} n} {C : Set X}
    [Fact (IsClosedSubmanifold n C)] (c : FlatChart n C) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c.invFun c.target := by
  intro w hw
  have hm := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  exact (contMDiffAt_symm_of_mem_maximalAtlas hm hw).contMDiffWithinAt

section MatchingCones
variable {n r ℓ : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {P : CMfd.{u} ℓ}
  {f : Y → X} {C : Set X} [Fact (IsClosedSubmanifold n C)]
  [Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C))]

theorem exists_matching_chart_cone (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C))
    (hk : c'.k = r+c.k) (hj : c'.j = rotateBlocks n r (Fin.castAdd r c.j))
    (hd : ∀ q ∈ c'.dom, adaptedTargetProjection n r
      (c'.Φ.toFun (chartAt (ComplexModel (n+r)) c'.y₀ q)) =
      c.Φ.toFun (chartAt (ComplexModel n) c.y₀ (f q)))
    (u : P → Y) (v : P → BlowupSpace n C)
    (hu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ u)
    (hv : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v)
    (hs : ∀ p, (v p).base = f (u p)) (p₀ : P) (hu₀ : u p₀ ∈ c'.dom) (hv₀ : v p₀ ∈ c.source) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ g : P → BlowupSpace (n+r) (f ⁻¹' C),
      ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ g W ∧
      ∀ p ∈ W, g p ∈ c'.source ∧ (g p).base = u p ∧ flatChartMap c c' (g p) = v p := by
  let W : Set P := u ⁻¹' c'.dom ∩ v ⁻¹' c.source
  have hW : IsOpen W := (isOpen_flatDomain c'.Φ |>.preimage hu.continuous).inter
    (c.isOpen_source.preimage hv.continuous)
  have h₀ : p₀ ∈ W := ⟨hu₀,hv₀⟩
  let U : P → ComplexModel (n+r) := fun p => c'.Φ.toFun (chartAt (ComplexModel (n+r)) c'.y₀ (u p))
  let V : P → ComplexModel n := fun p => c.toFun (v p)
  let w : P → ComplexModel (n+r) := fun p => (fibreFirstSplit n r).symm (adaptedFibreProjection n r (U p),V p)
  have hU : ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ U W :=
    (contMDiffOn_flatCoordinates c'.Φ).comp hu.contMDiffOn (fun p hp => hp.1)
  have hV : ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ V W :=
    (flatChart_coordinates_contMDiffOn c).comp hv.contMDiffOn (fun p hp => hp.2)
  have hwmono (p : P) (hp : p ∈ W) : monomial c'.k c'.j (w p) = U p := by
    rw [hk,hj]
    apply (fibreFirstSplit n r).injective
    rw [fibreFirstSplit_monomial]
    have hw : fibreFirstSplit n r (w p) = (adaptedFibreProjection n r (U p),V p) :=
      (fibreFirstSplit n r).apply_symm_apply _
    have hF : adaptedFibreProjection n r (w p) = adaptedFibreProjection n r (U p) := by
      change (fibreFirstSplit n r (w p)).1 = _
      rw [hw]
    have hV' : adaptedTargetProjection n r (w p) = V p := congrArg (fun z : ComplexModel r × ComplexModel n => z.2) hw
    rw [hF,hV']
    have ht := c.flat_pt (c.map_source hp.2)
    rw [c.pt_toFun hp.2,hs] at ht
    have he : monomial c.k c.j (V p) = adaptedTargetProjection n r (U p) :=
      ht.symm.trans (hd (u p) hp.1).symm
    exact Prod.ext rfl he
  have hwt (p : P) (hp : p ∈ W) : w p ∈ c'.target := by
    change monomial c'.k c'.j (w p) ∈ c'.Φ.target
    rw [hwmono p hp]
    exact c'.Φ.mapsTo_toFun hp.1.2
  have hw : ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ w W := by
    have hF : ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel r) ∞
        (fun p => adaptedFibreProjection n r (U p)) W :=
      ((ContinuousLinearMap.fst ℂ (ComplexModel r) (ComplexModel n)).contDiff.contMDiff.comp
        (fibreFirstSplit n r).contDiff.contMDiff).comp_contMDiffOn hU
    exact (fibreFirstSplit n r).symm.contDiff.contMDiff.comp_contMDiffOn (hF.prodMk_space hV)
  let g : P → BlowupSpace (n+r) (f ⁻¹' C) := fun p => c'.invFun (w p)
  have hg : ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ g W :=
    (flatChart_inverse_contMDiffOn c').comp hw (fun p hp => hwt p hp)
  refine ⟨W,hW,h₀,g,hg,?_⟩
  intro p hp
  refine ⟨c'.map_target (hwt p hp),?_,?_⟩
  · rw [c'.base_invFun (hwt p hp)]
    change (chartAt (ComplexModel (n+r)) c'.y₀).symm (c'.Φ.invFun (monomial c'.k c'.j (w p))) = u p
    rw [hwmono p hp]
    exact flatInverse_flat c'.Φ hp.1
  · change c.invFun (adaptedTargetProjection n r (c'.toFun (c'.invFun (w p)))) = v p
    rw [c'.right_inv (hwt p hp)]
    have he : adaptedTargetProjection n r (w p) = V p :=
      congrArg (fun z : ComplexModel r × ComplexModel n => z.2) ((fibreFirstSplit n r).apply_symm_apply _)
    rw [he]
    exact c.left_inv hp.2
omit [Fact (IsClosedSubmanifold n C)] [Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C))] in
theorem matching_chart_joint_point_unique (c : FlatChart n C)
    (c' : FlatChart (n+r) (f ⁻¹' C))
    (hk : c'.k = r+c.k) (hj : c'.j = rotateBlocks n r (Fin.castAdd r c.j))
    (hdrop : MapsTo (adaptedTargetProjection n r) c'.target c.target)
    (p q : BlowupSpace (n+r) (f ⁻¹' C)) (hp : p ∈ c'.source) (hq : q ∈ c'.source)
    (hbase : p.base = q.base) (hmap : flatChartMap c c' p = flatChartMap c c' q) : p = q := by
  have hmono : monomial c'.k c'.j (c'.toFun p) = monomial c'.k c'.j (c'.toFun q) := by
    have h1 := c'.flat_pt (c'.map_source hp)
    have h2 := c'.flat_pt (c'.map_source hq)
    rw [c'.pt_toFun hp,hbase] at h1
    rw [c'.pt_toFun hq] at h2
    exact h1.symm.trans h2
  have hfib : adaptedFibreProjection n r (c'.toFun p) = adaptedFibreProjection n r (c'.toFun q) := by
    have he := congrArg (adaptedFibreProjection n r) hmono
    rw [hk,hj,adaptedFibreProjection_monomial,adaptedFibreProjection_monomial] at he
    exact he
  have hdp : adaptedTargetProjection n r (c'.toFun p) ∈ c.target := hdrop (c'.map_source hp)
  have hdq : adaptedTargetProjection n r (c'.toFun q) ∈ c.target := hdrop (c'.map_source hq)
  have htarget : adaptedTargetProjection n r (c'.toFun p) = adaptedTargetProjection n r (c'.toFun q) := by
    have he := congrArg c.toFun hmap
    change c.toFun (c.invFun (adaptedTargetProjection n r (c'.toFun p))) =
      c.toFun (c.invFun (adaptedTargetProjection n r (c'.toFun q))) at he
    rwa [c.right_inv hdp,c.right_inv hdq] at he
  have he : c'.toFun p = c'.toFun q := (fibreFirstSplit n r).injective (Prod.ext hfib htarget)
  have hh := congrArg c'.invFun he
  rwa [c'.left_inv hp,c'.left_inv hq] at hh

end MatchingCones


private theorem exists_original_matching_cone_charts {n r : ℕ}
    {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X} {y : Y} {C : Set X}
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (hyC : f y ∈ C) (z : BlowupSpace n C) (hb : z.base = f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0) (k : ℕ)
    (hflat : ∀ q ∈ flatDomain Φ, q ∈ C ↔
      Φ.toFun (chartAt (ComplexModel n) (f y) q) ∈ complexCoordinatePlane n k) :
    ∃ (R : TopologicalSpace.Opens (ComplexModel r))
      (c : FlatChart n C) (c' : FlatChart (n+r) (f ⁻¹' C)),
      c'.target = (fibreFirstSplit n r) ⁻¹' ((R : Set (ComplexModel r)) ×ˢ c.target) ∧
      (∀ w ∈ c'.target, f (c'.pt w) = c.pt (adaptedTargetProjection n r w)) ∧
      c'.k = r+c.k ∧ c'.j = rotateBlocks n r (Fin.castAdd r c.j) ∧
      (∀ q ∈ c'.dom, adaptedTargetProjection n r
        (c'.Φ.toFun (chartAt (ComplexModel (n+r)) c'.y₀ q)) =
        c.Φ.toFun (chartAt (ComplexModel n) c.y₀ (f q))) ∧
      y ∈ c'.dom ∧ z ∈ c.source := by
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
  refine ⟨R,c,c',hs,hpoint,rfl,rfl,?_,?_,hcz⟩
  · intro q hq
    exact (hd q hq).2.1
  · exact mem_flatDomain_self Ψ

section OriginalCones
variable {n r ℓ : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {P : CMfd.{u} ℓ} {f : Y → X}

theorem exists_canonical_exceptional_local_cone
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    ∀ (u : P → Y) (v : P → BlowupSpace n C),
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ u →
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v →
    (∀ p, (v p).base = f (u p)) → ∀ p₀ : P, f (u p₀) ∈ C →
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
      (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ g : P → BlowupSpace (n+r) (f ⁻¹' C),
      ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ g W ∧
      ∀ p ∈ W, (g p).base = u p ∧ actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ' (g p) = v p := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  intro u v hu hv hsquare p₀ h₀
  obtain ⟨k,-,-,Φ,hΦsrc,h0,hflat⟩ := hC.2 (f (u p₀)) h₀
  obtain ⟨R,c,c',hdom,hpoint,hk,hj,hd,hu₀,hv₀⟩ :=
    exists_original_matching_cone_charts (hf.isSubmersionAt (u p₀)) h₀ (v p₀) (hsquare p₀)
      Φ hΦsrc h0 k (fun q hq => hflat hq.1 hq.2)
  obtain ⟨W,hW,hW₀,g,hg,hgdict⟩ := exists_matching_chart_cone c c' hk hj hd u v hu hv hsquare p₀ hu₀ hv₀
  refine ⟨W,hW,hW₀,g,hg,?_⟩
  intro p hp
  obtain ⟨hgsrc,hgbase,hgmap⟩ := hgdict p hp
  exact ⟨hgbase,(canonical_actualLift_eqOn_flatChart hf hCi c c' R hdom hpoint hgsrc).trans hgmap⟩

theorem exists_canonical_off_local_cone
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    ∀ (u : P → Y) (v : P → BlowupSpace n C),
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ u →
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v →
    (∀ p, (v p).base = f (u p)) → ∀ p₀ : P, f (u p₀) ∉ C →
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
      (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ g : P → BlowupSpace (n+r) (f ⁻¹' C),
      ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ g W ∧
      ∀ p ∈ W, (g p).base = u p ∧ actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ' (g p) = v p := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  intro u v hu _ hsquare p₀ h₀
  let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
  let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
    (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
  let q₀ : BlowupSpace (n+r) (f ⁻¹' C) := offPoint (u p₀) h₀
  have hq₀ : blowupProj (n := n+r) (C := f ⁻¹' C) q₀ ∉ f ⁻¹' C := h₀
  let a := complementPartial (Z := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hπ' q₀ hq₀
  let W : Set P := u ⁻¹' (f ⁻¹' C)ᶜ
  have hW : IsOpen W := ((hC.1.preimage hf.contMDiff.continuous).isOpen_compl).preimage hu.continuous
  have ht (p : P) (hp : p ∈ W) : u p ∈ a.target := by
    rw [complementPartial_target]; exact hp
  let g : P → BlowupSpace (n+r) (f ⁻¹' C) := fun p => a.symm (u p)
  have hg : ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ g W :=
    (complementPartial_holomorphic (Z := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hπ' q₀ hq₀).2.comp
      hu.contMDiffOn ht
  refine ⟨W,hW,h₀,g,hg,?_⟩
  intro p hp
  have hgs : (g p).base ∉ f ⁻¹' C := by
    have hh := a.map_target (ht p hp)
    rw [complementPartial_source] at hh
    exact hh
  have hbase : (g p).base = u p :=
    (complementPartial_apply (Z := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hπ' q₀ hq₀ hgs).symm.trans
      (a.right_inv (ht p hp))
  refine ⟨hbase,?_⟩
  have hb : (actualLift (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ' (g p)).base = f (u p) := by
    have hh := congrFun (actualLift_proj_comm (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ') (g p)
    exact hh.trans (congrArg f hbase)
  exact eq_of_base_eq_of_not_mem (hb.trans (hsquare p).symm) (by rw [hb]; exact hp)

end OriginalCones


section ChosenCones
variable {n m ℓ : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m} {P : CMfd.{u} ℓ}
  {f : Y → X} {C : Set X} {π : D → X} {π' : D' → Y}

theorem exists_actual_local_cone
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong m (f ⁻¹' C) π')
    (u : P → Y) (v : P → D)
    (hu : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ u)
    (hv : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v)
    (hsquare : ∀ p, π (v p) = f (u p)) (p₀ : P) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ g : P → D',
      ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g W ∧
      ∀ p ∈ W, π' (g p) = u p ∧ actualLift hf hπ hπ' (g p) = v p := by
  have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt
    (hf.isSubmersionAt (u p₀))
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hnm
  subst m
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) := ⟨(actual_source_centre hf hπ).1⟩
  obtain ⟨a,b,ha,hb,he⟩ := exists_actual_comparison_conjugate hf hπ hπ'
  have hav : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ (fun p => a (v p)) :=
    a.contMDiff.comp hv
  have hasquare (p : P) : (a (v p)).base = f (u p) := (ha (v p)).trans (hsquare p)
  let h₀ := isBlowupAlong_blowupProj (n := n) (C := C) hπ.2.1
  let h₀' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) (actual_source_centre hf hπ).2
  have hlocal : ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ g₀ : P → BlowupSpace (n+r) (f ⁻¹' C),
      ContMDiffOn 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (n+r)) ∞ g₀ W ∧
      ∀ p ∈ W, (g₀ p).base = u p ∧ actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf h₀ h₀' (g₀ p) = a (v p) := by
    by_cases hC₀ : f (u p₀) ∈ C
    · exact exists_canonical_exceptional_local_cone hf C hπ.1 hπ.2.1 u (fun p => a (v p))
        hu hav hasquare p₀ hC₀
    · exact exists_canonical_off_local_cone hf C hπ.1 hπ.2.1 u (fun p => a (v p))
        hu hav hasquare p₀ hC₀
  obtain ⟨W,hW,hW₀,g₀,hg₀,hgdict⟩ := hlocal
  refine ⟨W,hW,hW₀,(fun p => b.symm (g₀ p)),b.symm.contMDiff.comp_contMDiffOn hg₀,?_⟩
  intro p hp
  obtain ⟨hbase,hG⟩ := hgdict p hp
  constructor
  · have hh : π' (b.symm (g₀ p)) = (g₀ p).base := by
      simpa only [Diffeomorph.apply_symm_apply,BlowupConstruction.blowupProj] using
        (hb (b.symm (g₀ p))).symm
    exact hh.trans hbase
  · rw [he]
    change a.symm (actualLift (D := CMfd.of (BlowupSpace n C))
      (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf h₀ h₀' (b (b.symm (g₀ p)))) = v p
    rw [Diffeomorph.apply_symm_apply,hG,Diffeomorph.symm_apply_apply]
end ChosenCones

end
end Hironaka.HironakaSmoothSubmersionBlowupLocalCones
