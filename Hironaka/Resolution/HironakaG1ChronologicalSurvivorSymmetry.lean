import Hironaka.Resolution.HironakaG1ChronologicalMixedMaxima

/-! # Chronological charts for distinct surviving anchors related by a tower symmetry -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1ChronologicalSurvivorSymmetry

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres ResolutionDriver StepOneTangentChange
  HironakaG1ChronologicalLeafTies HironakaG1ChronologicalMixedMaxima

variable {n : ℕ}

private theorem pullback_comp_record {A B C : CMfd.{0} n}
    (M : MarkedIdeal n C) (hM : M.ideal.IsCoherent) (f : B → C) (g : A → B)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) :
    pullback g (pullback f M) = pullback (f ∘ g) M := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · change (M.E.map (f ⁻¹' ·)).map (g ⁻¹' ·) = M.E.map ((f ∘ g) ⁻¹' ·)
    rw [List.map_map]
    rfl
  · exact (GermIdealTotalTransform.pullback_comp hf hg hM).symm

set_option maxHeartbeats 1000000 in
/-- An isomorphism between actual supported suffixes identifies the
charts at corresponding endpoints. Their source open sets may be
different. Invariance of the full marked record includes the ordered
boundary and yields exact equality after the chart transport. -/
theorem common_chronological_chart_of_tower_symmetry
    {X₁ Y₁ X₂ Y₂ : CMfd.{0} n}
    (K₁ : MarkedIdeal n X₁) (K₂ : MarkedIdeal n X₂)
    (h₁ : K₁.ideal.IsCoherent) (h₂ : K₂.ideal.IsCoherent)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (χ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    (hIso : IsTowerIso φ T₁ T₂ χ)
    (hK : pullback φ K₂ = K₁) (y : Y₁)
    (U₁ : Opens X₁) (U₂ : Opens X₂)
    (hOpen : ∀ x, x ∈ U₁ ↔ φ x ∈ U₂) (hy : T₁.proj y ∈ U₁) :
    let z : openPreimage T₁ U₁ := ⟨y, hy⟩
    ∃ (C₁ : ChronologicalChart (K := K₁) T₁ y (restrict U₁ T₁) z)
      (C₂ : ChronologicalChart (K := K₂) T₂ (χ y) (restrict U₁ T₁) z),
      C₁.record = C₂.record := by
  intro z
  have hEnd := isTowerIso_mem_openPreimage_iff hIso hOpen
  let C₁ : ChronologicalChart (K := K₁) T₁ y (restrict U₁ T₁) z :=
    ⟨U₁, Diffeomorph.refl _ _ ∞, Diffeomorph.refl _ _ ∞, (IsTowerIso.refl_self (restrict U₁ T₁)), rfl⟩
  let C₂ : ChronologicalChart (K := K₂) T₂ (χ y) (restrict U₁ T₁) z :=
    ⟨U₂, diffeoOpens φ U₁ U₂ hOpen,
      diffeoOpens χ (openPreimage T₁ U₁) (openPreimage T₂ U₂) hEnd,
      isTowerIso_restrictOpens hOpen hIso hEnd, rfl⟩
  refine ⟨C₁, C₂, ?_⟩
  change pullback (id : U₁ → U₁) (pullback (Subtype.val : U₁ → X₁) K₁) =
    pullback (diffeoOpens φ U₁ U₂ hOpen) (pullback (Subtype.val : U₂ → X₂) K₂)
  let A := CMfd.of (n := n) U₁
  let B := CMfd.of (n := n) U₂
  have hLeft := pullback_comp_record (A := A) (B := A) (C := X₁) K₁ h₁
    Subtype.val id contMDiff_subtype_val contMDiff_id
  have hRight := pullback_comp_record (A := A) (B := B) (C := X₂) K₂ h₂
    Subtype.val (diffeoOpens φ U₁ U₂ hOpen) contMDiff_subtype_val
    (diffeoOpens φ U₁ U₂ hOpen).contMDiff
  have hMid := pullback_comp_record (A := A) (B := X₁) (C := X₂) K₂ h₂
    φ Subtype.val φ.contMDiff contMDiff_subtype_val
  exact hLeft.trans ((congrArg (pullback (Subtype.val : U₁ → X₁)) hK.symm).trans
    (hMid.trans hRight.symm))


set_option maxHeartbeats 950000 in
/-- A symmetry of a genuine canonical suffix ties the realized recursive
reads at two corresponding survivors, including distinct survivors. -/
theorem recursive_tie_of_canonical_survivor_symmetry
    {k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain k K)
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn k).inv K) T)
    (φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hIso : IsTowerIso φ T T χ) (hRecord : pullback φ K = K)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp)
    (U₁ U₂ : Opens X) (hOpen : ∀ x, x ∈ U₁ ↔ φ x ∈ U₂) (hU : T.proj y ∈ U₁) :
    χ y ∈ (geoTransformAlong K T).cosupp ∧
    (invFamily hn k).inv K T y = (invFamily hn k).inv K T (χ y) := by
  let I := invFamily hn k
  have hTest := I.isInvValue.isGeoTestTower_of_isCanonical hK T hCan
  have hy' : χ y ∈ (geoTransformAlong K T).cosupp := by
    have hCos := IsTowerIso.cosupp_geoTransformAlong φ hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hIso hTest
    rw [hRecord] at hCos
    have hMem : y ∈ χ ⁻¹' (geoTransformAlong K T).cosupp := hCos ▸ hy
    exact hMem
  let L : SelectedLeafRead hn ((I.inv K T y : ValTy k) : WithTop (ValTy k)) :=
    ⟨X,Y,K,T,y,hK,hCan,hy,rfl⟩
  let R : SelectedLeafRead hn ((I.inv K T (χ y) : ValTy k) : WithTop (ValTy k)) :=
    ⟨X,Y,K,T,χ y,hK,hCan,hy',rfl⟩
  obtain ⟨C₁,C₂,hC⟩ := common_chronological_chart_of_tower_symmetry
    K K hK.isWellFormed.isCoherent hK.isWellFormed.isCoherent T T φ χ hIso hRecord y U₁ U₂ hOpen hU
  exact ⟨hy', WithTop.coe_inj.mp
    (SelectedLeafRead.eq_of_sameChart (L.sameChart_of_matching_records R C₁ C₂ hC))⟩

set_option maxHeartbeats 900000 in
/-- A nonfixed surviving maximum generates two distinct actual maximum
anchors under a symmetry of the marked canonical suffix. The two
recursive values agree on their geometrically matched opens. -/
theorem canonical_distinct_max_anchors_of_survivor_symmetry
    {k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain k K)
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn k).inv K) T)
    (φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hIso : IsTowerIso φ T T χ) (hRecord : pullback φ K = K)
    (y : Y) (hMove : y ≠ χ y)
    (hy : y ∈ maxLocus ((invFamily hn k).inv K T) (geoTransformAlong K T).cosupp) :
    ∃ z : Y, y ≠ z ∧ z ∈ maxLocus ((invFamily hn k).inv K T) (geoTransformAlong K T).cosupp ∧
      (invFamily hn k).inv K T z = (invFamily hn k).inv K T y := by
  let I := invFamily hn k
  let D := (geoTransformAlong K T).cosupp
  have hTest := I.isInvValue.isGeoTestTower_of_isCanonical hK T hCan
  have hCos := IsTowerIso.cosupp_geoTransformAlong φ hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hIso hTest
  rw [hRecord] at hCos
  have hMatch : ∀ x : X, x ∈ (⊤ : Opens X) ↔ φ x ∈ (⊤ : Opens X) := fun _ => Iff.rfl
  have hRead (z : Y) (hz : z ∈ D) := recursive_tie_of_canonical_survivor_symmetry hn
    K hK T hCan φ χ hIso hRecord z hz ⊤ ⊤ hMatch (mem_univ _)
  obtain ⟨hy', hValue⟩ := hRead y hy.1
  refine ⟨χ y, hMove, ⟨hy', fun z hz => ?_⟩, hValue.symm⟩
  let w := χ.symm z
  have hw : w ∈ D := by
    change w ∈ (geoTransformAlong K T).cosupp
    rw [hCos]
    change χ (χ.symm z) ∈ D
    simpa only [Diffeomorph.apply_symm_apply] using hz
  have hW := (hRead w hw).2
  change I.inv K T w = I.inv K T (χ (χ.symm z)) at hW
  rw [Diffeomorph.apply_symm_apply] at hW
  exact hW.symm.le.trans ((hy.2 w hw).trans hValue.le)

end
end Hironaka.HironakaG1ChronologicalSurvivorSymmetry
