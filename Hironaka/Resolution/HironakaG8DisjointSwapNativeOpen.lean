import Hironaka.Resolution.HironakaG8DisjointSwapRecord
import Hironaka.Resolution.HironakaG8LabelledNativeOverlap
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Resolution.HironakaG3BoundaryStoppingOpenRestriction

/-! Local native comparison after a disjoint physical swap. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointSwapNativeOpen
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG8DisjointSwapRecord
  HironakaG8LabelledNativeHistory HironakaG8LabelledNativeOverlap HironakaG3EmptyAwareHistory
  HironakaSharpActualCurveComparisonRestriction HironakaNormalCrossingsSeparationChoiceComparison
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance
  HironakaG3BoundaryStoppingOpenRestriction

variable {n : ℕ} {X Y W Z Q : CMfd.{0} n}

private abbrev twice {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q) :
    BlowupTower X Z := .step (.step .refl C π hπ) (π ⁻¹' D) q hq

/-- Restricting to an open which misses either birth makes the two
chronological boundary lists literally equal after filtering empty slots. -/
theorem filtered_ordered_birth_swap_on_open
    (M : MarkedIdeal n X)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : W → X} {r : Q → W}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hCD : Disjoint C D) (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) (U : Opens Z)
    (hMiss : Disjoint (U : Set Z) ((π ∘ q) ⁻¹' C) ∨ Disjoint (U : Set Z) ((π ∘ q) ⁻¹' D)) :
    (((geoTransformAlong M (twice hπ hq)).E.map ((Subtype.val : U → Z) ⁻¹' ·)).filter
      (fun H => decide H.Nonempty)) =
    ((((geoTransformAlong M (twice hρ hr)).E.map (e ⁻¹' ·)).map
      ((Subtype.val : U → Z) ⁻¹' ·)).filter (fun H => decide H.Nonempty)) := by
  obtain ⟨hL,hR⟩ := ordered_boundary_disjoint_swap M hπ hq hρ hr hCD e he
  rw [hL,hR]
  simp only [List.map_append,List.filter_append,List.map_cons,List.map_nil]
  rcases hMiss with hC | hD
  · have h : (Subtype.val : U → Z) ⁻¹' ((π ∘ q) ⁻¹' C) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => disjoint_left.mp hC x.property hx
    rw [h]
    by_cases he : ((Subtype.val : U → Z) ⁻¹' ((π ∘ q) ⁻¹' D)).Nonempty <;> simp [he]
  · have h : (Subtype.val : U → Z) ⁻¹' ((π ∘ q) ⁻¹' D) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => disjoint_left.mp hD x.property hx
    rw [h]
    by_cases he : ((Subtype.val : U → Z) ⁻¹' ((π ∘ q) ⁻¹' C)).Nonempty <;> simp [he]

/-- The complementary birth opens cover the actual swapped endpoint. -/
theorem exists_open_missing_birth
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hD : IsClosed D)
    (hq : IsBlowupAlong n (π ⁻¹' D) q) (hCD : Disjoint C D) (z : Z) :
    ∃ U : Opens Z, z ∈ U ∧
      (Disjoint (U : Set Z) ((π ∘ q) ⁻¹' C) ∨ Disjoint (U : Set Z) ((π ∘ q) ⁻¹' D)) := by
  let f := π ∘ q
  have hf : Continuous f := hπ.contMDiff.continuous.comp hq.contMDiff.continuous
  by_cases hzC : f z ∈ C
  · exact ⟨⟨(f ⁻¹' D)ᶜ,(hD.preimage hf).isOpen_compl⟩,
      fun hzD => disjoint_left.mp hCD hzC hzD,Or.inr disjoint_compl_left⟩
  · exact ⟨⟨(f ⁻¹' C)ᶜ,(hπ.1.1.preimage hf).isOpen_compl⟩,hzC,Or.inl disjoint_compl_left⟩

/-- The literal corresponding open of the reversed endpoint. -/
def swappedOpen (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q) (U : Opens Z) :
    Opens Q := ⟨e.symm ⁻¹' (U : Set Z),U.isOpen.preimage e.symm.continuous⟩

def swappedOpenEquiv (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q) (U : Opens Z) :
    CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (swappedOpen e U) :=
  openRestriction e U (swappedOpen e U) (by
    ext z
    change z ∈ U ↔ e.symm (e z) ∈ U
    rw [e.symm_apply_apply])

private theorem strict_carrier_on_swapped_open
    (A : Set X) (hA : IsClosed A)
    {f : Z → X} {g : Q → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : g ∘ e = f) (U : Opens Z) :
    (Subtype.val : U → Z) ⁻¹' strictTransform n f A =
      (swappedOpenEquiv e U) ⁻¹' ((Subtype.val : swappedOpen e U → Q) ⁻¹' strictTransform n g A) := by
  have hStrict : strictTransform n f A = e ⁻¹' strictTransform n g A := by
    simpa using strictTransform_preimage_of_square (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      e hf hg A hA (fun z => congrFun he z)
  rw [hStrict]
  rfl

/-- The full intrinsic Hilbert–Samuel profile partition of every literal
endpoint open is carried by its actual swap comparison. The assertion
concerns equality loci of profiles, independently of choices of native cut. -/
theorem intrinsic_profile_partition_on_swapped_open
    (A : Set X) (hA : IsClosed A) {f : Z → X} {g : Q → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : g ∘ e = f) (U : Opens Z) (H : ℕ → ℕ) :
    let V := swappedOpen e U
    let Aₗ := (Subtype.val : U → Z) ⁻¹' strictTransform n f A
    let Aᵣ := (Subtype.val : V → Q) ⁻¹' strictTransform n g A
    {x : U | (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) Aₗ) x ℓ) = H} =
      (swappedOpenEquiv e U) ⁻¹'
        {y : V | (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) Aᵣ) y ℓ) = H} := by
  dsimp only
  rw [strict_carrier_on_swapped_open A hA hf hg e he U]
  ext x
  have h := funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any (swappedOpenEquiv e U)
    ((Subtype.val : swappedOpen e U → Q) ⁻¹' strictTransform n g A) x)
  exact congrArg (· = H) h |>.to_iff

/-- Compare actual independently produced labelled native histories
on the same birth-complement open of the two physical orders. Each
history starts with its own full literal ordered boundary. -/
theorem labelled_native_histories_after_swap_on_open
    (hn : 0 < n) (A : Set X) (hA : IsClosed A) (M : MarkedIdeal n X)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : W → X} {r : Q → W}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hCD : Disjoint C D) (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) (U : Opens Z)
    (hMiss : Disjoint (U : Set Z) ((π ∘ q) ⁻¹' C) ∨ Disjoint (U : Set Z) ((π ∘ q) ⁻¹' D)) :
    let V := swappedOpen e U
    let φ := swappedOpenEquiv e U
    let Aₗ := (Subtype.val : U → Z) ⁻¹' strictTransform n (π ∘ q) A
    let Aᵣ := (Subtype.val : V → Q) ⁻¹' strictTransform n (ρ ∘ r) A
    let Eₗ := (geoTransformAlong M (twice hπ hq)).E.map ((Subtype.val : U → Z) ⁻¹' ·)
    let Eᵣ := (geoTransformAlong M (twice hρ hr)).E.map ((Subtype.val : V → Q) ⁻¹' ·)
    (Aₗ ⊆ closure (Aₗ \ ⋃ B ∈ Eₗ, B)) →
    ∀ {Yₗ Yᵣ : CMfd.{0} n} {Tₗ : BlowupTower (CMfd.of (n := n) U) Yₗ}
      {Tᵣ : BlowupTower (CMfd.of (n := n) V) Yᵣ} {Lₗ Lᵣ : List (ℕ → ℕ)},
      LabelledNativeTower n Aₗ Eₗ univ Tₗ Lₗ → LabelledNativeTower n Aᵣ Eᵣ univ Tᵣ Lᵣ →
      ∃ χ : Yₗ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Yᵣ, EmptyAwareTowerIso φ Tₗ Tᵣ χ := by
  dsimp only
  intro hDenseL Yₗ Yᵣ Tₗ Tᵣ Lₗ Lᵣ hL hR
  let φ := swappedOpenEquiv e U
  have hAeq := strict_carrier_on_swapped_open A hA
    (hπ.contMDiff.comp hq.contMDiff) (hρ.contMDiff.comp hr.contMDiff) e he U
  have hB := filtered_ordered_birth_swap_on_open M hπ hq hρ hr hCD e he U hMiss
  have hB' : ((((geoTransformAlong M (twice hρ hr)).E.map (e ⁻¹' ·)).map
      ((Subtype.val : U → Z) ⁻¹' ·))) =
    (((geoTransformAlong M (twice hρ hr)).E.map
      ((Subtype.val : swappedOpen e U → Q) ⁻¹' ·)).map (φ ⁻¹' ·)) := by
    simp only [List.map_map]
    rfl
  rw [hB'] at hB
  let V := swappedOpen e U
  let Aᵣ := (Subtype.val : V → Q) ⁻¹' strictTransform n (ρ ∘ r) A
  let Eₗ := (geoTransformAlong M (twice hπ hq)).E.map ((Subtype.val : U → Z) ⁻¹' ·)
  let Eᵣ := (geoTransformAlong M (twice hρ hr)).E.map ((Subtype.val : V → Q) ⁻¹' ·)
  have hUnion : (⋃ B ∈ Eₗ, B) = φ ⁻¹' (⋃ B ∈ Eᵣ, B) := by
    calc
      _ = ⋃ B ∈ Eₗ.filter (fun B => decide B.Nonempty), B := (biUnion_nonempty_filter Eₗ).symm
      _ = ⋃ B ∈ (Eᵣ.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty), B := by rw [hB]
      _ = ⋃ B ∈ Eᵣ.map (φ ⁻¹' ·), B := biUnion_nonempty_filter _
      _ = _ := (HironakaEmbeddedBoundary.preimage_biUnion_list _ _).symm
  have hDenseR : Aᵣ ⊆ closure (Aᵣ \ ⋃ B ∈ Eᵣ, B) := by
    change (Subtype.val : U → Z) ⁻¹' strictTransform n (π ∘ q) A ⊆
      closure (((Subtype.val : U → Z) ⁻¹' strictTransform n (π ∘ q) A) \ ⋃ B ∈ Eₗ, B) at hDenseL
    rw [hAeq,hUnion,← preimage_sdiff] at hDenseL
    have hClosure := φ.toHomeomorph.preimage_closure (Aᵣ \ ⋃ B ∈ Eᵣ, B)
    change φ ⁻¹' closure _ = closure (φ ⁻¹' _) at hClosure
    rw [← hClosure] at hDenseL
    intro y hy
    obtain ⟨x,rfl⟩ := φ.surjective y
    exact hDenseL hy
  exact labelled_native_history_overlap hn φ hAeq hB hDenseL hDenseR hL hR


end
end Hironaka.HironakaG8DisjointSwapNativeOpen
