import Hironaka.Geometry.CurveFibrationGenericSectionSpread
import Hironaka.Geometry.CurveFibrationMarkedOpenSections
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Actual generic smooth points construct closed disjoint sections on one dense original open. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationGenericMarksSpread

open CurveFibrationGenericSectionSpread

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Actual distinct smooth generic maps INTERNALLY produce the original common dense open,
genuine closed sections, disjoint entire ranges and all original generic coefficient triangles. -/
theorem exists_smooth_disjoint_spread {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [IsSeparated f]
    {ι : Type u} [Finite ι] (φ : ι → (Spec S.functionField ⟶ X))
    (hφ : ∀ i, φ i ≫ f = S.fromSpecStalk (genericPoint S))
    (hdist : Function.Injective (fun i => φ i (IsLocalRing.closedPoint S.functionField)))
    (hsm : ∀ i, φ i (IsLocalRing.closedPoint S.functionField) ∈ f.smoothLocus) :
    ∃ (V : S.Opens) (hη : genericPoint S ∈ V)
      (ρ : ι → (V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme)),
      Dense (V : Set S) ∧
      (∀ i, ρ i ≫ (f ∣_ V) = 𝟙 V.toScheme ∧ IsClosedImmersion (ρ i)) ∧
      (∀ v : V, Function.Injective (fun i => ρ i v)) ∧
      (∀ i, Set.range ((ρ i) ≫ (f ⁻¹ᵁ V).ι) ⊆ f.smoothLocus) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ρ i)) (Set.range (ρ j))) ∧
      ∀ i, V.fromSpecStalkOfMem (genericPoint S) hη ≫ ρ i ≫ (f ⁻¹ᵁ V).ι = φ i := by
  classical
  obtain ⟨V₀, hη₀, σ, _, hσ, hgeneric⟩ := exists_common_spread f φ hφ
  let ρ₀ : ι → (V₀.toScheme ⟶ (f ⁻¹ᵁ V₀).toScheme) :=
    fun i => relativeSection f V₀ (σ i) (hσ i)
  have hρ₀ (i : ι) : ρ₀ i ≫ (f ∣_ V₀) = 𝟙 V₀.toScheme :=
    relativeSection_snd f V₀ (σ i) (hσ i)
  let (i : ι) : IsClosedImmersion (ρ₀ i) :=
    relativeSection_isClosedImmersion f V₀ (σ i) (hσ i)
  let η₀ : V₀ := ⟨genericPoint S, hη₀⟩
  have hσgeneric (i : ι) : σ i η₀ = φ i (IsLocalRing.closedPoint S.functionField) := by
    have H := congrArg (fun m : Spec S.functionField ⟶ X =>
      m (IsLocalRing.closedPoint S.functionField)) (hgeneric i)
    change σ i (V₀.fromSpecStalkOfMem (genericPoint S) hη₀
      (IsLocalRing.closedPoint S.functionField)) = _ at H
    rwa [genericFactor_closedPoint] at H
  let B : Set V₀ := ⋃ i : ι, ⋃ j : {j : ι // j ≠ i}, {s : V₀ | ρ₀ i s = ρ₀ j.val s}
  have hB : IsClosed B := isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun j =>
      CurveFibrationMarkedOpen.closedSections_equalizer_isClosed (f ∣_ V₀)
        (ρ₀ i) (ρ₀ j.val) (hρ₀ i) (hρ₀ j.val)
  let Wdist : V₀.toScheme.Opens := ⟨Bᶜ, hB.isOpen_compl⟩
  let Wsm : V₀.toScheme.Opens := ⨅ i, (σ i) ⁻¹ᵁ f.smoothLocus
  let W : V₀.toScheme.Opens := Wdist ⊓ Wsm
  have hηW : η₀ ∈ W := by
    constructor
    · intro hbad
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hbad
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      have ha := congrArg (f ⁻¹ᵁ V₀).ι hj
      change (f ⁻¹ᵁ V₀).ι (relativeSection f V₀ (σ i) (hσ i) η₀) =
        (f ⁻¹ᵁ V₀).ι (relativeSection f V₀ (σ j.val) (hσ j.val) η₀) at ha
      rw [relativeSection_apply, relativeSection_apply, hσgeneric, hσgeneric] at ha
      exact j.property (hdist ha).symm
    · change η₀ ∈ ((⨅ i, (σ i) ⁻¹ᵁ f.smoothLocus : V₀.toScheme.Opens) : Set V₀)
      rw [Opens.coe_iInf]
      apply Set.mem_iInter.mpr
      intro i
      change σ i η₀ ∈ f.smoothLocus
      rw [hσgeneric]
      exact hsm i
  let V : S.Opens := V₀.ι ''ᵁ W
  let e : W.toScheme ≅ V.toScheme := V₀.ι.isoImage W
  let j : V.toScheme ⟶ V₀.toScheme := e.inv ≫ W.ι
  have hj : j ≫ V₀.ι = V.ι := V₀.ι.isoImage_inv_ι W
  have hηV : genericPoint S ∈ V := by
    exact ⟨η₀, hηW, rfl⟩
  let τ : ι → (V.toScheme ⟶ X) := fun i => j ≫ σ i
  have hτ (i : ι) : τ i ≫ f = V.ι := by
    dsimp [τ]
    rw [Category.assoc, hσ]
    exact hj
  let ρ : ι → (V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme) :=
    fun i => relativeSection f V (τ i) (hτ i)
  have hρ (i : ι) : ρ i ≫ (f ∣_ V) = 𝟙 V.toScheme :=
    relativeSection_snd f V (τ i) (hτ i)
  have hjW (v : V) : j v ∈ W := (e.inv v).property
  have hτdist (v : V) : Function.Injective (fun i => τ i v) := by
    intro i l hil
    by_contra hne
    have hρeq : ρ₀ i (j v) = ρ₀ l (j v) := by
      apply (f ⁻¹ᵁ V₀).ι.isOpenEmbedding.injective
      rw [relativeSection_apply, relativeSection_apply]
      exact hil
    exact (hjW v).1 (Set.mem_iUnion.mpr ⟨i,
      Set.mem_iUnion.mpr ⟨⟨l, Ne.symm hne⟩, hρeq⟩⟩)
  have hρdist (v : V) : Function.Injective (fun i => ρ i v) := by
    intro i l hil
    apply hτdist v
    have H := congrArg (f ⁻¹ᵁ V).ι hil
    change (f ⁻¹ᵁ V).ι (relativeSection f V (τ i) (hτ i) v) =
      (f ⁻¹ᵁ V).ι (relativeSection f V (τ l) (hτ l) v) at H
    simpa only [relativeSection_apply] using H
  refine ⟨V, hηV, ρ, V.isOpen.dense ⟨genericPoint S, hηV⟩, ?_, hρdist, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hρ i, relativeSection_isClosedImmersion f V (τ i) (hτ i)⟩
  · intro i x hx
    obtain ⟨v, rfl⟩ := hx
    change (f ⁻¹ᵁ V).ι (relativeSection f V (τ i) (hτ i) v) ∈ f.smoothLocus
    rw [relativeSection_apply]
    exact (iInf_le (fun i => (σ i) ⁻¹ᵁ f.smoothLocus) i) (hjW v).2
  · intro i l hil
    rw [Set.disjoint_left]
    rintro x ⟨v, hv⟩ ⟨w, hw⟩
    have hvw : v = w := by
      have H := congrArg (f ∣_ V) (hv.trans hw.symm)
      have hi := congrArg (fun m : V.toScheme ⟶ V.toScheme => m v) (hρ i)
      have hl := congrArg (fun m : V.toScheme ⟶ V.toScheme => m w) (hρ l)
      exact hi.symm.trans (H.trans hl)
    subst w
    exact hil (hρdist v (hv.trans hw.symm))
  · intro i
    change V.fromSpecStalkOfMem (genericPoint S) hηV ≫
      (relativeSection f V (τ i) (hτ i) ≫ (f ⁻¹ᵁ V).ι) = φ i
    rw [relativeSection_fst]
    change V.fromSpecStalkOfMem (genericPoint S) hηV ≫ (j ≫ σ i) = φ i
    have hgj : V.fromSpecStalkOfMem (genericPoint S) hηV ≫ j =
        V₀.fromSpecStalkOfMem (genericPoint S) hη₀ := by
      apply (cancel_mono V₀.ι).mp
      rw [Category.assoc, hj, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [← Category.assoc, hgj]
    exact hgeneric i

end Hironaka.Geometry.CurveFibrationGenericMarksSpread
