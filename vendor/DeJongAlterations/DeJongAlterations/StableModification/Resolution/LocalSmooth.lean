import DeJongAlterations.Algebra.NodeFlatPresentation
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Complete local rings at smooth points of a flat family of curves

Let `A` be a complete Noetherian local ring with residue field `κ` and `B` a flat complete
Noetherian local `A`-algebra whose closed fibre `B/𝔪_A B` is `κ[[w]]`. Then `B ≅ A[[w]]`, the
variable going to any lift of `w`. This is the smooth-point half of de Jong's local description of
a semi-stable curve over a regular base, used in 4.23–4.25
(de Jong 1996, `references/dejong96-alterations/tex/page-0026.tex`: at a smooth point of
`f : X → Y` the complete local ring is `Ô_{Y,y}[[w]]`), and the analogue for smooth points of
Codex's split node presentation `Algebra.NodeFlatPresentation.exists_split_normal_form`
(de Jong 2.23).

If moreover `ρ : B → A` is an `A`-algebra retraction (the complete local ring of a section
`τ : Y → X` through the point), the variable can be chosen in `ker ρ`, so that the section is
`w = 0` (de Jong 4.23: the sections `τ_i` map into the smooth locus; 4.25 (i)).

## Main results

* `smoothPresentationEquiv`: for a lift `b ∈ B` of the closed-fibre variable, the evaluation
  `A[[w]] → B`, `w ↦ b`, is an `A`-algebra isomorphism.
* `exists_smooth_normal_form`: `B ≃ₐ[A] A[[w]]`.
* `exists_smooth_normal_form_of_retraction`: given an `A`-algebra retraction `ρ : B → A`, there is
  `B ≃ₐ[A] A[[w]]` carrying `ker ρ` onto `(w)`.

The proof follows Codex's split node presentation: completeness of `A` makes the evaluation
surjective (it is so on closed fibres), and flatness of `B` gives `K ∩ 𝔪_A A[[w]] = 𝔪_A K` for its
kernel `K`, so `K = 𝔪_A K = 0` by Nakayama.
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open IsLocalRing Algebra.NodeFlatPresentation

universe u v

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]
  (B : Type v) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
  [IsAdicComplete (maximalIdeal B) B]

/-- The closed-fibre map `A[[w]] → κ[[w]] ≅ B/𝔪_A B` determined by a smooth closed-fibre model. -/
def smoothFiberMap (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A]
    ClosedFiber A B) : PowerSeries A →+* ClosedFiber A B :=
  e.toRingHom.comp (PowerSeries.map (Ideal.Quotient.mk (maximalIdeal A)))

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsLocalRing B] [IsNoetherianRing B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] [IsAdicComplete (maximalIdeal B) B] in
theorem smoothFiberMap_C (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A]
    ClosedFiber A B) (a : A) :
    smoothFiberMap A B e (PowerSeries.C a) =
      Ideal.Quotient.mk (closedFiberIdeal A B) (algebraMap A B a) := by
  change e (PowerSeries.map _ (PowerSeries.C a)) = _
  rw [PowerSeries.map_C]
  change e (algebraMap (CoefficientResidue A) (PowerSeries (CoefficientResidue A))
    (Ideal.Quotient.mk (maximalIdeal A) a)) = _
  rw [e.commutes]
  rfl

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsLocalRing B] [IsNoetherianRing B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] [IsAdicComplete (maximalIdeal B) B] in
theorem smoothFiberMap_surjective (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A]
    ClosedFiber A B) : Function.Surjective (smoothFiberMap A B e) :=
  e.surjective.comp (map_surjective (σ := Unit) _ Ideal.Quotient.mk_surjective)

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] [IsAdicComplete (maximalIdeal B) B] in
/-- A lift of the closed-fibre variable lies in the maximal ideal of `B`. -/
theorem smoothLift_mem (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A]
    ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) : b ∈ maximalIdeal B := by
  intro hu
  have hq := hu.map (Ideal.Quotient.mk (closedFiberIdeal A B))
  rw [hb] at hq
  have hn := hq.map e.symm.toRingHom
  change IsUnit (e.symm (e PowerSeries.X)) at hn
  rw [AlgEquiv.symm_apply_apply] at hn
  exact PowerSeries.X_prime.not_isUnit hn

/-- The evaluation `A[[w]] → B`, `w ↦ b`, at a lift `b` of the closed-fibre variable. -/
def smoothPresentationMap (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A]
    ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    PowerSeries A →ₐ[A] B :=
  evaluation (σ := Unit) (maximalIdeal B) (fun _ => b) (fun _ => smoothLift_mem A B e b hb)

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] in
@[simp]
theorem smoothPresentationMap_C (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A]
    ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) (a : A) :
    smoothPresentationMap A B e b hb (PowerSeries.C a) = algebraMap A B a :=
  evaluation_C _ _ _ _

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] in
@[simp]
theorem smoothPresentationMap_X (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A]
    ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    smoothPresentationMap A B e b hb PowerSeries.X = b :=
  evaluation_X (σ := Unit) _ _ _ ()

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [Module.Flat A B] in
/-- On closed fibres the evaluation is the given model. -/
theorem smoothPresentationMap_closedFiber
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    (Ideal.Quotient.mk (closedFiberIdeal A B)).comp (smoothPresentationMap A B e b hb).toRingHom =
      smoothFiberMap A B e := by
  let : IsNoetherianRing (ClosedFiber A B) := isNoetherianRing_of_surjective B _
    (Ideal.Quotient.mk (closedFiberIdeal A B)) Ideal.Quotient.mk_surjective
  apply formal_hom_ext (σ := Unit) (maximalIdeal (ClosedFiber A B))
  · intro a
    change Ideal.Quotient.mk _ (smoothPresentationMap A B e b hb (PowerSeries.C a)) =
      smoothFiberMap A B e (PowerSeries.C a)
    rw [smoothPresentationMap_C, smoothFiberMap_C]
  · intro i
    change Ideal.Quotient.mk _ (smoothPresentationMap A B e b hb PowerSeries.X) =
      smoothFiberMap A B e PowerSeries.X
    rw [smoothPresentationMap_X, hb]
    change e PowerSeries.X = e (PowerSeries.map _ PowerSeries.X)
    rw [PowerSeries.map_X]
  · intro i
    change Ideal.Quotient.mk _ (smoothPresentationMap A B e b hb PowerSeries.X) ∈ _
    rw [smoothPresentationMap_X]
    let := IsLocalHom.of_surjective (Ideal.Quotient.mk (closedFiberIdeal A B))
      Ideal.Quotient.mk_surjective
    exact map_nonunit _ _ (smoothLift_mem A B e b hb)

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing B]
  [IsLocalHom (algebraMap A B)] [Module.Flat A B] in
/-- The coefficient ideal `𝔪_A A[[w]]` is carried onto `𝔪_A B`. -/
theorem smoothPresentationMap_image_coefficientIdeal
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    ((maximalIdeal A).map (PowerSeries.C : A →+* PowerSeries A)).map
      (smoothPresentationMap A B e b hb).toRingHom = closedFiberIdeal A B := by
  rw [Ideal.map_map]
  apply congrArg (fun f : A →+* B => (maximalIdeal A).map f)
  ext a
  exact smoothPresentationMap_C A B e b hb a

omit [Module.Flat A B] in
/-- Completeness of `A` upgrades surjectivity on closed fibres to surjectivity. -/
theorem smoothPresentationMap_surjective
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    Function.Surjective (smoothPresentationMap A B e b hb) := by
  let M : Ideal (PowerSeries A) := (maximalIdeal A).map PowerSeries.C
  let : IsPrecomplete M (PowerSeries A) :=
    isPrecomplete_extended (σ := Unit) (maximalIdeal A) (IsNoetherian.noetherian _)
  have hm : M.map (smoothPresentationMap A B e b hb).toRingHom = closedFiberIdeal A B :=
    smoothPresentationMap_image_coefficientIdeal A B e b hb
  let : IsHausdorff (M.map (smoothPresentationMap A B e b hb).toRingHom) B :=
    IsHausdorff.of_le_jacobson _ _ (by
      rw [hm]
      exact (map_maximalIdeal_le (algebraMap A B)).trans (maximalIdeal_le_jacobson _))
  apply surjective_of_mk_map_comp_surjective (I := M) (smoothPresentationMap A B e b hb).toRingHom
  rw [hm, smoothPresentationMap_closedFiber]
  exact smoothFiberMap_surjective A B e

/-- Flatness of `B` and Nakayama make the evaluation injective. -/
theorem smoothPresentationMap_injective
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    Function.Injective (smoothPresentationMap A B e b hb) := by
  let φ := smoothPresentationMap A B e b hb
  let M : Ideal (PowerSeries A) := (maximalIdeal A).map PowerSeries.C
  let K : Ideal (PowerSeries A) := RingHom.ker φ.toRingHom
  have hφ : Function.Surjective φ := smoothPresentationMap_surjective A B e b hb
  have hinter : K ⊓ M = M * K := ker_inf_extended φ hφ (maximalIdeal A)
  have hKM : K ≤ M := by
    intro x hx
    change φ x = 0 at hx
    have h1 : smoothFiberMap A B e x = 0 := by
      rw [← smoothPresentationMap_closedFiber A B e b hb]
      change Ideal.Quotient.mk _ (φ x) = 0
      rw [hx, map_zero]
    have h2 : PowerSeries.map (Ideal.Quotient.mk (maximalIdeal A)) x = 0 :=
      (map_eq_zero_iff _ e.injective).mp h1
    have hk := ker_coefficientReduction (σ := Unit) (maximalIdeal A) (IsNoetherian.noetherian _)
    change x ∈ (maximalIdeal A).map (MvPowerSeries.C : A →+* MvPowerSeries Unit A)
    rw [← hk]
    exact h2
  have hK : K ≤ M • K := by
    intro x hx
    rw [Ideal.smul_eq_mul, ← hinter]
    exact ⟨hx, hKM hx⟩
  have hMmax : M ≤ maximalIdeal (PowerSeries A) := by
    intro f hf
    have hc := coeff_mem_of_mem_extended (σ := Unit) (maximalIdeal A) hf 0
    change MvPowerSeries.constantCoeff f ∈ maximalIdeal A at hc
    intro hu
    exact hc ((MvPowerSeries.isUnit_iff_constantCoeff).mp hu)
  have hK0 : K = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot M K (IsNoetherian.noetherian K) hK
      (hMmax.trans (maximalIdeal_le_jacobson _))
  exact (injective_iff_map_eq_zero φ).mpr fun x hx =>
    (Submodule.mem_bot _).mp (hK0 ▸ (show x ∈ K from hx))

/-- **Smooth points (de Jong 4.25 (i)).** For a lift `b` of the closed-fibre variable, the
evaluation `A[[w]] → B`, `w ↦ b`, is an `A`-algebra isomorphism. -/
def smoothPresentationEquiv
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    PowerSeries A ≃ₐ[A] B :=
  AlgEquiv.ofBijective (smoothPresentationMap A B e b hb)
    ⟨smoothPresentationMap_injective A B e b hb, smoothPresentationMap_surjective A B e b hb⟩

@[simp]
theorem smoothPresentationEquiv_X
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (b : B)
    (hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X) :
    smoothPresentationEquiv A B e b hb PowerSeries.X = b :=
  smoothPresentationMap_X A B e b hb

/-- **Smooth points (de Jong 4.25 (i)).** A flat complete local `A`-algebra with closed fibre
`κ[[w]]` is `A[[w]]`. -/
theorem exists_smooth_normal_form
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    Nonempty (B ≃ₐ[A] PowerSeries A) := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e PowerSeries.X)
  exact ⟨(smoothPresentationEquiv A B e b hb).symm⟩

/-- **Smooth points with a section (de Jong 4.23, 4.25 (i)).** Given an `A`-algebra retraction
`ρ : B → A` (the complete local ring of a section `τ` through the point), there is an `A`-algebra
isomorphism `B ≃ A[[w]]` carrying `ker ρ` (the ideal of `τ`) onto `(w)`. -/
theorem exists_smooth_normal_form_of_retraction
    (e : PowerSeries (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B)
    (ρ : B →ₐ[A] A) :
    ∃ φ : B ≃ₐ[A] PowerSeries A,
      (RingHom.ker ρ.toRingHom).map φ = Ideal.span {PowerSeries.X} := by
  obtain ⟨b₀, hb₀⟩ := Ideal.Quotient.mk_surjective (e PowerSeries.X)
  -- `ρ` is local: `ρ⁻¹(𝔪_A)` is a maximal ideal of the local ring `B`.
  have hρloc : ∀ y ∈ maximalIdeal B, ρ y ∈ maximalIdeal A := by
    intro y hy
    by_contra hny
    have hu : IsUnit (ρ y) := by
      by_contra hnu
      exact hny hnu
    have hyu : IsUnit (y * algebraMap A B (hu.unit⁻¹ : Aˣ)) ∨
        IsUnit (1 - y * algebraMap A B (hu.unit⁻¹ : Aˣ)) :=
      IsLocalRing.isUnit_or_isUnit_one_sub_self _
    rcases hyu with hyu | hyu
    · exact hy (isUnit_of_mul_isUnit_left hyu)
    · have := hyu.map ρ
      rw [map_sub, map_one, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        IsUnit.mul_val_inv, sub_self] at this
      exact not_isUnit_zero this
  let b : B := b₀ - algebraMap A B (ρ b₀)
  have hb : Ideal.Quotient.mk (closedFiberIdeal A B) b = e PowerSeries.X := by
    have hmem : algebraMap A B (ρ b₀) ∈ closedFiberIdeal A B :=
      Ideal.mem_map_of_mem _ (hρloc b₀ (smoothLift_mem A B e b₀ hb₀))
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, sub_zero, hb₀]
  have hρb : ρ b = 0 := by
    simp only [b, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  let Φ := smoothPresentationEquiv A B e b hb
  -- `ρ ∘ Φ` is the constant coefficient.
  have hcomp : ρ.toRingHom.comp (Φ : PowerSeries A →+* B) =
      (PowerSeries.constantCoeff : PowerSeries A →+* A) := by
    apply formal_hom_ext (σ := Unit) (maximalIdeal A)
    · intro a
      change ρ (Φ (PowerSeries.C a)) = PowerSeries.constantCoeff (PowerSeries.C a)
      change ρ (smoothPresentationMap A B e b hb (PowerSeries.C a)) = _
      rw [smoothPresentationMap_C, AlgHom.commutes, PowerSeries.constantCoeff_C]
      rfl
    · intro i
      change ρ (Φ PowerSeries.X) = PowerSeries.constantCoeff PowerSeries.X
      rw [smoothPresentationEquiv_X, hρb, PowerSeries.constantCoeff_X]
    · intro i
      change ρ (Φ PowerSeries.X) ∈ maximalIdeal A
      rw [smoothPresentationEquiv_X, hρb]
      exact Ideal.zero_mem _
  refine ⟨Φ.symm, ?_⟩
  ext F
  constructor
  · intro hF
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Φ.symm.surjective).mp hF
    have h0 : PowerSeries.constantCoeff (Φ.symm y) = 0 := by
      rw [← hcomp]
      change ρ (Φ (Φ.symm y)) = 0
      rw [AlgEquiv.apply_symm_apply]
      exact hy
    exact Ideal.mem_span_singleton.mpr (PowerSeries.X_dvd_iff.mpr h0)
  · intro hF
    have h0 : PowerSeries.constantCoeff F = 0 :=
      PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp hF)
    have hy : Φ F ∈ RingHom.ker ρ.toRingHom := by
      change ρ (Φ F) = 0
      rw [← h0, ← hcomp]
      rfl
    have := Ideal.mem_map_of_mem (Φ.symm : B →+* PowerSeries A) hy
    rwa [show (Φ.symm : B →+* PowerSeries A) (Φ F) = F from Φ.symm_apply_apply F] at this

end DeJongAlterations.StableModification.Resolution
