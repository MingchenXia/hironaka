import DeJongAlterations.Geometry.ChowLemma
import DeJongAlterations.Geometry.BlowupProjective
import DeJongAlterations.Geometry.ProperQuasiProjective

/-!
# Full conditional projective Cartier reduction, de Jong 4.4 and 4.6--4.8

Every geometric modification and compactification is constructed by the
released producers. Existence for projective varieties with actual effective
Cartier boundary is the explicit remaining premise. No general alteration
existence theorem is asserted without this premise.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveReduction

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Surjectivity of an actual alteration keeps the actual inverse-image closed set proper. -/
theorem alteration_preimage_ne_top (f : Y ⟶ X) [IsAlteration f]
    (Z : Closeds X) (hZ : Z ≠ ⊤) : Z.preimage f.continuous ≠ ⊤ := by
  have hZset : (Z : Set X) ≠ Set.univ := by
    intro h
    apply hZ
    exact SetLike.coe_injective h
  intro hpre
  apply IsAlteration.preimage_ne_univ f hZset
  exact congrArg (fun W : Closeds Y => (W : Set Y)) hpre

/-- Rewrite only the prescribed subset, then use the proved full-output alteration composition. -/
def compOutput {p : X ⟶ Spec (CommRingCat.of k)} {Z : Set X}
    (f : Y ⟶ X) [IsAlteration f] {W : Set Y} (hW : W = f ⁻¹' Z)
    (d : AlterationWithBoundary (f ≫ p) W) : AlterationWithBoundary p Z :=
  ({ d with
      boundarySupport := by
        rw [← hW]
        exact d.boundarySupport } :
    AlterationWithBoundary (f ≫ p) (f ⁻¹' Z)).comp f

@[simp]
theorem compOutput_compactification {p : X ⟶ Spec (CommRingCat.of k)} {Z : Set X}
    (f : Y ⟶ X) [IsAlteration f] {W : Set Y} (hW : W = f ⁻¹' Z)
    (d : AlterationWithBoundary (f ≫ p) W) :
    (compOutput f hW d).compactification = d.compactification := by cases hW; rfl

@[simp]
theorem compOutput_compactificationStructure {p : X ⟶ Spec (CommRingCat.of k)} {Z : Set X}
    (f : Y ⟶ X) [IsAlteration f] {W : Set Y} (hW : W = f ⁻¹' Z)
    (d : AlterationWithBoundary (f ≫ p) W) :
    (compOutput f hW d).compactificationStructure = d.compactificationStructure := by cases hW; rfl

@[simp]
theorem compOutput_boundary {p : X ⟶ Spec (CommRingCat.of k)} {Z : Set X}
    (f : Y ⟶ X) [IsAlteration f] {W : Set Y} (hW : W = f ⁻¹' Z)
    (d : AlterationWithBoundary (f ≫ p) W) :
    (compOutput f hW d).boundary = d.boundary := by cases hW; rfl

@[simp]
theorem compOutput_alteration {p : X ⟶ Spec (CommRingCat.of k)} {Z : Set X}
    (f : Y ⟶ X) [IsAlteration f] {W : Set Y} (hW : W = f ⁻¹' Z)
    (d : AlterationWithBoundary (f ≫ p) W) :
    (compOutput f hW d).alteration = d.alteration ≫ f := by cases hW; rfl

/-- The exact same compactification retains smoothness, and the actual alteration composite retains generic etaleness. -/
theorem compOutput_genericallyEtale {p : X ⟶ Spec (CommRingCat.of k)} {Z : Set X}
    (f : Y ⟶ X) [IsAlteration f] {W : Set Y} (hW : W = f ⁻¹' Z)
    (d : AlterationWithBoundary (f ≫ p) W)
    (hf : IsGenericallyEtale f) (hd : IsGenericallyEtale d.alteration) :
    IsGenericallyEtale (compOutput f hW d).alteration := by
  rw [compOutput_alteration]
  exact hd.comp hf

/-- Source 4.8: the actual projective Cartier blowup reduces arbitrary closed boundary to the explicit Cartier-case existence premise. -/
theorem reduce_projective_cartier_case
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (Z : Closeds X) (hZ : Z ≠ ⊤)
    (hcartier : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ D : Y.IdealSheafData,
        IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
          Nonempty (AlterationWithBoundary q (D.support : Set Y))) :
    Nonempty (AlterationWithBoundary p (Z : Set X)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨Y, f, E, hproj, hf, _hge, hE, hs⟩ :=
    BlowupProjective.exists_projective_genericallyEtale_alteration_cartierPreimage p hp Z hZ
  let := hf
  let : IsIntegral Y := hf.sourceIntegral
  have hv : IsVariety (f ≫ p) := {}
  have hproper : E.support ≠ ⊤ := by
    rw [hs]
    exact alteration_preimage_ne_top f Z hZ
  obtain ⟨d⟩ := hcartier Y (f ≫ p) hv hproj E hE hproper
  have hset : (E.support : Set Y) = f ⁻¹' (Z : Set X) :=
    congrArg (fun W : Closeds Y => (W : Set Y)) hs
  exact ⟨compOutput f hset d⟩

/-- The actual generically etale Cartier blowup preserves both refinements of the complete output. -/
theorem reduce_projective_cartier_case_refined
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (Z : Closeds X) (hZ : Z ≠ ⊤)
    (hcartier : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ D : Y.IdealSheafData,
        IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
          ∃ d : AlterationWithBoundary q (D.support : Set Y),
            IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure) :
    ∃ d : AlterationWithBoundary p (Z : Set X),
      IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨Y, f, E, hproj, hf, hge, hE, hs⟩ :=
    BlowupProjective.exists_projective_genericallyEtale_alteration_cartierPreimage p hp Z hZ
  let := hf
  let : IsIntegral Y := hf.sourceIntegral
  have hv : IsVariety (f ≫ p) := {}
  have hproper : E.support ≠ ⊤ := by
    rw [hs]
    exact alteration_preimage_ne_top f Z hZ
  obtain ⟨d, hd, hdsm⟩ := hcartier Y (f ≫ p) hv hproj E hE hproper
  have hset : (E.support : Set Y) = f ⁻¹' (Z : Set X) :=
    congrArg (fun W : Closeds Y => (W : Set Y)) hs
  exact ⟨compOutput f hset d, compOutput_genericallyEtale f hset d hge hd, by
    simpa only [compOutput_compactificationStructure] using hdsm⟩

/-- Actual Chow and projective compactification reduce every original variety pair to the explicit projective Cartier-case premise. -/
theorem reduce_to_projective_cartier_case
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (Z : Closeds X) (hZ : Z ≠ ⊤)
    (hcartier : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ D : Y.IdealSheafData,
        IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
          Nonempty (AlterationWithBoundary q (D.support : Set Y))) :
    Nonempty (AlterationWithBoundary p (Z : Set X)) := by
  obtain ⟨Y, π, hπ, hv, hqp⟩ := ChowLemma.exists_quasiProjective_modification p
  let := hπ
  let := hv
  let W := Z.preimage π.continuous
  have hW : W ≠ ⊤ := alteration_preimage_ne_top π Z hZ
  obtain ⟨d⟩ := QuasiProjectiveCompactification.reduce_projective_case (π ≫ p) hqp W hW
    (fun Y q hq hproj T hT => by
      let := hq
      exact reduce_projective_cartier_case q hproj T hT hcartier)
  exact ⟨compOutput π rfl d⟩

/-- The entire actual reduction cone preserves generic etaleness and the same smooth compactification. -/
theorem reduce_to_projective_cartier_case_refined
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (Z : Closeds X) (hZ : Z ≠ ⊤)
    (hcartier : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ D : Y.IdealSheafData,
        IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
          ∃ d : AlterationWithBoundary q (D.support : Set Y),
            IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure) :
    ∃ d : AlterationWithBoundary p (Z : Set X),
      IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure := by
  obtain ⟨Y, π, hπ, hv, hqp⟩ := ChowLemma.exists_quasiProjective_modification p
  let := hπ
  let := hv
  let W := Z.preimage π.continuous
  have hW : W ≠ ⊤ := alteration_preimage_ne_top π Z hZ
  obtain ⟨d, hd, hs⟩ := QuasiProjectiveCompactification.reduce_projective_case_refined
    (π ≫ p) hqp W hW (fun Y q hq hproj T hT => by
      let := hq
      exact reduce_projective_cartier_case_refined q hproj T hT hcartier)
  exact ⟨compOutput π rfl d,
    compOutput_genericallyEtale π rfl d (IsModification.isGenericallyEtale π) hd, by
      simpa only [compOutput_compactificationStructure] using hs⟩

/-- The named full main-theorem proposition follows conditionally from precisely the projective Cartier case. -/
theorem alterationTheorem_of_projective_cartier_case
    (hcartier : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ D : Y.IdealSheafData,
        IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
          Nonempty (AlterationWithBoundary q (D.support : Set Y))) :
    DeJongAlterationTheorem k := by
  intro X p hp Z hZ
  let := hp
  exact reduce_to_projective_cartier_case p Z hZ hcartier

/-- The named perfect-field target remains conditional on the explicit refined Cartier-case premise. -/
theorem perfectAlterationTheorem_of_projective_cartier_case [PerfectField k]
    (hcartier : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ D : Y.IdealSheafData,
        IsEffectiveCartierDivisor D → D.support ≠ ⊤ →
          ∃ d : AlterationWithBoundary q (D.support : Set Y),
            IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure) :
    DeJongPerfectAlterationTheorem k := by
  intro X p hp Z hZ
  let := hp
  exact reduce_to_projective_cartier_case_refined p Z hZ hcartier

/-- Proper varieties admit actual projective Chow modifications over their original field. -/
theorem exists_projective_modification_of_isProper
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] [IsProper p] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X),
      IsModification π ∧ IsVariety (π ≫ p) ∧ IsProjectiveOver (π ≫ p) := by
  obtain ⟨Y, π, hπ, hv, hqp⟩ := ChowLemma.exists_quasiProjective_modification p
  let := hπ
  exact ⟨Y, π, hπ, hv, hqp.isProjective_of_isProper⟩

end DeJongAlterations.Geometry.ProjectiveReduction
