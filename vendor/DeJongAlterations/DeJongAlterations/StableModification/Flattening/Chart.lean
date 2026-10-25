import DeJongAlterations.StableModification.Flattening.Torsion
import DeJongAlterations.StableModification.DeJong.Interface
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Strict transforms on affine charts

Let `w : W → S` and `ψ : S₁ → S` be morphisms with `S₁` integral, with generic point `η`, and let
`X = W ×_S S₁`. For affine opens `U ⊆ S`, `U_W ⊆ w⁻¹ U` and `O ⊆ ψ⁻¹ U`, the chart
`P = U_W ×_U O` of `X` is affine with ring `Γ(U_W) ⊗_{Γ(U)} Γ(O)` (`isAffineOpen_chart`,
`isPushout_chart`), and the ideal of the strict transform `strictTransform w ψ` (the
scheme-theoretic closure of the generic fibre `X_η`, de Jong 2.18, Temkin §3.4) on `P` is the
`Γ(O)`-torsion of `Γ(P)` (`mem_strictTransform_ideal_chart_iff`): the generic fibre over the
chart is `Spec (Γ(P) ⊗_{Γ(O)} κ(η))`, and `Γ(O) → κ(η)` inverts every nonzero element.

Consequently flatness of the strict transform can be checked on such charts, where it is the
flatness of `Γ(P) ⧸ torsion` over `Γ(O)`; and by `Flattening.flat_quotient_of_isPushout` it
follows from the flatness of `(F ⊗_{Γ(U)} Γ(U_W)) ⧸ torsion` over a domain `F` with an injective
map `F → Γ(O)` over `Γ(U)` (`flat_strictTransform_of_forall`, blueprint
`lem:sm-strict-transform-local`). This is how the flat models produced over the valuation rings
(`Flattening.Valuation`) spread to an alteration of the base.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

namespace DeJongAlterations.StableModification.Flattening

universe u

open DeJong

/-- Morphisms out of the spectrum of a residue field are quasi-compact (the source is a point). -/
instance quasiCompact_fromSpecResidueField {X : Scheme.{u}} (x : X) :
    QuasiCompact (X.fromSpecResidueField x) := by
  have : Subsingleton (Spec (X.residueField x)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (X.residueField x)))
  exact ⟨fun _ _ _ => (Set.subsingleton_of_subsingleton).isCompact⟩

variable {W S S₁ : Scheme.{u}} (w : W ⟶ S) (ψ : S₁ ⟶ S)

/-- The chart `U_W ×_S O` of `W ×_S S₁` for opens `U_W ⊆ W` and `O ⊆ S₁`. -/
def chart (UW : W.Opens) (O : S₁.Opens) : (pullback w ψ).Opens :=
  pullback.fst w ψ ⁻¹ᵁ UW ⊓ pullback.snd w ψ ⁻¹ᵁ O

lemma chart_le_fst (UW : W.Opens) (O : S₁.Opens) : chart w ψ UW O ≤ pullback.fst w ψ ⁻¹ᵁ UW :=
  inf_le_left

lemma chart_le_snd (UW : W.Opens) (O : S₁.Opens) : chart w ψ UW O ≤ pullback.snd w ψ ⁻¹ᵁ O :=
  inf_le_right

variable {w ψ} {U : S.Opens} (hU : IsAffineOpen U) {UW : W.Opens} (hUW : IsAffineOpen UW)
  (hUWU : UW ≤ w ⁻¹ᵁ U) {O : S₁.Opens} (hO : IsAffineOpen O) (hOU : O ≤ ψ ⁻¹ᵁ U)

include hU hUW hUWU hO hOU in
/-- The chart `U_W ×_U O` of affine opens over an affine open is affine. -/
lemma isAffineOpen_chart : IsAffineOpen (chart w ψ UW O) := by
  have : IsAffine U := hU
  have : IsAffine UW := hUW
  have : IsAffine O := hO
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback w ψ) hOU hUWU
    (UY := chart w ψ UW O) rfl
  have : IsAffine (pullback (w.resLE U UW hUWU) (ψ.resLE U O hOU)) := inferInstance
  exact IsAffine.of_isIso H.isoPullback.hom

include hU hUW hUWU hO hOU in
/-- **The ring of a chart is a tensor product**: `Γ(U_W ×_U O) = Γ(U_W) ⊗_{Γ(U)} Γ(O)`. -/
lemma isPushout_chart :
    IsPushout (w.appLE U UW hUWU) (ψ.appLE U O hOU)
      ((pullback.fst w ψ).appLE UW (chart w ψ UW O) (chart_le_fst w ψ UW O))
      ((pullback.snd w ψ).appLE O (chart w ψ UW O) (chart_le_snd w ψ UW O)) :=
  (isIso_pushoutSection_iff (IsPullback.of_hasPullback w ψ) hOU hUWU rfl).1
    (isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback w ψ) hOU hUWU rfl hU hO hUW)

include hU hUW hUWU hO hOU in
/-- **The strict transform on a chart is cut out by torsion.** If `S₁` is integral and `O` is
nonempty, an element of `Γ(U_W ×_U O)` lies in the ideal of the strict transform iff it is killed
by a nonzero element of `Γ(S₁, O)`. -/
theorem mem_strictTransform_ideal_chart_iff [IsIntegral S₁] [Nonempty O]
    (x : Γ(pullback w ψ, chart w ψ UW O)) :
    x ∈ (strictTransform w ψ).ideal ⟨chart w ψ UW O, isAffineOpen_chart hU hUW hUWU hO hOU⟩ ↔
      ∃ a : Γ(S₁, O), a ≠ 0 ∧
        (pullback.snd w ψ).appLE O (chart w ψ UW O) (chart_le_snd w ψ UW O) a * x = 0 := by
  let η := genericPoint S₁
  let f := pullback.snd w ψ
  let P := chart w ψ UW O
  have hP : IsAffineOpen P := isAffineOpen_chart hU hUW hUWU hO hOU
  let j := f.fiberι η
  let t := S₁.fromSpecResidueField η
  have hηO : η ∈ O := by
    obtain ⟨y, hy⟩ := (inferInstance : Nonempty O)
    exact (genericPoint_spec S₁).mem_open_set_iff O.isOpen |>.2 ⟨y, trivial, hy⟩
  have htO : (⊤ : (Spec (S₁.residueField η)).Opens) ≤ t ⁻¹ᵁ O := by
    intro z _
    change t z ∈ O
    have : t z ∈ Set.range t := ⟨z, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at this
    rw [this]
    exact hηO
  have hUY : j ⁻¹ᵁ P = j ⁻¹ᵁ P ⊓ f.fiberToSpecResidueField η ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have H₂ : IsPullback j (f.fiberToSpecResidueField η) f t := IsPullback.of_hasPullback f t
  have hPO : P ≤ f ⁻¹ᵁ O := chart_le_snd w ψ UW O
  have hpush := (isIso_pushoutSection_iff H₂ htO hPO hUY).1
    (isIso_pushoutSection_of_isAffineOpen H₂ htO hPO hUY hO (isAffineOpen_top _) hP)
  -- the map `Γ(S₁, O) → Γ(Spec κ(η), ⊤)` inverts nonzero elements
  have : IsDominant t := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.range_fromSpecResidueField, dense_iff_closure_eq]
    exact (genericPoint_spec S₁).def
  have : IsSchemeTheoreticallyDominant t := .of_isDominant t
  have hinj : Function.Injective (t.appLE O ⊤ htO).hom := by
    have h1 := t.app_injective O
    have heq : t ⁻¹ᵁ O = ⊤ := top_le_iff.1 htO
    have h2 : Function.Injective
        ((Spec (S₁.residueField η)).presheaf.map (homOfLE htO).op) := by
      have : IsIso ((Spec (S₁.residueField η)).presheaf.map (homOfLE htO).op) := by
        have : (homOfLE htO).op = eqToHom (by rw [heq]) := Subsingleton.elim _ _
        rw [this]
        infer_instance
      exact (ConcreteCategory.bijective_of_isIso _).1
    rw [Scheme.Hom.appLE]
    exact h2.comp h1
  let eκ := (Scheme.ΓSpecIso (S₁.residueField η)).commRingCatIsoToRingEquiv
  have : Nontrivial Γ(Spec (S₁.residueField η), ⊤) := eκ.symm.injective.nontrivial
  have hk : ∀ a : Γ(S₁, O), a ≠ 0 → IsUnit (t.appLE O ⊤ htO a) := by
    intro a ha
    have h1 : t.appLE O ⊤ htO a ≠ 0 := by
      rw [Ne, ← map_zero (t.appLE O ⊤ htO).hom]
      exact fun h => ha (hinj h)
    have h2 : eκ (t.appLE O ⊤ htO a) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ eκ.injective]
      exact h1
    exact (MulEquiv.isUnit_map eκ).1 (IsUnit.mk0 _ h2)
  have hker := eq_zero_iff_of_isPushout hpush hk x
  have hj : QuasiCompact j := by
    change QuasiCompact (pullback.fst f t)
    infer_instance
  change x ∈ j.ker.ideal ⟨P, hP⟩ ↔ _
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.app_eq_appLE]
  exact hker

/-- The preimage of a chart in the strict transform lies over `O`. -/
lemma subschemeι_preimage_chart_le (I : (pullback w ψ).IdealSheafData) :
    I.subschemeι ⁻¹ᵁ chart w ψ UW O ≤ (I.subschemeι ≫ pullback.snd w ψ) ⁻¹ᵁ O :=
  fun _ hx => chart_le_snd w ψ UW O hx

include hU hUW hUWU hO hOU in
/-- On a chart, flatness of `Γ(P) ⧸ I(P)` over `Γ(O)` gives flatness of the strict transform over
`S₁` at the points of the chart: the ring of the strict transform over `P` is `Γ(P) ⧸ I(P)`. -/
theorem flat_appLE_strictTransform_chart [IsIntegral S₁]
    (h : RingHom.Flat ((Ideal.Quotient.mk ((strictTransform w ψ).ideal
      ⟨chart w ψ UW O, isAffineOpen_chart hU hUW hUWU hO hOU⟩)).comp
        ((pullback.snd w ψ).appLE O (chart w ψ UW O) (chart_le_snd w ψ UW O)).hom)) :
    RingHom.Flat (((strictTransform w ψ).subschemeι ≫ pullback.snd w ψ).appLE O
      ((strictTransform w ψ).subschemeι ⁻¹ᵁ chart w ψ UW O)
        (subschemeι_preimage_chart_le (UW := UW) (O := O) _)).hom := by
  set I := strictTransform w ψ
  set P : (pullback w ψ).affineOpens := ⟨chart w ψ UW O, isAffineOpen_chart hU hUW hUWU hO hOU⟩
  rw [← Scheme.Hom.appLE_comp_appLE _ _ O (chart w ψ UW O) _ (chart_le_snd w ψ UW O) le_rfl,
    ← Scheme.Hom.app_eq_appLE, show I.subschemeι.app (chart w ψ UW O) = I.subschemeι.app P from rfl,
    I.subschemeι_app P]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rw [RingHom.comp_assoc]
  exact RingHom.Flat.respectsIso.1 _ (I.subschemeObjIso P).symm.commRingCatIsoToRingEquiv h

variable (w ψ) in
/-- **Lemma `lem:sm-strict-transform-local`.** Let `ψ : S₁ → S` with `S₁` integral and
`w : W → S`. Suppose every point of `S₁` has an affine neighbourhood `O`, mapping into an affine
open `U` of `S`, with a domain `F` over `Γ(U)` and an injective map `F → Γ(O)` over `Γ(U)`, such
that `(F ⊗_{Γ(U)} Γ(U_W)) ⧸ torsion` is flat over `F` for affine opens `U_W ⊆ w⁻¹ U` covering
`w⁻¹ U`. Then the strict transform of `W` along `ψ` is flat over `S₁`. -/
theorem flat_strictTransform_of_forall [IsIntegral S₁]
    (H : ∀ s : S₁, ∃ (U : S.Opens) (_ : IsAffineOpen U) (O : S₁.Opens) (_ : IsAffineOpen O)
      (_ : s ∈ O) (hOU : O ≤ ψ ⁻¹ᵁ U) (F : Type u) (_ : CommRing F) (_ : IsDomain F)
      (_ : Algebra Γ(S, U) F) (σ : F →+* Γ(S₁, O)),
      Function.Injective σ ∧ σ.comp (algebraMap Γ(S, U) F) = (ψ.appLE U O hOU).hom ∧
      ∀ y ∈ w ⁻¹ᵁ U, ∃ (UW : W.Opens) (_ : IsAffineOpen UW) (_ : y ∈ UW)
        (hUWU : UW ≤ w ⁻¹ᵁ U),
        letI := (w.appLE U UW hUWU).hom.toAlgebra
        Module.Flat F ((F ⊗[Γ(S, U)] Γ(W, UW)) ⧸
          Submodule.torsion F (F ⊗[Γ(S, U)] Γ(W, UW)))) :
    Flat ((strictTransform w ψ).subschemeι ≫ pullback.snd w ψ) := by
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource RingHom.Flat :=
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).1
  refine (HasRingHomProperty.iff_exists_appLE (P := @Flat) hQ).2 fun z => ?_
  let I := strictTransform w ψ
  obtain ⟨U, hU, O, hO, hsO, hOU, F, _, _, _, σ, hσ, hσg, hW⟩ :=
    H (pullback.snd w ψ (I.subschemeι z))
  have hyU : pullback.fst w ψ (I.subschemeι z) ∈ w ⁻¹ᵁ U := by
    change (pullback.fst w ψ ≫ w) (I.subschemeι z) ∈ U
    rw [pullback.condition]
    exact hOU hsO
  obtain ⟨UW, hUW, hyUW, hUWU, hflat⟩ := hW _ hyU
  have : Nonempty O := ⟨⟨_, hsO⟩⟩
  have hxP : I.subschemeι z ∈ chart w ψ UW O := ⟨hyUW, hsO⟩
  have hP := isAffineOpen_chart hU hUW hUWU hO hOU
  refine ⟨⟨O, hO⟩, ⟨I.subschemeι ⁻¹ᵁ chart w ψ UW O, hP.preimage I.subschemeι⟩, hxP,
    subschemeι_preimage_chart_le I, ?_⟩
  apply flat_appLE_strictTransform_chart hU hUW hUWU hO hOU
  let _ : Algebra Γ(S, U) Γ(W, UW) := (w.appLE U UW hUWU).hom.toAlgebra
  exact flat_quotient_of_isPushout (isPushout_chart hU hUW hUWU hO hOU) rfl σ hσ hσg _
    (mem_strictTransform_ideal_chart_iff hU hUW hUWU hO hOU)

end DeJongAlterations.StableModification.Flattening
