import DeJongAlterations.Algebra.NodeFittingOmegaStalk

/-! ORIGINAL chart-relative Ω and ORIGINAL local relative Ω at the SAME original point.
Both native localization coefficient maps are the ACTUAL original section germs, and
local relative coefficients are precisely the ACTUAL original f.stalkMap. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

namespace DeJongAlterations.Geometry.NodeCompletedLocalOriginalStalkOmega

open Algebra.NodeFittingOmegaCharts Algebra.NodeFittingOmegaStalk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (C : Chart f) (x : X) (hx : x ∈ C.source.1)

/-- Native double localization of the ORIGINAL relative module, with no finiteness,
Noetherianity, field, completed model, or supplied output equivalence hypothesis. -/
def chartLocalOmegaEquiv :
    letI := C.algebra f
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI := Algebra.NodeFittingOmegaStalk.stalkAlgebra f x
    (X.presheaf.stalk x ⊗[Γ(X, C.source.1)]
      KaehlerDifferential Γ(S, C.base.1) Γ(X, C.source.1)) ≃ₗ[X.presheaf.stalk x]
        KaehlerDifferential (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  letI := C.algebra f
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := S.presheaf.algebra_section_stalk ⟨f x, C.le_preimage hx⟩
  letI := Algebra.NodeFittingOmegaStalk.stalkAlgebra f x
  letI := chartStalkAlgebra f C hx
  letI := chart_source_tower f C hx
  letI := chart_base_tower f C hx
  letI := C.source.2.isLocalization_stalk ⟨x, hx⟩
  letI := C.base.2.isLocalization_stalk ⟨f x, C.le_preimage hx⟩
  letI : Algebra.FormallyEtale Γ(X, C.source.1) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization
      (C.source.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  letI : Algebra.FormallyEtale Γ(S, C.base.1) (S.presheaf.stalk (f x)) :=
    Algebra.FormallyEtale.of_isLocalization
      (C.base.2.primeIdealOf ⟨f x, C.le_preimage hx⟩).asIdeal.primeCompl
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      Γ(S, C.base.1) Γ(X, C.source.1) (X.presheaf.stalk x)).trans
    (Algebra.NodeFittingOmega.baseEquiv Γ(S, C.base.1) (S.presheaf.stalk (f x)) (X.presheaf.stalk x))

/-- EVERY original section differential retains its SAME original germ in the ORIGINAL
local relative module, with the ENTIRE original local scalar action. -/
theorem chartLocalOmegaEquiv_tmul_D (b : X.presheaf.stalk x) (r : Γ(X, C.source.1)) :
    letI := C.algebra f
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI := Algebra.NodeFittingOmegaStalk.stalkAlgebra f x
    chartLocalOmegaEquiv f C x hx
      (b ⊗ₜ[Γ(X, C.source.1)] KaehlerDifferential.D Γ(S, C.base.1) Γ(X, C.source.1) r) =
      b • KaehlerDifferential.D (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (X.presheaf.germ C.source.1 x hx r) := by
  let := C.algebra f
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let := S.presheaf.algebra_section_stalk ⟨f x, C.le_preimage hx⟩
  let := Algebra.NodeFittingOmegaStalk.stalkAlgebra f x
  let := chartStalkAlgebra f C hx
  let := chart_source_tower f C hx
  let := chart_base_tower f C hx
  let := C.source.2.isLocalization_stalk ⟨x, hx⟩
  let := C.base.2.isLocalization_stalk ⟨f x, C.le_preimage hx⟩
  let : Algebra.FormallyEtale Γ(X, C.source.1) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization
      (C.source.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : Algebra.FormallyEtale Γ(S, C.base.1) (S.presheaf.stalk (f x)) :=
    Algebra.FormallyEtale.of_isLocalization
      (C.base.2.primeIdealOf ⟨f x, C.le_preimage hx⟩).asIdeal.primeCompl
  change Algebra.NodeFittingOmega.baseEquiv Γ(S, C.base.1) (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      Γ(S, C.base.1) Γ(X, C.source.1) (X.presheaf.stalk x))
        (b ⊗ₜ[Γ(X, C.source.1)] KaehlerDifferential.D Γ(S, C.base.1) Γ(X, C.source.1) r)) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
    LinearEquiv.map_smul, Algebra.NodeFittingOmega.baseEquiv_D]
  rfl

end DeJongAlterations.Geometry.NodeCompletedLocalOriginalStalkOmega
