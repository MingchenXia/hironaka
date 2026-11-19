import Hironaka.Geometry.NodeCompletedLocalOriginalNodeQuadraticRelation
import Hironaka.Algebra.NodeFieldSeriesJetQuadratic
import Hironaka.Algebra.NodeFieldJetRigidity

/-! The whole original closed-fibre completion has its actual nondegenerate quadratic model. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNodeQuadraticClassification

open NodeCompletedLocalMap NodeCompletedLocalOriginalNodeJets NodeCompletedLocalResiduePoint
  NodeCompletedLocalOriginalNodePresentation NodeCompletedLocalSelectedFiberGeometric
  NodeCompletedLocalOriginalNodeJetDimensions
open Algebra.NodeFormalMorse Algebra.NodeVariableMorse Algebra.NodeFieldQuadraticSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f]
  (z : (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subscheme)

local notation "x" => (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z
local notation "Q" => OriginalFiberRing f x
local notation "κ" => ResidueField Q
local notation "C" => Algebra.CompletionRegularityBasics.Completion Q

attribute [local instance] originalAlgebra originalFiberResidueAlgebra originalFiber_isNoetherianRing
  originalBaseAlgebra selectedQuotientPointAlgebra selectedQuotientPoint_scalarTower

local instance originalQuotientLocalRing : IsLocalRing Q := originalFiberLocalRing f x

variable (L : Type u) [Field L] [IsAlgClosed L]
  [Algebra (X.residueField ((Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z)) L]

include L in
theorem exists_quadratic_model :
    letI := originalPointAlgebra f z
    ∃ q : Algebra.NodeNonsplit.Quadratic κ,
      Nonempty (C ≃ₐ[κ] (Series κ ⧸ Ideal.span {q.series})) := by
  let := originalCompletion_isNoetherianRing f z
  let := originalCompletion_isAdicComplete f z
  let := originalPointAlgebra f z
  obtain ⟨g, hg0, _, _, hΔ⟩ :=
    NodeCompletedLocalOriginalNodeQuadraticRelation.exists_nondegenerate_relation f z L
  let hres := originalPoint_residue_bijective f z
  let hdim2 := jet_finrank_two f z L
  have hg : g ∈ RingHom.ker
      (Algebra.NodeFieldCotangentGeneratorsPresentation.evaluation κ C hres hdim2).toRingHom := hg0
  let p : QuadraticSource κ g →ₐ[κ] C :=
    Algebra.NodeFieldQuadraticPresentation.quadraticQuotientMap κ C hres hdim2 g hg hΔ
  have hp : Function.Surjective p :=
    Algebra.NodeFieldQuadraticPresentation.quadraticQuotientMap_surjective κ C hres hdim2 g hg hΔ
  let : ∀ n : ℕ, FiniteDimensional κ
      (QuadraticSource κ g ⧸ maximalIdeal (QuadraticSource κ g) ^ n) :=
    fun n => Algebra.NodeFieldSeriesJetQuadratic.quadraticJet_finiteDimensional κ L g hΔ n
  let : ∀ n : ℕ, FiniteDimensional κ (C ⧸ maximalIdeal C ^ n) :=
    fun n => jet_finiteDimensional f z L n
  have hdim : ∀ n : ℕ,
      Module.finrank κ (QuadraticSource κ g ⧸ maximalIdeal (QuadraticSource κ g) ^ n) =
      Module.finrank κ (C ⧸ maximalIdeal C ^ n) := by
    intro n
    cases n with
    | zero =>
      let : Subsingleton (QuadraticSource κ g ⧸ maximalIdeal (QuadraticSource κ g) ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
      let : Subsingleton (C ⧸ maximalIdeal C ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
    | succ n =>
      exact (Algebra.NodeFieldSeriesJetQuadratic.quadraticJet_finrank_succ κ L g hΔ n).trans
        (jet_finrank_succ f z L n).symm
  let e := Algebra.NodeFieldJetRigidity.equivOfJetRanks κ p hp hdim
  let q := jetQuadratic g hΔ
  let sourceEquiv : (Series κ ⧸ Ideal.span {q.series}) ≃ₐ[κ] QuadraticSource κ g :=
    Ideal.quotientEquivAlgOfEq κ (congrArg (fun a : Series κ => Ideal.span {a})
      (jetQuadratic_series g hΔ))
  exact ⟨q, ⟨(sourceEquiv.trans e).symm⟩⟩

end Hironaka.Geometry.NodeCompletedLocalOriginalNodeQuadraticClassification
