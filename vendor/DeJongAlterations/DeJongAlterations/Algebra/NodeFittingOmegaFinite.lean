import DeJongAlterations.Algebra.NodeFittingModuleBaseChange
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.Algebra.Module.Presentation.Finite

/-! # Finite presentation of the actual original relative differential module -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingOmega

universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The native conormal presentation of a native finite algebra presentation is finite. -/
instance finitePresentation [Algebra.FinitePresentation R S] :
    Module.FinitePresentation S (KaehlerDifferential R S) := by
  let p := Algebra.Presentation.ofFinitePresentation R S
  let : Finite p.differentials.G := by
    change Finite (Fin (Algebra.Presentation.ofFinitePresentationVars R S))
    infer_instance
  let : Finite p.differentials.R := by
    change Finite (Fin (Algebra.Presentation.ofFinitePresentationRels R S))
    infer_instance
  exact p.differentials.finitePresentation

end DeJongAlterations.Algebra.NodeFittingOmega
