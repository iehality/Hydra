import Hydra.Peano.Language
import Hydra.Peano.Epsilon0

namespace LO.FirstOrder

namespace Hydra

open Ordinal

abbrev numeral {L : Language} [L.ORing] (n : ℕ) : Nilterm L := ‘↑n’

abbrev OmegaArith.Sequent := List (Sentence ℒₒᵣ[𝗫])

inductive OmegaArith.Sequent.TrueLiteral : OmegaArith.Sequent → Prop
  | axL (Γ) {t u : Nilterm ℒₒᵣ[𝗫]} : t.xnval = t.xnval → TrueLiteral (“!!t ∈ 𝗫” :: “!!u ∉ 𝗫” :: Γ)
  | eq  (Γ) {t u : Nilterm ℒₒᵣ[𝗫]} : t.xnval = t.xnval → TrueLiteral (“!!t = !!u” :: Γ)
  | neq (Γ) {t u : Nilterm ℒₒᵣ[𝗫]} : t.xnval ≠ t.xnval → TrueLiteral (“!!t ≠ !!u” :: Γ)
  | lt  (Γ) {t u : Nilterm ℒₒᵣ[𝗫]} : t.xnval < t.xnval → TrueLiteral (“!!t < !!u” :: Γ)
  | nlt (Γ) {t u : Nilterm ℒₒᵣ[𝗫]} : t.xnval ≥ t.xnval → TrueLiteral (“!!t ≮ !!u” :: Γ)

structure DepthCut where
  depth : Epsilon0
  cut : ℕ

inductive OmegaArith : DepthCut → OmegaArith.Sequent → Type
  | literal (d) {Γ}      : Γ.TrueLiteral → OmegaArith d Γ
  | verum (d Γ)          : ⊤ ∈ Γ → OmegaArith d Γ
  | and {a c φ ψ Γ}      : φ ⋏ ψ ∈ Γ → OmegaArith ⟨a, c⟩ (φ :: Γ) → OmegaArith ⟨a, c⟩ (ψ :: Γ) → OmegaArith ⟨.succ a, c⟩ Γ
  | or  {a c φ ψ Γ}      : φ ⋎ ψ ∈ Γ → OmegaArith ⟨a, c⟩ (φ :: ψ :: Γ) → OmegaArith ⟨.succ a, c⟩ Γ
  | allOmega {b a c φ Γ} : ∀' φ ∈ Γ → ((n : ℕ) → OmegaArith ⟨b, c⟩ (φ/[numeral n] :: Γ)) → b < a → OmegaArith ⟨a, c⟩ Γ
  | ex {a φ Γ} (t)       : ∃' φ ∈ Γ → OmegaArith ⟨a, c⟩ (φ/[t] :: Γ) → OmegaArith ⟨.succ a, c⟩ Γ
  | cut {a φ}            : φ.complexity < c → OmegaArith ⟨a, c⟩ (φ :: Γ) → OmegaArith ⟨a, c⟩ (∼φ :: Γ) → OmegaArith ⟨.succ a, c⟩ Γ

instance : System OmegaArith.Sequent DepthCut := ⟨OmegaArith⟩

end Hydra

end LO.FirstOrder
