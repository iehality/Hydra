import Hydra.Peano.Language
import Hydra.Peano.Epsilon0

namespace LO.FirstOrder

namespace OmegaArith

inductive Epsilon0 : Type
  | zero : Epsilon0
  | oadd : Epsilon0 → Epsilon0

end OmegaArith

abbrev OmegaArith.Sequent := List (Sentence ℒₒᵣ[𝗫])

open Ordinal

inductive OmegaArith : Epsilon0 → ℕ → OmegaArith.Sequent → Type _
  | axL (a c) (t u : Nilterm ℒₒᵣ[𝗫]) (h : t.xnval = t.xnval) (Γ) : OmegaArith a c (“!!t ∈ 𝗫” :: “!!u ∉ 𝗫” :: Γ)
  | eq  (a c) (t u : Nilterm ℒₒᵣ[𝗫]) (h : t.xnval = t.xnval) (Γ) : OmegaArith a c (“!!t = !!u” :: Γ)
  | neq (a c) (t u : Nilterm ℒₒᵣ[𝗫]) (h : t.xnval ≠ t.xnval) (Γ) : OmegaArith a c (“!!t ≠ !!u” :: Γ)
  | lt  (a c) (t u : Nilterm ℒₒᵣ[𝗫]) (h : t.xnval < t.xnval) (Γ) : OmegaArith a c (“!!t < !!u” :: Γ)
  | nlt (a c) (t u : Nilterm ℒₒᵣ[𝗫]) (h : t.xnval ≥ t.xnval) (Γ) : OmegaArith a c (“!!t ≮ !!u” :: Γ)
  | verum (a c Γ)                     : ⊤ ∈ Γ → OmegaArith a c Γ
  | and {c a φ ψ Γ}                   : φ ⋏ ψ ∈ Γ → OmegaArith a c (φ :: Γ) → OmegaArith a c (ψ :: Γ) → OmegaArith (.succ a) c Γ
  | or  {c a φ ψ Γ}                   : φ ⋎ ψ ∈ Γ → OmegaArith a c (φ :: ψ :: Γ) → OmegaArith (.succ a) c Γ
  | allOmega {c φ Γ} {b a : Epsilon0} : ∀' φ ∈ Γ → ((n : ℕ) → OmegaArith b c (φ/[‘↑n’] :: Γ)) → b < a → OmegaArith a c Γ
  | ex {φ Γ} (t)                      : ∃' φ ∈ Γ → OmegaArith a c (φ/[t] :: Γ) → OmegaArith (.succ a) c Γ
  | cut {φ} (hφ : φ.complexity < c)   : OmegaArith a c (φ :: Γ) → OmegaArith a c (∼φ :: Γ) → OmegaArith (.succ a) c Γ

end LO.FirstOrder
