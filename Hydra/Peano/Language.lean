import Foundation.FirstOrder.Arith.Representation
import Mathlib.SetTheory.Ordinal.Notation

namespace LO.FirstOrder

namespace Language

class SingleSetVariable (L : Language) where
  x : L.Rel 1

attribute [match_pattern] SingleSetVariable.x

namespace ORingX

inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2
  | mul : Func 2

inductive Rel : ℕ → Type
  | X : Rel 1
  | eq : Rel 2
  | lt : Rel 2

end ORingX

@[reducible]
def oRingX : Language where
  Func := ORingX.Func
  Rel := ORingX.Rel

notation "ℒₒᵣ[𝗫]" => oRingX

namespace ORingX

instance (k) : DecidableEq (oRingX.Func k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : DecidableEq (oRingX.Rel k) := fun a b =>
  by rcases a <;> rcases b <;> simp <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}

instance (k) : Encodable (oRingX.Func k) where
  encode := fun x =>
    match x with
    | Func.zero => 0
    | Func.one  => 1
    | Func.add  => 0
    | Func.mul  => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.zero
    | 0, 1 => some Func.one
    | 2, 0 => some Func.add
    | 2, 1 => some Func.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance (k) : Encodable (oRingX.Rel k) where
  encode := fun x =>
    match x with
    | Rel.X  => 0
    | Rel.eq => 1
    | Rel.lt => 2
  decode := fun e =>
    match k, e with
    | 1, 0 => some Rel.X
    | 2, 1 => some Rel.eq
    | 2, 2 => some Rel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance : SingleSetVariable ℒₒᵣ[𝗫] := ⟨.X⟩

instance : ORing ℒₒᵣ[𝗫] where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

end ORingX

end Language

namespace Semiformula.Operator

class SingleSetVariable (L : Language) where
  x : Semiformula.Operator L 1

variable {L : Language} [L.SingleSetVariable]

instance : Operator.SingleSetVariable L :=
  ⟨⟨Semiformula.rel Language.SingleSetVariable.x Semiterm.bvar⟩⟩

lemma SingleSetVariable.sentence_eq :
    (@SingleSetVariable.x L _).sentence = Semiformula.rel Language.SingleSetVariable.x Semiterm.bvar := rfl

@[simp] lemma SingleSetVariable.equal_inj {t₁ t₂ : Semiterm L ξ₂ n₂} :
    SingleSetVariable.x.operator ![t₁] = SingleSetVariable.x.operator ![t₂] ↔ t₁ = t₂ := by
  simp [operator, SingleSetVariable.sentence_eq, Matrix.constant_eq_singleton']

lemma SingleSetVariable.def (t : Semiterm L ξ n) :
    SingleSetVariable.x.operator ![t] = Semiformula.rel Language.SingleSetVariable.x ![t] := by
  simp [operator, sentence_eq, rew_rel, Matrix.constant_eq_singleton]

@[simp] lemma SingleSetVariable.open (t : Semiterm L ξ n) :
    (SingleSetVariable.x.operator ![t]).Open := by simp [Operator.operator, sentence_eq]

end Semiformula.Operator

namespace BinderNotation

open Semiformula

syntax:45 first_order_term:45 " ∈ " "𝗫" : first_order_formula
syntax:45 first_order_term:45 " ∉ " "𝗫" : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ∈ 𝗫 ]) => `(Semiformula.Operator.operator Operator.SingleSetVariable.x ![⤫term[ $binders* | $fbinders* | $t ]])
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ∉ 𝗫 ]) => `(∼Semiformula.Operator.operator Operator.SingleSetVariable.x ![⤫term[ $binders* | $fbinders* | $t ]])

end BinderNotation

abbrev Seminilterm (L : Language) (n : ℕ) := Semiterm L Empty n

abbrev Nilterm (L : Language) := Semiterm L Empty 0

namespace Semiterm

def oringXToOring {L : Language} [L.ORing] : Semiterm ℒₒᵣ[𝗫] ξ n → Semiterm L ξ n
  | #x                         => #x
  | &x                         => &x
  | .func Language.Zero.zero _ => .func Language.Zero.zero ![]
  | .func Language.One.one _   => .func Language.One.one ![]
  | .func Language.Add.add v   => .func Language.Add.add ![oringXToOring (v 0), oringXToOring (v 1)]
  | .func Language.Mul.mul v   => .func Language.Mul.mul ![oringXToOring (v 0), oringXToOring (v 1)]

private lemma coe_oringXToOring : (t : Semiterm ℒₒᵣ[𝗫] ξ n) → ((t.oringXToOring : Semiterm ℒₒᵣ ξ n) : Semiterm ℒₒᵣ[𝗫] ξ n) = t
  | #x                         => rfl
  | &x                         => rfl
  | .func Language.Zero.zero _ => by simp [oringXToOring, lMap_func, Matrix.empty_eq]
  | .func Language.One.one _   => by simp [oringXToOring, lMap_func, Matrix.empty_eq]
  | .func Language.Add.add v   => by
    simp [oringXToOring, lMap_func, Matrix.comp_vecCons, coe_oringXToOring (v 0), coe_oringXToOring (v 1), ←Matrix.fun_eq_vec₂]
  | .func Language.Mul.mul v   => by
    simp [oringXToOring, lMap_func, Matrix.comp_vecCons, coe_oringXToOring (v 0), coe_oringXToOring (v 1), ←Matrix.fun_eq_vec₂]

private lemma oringXToOring_coe : (t : Semiterm ℒₒᵣ ξ n) → ((t : Semiterm ℒₒᵣ[𝗫] ξ n).oringXToOring : Semiterm ℒₒᵣ ξ n) = t
  | #x => rfl
  | &x => rfl
  | .func Language.Zero.zero _ => by simp [oringXToOring, lMap_func, Matrix.empty_eq]
  | .func Language.One.one _   => by simp [oringXToOring, lMap_func, Matrix.empty_eq]
  | .func Language.Add.add v   => by
    simp [oringXToOring, lMap_func, Matrix.comp_vecCons, oringXToOring_coe (v 0), oringXToOring_coe (v 1), ←Matrix.fun_eq_vec₂]
  | .func Language.Mul.mul v   => by
    simp [oringXToOring, lMap_func, Matrix.comp_vecCons, oringXToOring_coe (v 0), oringXToOring_coe (v 1), ←Matrix.fun_eq_vec₂]

def oringXEquiv : Semiterm ℒₒᵣ[𝗫] ξ n ≃ Semiterm ℒₒᵣ ξ n where
  toFun := oringXToOring
  invFun := Coe.coe
  left_inv := coe_oringXToOring
  right_inv := oringXToOring_coe

def xnval : Nilterm ℒₒᵣ[𝗫] → ℕ
  | .func Language.Zero.zero _ => 0
  | .func Language.One.one _   => 1
  | .func Language.Add.add v   => (v 0).xnval + (v 1).xnval
  | .func Language.Mul.mul v   => (v 0).xnval * (v 1).xnval

@[simp] lemma xnval_zero : (‘0’ : Nilterm ℒₒᵣ[𝗫]).xnval = 0 := rfl

@[simp] lemma xnval_one : (‘1’ : Nilterm ℒₒᵣ[𝗫]).xnval = 1 := rfl

@[simp] lemma xnval_add (t u : Nilterm ℒₒᵣ[𝗫]) : (‘!!t + !!u’ : Nilterm ℒₒᵣ[𝗫]).xnval = t.xnval + u.xnval := rfl

@[simp] lemma xnval_mul (t u : Nilterm ℒₒᵣ[𝗫]) : (‘!!t * !!u’ : Nilterm ℒₒᵣ[𝗫]).xnval = t.xnval * u.xnval := rfl

@[simp] lemma xnval_numeral : (n : ℕ) → (‘↑n’ : Nilterm ℒₒᵣ[𝗫]).xnval = n
  | 0     => rfl
  | 1     => rfl
  | n + 2 =>
    calc
      (‘↑(n + 2)’ : Nilterm ℒₒᵣ[𝗫]).xnval = (‘↑(n + 1)’ : Nilterm ℒₒᵣ[𝗫]).xnval + 1 := rfl
      _                                   = n + 2 := by simp [xnval_numeral (n + 1)]

end Semiterm

namespace Semiformula

def svSubst (ρ : Semiformula ℒₒᵣ ξ 1) : Semiformula ℒₒᵣ[𝗫] ξ n → Semiformula ℒₒᵣ ξ n
  | .rel Language.SingleSetVariable.x v  => ρ/[(v 0).oringXEquiv]
  | .rel Language.Eq.eq v                => .rel Language.Eq.eq ![(v 0).oringXEquiv, (v 1).oringXEquiv]
  | .rel Language.LT.lt v                => .rel Language.LT.lt ![(v 0).oringXEquiv, (v 1).oringXEquiv]
  | .nrel Language.SingleSetVariable.x v => ∼ρ/[(v 0).oringXEquiv]
  | .nrel Language.Eq.eq v               => .nrel Language.Eq.eq ![(v 0).oringXEquiv, (v 1).oringXEquiv]
  | .nrel Language.LT.lt v               => .nrel Language.LT.lt ![(v 0).oringXEquiv, (v 1).oringXEquiv]
  | ⊤                                    => ⊤
  | ⊥                                    => ⊥
  | φ ⋏ ψ                                => svSubst ρ φ ⋏ svSubst ρ ψ
  | φ ⋎ ψ                                => svSubst ρ φ ⋎ svSubst ρ ψ
  | ∀' φ                                 => ∀' svSubst ρ φ
  | ∃' φ                                 => ∃' svSubst ρ φ

end Semiformula

end LO.FirstOrder
