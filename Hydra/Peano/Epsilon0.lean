import Foundation.Logic.LogicSymbol

namespace LO

namespace Ordinal

inductive CantorNot : Type
  | zero : CantorNot -- 0
  | oadd : CantorNot → CantorNot → CantorNot -- ω^x + y
  deriving DecidableEq

namespace CantorNot

instance : Zero CantorNot := ⟨zero⟩

instance : One CantorNot := ⟨oadd 0 0⟩

scoped infixr:60 " o+ " => oadd

lemma zero_def : (0 : CantorNot) = zero := rfl

lemma one_def : (1 : CantorNot) = 0 o+ 0 := rfl

section ToString

def toStr : CantorNot → String
  | 0      => "0"
  | 0 o+ 0 => "1"
  | 0 o+ b => "1 + " ++ b.toStr
  | 1 o+ 0 => "ω"
  | 1 o+ b => "ω + " ++ b.toStr
  | a o+ 0 => "ω^(" ++ a.toStr ++ ")"
  | a o+ b => "ω^(" ++ a.toStr ++ ") + " ++ b.toStr

instance : Repr CantorNot := ⟨fun a _ ↦ a.toStr⟩

instance : ToString CantorNot := ⟨toStr⟩

end ToString

def exp (a : CantorNot) : CantorNot := a o+ 0

def omega : CantorNot := 1 o+ 0

@[elab_as_elim]
def cases' {C : CantorNot → Sort*}
    (zero : C 0)
    (succ : ∀ a b, C (a o+ b)) : ∀ a, C a
  | 0      => zero
  | a o+ b => succ a b

@[elab_as_elim]
def rec' {C : CantorNot → Sort*}
    (zero : C 0)
    (succ : ∀ a b, C a → C b → C (a o+ b)) : ∀ a, C a
  | 0      => zero
  | a o+ b => succ a b (rec' zero succ a) (rec' zero succ b)

def succ : CantorNot → CantorNot
  | 0      => 1
  | a o+ b => a o+ b.succ

@[simp] lemma succ_zero : (0 : CantorNot).succ = 1 := rfl

@[simp] lemma succ_oadd (a b : CantorNot) : (a o+ b).succ = a o+ b.succ := rfl

inductive Lt : CantorNot → CantorNot → Prop
  | zero (a b) : Lt 0 (oadd a b)
  | oadd_left {a₁ a₂ b₁ b₂} : Lt a₁ a₂ → Lt (a₁ o+ b₁) (a₂ o+ b₂)
  | oadd_right {a b₁ b₂} : Lt b₁ b₂ → Lt (a o+ b₁) (a o+ b₂)

instance : LT CantorNot := ⟨Lt⟩

def Le (a b : CantorNot) : Prop := a = b ∨ a < b

instance : LE CantorNot := ⟨Le⟩

@[simp] lemma lt_zero (a b : CantorNot) : 0 < oadd a b := Lt.zero a b

lemma lt_oadd_left {a₁ a₂} (h : a₁ < a₂) (b₁ b₂) : a₁ o+ b₁ < a₂ o+ b₂ := Lt.oadd_left h

lemma lt_oadd_right (a) {b₁ b₂} (h : b₁ < b₂) : a o+ b₁ < a o+ b₂ := Lt.oadd_right h

def lt_decidable : DecidableRel (fun a b : CantorNot ↦ a < b)
  | 0,          0          => .isFalse <| by rintro ⟨⟩
  | 0,          oadd a b   => .isTrue (lt_zero a b)
  | oadd a b,   0          => .isFalse <| by rintro ⟨⟩
  | a₁ o+ b₁, a₂ o+ b₂ =>
    match lt_decidable a₁ a₂ with
    | .isTrue h    => .isTrue <| lt_oadd_left h _ _
    | .isFalse ha  =>
      match inferInstanceAs (Decidable (a₁ = a₂)), lt_decidable b₁ b₂ with
      | .isTrue ha,   .isTrue hb => .isTrue <| by rcases ha; apply lt_oadd_right _ hb
      | .isFalse ha', _          => .isFalse <| by { rintro (h | h); { exact ha h }; { exact ha' rfl } }
      | _,           .isFalse hb => .isFalse <| by { rintro (h | h); { exact ha h }; { exact hb (by assumption) } }

instance : DecidableRel (fun a b : CantorNot ↦ a < b) := lt_decidable

@[simp] lemma lt_oadd_self_left (a b) : a < a o+ b := by
  match a with
  | 0      => simp
  | a o+ c => exact lt_oadd_left (lt_oadd_self_left a c) _ _

@[simp] lemma zero_lt_one : (0 : CantorNot) < 1 := lt_zero 0 0

@[simp] lemma lt_succ (a : CantorNot) : a < a.succ :=
  match a with
  | 0      => by simp
  | a o+ b => lt_oadd_right a (lt_succ b)

@[trans] lemma lt_trans {a b c : CantorNot} (hab : a < b) (hbc : b < c) : a < c := by
  rcases hab
  case zero a b => rcases hbc <;> simp
  case oadd_left a₁ a₂ b₁ b₂ ha =>
    rcases hbc
    case oadd_left a₃ b₃ h => exact lt_oadd_left (lt_trans ha h) b₁ b₃
    case oadd_right => apply lt_oadd_left; assumption
  case oadd_right a b₁ b₂ hb =>
    rcases hbc
    case oadd_left => apply lt_oadd_left; assumption
    case oadd_right b₃ h => apply lt_oadd_right _ (lt_trans hb h)

@[simp] lemma lt_antirefl (a : CantorNot) : ¬a < a := by
  match a with
  | 0      => rintro ⟨⟩
  | a o+ b =>
    rintro (_ | h | h)
    · exact lt_antirefl a h
    · exact lt_antirefl b h

lemma lt_trichotomy (a b : CantorNot) : a < b ∨ a = b ∨ a > b := by
  match a, b with
  | 0,        0        => simp
  | 0,        a o+ b   => simp
  | a o+ b,   0        => simp
  | a₁ o+ b₁, a₂ o+ b₂ =>
    rcases lt_trichotomy a₁ a₂ with (h | rfl | h)
    · left; apply lt_oadd_left h
    · rcases lt_trichotomy b₁ b₂ with (h | rfl | h)
      · left; apply lt_oadd_right _ h
      · simp
      · right; right; apply lt_oadd_right _ h
    · right; right; apply lt_oadd_left h

@[simp] lemma lt_oadd_right_iff {a b₁ b₂} : a o+ b₁ < a o+ b₂ ↔ b₁ < b₂ :=
  ⟨by rintro (h | h | h)
      · exact (lt_antirefl a h).elim
      · exact h,
    Lt.oadd_right⟩

instance le_decidable : DecidableRel (fun a b : CantorNot ↦ a ≤ b) := fun _ _ ↦ instDecidableOr

@[refl, simp] lemma le_refl (a : CantorNot) : a ≤ a := Or.inl rfl

@[simp] lemma le_of_lt {a b : CantorNot} (h : a < b) : a ≤ b := Or.inr h

@[simp] lemma zero_le (a : CantorNot) : 0 ≤ a := by
  match a with
  | 0 => rfl
  | a o+ b => apply le_of_lt; simp

instance : LinearOrder CantorNot where
  le_refl := le_refl
  le_trans a b c := by
    rintro (rfl | hab)
    · intro h; exact h
    · rintro (rfl | hbc)
      · exact le_of_lt hab
      · exact le_of_lt (lt_trans hab hbc)
  le_total a b := by
    rcases lt_trichotomy a b with (h | rfl | h)
    · left; exact le_of_lt h
    · simp
    · right; exact le_of_lt h
  le_antisymm a b := by
    rintro (rfl | hab)
    · simp
    rintro (rfl | hba)
    · simp
    · have := lt_antirefl a (lt_trans hab hba); contradiction
  decidableLE := inferInstance
  decidableLT := inferInstance
  lt_iff_le_not_le a b := by
    constructor
    · intro h
      exact ⟨le_of_lt h, by
        rintro (rfl | h')
        · exact lt_antirefl b h
        · exact lt_antirefl a (lt_trans h h')⟩
    · rintro ⟨(rfl | hab), hba⟩
      · simp at hba
      · exact hab

@[simp] lemma le_oadd_right_iff {a b₁ b₂} : a o+ b₁ ≤ a o+ b₂ ↔ b₁ ≤ b₂ := by
  constructor
  · rintro (e | h)
    · simp [show b₁ = b₂ from by simpa using e]
    · apply le_of_lt; simpa using h
  · rintro (rfl | h)
    · simp
    · apply le_of_lt; simpa using h

lemma oadd_le_monotone {a₁ a₂ b₁ b₂} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : a₁ o+ b₁ ≤ a₂ o+ b₂ := by
  rcases ha with (rfl | ha)
  · simp [hb]
  · apply le_of_lt (lt_oadd_left ha b₁ b₂)

def add : CantorNot → CantorNot → CantorNot
  | 0,        b        => b
  | a,        0        => a
  | a₁ o+ b₁, a₂ o+ b₂ => if a₁ ≥ a₂ then a₁ o+ (add b₁ (a₂ o+ b₂)) else a₂ o+ b₂

instance : Add CantorNot := ⟨add⟩

lemma add_def (a b : CantorNot) : a + b = add a b := rfl

@[simp] lemma add_zero (a : CantorNot) : a + 0 = a := by rcases a <;> rfl

@[simp] lemma zero_add (a : CantorNot) : 0 + a = a := by rcases a <;> rfl

lemma oadd_add_oadd (a₁ a₂ b₁ b₂ : CantorNot) : (a₁ o+ b₁) + (a₂ o+ b₂) = if a₁ ≥ a₂ then a₁ o+ (b₁ + (a₂ o+ b₂)) else a₂ o+ b₂ := rfl

lemma succ_eq_add_one (a : CantorNot) : a.succ = a + 1 := by
  match a with
  | 0      => simp
  | a o+ b => simp [one_def, oadd_add_oadd, succ_eq_add_one b]

@[simp] lemma le_add_right (a b : CantorNot) : a ≤ a + b := by
  match a, b with
  | 0,        a        => simp
  | a,        0        => simp
  | a₁ o+ b₁, a₂ o+ b₂ =>
    by_cases h : a₁ ≥ a₂
    · simp [oadd_add_oadd, h, le_add_right b₁]
    · simpa [oadd_add_oadd, h] using le_of_lt (lt_oadd_left (lt_of_not_ge h) b₁ b₂)

/-
lemma add_assoc (a b c : CantorNot) : a + (b + c) = (a + b) + c := by
  match a, b, c with
  | 0, b, c => simp
  | a, 0, c => simp
  | a, b, 0 => simp
  | a₁ o+ a₂, b₁ o+ b₂, c₁ o+ c₂ =>
    match inferInstanceAs (Decidable (a₁ ≥ b₁)), inferInstanceAs (Decidable (b₁ ≥ c₁)), inferInstanceAs (Decidable (c₁ ≥ a₁)) with
    | .isFalse hab, .isFalse hbc, _ => { simp [oadd_add_oadd, hab, hbc] }
-/

def log : CantorNot → CantorNot
  | 0      => 0
  | a o+ _ => a

@[simp] lemma log_zero : log 0 = 0 := rfl

@[simp] lemma log_oadd (a b) : log (a o+ b) = a := rfl

@[simp] lemma log_add (a b) : log (a + b) = log a ⊔ log b := by
  match a, b with
  | 0,        a        => simp
  | a,        0        => simp
  | a₁ o+ a₂, b₁ o+ b₂ =>
    by_cases h : a₁ ≥ b₁
    · simp [oadd_add_oadd, h]
    · have : a₁ < b₁ := by simpa using h
      simp [oadd_add_oadd, h, le_of_lt this]

inductive IsNF : CantorNot → Prop
  | protected zero : IsNF 0
  | oadd_zero {a} : IsNF a → IsNF (a o+ 0)
  | oadd_oadd {a b c} : IsNF a → IsNF (b o+ c) → a ≥ b → IsNF (a o+ b o+ c)

attribute [simp] IsNF.zero

namespace IsNF

@[simp] protected lemma one : IsNF 1 := oadd_zero .zero

lemma oadd_iff {a b} : IsNF (a o+ b) ↔ IsNF a ∧ IsNF b ∧ a ≥ log b := by
  match b with
  | 0      =>
    constructor
    · rintro (h | h | h); simp [h]
    · rintro ⟨ha, _⟩; exact oadd_zero ha
  | b o+ c =>
    constructor
    · rintro (_ | _ | ⟨ha, hbc, hab⟩); simp [*]
    · rintro ⟨ha, hb, h⟩; exact oadd_oadd ha hb (by simpa using h)

lemma left (h : IsNF (a o+ b)) : IsNF a := (oadd_iff.mp h).1

lemma right (h : IsNF (a o+ b)) : IsNF b := (oadd_iff.mp h).2.1

lemma log_le (h : IsNF (a o+ b)) : log b ≤ a := (oadd_iff.mp h).2.2

lemma add {a b} (ha : IsNF a) (hb : IsNF b) : IsNF (a + b) := by
  match a, b with
  | 0,        b        => simpa
  | a,        0        => simpa
  | a₁ o+ b₁, a₂ o+ b₂ =>
    by_cases h : a₁ ≥ a₂
    · have : IsNF (b₁ + (a₂ o+ b₂)) := add ha.right hb
      simp [oadd_add_oadd, h, oadd_iff, oadd_iff.mp ha, this]
    · simp [oadd_add_oadd, h, hb]

lemma succ {a} (ha : IsNF a) : IsNF a.succ := by simpa [succ_eq_add_one] using ha.add .one

end IsNF

lemma lt_oadd_self_right_of_isNF {a b} (hb : b.IsNF) (h : log b ≤ a) : b < a o+ b := by
  match b with
  | 0      => simp
  | b o+ c =>
    have : b = a ∨ b < a := by simpa using h
    rcases this with (rfl | hab)
    · have : c < b o+ c := lt_oadd_self_right_of_isNF hb.right hb.log_le
      simp [this]
    · exact lt_oadd_left hab _ _

lemma le_add_left (a b : CantorNot) (hb : b.IsNF) : b ≤ a + b := by
  match a, b with
  | 0,        a        => simp
  | a,        0        => simp
  | a₁ o+ b₁, a₂ o+ b₂ =>
    by_cases h : a₁ ≥ a₂
    · have ih : a₂ o+ b₂ ≤ b₁ + (a₂ o+ b₂) := le_add_left b₁ (a₂ o+ b₂) hb
      have : b₂ ≤ b₁ + (a₂ o+ b₂) := le_trans (le_of_lt <| lt_oadd_self_right_of_isNF hb.right hb.log_le) ih
      simpa [oadd_add_oadd, h] using oadd_le_monotone h this
    · simp [oadd_add_oadd, h]

end CantorNot

@[ext] structure Epsilon0 where
  not : CantorNot
  isNF : not.IsNF

namespace Epsilon0

open CantorNot

instance : DecidableEq Epsilon0
  | ⟨a, ha⟩, ⟨b, hb⟩ => if h : a = b then .isTrue (by simp [h]) else .isFalse (by simp [h])

instance : Repr Epsilon0 := ⟨fun a _ ↦ repr a.not⟩

instance : ToString Epsilon0 := ⟨fun a ↦ toString a.not⟩

instance : Zero Epsilon0 := ⟨⟨0, by simp⟩⟩

instance : One Epsilon0 := ⟨⟨1, by simp⟩⟩

@[simp] lemma not_zero : (0 : Epsilon0).not = 0 := rfl

@[simp] lemma not_one : (1 : Epsilon0).not = 1 := rfl

instance : LinearOrder Epsilon0 := LinearOrder.lift' not (by rintro ⟨a, _⟩ ⟨b, _⟩; simp)

lemma lt_def {a b : Epsilon0} : a < b ↔ a.not < b.not := by rfl

lemma le_def {a b : Epsilon0} : a ≤ b ↔ a.not ≤ b.not := by rfl

def succ : Epsilon0 → Epsilon0
  | ⟨a, h⟩ => ⟨a.succ, h.succ⟩

def exp : Epsilon0 → Epsilon0
  | ⟨a, h⟩ => ⟨a o+ 0, IsNF.oadd_zero h⟩

def omega : ℕ → Epsilon0
  | 0     => 0
  | n + 1 => exp (omega n)

@[simp] lemma not_succ (a : Epsilon0) : a.succ.not = a.not.succ := rfl

@[simp] lemma not_exp (a : Epsilon0) : a.exp.not = a.not o+ 0 := rfl

@[simp] lemma exp_zero : exp 0 = 1 := rfl

@[simp] lemma omega_zero : omega 0 = 0 := rfl

@[simp] lemma omega_succ (n : ℕ) : omega (n + 1) = exp (omega n) := rfl

@[simp] lemma succ_zero : (0 : Epsilon0).succ = 1 := rfl

@[simp] lemma lt_succ (a : Epsilon0) : a < a.succ := by simp [lt_def]

def add : Epsilon0 → Epsilon0 → Epsilon0
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a + b, ha.add hb⟩

instance : Add Epsilon0 := ⟨add⟩

@[simp] lemma note_add (a b : Epsilon0) : (a + b).not = a.not + b.not := rfl

@[simp] lemma add_zero (a : Epsilon0) : a + 0 = a := by ext; simp

@[simp] lemma zero_add (a : Epsilon0) : 0 + a = a := by ext; simp

lemma succ_eq_add_one (a : Epsilon0) : a.succ = a + 1 := by ext; simp [CantorNot.succ_eq_add_one]

@[simp] lemma le_add_left (a b : Epsilon0) : a ≤ a + b := by simp [le_def]

@[simp] lemma le_add_right (a b : Epsilon0) : b ≤ a + b := by simpa [le_def] using CantorNot.le_add_left _ _ b.isNF

/-
ω^(ω^(ω^(ω^(ω^(ω^(ω^(ω^(ω))))))) + ω^(ω^(ω^(ω))) + 1 + 1) + ω^(ω^(ω^(ω^(ω)) + ω^(ω) + 1)) + ω^(ω) + 1
-/
#eval exp (omega 9 + omega 5 + 1 + 1) + exp (exp (omega 4 + omega 3 + 1)) + omega 3 + 1

end Epsilon0

end Ordinal

end LO
