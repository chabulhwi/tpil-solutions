/-
Copyright (c) 2026 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 8

## Structural Recursion and Induction
-/

universe u

def Nat.below' {motive : Nat → Sort u} (t : Nat) : Sort (max 1 u) :=
  Nat.recOn t (motive := fun _ ↦ Sort (max 1 u))
   (zero := PUnit)
   (succ := fun (n : Nat) (n_ih : Sort (max 1 u)) ↦ motive n ×' n_ih)

section

variable {motive : Nat → Sort u}

example : Nat.below' (motive := motive) = Nat.below (motive := motive) :=
  rfl

example : Nat.below (motive := motive) 0 = PUnit :=
  rfl

example (n : Nat) : Nat.below (motive := motive) (n + 1) =
    (motive n ×' Nat.below (motive := motive) n) :=
  rfl

example : Nat.below (motive := motive) 1 = (motive 0 ×' PUnit) :=
  rfl

example : Nat.below (motive := motive) 2 = (motive 1 ×' (motive 0 ×' PUnit)) :=
  rfl

example : Nat.below (motive := motive) 3 = (motive 2 ×' motive 1 ×' motive 0 ×' PUnit) :=
  rfl

end

noncomputable def Nat.brecOn.go' {motive : Nat → Sort u} (t : Nat)
    (F : (t : Nat) → Nat.below (motive := motive) t → motive t) :
    Nat.below (motive := motive) (t + 1) :=
  Nat.recOn t (motive := fun t ↦ Nat.below (t + 1))
    (zero := show Nat.below 1 from ⟨F 0 PUnit.unit, PUnit.unit⟩)
    (succ := fun (n : Nat) (n_ih : Nat.below (n + 1)) ↦ show Nat.below (n + 2) from
      ⟨F (n + 1) n_ih, n_ih⟩)

section

variable {motive : Nat → Sort u}

example : Nat.brecOn.go' (motive := motive) = Nat.brecOn.go (motive := motive) :=
  rfl

variable (n : Nat) (F : (t : Nat) → Nat.below (motive := motive) t → motive t)

example : Nat.brecOn.go 0 F = (show Nat.below 1 from ⟨F 0 PUnit.unit, PUnit.unit⟩) :=
  rfl

example : Nat.brecOn.go (n + 1) F = (show Nat.below (n + 2) from
    ⟨F (n + 1) (Nat.brecOn.go n F), Nat.brecOn.go n F⟩) :=
  rfl

example : Nat.brecOn.go 1 F = (show Nat.below 2 from
    ⟨F 1 ⟨F 0 PUnit.unit, PUnit.unit⟩, ⟨F 0 PUnit.unit, PUnit.unit⟩⟩) :=
  rfl

example : Nat.brecOn.go 2 F = (show Nat.below 3 from
    ⟨F 2 ⟨F 1 ⟨F 0 PUnit.unit, PUnit.unit⟩, ⟨F 0 PUnit.unit, PUnit.unit⟩⟩,
     F 1 ⟨F 0 PUnit.unit, PUnit.unit⟩,
     F 0 PUnit.unit,
     PUnit.unit⟩) :=
  rfl

example : Nat.brecOn.go 3 F = (show Nat.below 4 from
    ⟨F 3 ⟨F 2 ⟨F 1 ⟨F 0 PUnit.unit, PUnit.unit⟩, ⟨F 0 PUnit.unit, PUnit.unit⟩⟩,
       F 1 ⟨F 0 PUnit.unit, PUnit.unit⟩, F 0 PUnit.unit, PUnit.unit⟩,
     F 2 ⟨F 1 ⟨F 0 PUnit.unit, PUnit.unit⟩, ⟨F 0 PUnit.unit, PUnit.unit⟩⟩,
     F 1 ⟨F 0 PUnit.unit, PUnit.unit⟩,
     F 0 PUnit.unit,
     PUnit.unit⟩) :=
  rfl

example : Nat.brecOn.go 4 F = (show Nat.below 5 from
    ⟨F 4 (Nat.brecOn.go 3 F),
     F 3 (Nat.brecOn.go 2 F),
     F 2 (Nat.brecOn.go 1 F),
     F 1 (Nat.brecOn.go 0 F),
     F 0 PUnit.unit,
     PUnit.unit⟩) :=
  rfl

end

noncomputable def Nat.brecOn' {motive : Nat → Sort u} (t : Nat)
    (F : (t : Nat) → Nat.below (motive := motive) t → motive t) : motive t :=
  (Nat.brecOn.go' t F).1

example : Nat.brecOn' (motive := motive) = Nat.brecOn (motive := motive) :=
  rfl

namespace Nat

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

noncomputable def fib' (n : Nat) : Nat :=
  Nat.brecOn n aux
where
  aux (n : Nat) (prev : Nat.below n) : Nat :=
    match n with
    | 0 => 1
    | 1 => 1
    | _ + 2 => prev.1 + prev.2.1

theorem brecOn.go_succ_succ {motive : Nat → Sort u} (n : Nat)
    (F : (t : Nat) → Nat.below (motive := motive) t → motive t) :
    brecOn.go (n + 2) F = ⟨F (n + 2) (brecOn.go (n + 1) F), F (n + 1) (brecOn.go n F),
      brecOn.go n F⟩ :=
  rfl

theorem fib'_succ_succ (n : Nat) : fib' (n + 2) = fib' (n + 1) + fib' n := by
  unfold fib' Nat.brecOn
  rw [brecOn.go_succ_succ]
  show fib'.aux (n + 2) (brecOn.go (n + 1) fib'.aux) = (brecOn.go (n + 1) fib'.aux).1 +
    (brecOn.go n fib'.aux).1
  rw [fib'.aux]

theorem fib_eq_fib' (n : Nat) : fib n = fib' n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | k + 2 => rw [fib, fib'_succ_succ, fib_eq_fib' k, fib_eq_fib' (k + 1)]

#reduce brecOn.go 0 fib'.aux -- output:            ⟨1, PUnit.unit⟩
#reduce brecOn.go 1 fib'.aux --                 ⟨1, 1, PUnit.unit⟩
#reduce brecOn.go 2 fib'.aux --              ⟨2, 1, 1, PUnit.unit⟩
#reduce brecOn.go 3 fib'.aux --           ⟨3, 2, 1, 1, PUnit.unit⟩
#reduce brecOn.go 4 fib'.aux --        ⟨5, 3, 2, 1, 1, PUnit.unit⟩
#reduce brecOn.go 5 fib'.aux --     ⟨8, 5, 3, 2, 1, 1, PUnit.unit⟩
#reduce brecOn.go 6 fib'.aux -- ⟨13, 8, 5, 3, 2, 1, 1, PUnit.unit⟩

-- Slow:
#eval fib 30
-- Fast:
#reduce fib 169

end Nat
