/-
Copyright (c) 2026 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 8

## Accessibility
-/

set_option pp.proofs true

/-- Every natural number is accessible through the less-than relation `<` on the natural numbers. -/
theorem Nat.acc_lt (n : Nat) : Acc (· < ·) n :=
  match n with
  | 0 => ⟨0, fun m hm ↦ False.elim (Nat.not_lt_zero m hm)⟩
  | m + 1 => Acc.intro (m + 1) (fun k hk ↦
    match Nat.lt_add_one_iff_lt_or_eq.mp hk with
    | Or.inl hlt => let ⟨.(m), acc⟩ := Nat.acc_lt m; acc k hlt
    | Or.inr heq => heq ▸ Nat.acc_lt m)

namespace Acc

universe u

/-- If `a` is a minimal element of a type `α` with respect to a binary relation `r`, then it is
accessible through `r`. -/
theorem acc_of_is_min {α : Sort u} {r : α → α → Prop} {a : α} (h : ∀ (x : α), ¬r x a) : Acc r a :=
  ⟨a, fun x hrxa ↦ False.elim (h x hrxa)⟩

section

universe v

#check (@Acc.rec : {α : Sort u} → {r : α → α → Prop} → {motive : (a : α) → Acc r a → Sort v} →
  ((x : α) → (h : ∀ y : α, r y x → Acc r y) → ((y : α) → (ryx : r y x) →
  motive y (h y ryx : Acc r y)) → motive x (h x (_ : r x x) : Acc r x)) → {a : α} → (t : Acc r a) →
  motive a t)

#check (@Acc.recOn : {α : Sort u} → {r : α → α → Prop} → {motive : (a : α) → Acc r a → Sort v} →
  {a : α} → (t : Acc r a) → ((x : α) → (h : ∀ y : α, r y x → Acc r y) → ((y : α) → (ryx : r y x) →
  motive y (h y ryx : Acc r y)) → motive x (h x (_ : r x x) : Acc r x)) → motive a t)

end

variable {α : Sort u} {r : α → α → Prop}

/-- `a` is accessible from below if and only if all its predecessors are accessible. -/
theorem acc_def {a : α} : Acc r a ↔ ∀ (b : α), r b a → Acc r b where
  mp h := Acc.recOn h (fun x h _ih ↦ show ∀ (b : α), r b x → Acc r b from h)
  mpr := Acc.intro a

/-- If every element of a nonempty set `p` is accessible through a binary relation `r`, then it is
not false that the set has a minimal element. -/
theorem not_not_has_min {p : α → Prop} (acc : ∀ ⦃x : α⦄, p x → Acc r x) (hex : ∃ (x : α), p x) :
    ¬¬∃ (min : α), p min ∧ ∀ ⦃z : α⦄, p z → ¬r z min :=
  let ⟨w, hpw⟩ := hex
  Acc.recOn (acc hpw) (motive := fun (x : α) (_ : Acc r x) ↦ p x → ¬¬∃ (min : α), p min ∧
      ∀ ⦃z : α⦄, p z → ¬r z min)
    (fun x _hacx (ih : ∀ (y : α), r y x → p y → ¬¬∃ min, p min ∧ ∀ ⦃z : α⦄, p z → ¬r z min) ↦
      show p x → ¬¬∃ min, p min ∧ ∀ ⦃z : α⦄, p z → ¬r z min from fun hpx not_has_min ↦
        not_has_min ⟨x, hpx, fun {z} hpz hrzx ↦ ih z hrzx hpz not_has_min⟩)
    (show p w from hpw)

-- alternative proof of `Acc.not_not_has_min`
example {p : α → Prop} (acc : ∀ ⦃x : α⦄, p x → Acc r x) (hex : ∃ (x : α), p x) :
    ¬¬∃ (min : α), p min ∧ ∀ ⦃z : α⦄, p z → ¬r z min := by
  let ⟨w, hqw⟩ := hex
  induction acc hqw with
  | intro w _ ih =>
    intro not_has_min
    refine not_has_min ⟨w, hqw, ?_⟩
    intro z hqz hrzw
    exact ih z hrzw hqz not_has_min

/-- If `a` is accessible through a binary relation `r` and there exists an element below `a`, then
it is not false that the set `{y : α | r y a}` has a minimal element. -/
theorem not_not_has_min_below {a : α} (acc : Acc r a) (hex : ∃ (x : α), r x a) :
    ¬¬∃ (min : α), r min a ∧ ∀ ⦃z : α⦄, r z a → ¬r z min :=
  let ⟨.(a), hrac⟩ := acc
  not_not_has_min (p := fun (x : α) ↦ r x a) (fun {x} (hrx : r x a) ↦ hrac x hrx) (show ∃ x, r x a
    from hex)

theorem not_refl {a : α} (acc : Acc r a) : ¬r a a :=
  fun (hrfl : r a a) ↦
    have hmin : ¬¬∃ (min : α), min = a ∧ ∀ ⦃z : α⦄, (fun x ↦ x = a) z → ¬r z min :=
      not_not_has_min (p := fun (x : α) ↦ x = a) (fun {x} (heq : x = a) ↦ show Acc r x from
        heq ▸ acc) (show ∃ x, x = a from ⟨a, rfl⟩)
    hmin (fun ⟨min, (heq : min = a), hnrm⟩ ↦
      have hnrf : ¬r min min := hnrm heq
      (heq ▸ hnrf) hrfl)

/-- An alias of `Acc.not_refl`. -/
theorem not_rfl {a : α} (acc : Acc r a) : ¬r a a :=
  not_refl acc

end Acc

namespace Relation

variable {α : Sort u} (r : α → α → Prop)

/-- `isMin_below min a` means that `min` is a minimal element of the set `{y : α | r y a}` with
respect to `r`. -/
def isMin_below (min a : α) : Prop :=
  r min a ∧ ∀ ⦃y : α⦄, r y a → ¬r y min

end Relation

namespace Sequence

variable {α : Sort u} {f : Nat → α}

/-- A sequence `f` is constant if its `n`th term equals the next term for every natural number `n`.
-/
theorem const_of_rec (hcon : ∀ (n : Nat), f (n + 1) = f n) (n : Nat) : f n = f 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [hcon k, ih]

/-- A sequence `f` is constant if and only if its `n`th term equals the next term for every natural
number `n`. -/
theorem const_iff_rec : (∀ (n : Nat), f n = f 0) ↔ ∀ (n : Nat), f (n + 1) = f n := by
  constructor
  · intro hcon n
    rw [hcon n, hcon (n + 1)]
  · exact const_of_rec

/-- A sequence `f` is eventually constant if the `n`th term of `f` equals the next term for every
natural number `n` greater than or equal to some natural number. -/
theorem eventually_const_of_strongRec {c : Nat} (hcon : ∀ ⦃n : Nat⦄, c ≤ n → f (n + 1) = f n)
    ⦃n : Nat⦄ (hle : c ≤ n) : f n = f c := by
  let g (d : Nat) : α := f (c + d)
  have heq : g (n - c) = g 0 := by
    refine const_of_rec ?_ (n - c)
    intro d
    exact hcon (show c ≤ c + d from Nat.le_add_right c d)
  unfold g at heq
  rwa [← Nat.add_sub_assoc hle, Nat.add_sub_self_left, Nat.add_zero] at heq

/-- A sequence `f` is eventually constant if and only if the `n`th term of `f` equals the next term
for every natural number `n` greater than or equal to some natural number. -/
theorem eventually_const_iff_strongRec {c : Nat} : (∀ ⦃n : Nat⦄, c ≤ n → f n = f c) ↔
    (∀ ⦃n : Nat⦄, c ≤ n → f (n + 1) = f n) := by
  constructor
  · intro hcon n hle
    have hn1 : f (n + 1) = f c := hcon (show c ≤ n + 1 from Nat.le_trans hle (Nat.le_succ n))
    rw [hcon hle, hn1]
  · exact eventually_const_of_strongRec

theorem induction_step_of_rec {p : α → Prop} (hcon : ∀ ⦃n : Nat⦄, p (f n) → f (n + 1) = f n)
    ⦃n : Nat⦄ (ih : p (f n)) : p (f (n + 1)) := by
  have hrec : f (n + 1) = f n := hcon ih
  rwa [hrec]

theorem induction_of_rec {p : α → Prop} (base : p (f 0))
    (hcon : ∀ ⦃n : Nat⦄, p (f n) → f (n + 1) = f n) (m : Nat) : p (f m) := by
  induction m with
  | zero => exact base
  | succ k ih => exact induction_step_of_rec hcon ih

theorem induction_of_strongRec {p : α → Prop} {c : Nat} (base : p (f c))
    (hcon : ∀ ⦃n : Nat⦄, p (f n) → f (n + 1) = f n) ⦃m : Nat⦄ (hle : c ≤ m) : p (f m) := by
  let g (d : Nat) : α := f (c + d)
  have hp : p (g (m - c)) := by
    refine induction_of_rec base ?_ (m - c)
    intro d
    exact hcon (n := c + d)
  unfold g at hp
  rwa [← Nat.add_sub_assoc hle, Nat.add_sub_self_left] at hp

end Sequence

namespace Acc

variable {α : Sort u} {r : α → α → Prop}

open Relation

/-- `a` is not accessible through a binary relation `r` if there exists an infinite descending chain
starting from `a`. -/
theorem not_acc_of_exists_descending_chain {a : α} (h : ∃ (f : Nat → α), f 0 = a ∧
    ∀ (n : Nat), r (f (n + 1)) (f n)) : ¬Acc r a :=
  fun (acc : Acc r a) ↦ show False from Acc.recOn acc (motive := fun (x : α) (_ : Acc r x) ↦
    ¬∃ (f : Nat → α), f 0 = x ∧ ∀ (n : Nat), r (f (n + 1)) (f n))
    (fun x _ (ih : ∀ (y : α), r y x → ¬∃ (f : Nat → α), f 0 = y ∧ ∀ (n : Nat), r (f (n + 1)) (f n))
      ⟨f, hsta, hdes⟩ ↦ ih (f 1) (show r (f 1) x from hsta ▸ hdes 0)
        (show ∃ (g : Nat → α), g 0 = f 1 ∧ ∀ (n : Nat), r (g (n + 1)) (g n) from
          ⟨(f <| · + 1),
            show f (0 + 1) = f 1 from rfl,
            fun n ↦ show r (f (n + 2)) (f (n + 1)) from hdes (n + 1)⟩))
    (h : ∃ (f : Nat → α), f 0 = a ∧ ∀ (n : Nat), r (f (n + 1)) (f n))

theorem asymm_of_acc_above {a : α} (acc : Acc r a) ⦃b : α⦄ : r b a → ¬r a b := by
  intro hr hnr
  let f (n : Nat) : α := if n % 2 = 0 then a else b
  have is_infinite_descending_chain (n : Nat) : r (f (n + 1)) (f n) := by
    if hn : n % 2 = 0 then
      have hn1 : (n + 1) % 2 = 1 := by simp [Nat.add_mod n 1 2, hn]
      simpa [f, hn, hn1]
    else
      have hn1 : (n + 1) % 2 = 0 := by simp [Nat.add_mod n 1 2, Nat.mod_two_ne_zero.mp hn]
      simpa [f, hn, hn1]
  have nacc : ¬Acc r a :=
    not_acc_of_exists_descending_chain ⟨f, by simp [f], is_infinite_descending_chain⟩
  contradiction

theorem asymm_of_acc_below {a : α} (acc : Acc r a) ⦃b : α⦄ : r a b → ¬r b a :=
  imp.swap.mp (asymm_of_acc_above acc (b := b))

/-- `a` is not accessible through a binary relation `r` if there exists a descending cycle starting
from and ending at `a`. -/
theorem not_acc_of_has_cycle {a : α} {f : Nat → α}
    (hsta : f 0 = a)
    ⦃last : Nat⦄
    (hpos : 0 < last)
    (hdes : ∀ ⦃n : Nat⦄, n < last → r (f (n + 1)) (f n))
    (hlas : f last = a) :
    ¬Acc r a := by
  let g (n : Nat) : α := f (n % last)
  refine not_acc_of_exists_descending_chain ⟨g, hsta, ?_⟩
  intro n
  induction n, last using Nat.mod.inductionOn with
  | base n last h =>
    have hlt : n < last :=  Nat.lt_of_not_le (not_and.mp h hpos)
    have hg : g n = f n := by simp [g, Nat.mod_eq_of_lt hlt]
    have hg1 : g (n + 1) = f (n + 1) := by
      unfold g
      match Nat.lt_or_eq_of_le (hlt : n + 1 ≤ last) with
      | Or.inl (h1lt : n + 1 < last) => rw [Nat.mod_eq_of_lt h1lt]
      | Or.inr (h1eq : n + 1 = last) => rw [h1eq, Nat.mod_self, hsta, hlas]
    rw [hg, hg1]
    exact hdes hlt
  | ind n last hbet IH =>
    have hle1 : last ≤ n + 1 := (Nat.le_trans hbet.2 (Nat.le_succ n))
    have hgl : g (n - last) = g n := by simp [g, Nat.mod_eq_sub_mod hbet.2]
    have hgl1 : g (n - last + 1) = g (n + 1) := by
      simp [g, ← Nat.sub_add_comm hbet.2, Nat.mod_eq_sub_mod hle1]
    rw [← hgl, ← hgl1]
    exact IH hpos hdes hlas

theorem not_not_descending_chain_ends_of_acc {p : α → Prop} {a : α} (acc : Acc r a) {f : Nat → α}
    (hsta : f 0 = a)
    (hcon : ∀ ⦃n : Nat⦄, p (f n) → f (n + 1) = f n)
    (hdes : ∀ ⦃n : Nat⦄, ¬p (f n) → r (f (n + 1)) (f n)) :
    ¬¬∃ (c : Nat), p (f c) ∧ ∀ ⦃m : Nat⦄, c ≤ m → f m = f c :=
  have ind_of_rec {c : Nat} (hc : p (f c)) ⦃m : Nat⦄ (hle : c ≤ m) : p (f m) :=
    Sequence.induction_of_strongRec hc hcon hle
  have const_of_rec {c : Nat} (hc : p (f c)) ⦃m : Nat⦄ (hle : c ≤ m) : f m = f c :=
    Sequence.eventually_const_of_strongRec (fun n hle ↦ show f (n + 1) = f n from
      hcon (ind_of_rec hc hle)) hle
  fun not_has_last ↦
    have not_has_min (c : Nat) : ¬p (f c) := fun hc ↦ not_has_last ⟨c, hc, const_of_rec hc⟩
    have is_infinite_descending_chain (m : Nat) : r (f (m + 1)) (f m) := hdes (not_has_min m)
    have hnac : ¬Acc r a :=
      not_acc_of_exists_descending_chain ⟨f, hsta, is_infinite_descending_chain⟩
    hnac acc

/-- If `a` is accessible through a binary relation `r`, then for every descending chain `f`, it is
not false that `f` ends at a minimal element of the set `{y : α | r y a}` with respect to `r`.  -/
theorem not_not_descending_chain_ends_at_min_of_acc {a : α} (acc : Acc r a) {f : Nat → α}
    (hsta : f 0 = a)
    (hcon : ∀ ⦃n : Nat⦄, isMin_below r a (f n) → f (n + 1) = f n)
    (hdes : ∀ ⦃n : Nat⦄, ¬isMin_below r a (f n) → r (f (n + 1)) (f n)) :
    ¬¬∃ (c : Nat), isMin_below r a (f c) ∧ ∀ ⦃m : Nat⦄, c ≤ m → f m = f c :=
  not_not_descending_chain_ends_of_acc (p := isMin_below r a) acc hsta hcon hdes

open Classical

/-- If `a` is not accessible through a binary relation `r`, then there exists an element `b` that is
below `a` and not accessible. -/
theorem exists_not_acc_lt_of_not_acc {α : Sort u} {a : α} {r : α → α → Prop} (h : ¬Acc r a) :
    ∃ (b : α), ¬Acc r b ∧ r b a := by
  rw [acc_def] at h
  simpa [and_comm] using h

variable {α : Sort u} {r : α → α → Prop}

/-- If every element of a nonempty set `p` is accessible through a binary relation `r`, then the set
has a minimal element. -/
theorem has_min {p : α → Prop} (acc : ∀ ⦃x : α⦄, p x → Acc r x) (hex : ∃ (x : α), p x) :
    ∃ (min : α), p min ∧ ∀ ⦃z : α⦄, p z → ¬r z min :=
  Classical.byContradiction (not_not_has_min acc hex)

/-- If `a` is accessible through a binary relation `r` and there exists an element below `a`, then
the set `{y : α | r y a}` has a minimal element. -/
theorem has_min_below {a : α} (acc : Acc r a) (hex : ∃ (x : α), r x a) : ∃ (min : α), r min a ∧
    ∀ ⦃z : α⦄, r z a → ¬r z min :=
  Classical.byContradiction (not_not_has_min_below acc hex)

/-- `x` is not accessible through a binary relation `r` if and only if there exists an infinite
descending chain starting from `x`. -/
theorem not_acc_iff_exists_descending_chain {x : α} :
    ¬Acc r x ↔ ∃ (f : Nat → α), f 0 = x ∧ ∀ (n : Nat), r (f (n + 1)) (f n) where
  mp nacc :=
    let f : Nat → {a : α // ¬Acc r a} :=
      Nat.rec
        (zero := show {a : α // ¬Acc r a} from ⟨x, nacc⟩)
        (succ := fun (_n : Nat) (a : {a : α // ¬Acc r a}) ↦
          let b : α := Classical.choose (exists_not_acc_lt_of_not_acc a.property)
          have hb : ¬Acc r b ∧ r b a :=
            Classical.choose_spec (exists_not_acc_lt_of_not_acc a.property)
          show {a : α // ¬Acc r a} from ⟨b, hb.1⟩)
    ⟨(f · |>.val), rfl, fun (n : Nat) ↦ show r (f (n + 1)).val ((f n).val) from
      have hfn1 : ¬Acc r (f (n + 1)).val ∧ r (f (n + 1)).val (f n).val :=
        Classical.choose_spec <| exists_not_acc_lt_of_not_acc (f n).property
      hfn1.2⟩
  mpr := not_acc_of_exists_descending_chain

theorem descending_chain_ends_of_acc {p : α → Prop} {a : α} (acc : Acc r a) {f : Nat → α}
    (hsta : f 0 = a)
    (hcon : ∀ ⦃n : Nat⦄, p (f n) → f (n + 1) = f n)
    (hdes : ∀ ⦃n : Nat⦄, ¬p (f n) → r (f (n + 1)) (f n)) :
    ∃ (c : Nat), p (f c) ∧ ∀ ⦃m : Nat⦄, c ≤ m → f m = f c :=
  Classical.byContradiction (not_not_descending_chain_ends_of_acc acc hsta hcon hdes)

/-- If `a` is accessible through a binary relation `r`, then every descending chain ends at a
minimal element of the set `{y : α | r y a}` with respect to `r`. -/
theorem descending_chain_ends_at_min_of_acc {a : α} (acc : Acc r a) {f : Nat → α}
    (hsta : f 0 = a)
    (hcon : ∀ ⦃n : Nat⦄, isMin_below r a (f n) → f (n + 1) = f n)
    (hdes : ∀ ⦃n : Nat⦄, ¬isMin_below r a (f n) → r (f (n + 1)) (f n)) :
    ∃ (c : Nat), isMin_below r a (f c) ∧ ∀ ⦃m : Nat⦄, c ≤ m → f m = f c :=
  Classical.byContradiction (not_not_descending_chain_ends_at_min_of_acc acc hsta hcon hdes)

end Acc

/-- No integer is accessible through the less-than relation `<` on the integers. -/
theorem Int.not_acc_lt (a : Int) : ¬Acc (· < ·) a :=
  fun (acc : Acc (· < ·) a) ↦
    have hnnm := Acc.not_not_has_min_below acc (show ∃ z, z < a from ⟨a - 1, by simp +arith⟩)
    hnnm <| fun hmin ↦
    let ⟨min, hlma, hnlm⟩ := hmin
    have hlpm : min - 1 < min := by simp +arith
    have hnlpm : ¬min - 1 < min := hnlm (show min -1 < a from Int.lt_trans hlpm hlma)
    hnlpm hlpm
