import Mathlib.Data.Prod.Basic

open Nat hiding iterate

-- 1.9, 1.10
def iterate {α : Type} (f : α → α) (n : Nat) (x : α) :=
  match n with
  | zero => x
  | succ m => f (iterate f m x)

-- Exercise 1.9.2
example : ∀ {n x : Nat}, n + x = iterate succ n x := by
  intro n x
  induction n <;> unfold iterate
  · simp [Nat.add]
  · rename_i m IH
    have Hs : m + 1 + x = m + x + 1 := by
      apply Nat.succ_add_eq_add_succ m x
    rw [Hs]; rw [IH]

example : ∀ {n x : Nat}, x ^ n = iterate (Nat.mul x) n 1 := by
  intro n x
  induction n
  · unfold iterate; apply Nat.pow_zero
  · rename_i m IH
    rw [Nat.pow_succ x m]
    rw [IH]
    simp [iterate]
    apply Nat.mul_comm

-- Exercise 1.9.4 (Shift)
theorem shift : ∀ {α : Type} {f : α → α} {n x},
  iterate f (succ n) x = iterate f n (f x)
  := by
  intro α f n x; induction n
  · simp [iterate]
  · rename_i m IH
    have H' : iterate f (m + 1).succ x = f (iterate f (m + 1) x) :=
      by simp [iterate]
    rw [H']; rw [IH]; simp [iterate]

-- Exercise 1.9.5 (Tail recursive iteration)
def iter {α : Type} (f : α → α) (n : Nat) (x : α) :=
  iter' f n x
  where
    iter' {α : Type} (f : α → α) (n : Nat) (accum : α) :=
      match n with
      | zero => accum
      | succ m => iter' f m (f accum)

theorem iter_shift : ∀ {α : Type} (f : α → α) (n x),
  iter f (succ n) x = f (iter f n x)
  := by
  intro α f n x; revert x; induction n
  · simp [iter, iter.iter']
  · rename_i m IH; intro x
    simp [iter, iter.iter'] at IH
    simp [iter, iter.iter']
    apply IH

example : ∀ {α : Type} {f : α → α} {n x},
  iterate f n x = iter f n x
  := by
  intro α f n x; induction n
  · simp [iterate, iter, iter.iter']
  · rename_i m IH
    simp [iterate]
    rw [IH]
    rw [iter_shift f m x]

-- Exercise 1.9.6 (Even)
open Bool

example : ∀ {n b}, iterate not (n * 2) b = b := by
  intro n b; induction n
  · rfl
  · rename_i m IH
    simp [iterate]
    rw [Nat.succ_add]
    simp [iterate]
    rw [←Nat.two_mul, Nat.mul_comm]
    apply IH

-- Exercise 1.9.7 (Factorials with iteration)
def fact : Nat → Nat
  | zero => 1
  | succ n => succ n * fact n

def succ_and_mul : (Nat × Nat) → (Nat × Nat)
  | (n, k) => (succ n, succ n * k)

example : ∀ {n}, (n, fact n) = iterate succ_and_mul n (0,1)
  := by
  intro n; induction n
  . simp [iterate]; rfl
  . rename_i m IH
    simp [fact, iterate, succ_and_mul]
    simp [Prod.eq_iff_fst_eq_snd_eq] at IH
    have Hf := IH.left
    have Hs := IH.right
    apply And.intro
    . apply Hf
    . rw [← Hs, ←Hf]

-- Exercise 1.9.8 (Fibonacci with iteration)
def fib_prod : Nat × Nat → Nat × Nat
  | (n,k) => (n + k, n)
