import Mathlib.Data.Int.Fib.Basic

namespace Axeyum.Autogenesis

theorem intFibonacciRecurrenceUniqueV1
    (f g : Int → Int)
    (succ pred : Int → Int)
    (succ_pred : ∀ n : Int, succ (pred n) = n)
    (pred_succ : ∀ n : Int, pred (succ n) = n)
    (induct : ∀ P : Int → Prop, P 0 →
      (∀ n : Int, P n → P (succ n)) →
      (∀ n : Int, P n → P (pred n)) → ∀ n : Int, P n)
    (cancel_right : ∀ a b c : Int, a + c = b + c → a = b)
    (f_step : ∀ n : Int, f (succ n) = f (pred n) + f n)
    (g_step : ∀ n : Int, g (succ n) = g (pred n) + g n)
    (zero_eq : f 0 = g 0)
    (succ_zero_eq : f (succ 0) = g (succ 0)) :
    ∀ n : Int, f n = g n := by
  let P := fun n : Int => f n = g n ∧ f (succ n) = g (succ n)
  have base : P 0 := And.intro zero_eq succ_zero_eq
  have forward : ∀ n : Int, P n → P (succ n) := by
    intro n hn
    apply And.intro hn.right
    calc
      f (succ (succ n)) = f (pred (succ n)) + f (succ n) := f_step (succ n)
      _ = f n + f (succ n) :=
        congrArg (fun x => x + f (succ n)) (congrArg f (pred_succ n))
      _ = g n + f (succ n) := congrArg (fun x => x + f (succ n)) hn.left
      _ = g n + g (succ n) := congrArg (fun x => g n + x) hn.right
      _ = g (pred (succ n)) + g (succ n) :=
        congrArg (fun x => x + g (succ n)) (congrArg g (pred_succ n)).symm
      _ = g (succ (succ n)) := (g_step (succ n)).symm
  have backward : ∀ n : Int, P n → P (pred n) := by
    intro n hn
    have sums : f (pred n) + f n = g (pred n) + g n :=
      (f_step n).symm.trans (hn.right.trans (g_step n))
    have same_right : f (pred n) + g n = g (pred n) + g n :=
      (congrArg (fun x => f (pred n) + x) hn.left).symm.trans sums
    have previous : f (pred n) = g (pred n) :=
      cancel_right (f (pred n)) (g (pred n)) (g n) same_right
    apply And.intro previous
    calc
      f (succ (pred n)) = f n := congrArg f (succ_pred n)
      _ = g n := hn.left
      _ = g (succ (pred n)) := (congrArg g (succ_pred n)).symm
  exact fun n => (induct P base forward backward n).left

end Axeyum.Autogenesis
