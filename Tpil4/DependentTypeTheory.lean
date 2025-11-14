#check fun (x : Nat) => x + 5-- λ and fun mean the same thing
#check λ (x : Nat) => x + 5

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2
