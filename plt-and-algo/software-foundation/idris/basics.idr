plus_0_l : (n:Nat) -> 0 + n = n
plus_0_l _ = Refl

plus_s_l : (n:Nat) -> (m:Nat) -> (S n) + m = S (n + m)
plus_s_l Z m = Refl
plus_s_l (S n) m = cong (plus_s_l n m)

plus_0_l_rev : (n:Nat) -> n = 0 + n
plus_0_l_rev Z = Refl
plus_0_l_rev (S k) = cong (plus_0_l_rev k)

-- cong : {f : u -> v} -> a = b -> f a = f b
plus_id_example : {n, m : Nat} -> n = m -> n + n = m + m
plus_id_example prf = cong {f=twice} prf
 where
   twice : (n:Nat) -> Nat
   twice n = n + n
-- plus_id_example n m h = rewrite h in Refl
-- ^ From idris-hackers/software-foundations:src/Basics.lidr

-- cong : {f : u -> v} -> a = b -> f a = f b
-- plus : Nat -> Nat -> Nat
-- nm : n = m
-- cong {f=plus} nm = plus n = plus m : Nat -> Nat
plus_id_exercise : {n, m, o : Nat} -> n = m -> m = o -> n + m = m + o
-- plus_id_exercise n m o nm mo = cong {f=(cong {f=plus} nm)} mo
-- plus_id_exercise n m o nm mo = rewrite (plus_id_example n m nm) in Refl
plus_id_exercise {n} {m} {o} nm mo = ?wtf


