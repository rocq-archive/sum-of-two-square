(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(***********************************************************************
    Proof of Bertrand's conjecture: Product.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Import ZArith.
Require ZArithRing.
Require Export Aux.
Require Export Iterator.
Require Export ZProgression.
(* *  	Iterated Product:
   (Zprod n m f) = f(n).f(n+1)...f(m)*)
Open Scope Z_scope.
 
Definition Zprod :=
   fun n m f =>
   if Zle_bool n m
     then iter 1 f Zmult (progression Z.succ n (Z.abs_nat ((1 + m) - n)))
     else iter 1 f Zmult (progression Z.pred n (Z.abs_nat ((1 + n) - m))).
Hint Unfold Zprod : core.
 
Lemma Zprod_nn: forall (n : Z) (f : Z ->  Z),  Zprod n n f = f n.
intros n f; unfold Zprod; rewrite Zle_bool_refl.
replace ((1 + n) - n) with 1; auto with zarith.
simpl; ring.
Qed.
 
Theorem permutation_rev: forall (A:Set) (l : list A),  permutation (rev l) l.
intros a l; elim l; simpl; auto.
intros a1 l1 Hl1.
apply permutation_trans with (cons a1 (rev l1)); auto.
Qed.
 
Lemma Zprod_swap: forall (n m : Z) (f : Z ->  Z),  Zprod n m f = Zprod m n f.
intros n m f; unfold Zprod.
generalize (Zle_cases n m) (Zle_cases m n); case (Zle_bool n m);
 case (Zle_bool m n); auto with arith.
intros; replace n with m; auto with zarith.
3:intros H1 H2; contradict H2; auto with zarith.
intros H1 H2; apply iter_permutation; auto with zarith.
apply permutation_trans
     with (rev (progression Z.succ n (Z.abs_nat ((1 + m) - n)))).
apply permutation_sym; apply permutation_rev.
rewrite Zprogression_opp; auto with zarith.
replace (n + Z_of_nat (pred (Z.abs_nat ((1 + m) - n)))) with m; auto.
replace (Z.abs_nat ((1 + m) - n)) with (S (Z.abs_nat (m - n))); auto with zarith.
intros H1 H2; apply iter_permutation; auto with zarith.
apply permutation_trans
     with (rev (progression Z.succ m (Z.abs_nat ((1 + n) - m)))).
rewrite Zprogression_opp; auto with zarith.
replace (m + Z_of_nat (pred (Z.abs_nat ((1 + n) - m)))) with n; auto.
replace (Z.abs_nat ((1 + n) - m)) with (S (Z.abs_nat (n - m))); auto with zarith.
apply permutation_rev.
Qed.

 
Lemma Zprod_split_up:
 forall (n m p : Z) (f : Z ->  Z),
 ( n <= m < p ) ->  Zprod n p f = Zprod n m f * Zprod (m + 1) p f.
intros n m p f [H H0].
case (Zle_lt_or_eq _ _ H); clear H; intros H.
unfold Zprod; (repeat rewrite Zle_imp_le_bool); auto with zarith.
assert (H1: n < p).
apply Z.lt_trans with ( 1 := H ); auto with zarith.
assert (H2: m < 1 + p).
apply Z.lt_trans with ( 1 := H0 ); auto with zarith.
assert (H3: n < 1 + m).
apply Z.lt_trans with ( 1 := H ); auto with zarith.
assert (H4: n < 1 + p).
apply Z.lt_trans with ( 1 := H1 ); auto with zarith.
replace (Z.abs_nat ((1 + p) - (m + 1)))
     with (minus (Z.abs_nat ((1 + p) - n)) (Z.abs_nat ((1 + m) - n))).
apply iter_progression_app; auto with zarith.
(repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
rewrite next_n_Z; auto with zarith.
rewrite <- Zabs2Nat.inj_sub; auto with zarith.
subst m.
rewrite Zprod_nn; auto with zarith.
unfold Zprod; generalize (Zle_cases n p); generalize (Zle_cases (n + 1) p);
 case (Zle_bool n p); case (Zle_bool (n + 1) p); auto with zarith.
intros H1 H2.
replace (Z.abs_nat ((1 + p) - n)) with (S (Z.abs_nat (p - n))); auto with zarith.
replace (n + 1) with (Z.succ n); auto with zarith.
replace ((1 + p) - Z.succ n) with (p - n); auto with zarith.
Qed.
 
Lemma Zprod_S_left:
 forall (n m : Z) (f : Z ->  Z), n < m ->  Zprod n m f = f n * Zprod (n + 1) m f.
intros n m f H; rewrite (Zprod_split_up n n m f); auto with zarith.
rewrite Zprod_nn; auto with zarith.
Qed.
 
Lemma Zprod_S_right:
 forall (n m : Z) (f : Z ->  Z),
 n <= m ->  Zprod n (m + 1) f = Zprod n m f * f (m + 1).
intros n m f H; rewrite (Zprod_split_up n m (m + 1) f); auto with zarith.
rewrite Zprod_nn; auto with zarith.
Qed.
 
Lemma Zprod_split_down:
 forall (n m p : Z) (f : Z ->  Z),
 (p < m <= n) ->  Zprod n p f = Zprod n m f * Zprod (m - 1) p f.
intros n m p f [H H0].
case (Zle_lt_or_eq p (m - 1)); auto with zarith; intros H1.
pattern m at 1; replace m with ((m - 1) + 1); auto with zarith.
repeat rewrite (Zprod_swap n).
rewrite (Zprod_swap (m - 1)).
rewrite Zmult_comm.
apply Zprod_split_up; auto with zarith.
subst p.
repeat rewrite (Zprod_swap n).
rewrite Zprod_nn.
unfold Zprod; (repeat rewrite Zle_imp_le_bool); auto with zarith.
replace (Z.abs_nat ((1 + n) - (m - 1))) with (S (Z.abs_nat (n - (m - 1)))).
rewrite Zmult_comm.
replace (Z.abs_nat ((1 + n) - m)) with (Z.abs_nat (n - (m - 1))); auto with zarith.
pattern m at 4; replace m with (Z.succ (m - 1)); auto with zarith.
apply inj_eq_inv; auto with zarith.
Qed.
 
Lemma Zprod_ext:
 forall (n m : Z) (f g : Z ->  Z),
 n <= m ->
 (forall (x : Z), ( n <= x <= m ) ->  f x = g x) ->  Zprod n m f = Zprod n m g.
intros n m f g HH H.
unfold Zprod; auto.
unfold Zprod; (repeat rewrite Zle_imp_le_bool); auto with zarith.
apply iter_ext; auto with zarith.
intros a H1; apply H; auto; split.
apply Zprogression_le_init with ( 1 := H1 ).
cut (a < Z.succ m); auto with zarith.
replace (Z.succ m) with (n + Z_of_nat (Z.abs_nat ((1 + m) - n))); auto with zarith.
apply Zprogression_le_end; auto with zarith.
Qed.
 
Lemma Zprod_mult:
 forall (n m : Z) (f g : Z ->  Z),
  Zprod n m f * Zprod n m g = Zprod n m (fun (i : Z) => f i * g i).
intros n m f g; unfold Zprod; case (Zle_bool n m); apply iter_comp;
 auto with zarith.
Qed.
 
Lemma inv_Zprod:
 forall (P : Z ->  Prop) (n m : Z) (f : Z ->  Z),
 n <= m ->
 P 1 ->
 (forall (a b : Z), P a -> P b ->  P (a * b)) ->
 (forall (x : Z), ( n <= x <= m ) ->  P (f x)) ->  P (Zprod n m f).
intros P n m f HH H H0 H1.
unfold Zprod; rewrite Zle_imp_le_bool; auto with zarith; apply iter_inv; auto.
intros x H3; apply H1; auto; split.
apply Zprogression_le_init with ( 1 := H3 ).
cut (x < Z.succ m); auto with zarith.
replace (Z.succ m) with (n + Z_of_nat (Z.abs_nat ((1 + m) - n))); auto with zarith.
apply Zprogression_le_end; auto with zarith.
Qed.
 
Lemma Zprod_pred:
 forall (n m : Z) (f : Z ->  Z),
  Zprod n m f = Zprod (n + 1) (m + 1) (fun (i : Z) => f (Z.pred i)).
intros n m f.
unfold Zprod.
generalize (Zle_cases n m); generalize (Zle_cases (n + 1) (m + 1));
 case (Zle_bool n m); case (Zle_bool (n + 1) (m + 1)); auto with zarith.
replace ((1 + (m + 1)) - (n + 1)) with ((1 + m) - n); auto with zarith.
intros H1 H2; cut (exists c , c = Z.abs_nat ((1 + m) - n) ).
intros [c H3]; rewrite <- H3.
generalize n; elim c; auto with zarith; clear H1 H2 H3 c n.
intros c H n; simpl; (apply f_equal2 with ( f := Zmult ); auto with zarith).
apply f_equal with ( f := f ); unfold Z.pred; auto with zarith.
replace (Z.succ (n + 1)) with (Z.succ n + 1); auto with zarith.
exists (Z.abs_nat ((1 + m) - n)); auto.
replace ((1 + (n + 1)) - (m + 1)) with ((1 + n) - m); auto with zarith.
intros H1 H2; cut (exists c , c = Z.abs_nat ((1 + n) - m) ).
intros [c H3]; rewrite <- H3.
generalize n; elim c; auto with zarith; clear H1 H2 H3 c n.
intros c H n; simpl; (apply f_equal2 with ( f := Zmult ); auto with zarith).
apply f_equal with ( f := f ); unfold Z.pred; auto with zarith.
replace (Z.pred (n + 1)) with (Z.pred n + 1); auto with zarith.
unfold Z.pred; auto with zarith.
exists (Z.abs_nat ((1 + n) - m)); auto.
Qed.
Hint Unfold Zprod : core.
 
Theorem Zprod_c:
 forall (c p q : Z), p <= q ->  Zprod p q (fun x => c) = Zpower c ((1 + q) - p).
intros c p q Hq; unfold Zprod.
rewrite Zle_imp_le_bool; auto with zarith.
pattern ((1 + q) - p) at 2; rewrite <- Z_of_nat_Zabs_nat; auto with zarith.
cut (exists r , r = Z.abs_nat ((1 + q) - p) );
 [intros [r H1]; rewrite <- H1 | exists (Z.abs_nat ((1 + q) - p))]; auto.
generalize p; elim r; auto with zarith.
intros n H p0; replace (Z_of_nat (S n)) with (Z_of_nat n + 1); auto with zarith.
rewrite Zpower_exp; simpl; auto with zarith.
rewrite (Zmult_comm c).
apply f_equal2 with ( f := Zmult ); auto with zarith.
Qed.
 
Theorem Zprod_Zprod_f:
 forall (i j k l : Z) (f : Z -> Z ->  Z),
 i <= j ->
 k < l ->
  Zprod i j (fun x => Zprod k (l + 1) (fun y => f x y)) =
  Zprod i j (fun x => Zprod k l (fun y => f x y) * f x (l + 1)).
intros; apply Zprod_ext; intros; auto with zarith.
rewrite Zprod_S_right; auto with zarith.
Qed.
 
Theorem Zprod_com:
 forall (i j k l : Z) (f : Z -> Z ->  Z),
  Zprod i j (fun x => Zprod k l (fun y => f x y)) =
  Zprod k l (fun y => Zprod i j (fun x => f x y)).
intros; unfold Zprod; case (Zle_bool i j); case (Zle_bool k l); apply iter_com;
 auto with zarith.
Qed.
 
Theorem Zprod_le:
 forall (n m : Z) (f g : Z ->  Z),
 n <= m ->
 (forall (x : Z), ( n <= x <= m ) ->  ( 0 <= f x <= g x )) ->
  ( 0 <= Zprod n m f <= Zprod n m g ).
intros n m f g Hl H.
unfold Zprod; rewrite Zle_imp_le_bool; auto with zarith.
unfold Zprod;
 cut
  (forall x,
   In x (progression Z.succ n (Z.abs_nat ((1 + m) - n))) ->  ( 0 <= f x <= g x )).
elim (progression Z.succ n (Z.abs_nat ((1 + m) - n))); simpl; auto with zarith.
intros a l H0 H1; split; auto with zarith.
apply Zmult_le_0_compat; auto with zarith.
case (H1 a); auto with zarith.
case H0; auto with zarith.
apply Zmult_le_compat; auto with zarith.
case (H1 a); auto with zarith.
case H0; auto with zarith.
case (H1 a); auto with zarith.
case H0; auto with zarith.
intros x H1; apply H; split.
apply Zprogression_le_init with ( 1 := H1 ); auto.
cut (x < m + 1); auto with zarith.
replace (m + 1) with (n + Z_of_nat (Z.abs_nat ((1 + m) - n))); auto with zarith.
apply Zprogression_le_end; auto with zarith.
Qed.
