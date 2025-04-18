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


Require Export Iterator.
Require Export UList.
Open Scope Z_scope.
 
Theorem next_n_Z: forall n m,  next_n Z.succ n m = n + Z_of_nat m.
intros n m; generalize n; elim m; clear n m.
intros n; simpl; auto with zarith.
intros m H n.
replace (n + Z_of_nat (S m)) with (Z.succ n + Z_of_nat m); auto with zarith.
rewrite <- H; auto with zarith.
Qed.
 
Theorem Zprogression_end:
 forall n m,
  progression Z.succ n (S m) =
  app (progression Z.succ n m) (cons (n + Z_of_nat m) nil).
intros n m; generalize n; elim m; clear n m.
simpl; intros; apply f_equal2 with ( f := @cons Z ); auto with zarith.
intros m1 Hm1 n1.
apply trans_equal with (cons n1 (progression Z.succ (Z.succ n1) (S m1))); auto.
rewrite Hm1.
replace (Z.succ n1 + Z_of_nat m1) with (n1 + Z_of_nat (S m1)); auto with zarith.
Qed.
 
Theorem Zprogression_pred_end:
 forall n m,
  progression Z.pred n (S m) =
  app (progression Z.pred n m) (cons (n - Z_of_nat m) nil).
intros n m; generalize n; elim m; clear n m.
simpl; intros; apply f_equal2 with ( f := @cons Z ); auto with zarith.
intros m1 Hm1 n1.
apply trans_equal with (cons n1 (progression Z.pred (Z.pred n1) (S m1))); auto.
rewrite Hm1.
replace (Z.pred n1 - Z_of_nat m1) with (n1 - Z_of_nat (S m1)); auto with zarith.
Qed.
 
Theorem Zprogression_opp:
 forall n m,
  rev (progression Z.succ n m) = progression Z.pred (n + Z_of_nat (pred m)) m.
intros n m; generalize n; elim m; clear n m.
simpl; auto.
intros m Hm n.
rewrite (Zprogression_end n); auto.
rewrite distr_rev.
rewrite Hm; simpl; auto.
case m.
simpl; auto.
intros m1;
 replace (n + Z_of_nat (pred (S m1))) with (Z.pred (n + Z_of_nat (S m1))); auto.
rewrite inj_S; simpl; (unfold Z.pred; unfold Z.succ); auto with zarith.
Qed.
 
Theorem Zprogression_le_init:
 forall n m p, In p (progression Z.succ n m) ->  (n <= p).
intros n m; generalize n; elim m; clear n m; simpl; auto.
intros; contradiction.
intros m H n p [H1|H1]; auto with zarith.
generalize (H _ _ H1); auto with zarith.
Qed.
 
Theorem Zprogression_le_end:
 forall n m p, In p (progression Z.succ n m) ->  (p < n + Z_of_nat m).
intros n m; generalize n; elim m; clear n m; auto.
intros; contradiction.
intros m H n p H1; simpl in H1 |-; case H1; clear H1; intros H1;
 auto with zarith.
rewrite inj_S; rewrite <- Zplus_succ_comm; auto with zarith.
Qed.
 
Theorem ulist_Zprogression: forall a n,  ulist (progression Z.succ a n).
intros a n; generalize a; elim n; clear a n; simpl; auto with zarith.
intros n H1 a; apply ulist_cons; auto.
intros H2; absurd (Z.succ a <= a); auto with zarith.
apply Zprogression_le_init with ( 1 := H2 ).
Qed.
 
Theorem in_Zprogression:
 forall a b n, ( a <= b < a + Z_of_nat n ) ->  In b (progression Z.succ a n).
intros a b n; generalize a b; elim n; clear a b n; auto with zarith.
simpl; auto with zarith.
intros n H a b.
replace (a + Z_of_nat (S n)) with (Z.succ a + Z_of_nat n); auto with zarith.
intros [H1 H2]; simpl; auto with zarith.
case (Zle_lt_or_eq _ _ H1); auto with zarith.
Qed.
