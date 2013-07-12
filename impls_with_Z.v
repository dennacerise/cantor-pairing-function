Require Import R_sqrt.
Require Import Rdefinitions.
Require Import Raxioms.
Require Import RIneq.
(** Require Import QArith. **)
Require Import ZNatPairs.
Require Import Zsqrt.
Require Import R_Ifp.
Require Import Even.
Require Import Znat.

Open Scope Z_scope.


(** 
    encode(k1, k2) = (k1 + k2) * (k1 + k2 + 1) / 2 + k2  
**)

Definition encode (k : (Z * Z)) : Z :=
  let x := fst k in
  let y := snd k in
  (Zdiv2 (x + y) * (x + y + 1)) 
 + y.

(** 
    decode(z):
        w = (sqrt(8z + 1) - 1) / 2
        t = (w^2 + w) / 2
        y = z - t
        x = w - y
        return <x, y>

    x = w - (z - t)
    y = z - t
**)

Definition to_pos (z:Z) : positive :=
  match z with
    | Zpos p => p
    | _ => 1%positive
  end.

Definition Zsqrt_plain_pos (p : positive) : positive :=
to_pos (Zsqrt_plain (Zpos p)).

Definition Result (z:Z) : R :=
  (Rdiv 
    (Rminus 
      (sqrt (8 * (IZR z) + 1)) 
       1) 
     2).

Definition T_Z (w : Z) : Z :=
Z0.

Definition decode (z:Z) : (Z * Z) :=
  let w := Int_part (Result z) in
  let t := T_Z w in
  let y := z - t in
  let x := w - y in
  (x, y).

Definition Result_Z (t : Z) : Z :=
  Zdiv2 ((Zsqrt_plain (8 * t + 1)) 
      -   1).

(* w = quadratic t  *)

Definition w_Result_Z (w t : Z) : Prop :=
    w = Result_Z t.

Lemma consec_mult__even : forall (w : Z),
(Zeven (w * (w + 1))).
Proof.
intro w.
destruct (Zeven_odd_dec w) as [E | O].

SearchAbout Zeven.

apply Zeven_ex in E.
destruct E as [m EQ].
subst w.
(* apply Zeven_2p. *)

Admitted.

Lemma refactor_sqr_term : forall w,
(4 * (w * (w + 1)) + 1) = (2 * w + 1) * (2 * w + 1).
Proof.
intro w. ring.
Qed.

Lemma plus_minus_assoc : forall n m p,
n + m - p = n + (m - p).
Proof.
intros. ring.
Qed.

Lemma Zdiv2_Zmult2 : forall w,
w = Zdiv2 (2 * w).
Proof.
intro w. induction w; reflexivity.
Qed.

Lemma sqr_term_positive : forall w,
w >= 0 ->
0 <= 2 * w + 1.
Proof.
intros w w_pos.
omega.
Qed.

Theorem w_Result_Z_int : forall w t,
  w >= 0 ->
  t = Zdiv2 (w * (w + 1)) ->
  w_Result_Z w t.
Proof.
  intros w t w_positive t_def. subst. 
  unfold w_Result_Z. unfold Result_Z.

  assert (
        Zdiv2 (Zsqrt_plain (8 * Zdiv2 (w * (w + 1)) + 1) - 1) =
        Zdiv2 (Zsqrt_plain (4*2*Zdiv2 (w * (w + 1)) + 1) - 1)).
  reflexivity.
  rewrite -> H. clear H.


  rewrite <- Zmult_assoc.
  rewrite <- Zeven_div2.

  rewrite refactor_sqr_term.
  remember (2 * w + 1) as sqr_term.

  rewrite Zsqrt_square_id.

  rewrite Heqsqr_term.

  rewrite plus_minus_assoc.
  rewrite (Zminus_diag 1).
  rewrite Zplus_0_r.

  apply Zdiv2_Zmult2.

  rewrite Heqsqr_term.
  apply sqr_term_positive. exact w_positive.

  apply consec_mult__even.
Qed.

(*
define decreasing
increasing f -> n <= m <-> f n <= f m
increasing result
therefore n <= m -> result n <= result m
*)

Definition increasing f : Prop := forall x y, x <= y -> f x <= f y.

Lemma Result_Z_increasing :
increasing Result_Z.
Proof.
  unfold increasing.
  intros.
  unfold Result_Z.
  assert (increasing Zdiv2). admit.
  apply H0.
  assert (increasing Zsqrt_plain). admit.
  assert (increasing (fun x => x - 1)). admit.
  apply H2. apply H1. omega.
Qed.
  

(* t <= z < t + w + 1  ->
   w <= Result z < w + 1  *)
Theorem z_bounds : forall (w t z : Z),
 w_Result_Z w t ->
 t <= z -> z < (t + w + 1) ->
 w <= (Result_Z z) < (w + 1).
Proof.
  intros w t z H1 H2 H3.
  split.
  unfold w_Result_Z in H1. subst w.
  assert (increasing Result_Z).
  apply Result_Z_increasing.
  apply H. exact H2.

  unfold w_Result_Z in H1.
  subst w.
Admitted.

Definition Zfloor (x : R) := (up x - 1)%Z.

(* w <= Result z < w + 1  ->
   w = floor (Result z)  *)
Theorem w__floor_Result_Z : forall (w z : Z),
  Zle w (Result_Z z) -> Zlt (Result_Z z) (w + 1) ->
  w = Zfloor (Result z).
Proof.
  intros w z H1 H2.
  unfold Zfloor.
  (* change definitions to Zfloor instead of Int_part! *)
Admitted.


Theorem decode_encode : forall x y ,
    decode (encode (x, y)) = (x, y).
Proof.
  intros x y.
Admitted.

Theorem encode_decode : forall z ,
    encode (decode z) = z.
Proof.
  intros. unfold decode. unfold encode. simpl.
Admitted.

Close Scope Z_scope.