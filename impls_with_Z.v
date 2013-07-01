Require Import R_sqrt.
Require Import Rdefinitions.
Require Import Raxioms.
Require Import RIneq.
(** Require Import QArith. **)
Require Import ZNatPairs.
Require Import Zsqrt.
Require Import R_Ifp.
Require Import Even.


(** 
    encode(k1, k2) = (k1 + k2) * (k1 + k2 + 1) / 2 + k2  
**)

Definition encode (k : (Z * Z)) : Z :=
  let x := fst k in
  let y := snd k in
  Zplus 
    (Zdiv2 (x + y) * (x + y + 1)) 
     y.

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
  let y := Zminus z t in
  let x := Zminus w y in
  (x, y).

Definition Result_Z (t : Z) : Z :=
  Zdiv2 (Zminus (Zsqrt_plain (Zplus (Zmult 8 t) 1)) 1).

(* w = quadratic t  *)

Definition w_Result_Z (w t : Z) : Prop :=
    w = Result_Z t.

Theorem w_Result_Z_int : forall w t,
   t = Zdiv2 (Zmult w (Zplus w 1)) ->
  w_Result_Z w t.
Proof.
intros. subst. unfold w_Result_Z. unfold Result_Z.
assert (Zeven (w * (w + 1))). admit.
apply Zeven_div2 in H.
(* factor the 8 into 4 * 2 then rewrite <- H *)
Admitted.

(* t <= z < t + w + 1  ->
   w <= Result z < w + 1  *)
Theorem z_bounds : forall (w t z : Z),
 Zle t z -> Zlt z (t + w + 1) ->
 Zle w (Result_Z z) -> Zlt (Result_Z z) (w + 1).
Proof.
  intros.
  unfold Result_Z.
Admitted.

(* w <= Result z < w + 1  ->
   w = floor (Result z)  *)
Theorem w__floor_Result_Z : forall (w z : Z),
  Zle w (Result_Z z) -> Zlt (Result_Z z) (w + 1) ->
  w = Int_part (Result z).
Proof.
Admitted.


Theorem decode_encode : forall x y ,
    decode (encode (x, y)) = (x, y).
Proof.
 intros x y.
Admitted.

Theorem encode_decode : forall z ,
    encode (decode z) = z.
Proof.
Admitted.