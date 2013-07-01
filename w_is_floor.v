Require Import R_sqrt.
Require Import Raxioms.
Require Import QArith.
Require Import R_Ifp.


Definition Result (z:Z) : R :=
  (Rdiv 
    (Rminus 
      (sqrt (8 * (IZR z) + 1)) 
       1) 
     2).

Theorem w_is_floor : forall (w:R) (w_Z t x y z : Z),
  w = (IZR (Zplus x y)) ->
  w_Z = (Zplus x y) ->
  t = (Zdiv (Zplus (Zmult w_Z w_Z) w_Z) 2) ->
  z = (Zplus t y) ->
  Rle w (Result z) ->
  Rlt (Result z) (w + 1) ->
  w_Z = Int_part (Result z).
Proof.
  intros.
  subst.
  unfold Result.
  unfold Int_part.
  unfold Result in H3.
  unfold Result in H4.
Admitted.