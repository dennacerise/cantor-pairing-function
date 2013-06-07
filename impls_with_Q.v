Require Import QArith.
Require Import ZNatPairs.
Require Import Zsqrt.

(** 
    encode(k1, k2) = (k1 + k2) * (k1 + k2 + 1) / 2 + k2  
**)


Definition encode (k : (Z * Z)) : Q :=
Qmake 
  (((fst k) + (snd k)) * ((fst k) + (snd k) + 1) + 2 * (snd k))
    2.


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


(** The definition of 'w' has been refactored to facilitate
    using 'Qmake'.  The problem is that (Qden z) has type
    'positive' while it needs to have type 'Z', in order to
    take the square root of it.  Taking 'Zpos: positive -> Z'
    works, but then the whole sqrt term has type 'Z' when it
    is expected to have type 'positive'. **)

(**
Definition W (z : Q) : Q :=
Qmake
  (Qmake (Zsqrt_plain (8 * (Qnum z) + (Zpos (Qden z)))) (Zsqrt_plain (Qden z))) - 1
  2.
**)


(** this is a stand-in function with the correct types: **)
Definition W (z : Q) : Q :=
1.


(** The definition of 't' has been refactored to facilitate
    using 'Qmake'. **)
Definition T (w : Q) : Q :=
  let a := (Qnum w) in
  let b := (Qden w) in
Qmake (a*a + a* (Zpos b)) (2 * b * b).


(** This expression has type (Q * Q) when it is expected to
    have type (Z * Z).  The types of the functions guarantee
    that the results are at least rationals.  It can be proven
    that the results are in fact naturals (Z), but I'm not sure
    how to incporate that fact into the types.  **)

(**
Definition decode (z : Q) : (Z * Z) :=
((W z) - (z - T (W z)), (z - (T (W z)))).
**)

(** This is a filler function with the right types **)
Definition decode (z : Q) : (Z * Z) :=
(Z0, Z0).

Theorem decode_encode : forall x y ,
    decode (encode (x, y)) = (x, y).

Theorem encode_decode : forall z ,
    encode (decode z) = z.