Require Import ZNatPairs.
Require Import Zsqrt.

(** 
    encode(k1, k2) = (k1 + k2) * (k1 + k2 + 1) / 2 + k2  
**)

(** The definition of encode makes it clear that the result of
    encoding is a rational (Q).  However, it can be proven that 
    encoding actually results in a natural because the denominator
    is always even, and dividing any even number by 2 gives a natural.
**)

Definition encode (k : (nat * nat)) : nat :=
  (((fst k) + (snd k)) * ((fst k) + (snd k) + 1) + 2 * (snd k)).


(** ^^ this whole thing should be divided by two **)

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

Definition W (z : nat) : nat :=
O.

Definition T (w : nat) : nat :=
O.

Definition decode (z : nat) : (nat * nat) :=
((W z) - (z - T (W z)), (z - (T (W z)))).

Theorem decode_encode : forall x y ,
    decode (encode (x, y)) = (x, y).

Theorem encode_decode : forall z ,
    encode (decode z) = z.