Require Import QArith.
Require Import ZNatPairs.

(** 
    encode(k1, k2) = (k1 + k2) * (k1 + k2 + 1) / 2 + k2  
**)

Definition encode (k : (nat * nat)) : Q :=
1.


(** 
    decode(z):
        w = floor ( (sqrt(8z + 1) - 1) / 2
        t = (w^2 + w) / 2
        y = z - t
        x = w - y
        return <x, y>
**)

Definition decode (z : Q) : (nat * nat) :=
(O, O).

Theorem decode_encode : forall x y ,
    decode (encode (x, y)) = (x, y).

Theorem encode_decode : forall z ,
    encode (decode z) = z.