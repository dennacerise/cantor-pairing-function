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

Definition to_pos (z:Z) : positive :=
  match z with
    | Zpos p => p
    | _ => 1%positive
  end.

Definition Zsqrt_plain_pos (p : positive) : positive :=
to_pos (Zsqrt_plain (Zpos p)).

Definition W (z : Q) : Q :=
 let x := (Zsqrt_plain (8 * (Qnum z) + (Zpos (Qden z)))) in
 let y := (Zsqrt_plain_pos (Qden z)) in
 Qmake (x - (Zpos y)) (2 * y).

Definition T (w : Q) : Q :=
  let a := (Qnum w) in
  let b := (Qden w) in
Qmake (a*a + a* (Zpos b)) (2 * b * b).

Definition ZofQ (x : Q) : option Z :=
  let (q,r) := Zdiv_eucl (Qnum x) (Zpos (Qden x)) in
  match r with
  | Z0 => Some q
  | Zpos r' => None
  | Zneg r' => None
  end.


Definition option_bind {A B:Type} (f : A -> option B) (o : option A) :=
match o with
| Some a => f a
| None => None
end.

Definition mdecode (z : Q) : option (Z * Z) :=
option_bind (fun lhs =>
 option_bind (fun rhs => Some (lhs, rhs))
 (ZofQ (z - (T (W z)))))
 (ZofQ ((W z) - (z - T (W z)))).

Theorem mdecode_some :
 forall z,
  { zz | mdecode z = Some zz }.
Proof.
  intros.  
Admitted.

Definition decode z :=
match mdecode_some z with
| exist zz _ => zz
end.

Theorem decode_encode : forall x y ,
    decode (encode (x, y)) = (x, y).
Proof.
 intros x y.
 unfold decode.
 remember (encode (x, y)) as exy.
 destruct (mdecode_some exy) as [[ax ay] P].

Admitted.

Theorem encode_decode : forall z ,
    encode (decode z) = z.
Proof.
Admitted.