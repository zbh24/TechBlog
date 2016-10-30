Section Auto6.
  Variables P P1 P2 P3 P4 P5 : Prop.
    Lemma auto6 :
     (P -> P1) ->
     (P1 -> P2) -> 
     (P2 -> P3) -> 
     (P3 -> P4) ->
     (P4 -> P5) -> 
     P -> P5.
    Proof.
     auto. (* no progress *)
     auto 6.
    Qed.
End Auto6.
