open classical 
#check Prop

variables P Q R : Prop 
#check P 

-- Capítulo 3, Ejemplo 3.8.1, página 20
theorem T1 (h1 : P) (h2 : Q) : P ∧ Q :=
begin
  exact and.intro h1 h2,
end

-- Capítulo 3, Ejemplo 3.8.2, página 20
theorem T2 (h1:P) (h2:P → Q) : Q  :=
begin
exact h2 h1,
end

-- Capítulo 3, Ejemplo 3.8.3, página 21
theorem T3: ¬¬P ↔ P:=
begin
split,
-- de izquierda a derecha
assume h1, 
by_contradiction h2,
exact h1 h2,
-- de derecha a izquierda
assume h1, 
by_contradiction h2, 
exact h2 h1, 
end 

-- Capítulo 3, Lema 3.11.1 reflexividad, página 22
theorem T4: P ↔ P :=
begin
split,
-- de izquierda a derecha
assume h1, 
exact h1, 
-- de derecha a izquierda
assume h1, 
exact h1,
end

-- Capítulo 3, Lema 3.11.2 simetría, página 22
theorem T5 (h1: P ↔ Q) : Q ↔ P :=
begin
split,
exact iff.elim_right h1,
exact iff.elim_left h1,
end

-- Capítulo 3, Lema 3.11.3 transitividad, página 22
theorem T6 (h1: P ↔ Q) (h2: Q ↔  R) : P ↔ R:=
begin
split, 
-- de izquierda a derecha
have h3: P → Q, exact iff.elim_left h1,
have h4: Q → R, exact iff.elim_left h2,
assume h5,
have h6: Q, exact h3 h5,
exact h4 h6,
-- de derecha a izquierda
have h3: Q → P, exact iff.elim_right h1,
have h4: R → Q, exact iff.elim_right h2,
assume h5,
have h6: Q, exact h4 h5,
exact h3 h6,
end 

-- Capítulo 3, Lema 3.12.1
theorem T7 (h1: P → Q) : P ∧ Q ↔ P:=
begin
split,
-- de izquierda a derecha
assume h2,
exact and.elim_left h2,
-- de derecha a izquierda
assume h2, 
have h3: Q, exact h1 h2, 
exact and.intro h2 h3,
end

-- Capítulo 3, Lema 3.12.2
theorem T8 (h1: P → Q) : P ∨ Q ↔ Q:=
begin
split,
--de izquierda a derecha
assume h2,
cases h2 with hP hQ,
--Caso hP
have h3: Q, exact h1 hP,
exact h3,
--Caso hQ
exact hQ,
-- de derecha a izquierda
assume h2, 
exact or.inr h2,
end

-- Capítulo 3, Lema 3.12.3
theorem T9 (h1: P) : P ∧ Q ↔ Q:=
begin
split, 
-- de izquierda a derecha 
assume h2, 
exact and.elim_right h2, 
-- de derecha a izquierda
assume h2,
exact and.intro h1 h2,
end

-- Capítulo 3, Lema 3.12.4
theorem T10 (h1: P) : ¬ P ∨ Q ↔ Q:=
begin
split,
--de izquierda a derecha
assume h2,
cases h2 with hNP hQ,
--caso hNP
have h3: false, exact hNP h1,
exact false.elim h3,
--caso hQ
exact hQ,
-- de derecha a izquierda
assume h2, 
exact or.inr h2,
end

-- Capítulo 5, Ejemplo 5.3, página 29
theorem T11: (P → Q) ↔ (¬P ∨ Q):= 
begin
split,
--de izquierda a derecha
assume h1,
have h2: P ∨ ¬ P , exact em P,
cases h2 with hP hnP,
-- caso 1
have h3: Q, exact h1 hP,
exact or.inr h3,
-- caso 2
exact or.inl hnP,
-- de derecha a izquierda
assume h1,
cases h1 with hnP hQ,
--caso 1
assume h2, 
have h3: false, exact hnP h2,
exact false.elim h3, 
--caso 2
assume h2,
exact hQ,
end

-- Capítulo 5 Teorema 5.5.1, página 30
theorem T12 : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
begin
split,
-- de izquierda a derecha
assume h1,
have h2: P → Q, exact iff.elim_left h1,
have h3: Q → P, exact iff.elim_right h1,
exact and.intro h2 h3,
--de derecha a izquierda
assume h1, 
have h2: P → Q, exact and.elim_left h1,
have h3: Q → P, exact and.elim_right h1,
split, 
-- de izquierda a derecha
exact h2,
-- de derecha a izquierda 
exact h3,
end

-- Capítulo 5 Teorema 5.5.2, página 31
theorem T13: (P → Q) ↔ (¬P ∨ Q):= 
begin
split,
--de izquierda a derecha
assume h1,
have h2: P ∨ ¬ P , exact em P,
cases h2 with hP hnP,
-- caso 1
have h3: Q, exact h1 hP,
exact or.inr h3,
-- caso 2
exact or.inl hnP,
-- de derecha a izquierda
assume h1,
cases h1 with hnP hQ,
--caso 1
assume h2, 
have h3: false, exact hnP h2,
exact false.elim h3, 
--caso 2
assume h2,
exact hQ,
end

-- Capítulo 5 Teorema 5.5.3, página 31
theorem T14: (P ∨ Q) ↔ (¬ P → Q) :=
begin
split,
--de izquierda a derecha 
assume h1,
cases h1 with hP hQ,
--caso hP
have h2: P ∨ ¬ P, exact em P,
assume h3,
have h4: false, exact h3 hP,
exact false.elim h4,
--caso hQ
assume h1,
exact hQ,
-- de derecha a izquierda
assume h1,
have h2: P ∨ ¬ P, exact em P, 
cases h2 with hP hnP,
--caso hP
exact or.inl hP,
--caso hnP
have h1: Q, exact h1 hnP,
exact or.inr h1, 
end

-- Capítulo 5 Teorema 5.5.4, página 31
theorem T15: (P ∨ Q) ↔ ¬ (¬ P ∧ ¬ Q) :=
begin
split,
-- de izquierda a derecha 
assume h1,
by_contradiction h2, 
have h3: ¬ P, exact and.elim_left h2,
have h4: ¬ Q, exact and.elim_right h2,
cases h1 with hP hQ, 
-- caso 1
exact h3 hP,
--caso 2
exact h4 hQ,
-- de derecha a izquierda
assume h1, 
have h2: P ∨ ¬ P, exact em P,
cases h2 with hP hnP,
exact or.inl hP, 
have h3: Q ∨ ¬ Q, exact em Q,
cases h3 with hQ hnQ,
exact or.inr hQ,
have h4: ¬ P ∧ ¬ Q , exact and.intro hnP hnQ,
have h5: false, exact h1 h4,
exact false.elim h5,
end

-- Capítulo 5 Teorema 5.5.5, página 31
theorem T16: (P ∧ Q) ↔ ¬ (¬ Q ∨ ¬ P):=
begin
split,
-- de izquierda a derecha
assume h1,
by_contradiction h2,
cases h2 with hnQ hnP,
have h3: Q, exact and.elim_right h1,
exact hnQ h3,
have h4: P, exact and.elim_left h1,
exact hnP h4,
-- de derecha a izquierda
assume h1,
have h2: P ∨ ¬ P, exact em P,
cases h2 with hP hnP,
have h3: Q ∨ ¬ Q, exact em Q,
cases h3 with hQ hnQ,
exact and.intro hP hQ,
have h4: ¬ Q ∨ ¬ P, exact or.inl hnQ,
have h5: false, exact h1 h4,
exact false.elim h5,
have h2: Q ∨ ¬ Q, exact em Q, 
cases h2 with hQ hnQ, 
have h3: ¬ Q ∨ ¬ P , exact or.inr hnP,
have h5: false, exact h1 h3, 
exact false.elim h5, 
have h2: ¬ Q ∨ ¬ P, exact or.inr hnP, 
have h3: false, exact h1 h2, 
exact false.elim h3, 
end

-- Capítulo 5 Teorema 5.5.6, página 31
theorem T17: (¬ P) ↔ P → false  :=
begin
split,
-- de izquierda a derecha
assume h1,
assume h2,
exact h1 h2,
-- de derecha a izquierda
assume h1,
exact h1,
end

-- Capítulo 5 Teorema 5.5.7, página 31
theorem T18: false ↔ (P ∧ ¬ P):=
begin
split,
-- de izquierda a derecha
assume h1,
exact false.elim h1, 
-- de derecha a izquierda
assume h1,
cases h1 with hP hnP,
exact hnP hP, 
end

-- Capítulo 6, Teorema 6.1, 1.1 Asociatividad de ∧ 
theorem T19: ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)):=
begin
split,
assume h1,
have h2: R, exact and.elim_right h1, 
have h3: P ∧ Q, exact and.elim_left h1,
have h4: P, exact and.elim_left h3,
have h5: Q, exact and.elim_right h3,
have h6: Q ∧ R, exact and.intro h5 h2,
exact and.intro h4 h6,
assume h1, 
have h2: P, exact and.elim_left h1,
have h3: Q ∧ R, exact and.elim_right h1,
have h4: Q, exact and.elim_left h3,
have h5: R, exact and.elim_right h3,
have h6: P ∧ Q, exact and.intro h2 h4,
exact and.intro h6 h5,
end 

-- Capítulo 6, Teorema 6.1, 1.2 Asociatividad de ∨ 
theorem T20: ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)):=
begin
split,
assume h1, 
cases h1 with hPQ hR,
cases hPQ with hP hQ,
exact or.inl hP, 
have h1: Q ∨ R, exact or.inl hQ,
exact or.inr h1,
have h1: Q ∨ R, exact or.inr hR,
exact or.inr h1,
assume h1, 
cases h1 with hP hQR,
have h1: P ∨ Q, exact or.inl  hP,
exact or.inl h1,
cases hQR with hQ hR,
have h1: P ∨ Q, exact or.inr hQ,
exact or.inl h1,
exact or.inr hR,
end

-- Capítulo 6, Teorema 6.1, 2.1 Neutro para ∧ 
theorem T21: (P ∧ ¬ false) ↔ P:=
begin
split,
assume h1,
exact and.elim_left h1,
assume h1,
have h2: ¬ false, by_contradiction h3,
exact h3,
exact and.intro h1 h2,
end

-- Capítulo 6, Teorema 6.1, 2.2 Neutro para ∨ 
theorem T22: (P ∨ false) ↔ P:=
begin
split,
-- de izquierda a derecha
assume h1,
cases h1 with hP hF,
--caso 1
exact hP,
--caso 2
exact false.elim hF,
-- de derecha a izquierda
assume h1,
exact or.inl h1,
end

-- Capítulo 6, Teorema 6.1, 3.1 Commutatividad de ∧ 
theorem T23: (P ∧ Q) ↔ (Q ∧ P):=
begin
split,
-- de izquierda a derecha
assume h1,
have h2: P, exact and.elim_left h1, 
have h3: Q, exact and.elim_right h1,
exact and.intro h3 h2, 
-- de derecha a izquierda
assume h1, 
have h2: Q, exact and.elim_left h1,
have h3: P, exact and.elim_right h1,
exact and.intro h3 h2, 
end

-- Capítulo 6, Teorema 6.1, 3.2 Commutatividad de ∨
theorem T24: (P ∨ Q) ↔ (Q ∨ P):=
begin
split, 
-- de izquierda a derecha
assume h1, 
cases h1 with hP hQ,
--caso 1
exact or.inr hP,
--caso 2
exact or.inl hQ, 
-- de derecha a izquierda
assume h1,
cases h1 with hQ hP, 
--caso 1
exact or.inr hQ,
--caso 2
exact or.inl hP, 
end

-- Capítulo 6, Teorema 6.1, 4.1 Distributividad de ∧ 
theorem T25: P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R):=
begin
split, 
assume h1, 
cases h1 with h1 h2,
have h2: P ∨ Q, exact or.inl h1,
have h3: P ∨ R, exact or.inl h1,
exact and.intro h2 h3,
have h3: Q, exact and.elim_left h2,
have h4: R, exact and.elim_right h2,
have h5: P ∨ Q, exact or.inr h3,
have h6: P ∨ R, exact or.inr h4,
exact and.intro h5 h6,
assume h1,
have h2: P ∨ Q, exact and.elim_left h1,
have h3: P ∨ R, exact and.elim_right h1,
cases h2 with hP hQ,
exact or.inl hP,
cases h3 with hP hR,
exact or.inl hP,
exact or.inr (and.intro hQ hR),
end 

-- Capítulo 6, Teorema 6.1, 4.2 Distributividad de ∨ 
theorem T26: P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R):=
begin
split, 
assume h1, 
have hP: P, exact and.elim_left h1,
have hQR: Q ∨ R, exact and.elim_right h1,
cases hQR with hQ hR,
exact or.inl (and.intro hP hQ),
exact or.inr (and.intro hP hR),
assume h1,
cases h1 with hPQ hPR,
have hP: P, exact and.elim_left hPQ,
have hQ: Q, exact and.elim_right hPQ,
have hQR: Q ∨ R, exact or.inl hQ,
exact and.intro hP hQR,
have hP: P, exact and.elim_left hPR,
have hR: R, exact and.elim_right hPR,
have hQR: Q ∨ R, exact or.inr hR,
exact and.intro hP hQR,
end

-- Capítulo 6, Teorema 6.1, 5.1 Leyes de De Morgan
theorem T27: ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q):=
begin
split, 
assume h1,
have h2: P ∨ ¬ P, exact em P,
cases h2 with h2,
have h3: Q ∨ ¬ Q, exact em Q,
cases h3 with h3,
have h4: P ∧ Q, exact and.intro h2 h3,
have h5 : false, exact h1 h4,
exact false.elim h5, 
exact or.inr h3,
exact or.inl h2,
assume h1,
by_contradiction h2,
have h3: P, exact and.elim_left h2,
have h4: Q, exact and.elim_right h2,
cases h1 with h1,
exact h1 h3,
exact h1 h4,
end

-- Capítulo 6, Teorema 6.1, 5.2 Leyes de De Morgan
theorem T28: ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q):=
begin
split, 
assume h1, 
have hP: ¬ P, by_contradiction hP,
have hPQ: P ∨ Q, exact or.inl hP,
exact h1 hPQ,
have hQ: ¬ Q, by_contradiction hQ,
have hPQ: P ∨ Q, exact or.inr hQ,
exact h1 hPQ,
exact and.intro hP hQ,
assume h1,
have h2: ¬ P, exact and.elim_left h1,
have h3: ¬ Q, exact and.elim_right h1,
by_contradiction h4,
cases h4 with hP hQ,
exact h2 hP,
exact h3 hQ,
end 

-- Capítulo 6, Teorema 6.1, 6.1 Idempotencia de ∧ 
theorem T29: P ∧ P ↔ P:=
begin
split, 
--de izquierda a derecha
assume h1,
exact and.elim_left h1, 
-- de derecha a izquierda
assume h1, 
exact and.intro h1 h1,
end 

-- Capítulo 6, Teorema 6.1, 6.2 Idempotencia de ∨
theorem T30: P ∨ P ↔ P:=
begin
split, 
-- de izquierda a derecha 
assume h1, 
cases h1 with hP hiP,
exact hP,
exact hiP,
-- de derecha a izquierda
assume h1, 
exact or.inl h1, 
end

-- Capítulo 6, Teorema 6.1, 7 Doble negación
theorem T31: ¬ ¬ P ↔ P:=
begin
split,
-- de izquierda a derecha
assume h1, 
by_contradiction h2,
exact h1 h2,
-- de derecha a izquierda
assume h1, 
by_contradiction h2, 
exact h2 h1, 
end 

-- Capítulo 6, Teorema 6.2, 1 Exportación e importación
theorem T32: P → (Q → R) ↔ P ∧ Q → R:=
begin
split, 
assume h1, 
assume h2, 
have h3: P, exact and.elim_left h2,
have h4: Q, exact and.elim_right h2, 
have h5: Q→ R, exact h1 h3,
exact h5 h4,
assume h1, 
assume h2, 
assume h3, 
have h4: P ∧ Q , exact and.intro h2 h3,
exact h1 h4, 
end

-- Capítulo 6, Teorema 6.2, 2 Contraposición
theorem T33: P → Q ↔ ¬ Q → ¬ P:=
begin
split, 
-- de izquierda a derecha
assume h1,
assume h2,
have h3: ¬ P, by_contradiction hP, 
have h4: Q, exact h1 hP,
exact h2 h4, 
exact h3,  
-- de derecha a izquierda
assume h1,
assume h2, 
have h2: Q, by_contradiction hQ,
have h3: ¬P, exact h1 hQ,
exact h3 h2,
exact h2, 
end

-- Capítulo 6, Teorema 6.2, 3 Implicación de una disjuntiva
theorem T34: ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R):=
begin
split,
-- de izquierda a derecha
assume h1, 
have h2: P → R,
assume h3,
have h4: P ∨ Q, exact or.inl h3,
exact h1 h4,
have h3: Q → R,
assume h4,
have h5: P ∨ Q, exact or.inr h4,
exact h1 h5,
exact and.intro h2 h3,
-- de derecha a izquierda
assume h1,
have h2: P → R, exact and.elim_left h1,
have h3: Q → R, exact and.elim_right h1,
assume h4,
cases h4 with hP hQ,
--caso hP
exact h2 hP,
--caso hQ
exact h3 hQ,
end

-- Capítulo 6, Teorema 6.2, 4 Implicación a una disjuntiva
theorem T35: R → (P ∧ Q) ↔ (R → P) ∧ (R → Q):=
begin
split,
-- de izquierda a derecha
assume h1, 
have h2: R → P,
assume h3,
have h4: P ∧ Q, exact h1 h3,
exact and.elim_left h4,
have h7: R → Q,
assume h3,
have h4: P ∧ Q, exact h1 h3,
exact and.elim_right h4,
exact and.intro h2 h7,
-- de derecha a izquierda
assume h1, 
assume h2,
have h3: R → P, exact and.elim_left h1,
have h4: R → Q, exact and.elim_right h1,
have h5: P, exact h3 h2, 
have h6: Q, exact h4 h2, 
exact and.intro h5 h6, 
end
