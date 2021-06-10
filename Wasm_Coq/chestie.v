Goal forall m n,
m + n = n + m.

induction n.

- admit.
- admit.
Admitted.

Goal forall m n,
m + n = n + m.
intros m n.
generalize dependent m.
induction n.
- admit.
- 