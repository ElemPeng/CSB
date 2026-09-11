# A proof of Cantor-Schroder-Bernstein:
If A and B are types, f : A -> B is injective, and g : B -> A is injective, then there is a bijection
phi : A -> B

this is essentially a proof that if A and B are sets such that |A| <= |B| and |B| <= |A| (ie there are injections from A to B and vice versa), then |A| = |B| (ie there is a bijection from A to B). This proves that the relation |A| <= |B| iff there is an injection f : A -> B is antisymmetric. 

The basic argument is as follows:
For any element a of A, there is a chain (possibly of zero length, possibly infinite) of points, alternatively in B and A so that a = g (b) = g (f (a1)) = g (f (g (b1)))....

there are three possibilities: 
1) This chain is finite and ends in A (or in fact never starts); in this case a is in A1.
2) This chain is finite and ends in B; in this case a is in A2.
3) This chain is infinite; in this case a is in A3.

Similarly, define B1, B2, and B3 in B.

the end result is that
1) f is a bijection from A1 to B2
2) g is a bijection from B1 to A2
3) f is a bijection from A3 to B3 (and g is a bijection from B3 to A3, though note that f and g are generally not inverses)

We then define a function phi : A -> B so that
1) if a is in A2, phi (a) = g^-1 (a)
2) otherwise, phi (a) = f (a)

This function is the bijection we need.

The proof itself is in CSB/Basic.lean; probably should have been in CSB.lean or Main.lean but I'm lazy.
