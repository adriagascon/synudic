
Using dual to synthesize bitvector programs.
-------------------------------------------

We have to define an 'abstraction' that will be sufficient to prove correctness.
For bitvector examples, when we use only primals, synthesis output looks like magic:
we have no intuition for why the solution works, but we get a correct solution.
However, if we try to do bitvector examples using just duals, we need to encode a
proof system which will prove the correctness of the (synthesized) bitvector program:
hence, it does not look like magic any more-- the dual appears to encode strong hints
about the solution.  Nevertheless, the goal here is to demonstrate that almost any
example can be solved using only duals.

For rightmostOff, isolateRightOnes, mask10s:
--------------------------------------------
We use the abstraction 
 x100 --> any bitvector of the form x10*0
 x is any size bitvector, 1 is a single bit, next 0 denotes arbitrary number of zeros, and the last 0 denotes a single bit (set to 0)

 x111 --> any bitvector of the form x11*1
  Similar to above.
  
This abstraction is designed for program that take ONE input
bitvector. 
It is assumed that "x" means that the value is the same as the
first |x| bits of the input.

c0100 --> denotes the constant 0* 1 0* 0
 i.e. we have isolated the rightmost 1 bit in x100

Using this abstraction, we have synthesized
rightmostOneOff and isolateRightMostOne;
see file *_Dual.sketch 

In principle, we also need another dual for the case x011 abstraction,
but I was too lazy to write it up.


For max_Dual:
-------------
We use the abstraction 
a,b,ab,c0,c1,unknown
where a = first input, b = second input,
ab = a xor b,  c0 = constant with all zeros,
c1 = constant with all ones, unknown = could be anything

Note that we have TWO duals here;
one abstraction was designed for the case when input1 > input2
and the second abstraction was for the case when input1 <= input2


For computing average of two numbers without overflowing:
---------------------------------------------------------

We abstract by performing symbolic computation and noting
that a+b = (a xor b) + 2*(a and b)   ----- (1)
( decompose plus to sum-bit and carry-bit computation).
Then, we need something in the abstraction to recognize overflows.
So, we abstract by a symbolic expression representing an upper-bound
of the value computed at that program point.
 each expression is associated to (a,b,c,op) with the meaning that
 the primal value of the expression is upper-bounded by (a*in1 op b*in2  + c)

And then we note that right-shift introduces an error of atmost 0.5 , 
and we note equation (1) when writing the dual rules.



