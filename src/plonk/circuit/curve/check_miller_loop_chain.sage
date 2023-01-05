# NB: in all our reasonings we only deal with the case of BN256 curve. BLS12-curve is not considered for now.
# For two points P and Q - input of the pairing it is rather cheaply verified in circuit that they belong to 
# corresponding curves E(F_q) and  E`(Fq^2), where E` - sextic D-type twist
# the verification is done simply by enforcing: y_p^2 = x_p^3 + b and y_q^2 = x_q^3 + b`
# After this check P is automatically in G1 (G1 == E(F_q)) and |E`(Fq^2)| is much larger than G2.
# we want to aggregate subgroup check for Q (attesing that Q is indeed in G2) and miller loop for (P, Q) in a single
# circuit. 

# The trick is the following: let u be the seed for BN256 curve, than subgroup check for Q boils down to verifying:
# twisted_frob(Q) = u * Q [ref: https://eprint.iacr.org/2022/352.pdf, page 15]
# during Miller loop we have to compute both t* Q = [6 * u + 2] * Q and twisted_frob(Q)
# [ref: https://eprint.iacr.org/2010/354.pdf, page 3]
# we select addition-chain for t which goes through u.

# In order to compute t * Q we use standard double and add ladder: let u_dec - ternary decomposition for t 
# (in base 0, 1, -1). The scalar multiplication algorithm is the following: 
# acc = Q
# for signed_bit in u_dec[1..]:
#     acc = double(acc)
#     if signed_bit == 1:
#           acc = add(acc, Q)    (*)
#     else if signed_bit =-1:
#           acc = add(acc, -Q)   (**)
# return Q
# Both of operations doble and add may in general cause exceptions. The aim of the script is to justify that for
# paritcularly selected addition chain for t (of cause going, through u, is pointed out earlier) there will be 
# NO EXCEPTIONS regardless the choice for starting point Q in E`(Fq^2).
# 
# For doubling to be exception-free it is enough to verify that there are no points of order 2 on the twisted curve 
# E`(Fq^2) i.e. no points with y coordinate = 0. It boils down to verify that polynomial equation x^3 + b` has no roots
# over Fq^2.

# Addition of two points R and T only cause exception for R = +/- T <=> x_r = t_r. 
# However, in our scenario we are not interested in general additions, but only in additions of special form 
# which arise from point by scalar multiplication algorithm, where all the additions (*), (**) are of the form 
# k * P +/- P and exceptions are hence only possible in the case when ord(P) = k+/- 1.
# however, by basic group theory ord(P) | |E`(Fq)| => (k+\-1) | |E`(Fq)| and later we  are going to prove that 
# with respect to the chosen additon chain for t there are no intermidiate k, such that (k+\-1) | |E`(Fq)|

# That was the plan now we start to carry out it's implementation:
# parameters of the base curve are:
Fq = 21888242871839275222246405745257275088696311157297823662689037894645226208583
a = 0
b = 3
Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617
base_field = GF(Fq)
base_curve = EllipticCurve(base_field, [a, b])
assert(base_curve.order() == Fr)
t = Fq + 1 - Fr

# we first start with computing the order of |E`(Fq)|
# there is an algorithm (A) that allows to determine the number of points over F_p^k if we know the number of points
# over F_p, where p = q^r - some extension of prime field.
# ref: http://jjmcgee.asp.radford.edu/SchoofsAlgorithm06.pdf, formula 21
# E(F_p^n) = p^n + 1 − s_n
# s_0= 2, s_1 = t and s_{n+1} = t * s_n − p * s_{n−1}, t = trace of Frobenius: t = p + 1 - E(F_p)
# Usinh this algorithm we are able to compute |E(F_p^2)|
# according to "Guide_to_pairing_based_crypto" 2-27: if curve E admits the twist E` of degree d then:
# num_points_twist = q + 1 - (3 * f + t)/2 or num_points_twist =q + 1 + (3 * f - t)/2 and
# t^2 - 4 * q = - 3 * f^2
# we also now that num_points_twist % Fr == 0
# apply previous remark to the pair of curves E(F_p^2) and E`(F_p^2)
def compute_num_points_on_ext(base_num_points, base_degree, ext_degree):
    t = Fq^base_degree + 1 - base_num_points
    s_arr = [2, t]
    cur_degree = base_degree
    while cur_degree < ext_degree:
        s_new = t * s_arr[-1] - Fq^base_degree * s_arr[-2]
        s_arr.append(s_new)
        cur_degree += base_degree
    assert(cur_degree == ext_degree)
    return Fq^ext_degree + 1 - s_arr[-1]

num_points_ext = compute_num_points_on_ext(Fr, 1, 2)
t2 = Fq^2 + 1 - num_points_ext
f_squared = (4 * Fq^2 - t2^2) / 3
f = sqrt(f_squared)
assert(f^2 == f_squared)

x1 = Fq^2 + 1 - (3 * f + t2)/2
x2 =  Fq^2 + 1 + (3 * f - t2)/2
# only x1 satisfies x % Fr == 0
assert(x1 % Fr == 0 and x2 % Fr != 0)
num_points_twist = x1

# for self-check that we have found the number of points on the twist correctly we also do the following:
# compute the number of points of the curve E`(F_q^12) starting with |E`(F_q^2)| = num_points_twist, p = q^2
# and the number of points of the curve E(F_q^12) starting with |E(F_q)| = Fr, p = q (we use (A) for both)
# there is an isogeny between these curves over F_q^12 and hence the number of points should be the same
lhs = compute_num_points_on_ext(Fr, 1, 12)
rhs = compute_num_points_on_ext(num_points_twist, 2, 12)
assert(lhs == rhs)


R.<x>=PolynomialRing(base_field)
ext2 = base_field.extension(x^2 + 1, 'u')
a_ext = ext2(a)
b_ext = ext2(b)
non_residue = ext2(9 + 1 * x)
b_new = b_ext/non_residue
twisted_curve = EllipticCurve(ext2, [a_ext, b_new])
assert(twisted_curve.order() == num_points_twist)

# checking there are no points on twisted curve of order 2: these are precisely the points of the form (x, 0):
# equation x^3 + b_new = 0 has no roots in Fq2
R.<y>=PolynomialRing(ext2)
roots = (y^3 + b_new).roots(multiplicities=False)
assert(len(roots) == 0)


u = 4965661367192848881
t = 6*u + 2
u_dec = [
    1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 
    1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1 
]
acc = 1
for bit in u_dec[1:]:
    acc *= 2
    if bit != 0 and (num_points_twist % (acc + 1) == 0 or num_points_twist % (acc - 1) == 0):
        raise Exception("The selected chain for u is not exception free")
    acc += bit
assert(acc == u)

# remainign addition chain from u to t = 6 * u + 2
# u -> 2 * u (doubling no exceptions) -> 3u = 2u + u (exceptions iff u | num_points_twist) -> 3u + 1 
# (exceptions of 3u + 1 | num_points twist or  3u - 1 | num_points_twist) -> 6u + 2 (doubling no exceptions)
assert(num_points_twist % u > 0)
assert(num_points_twist % (3*u+1) > 0)
assert(num_points_twist % (3*u-1) > 0)

# if we are here everything should be good
print "Success"