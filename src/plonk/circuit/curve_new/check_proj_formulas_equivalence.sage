# Reference: https://eprint.iacr.org/2015/1060.pdf

x = var('x')
y = var('y')
z = var('z')

x1 = var('x1')
y1 = var('y1')
z1 = var('z1')

x2 = var('x2')
y2 = var('y2')
b3 = var('b3')

def check_mixed_add_formulas_equivalence():
    def optimized_impl(): 
        t4 = y2 * z1 + y1
        y3 = x2 * z1 + x1
        z3 = y1 * y2 + b3 * z1
        t0 = x1 * x2
        t3 = (x2 + y2) * (x1 + y1) - t0 - z3 + b3 * z1
        x3 = t4 * b3 * y3
        t1 = z3 - 2 * b3 * z1
        x3 = t3 * t1 - x3
        y3 = b3 * y3 * 3 * t0 
        y3 = t1 * z3  + y3 
        t0 = 3 * t0 * t3
        z3 = z3 * t4 + t0
        return (x3, y3, z3)
    (x3_opt, y3_opt, z3_opt) = optimized_impl()
    
    def raw_impl():
        t0 = x1 * x2 
        t1 = y1 * y2 
        t3 = x2 + y2
        t4 = x1 + y1 
        t3 = t3 * t4 
        t4 = t0 + t1
        t3 = t3 - t4 
        t4 = y2 * z1 
        t4 = t4 + y1
        y3 = x2 * z1 
        y3 = y3 + x1 
        x3 = t0 + t0
        t0 = x3 + t0 
        t2 = b3 * z1 
        z3 = t1 + t2
        t1 = t1 - t2 
        y3 = b3 * y3 
        x3 = t4 * y3
        t2 = t3 * t1 
        x3 = t2 - x3 
        y3 = y3 * t0
        t1 = t1 * z3 
        y3 = t1 + y3 
        t0 = t0 * t3
        z3 = z3 * t4 
        z3 = z3 + t0
        return (x3, y3, z3)
    (x3_raw, y3_raw, z3_raw) = raw_impl()
    
    assert bool(x3_raw == x3_opt)
    assert bool(y3_raw == y3_opt)
    assert bool(z3_raw == z3_opt)
    
    
def check_double_formulas_equivalence():
    def optimized_impl(): 
        t0 = y * y 
        t2 = b3 * z * z
        y3 = t0 + t2
        t1 = y * z 
        z3 = 8 * t0 * t1
        t4 = 4 * t0 - 3 * y3
        y3 = t4 * y3
        y3 = 8 * t0 * t2  + y3
        t1 = x * y 
        x3 = 2 * t4 * t1
        return (x3, y3, z3)
    (x3_opt, y3_opt, z3_opt) = optimized_impl()
    
    def raw_impl():
        t0 = y * y 
        z3 = t0 + t0 
        z3 = z3 + z3
        z3 = z3 + z3 
        t1 = y * z 
        t2 = z * z
        t2 = b3 * t2 
        x3 = t2 * z3 
        y3 = t0 + t2
        z3 = t1 * z3 
        t1 = t2 + t2 
        t2 = t1 + t2
        t0 = t0 - t2 
        y3 = t0 * y3 
        y3 = x3 + y3
        t1 = x * y 
        x3 = t0 * t1 
        x3 = x3 + x3
        return (x3, y3, z3)
    (x3_raw, y3_raw, z3_raw) = raw_impl()
    
    assert bool(x3_raw == x3_opt)
    assert bool(y3_raw == y3_opt)
    assert bool(z3_raw == z3_opt)


def check_general_add_formulas_equivalence():
    def raw_impl():
        t0 = x1 * x2 
        t1 = y1 * y2 
        t2 = z1 * z2
        t3 = x1 + y1 
        t4 = x2 + y2 
        t3 = t3 * t4
        t4 = t0 + t1 
        t3 = t3 - t4 
        t4 = y1 + z1
        x3 = y2 + z2 
        t4 = t4 * x3 
        x3 = t1 + t2
        t4 = t4 - x3 
        x3 = x1 + z1 
        y3 = x2 + z2
        x3 = x3 * y3 
        y3 = t0 + t2 
        y3 = x3 - y3
        x3 = t0 + t0 
        t0 = x3 + t0 
        t2 = b3 * t2
        z3 = t1 + t2 
        t1 = t1 - t2 
        y3 = b3 * y3
        x3 = t4 * y3 
        t2 = t3 * t1
        x3 = t2 - x3
        y3 = y3 * t0 
        t1 = t1 * z3 
        y3 = t1 + y3
        t0 = t0 * t3 
        z3 = z3 * t4 
        z3 = z3 + t0
        return (x3, y3, z3)
    (x3_raw, y3_raw, z3_raw) = raw_impl()
    
    def optimized_impl():
        t0 = x1 * x2 
        t1 = y1 * y2 
        t2 = z1 * z2
        a1 = x1 + y1
        a2 = x2 + y2
        t3 = a1 * a2 - t0 - t1 
        t4 = y1 + z1
        x3 = y2 + z2 
        t4 = t4 * x3 - t1 - t2 
        a3 = x1 + z1
        a4 = x2 + z2
        y3 = a3 * a4 - t0 - t2
        t2 = b3 * z1 * z2
        z3 = t1 + t2 
        t1 = t1 - t2 
        x3 = t4 * b3 * y3
        x3 = t3 * t1 - x3
        y3 = b3 * y3 * 3 * t0 
        y3 = t1 * z3  + y3
        z3 = z3 * t4 
        z3 = z3 + 3 * t0 * t3 
        return (x3, y3, z3)
    (x3_opt, y3_opt, z3_opt) = optimized_impl()
    
    assert bool(x3_raw == x3_opt)
    assert bool(y3_raw == y3_opt)
    assert bool(z3_raw == z3_opt)



check_mixed_add_formulas_equivalence()
check_double_formulas_equivalence()
check_general_add_formulas_equivalence()
print "done"
