import collections
from basic_functionalities import *

set_vars = collections.namedtuple('BJMM_MO', 'p d1 d2 d3 l la lb lc')
num_vars=8
def bjmm_mo(f) : return wrap(f, set_vars)

k = lambda x : 0.1
w_=Hi(1-k([0]))
w = lambda x : w_

p3 = lambda x: x.p/2+x.d3
p2 = lambda x: x.p/4+x.d3/2+x.d2
p1 = lambda x: x.p/8+x.d3/4+x.d2/2+x.d1

r1 = lambda x: reps(p2(x), x.d1, k(x)+x.l)
r2 = lambda x: reps(p3(x), x.d2, k(x)+x.l)
r3 = lambda x: reps(x.p , x.d3, k(x)+x.l)

D1 = lambda x: binomH(k(x)+x.l,p1(x))
D2 = lambda x: binomH(k(x)+x.l,p2(x))
D3 = lambda x: binomH(k(x)+x.l,p3(x))

q2 = lambda x: D2(x)+r1(x)-2*D1(x)
q3 = lambda x: D3(x)+r2(x)-2*D2(x)
q4 = lambda x: 1+r(x)-2*D3(x)

L1 = lambda x: binomH((k(x)+x.l)/2,p1(x)/2)
L2 = lambda x: 2*L1(x) - x.la
L3 = lambda x: 2*L2(x) - x.lb + q2(x)
L4 = lambda x: 2*L3(x) - x.lc + q3(x)

perms = lambda x: binomH(1., w(x)) - binomH(k(x)+x.l, x.p) - binomH(1-k(x)-x.l, w(x)-x.p)

constraints = [    
# original strict constraints
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : r1(x) - x.la)},
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : r2(x) - x.la - x.lb)},
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : r3(x) - x.la - x.lb - x.lc) },
    
# more flexible constraints (no difference for this algorithm)
# { 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : x.la-r1(x))}, 
# { 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : 3*x.la+x.lb-2*r1(x)-r2(x)) }, 
# { 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : 4*r1(x)+2*r2(x)+r3(x)-(7*x.la+3*x.lb+x.lc)) }, 
    

# correctness 
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : k(x) - x.p - x.d3  )},
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : k(x) - p3(x) - x.d2)},
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : k(x) - p2(x) - x.d1)},
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : k(x) - p1(x)       )},
    
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : x.l - (x.la+x.lb+x.lc)) }, 
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : (1. - k(x)- x.l) - (w(x) - x.p)) }, 
{ 'type' : 'ineq',   'fun' : bjmm_mo(lambda x : w(x) - x.p) }, 
]

def memory(x):
    return max(L1(x),L2(x),L3(x),L4(x))

def time(x):
    x = set_vars(*x)    

    time1=max(L1(x),2*L1(x)-x.la)
    time2=max(L2(x),2*L2(x)-x.lb)
    time3=max(L3(x),2*L3(x)-x.lc)
    time4=mo_nn(L4(x),1-k(x)-x.l,w(x)-x.p)
    
    return perms(x) + max(time1,time2,time3,time4)
