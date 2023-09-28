# Implementing TMTO complexity from https://eprint.iacr.org/2022/1329

import collections
from basic_functionalities import *

set_vars = collections.namedtuple('BJMM', 'p d1 d2 la lb lc')
num_vars=6
def inject(f) : return wrap(f, set_vars)

k = lambda x : 0.1
w_=Hi(1-k([0]))
w = lambda x : w_

p2 = lambda x: x.p/2   + x.d2
p1 = lambda x: p2(x)/2 + x.d1

r1 = lambda x: reps(p2(x), x.d1, k(x)+x.la+x.lb+x.lc)
r2 = lambda x: reps(x.p  , x.d2, k(x)+x.la+x.lb+x.lc)

D1 = lambda x: binomH(k(x)+x.la+x.lb+x.lc,p1(x))
D2 = lambda x: binomH(k(x)+x.la+x.lb+x.lc,p2(x))

q2 = lambda x: D2(x)+r1(x)-2*D1(x)
q3 = lambda x: D3(x)+r2(x)-2*D2(x)

L1 = lambda x: binomH((k(x)+x.la+x.lb+x.lc)/2,p1(x)/2)
L2 = lambda x: 2*L1(x) - x.la
L3 = lambda x: 2*L2(x) - x.lb + q2(x)
#L4 = lambda x: 2*L3(x) - x.lc + q3(x)

perms = lambda x: binomH(1., w(x)) - binomH(k(x)+x.la+x.lb+x.lc, x.p) - binomH(1-k(x)-x.la-x.lb-x.lc, w(x)-x.p)

constraints = [    
# original strict constraints
# { 'type' : 'ineq',   'fun' : inject(lambda x : r1(x) - x.la)},
# { 'type' : 'ineq',   'fun' : inject(lambda x : r2(x) - x.la - x.lb)},

{ 'type' : 'ineq',   'fun' : inject(lambda x : x.la - r1(x) )},
{ 'type' : 'ineq',   'fun' : inject(lambda x : 3*x.la + x.lb - 2*r1(x)-r2(x))},
    
# correctness 
{ 'type' : 'ineq',   'fun' : inject(lambda x : k(x) - x.p   - x.d2)},
{ 'type' : 'ineq',   'fun' : inject(lambda x : k(x) - p2(x) - x.d1)},
{ 'type' : 'ineq',   'fun' : inject(lambda x : k(x) - p1(x)       )},

{ 'type' : 'ineq',   'fun' : inject(lambda x : (1. - k(x)- x.la-x.lb-x.lc) - (w(x) - x.p)) }, 
{ 'type' : 'ineq',   'fun' : inject(lambda x : w(x) - x.p) }, 
]

def memory(x):
    return max(L1(x)/2,L2(x),L3(x))

def time(x):
    x = set_vars(*x)    

    time1=max(L1(x),2*L1(x)-x.la)
    time2=max(L2(x),2*L2(x)-x.lb)
    time3=max(L3(x),2*L3(x)-x.lc)
    
    return perms(x) + max( max(3*x.la - 2*r1(x) - r2(x), 0)+time1,max(3*x.la + x.lb - 2*r1(x) - r2(x), 0)+max(time2,time3))
