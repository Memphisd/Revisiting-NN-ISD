# Implementing TMTO complexity from https://eprint.iacr.org/2022/1329

import collections
from basic_functionalities import *

set_vars = collections.namedtuple('MMT', 'p l l1')
num_vars=3
def inject(f) : return wrap(f, set_vars)

k = lambda x : 0.1
w_=Hi(1-k([0]))
w = lambda x : w_

r1 = lambda x: binomH(x.p,x.p/2)

L1 = lambda x: binomH((k(x)+x.l)/2,x.p/4)
L2 = lambda x: 2*L1(x) - x.l1

perms = lambda x: binomH(1., w(x)) - binomH(k(x)+x.l, x.p) - binomH(1-k(x)-x.l, w(x)-x.p)

constraints = [   
# correctness 
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.l - x.l1) },
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.l1 - r1(x)) },
{ 'type' : 'ineq',   'fun' : inject(lambda x : (1. - k(x)- x.l) - (w(x) - x.p)) }, 
{ 'type' : 'ineq',   'fun' : inject(lambda x : w(x) - x.p) }, 
]

def memory(x):
    return max(L1(x)/2,L2(x))

def time(x):
    x = set_vars(*x)    

    time1=max(x.l1-r1(x),0)+max(L1(x),L2(x),2*L2(x)-(x.l-x.l1))
    
    return perms(x) + time1
