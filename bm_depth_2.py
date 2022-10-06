import collections
from basic_functionalities import *

set_vars = collections.namedtuple('BM2', 'p d1 da1 la wa')
num_vars=5

def bm2(f) : return wrap(f, set_vars)

k = lambda x : 0.1
w_=Hi(1-k([0]))
w = lambda x : w_

p1 = lambda x: x.p/2+x.d1

wa1 = lambda x: x.wa/2   + x.da1

r1 = lambda x: reps(x.p , x.d1, k(x))
c1 = lambda x: x.la - reps(x.wa,x.da1,x.la) 

L1 = lambda x: binomH((k(x))/2, (p1(x))/2.)
L2 = lambda x: binomH( k(x)    , p1(x)    ) - x.la + binomH(x.la,wa1(x)) 

constraints =[
#representation constraints
{ 'type' : 'eq',   'fun' : bm2(lambda x : r1(x) - c1(x))},

#correctness
{ 'type' : 'ineq',   'fun' : bm2(lambda x : (1 - k(x) - x.la) - (w - x.p - x.wa)) }, 
{ 'type' : 'ineq',   'fun' : bm2(lambda x :  1 - k(x)  -x.la)                     }, 
    
{ 'type' : 'ineq',   'fun' : bm2(lambda x : w(x) - x.p - x.wa) },
    
{ 'type' : 'ineq',   'fun' : bm2(lambda x : x.la - x.wa   - x.da1) },    
{ 'type' : 'ineq',   'fun' : bm2(lambda x : x.la - wa1(x))         },
    
{ 'type' : 'ineq',   'fun' : bm2(lambda x : k(x) - x.p  - x.d1)},
{ 'type' : 'ineq',   'fun' : bm2(lambda x : k(x) - p1(x)      )}
]

def memory(x):
    return max(L1(x),L2(x))

def time_lists(x):
    timeL1=mo_nn(L1(x), x.la, wa1(x))
    timeL2=mo_nn(L2(x), 1 - k(x) - x.la,  w - x.p - x.wa)
    
    return timeL1, timeL2

def time_perms(x):
    perms = binomH(1, w(x)) - binomH(1 - k(x) - x.la, w(x) - x.p - x.wa) - binomH(k(x), x.p) - binomH(x.la, x.wa)
    
    return perms

def time(x):  
    x = set_vars(*x) 
    perms = time_perms(x)
    timeL1, timeL2 = time_lists(x)
    
    return perms + max(timeL1, timeL2)




