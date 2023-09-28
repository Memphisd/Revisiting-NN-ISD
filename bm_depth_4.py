import collections
from basic_functionalities import *

set_vars = collections.namedtuple('BM', 'p d1 d2 d3 da1 da2 da3 db2 db3 dc3 la lb lc wa wb wc')

num_vars=16

def inject(f) : return wrap(f, set_vars)

k = lambda x : 0.1
w_=Hi(1-k([0]))
w = lambda x : w_

p3 = lambda x: x.p/2   + x.d3
p2 = lambda x: p3(x)/2 + x.d2
p1 = lambda x: p2(x)/2 + x.d1

wa3 = lambda x: x.wa/2   + x.da3
wa2 = lambda x: wa3(x)/2 + x.da2
wa1 = lambda x: wa2(x)/2 + x.da1

wb3 = lambda x: x.wb/2   + x.db3
wb2 = lambda x: wb3(x)/2 + x.db2

wc3 = lambda x: x.wc/2 + x.dc3

r1 = lambda x: reps(p2(x), x.d1, k(x)) 
r2 = lambda x: reps(p3(x), x.d2, k(x))
r3 = lambda x: reps(x.p  , x.d3, k(x))  

c1 = lambda x: x.la - reps(wa2(x), x.da1, x.la) 
c2 = lambda x: x.la - reps(wa3(x), x.da2, x.la) + x.lb - reps(wb3(x), x.db2, x.lb) 
c3 = lambda x: x.la - reps(x.wa  , x.da3, x.la) + x.lb - reps(x.wb  , x.db3, x.lb) + x.lc - reps(x.wc, x.dc3, x.lc)

L1 = lambda x: binomH((k(x))/2, (p1(x))/2.)
L2 = lambda x: binomH( k(x)    , p1(x)    ) - x.la + binomH(x.la,wa1(x)) 
L3 = lambda x: binomH( k(x)    , p2(x)    ) - x.la + binomH(x.la,wa2(x)) - x.lb + binomH(x.lb,wb2(x)) 
L4 = lambda x: binomH( k(x)    , p3(x)    ) - x.la + binomH(x.la,wa3(x)) - x.lb + binomH(x.lb,wb3(x)) - x.lc + binomH(x.lc,wc3(x))

constraints = [
#representation constraints
{ 'type' : 'eq',   'fun' : inject(lambda x : r1(x) - c1(x))},
{ 'type' : 'eq',   'fun' : inject(lambda x : r2(x) - c2(x)) },
{ 'type' : 'eq',   'fun' : inject(lambda x : r3(x) - c3(x)) },
 
#more flexible representation constraints
# { 'type' : 'ineq',   'fun' : inject(lambda x : c1(x) - r1(x))},
# { 'type' : 'ineq',   'fun' : inject(lambda x : c2(x)+ 2 * c1(x)                         -(2*r1(x)+r2(x))) },
# { 'type' : 'ineq',   'fun' : inject(lambda x : c3(x)+ 2 * c2(x) + 4 * c1(x)             -(4*r1(x)+2*r2(x)+r3(x))) },
# { 'type' : 'eq'  ,   'fun' : inject(lambda x : c4(x)+ 2 * c3(x) + 4 * c2(x) + 8 * c1(x) -(8*r1(x)+4*r2(x)+2*r3(x)+r4(x)) ) },
    
#correctness
{ 'type' : 'ineq',   'fun' : inject(lambda x : (1 - k(x) - x.la              ) - (w(x) - x.p - x.wa              ))},
{ 'type' : 'ineq',   'fun' : inject(lambda x : (1 - k(x) - x.la - x.lb       ) - (w(x) - x.p - x.wa - x.wb       ))}, 
{ 'type' : 'ineq',   'fun' : inject(lambda x : (1 - k(x) - x.la - x.lb - x.lc) - (w(x) - x.p - x.wa - x.wb - x.wc))}, 
{ 'type' : 'ineq',   'fun' : inject(lambda x :  1 - k(x) - x.la - x.lb - x.lc                                  )}, 
    
{ 'type' : 'ineq',   'fun' : inject(lambda x : w(x) - x.p - x.wa - x.wb - x.wc) },

{ 'type' : 'ineq',   'fun' : inject(lambda x : k(x) - x.p - x.d3  )},
{ 'type' : 'ineq',   'fun' : inject(lambda x : k(x) - p3(x) - x.d2)},
{ 'type' : 'ineq',   'fun' : inject(lambda x : k(x) - p2(x) - x.d1)},
{ 'type' : 'ineq',   'fun' : inject(lambda x : k(x) - p1(x)       )},
    
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.la - x.wa   - x.da3) },    
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.la - wa3(x) - x.da2) },
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.la - wa2(x) - x.da1) },
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.la - wa1(x)        ) },
    
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.lb - x.wb   - x.db3) },    
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.lb - wb3(x) - x.db2) },
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.lb - wb2(x))         },
    
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.lc - x.wc   - x.dc3) }, 
{ 'type' : 'ineq',   'fun' : inject(lambda x : x.lc - wc3(x))         },
]


def memory(x):
    return max(L1(x),L2(x),L3(x),L4(x))

def time_lists(x):
    timeL1=mo_nn(L1(x), x.la, wa1(x))
    
    timeL2=mo_nn(L2(x), x.lb, wb2(x))
    timeL3=mo_nn(L3(x), x.lc, wc3(x))
    
    timeL4=mo_nn(L4(x), 1 - k(x) -x.la - x.lb - x.lc, w(x) - x.p - x.wa - x.wb - x.wc)
    
    return timeL1, timeL2, timeL3, timeL4

def time_perms(x):
    perms_p = binomH(1.                    , w(x)                    ) - binomH(1 - k(x)                     , w(x) - x.p                     ) - binomH(k(x), x.p )
    perms_a = binomH(1 - k(x)              , w(x) - x.p              ) - binomH(1 - k(x) - x.la              , w(x) - x.p - x.wa              ) - binomH(x.la, x.wa)
    perms_b = binomH(1 - k(x) - x.la       , w(x) - x.p - x.wa       ) - binomH(1 - k(x) - x.la - x.lb       , w(x) - x.p - x.wa - x.wb       ) - binomH(x.lb, x.wb)
    perms_c = binomH(1 - k(x) - x.la - x.lb, w(x) - x.p - x.wa - x.wb) - binomH(1 - k(x) - x.la - x.lb - x.lc, w(x) - x.p - x.wa - x.wb - x.wc) - binomH(x.lc, x.wc)
    
    return perms_p, perms_a, perms_b, perms_c

def time(x):  
    x = set_vars(*x)
    perms_p, perms_a, perms_b, perms_c = time_perms(x)
    timeL1, timeL2, timeL3, timeL4 = time_lists(x)
    
    return perms_p + perms_a + max(timeL1, perms_b + timeL2, perms_b + perms_c + max(timeL3,timeL4))



