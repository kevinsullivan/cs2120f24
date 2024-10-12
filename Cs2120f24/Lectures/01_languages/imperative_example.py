
'''
A step-by-step procedure that takes a number,
x, as input, along with a few other values, and
that computes and returns a value that is within 
a small tolerance of the square root of the input. 
The point of this example is to reinforce the 
idea that the *expressiveness* of code is low. 
It explains *how* to solve a problem, not *what* 
makes an answer correct. 
'''
def a_relation(x, tol=1e-10, max_iterations=1000):
    if x < 0:
        raise ValueError("Oops.")
    elif x == 0:
        return 0
    out = x / 2.0
    for _ in range(max_iterations):
        new_init = (out + x / out) / 2
        if abs(new_init - out) < tol:
            return new_init
        out = new_init
    return out
print(a_relation(25))  
