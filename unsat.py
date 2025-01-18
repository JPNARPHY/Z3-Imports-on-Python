from z3 import *

# Define bit-width for the adder
bit_width = 4

# Input variables for the two numbers to add
X = BitVec('X', bit_width)
Y = BitVec('Y', bit_width)

# I defined RCA function
def rca(X, Y):
    # Ripple Carry Adder description. I will extract the i -th bit of X and Y in order.
    A3, A2, A1, A0 = [Extract(i, i, X) for i in range(3, -1, -1)]#start from 3, ends in 0
    B3, B2, B1, B0 = [Extract(i, i, Y) for i in range(3, -1, -1)]#start from 3, ends in 0
    
    # Half Adder (HA) and Full Adder (FA)
    def HA(a, b): # Sum S=axorb, Carry C=aandb
        return Concat(a & b, a ^ b)# combine sum and carry into 2-bit output
    
    def FA(a, b, c):#Sum=a xor b xor c, C=ab + bc + ac, c=cin
        return Concat((a & b) | (b & c) | (a & c), a ^ b ^ c)#Computes carry-out
    
    # I computed RCA logic here
    S0, C0 = Extract(0, 0, HA(A0, B0)), Extract(1, 1, HA(A0, B0))
    S1, C1 = Extract(0, 0, FA(A1, B1, C0)), Extract(1, 1, FA(A1, B1, C0))
    S2, C2 = Extract(0, 0, FA(A2, B2, C1)), Extract(1, 1, FA(A2, B2, C1))
    S3, C3 = Extract(0, 0, FA(A3, B3, C2)), Extract(1, 1, FA(A3, B3, C2))
    
    return Concat(S3, S2, S1, S0)

# I defined CLA function
def cla(X, Y):
    # Generate and Propagate for bit i
    G = [Extract(i, i, X) & Extract(i, i, Y) for i in range(bit_width)]  # Generate
    P = [Extract(i, i, X) ^ Extract(i, i, Y) for i in range(bit_width)]  # Propagate
    
    # Carry lookahead logic (using bit-vector operations)
    C = [G[0]]  # Initial carry 
    for i in range(1, bit_width):
        carry = G[i] | (P[i] & C[i - 1])  # Ci =Gi+(Pi * C[i-1]).Use | and & for bit-vector operations
        C.append(carry)# I computed carry for each bit at a time
    
    # Compute sum and carry-out
    S = [P[i] ^ (C[i - 1] if i > 0 else BitVecVal(0, 1)) for i in range(bit_width)]# Si=Pi^C[i-1]
    return Concat(*reversed(S)) #reversing it to be in order[S3,S2,S1,S0][MSB-LSB]

# Verify equivalence by initialising z3 solver
solver = Solver()

# Define RCA and CLA outputs
RCA_out = rca(X, Y)
CLA_out = cla(X, Y)

# Assert equivalence and introduce a contradiction (assert not)
solver.add(Not(RCA_out == CLA_out))#find specific inputs (X,Y) where RCA_out and CLA_out behave differently

# Check satisfiability
result = solver.check()
solver_result = solver.model() if result == sat else None

print("Result:", result)
if result == sat:
    print("Counterexample:", solver_result)
else:
    print("RCA and CLA are functionally equivalent (UNSAT).")
